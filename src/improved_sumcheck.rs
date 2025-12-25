use ark_poly_commit::kzg10::*;
use ark_poly_commit::error::Error;
use ark_ec::pairing::Pairing;
use ark_poly::polynomial::Polynomial;
use ark_ff::fields::Field;
use ark_poly::DenseUVPolynomial;
use ark_poly::univariate::DensePolynomial;
use ark_poly::evaluations::multivariate::multilinear::MultilinearExtension;
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension;
use ark_poly::EvaluationDomain;
use ark_poly::Radix2EvaluationDomain;
use ark_std::{start_timer, end_timer, Zero, One, marker::PhantomData};
use ark_std::{UniformRand};
use ark_std::rand::rngs::StdRng;
use ark_std::rand::{SeedableRng, RngCore};
use merlin::Transcript;
use ark_ff::BigInteger;
use ark_ff::PrimeField;
use ark_ff::FftField;
use ark_serialize::CanonicalSerialize;
use ark_poly_commit::PCCommitmentState;
use crate::samaritan_mlpcs::*;
use crate::util;
use ark_ec::VariableBaseMSM;
use ark_ec::CurveGroup;
use ark_ff::batch_inversion;

pub struct ImprovedSumcheckProof<E: Pairing> {
	number_of_initial_rounds: usize,
	mlp_a_commit: Commitment<E>,
	mlp_b_commit: Commitment<E>,
	mlp_ab_commit: Commitment<E>,
	coeffs: Vec<Vec<E::ScalarField>>,
	g_hat_commit: Commitment<E>,
	h_hat_commit: Commitment<E>,
	V_eq: E::ScalarField,
	V_mlp_a: E::ScalarField,
	V_mlp_b: E::ScalarField,
	V_mlp_ab: E::ScalarField,
	F_bar_commit: Commitment<E>,
	F_bar_eval_proof: KZG10EvalProof<E>,
	H_bar_commit: Commitment<E>,
	K_hat_commit: Commitment<E>,
	K_ext_hat_commit: Commitment<E>,
	V_y: E::ScalarField,
	t_hat_commit: Commitment<E>,
	eval_for_eta: E::ScalarField,
	A_hat_commit: Commitment<E>,
	eval_for_delta: E::ScalarField,
	S_hat_commit: Commitment<E>,
	d_hat_commit: Commitment<E>,
	D_hat_commit: Commitment<E>,
	// W1: E::ScalarField,
	W2: E::ScalarField,
	W3: E::ScalarField,
	W4: E::ScalarField,
	W5: E::ScalarField,
	W6: E::ScalarField,
	combined_mlp_eval_proof: SamaritanMLPCSEvalProof<E>,
	L_hat_eval_proof: KZG10EvalProof<E>,
}

pub struct ImprovedSumcheck<E: Pairing> {
	_engine: PhantomData<E>,
}

impl<E: Pairing> ImprovedSumcheck<E> {
	pub fn setup<R: RngCore>(rng: &mut R, log_number_of_gates: usize) -> Result<SamaritanMLPCS_SRS<E>, Error> {
		let srs = SamaritanMLPCS::<E>::setup(log_number_of_gates, rng).unwrap();

		// let qM_comm = SamaritanMLPCS::<E>::commit_G1(&srs, &mlp_ab).unwrap();

		Ok(srs)
	}

	pub(crate) fn compute_eq_tilde(log_number_of_gates: usize, tau: &Vec<E::ScalarField>) -> DenseMultilinearExtension<E::ScalarField> {
		let number_of_gates: usize = 1 << log_number_of_gates;

		let mut tau_inverses = tau.clone();
		batch_inversion(&mut tau_inverses);
		let mut one_minus_tau: Vec<E::ScalarField> = Vec::new();
		for i in 0..log_number_of_gates {
			one_minus_tau.push(E::ScalarField::one() - tau[i]);
		}
		let mut one_minus_tau_inverses = one_minus_tau.clone();
		batch_inversion(&mut one_minus_tau_inverses);

		let gray_code_seq: Vec<_> = (0..number_of_gates).map(|i| i ^ (i >> 1)).collect();

		let mut first = E::ScalarField::one();
		for i in 0..log_number_of_gates {
			first *= E::ScalarField::one() - tau[i];
		}
		let mut evals: Vec<E::ScalarField> = vec![first; number_of_gates];
		let mut bit_seq: Vec<i8> = vec![0; log_number_of_gates];
		for i in 1..number_of_gates {
			let flip_pos: usize = (((gray_code_seq[i] as i32) - (gray_code_seq[i-1] as i32)).abs().ilog2()).try_into().unwrap();
			if bit_seq[flip_pos] == 0 {
				first *= tau[flip_pos] * one_minus_tau_inverses[flip_pos];
				evals[gray_code_seq[i]] = first;
				bit_seq[flip_pos] = 1;
			}
			else {
				first *= one_minus_tau[flip_pos] * tau_inverses[flip_pos];
				evals[gray_code_seq[i]] = first;
				bit_seq[flip_pos] = 0;
			}
		}
		DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_number_of_gates, evals)
	}

	pub(crate) fn evaluate_eq_tilde_at_point(log_number_of_gates: usize, tau: &Vec<E::ScalarField>, eval_point: &Vec<E::ScalarField>) -> E::ScalarField {
		let mut res = E::ScalarField::one();
		for i in 0..log_number_of_gates {
			res = res * (tau[i] * eval_point[i] + (E::ScalarField::one() - tau[i]) * (E::ScalarField::one() - eval_point[i]));
		}
		res
	}

	pub(crate) fn compute_univariate_r_X_evaluation(mlp_set: &mut Vec<&mut DenseMultilinearExtension<E::ScalarField>>, eval_point: E::ScalarField) -> E::ScalarField {
		let mut tmp : Vec<_> = Vec::new();
		let mut i = 0;
		for mlp in mlp_set.iter_mut() {
			let tmp_poly = (*mlp).fix_variables(&[eval_point]);
			tmp.push(tmp_poly);
			i += 1;
		}
		let mut res = vec![E::ScalarField::zero(); tmp[0].to_evaluations().len()];
		for i in 0..res.len() {
			res[i] = tmp[0][i] * (tmp[3][i] - (tmp[1][i] * tmp[2][i])); 
		}
		res.iter().sum()
	}

	pub(crate) fn compute_evaluation_through_lagrange_interpolation(d_plus_one_evaluation_points: &Vec<E::ScalarField>, d_plus_one_evaluations: &Vec<E::ScalarField>, alpha: E::ScalarField) -> E::ScalarField {
		assert_eq!(d_plus_one_evaluation_points.len(), d_plus_one_evaluations.len());
		let num_points = d_plus_one_evaluation_points.len();
		let mut eval = E::ScalarField::zero();
		for i in 0..num_points {
			let mut prod_term = d_plus_one_evaluations[i];
			let mut denom = E::ScalarField::one();
			for j in 0..num_points {
				if i != j {
					prod_term *= alpha - d_plus_one_evaluation_points[j]; 
					denom *= d_plus_one_evaluation_points[i] - d_plus_one_evaluation_points[j];
				}
			}
			eval += prod_term * denom.inverse().unwrap();
		}
		eval
	}

	pub(crate) fn compute_G_bar_from_O_bar_set(O_bar_set: &Vec<DensePolynomial<E::ScalarField>>) -> DensePolynomial<E::ScalarField> {
		/* Note that (for reference to the sequence of polynomials present in the vector) : 
		mlp_set = {eq_tilde, mlp_a_copy, mlp_b_copy, mlp_ab_copy} */
		let res = &O_bar_set[0] * (&O_bar_set[3] - (&O_bar_set[1] * &O_bar_set[2]));
		res 
	}

	pub(crate) fn compute_G_prime(O_bar_set: &Vec<DensePolynomial<E::ScalarField>>, g_hat: &DensePolynomial<E::ScalarField>, h_hat: &DensePolynomial<E::ScalarField>, z: E::ScalarField, m: usize, V_eq: E::ScalarField, V_mlp_b: E::ScalarField) -> DensePolynomial<E::ScalarField> {
		let res = (&O_bar_set[3] - &O_bar_set[1] * V_mlp_b) * V_eq - g_hat * (z.pow(&[m as u64]) - E::ScalarField::from(1 as u64)) - h_hat * z;
		res
	}

	pub(crate) fn compute_F_bar(O_bar_set: &Vec<DensePolynomial<E::ScalarField>>, G_prime: &DensePolynomial<E::ScalarField>, alpha_powers: &Vec<E::ScalarField>) -> DensePolynomial<E::ScalarField> {
		let F_bar = G_prime + &O_bar_set[0] * alpha_powers[0] + &O_bar_set[1] * alpha_powers[1] + &O_bar_set[2] * alpha_powers[2] + &O_bar_set[3] * alpha_powers[3];
		F_bar
	}

	pub(crate) fn compute_H_bar(O_bar_set: &Vec<DensePolynomial<E::ScalarField>>, a_vec: &Vec<E::ScalarField>) -> DensePolynomial<E::ScalarField> {
		let mut H_bar = DensePolynomial::<E::ScalarField>::zero();
		let mut iter = 0;
		for O_bar in O_bar_set {
			H_bar = H_bar + O_bar * a_vec[iter];
			iter = iter + 1;
		}
		H_bar
	}

	pub(crate) fn compute_K_hat(O_tilde_set: &Vec<&mut DenseMultilinearExtension<E::ScalarField>>, a_vec: &Vec<E::ScalarField>) -> DensePolynomial<E::ScalarField> {
		let mut K_hat = DensePolynomial::<E::ScalarField>::zero();
	    let mut iter = 0;
	    for O_tilde in O_tilde_set {
	    	K_hat = K_hat + (DensePolynomial::<E::ScalarField>::from_coefficients_vec(O_tilde.to_evaluations()) * a_vec[iter]);
	    	iter = iter + 1;
	    }
	    K_hat
	}

	// Following function is computed by the Prover: O(mlog(m)) = O(n)
	pub(crate) fn compute_e_hat_coeffs(kappa: usize, y: &Vec<E::ScalarField>) -> Vec<E::ScalarField> {
		let m = 1 << kappa;
		let mut e_hat_coeffs : Vec<_> = Vec::new();
		for i in 0..m {
			let mut term = E::ScalarField::one();
			for j in 0..kappa {
				if (i >> j) & 1 == 1 {
					term *= y[j];
				}
				else {
					term *= E::ScalarField::one() - y[j];
				}
			}
			e_hat_coeffs.push(term);
		}
		e_hat_coeffs
	}

	// Following function is computed by the Verifier: O(log(m))
	pub(crate) fn evaluate_e_hat_at_point(kappa: usize, y: &Vec<E::ScalarField>, point: &E::ScalarField) -> E::ScalarField {
		let mut res = E::ScalarField::one();
		let mut point_pow = *point;
		for i in 0..kappa {
			res = res * (y[i] * point_pow + (E::ScalarField::one() - y[i]));
			point_pow = point_pow * point_pow;
		}
		res
	}

	// t_hat = fft(e_hat)
	pub(crate) fn compute_t_hat(m: usize, e_hat_coeffs: &Vec<E::ScalarField>) -> DensePolynomial<E::ScalarField> {
		let domain = Radix2EvaluationDomain::<E::ScalarField>::new(m).unwrap();
		let t_coeffs_vec = domain.fft(&e_hat_coeffs);
		let t_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(t_coeffs_vec);
		t_hat
	}

	// A_hat_coeffs[i] = 1/(eta*omega_pow_i - 1). So first perform fft on polynomial (eta * X - 1) to get the inverse of the actual A_hat coefficients, and then perform inverse of each element in the vector
	pub(crate) fn compute_A_hat(eta: E::ScalarField, m: usize) -> DensePolynomial<E::ScalarField> {
		let domain = Radix2EvaluationDomain::<E::ScalarField>::new(m).unwrap();
		let eta_x_minus_one_coeffs = vec![-E::ScalarField::one(), eta];
		let A_hat_evals_at_roots_of_unity_inv = domain.fft(&eta_x_minus_one_coeffs);

		let mut A_hat_coeffs : Vec<_> = Vec::new();
		for i in 0..m {
			A_hat_coeffs.push(A_hat_evals_at_roots_of_unity_inv[i].inverse().unwrap());
		}
		let A_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(A_hat_coeffs);
		A_hat
	}

	pub(crate) fn compute_B_hat_delta_coeffs(A_hat: &DensePolynomial<E::ScalarField>, delta: E::ScalarField, m: usize) -> Vec<E::ScalarField> {
		let mut B_hat_delta_coeffs : Vec<_> = Vec::new();
		let A_hat_coeffs = A_hat.coeffs().to_vec();
		for i in 0..m {
			B_hat_delta_coeffs.push(A_hat_coeffs[i].inverse().unwrap() * delta.pow(&[i as u64]));
		}
		B_hat_delta_coeffs
	}

	pub(crate) fn evaluate_B_hat_at_point(eta: &E::ScalarField, point: &E::ScalarField, kappa: usize) -> E::ScalarField {
		let mut Psi = E::ScalarField::one();
		let m = 1 << kappa;
		let mth_root_of_unity = E::ScalarField::get_root_of_unity(m.try_into().unwrap()).unwrap();
		let mut omega_pow = mth_root_of_unity;
		let mut point_pow = *point;
		for i in 0..kappa {
			Psi *= E::ScalarField::one() + omega_pow * point_pow;
			omega_pow = omega_pow * omega_pow;
			point_pow = point_pow * point_pow;
		}
		let res = Psi * eta - (point_pow - E::ScalarField::one()) * (*point - E::ScalarField::one()).inverse().unwrap();
		res
	}

	pub(crate) fn compute_S_hat(V_y: E::ScalarField, eval_for_eta: E::ScalarField, eval_for_delta: E::ScalarField, H_bar: &DensePolynomial<E::ScalarField>, t_hat: &DensePolynomial<E::ScalarField>, A_hat: &DensePolynomial<E::ScalarField>, e_hat_coeffs: &Vec<E::ScalarField>, B_hat_delta_coeffs: &Vec<E::ScalarField>, epsilon: E::ScalarField, m: usize) -> DensePolynomial<E::ScalarField> {
		let domain = Radix2EvaluationDomain::<E::ScalarField>::new(2*m).unwrap();

		let H_bar_evals_at_roots_of_unity = domain.fft(&H_bar);
		let H_bar_rev_evals_at_roots_of_unity = domain.fft(&H_bar.iter().rev().cloned().collect::<Vec<_>>());

		let t_hat_evals_at_roots_of_unity = domain.fft(&t_hat);
		let t_hat_rev_evals_at_roots_of_unity = domain.fft(&t_hat.iter().rev().cloned().collect::<Vec<_>>());

		let A_hat_evals_at_roots_of_unity = domain.fft(&A_hat);
		let A_hat_rev_evals_at_roots_of_unity = domain.fft(&A_hat.iter().rev().cloned().collect::<Vec<_>>());

		let e_hat_evals_at_roots_of_unity = domain.fft(&e_hat_coeffs);
		let e_hat_rev_evals_at_roots_of_unity = domain.fft(&e_hat_coeffs.iter().rev().cloned().collect::<Vec<_>>());

		let B_hat_evals_at_roots_of_unity = domain.fft(&B_hat_delta_coeffs);
		let B_hat_rev_evals_at_roots_of_unity = domain.fft(&B_hat_delta_coeffs.iter().rev().cloned().collect::<Vec<_>>());

		let mut lhs_evals_at_roots_of_unity : Vec<_> = Vec::new();
		for i in 0..(2*m) {
			lhs_evals_at_roots_of_unity.push(
				(H_bar_evals_at_roots_of_unity[i] * t_hat_rev_evals_at_roots_of_unity[i] + H_bar_rev_evals_at_roots_of_unity[i] * t_hat_evals_at_roots_of_unity[i])
				+ epsilon * (A_hat_evals_at_roots_of_unity[i] * e_hat_rev_evals_at_roots_of_unity[i] + A_hat_rev_evals_at_roots_of_unity[i] * e_hat_evals_at_roots_of_unity[i])
				+ epsilon * epsilon * (A_hat_evals_at_roots_of_unity[i] * B_hat_rev_evals_at_roots_of_unity[i] + A_hat_rev_evals_at_roots_of_unity[i] * B_hat_evals_at_roots_of_unity[i]));
		}

		let lhs_coeffs = domain.ifft(&lhs_evals_at_roots_of_unity);

		let S_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(lhs_coeffs[m..(2*m)-1].to_vec());
		S_hat
	}

	pub(crate) fn compute_d_hat(K_hat: &DensePolynomial<E::ScalarField>, h_hat: &DensePolynomial<E::ScalarField>, epsilon: E::ScalarField, n: usize, m: usize) -> DensePolynomial<E::ScalarField> {
		let d_hat = &DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); n - m], K_hat.coeffs().to_vec()].concat().to_vec()) 
			+ &DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); n - m + 1], h_hat.coeffs().to_vec()].concat().to_vec()) * epsilon;
		d_hat
	}

    pub(crate) fn compute_combined_mlp(log_number_of_gates: usize, mlp_ab: &DenseMultilinearExtension<E::ScalarField>, mlp_a: &DenseMultilinearExtension<E::ScalarField>,
    	eval_mlp_b_at_alphas: E::ScalarField, 
    	alphas: &Vec<E::ScalarField>, tau: &Vec<E::ScalarField>) -> DenseMultilinearExtension<E::ScalarField> {
    	let number_of_gates = 1 << log_number_of_gates;

    	let eval_eq_tilde_at_alphas = Self::evaluate_eq_tilde_at_point(log_number_of_gates, &tau, &alphas);

    	let mut combined_mlp_evals: Vec<_> = Vec::new();
    	for i in 0..number_of_gates {
    		let elem = eval_eq_tilde_at_alphas * (mlp_ab[i] - mlp_a[i] * eval_mlp_b_at_alphas);
    		combined_mlp_evals.push(elem);	
    	}
    	DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_number_of_gates, combined_mlp_evals)
    }

    pub fn prove(srs: &SamaritanMLPCS_SRS<E>, log_number_of_gates: usize, mlp_a: &DenseMultilinearExtension<E::ScalarField>, mlp_b: &DenseMultilinearExtension<E::ScalarField>, mlp_ab: &DenseMultilinearExtension<E::ScalarField>) -> Result<ImprovedSumcheckProof<E>, Error> {
    	let log_number_of_gates = log_number_of_gates;
		let number_of_gates = 2usize.pow(log_number_of_gates as u32);
		let number_of_initial_rounds = (log_number_of_gates as f64).log2().ceil() as usize;
		let seed = [42u8; 32];
		let mut rng = StdRng::from_seed(seed);
		
		// let prover_time = start_timer!(|| format!("HyperPlonk::prove with log_number_of_gates {}", log_number_of_gates));
		let mut transcript = Transcript::new(b"HyperPlonk Transcript");

		let mlp_a_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &mlp_a).unwrap();
		util::append_commitment_to_transcript::<E>(&mut transcript, b"mlp_a_commit", &mlp_a_commit);
		let mlp_b_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &mlp_b).unwrap();
		util::append_commitment_to_transcript::<E>(&mut transcript, b"mlp_b_commit", &mlp_b_commit);
		let mlp_ab_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &mlp_ab).unwrap();
		util::append_commitment_to_transcript::<E>(&mut transcript, b"mlp_ab_commit", &mlp_ab_commit);

		// let xi = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"xi");
		let tau = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"tau", log_number_of_gates);

		let mut eq_tilde = Self::compute_eq_tilde(log_number_of_gates, &tau);

		/* Deep copy or clone is done here, since we keep on squeezing the Boolean hypercube by replaing variables with randomly chosen field element one after another. 
		But we require original multilinear polynomials (e.q., w1_tilde, w2_tilde, w3_tilde, v_0_tilde, v_1_tilde, u_0_tilde, u_1_tilde) later 
		to generate evaluation proofs */

		let mut mlp_a_copy = mlp_a.clone();
		let mut mlp_b_copy = mlp_b.clone();
		let mut mlp_ab_copy = mlp_ab.clone();
		

		let mut mlp_set = vec![&mut eq_tilde, &mut mlp_a_copy, &mut mlp_b_copy,
			 &mut mlp_ab_copy];

		let mut coeffs: Vec<_> = Vec::new();
		let mut alphas: Vec<_> = Vec::new();
		
		for i in 0..number_of_initial_rounds {
		    // we use 1,2,..,5 as the evaluation points, then at verifier end evaluation at zero is determined by subtracting evaluation at one from previous round evaluation 
			let d_plus_one_evaluation_points = (1..=3).map(|x| E::ScalarField::from(x as u64)).collect::<Vec<_>>();
			if i > 0 {
				let alpha = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha");
				for mlp in mlp_set.iter_mut() {
					**mlp = (*mlp).fix_variables(&[alpha]);
				}
				alphas.push(alpha);
			}
			let mut d_plus_one_evaluations = vec![E::ScalarField::zero(); d_plus_one_evaluation_points.len()];
			for j in 0..d_plus_one_evaluation_points.len() {
				d_plus_one_evaluations[j] = Self::compute_univariate_r_X_evaluation(&mut mlp_set, d_plus_one_evaluation_points[j]);
			}
			util::append_field_element_vector_to_transcript::<E>(&mut transcript, b"d_plus_one_evaluations", &d_plus_one_evaluations);
			coeffs.push(d_plus_one_evaluations);
		}
		let alpha_nu = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_nu");
		for mlp in mlp_set.iter_mut() {
			**mlp = (*mlp).fix_variables(&[alpha_nu]);
		}
		alphas.push(alpha_nu);

		// O_tilde_set is the set of several multilinear polynomials, each with first few variables fixed to alphas
		let mut O_tilde_set : Vec<_> = Vec::new();
		for mlp in mlp_set {
			O_tilde_set.push(mlp);
		}

		let kappa = log_number_of_gates - number_of_initial_rounds;
		let m = (1 << kappa) as usize;

	    // O_bar_set is the set containing inverse ffts of several univariate polynomials which correspond to the multilinear polynomials in O_tilde_set

	    let domain = Radix2EvaluationDomain::<E::ScalarField>::new(m).unwrap();
	    let mut O_bar_set : Vec<_> = Vec::new();
	    for O_tilde in &O_tilde_set {
	    	O_bar_set.push(DensePolynomial::<E::ScalarField>::from_coefficients_vec(domain.ifft(&O_tilde.to_evaluations())));
	    }

	    let G_bar = Self::compute_G_bar_from_O_bar_set(&O_bar_set);

	    /* divisor = (X^m - 1), schoolbook division, with only two coefficients getting affected in each iteration.*/
	    let mut G_bar_coeffs = (&G_bar).coeffs.clone();
	    let mut g_hat_coeffs: Vec<_> = Vec::new();
        for i in (m..G_bar_coeffs.len()).rev() {
            let quotient = G_bar_coeffs[i];
            g_hat_coeffs.push(quotient);
            G_bar_coeffs[i] = E::ScalarField::zero();
            G_bar_coeffs[i - m] += quotient;
        }
        let rem_const = G_bar_coeffs[0];
        let h_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(G_bar_coeffs[1..].to_vec());
        let g_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(g_hat_coeffs.iter().rev().cloned().collect::<Vec<_>>());

	    let g_hat_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &g_hat).unwrap();
	    let h_hat_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &h_hat).unwrap();

	    util::append_commitment_to_transcript::<E>(&mut transcript, b"g_hat_commit", &g_hat_commit);
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"h_hat_commit", &h_hat_commit);

	    let z = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"z");

	    let V_eq = O_bar_set[0].evaluate(&z);
	    let V_mlp_a = O_bar_set[1].evaluate(&z);
	    let V_mlp_b = O_bar_set[2].evaluate(&z);
	    let V_mlp_ab = O_bar_set[3].evaluate(&z);

	    let G_prime = Self::compute_G_prime(&O_bar_set, &g_hat, &h_hat, z, m, V_eq, V_mlp_b);

	    let alpha_ = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_");
	    let mut alpha_powers : Vec<E::ScalarField> = Vec::new();
	    let mut cur = alpha_;
	    for i in 0..4 {
	    	alpha_powers.push(cur);
	    	cur = cur * alpha_;
	    }

	    let F_bar = Self::compute_F_bar(&O_bar_set, &G_prime, &alpha_powers);

	    let F_bar_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &F_bar).unwrap();
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"F_bar_commit", &F_bar_commit);

	    let F_bar_eval_proof = SamaritanMLPCS::<E>::kzg10_eval_prove(&srs, &F_bar, z).unwrap();

	    let a_vec = vec![alpha_powers[0], alpha_powers[1] - V_eq * V_mlp_b, alpha_powers[2], alpha_powers[3] + V_eq];

	    let H_bar = Self::compute_H_bar(&O_bar_set, &a_vec);

	    let H_bar_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &H_bar).unwrap();

	    util::append_commitment_to_transcript::<E>(&mut transcript, b"H_bar_commit", &H_bar_commit);

	    let K_hat = Self::compute_K_hat(&O_tilde_set, &a_vec);

	    let K_hat_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &K_hat).unwrap();

	    util::append_commitment_to_transcript::<E>(&mut transcript, b"K_hat_commit", &K_hat_commit);

	    let mut K_ext_hat_coeffs : Vec<E::ScalarField> = Vec::new();
	    for coeff in &K_hat.coeffs {
	    	for i in 0..(1 << number_of_initial_rounds) {
	    		K_ext_hat_coeffs.push(*coeff);
	    	}
	    }
	    let K_ext_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(K_ext_hat_coeffs);
	    let K_ext_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_number_of_gates, K_ext_hat.coeffs().to_vec());

	    let K_ext_hat_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &K_ext_hat).unwrap();

	    util::append_commitment_to_transcript::<E>(&mut transcript, b"K_ext_hat_commit", &K_ext_hat_commit);

	    let y = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"y", kappa);

	    let mut eval_point = Vec::new();
	    eval_point.extend_from_slice(&alphas);
	    eval_point.extend_from_slice(&y);
	    let V_y = K_ext_tilde.evaluate(&eval_point);

	    let e_hat_coeffs = Self::compute_e_hat_coeffs(kappa, &y);

	    let t_hat = Self::compute_t_hat(m, &e_hat_coeffs);

	    let t_hat_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &t_hat).unwrap();
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"t_hat_commit", &t_hat_commit);

	    let eta = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"eta");
	    let eval_for_eta = t_hat.evaluate(&eta) * (eta.pow(&[m as u64]) - E::ScalarField::one()).inverse().unwrap();
	    
	    let A_hat = Self::compute_A_hat(eta, m);

	    let A_hat_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &A_hat).unwrap();
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"A_hat_commit", &A_hat_commit);

	    let delta = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"delta");
	    let eval_for_delta = (delta.pow(&[m as u64]) - E::ScalarField::one()) * (delta - E::ScalarField::one()).inverse().unwrap();

	    let B_hat_delta_coeffs = Self::compute_B_hat_delta_coeffs(&A_hat, delta, m);

	    let epsilon = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"epsilon");

	    let S_hat = Self::compute_S_hat(V_y, eval_for_eta, eval_for_delta, &H_bar, &t_hat, &A_hat, &e_hat_coeffs, &B_hat_delta_coeffs, epsilon, m);

	    let S_hat_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &S_hat).unwrap();
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"S_hat_commit", &S_hat_commit);

	    let d_hat = Self::compute_d_hat(&K_hat, &h_hat, epsilon, number_of_gates, m);

	    let d_hat_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &d_hat).unwrap();
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"d_hat_commit", &d_hat_commit);

	    let max_deg = number_of_gates;

	    let D_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); max_deg - number_of_gates + 1], d_hat.coeffs().to_vec()].concat().to_vec());

	    let D_hat_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &D_hat).unwrap();
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"D_hat_commit", &D_hat_commit);

	    let r = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"r");
	    let r_inverse = r.inverse().unwrap();

	    // let W1 = (&v0_hat + &v1_hat * r).evaluate(&r.pow(&[2 as u64]));
	    let W2 = K_hat.evaluate(&r.pow(&[(1 << number_of_initial_rounds) as u64]));
	    let W3 = t_hat.evaluate(&r_inverse);
	    let W4 = H_bar.evaluate(&r_inverse);
	    let W5 = A_hat.evaluate(&r_inverse);
	    let W6 = S_hat.evaluate(&r_inverse);

	    let B_hat_delta_inv_eval = Self::evaluate_B_hat_at_point(&eta, &(delta * r_inverse), kappa);

	    let e_hat_inv_eval = Self::evaluate_e_hat_at_point(kappa, &y, &r_inverse);

	    let S_equality_left = (&H_bar * W3 + &t_hat * W4) + (&A_hat * e_hat_inv_eval) * epsilon + (&A_hat * B_hat_delta_inv_eval) * epsilon * epsilon - &S_hat * r;

	    let deg_check_left = &d_hat - &K_hat * r.pow(&[(number_of_gates - m) as u64]) - &h_hat * r.pow(&[(number_of_gates - m + 1) as u64]) * epsilon;

	    let phi = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"phi");

	    let L_hat = K_ext_hat + S_equality_left * phi + deg_check_left * phi.pow(&[2 as u64]);

	    let L_hat_eval_proof = SamaritanMLPCS::<E>::kzg10_eval_prove(&srs, &L_hat, r).unwrap();

	    let eq_tilde_val = Self::evaluate_eq_tilde_at_point(log_number_of_gates, &tau, &eval_point);

		let mut linear_combined_orig_mlps_and_K_ext_tilde_evals: Vec<_> = Vec::new();
		for i in 0..number_of_gates {
			let term = mlp_a[i] * a_vec[1] + mlp_b[i] * a_vec[2] + mlp_ab[i] * a_vec[3] + K_ext_tilde[i] * epsilon;
			linear_combined_orig_mlps_and_K_ext_tilde_evals.push(term);
		}

		let combined_mlp = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_number_of_gates, linear_combined_orig_mlps_and_K_ext_tilde_evals);
		let combined_mlp_eval = (E::ScalarField::one() + epsilon) * V_y - eq_tilde_val * a_vec[0];
		let combined_mlp_eval_proof = SamaritanMLPCS::<E>::prove(&srs, &combined_mlp, &eval_point, combined_mlp_eval, &mut rng).unwrap();

		let proof = ImprovedSumcheckProof{
			number_of_initial_rounds,
			mlp_a_commit,
			mlp_b_commit,
			mlp_ab_commit,
			coeffs,
			g_hat_commit,
			h_hat_commit,
			V_eq,
			V_mlp_a,
			V_mlp_b,
			V_mlp_ab,
			F_bar_commit,
			F_bar_eval_proof,
			H_bar_commit,
			K_hat_commit,
			K_ext_hat_commit,
			V_y,
			t_hat_commit,
			eval_for_eta,
			A_hat_commit,
			eval_for_delta,
			S_hat_commit,
			d_hat_commit,
			D_hat_commit,
			// W1,
			W2,
			W3,
			W4,
			W5,
			W6,
			combined_mlp_eval_proof,
			L_hat_eval_proof,
		};
		// end_timer!(prover_time);
		Ok(proof)
    }

    pub fn verify(proof: &ImprovedSumcheckProof<E>, srs: &SamaritanMLPCS_SRS<E>, log_number_of_gates: usize) -> Result<bool, Error> {
		// let verifier_time = start_timer!(|| format!("HyperPlonk::verify with multilinear polynomial"));

        let mut transcript = Transcript::new(b"HyperPlonk Transcript");

        let number_of_gates = 1 << log_number_of_gates;
        let number_of_initial_rounds = proof.number_of_initial_rounds;

        let kappa = log_number_of_gates - number_of_initial_rounds;
		let m = 1 << kappa;

        util::append_commitment_to_transcript::<E>(&mut transcript, b"mlp_a_commit", &proof.mlp_a_commit);
        util::append_commitment_to_transcript::<E>(&mut transcript, b"mlp_b_commit", &proof.mlp_b_commit);
        util::append_commitment_to_transcript::<E>(&mut transcript, b"mlp_ab_commit", &proof.mlp_ab_commit);

		let tau = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"tau", log_number_of_gates);
		let mut alphas: Vec<_> = Vec::new();
		let mut cur_eval_value = E::ScalarField::zero();
        let mut d_plus_one_evaluation_points = (1..=3).map(|x| E::ScalarField::from(x as u64)).collect::<Vec<_>>();
        d_plus_one_evaluation_points.push(E::ScalarField::zero());
		
		for i in 0..proof.number_of_initial_rounds {

            if i > 0 {
				let alpha = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha");
				alphas.push(alpha);
				let mut coeffs = proof.coeffs[i-1].clone();
				coeffs.push(cur_eval_value - coeffs[0]);
				cur_eval_value = Self::compute_evaluation_through_lagrange_interpolation(&d_plus_one_evaluation_points, &coeffs, alpha);
			}
			util::append_field_element_vector_to_transcript::<E>(&mut transcript, b"d_plus_one_evaluations", &proof.coeffs[i]);
		}
		let alpha_nu = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_nu");

		let mut final_poly_coeffs = proof.coeffs[proof.number_of_initial_rounds-1].clone();
		final_poly_coeffs.push(cur_eval_value- final_poly_coeffs[0]);

		cur_eval_value = Self::compute_evaluation_through_lagrange_interpolation(&d_plus_one_evaluation_points, &final_poly_coeffs, alpha_nu);
		alphas.push(alpha_nu);

		util::append_commitment_to_transcript::<E>(&mut transcript, b"g_hat_commit", &proof.g_hat_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"h_hat_commit", &proof.h_hat_commit);
		let z = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"z");

		let alpha_ = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_");
		let mut alpha_powers : Vec<E::ScalarField> = Vec::new();
	    let mut cur = alpha_;
	    for i in 0..4 {
	    	alpha_powers.push(cur);
	    	cur = cur * alpha_;
	    }

	    let V = proof.V_eq * alpha_powers[0] + proof.V_mlp_a * alpha_powers[1] + proof.V_mlp_b * alpha_powers[2] + proof.V_mlp_ab * alpha_powers[3]
	    		+ cur_eval_value * E::ScalarField::from(m as u64).inverse().unwrap();
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"F_bar_commit", &proof.F_bar_commit);
	    let F_bar_equality_check = SamaritanMLPCS::<E>::kzg10_eval_proof_verify(&srs, &proof.F_bar_commit, z, V, &proof.F_bar_eval_proof).unwrap();

	    util::append_commitment_to_transcript::<E>(&mut transcript, b"H_bar_commit", &proof.H_bar_commit);
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"K_hat_commit", &proof.K_hat_commit);
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"K_ext_hat_commit", &proof.K_ext_hat_commit);

	    let y = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"y", kappa);

	    util::append_commitment_to_transcript::<E>(&mut transcript, b"t_hat_commit", &proof.t_hat_commit);

	    let eta = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"eta");

	    util::append_commitment_to_transcript::<E>(&mut transcript, b"A_hat_commit", &proof.A_hat_commit);

	    let delta = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"delta");

	    let epsilon = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"epsilon");

	    util::append_commitment_to_transcript::<E>(&mut transcript, b"S_hat_commit", &proof.S_hat_commit);

	    util::append_commitment_to_transcript::<E>(&mut transcript, b"d_hat_commit", &proof.d_hat_commit);

	    util::append_commitment_to_transcript::<E>(&mut transcript, b"D_hat_commit", &proof.D_hat_commit);

	    let r = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"r");

	    let K_ext_hat_eval = proof.W2 * (r.pow(&[(1 << number_of_initial_rounds) as u64]) - E::ScalarField::from(1 as u64)) * (r - E::ScalarField::from(1 as u64)).inverse().unwrap();

	    let r_inverse = r.inverse().unwrap();

	    let B_hat_delta_eval = Self::evaluate_B_hat_at_point(&eta, &(delta * r), kappa);
	    let B_hat_delta_inv_eval = Self::evaluate_B_hat_at_point(&eta, &(delta * r_inverse), kappa);

	    let e_hat_eval = Self::evaluate_e_hat_at_point(kappa, &y, &r);
	    let e_hat_inv_eval = Self::evaluate_e_hat_at_point(kappa, &y, &r_inverse);

		let combined_eval = (proof.V_y + proof.eval_for_eta * epsilon + proof.eval_for_delta * epsilon * epsilon) * E::ScalarField::from(2 as u64) + r_inverse * proof.W6 - epsilon * proof.W5 * e_hat_eval - epsilon * epsilon * proof.W5 * B_hat_delta_eval;

	    let max_deg = number_of_gates + 1;

	    let phi = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"phi");

	    let comm_list = vec![ 
	    			proof.K_ext_hat_commit.0, 
	    			proof.H_bar_commit.0, proof.t_hat_commit.0, 
	    			proof.A_hat_commit.0, proof.S_hat_commit.0, 
	    			proof.d_hat_commit.0, proof.K_hat_commit.0, proof.h_hat_commit.0];
	    let scalar_list = vec![
	    			E::ScalarField::one(), 
	    			proof.W3 * phi, proof.W4 * phi,
	    			(epsilon * epsilon * B_hat_delta_inv_eval + epsilon * e_hat_inv_eval) * phi, - (r * phi),
	    			phi.pow(&[2 as u64]), 
	    			- (r.pow(&[(number_of_gates - m) as u64]) * phi.pow(&[2 as u64])), - (r.pow(&[(number_of_gates - m + 1) as u64]) * epsilon * phi.pow(&[2 as u64]))];

	    let phi_combined_univariates_commit = Commitment(E::G1::msm(&comm_list, &scalar_list).unwrap().into_affine());
	    let phi_combined_eval = K_ext_hat_eval + combined_eval * phi;
	    let L_equality_check = SamaritanMLPCS::<E>::kzg10_eval_proof_verify(&srs, &phi_combined_univariates_commit, r, phi_combined_eval, &proof.L_hat_eval_proof).unwrap();

	    let pairing_lhs_first = E::G1Prepared::from(proof.d_hat_commit.0);
        let pairing_lhs_second = srs.powers_of_h[max_deg - number_of_gates];
        let pairing_lhs_res = E::pairing(pairing_lhs_first, pairing_lhs_second);

        let pairing_rhs_first = E::G1Prepared::from(proof.D_hat_commit.0);
        let pairing_rhs_second = srs.powers_of_h[0];
        let pairing_rhs_res = E::pairing(pairing_rhs_first, pairing_rhs_second);

        let mut eval_point = Vec::new();
	    eval_point.extend_from_slice(&alphas);
	    eval_point.extend_from_slice(&y);

	    let a_vec = vec![alpha_powers[0], alpha_powers[1] - proof.V_eq * proof.V_mlp_b, alpha_powers[2], alpha_powers[3] + proof.V_eq];

	    let eq_tilde_val = Self::evaluate_eq_tilde_at_point(log_number_of_gates, &tau, &eval_point);

		let combined_mlp_commit = Commitment(E::G1::msm(
	    							&vec![proof.mlp_a_commit.0, proof.mlp_b_commit.0, proof.mlp_ab_commit.0,
		    							proof.K_ext_hat_commit.0],
		    						&vec![a_vec[1], a_vec[2], a_vec[3], epsilon]
		    						).unwrap().into_affine());

		let combined_mlp_eval = (E::ScalarField::one() + epsilon) * proof.V_y - eq_tilde_val * a_vec[0];
		let combined_mlp_check = SamaritanMLPCS::<E>::verify(&srs, &combined_mlp_commit, &eval_point, combined_mlp_eval, &proof.combined_mlp_eval_proof).unwrap();

        // end_timer!(verifier_time);
        // Note that L_equality_check includes uv_equality_check, K_ext_hat_equality_check, S_equality_check, and deg_check together.
        Ok(F_bar_equality_check && L_equality_check && combined_mlp_check && pairing_lhs_res == pairing_rhs_res)
	}
}
#[cfg(test)]
mod tests {
    // #![allow(non_camel_case_types)]
    use ark_poly_commit::kzg10::*;
    use ark_poly_commit::*;
    use ark_ec::pairing::Pairing;
    use ark_bls12_381::Bls12_381;
    use ark_bls12_381::Fr;
    // use ark_bn254::Bn254;
    // use ark_bn254::Fr;
    use ark_std::test_rng;
    use crate::improved_sumcheck::*;

    type ImprovedSumcheck_Bls12_381 = ImprovedSumcheck<Bls12_381>;
    // type SamaritanMLPCS_Bn254 = SamaritanMLPCS<Bn254>;

    #[test]
    fn functionality_test() {
        let mut rng = &mut test_rng();
        let log_number_of_gates = 4;
        let num_of_gates = 1 << log_number_of_gates;

        let mlp_a = DenseMultilinearExtension::rand(log_number_of_gates, rng);

        let mlp_b = DenseMultilinearExtension::rand(log_number_of_gates, rng);

        let mut ab_vec: Vec<_> = Vec::new();
        for i in 0..num_of_gates {
        	// println!("i: {}, term: {}", i, mlp_a[i] * mlp_b[i]);
        	ab_vec.push(Fr::from(mlp_a[i] * mlp_b[i]));
        }
        let mlp_ab = DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, ab_vec);

        // let mut c_vec: Vec<_> = Vec::new();
        // for i in 0..num_of_gates {
        // 	c_vec.push(Fr::zero());
        // }
        // mlp_c = DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, c_vec);

        let srs = ImprovedSumcheck_Bls12_381::setup(&mut rng, log_number_of_gates).unwrap();

		let improved_sumcheck_proof = ImprovedSumcheck_Bls12_381::prove(&srs, log_number_of_gates, &mlp_a, &mlp_b, &mlp_ab).unwrap();

    	let valid = ImprovedSumcheck_Bls12_381::verify(&improved_sumcheck_proof, &srs, log_number_of_gates).unwrap();

        assert_eq!(valid, true);
    }
}