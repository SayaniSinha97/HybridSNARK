use ark_poly_commit::kzg10::*;
use ark_poly_commit::error::Error;
use ark_ec::pairing::Pairing;
use ark_poly::polynomial::Polynomial;
use ark_ff::fields::Field;
use ark_poly::DenseUVPolynomial;
use ark_poly::univariate::DensePolynomial;
use ark_poly::evaluations::multivariate::multilinear::MultilinearExtension;
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension;
use ark_std::{start_timer, end_timer, Zero, One, marker::PhantomData};
use ark_std::{UniformRand};
use ark_std::rand::rngs::StdRng;
use ark_std::rand::{SeedableRng, RngCore};
use merlin::Transcript;
use ark_ff::BigInteger;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use ark_poly_commit::PCCommitmentState;
use crate::samaritan_mlpcs::*;
use crate::degree_check::*;
use crate::util;
use ark_ec::VariableBaseMSM;
use ark_ec::CurveGroup;
use ark_ff::batch_inversion;
use ark_poly::EvaluationDomain;
use ark_poly::Radix2EvaluationDomain;
use ark_ff::FftField;

#[derive(Clone)]
pub struct eq_tilde_eval_info<E: Pairing> {
	pub index: usize,
	pub tau: Vec<E::ScalarField>,
}

/* As we are dealing with multivariate sumcheck, "max_degree" denotes the maximum degree of any variable involved in the multivariate. 
"mlp_set" is the vector of all multilinear polynomials in the "function of multilinear polynomials" form (G_tilde) of the multivariate sumcheck.
"mark_if_eval_reqd_in_linear_combination" says if the polynomial is retained in linear combination, or is replaced by its evaluation at z. 
"rhs" is the sum, or simply the right-hand-side of the given sumcheck relation. 
"G_tilde_description" : a description of G_tilde in terms only field operations.
"G_tilde_description_poly" : same description but in terms of small m-sized polynomials. 
"G_bar_linear_combine" : description of G_tilde, where for each mulplication at most one polynomial remains, and ohers are replaced with their values 
at certain verifier-chosen point. That is how it becomes linear combination of a few polynomials from the reduced length set corresponding to mlp_set.*/
pub struct SumcheckRelation<E: Pairing> {
	pub log_number_of_vars: usize,
	pub max_degree: usize,
	pub mlp_set: Vec<DenseMultilinearExtension<E::ScalarField>>,
	pub commit_list: Vec<Option<Commitment<E>>>,
    pub eq_tilde_eval_infos: Vec<eq_tilde_eval_info<E>>,
	pub rhs: E::ScalarField,
	pub additional_field_elements: Vec<E::ScalarField>,
	pub G_tilde_description: fn(Vec<E::ScalarField>, &Vec<E::ScalarField>) -> E::ScalarField,
	pub G_tilde_description_poly: fn(&Vec<DensePolynomial<E::ScalarField>>, &Vec<E::ScalarField>) -> DensePolynomial<E::ScalarField>,
	pub G_bar_linear_combine: fn(&Vec<DensePolynomial<E::ScalarField>>, &Vec<Option<E::ScalarField>>, &Vec<E::ScalarField>) -> DensePolynomial<E::ScalarField>,
	// pub G_tilde_combined_commit: fn(Vec<Option<Commitment<E>>>, Vec<Option<E::ScalarField>>, &Vec<E::ScalarField>) -> Commitment<E>,
}

pub struct GenericImprovedSumcheckProof<E: Pairing> {
	log_number_of_gates: usize,
	max_degree: usize,
	rhs: E::ScalarField,
	G_tilde_description: fn(Vec<E::ScalarField>, &Vec<E::ScalarField>) -> E::ScalarField,
	additional_field_elements: Vec<E::ScalarField>,
	eq_tilde_eval_infos: Vec<eq_tilde_eval_info<E>>,
    // actual proof size count starts from here, previous elements can be considered as public parameter; clubbed inside proof structure for ease of implementation
	coeffs: Vec<Vec<E::ScalarField>>,
	g_hat_commit: Commitment<E>,
	h_hat_commit: Commitment<E>,
	rem_const: E::ScalarField,
	small_poly_evals_at_z: Vec<E::ScalarField>,
	g_hat_h_hat_correctness_eval_proof: KZG10EvalProof<E>,
	beta_power_combined_smaller_mlp_commit: Commitment<E>,
	beta_power_combined_smaller_mlp_ext_commit: Commitment<E>,
	combined_mlp_proof: SamaritanMLPCSEvalProof<E>,
	A_hat_z_commit: Commitment<E>,
	S_hat_commit: Commitment<E>,
	v_eta: E::ScalarField,
	p_hat_inv_eval: E::ScalarField,
	A_hat_z_inv_eval: E::ScalarField,
	S_hat_inv_eval: E::ScalarField,
	S_equality_left_eval_proof: KZG10EvalProof<E>,
	deg_check_proof: DegreeCheckProof<E>,
}

pub struct GenericImprovedSumcheck<E: Pairing> {
	_engine: PhantomData<E>,
}

impl<E: Pairing> GenericImprovedSumcheck<E> {

	pub(crate) fn compute_univariate_r_X_evaluation(G_tilde_description: fn(Vec<E::ScalarField>, &Vec<E::ScalarField>) -> E::ScalarField, mlp_set: &mut Vec<DenseMultilinearExtension<E::ScalarField>>, eval_point: E::ScalarField, additional_field_elements: &Vec<E::ScalarField>) -> E::ScalarField {
		let mut tmp : Vec<_> = Vec::new();
		for mlp in mlp_set.iter_mut() {
			let tmp_poly = (*mlp).fix_variables(&[eval_point]);
			tmp.push(tmp_poly);
		}
		let mut G_tilde_params: Vec<_> = vec![vec![E::ScalarField::zero(); tmp.len()]; tmp[0].to_evaluations().len()];
		for i in 0..G_tilde_params.len() {
			for j in 0..tmp.len() {
				G_tilde_params[i][j] = tmp[j][i];
			} 
		}
		let mut res = vec![E::ScalarField::zero(); tmp[0].to_evaluations().len()];
		for i in 0..G_tilde_params.len() {
			res[i] = G_tilde_description(G_tilde_params[i].clone(), additional_field_elements);
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

	// A_hat_z_coeffs[i] = omega^i/(z - omega^i) and B_hat_z_delta_coeffs[i] = ((z - omega^i) * delta^i)/omega^i = A_hat_z_coeffs[i].inverse() * delta^i
	pub(crate) fn compute_A_hat_z_and_B_hat_z_delta_coeffs(z: E::ScalarField, delta: E::ScalarField, m: usize) -> (DensePolynomial<E::ScalarField>, Vec<E::ScalarField>) {
		let domain = Radix2EvaluationDomain::<E::ScalarField>::new(m).unwrap();
		let roots: Vec<E::ScalarField> = domain.elements().collect();

		let mut coeffs = Vec::new();
		let mut delta_powers = Vec::new();
		let mut cur = E::ScalarField::one();
		for i in 0..m {
		    coeffs.push(z - roots[i]);
		    delta_powers.push(cur);
		    cur = cur * delta;
		}
		batch_inversion(&mut coeffs);
		for i in 0..m {
			coeffs[i] = coeffs[i] * roots[i];
		}
		let A_hat_z = DensePolynomial::<E::ScalarField>::from_coefficients_vec(coeffs.clone());

		batch_inversion(&mut coeffs);
		for i in 0..m {
			coeffs[i] = coeffs[i] * delta_powers[i];
		}

		(A_hat_z, coeffs) 
	}

	pub(crate) fn evaluate_B_hat_z_at_point(z: &E::ScalarField, point: &E::ScalarField, kappa: usize) -> E::ScalarField {
		let m = 1 << kappa;
		let mth_root_of_unity = E::ScalarField::get_root_of_unity(m.try_into().unwrap()).unwrap();
		let mut omega_inv_pow = mth_root_of_unity.inverse().unwrap();
		let mut point_pow = *point;
		let mut Psi = E::ScalarField::one();
				
		for i in 0..kappa {
			Psi *= E::ScalarField::one() + omega_inv_pow * point_pow;
			omega_inv_pow = omega_inv_pow * omega_inv_pow;
			point_pow = point_pow * point_pow;
		}
		let res = Psi * z - (point_pow - E::ScalarField::one()) * (*point - E::ScalarField::one()).inverse().unwrap();
		res
	}

	/* p_hat(X) * A_hat_z(1/X) + p_hat(1/X) * A_hat_z(X) + epsilon * (A_hat_z(X) * B_hat_z(delta/X) + A_hat_z(1/X) * B_hat_z(delta * X)) = 2 * (mv/(z^m -1) + epsilon * (delta^m - 1)/(delta - 1)) + X * S_hat(X) + (1/X) * S_hat(1/X) 
	The logic for computing S_hat is taken from Eagen-Gabizon Mercury paper. */
	pub(crate) fn compute_S_hat(p_hat: &DensePolynomial<E::ScalarField>, A_hat: &DensePolynomial<E::ScalarField>, B_hat_delta_coeffs: &Vec<E::ScalarField>, epsilon: E::ScalarField, m: usize) -> DensePolynomial<E::ScalarField> {
		let domain = Radix2EvaluationDomain::<E::ScalarField>::new(2*m).unwrap();

		let p_hat_evals_at_roots_of_unity = domain.fft(&p_hat);
		let p_hat_rev_evals_at_roots_of_unity = domain.fft(&p_hat.iter().rev().cloned().collect::<Vec<_>>());

		let A_hat_evals_at_roots_of_unity = domain.fft(&A_hat);
		let A_hat_rev_evals_at_roots_of_unity = domain.fft(&A_hat.iter().rev().cloned().collect::<Vec<_>>());

		let B_hat_evals_at_roots_of_unity = domain.fft(&B_hat_delta_coeffs);
		let B_hat_rev_evals_at_roots_of_unity = domain.fft(&B_hat_delta_coeffs.iter().rev().cloned().collect::<Vec<_>>());	

		let mut lhs_evals_at_roots_of_unity : Vec<_> = Vec::new();
		for i in 0..(2*m) {
			lhs_evals_at_roots_of_unity.push(
				p_hat_evals_at_roots_of_unity[i] * A_hat_rev_evals_at_roots_of_unity[i] + p_hat_rev_evals_at_roots_of_unity[i] * A_hat_evals_at_roots_of_unity[i]
				+ epsilon * (A_hat_evals_at_roots_of_unity[i] * B_hat_rev_evals_at_roots_of_unity[i] + A_hat_rev_evals_at_roots_of_unity[i] * B_hat_evals_at_roots_of_unity[i])
			);
		}

		let lhs_coeffs = domain.ifft(&lhs_evals_at_roots_of_unity);

		let S_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(lhs_coeffs[m..(2*m)-1].to_vec());
		S_hat
	}

	/* This function directly returns evaluation of eq_tilde at a point eval_point, without looking at individual hypercube evaluations of eq_tilde. Runtime is O(log(n)). */
	pub(crate) fn evaluate_eq_tilde_at_point(log_number_of_gates: usize, tau: &Vec<E::ScalarField>, eval_point: &Vec<E::ScalarField>) -> E::ScalarField {
		let mut res = E::ScalarField::one();
		for i in 0..log_number_of_gates {
			res = res * (tau[i] * eval_point[i] + (E::ScalarField::one() - tau[i]) * (E::ScalarField::one() - eval_point[i]));
		}
		res
	}

	pub fn compute_ext_commit(srs: &SamaritanMLPCS_SRS<E>, poly: &DensePolynomial<E::ScalarField>, number_of_initial_rounds: usize) -> Commitment<E> {
		let mut modified_bases = Vec::new();
		let rep_count = 1 << number_of_initial_rounds;
		for i in 0..poly.coeffs().len() {
			let mut tmp = E::G1::zero();
			for j in &srs.powers_of_g[(i * rep_count)..((i+1) * rep_count)] {
				tmp += j;
			}
			modified_bases.push(tmp.into_affine());
		}
		let comm = Commitment(E::G1::msm(&modified_bases, &poly.coeffs()).unwrap().into_affine());
		comm
	}

    pub fn prove(srs: &SamaritanMLPCS_SRS<E>, sumcheck_relation: &SumcheckRelation<E>) -> Result<GenericImprovedSumcheckProof<E>, Error> {

    	let prover_time = start_timer!(|| format!("GenericImprovedSumcheck::prove with log_number_of_vars {}", sumcheck_relation.log_number_of_vars));
		let mut transcript = Transcript::new(b"GenericImprovedSumcheck Transcript");

    	let log_number_of_gates = sumcheck_relation.log_number_of_vars;
		let number_of_gates = 1 << log_number_of_gates;
		let num_initial_rounds = (log_number_of_gates as f64).log2().ceil() as usize;

		let num_polys = sumcheck_relation.mlp_set.len();
		let mlp_set = &sumcheck_relation.mlp_set;

		let additional_field_elements = &sumcheck_relation.additional_field_elements;
		
		let seed = [42u8; 32];
		let mut rng = StdRng::from_seed(seed);

		let mut mlp_set_: Vec<DenseMultilinearExtension<E::ScalarField>> = Vec::new();
		for i in 0..num_polys {
			mlp_set_.push(sumcheck_relation.mlp_set[i].clone());
		}

		//======================================================================================================================
		/* The sumcheck phase for num_initial_rounds [PHASE - 0]*/

		let mut coeffs: Vec<_> = Vec::new();
		let mut alphas: Vec<_> = Vec::new();
		for i in 0..num_initial_rounds {
			let d_plus_one_evaluation_points = (1..=sumcheck_relation.max_degree).map(|x| E::ScalarField::from(x as u64)).collect::<Vec<_>>();
			if i > 0 {
				let alpha = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha");
				for mlp in mlp_set_.iter_mut() {
					*mlp = mlp.fix_variables(&[alpha]);
				}
				alphas.push(alpha);
			}
			let mut d_plus_one_evaluations = vec![E::ScalarField::zero(); d_plus_one_evaluation_points.len()];
			for j in 0..d_plus_one_evaluation_points.len() {
				d_plus_one_evaluations[j] = Self::compute_univariate_r_X_evaluation(sumcheck_relation.G_tilde_description, &mut mlp_set_, d_plus_one_evaluation_points[j], &additional_field_elements);
			}
			util::append_field_element_vector_to_transcript::<E>(&mut transcript, b"d_plus_one_evaluations", &d_plus_one_evaluations);
			coeffs.push(d_plus_one_evaluations);
		}
		let alpha_nu = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_nu");
		for mlp in mlp_set_.iter_mut() {
			*mlp = mlp.fix_variables(&[alpha_nu]);
		}
		alphas.push(alpha_nu);
		
		//==============================================================================================
		let kappa = log_number_of_gates - num_initial_rounds;
		let m = (1 << kappa) as usize;

		//======================================================================================================================
		/* Univariate sumcheck phase starts : [PHASE - 1] */
	    /* O_bar_set is the set containing inverse ffts of several univariate polynomials which correspond to the multilinear polynomials in mlp_set_. 
	    	mlp_set_[i] is basically p_tilde_i(X) for i\in[\ell] in the paper, and
	    	O_bar_set[i] is basically q_hat_i(X) = ifft(p_hat_i(X)) for i\in[\ell], in the paper. */

	    let domain = Radix2EvaluationDomain::<E::ScalarField>::new(m).unwrap();
	    let mut O_bar_set : Vec<_> = Vec::new();
	    for mlp in &mlp_set_ {
	    	O_bar_set.push(DensePolynomial::<E::ScalarField>::from_coefficients_vec(domain.ifft(&mlp.to_evaluations())));
	    }

	    //======================================================================================================================
	    /* compute g_hat and h_hat from G_bar */

	    let G_bar = (sumcheck_relation.G_tilde_description_poly)(&O_bar_set, &additional_field_elements);

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

	    //======================================================================================================================
	    /* sample a random element z, evaluate all the q_hat_i(x) for i\in[\ell], and send them to verifier. */

	    let z = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"z");
	    let mut small_poly_evals_at_z = Vec::new();
	    for i in 0..num_polys {
	    	small_poly_evals_at_z.push(O_bar_set[i].evaluate(&z));
	    }
	    util::append_field_element_vector_to_transcript::<E>(&mut transcript, b"small_poly_evals_at_z", &small_poly_evals_at_z);

	    //======================================================================================================================
	    /* Provide kzg eval proof for (z^m - 1) * g_hat + z * h_hat */

	    let combined_g_hat_h_hat = g_hat * (z.pow(&[m as u64]) - E::ScalarField::one()) + &h_hat * z;
	    let g_hat_h_hat_correctness_eval_proof = SamaritanMLPCS::<E>::kzg10_eval_prove(&srs, &combined_g_hat_h_hat, z).unwrap();

		//======================================================================================================================
		/* Consistency check for f(r,.) and p(.) starts [PHASE - 2] */
		/* Compute commitments to updated mlp(alphas, *), and an eval proof for beta-powered linear combinations of all mlps at point y of dimension kappa */
		/* Also, compute the beta-power combination of original mlps (in its original length, not the smaller ones), 
			then do eval proof for its value at (alphas||y) */

		let beta = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"beta");
		let mut cur = E::ScalarField::one();
		let mut beta_powers = Vec::new();
		let mut beta_power_combined_smaller_mlp = DenseMultilinearExtension::<E::ScalarField>::zero();
		let mut beta_power_combined_original_mlp = DenseMultilinearExtension::<E::ScalarField>::zero();
		for i in 0..num_polys {
			beta_powers.push(cur);
			beta_power_combined_smaller_mlp = beta_power_combined_smaller_mlp + (mlp_set_[i].clone() * cur);
			if let Some(comm) = sumcheck_relation.commit_list[i] {
				beta_power_combined_original_mlp = beta_power_combined_original_mlp + (mlp_set[i].clone() * cur);
			}
			cur = cur * beta;
		}

		let beta_power_combined_smaller_mlp_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &beta_power_combined_smaller_mlp).unwrap();
		util::append_commitment_to_transcript::<E>(&mut transcript, b"beta_power_combined_smaller_mlp_commit", &beta_power_combined_smaller_mlp_commit);

		let mut ext_coeffs : Vec<E::ScalarField> = Vec::new();
	    for coeff in beta_power_combined_smaller_mlp.to_evaluations() {
	    	for i in 0..(1 << num_initial_rounds) {
	    		ext_coeffs.push(coeff);
	    	}
	    }

	    let beta_power_combined_smaller_mlp_ext = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_number_of_gates, ext_coeffs);
	    let beta_power_combined_smaller_univ = DensePolynomial::<E::ScalarField>::from_coefficients_vec(beta_power_combined_smaller_mlp.to_evaluations());
	    let beta_power_combined_smaller_mlp_ext_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &beta_power_combined_smaller_mlp_ext).unwrap();
	    // let beta_power_combined_smaller_mlp_ext_commit = Self::compute_ext_commit(&srs, &beta_power_combined_smaller_univ, num_initial_rounds);
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"beta_power_combined_smaller_mlp_ext_commit", &beta_power_combined_smaller_mlp_ext_commit);

		let y = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"y", kappa);
		let mut eval_point = Vec::new();
	    eval_point.extend_from_slice(&alphas);
	    eval_point.extend_from_slice(&y);

		let combined_mlp = beta_power_combined_original_mlp - beta_power_combined_smaller_mlp_ext.clone();

		let mut subtract_value = E::ScalarField::zero();
	    for elem in &sumcheck_relation.eq_tilde_eval_infos {
	    	let index = elem.index;
	    	let tau = &elem.tau;
	    	let eval = Self::evaluate_eq_tilde_at_point(log_number_of_gates, &tau, &eval_point);
	    	subtract_value = subtract_value + eval * beta_powers[index];
	    }

		let (combined_mlp_proof, deg_check_samaritan) = SamaritanMLPCS::<E>::prove(&srs, &combined_mlp, &eval_point, E::ScalarField::zero() - subtract_value, &mut rng).unwrap();

		//======================================================================================================================
		/* Consistency check for ifft(p_hat) and q_hat starts [PHASE - 3] */
		/* compute and commit to A_z(x). note p_hat = beta_power_combined_smaller_mlp */

		let delta = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"delta");
		let epsilon = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"epsilon");

		let p_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(beta_power_combined_smaller_mlp.to_evaluations().to_vec());
		let (A_hat_z, B_hat_z_delta_coeffs) = Self::compute_A_hat_z_and_B_hat_z_delta_coeffs(z, delta, m);
		let S_hat = Self::compute_S_hat(&p_hat, &A_hat_z, &B_hat_z_delta_coeffs, epsilon, m);

		let A_hat_z_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &A_hat_z).unwrap();
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"A_hat_z_commit", &A_hat_z_commit);

	    let S_hat_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &S_hat).unwrap();
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"S_hat_commit", &S_hat_commit);

	    let r = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"r");
	    let r_inverse = r.inverse().unwrap();

	    // this evaluation of v_eta and corresponding univariate check from phase-2 is batched within univarate check of phase-3
	    let beta_power_combined_smaller_ext_univ = DensePolynomial::<E::ScalarField>::from_coefficients_vec(beta_power_combined_smaller_mlp_ext.to_evaluations());
		let v_eta = beta_power_combined_smaller_univ.evaluate(&r.pow(&[(1 << num_initial_rounds) as u64]));
		
	    let p_hat_inv_eval = p_hat.evaluate(&r_inverse);
	    let A_hat_z_inv_eval = A_hat_z.evaluate(&r_inverse);
	    let S_hat_inv_eval = S_hat.evaluate(&r_inverse);

	    let B_hat_z_inv_delta_eval = Self::evaluate_B_hat_z_at_point(&z, &(delta * r_inverse), kappa);

	    util::append_field_element_to_transcript::<E>(&mut transcript, b"v_eta", &v_eta);
	    util::append_field_element_to_transcript::<E>(&mut transcript, b"p_hat_inv_eval", &p_hat_inv_eval);
	    util::append_field_element_to_transcript::<E>(&mut transcript, b"A_hat_z_inv_eval", &A_hat_z_inv_eval);
	    util::append_field_element_to_transcript::<E>(&mut transcript, b"S_hat_inv_eval", &S_hat_inv_eval);

	    let S_equality_left = (&p_hat * A_hat_z_inv_eval + &A_hat_z * p_hat_inv_eval) + &A_hat_z * B_hat_z_inv_delta_eval * epsilon - &S_hat * r + beta_power_combined_smaller_ext_univ * epsilon.pow(&[2 as u64]);
	    let S_equality_left_eval_proof = SamaritanMLPCS::<E>::kzg10_eval_prove(&srs, &S_equality_left, r).unwrap();

	  	//======================================================================================================================
	  	/* Three deg check combined in a single instance */

        let deg_check = DegreeCheckPolynomials {
        	polys: [deg_check_samaritan.polys, vec![h_hat]].concat(),
        	degs: [deg_check_samaritan.degs, vec![m - 1]].concat(),
        };
        let deg_check_proof = DegreeCheck::<E>::prove(&srs, &deg_check).unwrap();
	    
        let proof = GenericImprovedSumcheckProof {
        	log_number_of_gates,
        	max_degree: sumcheck_relation.max_degree,
        	rhs: sumcheck_relation.rhs,
        	G_tilde_description: sumcheck_relation.G_tilde_description,
        	additional_field_elements: sumcheck_relation.additional_field_elements.clone(),
        	eq_tilde_eval_infos: sumcheck_relation.eq_tilde_eval_infos.clone(),
        	coeffs,
        	g_hat_commit,
        	h_hat_commit,
        	rem_const,
        	small_poly_evals_at_z,
        	g_hat_h_hat_correctness_eval_proof,
        	beta_power_combined_smaller_mlp_commit,
        	beta_power_combined_smaller_mlp_ext_commit,
        	combined_mlp_proof,
        	A_hat_z_commit,
        	S_hat_commit,
        	v_eta,
        	p_hat_inv_eval,
        	A_hat_z_inv_eval,
        	S_hat_inv_eval,
        	S_equality_left_eval_proof,
        	deg_check_proof,
        };

		end_timer!(prover_time);

		Ok(proof)
	}

	// pub fn verify(proof: &GenericImprovedSumcheckProof<E>, public_computable_commit_list: &Vec<Option<Commitment<E>>>, srs: &SamaritanMLPCS_SRS<E>) -> Result<bool, Error> {
	pub fn verify(proof: &GenericImprovedSumcheckProof<E>, commit_list: Vec<Option<Commitment<E>>>, srs: &SamaritanMLPCS_SRS<E>) -> Result<bool, Error> {
		let verifier_time = start_timer!(|| format!("GenericImprovedSumcheck::verify"));

        let mut transcript = Transcript::new(b"GenericImprovedSumcheck Transcript");
        
        let log_number_of_gates = proof.log_number_of_gates;
        let number_of_gates = 1 << log_number_of_gates;
        let num_polys = commit_list.len();
        let num_initial_rounds = (log_number_of_gates as f64).log2().ceil() as usize;

        //======================================================================================================================
        /* sumcheck rounds */

		let mut alphas: Vec<_> = Vec::new();
		let mut cur_eval_value = proof.rhs;
        let mut d_plus_one_evaluation_points = (1..=proof.max_degree).map(|x| E::ScalarField::from(x as u64)).collect::<Vec<_>>();
        d_plus_one_evaluation_points.push(E::ScalarField::zero());
		for i in 0..num_initial_rounds {
			if i > 0 {
				let alpha = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha");
				alphas.push(alpha);
				let mut coeffs = proof.coeffs[i - 1].clone();
				coeffs.push(cur_eval_value - coeffs[0]);
				cur_eval_value = Self::compute_evaluation_through_lagrange_interpolation(&d_plus_one_evaluation_points, &coeffs, alpha);
			}
			util::append_field_element_vector_to_transcript::<E>(&mut transcript, b"d_plus_one_evaluations", &proof.coeffs[i]);
		}
		let alpha_nu = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_nu");

		let mut final_poly_coeffs = proof.coeffs[num_initial_rounds - 1].clone();
		final_poly_coeffs.push(cur_eval_value - final_poly_coeffs[0]);

		cur_eval_value = Self::compute_evaluation_through_lagrange_interpolation(&d_plus_one_evaluation_points, &final_poly_coeffs, alpha_nu);
		alphas.push(alpha_nu);

		let kappa = log_number_of_gates - num_initial_rounds;
		let m = (1 << kappa) as usize;

		//======================================================================================================================
		/* kzg10 verify for g_hat_h_hat correctness such that (z^m - 1) * g_hat + z * h_hat = G_tilde(small_poly_evals_at_z) - v_bar/m. note that v_bar should be equal to cur_eval_value. */

		util::append_commitment_to_transcript::<E>(&mut transcript, b"g_hat_commit", &proof.g_hat_commit);
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"h_hat_commit", &proof.h_hat_commit);

		let z = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"z");

		util::append_field_element_vector_to_transcript::<E>(&mut transcript, b"small_poly_evals_at_z", &proof.small_poly_evals_at_z);

		let G_tilde_eval_at_z = (proof.G_tilde_description)(proof.small_poly_evals_at_z.clone(), &proof.additional_field_elements);
		// let eval_of_combined_g_hat_h_hat_at_z = G_tilde_eval_at_z - cur_eval_value * E::ScalarField::from(m as u64).inverse().unwrap();
		let eval_of_combined_g_hat_h_hat_at_z = G_tilde_eval_at_z - proof.rem_const;

		let combined_g_hat_h_hat_commit = Commitment(E::G1::msm(&vec![proof.g_hat_commit.0, proof.h_hat_commit.0], &vec![z.pow(&[m as u64]) - E::ScalarField::one(), z]).unwrap().into_affine());

		let g_hat_h_hat_check = SamaritanMLPCS::<E>::kzg10_eval_proof_verify(&srs, &combined_g_hat_h_hat_commit, z, eval_of_combined_g_hat_h_hat_at_z, &proof.g_hat_h_hat_correctness_eval_proof).unwrap();
		// assert_eq!(g_hat_h_hat_check, true);

		//======================================================================================================================
		/* combine the smaller mlps (over m-sized Boolean hypercube) and original mlps (over n-sized Boolean hypercube) with powers of beta. then check if they are equal at y and alphas||y respectively. */

		let beta = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"beta");
		let mut cur = E::ScalarField::one();
		let mut beta_powers = Vec::new();
		for i in 0..num_polys {
			beta_powers.push(cur);
			cur = cur * beta;
		}

		util::append_commitment_to_transcript::<E>(&mut transcript, b"beta_power_combined_smaller_mlp_commit", &proof.beta_power_combined_smaller_mlp_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"beta_power_combined_smaller_mlp_ext_commit", &proof.beta_power_combined_smaller_mlp_ext_commit);
		let y = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"y", kappa);

		let mut commit_list_ = Vec::new();
		let mut scalar_list = Vec::new();
		for i in 0..num_polys {
			if let Some(comm) = commit_list[i] {
				commit_list_.push(comm.0);
				scalar_list.push(beta_powers[i]);
			}
		}
		commit_list_.push(proof.beta_power_combined_smaller_mlp_ext_commit.0);
		scalar_list.push(-E::ScalarField::one());
		let combined_mlp_commit = Commitment(E::G1::msm(&commit_list_, &scalar_list).unwrap().into_affine());
		let mut eval_point = Vec::new();
	    eval_point.extend_from_slice(&alphas);
	    eval_point.extend_from_slice(&y);

	    let mut subtract_value = E::ScalarField::zero();
	    for elem in &proof.eq_tilde_eval_infos {
	    	let index = elem.index;
	    	let tau = &elem.tau;
	    	let eval = Self::evaluate_eq_tilde_at_point(log_number_of_gates, &tau, &eval_point);
	    	subtract_value = subtract_value + eval * beta_powers[index];
	    }

		let combined_mlp_check = SamaritanMLPCS::<E>::verify(&srs, &combined_mlp_commit, &eval_point, E::ScalarField::zero() - subtract_value, &proof.combined_mlp_proof).unwrap();
		// assert_eq!(combined_mlp_check, true);

		//======================================================================================================================
		/* S_equality_left check */

		let delta = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"delta");
		let epsilon = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"epsilon");

		util::append_commitment_to_transcript::<E>(&mut transcript, b"A_hat_z_commit", &proof.A_hat_z_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"S_hat_commit", &proof.S_hat_commit);

		let mut v = E::ScalarField::zero();
		for i in 0..num_polys {
			v = v + beta_powers[i] * proof.small_poly_evals_at_z[i];
		}

		let r = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"r");
	    let r_inverse = r.inverse().unwrap();

	    util::append_field_element_to_transcript::<E>(&mut transcript, b"v_eta", &proof.v_eta);
	    util::append_field_element_to_transcript::<E>(&mut transcript, b"p_hat_inv_eval", &proof.p_hat_inv_eval);
	    util::append_field_element_to_transcript::<E>(&mut transcript, b"A_hat_z_inv_eval", &proof.A_hat_z_inv_eval);
	    util::append_field_element_to_transcript::<E>(&mut transcript, b"S_hat_inv_eval", &proof.S_hat_inv_eval);

	    let B_hat_z_delta_eval = Self::evaluate_B_hat_z_at_point(&z, &(delta * r), kappa);
	    let B_hat_z_inv_delta_eval = Self::evaluate_B_hat_z_at_point(&z, &(delta * r_inverse), kappa);

		let S_equality_left_eval = E::ScalarField::from(2 as u64) * 
									(E::ScalarField::from(m as u64) * v * (z.pow(&[m as u64]) - E::ScalarField::one()).inverse().unwrap()
										+ epsilon * (delta.pow(&[m as u64]) - E::ScalarField::one()) * (delta - E::ScalarField::one()).inverse().unwrap())
									+ r_inverse * proof.S_hat_inv_eval
									- epsilon * proof.A_hat_z_inv_eval * B_hat_z_delta_eval
									+ epsilon.pow(&[2 as u64]) * proof.v_eta * (r.pow(&[(1<<num_initial_rounds) as u64]) - E::ScalarField::one()) * (r - E::ScalarField::one()).inverse().unwrap();

		let S_equality_left_commit = Commitment(E::G1::msm(&vec![proof.beta_power_combined_smaller_mlp_commit.0, proof.A_hat_z_commit.0, proof.S_hat_commit.0, proof.beta_power_combined_smaller_mlp_ext_commit.0], 
	     													&vec![proof.A_hat_z_inv_eval, proof.p_hat_inv_eval + epsilon * B_hat_z_inv_delta_eval, E::ScalarField::zero() - r, epsilon.pow(&[2 as u64])]).unwrap().into_affine());

		let S_equality_left_check = SamaritanMLPCS::<E>::kzg10_eval_proof_verify(&srs, &S_equality_left_commit, r, S_equality_left_eval, &proof.S_equality_left_eval_proof).unwrap();
	    // assert_eq!(S_equality_left_check, true);

	    //======================================================================================================================
	    /* degree check */

	    let deg_check_verify = DegreeCheck::<E>::verify(&srs, &proof.deg_check_proof).unwrap();
        // assert_eq!(deg_check_verify, true);

        end_timer!(verifier_time);

		Ok(g_hat_h_hat_check && combined_mlp_check && S_equality_left_check && deg_check_verify)

	}
}


#[cfg(test)]
mod tests {
    #![allow(non_camel_case_types)]
    use ark_poly_commit::kzg10::*;
    use ark_poly_commit::*;
    use ark_ec::pairing::Pairing;
    use ark_bls12_381::Bls12_381;
    use ark_bls12_381::Fr;
    // use ark_bn254::Bn254;
    // use ark_bn254::Fr;
    use ark_std::test_rng;
    use ark_std::{start_timer, end_timer, Zero, One};
    
    use crate::samaritan_mlpcs::*;
    use crate::generic_improved_sumcheck::*;

    type GenericImprovedSumcheck_Bls12_381 = GenericImprovedSumcheck<Bls12_381>;
    // type GenericImprovedSumcheck_Bn254 = GenericImprovedSumcheck<Bn254>;

    fn myfunc(set_of_values: Vec<Fr>, additional_field_elements: &Vec<Fr>) -> Fr {
    	set_of_values[0] * set_of_values[1] - set_of_values[2]
    }

    fn myfunc_poly(set_of_polys: &Vec<DensePolynomial<Fr>>, additional_field_elements: &Vec<Fr>) -> DensePolynomial<Fr> {
    	&set_of_polys[0] * &set_of_polys[1] - &set_of_polys[2]
    }

    fn myfunc_linear_combined_poly(set_of_polys: &Vec<DensePolynomial<Fr>>, set_of_evals: &Vec<Option<Fr>>, additional_field_elements: &Vec<Fr>) -> DensePolynomial<Fr> {
    	&set_of_polys[0] * set_of_evals[1].unwrap() - &set_of_polys[2]
    }

    // fn myfunc_combined_commit(set_of_commits: Vec<Option<Commitment<Bls12_381>>>, set_of_evals: Vec<Option<Fr>>, additional_field_elements: &Vec<Fr>) -> Commitment<Bls12_381> {
    // 	let commit_list = vec![set_of_commits[0].unwrap().0, set_of_commits[2].unwrap().0];
    // 	let scalar_list = vec![set_of_evals[1].unwrap(), Fr::zero() - Fr::one()];
    // 	Commitment(<Bls12_381 as Pairing>::G1::msm(&commit_list, &scalar_list).unwrap().into_affine())
    // }

    #[test]
    fn functionality_test() {
        let mut rng = &mut test_rng();
        let log_number_of_gates = 16;
        let num_of_gates = 1 << log_number_of_gates;

        let mlp_a = DenseMultilinearExtension::rand(log_number_of_gates, rng);

        let mlp_b = DenseMultilinearExtension::rand(log_number_of_gates, rng);

        let mut ab_vec: Vec<_> = Vec::new();
        for i in 0..num_of_gates {
        	// println!("i: {}, term: {}", i, mlp_a[i] * mlp_b[i]);
        	ab_vec.push(Fr::from(mlp_a[i] * mlp_b[i]));
        }
        let mlp_ab = DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, ab_vec);

        let srs = SamaritanMLPCS::<Bls12_381>::setup(log_number_of_gates, rng).unwrap();
        let mlp_a_commit = SamaritanMLPCS::<Bls12_381>::commit_G1(&srs, &mlp_a).unwrap();
        let mlp_b_commit = SamaritanMLPCS::<Bls12_381>::commit_G1(&srs, &mlp_b).unwrap();
        let mlp_ab_commit = SamaritanMLPCS::<Bls12_381>::commit_G1(&srs, &mlp_ab).unwrap();

        let commit_list = vec![Some(mlp_a_commit), Some(mlp_b_commit), Some(mlp_ab_commit)];
        let sumcheck_relation: SumcheckRelation<Bls12_381> = SumcheckRelation {
        							log_number_of_vars: log_number_of_gates,
        							max_degree: 2,
        							mlp_set: vec![mlp_a, mlp_b, mlp_ab],
        							commit_list: commit_list,
        							// mark_if_eval_reqd_in_linear_combination: vec![false, true, false],
        							eq_tilde_eval_infos: Vec::new(),
        							rhs: Fr::zero(),
        							additional_field_elements: Vec::new(),
        							G_tilde_description: myfunc,
        							G_tilde_description_poly: myfunc_poly,
        							G_bar_linear_combine: myfunc_linear_combined_poly,
        							// G_tilde_combined_commit: myfunc_combined_commit,
        						};

        let generic_improved_sumcheck_proof = GenericImprovedSumcheck_Bls12_381::prove(&srs, &sumcheck_relation).unwrap();

        let valid = GenericImprovedSumcheck_Bls12_381::verify(&generic_improved_sumcheck_proof, sumcheck_relation.commit_list, &srs).unwrap();

        assert_eq!(valid, true);



        // let srs = SamaritanMLPCS::<Bn254>::setup(log_number_of_gates, rng).unwrap();
        // let mlp_a_commit = SamaritanMLPCS::<Bn254>::commit_G1(&srs, &mlp_a).unwrap();
        // let mlp_b_commit = SamaritanMLPCS::<Bn254>::commit_G1(&srs, &mlp_b).unwrap();
        // let mlp_ab_commit = SamaritanMLPCS::<Bn254>::commit_G1(&srs, &mlp_ab).unwrap();

        // let commit_list = vec![Some(mlp_a_commit), Some(mlp_b_commit), Some(mlp_ab_commit)];
        // let sumcheck_relation: SumcheckRelation<Bn254> = SumcheckRelation {
        // 							log_number_of_vars: log_number_of_gates,
        // 							max_degree: 2,
        // 							mlp_set: vec![mlp_a, mlp_b, mlp_ab],
        // 							commit_list: commit_list,
        // 							eq_tilde_eval_infos: Vec::new(),
        // 							rhs: Fr::zero(),
        // 							additional_field_elements: Vec::new(),
        // 							G_tilde_description: myfunc,
        // 							G_tilde_description_poly: myfunc_poly,
        // 							G_bar_linear_combine: myfunc_linear_combined_poly,
        // 							// G_tilde_combined_commit: myfunc_combined_commit,
        // 						};

        // let generic_improved_sumcheck_proof = GenericImprovedSumcheck_Bn254::prove(&srs, &sumcheck_relation).unwrap();

        // let valid = GenericImprovedSumcheck_Bn254::verify(&generic_improved_sumcheck_proof, sumcheck_relation.commit_list, &srs).unwrap();

        // assert_eq!(valid, true);
      }
}

