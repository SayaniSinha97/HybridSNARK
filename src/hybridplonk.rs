use ark_poly_commit::kzg10::*;
use ark_poly_commit::error::Error;
use ark_ec::pairing::Pairing;
use ark_poly::polynomial::Polynomial;
use ark_ff::fields::Field;
use ark_poly::DenseUVPolynomial;
use ark_poly::univariate::DensePolynomial;
use ark_poly::univariate::DenseOrSparsePolynomial;
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
use ark_ec::VariableBaseMSM;
use ark_ec::CurveGroup;
use ark_ff::batch_inversion;
use crate::samaritan_mlpcs::*;
use crate::util;

#[derive(Debug)]
pub struct HybridPlonkCircuit<E: Pairing> {
	log_number_of_gates: usize,
	number_of_wires : usize,
	qL : DenseMultilinearExtension<E::ScalarField>,
	qR : DenseMultilinearExtension<E::ScalarField>,
	qO : DenseMultilinearExtension<E::ScalarField>,
	qM : DenseMultilinearExtension<E::ScalarField>,
	qC : DenseMultilinearExtension<E::ScalarField>,
	sigma_1 : DenseMultilinearExtension<E::ScalarField>,
	sigma_2 : DenseMultilinearExtension<E::ScalarField>,
	sigma_3 : DenseMultilinearExtension<E::ScalarField>,
	id_1 : DenseMultilinearExtension<E::ScalarField>,
	id_2 : DenseMultilinearExtension<E::ScalarField>,
	id_3 : DenseMultilinearExtension<E::ScalarField>,
}

pub struct HybridPlonkProof<E: Pairing> {
	number_of_initial_rounds: usize,
	w1_tilde_commit: Commitment<E>,
	w2_tilde_commit: Commitment<E>,
	w3_tilde_commit: Commitment<E>,
	v_0_tilde_commit: Commitment<E>,
	v_1_tilde_commit: Commitment<E>,
	u_0_tilde_commit: Commitment<E>,
	u_1_tilde_commit: Commitment<E>,
	coeffs: Vec<Vec<E::ScalarField>>,
	g_hat_commit: Commitment<E>,
	h_hat_commit: Commitment<E>,
	V_eq: E::ScalarField,
	V_w1: E::ScalarField,
	V_w2: E::ScalarField,
	V_w3: E::ScalarField,
	V_sigma1: E::ScalarField,
	V_sigma2: E::ScalarField,
	V_sigma3: E::ScalarField,
	V_id1: E::ScalarField,
	V_id2: E::ScalarField,
	V_id3: E::ScalarField,
	V_u0: E::ScalarField,
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
	W1: E::ScalarField,
	W2: E::ScalarField,
	W3: E::ScalarField,
	W4: E::ScalarField,
	W5: E::ScalarField,
	W6: E::ScalarField,
	// elements corresponding to Samaritan MLPCS Proof after unrolling
	v_hat_commit_mlp: Commitment<E>,
    v_gamma_: E::ScalarField,
    p_hat_commit_mlp: Commitment<E>,
    b_hat_commit_mlp: Commitment<E>,
    u_hat_commit_mlp: Commitment<E>,
    t_hat_commit_mlp: Commitment<E>,
    s_hat_commit_mlp: Commitment<E>,
    L_hat_eval_proof: KZG10EvalProof<E>,
}

pub struct HybridPlonk<E: Pairing> {
	_engine: PhantomData<E>,
}

impl<E: Pairing> HybridPlonk<E> {
	/* This function generates a random inner product circuit for two vectors A and B of dimension n. The circuit description is hybridplonk-friendly. The circuit has total
	2n number of gates, among which n gates are for multiplication and the rest n are for addition. Last addition gate is a dummy gate to keep the number_of_gates 
	power-of-2. */  
	pub fn generate_circuit_for_inner_product(A: &Vec<usize>, B: &Vec<usize>, n: usize) -> HybridPlonkCircuit<E> {
		assert_eq!(A.len(), n);
		assert_eq!(B.len(), n);

		let number_of_gates: usize = 2 * n;
		let log_number_of_gates: usize = number_of_gates.trailing_zeros().try_into().unwrap();
		let number_of_wires: usize = 3 * number_of_gates;

		let evaluation_vec_L = [vec![E::ScalarField::zero(); n], vec![E::ScalarField::one(); n]].concat();
		let evaluation_vec_R = [vec![E::ScalarField::zero(); n], vec![E::ScalarField::one(); n]].concat();
		let evaluation_vec_M = [vec![E::ScalarField::one(); n], vec![E::ScalarField::zero(); n]].concat();
		let evaluation_vec_O = vec![-E::ScalarField::one(); 2*n];
		let evaluation_vec_C = vec![E::ScalarField::zero(); 2*n];

		let id_1_vec = (1..=number_of_gates).map(|i| E::ScalarField::from(i as u64)).collect();
    	let id_2_vec = ((number_of_gates+1)..=(2*number_of_gates)).map(|i| E::ScalarField::from(i as u64)).collect();
    	let id_3_vec = ((2*number_of_gates+1)..=(3*number_of_gates)).map(|i| E::ScalarField::from(i as u64)).collect();

		let mut sigma_1_vec: Vec<_> = Vec::new();
		let mut sigma_2_vec: Vec<_> = Vec::new();
		let mut sigma_3_vec: Vec<_> = Vec::new();

		for i in 0..n {
			sigma_1_vec.push(E::ScalarField::from((i + 1) as u64));
			sigma_2_vec.push(E::ScalarField::from((2 * n + i + 1) as u64));
			if i == 0 {
				sigma_3_vec.push(E::ScalarField::from((n + 1) as u64));
			}
			else{
				sigma_3_vec.push(E::ScalarField::from((3 * n + i) as u64));
			}
		}

		for i in 0..n {
			if i == 0 {
				sigma_1_vec.push(E::ScalarField::from((4 * n + 1) as u64));
			}
			else {
				sigma_1_vec.push(E::ScalarField::from((5 * n + i) as u64));
			}
			if i == n-1 {
				sigma_2_vec.push(E::ScalarField::from((4 * n) as u64));
			}
			else{
				sigma_2_vec.push(E::ScalarField::from((4 * n + (i + 2)) as u64));
			}
			if i == n-1 {
				sigma_3_vec.push(E::ScalarField::from((6 * n) as u64));
			}
			else{
				sigma_3_vec.push(E::ScalarField::from((n + (i + 2)) as u64));
			}
		}

		let myckt = HybridPlonkCircuit::<E>{
    		log_number_of_gates,
    		number_of_wires,
    		qL: DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, evaluation_vec_L),
    		qR: DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, evaluation_vec_R),
    		qO: DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, evaluation_vec_O),
    		qM: DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, evaluation_vec_M),
    		qC: DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, evaluation_vec_C),
    		sigma_1: DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, sigma_1_vec),
    		sigma_2: DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, sigma_2_vec),
    		sigma_3: DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, sigma_3_vec),
    		id_1: DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, id_1_vec),
    		id_2: DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, id_2_vec),
    		id_3: DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, id_3_vec),
    	};
    	myckt
	}

	pub fn setup<R: RngCore>(ckt: &HybridPlonkCircuit<E>, rng: &mut R) -> Result<(SamaritanMLPCS_SRS<E>, Commitment<E>, Commitment<E>, Commitment<E>, Commitment<E>, Commitment<E>,
		Commitment<E>, Commitment<E>, Commitment<E>, Commitment<E>, Commitment<E>, Commitment<E>), Error> {
		let srs = SamaritanMLPCS::<E>::setup(ckt.log_number_of_gates, rng).unwrap();

    	// some pre-computations done during setup, used later by the verifier
		let qM_comm = SamaritanMLPCS::<E>::commit_G1(&srs, &ckt.qM).unwrap();
		let qL_comm = SamaritanMLPCS::<E>::commit_G1(&srs, &ckt.qL).unwrap();
		let qR_comm = SamaritanMLPCS::<E>::commit_G1(&srs, &ckt.qR).unwrap();
		let qO_comm = SamaritanMLPCS::<E>::commit_G1(&srs, &ckt.qO).unwrap();
		let qC_comm = SamaritanMLPCS::<E>::commit_G1(&srs, &ckt.qC).unwrap();
		let sigma1_comm = SamaritanMLPCS::<E>::commit_G1(&srs, &ckt.sigma_1).unwrap();
		let sigma2_comm = SamaritanMLPCS::<E>::commit_G1(&srs, &ckt.sigma_2).unwrap();
		let sigma3_comm = SamaritanMLPCS::<E>::commit_G1(&srs, &ckt.sigma_3).unwrap();
		let id1_comm = SamaritanMLPCS::<E>::commit_G1(&srs, &ckt.id_1).unwrap();
		let id2_comm = SamaritanMLPCS::<E>::commit_G1(&srs, &ckt.id_2).unwrap();
		let id3_comm = SamaritanMLPCS::<E>::commit_G1(&srs, &ckt.id_3).unwrap();

		Ok((srs, qM_comm, qL_comm, qR_comm, qO_comm, qC_comm, 
        	sigma1_comm, sigma2_comm, sigma3_comm, 
        	id1_comm, id2_comm, id3_comm))
	}

	/* This function computes all the n (= number_of_gates) evaluations over log(n)-sized hypercube for eq_tilde in O(n) time. We elaborate the idea with 
	an example of the case log(n) = 3. Recall that eq_tilde at hypercube point (1,1,0) is (tau[0] * tau[1] * (1 - tau[2])), similarly, at point (0,1,0) it is 
	((1 - tau[0]) * tau[1] * (1 - tau[2])). So, we first generate the gray code sequence of 3-variables: 0,1,3,2,6,7,5,4. We start with hypercube point (0,0,0)
	with the evaluation computed as first = (1 - tau[0]) * (1 - tau[1]) * (1 - tau[2]). Then for point (1,0,0) we determine the bit flip position (flip 0->1) 
	to be 0, and multiply first with tau[0]/(1 - tau[0]) to get the evaluation at (1,0,0). Next point is (1,1,0) according to gray code sequence. We determine 
	the bit flip position (flip 0->1) to be 1, and multiply first with tau[1]/(1 - tau[1]). Similarly, for next point (0,1,0), we multiply first with 
	(1 - tau[0])/tau[0], since bit flip position is 0 (flip 1->0). */

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
			first *= one_minus_tau[i];
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

	/* This function directly returns evaluation of eq_tilde at a point eval_point, without looking at individual hypercube evaluations of eq_tilde. Runtime is O(log(n)). */
	pub(crate) fn evaluate_eq_tilde_at_point(log_number_of_gates: usize, tau: &Vec<E::ScalarField>, eval_point: &Vec<E::ScalarField>) -> E::ScalarField {
		let mut res = E::ScalarField::one();
		for i in 0..log_number_of_gates {
			res = res * (tau[i] * eval_point[i] + (E::ScalarField::one() - tau[i]) * (E::ScalarField::one() - eval_point[i]));
		}
		res
	}

	/* computes evaluations of v0 at all points of log(n)-sized hypercube from the evaluations of other multilinear polynomials at those points, and then returns the corresponding mlp */
	pub(crate) fn compute_v_0_tilde(log_number_of_gates: usize, 
									sigma_1: &DenseMultilinearExtension<E::ScalarField>, sigma_2: &DenseMultilinearExtension<E::ScalarField>, sigma_3: &DenseMultilinearExtension<E::ScalarField>,
									id_1: &DenseMultilinearExtension<E::ScalarField>, id_2: &DenseMultilinearExtension<E::ScalarField>, id_3: &DenseMultilinearExtension<E::ScalarField>,
									w1: &DenseMultilinearExtension<E::ScalarField>, w2: &DenseMultilinearExtension<E::ScalarField>, w3: &DenseMultilinearExtension<E::ScalarField>,
									beta: E::ScalarField, gamma: E::ScalarField) -> DenseMultilinearExtension<E::ScalarField> {
		let number_of_gates = 1 << log_number_of_gates;

		let mut denoms = vec![E::ScalarField::zero(); number_of_gates];
		for i in 0..number_of_gates {
			denoms[i] = (w1[i] + beta * sigma_1[i] + gamma) * (w2[i] + beta * sigma_2[i] + gamma) * (w3[i] + beta * sigma_3[i] + gamma);
		}
		batch_inversion(&mut denoms);

		let mut res = vec![E::ScalarField::zero(); number_of_gates];
		for i in 0..number_of_gates {
			res[i] = (w1[i] + beta * id_1[i] + gamma) * (w2[i] + beta * id_2[i] + gamma) * (w3[i] + beta * id_3[i] + gamma) * denoms[i];
		}
		DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, res)
	}

	/* v_vec contains elements of v0 at even positions and elements of v1 in odd positions. First half of v_vec is u0 and second half is u1. */ 
	pub(crate) fn compute_v_1_u_0_u_1_tilde(log_number_of_gates: usize, v_0: &DenseMultilinearExtension<E::ScalarField>) -> (DenseMultilinearExtension<E::ScalarField>, DenseMultilinearExtension<E::ScalarField>, DenseMultilinearExtension<E::ScalarField>) {
		let number_of_gates = 1 << log_number_of_gates;
		let v_0_vec = v_0.to_evaluations();
		let mut v_vec = vec![E::ScalarField::one(); 2 * number_of_gates];
		for i in 0..number_of_gates {
			v_vec[2 * i] = v_0[i]
		}
		for i in 1..=log_number_of_gates {
			let mut k = 2usize.pow((i-1) as u32)-1;
			for j in ((2usize.pow(i as u32)-1)..2*number_of_gates).step_by(2usize.pow((i+1) as u32)) {
				v_vec[j] = v_vec[k] * v_vec[k+number_of_gates];
				k += 2usize.pow(i as u32);
			}
		}
		let mut v_1_vec = vec![E::ScalarField::one(); number_of_gates];
		for i in 0..number_of_gates {
			v_1_vec[i] = v_vec[2 * i + 1];
		}
		let u_0_vec = v_vec[..number_of_gates].to_vec();
		let u_1_vec = v_vec[number_of_gates..].to_vec();

		(DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, v_1_vec), 
			DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, u_0_vec), 
				DenseMultilinearExtension::from_evaluations_vec(log_number_of_gates, u_1_vec))
	}
	/* In each round of sumcheck protocol, the univariate polynomial sent from the prover to the verifier consists of at most d (x,y) points for (d-1) degree bound
	 for each variable in the multivariate polynomial. This function computes y for a given x. */
	pub(crate) fn compute_univariate_r_X_evaluation(mlp_set: &mut Vec<&mut DenseMultilinearExtension<E::ScalarField>>, eval_point: E::ScalarField, xi: E::ScalarField, beta: E::ScalarField, gamma: E::ScalarField) -> E::ScalarField {
		/* Note that (for reference to the sequence of polynomials present in the vector) : 
		mlp_set = {eq_tilde, w1_tilde_copy, w2_tilde_copy, w3_tilde_copy, 
			 qM_copy, qL_copy, qR_copy, qO_copy, qC_copy, 
			 sigma_1_copy, sigma_2_copy, sigma_3_copy, 
			 id_1_copy, id_2_copy, id_3_copy, 
			 v_0_tilde_copy, v_1_tilde_copy, u_0_tilde_copy, u_1_tilde_copy} */
		let mut tmp : Vec<_> = Vec::new();
		let mut i = 0;
		for mlp in mlp_set.iter_mut() {
			let tmp_poly = (*mlp).fix_variables(&[eval_point]);
			tmp.push(tmp_poly);
			i += 1;
		}
		let mut res = vec![E::ScalarField::zero(); tmp[0].to_evaluations().len()];
		for i in 0..res.len() { 
			res[i] = tmp[0][i] * ((tmp[1][i] * tmp[2][i] * tmp[4][i]) + (tmp[1][i] * tmp[5][i]) + (tmp[2][i] * tmp[6][i]) + (tmp[3][i] * tmp[7][i]) + tmp[8][i]
						+ xi * ((tmp[15][i] * (tmp[1][i] + beta * tmp[9][i] + gamma) * (tmp[2][i] + beta * tmp[10][i] + gamma) * (tmp[3][i] + beta * tmp[11][i] + gamma)) - ((tmp[1][i] + beta * tmp[12][i] + gamma) * (tmp[2][i] + beta * tmp[13][i] + gamma) * (tmp[3][i] + beta * tmp[14][i] + gamma))) 
						+ xi * xi * (tmp[16][i] - (tmp[17][i] * tmp[18][i]))); 
		}
		res.iter().sum()
	}
	/* Given (d+1) points for a d-degree univariate polynomial, this function computes its evaluation at some other point. */
	pub(crate) fn compute_evaluation_through_lagrange_interpolation(d_plus_one_evaluation_points: &Vec<E::ScalarField>, d_plus_one_evaluations: &Vec<E::ScalarField>, alpha: E::ScalarField) -> E::ScalarField {
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

	pub(crate) fn compute_G_bar_from_O_bar_set(O_bar_set: &Vec<DensePolynomial<E::ScalarField>>, beta: E::ScalarField, gamma: E::ScalarField, xi: E::ScalarField) -> DensePolynomial<E::ScalarField> {
		/* Note that (for reference to the sequence of polynomials present in the vector) : 
		mlp_set = {eq_tilde, w1_tilde_copy, w2_tilde_copy, w3_tilde_copy, 
			 qM_copy, qL_copy, qR_copy, qO_copy, qC_copy, 
			 sigma_1_copy, sigma_2_copy, sigma_3_copy, 
			 id_1_copy, id_2_copy, id_3_copy, 
			 v_0_tilde_copy, v_1_tilde_copy, u_0_tilde_copy, u_1_tilde_copy} */
		let gamma_poly = DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![gamma]);
		let res = &O_bar_set[0] * ((&O_bar_set[1] * &O_bar_set[2] * &O_bar_set[4]) + (&O_bar_set[1] * &O_bar_set[5]) + (&O_bar_set[2] * &O_bar_set[6]) + (&O_bar_set[3] * &O_bar_set[7]) + &O_bar_set[8]
				+ (&O_bar_set[15] * (&O_bar_set[1] + &O_bar_set[9] * beta + &gamma_poly) * (&O_bar_set[2] + &O_bar_set[10] * beta + &gamma_poly) * (&O_bar_set[3] + &O_bar_set[11] * beta + &gamma_poly) - (&O_bar_set[1] + &O_bar_set[12] *beta + &gamma_poly) * (&O_bar_set[2] + &O_bar_set[13] *beta + &gamma_poly) * (&O_bar_set[3] + &O_bar_set[14] * beta + &gamma_poly)) * xi
				+ (&O_bar_set[16] - &(&O_bar_set[17] * &O_bar_set[18])) * xi * xi);
		res 
	}

	pub(crate) fn compute_G_prime(O_bar_set: &Vec<DensePolynomial<E::ScalarField>>, g_hat: &DensePolynomial<E::ScalarField>, h_hat: &DensePolynomial<E::ScalarField>, xi: E::ScalarField, beta: E::ScalarField, gamma: E::ScalarField, z: E::ScalarField, m: usize, V_eq: E::ScalarField, V_w1: E::ScalarField, V_w2: E::ScalarField, V_w3: E::ScalarField, V_sigma1: E::ScalarField, V_sigma2: E::ScalarField, V_sigma3: E::ScalarField, V_id1: E::ScalarField, V_id2: E::ScalarField, V_id3: E::ScalarField, V_u0: E::ScalarField) -> DensePolynomial<E::ScalarField> {
		let res = (&O_bar_set[4] * V_w1 * V_w2 + &O_bar_set[5] * V_w1 + &O_bar_set[6] * V_w2 + &O_bar_set[7] * V_w3 + &O_bar_set[8] 
			+ (&O_bar_set[15] * (V_w1 + beta * V_sigma1 + gamma) * (V_w2 + beta * V_sigma2 + gamma) * (V_w3 + beta * V_sigma3 + gamma) - DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![(V_w1 + beta * V_id1 + gamma) * (V_w2 + beta * V_id2 + gamma) * (V_w3 + beta * V_id3 + gamma)])) * xi
			+ (&O_bar_set[16] - &O_bar_set[18] * V_u0) * xi * xi) * V_eq - g_hat * (z.pow(&[m as u64]) - E::ScalarField::from(1 as u64)) - h_hat * z;
		res
	}

	pub(crate) fn compute_F_bar(O_bar_set: &Vec<DensePolynomial<E::ScalarField>>, G_prime: &DensePolynomial<E::ScalarField>, alpha_powers: &Vec<E::ScalarField>) -> DensePolynomial<E::ScalarField> {
		let F_bar = G_prime + &O_bar_set[0] * alpha_powers[0] + &O_bar_set[1] * alpha_powers[1] + &O_bar_set[2] * alpha_powers[2] + &O_bar_set[3] * alpha_powers[3] 
						+ &O_bar_set[9] * alpha_powers[4] + &O_bar_set[10] * alpha_powers[5] + &O_bar_set[11] * alpha_powers[6]
						+ &O_bar_set[12] * alpha_powers[7] + &O_bar_set[13] * alpha_powers[8] + &O_bar_set[14] * alpha_powers[9]
						+ &O_bar_set[17] * alpha_powers[10];
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
			A_hat_coeffs.push(A_hat_evals_at_roots_of_unity_inv[i]);
		}
		batch_inversion(&mut A_hat_coeffs);
		let A_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(A_hat_coeffs);
		A_hat
	}

	pub(crate) fn compute_B_hat_delta_coeffs(A_hat: &DensePolynomial<E::ScalarField>, delta: E::ScalarField, m: usize) -> Vec<E::ScalarField> {
		let mut B_hat_delta_coeffs : Vec<_> = Vec::new();
		let A_hat_coeffs = A_hat.coeffs().to_vec();
		let mut A_hat_coeffs_inverse = A_hat_coeffs.clone();
		batch_inversion(&mut A_hat_coeffs_inverse);
		for i in 0..m {
			B_hat_delta_coeffs.push(A_hat_coeffs_inverse[i] * delta.pow(&[i as u64]));
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

	// This function combines the degree check equations for both Samaritan MLPCS and unrolled Hybridplonk. This polynomial is batched version of the following polynomials,
	// batched with increasing powers of \epsilon:
	// t_hat_mlp = u0_hat + epsilon * u1_hat + epsilon^2 * v0_hat + epsilon^3 * v1_hat + epsilon^4 * X^(n-m) * K_hat + epsilon^5 * X^(n-m+1) * h_hat
	// Till this point it is the degree check equation of Hybridplonk, but t_hat_mlp has even other terms due to unrolling of Samaritan MLPCS degree checks, as follows:
	// + epsilon^6 * X^-l_ * (v_psi_phi_combined - (eval + alpha * v_gamma) * X^-(l_-1) - b_hat)
	// + epsilon^7 * X^-m_ * (p_psi_combined - v_gamma * X^-(m_-1) - u_hat)
	// + epsilon^8 * (X^m_ - gamma)^-1 * (f_hat - p_hat) + epsilon^9 * f_hat + epsilon^10 * X^(n_-m_) * p_hat + epsilon^11 * X^(n_-m_+1) * u_hat + epsilon^12 * X^(n_-l_+1) * b_hat

	// pub(crate) fn compute_t_hat_mlp(u0_hat: &DensePolynomial<E::ScalarField>, u1_hat: &DensePolynomial<E::ScalarField>, 
	// 	v0_hat: &DensePolynomial<E::ScalarField>, v1_hat: &DensePolynomial<E::ScalarField>, 
	// 	K_hat: &DensePolynomial<E::ScalarField>, h_hat: &DensePolynomial<E::ScalarField>, 
	// 	v_psi_phi_combined: &DensePolynomial<E::ScalarField>, b_hat: &DensePolynomial<E::ScalarField>,
	// 	p_psi_combined: &DensePolynomial<E::ScalarField>, u_hat: &DensePolynomial<E::ScalarField>, 
	// 	f_hat: &DensePolynomial<E::ScalarField>, p_hat: &DensePolynomial<E::ScalarField>,
	// 	eval: E::ScalarField, v_gamma: E::ScalarField, alpha: E::ScalarField, gamma: E::ScalarField,
	// 	epsilon: E::ScalarField, n: usize, m: usize, l_: usize, m_: usize) -> DensePolynomial<E::ScalarField> {

	// 	let d_hat = u0_hat + u1_hat * epsilon + v0_hat * epsilon.pow(&[2 as u64]) + v1_hat * epsilon.pow(&[3 as u64]) 
	// 		+ &DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); n - m], K_hat.coeffs().to_vec()].concat().to_vec()) * epsilon.pow(&[4 as u64])
	// 		+ &DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); n - m + 1], h_hat.coeffs().to_vec()].concat().to_vec()) * epsilon.pow(&[5 as u64]);
		
	// 	let mid_term1 = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); l_ - 1], vec![E::ScalarField::from(eval + (alpha * v_gamma))]].concat());
    //     let mut new_term_1 = (v_psi_phi_combined - &mid_term1 - b_hat) * epsilon.pow(&[6 as u64]);
    //     new_term_1 = DensePolynomial::<E::ScalarField>::from_coefficients_vec(new_term_1.coeffs()[l_..].to_vec());

    //     let mid_term2 = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); m_ - 1], vec![E::ScalarField::from(v_gamma)]].concat());
    //     let mut new_term_2 = (p_psi_combined - &mid_term2 - u_hat) * epsilon.pow(&[7 as u64]);
    //     new_term_2 = DensePolynomial::<E::ScalarField>::from_coefficients_vec(new_term_2.coeffs()[m_..].to_vec());

    //     let mut new_term_3 = (f_hat - p_hat) * epsilon.pow(&[8 as u64]);
    //     let mut third_term_coeffs = (&new_term_3).coeffs.clone();
    //     for i in (m_..third_term_coeffs.len()).rev() {
    //         let quotient = third_term_coeffs[i];
    //         third_term_coeffs[i - m_] += quotient * gamma;
    //     }
    //     third_term_coeffs = third_term_coeffs[m_..].to_vec();//  truncate(third_term_coeffs.len() - m_);
    //     new_term_3 = DensePolynomial::<E::ScalarField>::from_coefficients_vec(third_term_coeffs);

    //     let new_term_4 = f_hat * epsilon.pow(&[9 as u64]);

    //     let mut new_term_5 = p_hat * epsilon.pow(&[10 as u64]);
    //     new_term_5 = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); (m_ * l_) - m_], (&new_term_5).coeffs().to_vec()].concat());

    //     let mut new_term_6 = u_hat * epsilon.pow(&[11 as u64]);
    //     new_term_6 = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); (m_ * l_) - m_ + 1], (&new_term_6).coeffs().to_vec()].concat());

	// 	let mut new_term_7 = b_hat * epsilon.pow(&[12 as u64]);
    //     new_term_7 = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); (m_ * l_) - l_ + 1], (&new_term_7).coeffs().to_vec()].concat());

	// 	let t_hat_mlp = d_hat + new_term_1 + new_term_2 + new_term_3 + new_term_4 + new_term_5 + new_term_6 + new_term_7;

	// 	t_hat_mlp
	// }

	pub fn compute_K_ext_hat_commit(srs: &SamaritanMLPCS_SRS<E>, K_hat: &DensePolynomial<E::ScalarField>, number_of_initial_rounds: usize) -> Commitment<E> {
		let mut modified_bases = Vec::new();
		let rep_count = 1 << number_of_initial_rounds;
		for i in 0..K_hat.coeffs().len() {
			let mut tmp = E::G1::zero();
			for j in &srs.powers_of_g[(i * rep_count)..((i+1) * rep_count)] {
				tmp += j;
			}
			modified_bases.push(tmp.into_affine());
		}
		let K_ext_hat_commit_time = start_timer!(||format!("msm"));
		let c = Commitment(E::G1::msm(&modified_bases, &K_hat.coeffs()).unwrap().into_affine());
		end_timer!(K_ext_hat_commit_time);
		c
	}

	pub fn compute_t_hat_mlp_and_its_commit(srs: &SamaritanMLPCS_SRS<E>, u0_hat: &DensePolynomial<E::ScalarField>, u0_hat_commit: &Commitment<E>, 
												u1_hat: &DensePolynomial<E::ScalarField>, u1_hat_commit: &Commitment<E>,
												v0_hat: &DensePolynomial<E::ScalarField>, v0_hat_commit: &Commitment<E>,
												v1_hat: &DensePolynomial<E::ScalarField>, v1_hat_commit: &Commitment<E>,
												K_hat: &DensePolynomial<E::ScalarField>, h_hat: &DensePolynomial<E::ScalarField>, 
	        									v_psi_phi_combined_mlp: &DensePolynomial<E::ScalarField>, b_hat_mlp: &DensePolynomial<E::ScalarField>, 
        										p_psi_combined_mlp: &DensePolynomial<E::ScalarField>, u_hat_mlp: &DensePolynomial<E::ScalarField>,
        										f_hat_mlp: &DensePolynomial<E::ScalarField>, p_hat_mlp: &DensePolynomial<E::ScalarField>,
												eval: E::ScalarField, v_gamma: E::ScalarField, alpha: E::ScalarField, gamma: E::ScalarField, epsilon: E::ScalarField, 
												number_of_gates: usize, m: usize, l_: usize, m_: usize) -> (DensePolynomial<E::ScalarField>, Commitment<E>) {
		let K_hat_right_shifted_commit: Commitment<E> = Commitment(E::G1::msm(&srs.powers_of_g[(number_of_gates - m)..(number_of_gates - m + &K_hat.coeffs().len())], &K_hat.coeffs()).unwrap().into_affine());
		let h_hat_right_shifted_commit: Commitment<E> = Commitment(E::G1::msm(&srs.powers_of_g[(number_of_gates - m + 1)..(number_of_gates - m + 1 + &h_hat.coeffs().len())], &h_hat.coeffs()).unwrap().into_affine());


		let simple_term_1 = u0_hat + u1_hat * epsilon + v0_hat * epsilon.pow(&[2 as u64]) + v1_hat * epsilon.pow(&[3 as u64])
								+ &DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); number_of_gates - m], K_hat.coeffs().to_vec()].concat().to_vec()) * epsilon.pow(&[4 as u64])
								+ &DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); number_of_gates - m + 1], h_hat.coeffs().to_vec()].concat().to_vec()) * epsilon.pow(&[5 as u64]);
		let simple_term_1_commit: Commitment<E> = Commitment(E::G1::msm(&vec![u0_hat_commit.0, u1_hat_commit.0, v0_hat_commit.0, v1_hat_commit.0, K_hat_right_shifted_commit.0, h_hat_right_shifted_commit.0],
			&vec![E::ScalarField::one(), epsilon, epsilon.pow(&[2 as u64]), epsilon.pow(&[3 as u64]), epsilon.pow(&[4 as u64]), epsilon.pow(&[5 as u64])]).unwrap().into_affine());

		let mid_term1 = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); l_ - 1], vec![E::ScalarField::from(eval + (alpha * v_gamma))]].concat());
        let mut simple_term_2 = (v_psi_phi_combined_mlp - &mid_term1 - b_hat_mlp) * epsilon.pow(&[6 as u64]);
        simple_term_2 = DensePolynomial::<E::ScalarField>::from_coefficients_vec(simple_term_2.coeffs()[l_..].to_vec());

        let mid_term2 = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); m_ - 1], vec![E::ScalarField::from(v_gamma)]].concat());
        let mut simple_term_3 = (p_psi_combined_mlp - &mid_term2 - u_hat_mlp) * epsilon.pow(&[7 as u64]);
        simple_term_3 = DensePolynomial::<E::ScalarField>::from_coefficients_vec(simple_term_3.coeffs()[m_..].to_vec());

        let mut simple_term_4 = (f_hat_mlp - p_hat_mlp) * epsilon.pow(&[8 as u64]);
        let mut term_coeffs = (&simple_term_4).coeffs.clone();
        for i in (m_..term_coeffs.len()).rev() {
            let quotient = term_coeffs[i];
            term_coeffs[i - m_] += quotient * gamma;
        }
        term_coeffs = term_coeffs[m_..].to_vec();//  truncate(third_term_coeffs.len() - m_);
        simple_term_4 = DensePolynomial::<E::ScalarField>::from_coefficients_vec(term_coeffs);

        let simple_term_5 = f_hat_mlp * epsilon.pow(&[9 as u64]);

        let simple_terms_combined_long = &simple_term_4 + &simple_term_5;

        let simple_terms_combined_long_commit: Commitment<E> = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &simple_terms_combined_long).unwrap();

        let mut simple_term_6 = p_hat_mlp * epsilon.pow(&[10 as u64]);
        simple_term_6 = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); (m_ * l_) - m_], (&simple_term_6).coeffs().to_vec()].concat());

        let mut simple_term_7 = u_hat_mlp * epsilon.pow(&[11 as u64]);
        simple_term_7 = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); (m_ * l_) - m_ + 1], (&simple_term_7).coeffs().to_vec()].concat());

		let mut simple_term_8 = b_hat_mlp * epsilon.pow(&[12 as u64]);
        simple_term_8 = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); (m_ * l_) - l_ + 1], (&simple_term_8).coeffs().to_vec()].concat());

        let t_hat_mlp = &simple_term_1 + &simple_term_2 + &simple_term_3 + &simple_term_4 + &simple_term_5 + &simple_term_6 + &simple_term_7 + &simple_term_8;

        let simple_terms_combined = &simple_term_2 + simple_term_3 + simple_term_6 + simple_term_7 + simple_term_8;

        let simple_terms_combined_commit: Commitment<E> = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &simple_terms_combined).unwrap();
        
        let t_hat_mlp_commit: Commitment<E> = Commitment((simple_term_1_commit.0 + simple_terms_combined_long_commit.0 + simple_terms_combined_commit.0).into_affine());

		(t_hat_mlp, t_hat_mlp_commit)
	}

	pub fn prove(ckt: &HybridPlonkCircuit<E>, w1_tilde: &DenseMultilinearExtension<E::ScalarField>, w2_tilde: &DenseMultilinearExtension<E::ScalarField>, w3_tilde: &DenseMultilinearExtension<E::ScalarField>, srs: &SamaritanMLPCS_SRS<E>) -> Result<HybridPlonkProof<E>, Error> {
		// let prover_time = start_timer!(|| format!("HybridPlonk::prove with log_number_of_gates {}", ckt.log_number_of_gates));

		let log_number_of_gates = ckt.log_number_of_gates;
		let number_of_gates = 1 << log_number_of_gates;
		let number_of_wires = ckt.number_of_wires;
		let number_of_initial_rounds = (log_number_of_gates as f64).log2().ceil() as usize;
		// let number_of_initial_rounds = 5;
		let seed = [21u8; 32];
		let mut rng = StdRng::from_seed(seed);
		
		let mut transcript = Transcript::new(b"HybridPlonk Transcript");

		let w1_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &w1_tilde).unwrap();
		let w2_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &w2_tilde).unwrap();
		let w3_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &w3_tilde).unwrap();

		util::append_commitment_to_transcript::<E>(&mut transcript, b"w1_tilde_commit", &w1_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"w2_tilde_commit", &w2_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"w3_tilde_commit", &w3_tilde_commit);

		let beta = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"beta");
		let gamma = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"gamma");
		
		let v_0_tilde = Self::compute_v_0_tilde(log_number_of_gates, &ckt.sigma_1, &ckt.sigma_2, &ckt.sigma_3, &ckt.id_1, &ckt.id_2, &ckt.id_3, &w1_tilde, &w2_tilde, &w3_tilde, beta, gamma);

		let v_0_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &v_0_tilde).unwrap();

		util::append_commitment_to_transcript::<E>(&mut transcript, b"v_0_tilde_commit", &v_0_tilde_commit);

		let (v_1_tilde, u_0_tilde, u_1_tilde) = Self::compute_v_1_u_0_u_1_tilde(log_number_of_gates, &v_0_tilde);
		
		let v_1_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &v_1_tilde).unwrap();
		let u_0_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &u_0_tilde).unwrap();
		let u_1_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &u_1_tilde).unwrap();

		util::append_commitment_to_transcript::<E>(&mut transcript, b"v_1_tilde_commit", &v_1_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"u_0_tilde_commit", &u_0_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"u_1_tilde_commit", &u_1_tilde_commit);

		let xi = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"xi");
		let tau = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"tau", log_number_of_gates);

		let mut eq_tilde = Self::compute_eq_tilde(log_number_of_gates, &tau);

		let mut eq_tilde_copy = eq_tilde.clone();
		let mut w1_tilde_copy = w1_tilde.clone();
		let mut w2_tilde_copy = w2_tilde.clone();
		let mut w3_tilde_copy = w3_tilde.clone();
		let mut qM_copy = ckt.qM.clone();
		let mut qL_copy = ckt.qL.clone();
		let mut qR_copy = ckt.qR.clone();
		let mut qO_copy = ckt.qO.clone();
		let mut qC_copy = ckt.qC.clone();
		let mut sigma_1_copy = ckt.sigma_1.clone();
		let mut sigma_2_copy = ckt.sigma_2.clone();
		let mut sigma_3_copy = ckt.sigma_3.clone();
		let mut id_1_copy = ckt.id_1.clone();
		let mut id_2_copy = ckt.id_2.clone();
		let mut id_3_copy = ckt.id_3.clone();
		let mut v_0_tilde_copy = v_0_tilde.clone();
		let mut v_1_tilde_copy = v_1_tilde.clone();
		let mut u_0_tilde_copy = u_0_tilde.clone();
		let mut u_1_tilde_copy = u_1_tilde.clone();

		let mut mlp_set = vec![&mut eq_tilde_copy, &mut w1_tilde_copy, &mut w2_tilde_copy, &mut w3_tilde_copy, 
			 &mut qM_copy, &mut qL_copy, &mut qR_copy, &mut qO_copy, &mut qC_copy, 
			 &mut sigma_1_copy, &mut sigma_2_copy, &mut sigma_3_copy, 
			 &mut id_1_copy, &mut id_2_copy, &mut id_3_copy, 
			 &mut v_0_tilde_copy, &mut v_1_tilde_copy, &mut u_0_tilde_copy, &mut u_1_tilde_copy];

		let mut coeffs: Vec<_> = Vec::new();
		let mut alphas: Vec<_> = Vec::new();

		for i in 0..number_of_initial_rounds {
		    // we use 1,2,..,5 as the evaluation points, then at verifier end evaluation at zero is determined by subtracting evaluation at one from previous round evaluation 
			let d_plus_one_evaluation_points = (1..=5).map(|x| E::ScalarField::from(x as u64)).collect::<Vec<_>>();
			if i > 0 {
				let alpha = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha");
				for mlp in mlp_set.iter_mut() {
					**mlp = (*mlp).fix_variables(&[alpha]);
				}
				alphas.push(alpha);
			}
			let mut d_plus_one_evaluations = vec![E::ScalarField::zero(); d_plus_one_evaluation_points.len()];
			for j in 0..d_plus_one_evaluation_points.len() {
				d_plus_one_evaluations[j] = Self::compute_univariate_r_X_evaluation(&mut mlp_set, d_plus_one_evaluation_points[j], xi, beta, gamma);
			}
			util::append_field_element_vector_to_transcript::<E>(&mut transcript, b"d_plus_one_evaluations", &d_plus_one_evaluations);
			coeffs.push(d_plus_one_evaluations);
		}
		let alpha_nu = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_nu");
		for mlp in mlp_set.iter_mut() {
			**mlp = (*mlp).fix_variables(&[alpha_nu]);
		}
		alphas.push(alpha_nu);

		// the initial rounds of conventional (hyperplonk-like) multivariate sumcheck is done till this point

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

	    /* Here, G_bar = eq_bar * (
	    					(qM_bar * w1_bar * w2_bar + qL_bar * w1_bar + qR_bar * w2_bar + qO_bar * w3_bar + qC_bar) + 
	    					xi * (v0_bar * ... - ...) + 
	    					xi^2 * (v1_bar - u0_bar * u1_bar)).
	    		Each of the (m-1)-deg univariate polynomial in the expression is contained in O_bar_set. */

	    let G_bar = Self::compute_G_bar_from_O_bar_set(&O_bar_set, beta, gamma, xi);

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
	    let V_w1 = O_bar_set[1].evaluate(&z);
	    let V_w2 = O_bar_set[2].evaluate(&z);
	    let V_w3 = O_bar_set[3].evaluate(&z);
	    let V_sigma1 = O_bar_set[9].evaluate(&z);
	    let V_sigma2 = O_bar_set[10].evaluate(&z);
	    let V_sigma3 = O_bar_set[11].evaluate(&z);
	    let V_id1 = O_bar_set[12].evaluate(&z);
	    let V_id2 = O_bar_set[13].evaluate(&z);
	    let V_id3 = O_bar_set[14].evaluate(&z);
	    let V_u0 = O_bar_set[17].evaluate(&z);

	    let G_prime = Self::compute_G_prime(&O_bar_set, &g_hat, &h_hat, xi, beta, gamma, z, m, V_eq, V_w1, V_w2, V_w3, V_sigma1, V_sigma2, V_sigma3, V_id1, V_id2, V_id3, V_u0);

	    let alpha_ = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_");
	    let mut alpha_powers : Vec<E::ScalarField> = Vec::new();
	    let mut cur = alpha_;
	    for i in 0..11 {
	    	alpha_powers.push(cur);
	    	cur = cur * alpha_;
	    }

	    let F_bar = Self::compute_F_bar(&O_bar_set, &G_prime, &alpha_powers);

	    let F_bar_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &F_bar).unwrap();
	    util::append_commitment_to_transcript::<E>(&mut transcript, b"F_bar_commit", &F_bar_commit);

	    let F_bar_eval_proof = SamaritanMLPCS::<E>::kzg10_eval_prove(&srs, &F_bar, z).unwrap();

	    let a_vec = vec![alpha_powers[0], alpha_powers[1], alpha_powers[2], alpha_powers[3], V_eq * V_w1 * V_w2, V_eq * V_w1, V_eq * V_w2, V_eq * V_w3, V_eq,
	    					alpha_powers[4], alpha_powers[5], alpha_powers[6], alpha_powers[7], alpha_powers[8], alpha_powers[9], 
	    					V_eq * xi * (V_w1 + beta * V_sigma1 + gamma) * (V_w2 + beta * V_sigma2 + gamma) * (V_w3 + beta * V_sigma3 + gamma), V_eq * xi * xi,
	    					alpha_powers[10], - (V_eq * xi * xi * V_u0)];

	    // H_bar is "a_vec"-linear combination of the (m-1)-degree univariate polynomials in O_bar_set.

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

	    let K_ext_hat_commit = Self::compute_K_ext_hat_commit(&srs, &K_hat, number_of_initial_rounds);

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

	    let v0_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(v_0_tilde.to_evaluations());
	    let v1_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(v_1_tilde.to_evaluations());
	    let u0_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(u_0_tilde.to_evaluations());
	    let u1_hat = DensePolynomial::<E::ScalarField>::from_coefficients_vec(u_1_tilde.to_evaluations());

	    // According to unrolled Hybridplonk prover, at this point there should be degree check equation d(X) and corresponding D(X), but we defer it and merge it with 
	    // the degree check bound and other polynomial identity checks of unrolled Samaritan MLPCS, in order to save MSM cost and pairing check cost (one pairing check
	    // performed instead of two (one inside Samaritan MLPCS verifier and the other inside Hybridplonk verifier))

	    let r = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"r");
	    let r_inverse = r.inverse().unwrap();

	    let W1 = (&v0_hat + &v1_hat * r).evaluate(&r.pow(&[2 as u64]));
	    let W2 = K_hat.evaluate(&r.pow(&[(1 << number_of_initial_rounds) as u64]));
	    let W3 = t_hat.evaluate(&r_inverse);
	    let W4 = H_bar.evaluate(&r_inverse);
	    let W5 = A_hat.evaluate(&r_inverse);
	    let W6 = S_hat.evaluate(&r_inverse);

	    let uv_left = &u0_hat + &u1_hat * r.pow(&[number_of_gates as u64]);

	    let B_hat_delta_inv_eval = Self::evaluate_B_hat_at_point(&eta, &(delta * r_inverse), kappa);

	    let e_hat_inv_eval = Self::evaluate_e_hat_at_point(kappa, &y, &r_inverse);

	    let S_equality_left = (&H_bar * W3 + &t_hat * W4) + (&A_hat * e_hat_inv_eval) * epsilon + (&A_hat * B_hat_delta_inv_eval) * epsilon * epsilon - &S_hat * r;


		let eq_tilde_val = Self::evaluate_eq_tilde_at_point(log_number_of_gates, &tau, &eval_point);

		let mut linear_combined_orig_mlps_and_K_ext_tilde_evals: Vec<_> = Vec::new();
		for i in 0..number_of_gates {
			let term = w1_tilde[i] * a_vec[1] + w2_tilde[i] * a_vec[2] + w3_tilde[i] * a_vec[3] + 
					ckt.qM[i] * a_vec[4] + ckt.qL[i] * a_vec[5] + ckt.qR[i] * a_vec[6] + ckt.qO[i] * a_vec[7] + ckt.qC[i] * a_vec[8] + 
					ckt.sigma_1[i] * a_vec[9] + ckt.sigma_2[i] * a_vec[10] + ckt.sigma_3[i] * a_vec[11] + ckt.id_1[i] * a_vec[12] + ckt.id_2[i] * a_vec[13] + ckt.id_3[i] * a_vec[14] + 
					v_0_tilde[i] * a_vec[15] + v_1_tilde[i] * a_vec[16] + u_0_tilde[i] * a_vec[17] + u_1_tilde[i] * a_vec[18] + K_ext_tilde[i] * epsilon;
			linear_combined_orig_mlps_and_K_ext_tilde_evals.push(term);
		}

		let combined_mlp = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_number_of_gates, linear_combined_orig_mlps_and_K_ext_tilde_evals);
		let combined_mlp_eval = (E::ScalarField::one() + epsilon) * V_y - eq_tilde_val * a_vec[0];


		// let combined_mlp_eval_proof = SamaritanMLPCS::<E>::prove(&srs, &combined_mlp, &eval_point, combined_mlp_eval, &mut rng).unwrap();
		// Start the unrolled Samaritan MLPCS prover here, instead of calling its prove function directly.

		let mu_: usize = combined_mlp.num_vars;
		// assert_eq!(mu_, log_number_of_gates);
        let kappa_ = (mu_ as f64).log2().round() as i32;
        let nu_: i32 = (mu_ as i32) - kappa_;
        let n_: usize = 2usize.pow(mu_ as u32);
        let m_: usize = 2usize.pow(kappa_ as u32);
        let l_: usize = 2usize.pow(nu_ as u32);
        let max_deg_: usize = n_;

        let f_hat_mlp = SamaritanMLPCS::<E>::get_univariate_from_multilinear(&combined_mlp);

        //the v_i's, where v_i = g_i(z_x) = f(z_x, <i>) for all i\in[l]
        let g_evaluation_values: Vec<_> = SamaritanMLPCS::<E>::get_evaluation_set(&combined_mlp, &eval_point, kappa_ as usize, nu_ as usize);

        //the polynomial v(x)=\sum_{i=1}^l X^{i-1}v_i
        let v_hat_mlp = DensePolynomial::<E::ScalarField>::from_coefficients_vec(g_evaluation_values);

        //commit to v(x)
        let v_hat_commit_mlp = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &v_hat_mlp).unwrap();

        util::append_commitment_to_transcript::<E>(&mut transcript, b"v_hat_commit_mlp", &v_hat_commit_mlp);

        //choosing a random field element \gamma, supposed to be verifier's choice, will edit the code to emulate RO behaviour to generate it from H(transcript till the point) 
        let gamma_ = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"gamma_");

        //compute v_gamma = v(\gamma)
        let v_gamma_ = v_hat_mlp.evaluate(&gamma_);
        util::append_field_element_to_transcript::<E>(&mut transcript, b"v_gamma_", &v_gamma_);

        // divide the univariate polynomial into multiple chunks and return those chunks as vectors of univariate polynomials
        let all_gxs_mlp: Vec<_> = SamaritanMLPCS::<E>::divide_into_univ_polynomial_chunks(&f_hat_mlp, m_, n_);

        // linearly combine those small univariate polynomials 
        let p_hat_mlp = SamaritanMLPCS::<E>::linear_combination_of_polynomials(&all_gxs_mlp, gamma_, l_);

        // commit to linearly_combined_poly, p_hat(x) = \sum_{i=1}^l\gamma^{i-1}g_i(x)
        let p_hat_commit_mlp = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &p_hat_mlp).unwrap();

        util::append_commitment_to_transcript::<E>(&mut transcript, b"p_hat_commit_mlp", &p_hat_commit_mlp);

        #[allow(non_snake_case)]
        let psi_hat_X_zy_mlp = SamaritanMLPCS::<E>::compute_psi_hat_X_zy(&eval_point, kappa_ as usize, nu_ as usize);

        #[allow(non_snake_case)]
        let phi_hat_X_gamma_mlp = SamaritanMLPCS::<E>::compute_phi_hat_X_gamma(&gamma_, nu_ as usize);

        let alpha_ = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_");

        // v_psi_phi_combined = v * (psi + (alpha * phi))
        let v_psi_phi_combined_mlp = &v_hat_mlp * (&psi_hat_X_zy_mlp + (&phi_hat_X_gamma_mlp) * alpha_);

        // extract necessary (l-1) terms in b_hat
        let least_coeffs_mlp = v_psi_phi_combined_mlp.coeffs()[..(l_-1)].to_vec();
        let b_hat_mlp = DensePolynomial::<E::ScalarField>::from_coefficients_vec(least_coeffs_mlp);

        // compute commitment to b_hat
        let b_hat_commit_mlp = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &b_hat_mlp).unwrap();
        util::append_commitment_to_transcript::<E>(&mut transcript, b"b_hat_commit_mlp", &b_hat_commit_mlp);

        // compute psi_hat(X;zx)
        #[allow(non_snake_case)]
        let psi_hat_X_zx_mlp = SamaritanMLPCS::<E>::compute_psi_hat_X_zx(&eval_point, kappa_ as usize, nu_ as usize);

        // compute p_hat(x) * psi_hat(X;zx)
        let p_psi_combined_mlp = &p_hat_mlp * &psi_hat_X_zx_mlp;

        // extract necessary (m-1) number of terms in u_hat
        let selected_coeffs_mlp = p_psi_combined_mlp.coeffs()[..(m_ - 1)].to_vec();
        let u_hat_mlp = DensePolynomial::<E::ScalarField>::from_coefficients_vec(selected_coeffs_mlp);

        let u_hat_commit_mlp = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &u_hat_mlp).unwrap();
        util::append_commitment_to_transcript::<E>(&mut transcript, b"u_hat_commit_mlp", &u_hat_commit_mlp);

        let (t_hat_mlp, t_hat_commit_mlp) = Self::compute_t_hat_mlp_and_its_commit(&srs, &u0_hat, &u_0_tilde_commit, &u1_hat, &u_1_tilde_commit, 
        	&v0_hat, &v_0_tilde_commit, &v1_hat, &v_1_tilde_commit, &K_hat, &h_hat, 
        	&v_psi_phi_combined_mlp, &b_hat_mlp, &p_psi_combined_mlp, &u_hat_mlp, &f_hat_mlp, &p_hat_mlp,
			combined_mlp_eval, v_gamma_, alpha_, gamma_, epsilon, number_of_gates, m, l_, m_);
        
        util::append_commitment_to_transcript::<E>(&mut transcript, b"t_hat_commit_mlp", &t_hat_commit_mlp);

        let s_hat_mlp = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); max_deg_ - n_ + 1], t_hat_mlp.coeffs().to_vec()].concat());

        let s_hat_commit_mlp = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &s_hat_mlp).unwrap();
        util::append_commitment_to_transcript::<E>(&mut transcript, b"s_hat_commit_mlp", &s_hat_commit_mlp);

        let psi_hat_X_zy_at_r_mlp = SamaritanMLPCS::<E>::evaluate_psi_hat_X_zy_at_delta(&eval_point, &r, kappa_ as usize, nu_ as usize);
        let phi_hat_X_gamma_at_r_mlp = SamaritanMLPCS::<E>::evaluate_phi_hat_X_gamma_at_delta(&gamma_, &r, nu_ as usize);
        let psi_hat_X_zx_at_r_mlp = SamaritanMLPCS::<E>::evaluate_psi_hat_X_zx_at_delta(&eval_point, &r, kappa_ as usize, nu_ as usize);

        let deg_check_left = &t_hat_mlp - &u0_hat - &u1_hat * epsilon - &v0_hat * epsilon.pow(&[2 as u64]) - &v1_hat * epsilon.pow(&[3 as u64]) 
	    						- &K_hat * r.pow(&[(number_of_gates - m) as u64]) * epsilon.pow(&[4 as u64]) - &h_hat * r.pow(&[(number_of_gates - m + 1) as u64]) * epsilon.pow(&[5 as u64])
	    						- &v_hat_mlp * (epsilon.pow(&[6 as u64]) * r_inverse.pow(&[l_ as u64]) * (psi_hat_X_zy_at_r_mlp + alpha_ * phi_hat_X_gamma_at_r_mlp))
	    						+ &b_hat_mlp * (epsilon.pow(&[6 as u64]) * r_inverse.pow(&[l_ as u64]) - epsilon.pow(&[12 as u64]) * r.pow(&[(n_-l_+1) as u64]))
	    						+ &p_hat_mlp * (epsilon.pow(&[8 as u64]) * (r.pow(&[m_ as u64]) - gamma_).inverse().unwrap() - epsilon.pow(&[7 as u64]) * psi_hat_X_zx_at_r_mlp * r_inverse.pow(&[m_ as u64]) - epsilon.pow(&[10 as u64]) * r.pow(&[(n_ - m_) as u64]))
	    						+ &u_hat_mlp * (epsilon.pow(&[7 as u64]) * r_inverse.pow(&[m_ as u64]) - epsilon.pow(&[11 as u64]) * r.pow(&[(n_ - m_ + 1) as u64]))
	    						- &f_hat_mlp * (epsilon.pow(&[8 as u64]) * (r.pow(&[m_ as u64]) - gamma_).inverse().unwrap() + epsilon.pow(&[9 as u64]));


	    let phi = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"phi");

	    let L_hat = uv_left + K_ext_hat * phi + S_equality_left * phi.pow(&[2 as u64]) + deg_check_left * phi.pow(&[3 as u64]);

	    let L_hat_eval_proof = SamaritanMLPCS::<E>::kzg10_eval_prove(&srs, &L_hat, r).unwrap();

		let proof = HybridPlonkProof{
			number_of_initial_rounds,
			w1_tilde_commit,
			w2_tilde_commit,
			w3_tilde_commit,
			v_0_tilde_commit,
			v_1_tilde_commit,
			u_0_tilde_commit,
			u_1_tilde_commit,
			coeffs,
			g_hat_commit,
			h_hat_commit,
			V_eq,
			V_w1,
			V_w2,
			V_w3,
			V_sigma1,
			V_sigma2,
			V_sigma3,
			V_id1,
			V_id2,
			V_id3,
			V_u0,
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
			W1,
			W2,
			W3,
			W4,
			W5,
			W6,

			v_hat_commit_mlp,
		    v_gamma_,
		    p_hat_commit_mlp,
		    b_hat_commit_mlp,
		    u_hat_commit_mlp,
		    t_hat_commit_mlp,
		    s_hat_commit_mlp,
		    L_hat_eval_proof,
		};
		// end_timer!(prover_time);
		Ok(proof)
	}

	pub fn verify(proof: &HybridPlonkProof<E>, ckt: &HybridPlonkCircuit<E>, srs: &SamaritanMLPCS_SRS<E>, 
		qM_comm: Commitment<E>, qL_comm: Commitment<E>, qR_comm: Commitment<E>, qO_comm: Commitment<E>, qC_comm:Commitment<E>, 
        	sigma1_comm: Commitment<E>, sigma2_comm: Commitment<E>, sigma3_comm: Commitment<E>, 
        	id1_comm: Commitment<E>, id2_comm: Commitment<E>, id3_comm: Commitment<E>) -> Result<bool, Error> {
		// let verifier_time = start_timer!(|| format!("HybridPlonk::verify with multilinear polynomial"));

        let mut transcript = Transcript::new(b"HybridPlonk Transcript");

        let log_number_of_gates = ckt.log_number_of_gates;
        let number_of_gates = 1 << log_number_of_gates;
		let number_of_wires = ckt.number_of_wires;
		let number_of_initial_rounds = proof.number_of_initial_rounds;

		let kappa = log_number_of_gates - number_of_initial_rounds;
		let m = 1 << kappa;

        util::append_commitment_to_transcript::<E>(&mut transcript, b"w1_tilde_commit", &proof.w1_tilde_commit);
        util::append_commitment_to_transcript::<E>(&mut transcript, b"w2_tilde_commit", &proof.w2_tilde_commit);
        util::append_commitment_to_transcript::<E>(&mut transcript, b"w3_tilde_commit", &proof.w3_tilde_commit);

		let beta = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"beta");
		let gamma = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"gamma");

		util::append_commitment_to_transcript::<E>(&mut transcript, b"v_0_tilde_commit", &proof.v_0_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"v_1_tilde_commit", &proof.v_1_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"u_0_tilde_commit", &proof.u_0_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"u_1_tilde_commit", &proof.u_1_tilde_commit);

		let xi = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"xi");
		let tau = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"tau", log_number_of_gates);
		let mut alphas: Vec<_> = Vec::new();
		let mut cur_eval_value = E::ScalarField::zero();
        let mut d_plus_one_evaluation_points = (1..=5).map(|x| E::ScalarField::from(x as u64)).collect::<Vec<_>>();
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
	    for i in 0..11 {
	    	alpha_powers.push(cur);
	    	cur = cur * alpha_;
	    }
		
	    let V = proof.V_eq * alpha_powers[0] + proof.V_w1 * alpha_powers[1] + proof.V_w2 * alpha_powers[2] + proof.V_w3 * alpha_powers[3]
	    		+ proof.V_sigma1 * alpha_powers[4] + proof.V_sigma2 * alpha_powers[5] + proof.V_sigma3 * alpha_powers[6]
	    		+ proof.V_id1 * alpha_powers[7] + proof.V_id2 * alpha_powers[8] + proof.V_id3 * alpha_powers[9]
	    		+ proof.V_u0 * alpha_powers[10] + cur_eval_value * E::ScalarField::from(m as u64).inverse().unwrap();
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

	    let r = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"r");

	    let K_ext_hat_eval = proof.W2 * (r.pow(&[(1 << number_of_initial_rounds) as u64]) - E::ScalarField::from(1 as u64)) * (r - E::ScalarField::from(1 as u64)).inverse().unwrap();

	    let r_inverse = r.inverse().unwrap();

	    let B_hat_delta_eval = Self::evaluate_B_hat_at_point(&eta, &(delta * r), kappa);
	    let B_hat_delta_inv_eval = Self::evaluate_B_hat_at_point(&eta, &(delta * r_inverse), kappa);

	    let e_hat_eval = Self::evaluate_e_hat_at_point(kappa, &y, &r);
	    let e_hat_inv_eval = Self::evaluate_e_hat_at_point(kappa, &y, &r_inverse);

		let combined_eval = (proof.V_y + proof.eval_for_eta * epsilon + proof.eval_for_delta * epsilon * epsilon) * E::ScalarField::from(2 as u64) + r_inverse * proof.W6 - epsilon * proof.W5 * e_hat_eval - epsilon * epsilon * proof.W5 * B_hat_delta_eval;

        let mut eval_point = Vec::new();
	    eval_point.extend_from_slice(&alphas);
	    eval_point.extend_from_slice(&y);

        let a_vec = vec![alpha_powers[0], alpha_powers[1], alpha_powers[2], alpha_powers[3], proof.V_eq * proof.V_w1 * proof.V_w2, proof.V_eq * proof.V_w1, proof.V_eq * proof.V_w2, proof.V_eq * proof.V_w3, proof.V_eq,
	    					alpha_powers[4], alpha_powers[5], alpha_powers[6], alpha_powers[7], alpha_powers[8], alpha_powers[9], 
	    					proof.V_eq * xi * (proof.V_w1 + beta * proof.V_sigma1 + gamma) * (proof.V_w2 + beta * proof.V_sigma2 + gamma) * (proof.V_w3 + beta * proof.V_sigma3 + gamma), proof.V_eq * xi * xi,
	    					alpha_powers[10], - (proof.V_eq * xi * xi * proof.V_u0)];
        let eq_tilde_val = Self::evaluate_eq_tilde_at_point(log_number_of_gates, &tau, &eval_point);

		let combined_mlp_commit: ark_poly_commit::kzg10::Commitment<E> = Commitment(E::G1::msm(
	    							&vec![proof.w1_tilde_commit.0, proof.w2_tilde_commit.0, proof.w3_tilde_commit.0, qM_comm.0, qL_comm.0, qR_comm.0, qO_comm.0, qC_comm.0, 
	    								sigma1_comm.0, sigma2_comm.0, sigma3_comm.0, id1_comm.0, id2_comm.0, id3_comm.0,
		    							proof.v_0_tilde_commit.0, proof.v_1_tilde_commit.0, proof.u_0_tilde_commit.0, proof.u_1_tilde_commit.0,
		    							proof.K_ext_hat_commit.0],
		    						&vec![a_vec[1], a_vec[2], a_vec[3], a_vec[4], a_vec[5], a_vec[6], a_vec[7], a_vec[8], a_vec[9], a_vec[10], a_vec[11], a_vec[12], a_vec[13], a_vec[14], a_vec[15], a_vec[16], a_vec[17], a_vec[18], epsilon]
		    						).unwrap().into_affine());
		let combined_mlp_eval = (E::ScalarField::one() + epsilon) * proof.V_y - eq_tilde_val * a_vec[0];
		


		// let combined_mlp_check = SamaritanMLPCS::<E>::verify(&srs, &combined_mlp_commit, &eval_point, combined_mlp_eval, &proof.combined_mlp_eval_proof).unwrap();
		// instead of calling Samaritan MLPCS verifier directly, we unroll it in the following. 

		let mu_: usize = eval_point.len();
        let kappa_ = (mu_ as f64).log2().round() as i32;
        let nu_: i32 = (mu_ as i32)- kappa_;
        let n_: usize = 2usize.pow(mu_ as u32);
        let m_: usize = 2usize.pow(kappa_ as u32);
        let l_: usize = 2usize.pow(nu_ as u32);
        let max_deg_: usize = n_;

        util::append_commitment_to_transcript::<E>(&mut transcript, b"v_hat_commit_mlp", &proof.v_hat_commit_mlp);

        let gamma_ = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"gamma_");

        util::append_field_element_to_transcript::<E>(&mut transcript, b"v_gamma_", &proof.v_gamma_);
        util::append_commitment_to_transcript::<E>(&mut transcript, b"p_hat_commit_mlp", &proof.p_hat_commit_mlp);

        let alpha_ = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_");

        util::append_commitment_to_transcript::<E>(&mut transcript, b"b_hat_commit_mlp", &proof.b_hat_commit_mlp);
        util::append_commitment_to_transcript::<E>(&mut transcript, b"u_hat_commit_mlp", &proof.u_hat_commit_mlp);

        util::append_commitment_to_transcript::<E>(&mut transcript, b"t_hat_commit_mlp", &proof.t_hat_commit_mlp);
        util::append_commitment_to_transcript::<E>(&mut transcript, b"s_hat_commit_mlp", &proof.s_hat_commit_mlp);

        let phi = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"phi");

        let psi_hat_X_zy_at_r_mlp = SamaritanMLPCS::<E>::evaluate_psi_hat_X_zy_at_delta(&eval_point, &r, kappa_ as usize, nu_ as usize);
        let phi_hat_X_gamma_at_r_mlp = SamaritanMLPCS::<E>::evaluate_phi_hat_X_gamma_at_delta(&gamma_, &r, nu_ as usize);
        let psi_hat_X_zx_at_r_mlp = SamaritanMLPCS::<E>::evaluate_psi_hat_X_zx_at_delta(&eval_point, &r, kappa_ as usize, nu_ as usize);

        let deg_check_eval = -(epsilon.pow(&[6 as u64]) * r_inverse * (combined_mlp_eval + alpha_ * proof.v_gamma_) + epsilon.pow(&[7 as u64]) * r_inverse * proof.v_gamma_);

        let comm_list = vec![proof.u_0_tilde_commit.0, proof.u_1_tilde_commit.0, 
	    			proof.K_ext_hat_commit.0, 
	    			proof.H_bar_commit.0, proof.t_hat_commit.0, 
	    			proof.A_hat_commit.0, proof.S_hat_commit.0, 
	    			// proof.q_hat_commit_mlp.0, 
	    			proof.t_hat_commit_mlp.0, 
	    			proof.v_0_tilde_commit.0, proof.v_1_tilde_commit.0, 
	    			proof.K_hat_commit.0, 
	    			proof.h_hat_commit.0,
	    			proof.v_hat_commit_mlp.0, 
	    			proof.b_hat_commit_mlp.0,
	    			proof.p_hat_commit_mlp.0, 
	    			proof.u_hat_commit_mlp.0, 
	    			combined_mlp_commit.0];
	    let scalar_list = vec![E::ScalarField::one() - phi.pow(&[3 as u64]), r.pow(&[number_of_gates as u64]) - epsilon * phi.pow(&[3 as u64]),
	    			phi, 
	    			proof.W3 * phi.pow(&[2 as u64]), proof.W4 * phi.pow(&[2 as u64]),
	    			(epsilon * epsilon * B_hat_delta_inv_eval + epsilon * e_hat_inv_eval) * phi.pow(&[2 as u64]), - (r * phi.pow(&[2 as u64])),
	    			// phi.pow(&[3 as u64]), 
	    			phi.pow(&[3 as u64]), 
	    			- epsilon.pow(&[2 as u64]) * phi.pow(&[3 as u64]), - epsilon.pow(&[3 as u64]) * phi.pow(&[3 as u64]), 
	    			- r.pow(&[(number_of_gates - m) as u64]) * epsilon.pow(&[4 as u64]) * phi.pow(&[3 as u64]), 
	    			- r.pow(&[(number_of_gates - m + 1) as u64]) * epsilon.pow(&[5 as u64]) * phi.pow(&[3 as u64]),
	    			- (psi_hat_X_zy_at_r_mlp + phi_hat_X_gamma_at_r_mlp * alpha_) * phi.pow(&[3 as u64]) * epsilon.pow(&[6 as u64]) * r_inverse.pow(&[l_ as u64]),
	    			phi.pow(&[3 as u64]) * (epsilon.pow(&[6 as u64]) * r_inverse.pow(&[l_ as u64]) - epsilon.pow(&[12 as u64]) * r.pow(&[(n_-l_+1) as u64])),
	    			phi.pow(&[3 as u64]) * (epsilon.pow(&[8 as u64]) * (r.pow(&[m_ as u64]) - gamma_).inverse().unwrap() - epsilon.pow(&[7 as u64]) * psi_hat_X_zx_at_r_mlp * r_inverse.pow(&[m_ as u64]) - epsilon.pow(&[10 as u64]) * r.pow(&[(n_ - m_) as u64])),
	    			phi.pow(&[3 as u64]) * (epsilon.pow(&[7 as u64]) * r_inverse.pow(&[m_ as u64]) - epsilon.pow(&[11 as u64]) * r.pow(&[(n_ - m_ + 1) as u64])),
	    			- phi.pow(&[3 as u64]) * (epsilon.pow(&[8 as u64]) * (r.pow(&[m_ as u64]) - gamma_).inverse().unwrap() + epsilon.pow(&[9 as u64]))];

	    // phi_combined_univariates_commit is the computation of commitment of L_hat as a linear combination of other available commiments present in the proof 
	    let phi_combined_univariates_commit = Commitment(E::G1::msm(&comm_list, &scalar_list).unwrap().into_affine());
	    let phi_combined_eval = proof.W1 + K_ext_hat_eval * phi + combined_eval * phi.pow(&[2 as u64]) + deg_check_eval * phi.pow(&[3 as u64]);

	    let L_equality_check = SamaritanMLPCS::<E>::kzg10_eval_proof_verify(&srs, &phi_combined_univariates_commit, r, phi_combined_eval, &proof.L_hat_eval_proof).unwrap();

        let pairing_lhs_first = E::G1Prepared::from(proof.t_hat_commit_mlp.0);
        let pairing_lhs_second = srs.powers_of_h[max_deg_ - n_ + 1];
        let pairing_lhs_res = E::pairing(pairing_lhs_first, pairing_lhs_second);

        let pairing_rhs_first = E::G1Prepared::from(proof.s_hat_commit_mlp.0);
        let pairing_rhs_second = srs.powers_of_h[0];
        let pairing_rhs_res = E::pairing(pairing_rhs_first, pairing_rhs_second); 

        // end_timer!(verifier_time);
        // Note that L_equality_check includes uv_equality_check, K_ext_hat_equality_check, S_equality_check, and deg_check together.
        Ok(F_bar_equality_check && L_equality_check && pairing_lhs_res == pairing_rhs_res)

	}
}

#[cfg(test)]
mod tests {
    #![allow(non_camel_case_types)]

    use std::time::Instant;
    use ark_poly_commit::*;
    use ark_ec::pairing::Pairing;
    use ark_bls12_381::Bls12_381;
    use ark_bls12_381::Fr;
    // use ark_bn254::Bn254;
    // use ark_bn254::Fr;
    use ark_std::test_rng;
    use ark_std::{rand::Rng, vec::Vec};
	use ark_std::rand::seq::SliceRandom;
    use crate::samaritan_mlpcs::*;
    use crate::hybridplonk::*;

    type SamaritanMLPCS_Bls12_381 = SamaritanMLPCS<Bls12_381>;
    type HybridPlonk_Bls12_381 = HybridPlonk<Bls12_381>;
    // type SamaritanMLPCS_Bn254 = SamaritanMLPCS<Bn254>;
    // type HybridPlonk_Bn254 = HybridPlonk<Bn254>;

    #[test]
    fn functionality_test(){
    	let mut rng = &mut test_rng();
        // n is the dimension of each of the two vectors (A and B) participating in inner product. (2*n) is the number of gates in the circuit. 2^(n+1) is the size of
    	// evaluation vecs of each mlp. In short #vars = (n + 1).
    	let n: usize = 1 << 19;
    	let A: Vec<usize> = (0..n).map(|_| rng.gen_range(1..5)).collect();
    	let B: Vec<usize> = (0..n).map(|_| rng.gen_range(1..5)).collect();
    	let myckt: HybridPlonkCircuit::<Bls12_381> = HybridPlonk_Bls12_381::generate_circuit_for_inner_product(&A, &B, n);

    	let mut w1_vec: Vec<_> = Vec::new();
    	let mut w2_vec: Vec<_> = Vec::new();
    	let mut w3_vec: Vec<_> = Vec::new();

    	for i in 0..n {
    		w1_vec.push(Fr::from(A[i] as u64));
    		w2_vec.push(Fr::from(B[i] as u64));
    		w3_vec.push(Fr::from((A[i] * B[i]) as u64));
    	}

    	for i in 0..n {
    		if i == 0 {
    			w1_vec.push(w1_vec[0] * w2_vec[0]);
    		}
    		else{
    			w1_vec.push(w1_vec[n + i - 1] + w2_vec[n + i -1]);
    		}
    		if i == n-1 {
    			w2_vec.push(Fr::zero());
    		}
    		else{
    			w2_vec.push(w1_vec[i + 1] * w2_vec[i + 1]);
    		}
    		w3_vec.push(w1_vec[n + i] + w2_vec[n + i]);
    	}



    	let w1 = DenseMultilinearExtension::from_evaluations_vec(myckt.log_number_of_gates, w1_vec);
    	let w2 = DenseMultilinearExtension::from_evaluations_vec(myckt.log_number_of_gates, w2_vec);
    	let w3 = DenseMultilinearExtension::from_evaluations_vec(myckt.log_number_of_gates, w3_vec);

    	let (srs, 
    		qM_comm, qL_comm, qR_comm, qO_comm, qC_comm, 
        	sigma1_comm, sigma2_comm, sigma3_comm, 
        	id1_comm, id2_comm, id3_comm) = HybridPlonk_Bls12_381::setup(&myckt, &mut rng).unwrap();

    	// let prover_time = start_timer!(||"prover time");
    	let hybridplonk_proof = HybridPlonk_Bls12_381::prove(&myckt, &w1, &w2, &w3, &srs).unwrap();
    	// end_timer!(prover_time);

    	println!("number of initial rounds: {}", hybridplonk_proof.number_of_initial_rounds);

    	// let verifier_time = start_timer!(||"verifier time");
        let valid = HybridPlonk_Bls12_381::verify(&hybridplonk_proof, &myckt, &srs, 
        	qM_comm, qL_comm, qR_comm, qO_comm, qC_comm, 
        	sigma1_comm, sigma2_comm, sigma3_comm, 
        	id1_comm, id2_comm, id3_comm).unwrap();
        // end_timer!(verifier_time);

        assert_eq!(valid, true);

    }
}
