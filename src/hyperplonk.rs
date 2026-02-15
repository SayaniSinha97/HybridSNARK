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

pub struct HyperPlonkCircuit<E: Pairing> {
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

pub struct HyperPlonkProof<E: Pairing> {
	num_rounds: usize,
	w1_tilde_commit: Commitment<E>,
	w2_tilde_commit: Commitment<E>,
	w3_tilde_commit: Commitment<E>,
	v_0_tilde_commit: Commitment<E>,
	v_1_tilde_commit: Commitment<E>,
	u_0_tilde_commit: Commitment<E>,
	u_1_tilde_commit: Commitment<E>,
	eval_w1_tilde_at_alphas: E::ScalarField,
	eval_w2_tilde_at_alphas: E::ScalarField,
	eval_w3_tilde_at_alphas: E::ScalarField,
	eval_u_0_tilde_at_alphas: E::ScalarField,
	eval_sigma1_at_alphas: E::ScalarField,
	eval_sigma2_at_alphas: E::ScalarField,
	eval_sigma3_at_alphas: E::ScalarField,
	eval_id1_at_alphas: E::ScalarField,
	eval_id2_at_alphas: E::ScalarField,
	eval_id3_at_alphas: E::ScalarField,
	combined_mlp_eval_proof: SamaritanMLPCSEvalProof<E>,
	coeffs: Vec<Vec<E::ScalarField>>,
	deg_check_proof: DegreeCheckProof<E>,
}

pub struct HyperPlonk<E: Pairing> {
	_engine: PhantomData<E>,
}

impl<E: Pairing> HyperPlonk<E> {

	/* This function generates a random inner product circuit for two vectors A and B of dimension n. The circuit description is hyperplonk-friendly. The circuit has total
	2n number of gates, among which n gates are for multiplication and the rest n are for addition. Last addition gate is a dummy gate to keep the number_of_gates
	power-of-2. */
	pub fn generate_circuit_for_inner_product(A: &Vec<usize>, B: &Vec<usize>, n: usize) -> HyperPlonkCircuit<E> {
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

		let myckt = HyperPlonkCircuit::<E>{
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

	pub fn setup<R: RngCore>(ckt: &HyperPlonkCircuit<E>, rng: &mut R) -> Result<(SamaritanMLPCS_SRS<E>, Commitment<E>, Commitment<E>, Commitment<E>, Commitment<E>, Commitment<E>,
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

	pub(crate) fn evaluate_eq_tilde_at_point(log_number_of_gates: usize, tau: &Vec<E::ScalarField>, eval_point: &Vec<E::ScalarField>) -> E::ScalarField {
		let mut res = E::ScalarField::one();
		for i in 0..log_number_of_gates {
			res = res * (tau[i] * eval_point[i] + (E::ScalarField::one() - tau[i]) * (E::ScalarField::one() - eval_point[i]));
		}
		res
	}

	pub(crate) fn compute_v_0_tilde(log_number_of_gates: usize, 
									sigma_1: &DenseMultilinearExtension<E::ScalarField>, sigma_2: &DenseMultilinearExtension<E::ScalarField>, sigma_3: &DenseMultilinearExtension<E::ScalarField>,
									id_1: &DenseMultilinearExtension<E::ScalarField>, id_2: &DenseMultilinearExtension<E::ScalarField>, id_3: &DenseMultilinearExtension<E::ScalarField>,
									w1: &DenseMultilinearExtension<E::ScalarField>, w2: &DenseMultilinearExtension<E::ScalarField>, w3: &DenseMultilinearExtension<E::ScalarField>,
									beta: E::ScalarField, gamma: E::ScalarField) -> DenseMultilinearExtension<E::ScalarField> {
		let number_of_gates = 1 << log_number_of_gates;
		let mut res = vec![E::ScalarField::zero(); number_of_gates];

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

	pub(crate) fn compute_v_1_u_0_u_1_tilde(log_number_of_gates: usize, v_0: &DenseMultilinearExtension<E::ScalarField>) -> (DenseMultilinearExtension<E::ScalarField>, DenseMultilinearExtension<E::ScalarField>, DenseMultilinearExtension<E::ScalarField>) {
		let number_of_gates = 2usize.pow(log_number_of_gates as u32);
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

	pub(crate) fn compute_univariate_r_X_evaluation(mlp_set: &mut Vec<&mut DenseMultilinearExtension<E::ScalarField>>, eval_point: E::ScalarField, xi: E::ScalarField, beta: E::ScalarField, gamma: E::ScalarField) -> E::ScalarField {
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

    pub(crate) fn compute_combined_mlp(log_number_of_gates: usize, qM: &DenseMultilinearExtension<E::ScalarField>, qL: &DenseMultilinearExtension<E::ScalarField>, qR: &DenseMultilinearExtension<E::ScalarField>, qO: &DenseMultilinearExtension<E::ScalarField>, qC: &DenseMultilinearExtension<E::ScalarField>, 
    						v_0_tilde: &DenseMultilinearExtension<E::ScalarField>, v_1_tilde: &DenseMultilinearExtension<E::ScalarField>, u_1_tilde: &DenseMultilinearExtension<E::ScalarField>, 
    						eval_w1_tilde_at_alphas: E::ScalarField, eval_w2_tilde_at_alphas: E::ScalarField, eval_w3_tilde_at_alphas: E::ScalarField, eval_u_0_tilde_at_alphas: E::ScalarField, 
    						eval_sigma1_at_alphas: E::ScalarField, eval_sigma2_at_alphas: E::ScalarField, eval_sigma3_at_alphas: E::ScalarField, eval_id1_at_alphas: E::ScalarField, eval_id2_at_alphas: E::ScalarField, eval_id3_at_alphas: E::ScalarField, 
    						alphas: &Vec<E::ScalarField>, beta: E::ScalarField, gamma: E::ScalarField, xi: E::ScalarField, tau: &Vec<E::ScalarField>) -> DenseMultilinearExtension<E::ScalarField> {
    	let number_of_gates = 1 << log_number_of_gates;

    	let eval_eq_tilde_at_alphas = Self::evaluate_eq_tilde_at_point(log_number_of_gates, &tau, &alphas);

    	let mut combined_mlp_evals: Vec<_> = Vec::new();
    	for i in 0..number_of_gates {
    		let elem = eval_eq_tilde_at_alphas * (qM[i] * eval_w1_tilde_at_alphas * eval_w2_tilde_at_alphas + qL[i] * eval_w1_tilde_at_alphas + qR[i] * eval_w2_tilde_at_alphas + qO[i] * eval_w3_tilde_at_alphas + qC[i] +
    					xi * v_0_tilde[i] * (eval_w1_tilde_at_alphas + beta * eval_sigma1_at_alphas + gamma) * (eval_w2_tilde_at_alphas + beta * eval_sigma2_at_alphas + gamma) * (eval_w3_tilde_at_alphas + beta * eval_sigma3_at_alphas + gamma) +
    					xi * xi * (v_1_tilde[i] - eval_u_0_tilde_at_alphas * u_1_tilde[i]));
    		combined_mlp_evals.push(elem);	
    	}
    	DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_number_of_gates, combined_mlp_evals)
    }

	pub fn prove(ckt: &HyperPlonkCircuit<E>, w1_tilde: &DenseMultilinearExtension<E::ScalarField>, w2_tilde: &DenseMultilinearExtension<E::ScalarField>, w3_tilde: &DenseMultilinearExtension<E::ScalarField>, srs: &SamaritanMLPCS_SRS<E>) -> Result<HyperPlonkProof<E>, Error> {
		let log_number_of_gates = ckt.log_number_of_gates;
		let number_of_wires = ckt.number_of_wires;
		let number_of_gates = 2usize.pow(log_number_of_gates as u32);
		let seed = [42u8; 32];
		let mut rng = StdRng::from_seed(seed);
		
		let prover_time = start_timer!(|| format!("HyperPlonk::prove with log_number_of_gates {}", log_number_of_gates));
		let mut transcript = Transcript::new(b"HyperPlonk Transcript");

		let w1_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &w1_tilde).unwrap();

		util::append_commitment_to_transcript::<E>(&mut transcript, b"w1_tilde_commit", &w1_tilde_commit);

		let w2_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &w2_tilde).unwrap();

		util::append_commitment_to_transcript::<E>(&mut transcript, b"w2_tilde_commit", &w2_tilde_commit);

		let w3_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &w3_tilde).unwrap();

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

		/* Deep copy or clone is done here, since we keep on squeezing the Boolean hypercube by replaing variables with randomly chosen field element one after another. 
		But we require original multilinear polynomials (e.q., w1_tilde, w2_tilde, w3_tilde, v_0_tilde, v_1_tilde, u_0_tilde, u_1_tilde) later 
		to generate evaluation proofs */

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

		let mut mlp_set = vec![&mut eq_tilde, &mut w1_tilde_copy, &mut w2_tilde_copy, &mut w3_tilde_copy,
			 &mut qM_copy, &mut qL_copy, &mut qR_copy, &mut qO_copy, &mut qC_copy, 
			 &mut sigma_1_copy, &mut sigma_2_copy, &mut sigma_3_copy, 
			 &mut id_1_copy, &mut id_2_copy, &mut id_3_copy,  
			 &mut v_0_tilde_copy, &mut v_1_tilde_copy, &mut u_0_tilde_copy, &mut u_1_tilde_copy];

		let mut coeffs: Vec<_> = Vec::new();
		let mut alphas: Vec<_> = Vec::new();

		for i in 0..log_number_of_gates {
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
		let alpha_final = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_final");
		alphas.push(alpha_final);

		let eval_w1_tilde_at_alphas = w1_tilde.evaluate(&alphas);
		let eval_w2_tilde_at_alphas = w2_tilde.evaluate(&alphas);
		let eval_w3_tilde_at_alphas = w3_tilde.evaluate(&alphas);
		let eval_u_0_tilde_at_alphas = (&u_0_tilde).evaluate(&alphas);
		let eval_sigma1_at_alphas = ckt.sigma_1.evaluate(&alphas);
		let eval_sigma2_at_alphas = ckt.sigma_2.evaluate(&alphas);
		let eval_sigma3_at_alphas = ckt.sigma_3.evaluate(&alphas);
		let eval_id1_at_alphas = ckt.id_1.evaluate(&alphas);
		let eval_id2_at_alphas = ckt.id_2.evaluate(&alphas);
		let eval_id3_at_alphas = ckt.id_3.evaluate(&alphas);

		let combined_mlp = Self::compute_combined_mlp(log_number_of_gates, &ckt.qM, &ckt.qL, &ckt.qR, &ckt.qO, &ckt.qC, &v_0_tilde, &v_1_tilde, &u_1_tilde, eval_w1_tilde_at_alphas, eval_w2_tilde_at_alphas, eval_w3_tilde_at_alphas,
							eval_u_0_tilde_at_alphas, eval_sigma1_at_alphas, eval_sigma2_at_alphas, eval_sigma3_at_alphas, eval_id1_at_alphas, eval_id2_at_alphas, eval_id3_at_alphas, &alphas, beta, gamma, xi, &tau);

		let combined_mlp_eval = combined_mlp.evaluate(&alphas);

		let (combined_mlp_eval_proof, deg_check) = SamaritanMLPCS::<E>::prove(&srs, &combined_mlp, &alphas, combined_mlp_eval, &mut rng).unwrap();
		let deg_check_proof = DegreeCheck::<E>::prove(&srs, &deg_check).unwrap();

		let proof = HyperPlonkProof{
			num_rounds: log_number_of_gates,
			w1_tilde_commit,
			w2_tilde_commit,
			w3_tilde_commit,
			v_0_tilde_commit,
			v_1_tilde_commit,
			u_0_tilde_commit,
			u_1_tilde_commit,
			eval_w1_tilde_at_alphas,
			eval_w2_tilde_at_alphas,
			eval_w3_tilde_at_alphas,
			eval_u_0_tilde_at_alphas,
			eval_sigma1_at_alphas,
			eval_sigma2_at_alphas,
			eval_sigma3_at_alphas,
			eval_id1_at_alphas,
			eval_id2_at_alphas,
			eval_id3_at_alphas,
			combined_mlp_eval_proof,
			coeffs,
			deg_check_proof,
		};
		end_timer!(prover_time);
		Ok(proof)
	}

	pub fn verify(proof: &HyperPlonkProof<E>, ckt: &HyperPlonkCircuit<E>, srs: &SamaritanMLPCS_SRS<E>,
		qM_comm: Commitment<E>, qL_comm: Commitment<E>, qR_comm: Commitment<E>, qO_comm: Commitment<E>, qC_comm:Commitment<E>, 
        	sigma1_comm: Commitment<E>, sigma2_comm: Commitment<E>, sigma3_comm: Commitment<E>, 
        	id1_comm: Commitment<E>, id2_comm: Commitment<E>, id3_comm: Commitment<E>) -> Result<bool, Error> {
		let verifier_time = start_timer!(|| format!("HyperPlonk::verify with multilinear polynomial"));

        let mut transcript = Transcript::new(b"HyperPlonk Transcript");

        let log_number_of_gates = proof.num_rounds;

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
		for i in 0..log_number_of_gates {
			if i > 0 {
				let alpha = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha");
				alphas.push(alpha);
				let mut coeffs = proof.coeffs[i-1].clone();
				coeffs.push(cur_eval_value - coeffs[0]);
				cur_eval_value = Self::compute_evaluation_through_lagrange_interpolation(&d_plus_one_evaluation_points, &coeffs, alpha);
			}
			util::append_field_element_vector_to_transcript::<E>(&mut transcript, b"d_plus_one_evaluations", &proof.coeffs[i]);
		}
		let alpha_final = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_final");
		let mut final_poly_coeffs = proof.coeffs[log_number_of_gates-1].clone();
		final_poly_coeffs.push(cur_eval_value- final_poly_coeffs[0]);
		cur_eval_value = Self::compute_evaluation_through_lagrange_interpolation(&d_plus_one_evaluation_points, &final_poly_coeffs, alpha_final);
		alphas.push(alpha_final);

		let eval_eq_tilde_at_alphas = Self::evaluate_eq_tilde_at_point(log_number_of_gates, &tau, &alphas);
		let comm_list = vec![qM_comm.0, qL_comm.0, qR_comm.0, qO_comm.0, qC_comm.0, proof.v_0_tilde_commit.0, proof.v_1_tilde_commit.0, proof.u_1_tilde_commit.0];
		let scalar_list = vec![eval_eq_tilde_at_alphas * proof.eval_w1_tilde_at_alphas * proof.eval_w2_tilde_at_alphas, eval_eq_tilde_at_alphas * proof.eval_w1_tilde_at_alphas, eval_eq_tilde_at_alphas * proof.eval_w2_tilde_at_alphas, eval_eq_tilde_at_alphas * proof.eval_w3_tilde_at_alphas, eval_eq_tilde_at_alphas,
								eval_eq_tilde_at_alphas * xi * (proof.eval_w1_tilde_at_alphas + beta * proof.eval_sigma1_at_alphas + gamma) * (proof.eval_w2_tilde_at_alphas + beta * proof.eval_sigma2_at_alphas + gamma) * (proof.eval_w3_tilde_at_alphas + beta * proof.eval_sigma3_at_alphas + gamma),
								eval_eq_tilde_at_alphas * xi * xi, -eval_eq_tilde_at_alphas * xi * xi * proof.eval_u_0_tilde_at_alphas];
		let combined_mlp_commit = Commitment(E::G1::msm(&comm_list, &scalar_list).unwrap().into_affine());
		let combined_mlp_eval = cur_eval_value + eval_eq_tilde_at_alphas * xi * (proof.eval_w1_tilde_at_alphas + beta * proof.eval_id1_at_alphas + gamma) * (proof.eval_w2_tilde_at_alphas + beta * proof.eval_id2_at_alphas + gamma) * (proof.eval_w3_tilde_at_alphas + beta * proof.eval_id3_at_alphas + gamma);
		let combined_mlp_check = SamaritanMLPCS::<E>::verify(&srs, &combined_mlp_commit, &alphas, combined_mlp_eval, &proof.combined_mlp_eval_proof).unwrap();
		// assert_eq!(combined_mlp_check, true);

		let deg_check_verify = DegreeCheck::<E>::verify(&srs, &proof.deg_check_proof).unwrap();

        end_timer!(verifier_time);
        Ok(combined_mlp_check == true && deg_check_verify == true)
	}
}

#[cfg(test)]
mod tests {
    #![allow(non_camel_case_types)]
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
    use crate::hyperplonk::*;

    type SamaritanMLPCS_Bls12_381 = SamaritanMLPCS<Bls12_381>;
    type HyperPlonk_Bls12_381 = HyperPlonk<Bls12_381>;
    // type SamaritanMLPCS_Bn254 = SamaritanMLPCS<Bn254>;
    // type HyperPlonk_Bn254 = HyperPlonk<Bn254>;

    #[test]
    fn functionality_test(){
    	let mut rng = &mut test_rng();
    	// n is the dimension of each of the two vectors (A and B) participating in inner product. (2*n) is the number of gates in the circuit. 2^(n+1) is the size of 
    	// evaluation vecs of each mlp. In short #vars = (n + 1).
		let n: usize = 1 << 17;
		let mut rng = &mut test_rng();
		let A: Vec<usize> = (0..n).map(|_| rng.gen_range(1..5)).collect();
		let B: Vec<usize> = (0..n).map(|_| rng.gen_range(1..5)).collect();

		let myckt: HyperPlonkCircuit::<Bls12_381> = HyperPlonk_Bls12_381::generate_circuit_for_inner_product(&A, &B, n);

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
        	id1_comm, id2_comm, id3_comm) = HyperPlonk_Bls12_381::setup(&myckt, &mut rng).unwrap();

		let hyperplonk_proof = HyperPlonk_Bls12_381::prove(&myckt, &w1, &w2, &w3, &srs).unwrap();

    	let valid = HyperPlonk_Bls12_381::verify(&hyperplonk_proof, &myckt, &srs, 
        	qM_comm, qL_comm, qR_comm, qO_comm, qC_comm, 
        	sigma1_comm, sigma2_comm, sigma3_comm, 
        	id1_comm, id2_comm, id3_comm).unwrap();

        assert_eq!(valid, true);
    }

}