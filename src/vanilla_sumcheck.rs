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
use crate::util;
use ark_ec::VariableBaseMSM;
use ark_ec::CurveGroup;
use ark_ff::batch_inversion;

pub struct VanillaSumcheckProof<E: Pairing> {
	num_rounds: usize,
	mlp_a_commit: Commitment<E>,
	mlp_b_commit: Commitment<E>,
	mlp_ab_commit: Commitment<E>,
	eval_mlp_b_at_alphas: E::ScalarField,
	combined_mlp_eval_proof: SamaritanMLPCSEvalProof<E>,
	coeffs: Vec<Vec<E::ScalarField>>,
}

pub struct VanillaSumcheck<E: Pairing> {
	_engine: PhantomData<E>,
}

impl<E: Pairing> VanillaSumcheck<E> {
	pub fn setup<R: RngCore>(rng: &mut R, log_number_of_gates: usize) -> Result<SamaritanMLPCS_SRS<E>, Error> {
		let srs = SamaritanMLPCS::<E>::setup(log_number_of_gates, rng).unwrap();

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

    pub fn prove(srs: &SamaritanMLPCS_SRS<E>, log_number_of_gates: usize, mlp_a: &DenseMultilinearExtension<E::ScalarField>, mlp_b: &DenseMultilinearExtension<E::ScalarField>, mlp_ab: &DenseMultilinearExtension<E::ScalarField>) -> Result<VanillaSumcheckProof<E>, Error> {
    	let log_number_of_gates = log_number_of_gates;
		let number_of_gates = 2usize.pow(log_number_of_gates as u32);
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

		let tau = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"tau", log_number_of_gates);

		let mut eq_tilde = Self::compute_eq_tilde(log_number_of_gates, &tau);

		/* Deep copy or clone is done here, since we keep on squeezing the Boolean hypercube by replaing variables with randomly chosen field element one after another. 
		But we require original multilinear polynomials (e.q., w1_tilde, w2_tilde, w3_tilde, v_0_tilde, v_1_tilde, u_0_tilde, u_1_tilde) later 
		to generate evaluation proofs */

		let mut mlp_a_copy = mlp_a.clone();
		let mut mlp_b_copy = mlp_b.clone();
		let mut mlp_ab_copy = mlp_ab.clone();
		

		let mut mlp_set = vec![&mut eq_tilde, &mut mlp_a_copy, &mut mlp_b_copy, &mut mlp_ab_copy];

		let mut coeffs: Vec<_> = Vec::new();
		let mut alphas: Vec<_> = Vec::new();
		for i in 0..log_number_of_gates {
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
		let alpha_final = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha_final");
		alphas.push(alpha_final);

		let eval_mlp_b_at_alphas = mlp_b.evaluate(&alphas);

		let combined_mlp = Self::compute_combined_mlp(log_number_of_gates, &mlp_ab, &mlp_a, eval_mlp_b_at_alphas, &alphas, &tau);

		let combined_mlp_eval = combined_mlp.evaluate(&alphas);
		let combined_mlp_eval_proof = SamaritanMLPCS::<E>::prove(&srs, &combined_mlp, &alphas, combined_mlp_eval, &mut rng).unwrap();

		let proof = VanillaSumcheckProof{
			num_rounds: log_number_of_gates,
			mlp_a_commit,
			mlp_b_commit,
			mlp_ab_commit,
			eval_mlp_b_at_alphas,
			combined_mlp_eval_proof,
			coeffs,
		};
		// end_timer!(prover_time);
		Ok(proof)
    }

    pub fn verify(proof: &VanillaSumcheckProof<E>, srs: &SamaritanMLPCS_SRS<E>) -> Result<bool, Error> {
		// let verifier_time = start_timer!(|| format!("HyperPlonk::verify with multilinear polynomial"));

        let mut transcript = Transcript::new(b"HyperPlonk Transcript");

        let log_number_of_gates = proof.num_rounds;

        util::append_commitment_to_transcript::<E>(&mut transcript, b"mlp_a_commit", &proof.mlp_a_commit);
        util::append_commitment_to_transcript::<E>(&mut transcript, b"mlp_b_commit", &proof.mlp_b_commit);
        util::append_commitment_to_transcript::<E>(&mut transcript, b"mlp_ab_commit", &proof.mlp_ab_commit);

		let tau = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"tau", log_number_of_gates);
		let mut alphas: Vec<_> = Vec::new();
		let mut cur_eval_value = E::ScalarField::zero();
        let mut d_plus_one_evaluation_points = (1..=3).map(|x| E::ScalarField::from(x as u64)).collect::<Vec<_>>();
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
		final_poly_coeffs.push(cur_eval_value - final_poly_coeffs[0]);
		cur_eval_value = Self::compute_evaluation_through_lagrange_interpolation(&d_plus_one_evaluation_points, &final_poly_coeffs, alpha_final);
		alphas.push(alpha_final);

		let eval_eq_tilde_at_alphas = Self::evaluate_eq_tilde_at_point(log_number_of_gates, &tau, &alphas);
		let comm_list = vec![proof.mlp_ab_commit.0, proof.mlp_a_commit.0];
		let scalar_list = vec![eval_eq_tilde_at_alphas, E::ScalarField::zero()-(eval_eq_tilde_at_alphas * proof.eval_mlp_b_at_alphas)];
		let combined_mlp_commit = Commitment(E::G1::msm(&comm_list, &scalar_list).unwrap().into_affine());
		let combined_mlp_eval = cur_eval_value;
		let combined_mlp_check = SamaritanMLPCS::<E>::verify(&srs, &combined_mlp_commit, &alphas, combined_mlp_eval, &proof.combined_mlp_eval_proof).unwrap();
		assert_eq!(combined_mlp_check, true);

        // end_timer!(verifier_time);
        Ok(combined_mlp_check == true)
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
    use crate::vanilla_sumcheck::*;

    type VanillaSumcheck_Bls12_381 = VanillaSumcheck<Bls12_381>;
    // type SamaritanMLPCS_Bn254 = SamaritanMLPCS<Bn254>;

    #[test]
    fn functionality_test() {
        let mut rng = &mut test_rng();
        let log_number_of_gates = 15;
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

        let srs = VanillaSumcheck_Bls12_381::setup(&mut rng, log_number_of_gates).unwrap();

		let vanilla_sumcheck_proof = VanillaSumcheck_Bls12_381::prove(&srs, log_number_of_gates, &mlp_a, &mlp_b, &mlp_ab).unwrap();

    	let valid = VanillaSumcheck_Bls12_381::verify(&vanilla_sumcheck_proof, &srs).unwrap();

        assert_eq!(valid, true);
    }
}