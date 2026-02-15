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
use crate::generic_improved_sumcheck::*;
use crate::util;

#[derive(Debug)]
pub struct SparseMatrixRepr<E: Pairing> {
	rows: Vec<E::ScalarField>,
	cols: Vec<E::ScalarField>,
	vals: Vec<E::ScalarField>,
}

#[derive(Debug)]
pub struct HybridSpartanCircuit<E: Pairing> {
	number_of_constraints: usize,
	number_of_variables: usize,
	A: SparseMatrixRepr<E>,
	B: SparseMatrixRepr<E>,
	C: SparseMatrixRepr<E>,
}

pub struct HybridSpartanProof<E: Pairing> {
	sumcheck_proof: GenericImprovedSumcheckProof<E>,
	z_tilde_commit: Commitment<E>,
	a_tilde_commit: Commitment<E>,
	b_tilde_commit: Commitment<E>,
	c_tilde_commit: Commitment<E>,
	L_r_tilde_commit: Commitment<E>,
	m_r_tilde_commit: Commitment<E>,
	L_c_tilde_commit: Commitment<E>,
	m_c_tilde_commit: Commitment<E>,
	g_tilde_commit: Commitment<E>,
}

/* mlp_set: vec![ROW_tilde(0), COL_tilde(1), VAL_A_tilde(2), VAL_B_tilde(3), VAL_C_tilde(4), 
        											z_tilde(5), a_tilde(6), b_tilde(7), c_tilde(8), 
        											L_r_tilde(9), m_r_tilde(10), L_c_tilde(11), m_c_tilde(12),
        											eq_tilde_tau(13), id_tilde(14),
        											g_tilde(15), eq_tilde_tau_prime(16)] */

/* The sumcheck equation on left-hand-side (with summation over Boolean hypercube of size num_total_nonzero_entries, 
																additional_field_elements: [alpha, beta],
																rhs: 2 * alpha * log_num_total_nonzero_entries) is the following:
	eq_tilde_tau(x) (a_tilde(x) * b_tilde(x) - c_tilde(x))
		+ L_r_tilde(x) * L_c_tilde(x) * VAL_A_tilde(x) - eq_tilde_tau(x) * a_tilde(x)
		+ L_r_tilde(x) * L_c_tilde(x) * VAL_B_tilde(x) - eq_tilde_tau(x) * b_tilde(x)
		+ L_r_tilde(x) * L_c_tilde(x) * VAL_C_tilde(x) - eq_tilde_tau(x) * c_tilde(x)
		+ g_tilde(x)
		+ eq_tilde_tau_prime(x) * (g_tilde(x) * (alpha + beta * id_tilde(x) + eq_tilde_tau(x)) * (alpha + beta * ROW_tilde(x) + L_r_tilde(x)) * (alpha + beta * id_tilde(x) + z_tilde(x)) * (alpha + beta * COL_tilde(x) + L_c_tilde(x))
									- m_r_tilde(x) * (alpha + beta * ROW_tilde(x) + L_r_tilde(x)) * (alpha + beta * id_tilde(x) + z_tilde(x)) * (alpha + beta * COL_tilde(x) + L_c_tilde(x))
									+ (alpha + beta * id_tilde(x) + eq_tilde_tau(x)) * (alpha + beta * id_tilde(x) + z_tilde(x)) * (alpha + beta * COL_tilde(x) + L_c_tilde(x))
									- gamma * m_c_tilde(x) * (alpha + beta * id_tilde(x) + eq_tilde_tau(x)) * (alpha + beta * ROW_tilde(x) + L_r_tilde(x)) * (alpha + beta * COL_tilde(x) + L_c_tilde(x))
									+ gamma * (alpha + beta * id_tilde(x) + eq_tilde_tau(x)) * (alpha + beta * ROW_tilde(x) + L_r_tilde(x)) * (alpha + beta * id_tilde(x) + z_tilde(x)) */

pub fn myfunc<E: Pairing>(set_of_values: Vec<E::ScalarField>, additional_values: &Vec<E::ScalarField>) -> E::ScalarField {
	set_of_values[13] * (set_of_values[6] * set_of_values[7] - set_of_values[8]) 
		+ set_of_values[9] * set_of_values[2] * set_of_values[11] - set_of_values[13] * set_of_values[6]
		+ set_of_values[9] * set_of_values[3] * set_of_values[11] - set_of_values[13] * set_of_values[7]
		+ set_of_values[9] * set_of_values[4] * set_of_values[11] - set_of_values[13] * set_of_values[8]
		+ set_of_values[15]
		+ set_of_values[16] * (
								set_of_values[15] * (additional_values[0] + additional_values[1] * set_of_values[14] + set_of_values[13]) * (additional_values[0] + additional_values[1] * set_of_values[0] + set_of_values[9]) * (additional_values[0] + additional_values[1] * set_of_values[14] + set_of_values[5]) * (additional_values[0] + additional_values[1] * set_of_values[1] + set_of_values[11])
								- set_of_values[10] * (additional_values[0] + additional_values[1] * set_of_values[0] + set_of_values[9]) * (additional_values[0] + additional_values[1] * set_of_values[14] + set_of_values[5]) * (additional_values[0] + additional_values[1] * set_of_values[1] + set_of_values[11])
								+ (additional_values[0] + additional_values[1] * set_of_values[14] + set_of_values[13]) * (additional_values[0] + additional_values[1] * set_of_values[14] + set_of_values[5]) * (additional_values[0] + additional_values[1] * set_of_values[1] + set_of_values[11])
								- additional_values[2] * set_of_values[12] * (additional_values[0] + additional_values[1] * set_of_values[14] + set_of_values[13]) * (additional_values[0] + additional_values[1] * set_of_values[0] + set_of_values[9]) * (additional_values[0] + additional_values[1] * set_of_values[1] + set_of_values[11])
								+ additional_values[2] * (additional_values[0] + additional_values[1] * set_of_values[14] + set_of_values[13]) * (additional_values[0] + additional_values[1] * set_of_values[0] + set_of_values[9]) * (additional_values[0] + additional_values[1] * set_of_values[14] + set_of_values[5]))
		

}

pub fn myfunc_poly<E: Pairing>(set_of_polys: &Vec<DensePolynomial<E::ScalarField>>, additional_values: &Vec<E::ScalarField>) -> DensePolynomial<E::ScalarField> {
	&set_of_polys[13] * (&set_of_polys[6] * &set_of_polys[7] - &set_of_polys[8]) 
		+ &set_of_polys[9] * &set_of_polys[2] * &set_of_polys[11] - &set_of_polys[13] * &set_of_polys[6]
		+ &set_of_polys[9] * &set_of_polys[3] * &set_of_polys[11] - &set_of_polys[13] * &set_of_polys[7]
		+ &set_of_polys[9] * &set_of_polys[4] * &set_of_polys[11] - &set_of_polys[13] * &set_of_polys[8]
		+ &set_of_polys[15]
		+ &set_of_polys[16] * (
								&set_of_polys[15] * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[14] * additional_values[1] + &set_of_polys[13]) * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[0] * additional_values[1] + &set_of_polys[9]) * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[14] * additional_values[1] + &set_of_polys[5]) * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[1] * additional_values[1] + &set_of_polys[11])
								- &set_of_polys[10] * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[0] * additional_values[1] + &set_of_polys[9]) * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[14] * additional_values[1] + &set_of_polys[5]) * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[1] * additional_values[1] + &set_of_polys[11])
								+ (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[14] * additional_values[1] + &set_of_polys[13]) * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[14] * additional_values[1] + &set_of_polys[5]) * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[1] * additional_values[1] + &set_of_polys[11])
								- (&set_of_polys[12] * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[14] * additional_values[1] + &set_of_polys[13]) * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[0] * additional_values[1] + &set_of_polys[9]) * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[1] * additional_values[1] + &set_of_polys[11])) * additional_values[2]
								+ ((DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[14] * additional_values[1] + &set_of_polys[13]) * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[0] * additional_values[1] + &set_of_polys[9]) * (DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![additional_values[0]]) + &set_of_polys[14] * additional_values[1] + &set_of_polys[5])) * additional_values[2])
		
}

pub fn myfunc_linear_combined_poly<E: Pairing>(set_of_polys: &Vec<DensePolynomial<E::ScalarField>>, set_of_evals: &Vec<Option<E::ScalarField>>, additional_values: &Vec<E::ScalarField>) -> DensePolynomial<E::ScalarField> {
	&set_of_polys[2] * set_of_evals[9].unwrap() * set_of_evals[11].unwrap()
	+ &set_of_polys[3] * set_of_evals[9].unwrap() * set_of_evals[11].unwrap()
	+ &set_of_polys[4] * set_of_evals[9].unwrap() * set_of_evals[11].unwrap()
	- &set_of_polys[6] * set_of_evals[13].unwrap()
	+ &set_of_polys[7] * set_of_evals[13].unwrap() * (set_of_evals[6].unwrap() - E::ScalarField::one())
	- &set_of_polys[8] * E::ScalarField::from(2 as u64) * set_of_evals[13].unwrap()
	- &set_of_polys[10] * set_of_evals[16].unwrap() * (additional_values[0] + additional_values[1] * set_of_evals[0].unwrap() + set_of_evals[9].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[14].unwrap() + set_of_evals[5].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[1].unwrap() + set_of_evals[11].unwrap())
	- &set_of_polys[12] * additional_values[2] * set_of_evals[16].unwrap() * (additional_values[0] + additional_values[1] * set_of_evals[14].unwrap() + set_of_evals[13].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[0].unwrap() + set_of_evals[9].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[1].unwrap() + set_of_evals[11].unwrap())
	+ &set_of_polys[15] * (E::ScalarField::one() + set_of_evals[16].unwrap() * (additional_values[0] + additional_values[1] * set_of_evals[14].unwrap() + set_of_evals[13].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[0].unwrap() + set_of_evals[9].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[14].unwrap() + set_of_evals[5].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[1].unwrap() + set_of_evals[11].unwrap()))
	+ &set_of_polys[16] * (additional_values[0] + additional_values[1] * set_of_evals[14].unwrap() + set_of_evals[13].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[14].unwrap() + set_of_evals[5].unwrap()) * ((additional_values[0] + additional_values[1] * set_of_evals[1].unwrap() + set_of_evals[11].unwrap()) + additional_values[2] * (additional_values[0] + additional_values[1] * set_of_evals[0].unwrap() + set_of_evals[9].unwrap()))
}

// pub fn myfunc_combined_commit<E: Pairing>(set_of_commits: Vec<Option<Commitment<E>>>, set_of_evals: Vec<Option<E::ScalarField>>, additional_values: &Vec<E::ScalarField>) -> Commitment<E> {
// 	let commit_list = vec![
// 						set_of_commits[2].0,
// 						set_of_commits[3].0,
// 						set_of_commits[4].0,
// 						set_of_commits[6].0,
// 						set_of_commits[7].0,
// 						set_of_commits[8].0,
// 						set_of_commits[10].0,
// 						set_of_commits[12].0,
// 						set_of_commits[15].0,
// 						set_of_commits[16].0,
// 					];
// 	let scalar_list = vec![
// 						set_of_evals[9].unwrap() * set_of_evals[11].unwrap(),
// 						set_of_evals[9].unwrap() * set_of_evals[11].unwrap(),
// 						set_of_evals[9].unwrap() * set_of_evals[11].unwrap(),
// 						- set_of_evals[13].unwrap(),
// 						set_of_evals[13].unwrap() * (set_of_evals[6].unwrap() - E::ScalarField::one()),
// 						- E::ScalarField::from(2 as u64) * set_of_evals[13].unwrap(),
// 						- set_of_evals[16].unwrap() * (additional_values[0] + additional_values[1] * set_of_evals[0].unwrap() + set_of_evals[9].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[14].unwrap() + set_of_evals[5].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[1].unwrap() + set_of_evals[11].unwrap()),
// 						- additional_values[2] * set_of_evals[16].unwrap() * (additional_values[0] + additional_values[1] * set_of_evals[14].unwrap() + set_of_evals[13].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[0].unwrap() + set_of_evals[9].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[1].unwrap() + set_of_evals[11].unwrap()),
// 						(E::ScalarField::one() + set_of_evals[16].unwrap() * (additional_values[0] + additional_values[1] * set_of_evals[14].unwrap() + set_of_evals[13].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[0].unwrap() + set_of_evals[9].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[14].unwrap() + set_of_evals[5].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[1].unwrap() + set_of_evals[11].unwrap())),
// 						(additional_values[0] + additional_values[1] * set_of_evals[14].unwrap() + set_of_evals[13].unwrap()) * (additional_values[0] + additional_values[1] * set_of_evals[14].unwrap() + set_of_evals[5].unwrap()) * ((additional_values[0] + additional_values[1] * set_of_evals[1].unwrap() + set_of_evals[11].unwrap()) + additional_values[2] * (additional_values[0] + additional_values[1] * set_of_evals[0].unwrap() + set_of_evals[9].unwrap()))
// 					];
// 	Commitment(E::G1::msm(&commit_list, &scalar_list).unwrap().into_affine())
// }

pub struct HybridSpartan<E: Pairing> {
	_engine: PhantomData<E>,
}

impl<E: Pairing> HybridSpartan<E> {
	/* This function generates a random inner product circuit for two vectors A and B of dimension n. The circuit description is hybridspartan-friendly. */  
	pub fn generate_circuit_for_inner_product(A: &Vec<E::ScalarField>, B: &Vec<E::ScalarField>, k: E::ScalarField, n: usize) -> HybridSpartanCircuit<E> {
		let repr_A: SparseMatrixRepr<E> = SparseMatrixRepr {
											rows: (0..n).map(|i| E::ScalarField::from(i as u64)).collect(),
											cols: (1..=n).map(|i| E::ScalarField::from(i as u64)).collect(),
											vals: vec![E::ScalarField::one(); n],
										};

		// assert_eq!(repr_A.rows.len(), repr_A.cols.len());
		// assert_eq!(repr_A.cols.len(), repr_A.vals.len());

		let repr_B: SparseMatrixRepr<E> = SparseMatrixRepr {
											rows: (0..n).map(|i| E::ScalarField::from(i as u64)).collect(),
											cols: (n+1..=2*n).map(|i| E::ScalarField::from(i as u64)).collect(),
											vals: vec![E::ScalarField::one(); n],
										};

		// assert_eq!(repr_B.rows.len(), repr_B.cols.len());
		// assert_eq!(repr_B.cols.len(), repr_B.vals.len());

		let repr_C: SparseMatrixRepr<E> = SparseMatrixRepr {
											rows: vec![(0..n-1).map(|i| E::ScalarField::from(i as u64)).collect(), vec![E::ScalarField::from(n as u64) - E::ScalarField::one(); n]].concat(),
											cols: vec![(2*n+1..3*n).map(|i| E::ScalarField::from(i as u64)).collect(), vec![E::ScalarField::zero()], (2*n+1..3*n).map(|i| E::ScalarField::from(i as u64)).collect()].concat(),
											vals: vec![vec![E::ScalarField::one(); n-1], vec![k], vec![-E::ScalarField::one(); n-1]].concat(),
										};

		// assert_eq!(repr_C.rows.len(), repr_C.cols.len());
		// assert_eq!(repr_C.cols.len(), repr_C.vals.len());

		let myckt = HybridSpartanCircuit {
			number_of_constraints: n,
			number_of_variables: 3 * n,
			A: repr_A,
			B: repr_B,
			C: repr_C,
		};

		myckt
	}

	pub fn preprocessing<R: RngCore>(ckt: &HybridSpartanCircuit<E>, rng: &mut R) -> Result<(SamaritanMLPCS_SRS<E>,
																	DenseMultilinearExtension<E::ScalarField>, DenseMultilinearExtension<E::ScalarField>, DenseMultilinearExtension<E::ScalarField>, DenseMultilinearExtension<E::ScalarField>, DenseMultilinearExtension<E::ScalarField>, DenseMultilinearExtension<E::ScalarField>, 
																	Commitment<E>, Commitment<E>, Commitment<E>, Commitment<E>, Commitment<E>, Commitment<E>), Error> {
		//======================================================================================================================
		// N = nA + nB + nC

		let actual_num_total_nonzero_entries: usize = ckt.A.rows.len() + ckt.B.rows.len() + ckt.C.rows.len();
		let log_num_total_nonzero_entries: usize = (actual_num_total_nonzero_entries as f64).log2().ceil() as usize;
		let num_total_nonzero_entries = 1 << log_num_total_nonzero_entries;

		let srs = SamaritanMLPCS::<E>::setup(log_num_total_nonzero_entries, rng).unwrap();

		//======================================================================================================================
		// compute ROW, COL, VAL_A, VAL_B, VAL_C, these are publicly known

		let mut ROW = vec![E::ScalarField::zero(); num_total_nonzero_entries];
		let mut COL = vec![E::ScalarField::zero(); num_total_nonzero_entries];
		let mut VAL_A = vec![E::ScalarField::zero(); num_total_nonzero_entries];
		let mut VAL_B = vec![E::ScalarField::zero(); num_total_nonzero_entries];
		let mut VAL_C = vec![E::ScalarField::zero(); num_total_nonzero_entries];

		for i in 0..ckt.A.rows.len() {
			ROW[i] = ckt.A.rows[i];
			COL[i] = ckt.A.cols[i];
			VAL_A[i] = ckt.A.vals[i];
		}

		for i in 0..ckt.B.rows.len() {
			ROW[i + ckt.A.rows.len()] = ckt.B.rows[i];
			COL[i + ckt.A.rows.len()] = ckt.B.cols[i];
			VAL_B[i + ckt.A.rows.len()] = ckt.B.vals[i];
		}

		for i in 0..ckt.C.rows.len() {
			ROW[i + ckt.A.rows.len() + ckt.B.rows.len()] = ckt.C.rows[i];
			COL[i + ckt.A.rows.len() + ckt.B.rows.len()] = ckt.C.cols[i];
			VAL_C[i + ckt.A.rows.len() + ckt.B.rows.len()] = ckt.C.vals[i];
		}

		let ROW_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, ROW.clone());
		let COL_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, COL.clone());
		let VAL_A_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, VAL_A);
		let VAL_B_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, VAL_B);
		let VAL_C_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, VAL_C);

		let ROW_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &ROW_tilde).unwrap();
		let COL_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &COL_tilde).unwrap();
		let VAL_A_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &VAL_A_tilde).unwrap();
		let VAL_B_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &VAL_B_tilde).unwrap();
		let VAL_C_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &VAL_C_tilde).unwrap();

		//======================================================================================================================
		// compute id_tilde

		let id = (1..=num_total_nonzero_entries).map(|i| E::ScalarField::from(i as u64)).collect();
		let id_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, id);
		let id_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &id_tilde).unwrap();

		Ok((srs, 
		ROW_tilde, COL_tilde, VAL_A_tilde, VAL_B_tilde, VAL_C_tilde, id_tilde,
		ROW_tilde_commit, COL_tilde_commit, VAL_A_tilde_commit, VAL_B_tilde_commit, VAL_C_tilde_commit, id_tilde_commit))

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

	pub fn prove(ckt: &HybridSpartanCircuit<E>, srs: &SamaritanMLPCS_SRS<E>, z: &Vec<E::ScalarField>,
			ROW_tilde: &DenseMultilinearExtension<E::ScalarField>, COL_tilde: &DenseMultilinearExtension<E::ScalarField>, 
			VAL_A_tilde: &DenseMultilinearExtension<E::ScalarField>, VAL_B_tilde: &DenseMultilinearExtension<E::ScalarField>, VAL_C_tilde: &DenseMultilinearExtension<E::ScalarField>, id_tilde: &DenseMultilinearExtension<E::ScalarField>,
			ROW_tilde_commit: &Commitment<E>, COL_tilde_commit: &Commitment<E>, VAL_A_tilde_commit: &Commitment<E>, VAL_B_tilde_commit: &Commitment<E>, VAL_C_tilde_commit: &Commitment<E>, id_tilde_commit: &Commitment<E>) -> Result<HybridSpartanProof<E>, Error> {

		//======================================================================================================================
		// N = nA + nB + nC

		let actual_num_total_nonzero_entries: usize = ckt.A.rows.len() + ckt.B.rows.len() + ckt.C.rows.len();
		let log_num_total_nonzero_entries: usize = (actual_num_total_nonzero_entries as f64).log2().ceil() as usize;
		let num_total_nonzero_entries = 1 << log_num_total_nonzero_entries;

		let prover_time = start_timer!(|| format!("HybridSpartan::prove with log_num_total_nonzero_entries {}", log_num_total_nonzero_entries));
		let mut transcript = Transcript::new(b"HybridSpartan Transcript");

		let seed = [42u8; 32];
		let mut rng = StdRng::from_seed(seed);

		//======================================================================================================================
		// compute z_tilde

		let z_tilde_evals = [z.clone(), vec![E::ScalarField::zero(); ((num_total_nonzero_entries as i32) - (z.len() as i32)) as usize]].concat();
		let z_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, z_tilde_evals.clone());
		let z_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &z_tilde).unwrap();
		util::append_commitment_to_transcript::<E>(&mut transcript, b"z_tilde_commit", &z_tilde_commit);
		//======================================================================================================================

		// check if number_of_constraints <= num_total_nonzero_entries and number_of_variables < num_total_nonzero_entries
		// assert!(ckt.number_of_constraints <= num_total_nonzero_entries);
		// assert!(ckt.number_of_variables <= num_total_nonzero_entries);

		//======================================================================================================================
		// compute a_tilde, b_tilde, c_tilde

		let mut a: Vec<E::ScalarField> = vec![E::ScalarField::zero(); num_total_nonzero_entries];
		let mut b: Vec<E::ScalarField> = vec![E::ScalarField::zero(); num_total_nonzero_entries];
		let mut c: Vec<E::ScalarField> = vec![E::ScalarField::zero(); num_total_nonzero_entries];
		for i in 0..ckt.A.rows.len() {
			let row: usize = util::fe_to_index::<E>(ckt.A.rows[i]);
			let col: usize = util::fe_to_index::<E>(ckt.A.cols[i]);
			a[row] = a[row] + ckt.A.vals[i] * z[col];
		}
		for i in 0..ckt.B.rows.len() {
			let row: usize = util::fe_to_index::<E>(ckt.B.rows[i]);
			let col: usize = util::fe_to_index::<E>(ckt.B.cols[i]);
			b[row] = b[row] + ckt.B.vals[i] * z[col];
		}
		for i in 0..ckt.C.rows.len() {
			let row: usize = util::fe_to_index::<E>(ckt.C.rows[i]);
			let col: usize = util::fe_to_index::<E>(ckt.C.cols[i]);
			c[row] = c[row] + ckt.C.vals[i] * z[col];
		}
		let a_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, a);
		let b_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, b);
		let c_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, c);

		let a_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &a_tilde).unwrap();
		util::append_commitment_to_transcript::<E>(&mut transcript, b"a_tilde_commit", &a_tilde_commit);
		let b_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &b_tilde).unwrap();
		util::append_commitment_to_transcript::<E>(&mut transcript, b"b_tilde_commit", &b_tilde_commit);
		let c_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &c_tilde).unwrap();
		util::append_commitment_to_transcript::<E>(&mut transcript, b"c_tilde_commit", &c_tilde_commit);

		//======================================================================================================================
		// sample tau (by verifier) and compute eq_tilde_tau, L_r_tilde and m_r_tilde.

		let tau = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"tau", log_num_total_nonzero_entries);
		let eq_tilde_tau = Self::compute_eq_tilde(log_num_total_nonzero_entries, &tau);
		// let eq_tilde_tau_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &eq_tilde_tau).unwrap();
		// util::append_commitment_to_transcript::<E>(&mut transcript, b"eq_tilde_tau_commit", &eq_tilde_tau_commit);

		let ROW = ROW_tilde.to_evaluations();
		let mut L_r: Vec<E::ScalarField> = Vec::new();
		let mut m_r = vec![E::ScalarField::zero(); num_total_nonzero_entries];
		for i in 0..num_total_nonzero_entries {
			let row: usize = util::fe_to_index::<E>(ROW[i]);;
			L_r.push(eq_tilde_tau[row]);
			m_r[row] += E::ScalarField::one();
		}

		let L_r_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, L_r.clone());
		let m_r_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, m_r.clone());

		let L_r_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &L_r_tilde).unwrap();
		let m_r_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &m_r_tilde).unwrap();

		util::append_commitment_to_transcript::<E>(&mut transcript, b"L_r_tilde_commit", &L_r_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"m_r_tilde_commit", &m_r_tilde_commit);

		//======================================================================================================================
		// compute L_c and m_c.

		let COL = COL_tilde.to_evaluations();
		let mut L_c: Vec<E::ScalarField> = Vec::new();
		let mut m_c = vec![E::ScalarField::zero(); num_total_nonzero_entries];
		for i in 0..num_total_nonzero_entries {
			let col: usize = util::fe_to_index::<E>(COL[i]);
			L_c.push(z[col]);
			m_c[col] += E::ScalarField::one();
		}

		let L_c_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, L_c.clone());
		let m_c_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, m_c.clone());

		let L_c_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &L_c_tilde).unwrap();
		let m_c_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &m_c_tilde).unwrap();

		util::append_commitment_to_transcript::<E>(&mut transcript, b"L_c_tilde_commit", &L_c_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"m_c_tilde_commit", &m_c_tilde_commit);

		//======================================================================================================================
		// random sample field elements alpha, beta, gamma that are required in sumcheck relation. compute and commit to g_tilde

		let alpha = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha");
		let beta = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"beta");
		let gamma = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"gamma");

		//======================================================================================================================
		// compute g_tilde

		let mut xi_1_denom_first = vec![E::ScalarField::one(); num_total_nonzero_entries];
		let mut xi_1_denom_second = vec![E::ScalarField::one(); num_total_nonzero_entries];
		let mut xi_2_denom_first = vec![E::ScalarField::one(); num_total_nonzero_entries];
		let mut xi_2_denom_second = vec![E::ScalarField::one(); num_total_nonzero_entries];

		let eq_tilde_evals = eq_tilde_tau.to_evaluations();
		let id_tilde_evals = id_tilde.to_evaluations();
		for i in 0..num_total_nonzero_entries {
			xi_1_denom_first[i] = alpha + beta * id_tilde_evals[i] + eq_tilde_evals[i];
			xi_1_denom_second[i] = alpha + beta * ROW[i] + L_r[i];
			xi_2_denom_first[i] = alpha + beta * id_tilde_evals[i] + z_tilde_evals[i];
			xi_2_denom_second[i] = alpha + beta * COL[i] + L_c[i];
		}
		let mut xi_1_denom_first_inverses = xi_1_denom_first.clone();
		batch_inversion(&mut xi_1_denom_first_inverses);
		let mut xi_1_denom_second_inverses = xi_1_denom_second.clone();
		batch_inversion(&mut xi_1_denom_second_inverses);
		let mut xi_2_denom_first_inverses = xi_2_denom_first.clone();
		batch_inversion(&mut xi_2_denom_first_inverses);
		let mut xi_2_denom_second_inverses = xi_2_denom_second.clone();
		batch_inversion(&mut xi_2_denom_second_inverses);

		let mut xi_1 = vec![E::ScalarField::one(); num_total_nonzero_entries];
		let mut xi_2 = vec![E::ScalarField::one(); num_total_nonzero_entries];
		for i in 0..num_total_nonzero_entries {
			xi_1[i] = m_r[i] * xi_1_denom_first_inverses[i] - xi_1_denom_second_inverses[i];
			xi_2[i] = m_c[i] * xi_2_denom_first_inverses[i] - xi_2_denom_second_inverses[i];
		}

		let mut g = vec![E::ScalarField::one(); num_total_nonzero_entries];
		for i in 0..num_total_nonzero_entries {
			g[i] = xi_1[i] + gamma * xi_2[i];
		}
		let g_tilde = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(log_num_total_nonzero_entries, g.clone());
		let g_tilde_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &g_tilde).unwrap();
		util::append_commitment_to_transcript::<E>(&mut transcript, b"g_tilde_commit", &g_tilde_commit);

		//======================================================================================================================
		// sample tau_prime. compute eq_tilde_tau_prime

		let tau_prime = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"tau_prime", log_num_total_nonzero_entries);
		let eq_tilde_tau_prime = Self::compute_eq_tilde(log_num_total_nonzero_entries, &tau_prime);
		// let eq_tilde_tau_ime_commit = SamaritanMLPCS::<E>::commit_G1(&srs, &eq_tilde_tau_prime).unwrap();

		//======================================================================================================================
		// compile the list of commitments
		
		let commit_list: Vec<Option<Commitment<E>>> = vec![Some(ROW_tilde_commit.clone()), Some(COL_tilde_commit.clone()), Some(VAL_A_tilde_commit.clone()), Some(VAL_B_tilde_commit.clone()), Some(VAL_C_tilde_commit.clone()), 
								Some(z_tilde_commit), Some(a_tilde_commit), Some(b_tilde_commit), Some(c_tilde_commit), 
								Some(L_r_tilde_commit), Some(m_r_tilde_commit), Some(L_c_tilde_commit), Some(m_c_tilde_commit),
								None, Some(id_tilde_commit.clone()),
								Some(g_tilde_commit), None];

		let eq_tilde_eval_info_tau = eq_tilde_eval_info {
										index: 13,
										tau: tau,
									};
		let eq_tilde_eval_info_tau_prime = eq_tilde_eval_info {
										index: 16,
										tau: tau_prime,
									};

		//======================================================================================================================
		// setup combined sumcheck relation

		let sumcheck_relation: SumcheckRelation<E> = SumcheckRelation {
        							log_number_of_vars: log_num_total_nonzero_entries,
        							max_degree: 6,
        							mlp_set: vec![ROW_tilde.clone(), COL_tilde.clone(), VAL_A_tilde.clone(), VAL_B_tilde.clone(), VAL_C_tilde.clone(), 
        											z_tilde, a_tilde, b_tilde, c_tilde, 
        											L_r_tilde, m_r_tilde, L_c_tilde, m_c_tilde,
        											eq_tilde_tau, id_tilde.clone(),
        											g_tilde, eq_tilde_tau_prime],
        							commit_list: commit_list,
        							eq_tilde_eval_infos: vec![eq_tilde_eval_info_tau, eq_tilde_eval_info_tau_prime],
        							rhs: E::ScalarField::zero(),
        							additional_field_elements: vec![alpha, beta, gamma],
        							G_tilde_description: myfunc::<E>,
        							G_tilde_description_poly: myfunc_poly::<E>,
        							G_bar_linear_combine: myfunc_linear_combined_poly::<E>,
        							// G_tilde_combined_commit: myfunc_combined_commit::<E>,
        						};
        
        //======================================================================================================================
		// call sumcheck prover

		let sumcheck_proof = GenericImprovedSumcheck::<E>::prove(&srs, &sumcheck_relation).unwrap();

		let proof = HybridSpartanProof {
			sumcheck_proof,
			z_tilde_commit,
			a_tilde_commit,
			b_tilde_commit,
			c_tilde_commit,
			L_r_tilde_commit,
			m_r_tilde_commit,
			L_c_tilde_commit,
			m_c_tilde_commit,
			g_tilde_commit,
		};

		end_timer!(prover_time);
		Ok(proof)

	}

	pub fn verify(proof: &HybridSpartanProof<E>, ckt: &HybridSpartanCircuit<E>, srs: &SamaritanMLPCS_SRS<E>,
					ROW_tilde: &DenseMultilinearExtension<E::ScalarField>, COL_tilde: &DenseMultilinearExtension<E::ScalarField>, 
					VAL_A_tilde: &DenseMultilinearExtension<E::ScalarField>, VAL_B_tilde: &DenseMultilinearExtension<E::ScalarField>, VAL_C_tilde: &DenseMultilinearExtension<E::ScalarField>, id_tilde: &DenseMultilinearExtension<E::ScalarField>,
					ROW_tilde_commit: &Commitment<E>, COL_tilde_commit: &Commitment<E>, VAL_A_tilde_commit: &Commitment<E>, VAL_B_tilde_commit: &Commitment<E>, VAL_C_tilde_commit: &Commitment<E>, id_tilde_commit: &Commitment<E>) -> Result<bool, Error> {
		
		let verifier_time = start_timer!(|| format!("HybridSpartan::verify"));
		let mut transcript = Transcript::new(b"HybridSpartan Transcript");

		let actual_num_total_nonzero_entries: usize = ckt.A.rows.len() + ckt.B.rows.len() + ckt.C.rows.len();
		let log_num_total_nonzero_entries: usize = (actual_num_total_nonzero_entries as f64).log2().ceil() as usize;
		let num_total_nonzero_entries = 1 << log_num_total_nonzero_entries;

		util::append_commitment_to_transcript::<E>(&mut transcript, b"z_tilde_commit", &proof.z_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"a_tilde_commit", &proof.a_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"b_tilde_commit", &proof.b_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"c_tilde_commit", &proof.c_tilde_commit);

		let tau = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"tau", log_num_total_nonzero_entries);

		util::append_commitment_to_transcript::<E>(&mut transcript, b"L_r_tilde_commit", &proof.L_r_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"m_r_tilde_commit", &proof.m_r_tilde_commit);

		util::append_commitment_to_transcript::<E>(&mut transcript, b"L_c_tilde_commit", &proof.L_c_tilde_commit);
		util::append_commitment_to_transcript::<E>(&mut transcript, b"m_c_tilde_commit", &proof.m_c_tilde_commit);

		let alpha = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha");
		let beta = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"beta");
		let gamma = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"gamma");

		util::append_commitment_to_transcript::<E>(&mut transcript, b"g_tilde_commit", &proof.g_tilde_commit);

		let tau_prime = util::sample_random_challenge_vector_from_transcript::<E>(&mut transcript, b"tau_prime", log_num_total_nonzero_entries);

		let commit_list: Vec<Option<Commitment<E>>> = vec![Some(ROW_tilde_commit.clone()), Some(COL_tilde_commit.clone()), Some(VAL_A_tilde_commit.clone()), Some(VAL_B_tilde_commit.clone()), Some(VAL_C_tilde_commit.clone()), 
								Some(proof.z_tilde_commit), Some(proof.a_tilde_commit), Some(proof.b_tilde_commit), Some(proof.c_tilde_commit), 
								Some(proof.L_r_tilde_commit), Some(proof.m_r_tilde_commit), Some(proof.L_c_tilde_commit), Some(proof.m_c_tilde_commit),
								None, Some(id_tilde_commit.clone()),
								Some(proof.g_tilde_commit), None];

		let valid = GenericImprovedSumcheck::<E>::verify(&proof.sumcheck_proof, commit_list, &srs).unwrap();
		end_timer!(verifier_time);

		Ok(valid)
	}
	
}

#[cfg(test)]
mod tests {
    #![allow(non_camel_case_types)]
    use ark_poly_commit::kzg10::*;
    use ark_poly_commit::*;
    use ark_ec::pairing::Pairing;
    // use ark_bls12_381::Bls12_381;
    // use ark_bls12_381::Fr;
    use ark_bn254::Bn254;
    use ark_bn254::Fr;
    use ark_std::test_rng;
    use ark_std::{rand::Rng, vec::Vec};
    use ark_std::{start_timer, end_timer, Zero, One};
    
    use crate::samaritan_mlpcs::*;
    use crate::generic_improved_sumcheck::*;
    use crate::hybridspartan::*;

    // type GenericImprovedSumcheck_Bls12_381 = GenericImprovedSumcheck<Bls12_381>;
    // type HybridSpartan_Bls12_381 = HybridSpartan<Bls12_381>;
    type GenericImprovedSumcheck_Bn254 = GenericImprovedSumcheck<Bn254>;
    type HybridSpartan_Bn254 = HybridSpartan<Bn254>;

    #[test]
    fn functionality_test(){
    	let mut rng = &mut test_rng();
        // n is the dimension of each of the two vectors (A and B) participating in inner product.
    	let n: usize = 1 << 16;
    	let A: Vec<Fr> = (0..n).map(|_| Fr::from(rng.gen_range(1..5))).collect();
    	let B: Vec<Fr> = (0..n).map(|_| Fr::from(rng.gen_range(1..5))).collect();

    	let mut z: Vec<_> = Vec::new();
    	z.push(Fr::one());
    	for i in 0..n {
    		z.push(A[i]);
    	}
    	for i in 0..n {
    		z.push(B[i]);
    	}
    	for i in 0..(n - 1) {
    		z.push(A[i] * B[i]);
    	}

    	let mut k = Fr::zero();
    	for i in 0..n {
    		k += A[i] * B[i];
    	}

    	// println!("A: {:?}", A);
    	// println!("B: {:?}", B);
    	// println!("k: {}", k);



    	//====================================================

    	// let myckt: HybridSpartanCircuit::<Bls12_381> = HybridSpartan_Bls12_381::generate_circuit_for_inner_product(&A, &B, k, n);

    	// let (srs, 
		// ROW_tilde, COL_tilde, VAL_A_tilde, VAL_B_tilde, VAL_C_tilde, id_tilde,
		// ROW_tilde_commit, COL_tilde_commit, VAL_A_tilde_commit, VAL_B_tilde_commit, VAL_C_tilde_commit, id_tilde_commit) = HybridSpartan_Bls12_381::preprocessing(&myckt, &mut rng).unwrap();

    	// let hybridspartan_proof = HybridSpartan_Bls12_381::prove(&myckt, &srs, &z, 
    	// 													&ROW_tilde, &COL_tilde, &VAL_A_tilde, &VAL_B_tilde, &VAL_C_tilde, &id_tilde,
    	// 													&ROW_tilde_commit, &COL_tilde_commit, &VAL_A_tilde_commit, &VAL_B_tilde_commit, &VAL_C_tilde_commit, &id_tilde_commit).unwrap();

        // let valid = HybridSpartan_Bls12_381::verify(&hybridspartan_proof, &myckt, &srs,
        // 												&ROW_tilde, &COL_tilde, &VAL_A_tilde, &VAL_B_tilde, &VAL_C_tilde, &id_tilde,
        // 												&ROW_tilde_commit, &COL_tilde_commit, &VAL_A_tilde_commit, &VAL_B_tilde_commit, &VAL_C_tilde_commit, &id_tilde_commit).unwrap();

        // assert_eq!(valid, true);

        //=====================================================


        let myckt: HybridSpartanCircuit::<Bn254> = HybridSpartan_Bn254::generate_circuit_for_inner_product(&A, &B, k, n);

    	let (srs, 
		ROW_tilde, COL_tilde, VAL_A_tilde, VAL_B_tilde, VAL_C_tilde, id_tilde,
		ROW_tilde_commit, COL_tilde_commit, VAL_A_tilde_commit, VAL_B_tilde_commit, VAL_C_tilde_commit, id_tilde_commit) = HybridSpartan_Bn254::preprocessing(&myckt, &mut rng).unwrap();

    	let hybridspartan_proof = HybridSpartan_Bn254::prove(&myckt, &srs, &z, 
    														&ROW_tilde, &COL_tilde, &VAL_A_tilde, &VAL_B_tilde, &VAL_C_tilde, &id_tilde,
    														&ROW_tilde_commit, &COL_tilde_commit, &VAL_A_tilde_commit, &VAL_B_tilde_commit, &VAL_C_tilde_commit, &id_tilde_commit).unwrap();

        let valid = HybridSpartan_Bn254::verify(&hybridspartan_proof, &myckt, &srs,
        												&ROW_tilde, &COL_tilde, &VAL_A_tilde, &VAL_B_tilde, &VAL_C_tilde, &id_tilde,
        												&ROW_tilde_commit, &COL_tilde_commit, &VAL_A_tilde_commit, &VAL_B_tilde_commit, &VAL_C_tilde_commit, &id_tilde_commit).unwrap();

        assert_eq!(valid, true);
    }
}