use ark_poly_commit::kzg10::*;
use ark_poly_commit::error::Error;
use ark_poly::polynomial::Polynomial;
use ark_poly::DenseUVPolynomial;
use ark_poly::evaluations::multivariate::multilinear::MultilinearExtension;
use ark_poly::univariate::DensePolynomial;
use ark_poly::univariate::SparsePolynomial;
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension;
use ark_ec::pairing::Pairing;
use ark_ff::fields::Field;
use ark_std::{start_timer, end_timer, Zero, One, marker::PhantomData, ops::Div, ops::Mul, ops::Sub};
use ark_std::{UniformRand};
use ark_std::rand::{SeedableRng, RngCore};
use ark_std::rand::rngs::StdRng;
use ark_ff::PrimeField;
use merlin::Transcript;
use ark_ff::BigInteger;
use ark_serialize::CanonicalSerialize;
use ark_poly_commit::PCCommitmentState;
use ark_ec::VariableBaseMSM;
use ark_ec::CurveGroup;
use ark_ec::AffineRepr;
use ark_ec::ScalarMul;
use ark_std::collections::BTreeMap;
use ark_ff::FftField;
use crate::util;
use crate::samaritan_mlpcs::*;

pub struct DegreeCheckPolynomials<E: Pairing> {
    pub polys: Vec<DensePolynomial<E::ScalarField>>,
    pub degs: Vec<usize>,
}

pub struct DegreeCheckProof<E: Pairing> {
	shift: usize,
    poly_commit: Commitment<E>,
    extended_poly_commit: Commitment<E>,
}

pub struct DegreeCheck<E: Pairing>{
    _engine: PhantomData<E>,
}

impl<E: Pairing> DegreeCheck<E>
{
	pub fn prove(srs: &SamaritanMLPCS_SRS<E>, degree_check: &DegreeCheckPolynomials<E>) -> Result<DegreeCheckProof<E>, Error> {
		let mut transcript = Transcript::new(b"DegreeCheck Transcript");
		let num_polys = degree_check.polys.len();
		let max_deg = degree_check.degs.iter().copied().max().unwrap();

		let alpha = util::sample_random_challenge_from_transcript::<E>(&mut transcript, b"alpha");

		let mut aggregated_poly  = DensePolynomial::<E::ScalarField>::zero();
		for i in 0..num_polys {
			aggregated_poly = aggregated_poly + &degree_check.polys[i] * alpha.pow(&[i as u64]);
		}

		let aggregated_poly_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &aggregated_poly).unwrap();
        util::append_commitment_to_transcript::<E>(&mut transcript, b"aggregated_poly_commit", &aggregated_poly_commit);

        let shift = srs.powers_of_g.len() - (max_deg + 1);

        let aggregated_poly_extended_degree = DensePolynomial::<E::ScalarField>::from_coefficients_vec([vec![E::ScalarField::zero(); shift], aggregated_poly.coeffs().to_vec()].concat());
        let aggregated_poly_extended_degree_commit = SamaritanMLPCS::<E>::kzg10_commit_G1(&srs, &aggregated_poly_extended_degree).unwrap();
        util::append_commitment_to_transcript::<E>(&mut transcript, b"aggregated_poly_extended_degree_commit", &aggregated_poly_extended_degree_commit);

        Ok(DegreeCheckProof {
        	shift,
        	poly_commit: aggregated_poly_commit,
        	extended_poly_commit: aggregated_poly_extended_degree_commit,
        })
	}

	pub fn verify(srs: &SamaritanMLPCS_SRS<E>, proof: &DegreeCheckProof<E>) -> Result<bool, Error> {
		let pairing_lhs_first = E::G1Prepared::from(proof.poly_commit.0);
        let pairing_lhs_second = srs.powers_of_h[proof.shift];
        let pairing_lhs_res = E::pairing(pairing_lhs_first, pairing_lhs_second);

        let pairing_rhs_first = E::G1Prepared::from(proof.extended_poly_commit.0);
        let pairing_rhs_second = srs.powers_of_h[0];
        let pairing_rhs_res = E::pairing(pairing_rhs_first, pairing_rhs_second);

        Ok(pairing_lhs_res == pairing_rhs_res)
	}
}