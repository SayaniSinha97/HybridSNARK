use ark_poly_commit::kzg10::*;
use ark_poly_commit::*;
use ark_ec::pairing::Pairing;
use ark_bls12_381::Bls12_381;
use ark_bls12_381::Fr;
// use ark_bn254::Bn254;
// use ark_bn254::Fr;
use ark_std::test_rng;
use ark_std::{rand::Rng, vec::Vec};
use ark_std::{start_timer, end_timer, Zero, One, marker::PhantomData};
use ark_std::UniformRand;
use ark_std::rand::seq::SliceRandom;

use ark_poly::polynomial::Polynomial;
use ark_poly::DenseUVPolynomial;
use ark_poly::evaluations::multivariate::multilinear::MultilinearExtension;
use ark_poly::univariate::DensePolynomial;
use ark_poly::univariate::SparsePolynomial;
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension;

use SuperPlonk::samaritan_mlpcs::*;
use SuperPlonk::hyperplonk::*;
use SuperPlonk::hybridplonk::*;

type SamaritanMLPCS_Bls12_381 = SamaritanMLPCS<Bls12_381>;
type HyperPlonk_Bls12_381 = HyperPlonk<Bls12_381>;
type HybridPlonk_Bls12_381 = HybridPlonk<Bls12_381>;

// type SamaritanMLPCS_Bn254 = SamaritanMLPCS<Bn254>;
// type HyperPlonk_Bn254 = HyperPlonk<Bn254>;
// type HybridPlonk_Bn254 = HybridPlonk<Bn254>;

pub fn run_samaritan_mlpcs(num_vars: usize) {
    let mut rng = &mut test_rng();
    let mlp = DenseMultilinearExtension::rand(num_vars, rng);
    let srs = SamaritanMLPCS_Bls12_381::setup(num_vars, &mut rng).unwrap();
    let comm = SamaritanMLPCS_Bls12_381::commit_G1(&srs, &mlp).unwrap();
    // let srs = SamaritanMLPCS_Bn254::setup(num_vars, &mut rng).unwrap();
    // let comm = SamaritanMLPCS_Bn254::commit_G1(&srs, &mlp).unwrap();
    let point: Vec<_> = (0..num_vars).map(|_| Fr::rand(rng)).collect();
    let eval = mlp.evaluate(&point);

    let samaritan_prove_time = start_timer!(|| format!("SamaritanMLPCS::prove with multilinear polynomial of maximum variables {}", num_vars));
    let eval_proof = SamaritanMLPCS_Bls12_381::prove(&srs, &mlp, &point, eval, &mut rng).unwrap();
    end_timer!(samaritan_prove_time);

    let samaritan_verify_time = start_timer!(|| format!("SamaritanMLPCS::verify with multilinear polynomial"));
    let valid = SamaritanMLPCS_Bls12_381::verify(&srs, &comm, &point, eval, &eval_proof).unwrap();
    end_timer!(samaritan_verify_time);
    // let eval_proof = SamaritanMLPCS_Bn254::prove(&srs, &mlp, &point, eval, &mut rng).unwrap();
    // let valid = SamaritanMLPCS_Bn254::verify(&srs, &comm, &point, eval, &eval_proof).unwrap();
    assert_eq!(valid, true);
}

pub fn run_hyperplonk(num_vars: usize) {
    let n: usize = 1 << (num_vars - 1);
    let mut rng = &mut test_rng();
    let A: Vec<usize> = (0..n).map(|_| rng.gen_range(1..5)).collect();
    let B: Vec<usize> = (0..n).map(|_| rng.gen_range(1..5)).collect();
    let myckt = HyperPlonk_Bls12_381::generate_circuit_for_inner_product(&A, &B, n);
    // let myckt = HyperPlonk_Bn254::generate_circuit_for_inner_product(&A, &B, n);

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

    let w1 = DenseMultilinearExtension::from_evaluations_vec(num_vars, w1_vec);
    let w2 = DenseMultilinearExtension::from_evaluations_vec(num_vars, w2_vec);
    let w3 = DenseMultilinearExtension::from_evaluations_vec(num_vars, w3_vec);

    let srs = SamaritanMLPCS_Bls12_381::setup(num_vars, &mut rng).unwrap();

    let hyperplonk_prover_time = start_timer!(|| format!("HyperPlonk::prove with log_number_of_gates {}", num_vars));
    let hyperplonk_proof = HyperPlonk_Bls12_381::prove(&myckt, &w1, &w2, &w3, &srs).unwrap();
    end_timer!(hyperplonk_prover_time);

    let hyperplonk_verifier_time = start_timer!(|| format!("HyperPlonk::verify with multilinear polynomial"));
    let valid = HyperPlonk_Bls12_381::verify(&hyperplonk_proof, &myckt, &srs).unwrap();
    end_timer!(hyperplonk_verifier_time);

    // let srs = SamaritanMLPCS_Bn254::setup(num_vars, &mut rng).unwrap();
    // let hyperplonk_proof = HyperPlonk_Bn254::prove(&myckt, &w1, &w2, &w3, &srs).unwrap();
    // let valid = HyperPlonk_Bn254::verify(&hyperplonk_proof, &myckt, &srs).unwrap();

    assert_eq!(valid, true);
}

pub fn run_hybridplonk(num_vars: usize) {
    let n: usize = 1 << (num_vars - 1);
    let mut rng = &mut test_rng();
    let A: Vec<usize> = (0..n).map(|_| rng.gen_range(1..5)).collect();
    let B: Vec<usize> = (0..n).map(|_| rng.gen_range(1..5)).collect();
    let myckt = HybridPlonk_Bls12_381::generate_circuit_for_inner_product(&A, &B, n);
    // let myckt = HybridPlonk_Bn254::generate_circuit_for_inner_product(&A, &B, n);

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

    let w1 = DenseMultilinearExtension::from_evaluations_vec(num_vars, w1_vec);
    let w2 = DenseMultilinearExtension::from_evaluations_vec(num_vars, w2_vec);
    let w3 = DenseMultilinearExtension::from_evaluations_vec(num_vars, w3_vec);

    let srs = SamaritanMLPCS_Bls12_381::setup(num_vars, &mut rng).unwrap();

    let hybridplonk_prover_time = start_timer!(|| format!("HybridPlonk::prove with log_number_of_gates {}", num_vars));
    let hybridplonk_proof = HybridPlonk_Bls12_381::prove(&myckt, &w1, &w2, &w3, &srs).unwrap();
    end_timer!(hybridplonk_prover_time);

    let hybridplonk_verifier_time = start_timer!(|| format!("HybridPlonk::verify with multilinear polynomial"));
    let valid = HybridPlonk_Bls12_381::verify(&hybridplonk_proof, &myckt, &srs).unwrap();
    end_timer!(hybridplonk_verifier_time);

    // let srs = SamaritanMLPCS_Bn254::setup(num_vars, &mut rng).unwrap();
    // let hybridplonk_proof = HybridPlonk_Bn254::prove(&myckt, &w1, &w2, &w3, &srs).unwrap();
    // let valid = HybridPlonk_Bn254::verify(&hybridplonk_proof, &myckt, &srs).unwrap();

    assert_eq!(valid, true);
}

fn main(){
	let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: cargo run --release -- <mode> <num_vars>. \n
        	'mode' can take values 1, 2, or 3 to run Samaritan PCS, HyperPlonk or HybridPlonk respectively.\n
        	'num_vars' can take any unsigned integer value such that 2^num_vars is the number of constraints/gates in each of the three cases.");
        return;
    }

    let mode: u32 = args[1].parse().expect("Please provide a valid number");

    if ![1, 2, 3].contains(&mode) {
        eprintln!("Error: mode must be 1, 2, or 3");
        return;
    }

    let num_vars: usize = args[2].parse().expect("Please provide a valid number");

    if mode == 1 {
		run_samaritan_mlpcs(num_vars);
    }
    else if mode == 2 {
		run_hyperplonk(num_vars);
    }
    else {
		run_hybridplonk(num_vars);
    }
}
