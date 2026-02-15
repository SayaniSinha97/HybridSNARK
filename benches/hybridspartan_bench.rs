use ark_poly_commit::kzg10::*;
use ark_poly_commit::*;
use ark_ec::pairing::Pairing;
// use ark_bls12_381::Bls12_381;
// use ark_bls12_381::Fr;
use ark_bn254::Bn254;
use ark_bn254::Fr;
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

use criterion::*;

use SuperPlonk::samaritan_mlpcs::*;
use SuperPlonk::generic_improved_sumcheck::*;
use SuperPlonk::hybridspartan::*;

// type SamaritanMLPCS_Bls12_381 = SamaritanMLPCS<Bls12_381>;
// type GenericImprovedSumcheck_Bls12_381 = GenericImprovedSumcheck<Bls12_381>;
// type HybridSpartan_Bls12_381 = HybridSpartan<Bls12_381>;

type SamaritanMLPCS_Bn254 = SamaritanMLPCS<Bn254>;
type GenericImprovedSumcheck_Bn254 = GenericImprovedSumcheck<Bn254>;
type HybridSpartan_Bn254 = HybridSpartan<Bn254>;

fn prove_benchmark(c: &mut Criterion) {
  for num_vars in (14..=22).step_by(2) {
    let mut group = c.benchmark_group("HybridSpartan_prove_benchmark");

    let n: usize = 1 << (num_vars - 2);
    let mut rng = &mut test_rng();
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

    let myckt: HybridSpartanCircuit::<Bn254> = HybridSpartan_Bn254::generate_circuit_for_inner_product(&A, &B, k, n);
    let (srs, 
        ROW_tilde, COL_tilde, VAL_A_tilde, VAL_B_tilde, VAL_C_tilde, id_tilde,
        ROW_tilde_commit, COL_tilde_commit, VAL_A_tilde_commit, VAL_B_tilde_commit, VAL_C_tilde_commit, id_tilde_commit) = HybridSpartan_Bn254::preprocessing(&myckt, &mut rng).unwrap();



    let name = format!("HybridSpartan_prove_{}", num_vars);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        HybridSpartan_Bn254::prove(&myckt, &srs, &z, 
                                        &ROW_tilde, &COL_tilde, &VAL_A_tilde, &VAL_B_tilde, &VAL_C_tilde, &id_tilde,
                                        &ROW_tilde_commit, &COL_tilde_commit, &VAL_A_tilde_commit, &VAL_B_tilde_commit, &VAL_C_tilde_commit, &id_tilde_commit).unwrap();
      });
    });
    group.finish();
  }
}

fn verify_benchmark(c: &mut Criterion) {
  for num_vars in (14..=22).step_by(2) {
    let mut group = c.benchmark_group("HybridSpartan_verify_benchmark");

    let n: usize = 1 << (num_vars - 2);
    let mut rng = &mut test_rng();
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

    let myckt: HybridSpartanCircuit::<Bn254> = HybridSpartan_Bn254::generate_circuit_for_inner_product(&A, &B, k, n);
    let (srs, 
        ROW_tilde, COL_tilde, VAL_A_tilde, VAL_B_tilde, VAL_C_tilde, id_tilde,
        ROW_tilde_commit, COL_tilde_commit, VAL_A_tilde_commit, VAL_B_tilde_commit, VAL_C_tilde_commit, id_tilde_commit) = HybridSpartan_Bn254::preprocessing(&myckt, &mut rng).unwrap();

    let hybridspartan_proof = HybridSpartan_Bn254::prove(&myckt, &srs, &z, 
                                        &ROW_tilde, &COL_tilde, &VAL_A_tilde, &VAL_B_tilde, &VAL_C_tilde, &id_tilde,
                                        &ROW_tilde_commit, &COL_tilde_commit, &VAL_A_tilde_commit, &VAL_B_tilde_commit, &VAL_C_tilde_commit, &id_tilde_commit).unwrap();

    let name = format!("HybridSpartan_verify_{}", num_vars);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        HybridSpartan_Bn254::verify(&hybridspartan_proof, &myckt, &srs,
                                    &ROW_tilde, &COL_tilde, &VAL_A_tilde, &VAL_B_tilde, &VAL_C_tilde, &id_tilde,
                                    &ROW_tilde_commit, &COL_tilde_commit, &VAL_A_tilde_commit, &VAL_B_tilde_commit, &VAL_C_tilde_commit, &id_tilde_commit).unwrap();
      });
    });
    group.finish();
  }
}

criterion_group! {
    name = hybridspartan_benches;
    config = Criterion::default().sample_size(10);
    targets = prove_benchmark, verify_benchmark
}
criterion_main!(hybridspartan_benches);