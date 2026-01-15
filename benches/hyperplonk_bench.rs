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

use criterion::*;

use SuperPlonk::samaritan_mlpcs::*;
use SuperPlonk::hyperplonk::*;

type SamaritanMLPCS_Bls12_381 = SamaritanMLPCS<Bls12_381>;
type HyperPlonk_Bls12_381 = HyperPlonk<Bls12_381>;

// type SamaritanMLPCS_Bn254 = SamaritanMLPCS<Bn254>;
// type HyperPlonk_Bn254 = HyperPlonk<Bn254>;

fn prove_benchmark(c: &mut Criterion) {
  for num_vars in (14..=22).step_by(2) {
    let mut group = c.benchmark_group("HyperPlonk_prove_benchmark");

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

    let (srs, 
            qM_comm, qL_comm, qR_comm, qO_comm, qC_comm, 
            sigma1_comm, sigma2_comm, sigma3_comm, 
            id1_comm, id2_comm, id3_comm) = HyperPlonk_Bls12_381::setup(&myckt, &mut rng).unwrap();

    let name = format!("HyperPlonk_prove_{}", num_vars);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        HyperPlonk_Bls12_381::prove(&myckt, &w1, &w2, &w3, &srs).unwrap();
      });
    });
    group.finish();
  }
}

fn verify_benchmark(c: &mut Criterion) {
  for num_vars in (14..=22).step_by(2) {
    let mut group = c.benchmark_group("HyperPlonk_verify_benchmark");

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

    let (srs, 
            qM_comm, qL_comm, qR_comm, qO_comm, qC_comm, 
            sigma1_comm, sigma2_comm, sigma3_comm, 
            id1_comm, id2_comm, id3_comm) = HyperPlonk_Bls12_381::setup(&myckt, &mut rng).unwrap();

    let hyperplonk_proof = HyperPlonk_Bls12_381::prove(&myckt, &w1, &w2, &w3, &srs).unwrap();

    let name = format!("HyperPlonk_verify_{}", num_vars);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        HyperPlonk_Bls12_381::verify(&hyperplonk_proof, &myckt, &srs,
        qM_comm, qL_comm, qR_comm, qO_comm, qC_comm, 
            sigma1_comm, sigma2_comm, sigma3_comm, 
            id1_comm, id2_comm, id3_comm).unwrap();
      });
    });
    group.finish();
  }
}

criterion_group! {
    name = hyperplonk_benches;
    config = Criterion::default().sample_size(10);
    targets = prove_benchmark, verify_benchmark
}
criterion_main!(hyperplonk_benches);