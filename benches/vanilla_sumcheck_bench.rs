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
use SuperPlonk::vanilla_sumcheck::*;

type SamaritanMLPCS_Bls12_381 = SamaritanMLPCS<Bls12_381>;
type VanillaSumcheck_Bls12_381 = VanillaSumcheck<Bls12_381>;

// type SamaritanMLPCS_Bn254 = SamaritanMLPCS<Bn254>;
// type HyperPlonk_Bn254 = HyperPlonk<Bn254>;

fn prove_benchmark(c: &mut Criterion) {
  for num_vars in (16..=24).step_by(2) {
    let mut group = c.benchmark_group("VanillaSumcheck_prove_benchmark");

    let n: usize = 1 << num_vars;
    let mut rng = &mut test_rng();
    
    let mlp_a = DenseMultilinearExtension::rand(num_vars, rng);

    let mlp_b = DenseMultilinearExtension::rand(num_vars, rng);

    let mut ab_vec: Vec<_> = Vec::new();
    for i in 0..n {
        ab_vec.push(Fr::from(mlp_a[i] * mlp_b[i]));
    }
    let mlp_ab = DenseMultilinearExtension::from_evaluations_vec(num_vars, ab_vec);

    let srs = VanillaSumcheck_Bls12_381::setup(&mut rng, num_vars).unwrap();

    let name = format!("VanillaSumcheck_prove_{}", num_vars);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        VanillaSumcheck_Bls12_381::prove(&srs, num_vars, &mlp_a, &mlp_b, &mlp_ab).unwrap();
      });
    });
    group.finish();
  }
}

fn verify_benchmark(c: &mut Criterion) {
  for num_vars in (16..=24).step_by(2) {
    let mut group = c.benchmark_group("VanillaSumcheck_verify_benchmark");

    let n: usize = 1 << num_vars;
    let mut rng = &mut test_rng();

    let mlp_a = DenseMultilinearExtension::rand(num_vars, rng);

    let mlp_b = DenseMultilinearExtension::rand(num_vars, rng);

    let mut ab_vec: Vec<_> = Vec::new();
    for i in 0..n {
        ab_vec.push(Fr::from(mlp_a[i] * mlp_b[i]));
    }
    let mlp_ab = DenseMultilinearExtension::from_evaluations_vec(num_vars, ab_vec);

    let srs = VanillaSumcheck_Bls12_381::setup(&mut rng, num_vars).unwrap();

    let vanilla_sumcheck_proof = VanillaSumcheck_Bls12_381::prove(&srs, num_vars, &mlp_a, &mlp_b, &mlp_ab).unwrap();

    let name = format!("VanillaSumcheck_verify_{}", num_vars);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        VanillaSumcheck_Bls12_381::verify(&vanilla_sumcheck_proof, &srs).unwrap();
      });
    });
    group.finish();
  }
}

criterion_group! {
    name = vanilla_sumcheck_benches;
    config = Criterion::default().sample_size(10);
    targets = prove_benchmark, verify_benchmark
}
criterion_main!(vanilla_sumcheck_benches);