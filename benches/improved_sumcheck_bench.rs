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
use SuperPlonk::generic_improved_sumcheck::*;

type SamaritanMLPCS_Bls12_381 = SamaritanMLPCS<Bls12_381>;
type GenericImprovedSumcheck_Bls12_381 = GenericImprovedSumcheck<Bls12_381>;

// type SamaritanMLPCS_Bn254 = SamaritanMLPCS<Bn254>;
// type HyperPlonk_Bn254 = HyperPlonk<Bn254>;
fn myfunc(set_of_values: Vec<Fr>, additional_field_elements: &Vec<Fr>) -> Fr {
  set_of_values[0] * set_of_values[1] - set_of_values[2]
}

fn myfunc_poly(set_of_polys: &Vec<DensePolynomial<Fr>>, additional_field_elements: &Vec<Fr>) -> DensePolynomial<Fr> {
  &set_of_polys[0] * &set_of_polys[1] - &set_of_polys[2]
}

fn myfunc_linear_combined_poly(set_of_polys: &Vec<DensePolynomial<Fr>>, set_of_evals: &Vec<Option<Fr>>, additional_field_elements: &Vec<Fr>) -> DensePolynomial<Fr> {
  &set_of_polys[0] * set_of_evals[1].unwrap() - &set_of_polys[2]
}

fn prove_benchmark(c: &mut Criterion) {
  for num_vars in (14..=22).step_by(2) {
    let mut group = c.benchmark_group("ImprovedSumcheck_prove_benchmark");

    let n: usize = 1 << num_vars;
    let mut rng = &mut test_rng();
    
    let mlp_a = DenseMultilinearExtension::rand(num_vars, rng);

    let mlp_b = DenseMultilinearExtension::rand(num_vars, rng);

    let mut ab_vec: Vec<_> = Vec::new();
    for i in 0..n {
      // println!("i: {}, term: {}", i, mlp_a[i] * mlp_b[i]);
      ab_vec.push(Fr::from(mlp_a[i] * mlp_b[i]));
    }
    let mlp_ab = DenseMultilinearExtension::from_evaluations_vec(num_vars, ab_vec);

    let srs = SamaritanMLPCS::<Bls12_381>::setup(num_vars, rng).unwrap();
    let mlp_a_commit = SamaritanMLPCS::<Bls12_381>::commit_G1(&srs, &mlp_a).unwrap();
    let mlp_b_commit = SamaritanMLPCS::<Bls12_381>::commit_G1(&srs, &mlp_b).unwrap();
    let mlp_ab_commit = SamaritanMLPCS::<Bls12_381>::commit_G1(&srs, &mlp_ab).unwrap();

    let commit_list = vec![Some(mlp_a_commit), Some(mlp_b_commit), Some(mlp_ab_commit)];
    let sumcheck_relation: SumcheckRelation<Bls12_381> = SumcheckRelation {
                  log_number_of_vars: num_vars,
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

    let name = format!("ImprovedSumcheck_prove_{}", num_vars);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        GenericImprovedSumcheck_Bls12_381::prove(&srs, &sumcheck_relation).unwrap();
      });
    });
    group.finish();
  }
}

fn verify_benchmark(c: &mut Criterion) {
  for num_vars in (14..=22).step_by(2) {
    let mut group = c.benchmark_group("ImprovedSumcheck_verify_benchmark");

    let n: usize = 1 << num_vars;
    let mut rng = &mut test_rng();

    let mlp_a = DenseMultilinearExtension::rand(num_vars, rng);

    let mlp_b = DenseMultilinearExtension::rand(num_vars, rng);

    let mut ab_vec: Vec<_> = Vec::new();
    for i in 0..n {
      // println!("i: {}, term: {}", i, mlp_a[i] * mlp_b[i]);
      ab_vec.push(Fr::from(mlp_a[i] * mlp_b[i]));
    }
    let mlp_ab = DenseMultilinearExtension::from_evaluations_vec(num_vars, ab_vec);

    let srs = SamaritanMLPCS::<Bls12_381>::setup(num_vars, rng).unwrap();
    let mlp_a_commit = SamaritanMLPCS::<Bls12_381>::commit_G1(&srs, &mlp_a).unwrap();
    let mlp_b_commit = SamaritanMLPCS::<Bls12_381>::commit_G1(&srs, &mlp_b).unwrap();
    let mlp_ab_commit = SamaritanMLPCS::<Bls12_381>::commit_G1(&srs, &mlp_ab).unwrap();

    let commit_list = vec![Some(mlp_a_commit), Some(mlp_b_commit), Some(mlp_ab_commit)];
    let sumcheck_relation: SumcheckRelation<Bls12_381> = SumcheckRelation {
                  log_number_of_vars: num_vars,
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

    let name = format!("ImprovedSumcheck_verify_{}", num_vars);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        GenericImprovedSumcheck_Bls12_381::verify(&generic_improved_sumcheck_proof, sumcheck_relation.commit_list.clone(), &srs).unwrap();
      });
    });
    group.finish();
  }
}

criterion_group! {
    name = improved_sumcheck_benches;
    config = Criterion::default().sample_size(10);
    targets = prove_benchmark, verify_benchmark
}
criterion_main!(improved_sumcheck_benches);