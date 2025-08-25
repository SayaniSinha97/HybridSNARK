// use ark_poly_commit::kzg10::*;
// use ark_poly_commit::*;
// use ark_ec::pairing::Pairing;
// use ark_bls12_381::Bls12_381;
// use ark_bls12_381::Fr;
// // use ark_bn254::Bn254;
// // use ark_bn254::Fr;
// use ark_std::test_rng;
// use ark_std::{rand::Rng, vec::Vec};
// use ark_std::{start_timer, end_timer, Zero, One, marker::PhantomData};
// use ark_std::UniformRand;
// use ark_std::rand::seq::SliceRandom;

// use ark_poly::polynomial::Polynomial;
// use ark_poly::DenseUVPolynomial;
// use ark_poly::evaluations::multivariate::multilinear::MultilinearExtension;
// use ark_poly::univariate::DensePolynomial;
// use ark_poly::univariate::SparsePolynomial;
// use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension;

// use SuperPlonk::samaritan_mlpcs::*;
// use SuperPlonk::hyperplonk::*;
// use SuperPlonk::hybridplonk::*;

// type SamaritanMLPCS_Bls12_381 = SamaritanMLPCS<Bls12_381>;
// type HyperPlonk_Bls12_381 = HyperPlonk<Bls12_381>;
// type HybridPlonk_Bls12_381 = HybridPlonk<Bls12_381>;

// // type SamaritanMLPCS_Bn254 = SamaritanMLPCS<Bn254>;
// // type HyperPlonk_Bn254 = HyperPlonk<Bn254>;
// // type HybridPlonk_Bn254 = HybridPlonk<Bn254>;

// pub fn benchmark_samaritan_mlpcs(start_num_vars: usize, end_num_vars: usize) {
//     for num_vars in (start_num_vars..=end_num_vars).step_by(2) {
//         let mut rng = &mut test_rng();
//         let mlp = DenseMultilinearExtension::rand(num_vars, rng);
//         let srs = SamaritanMLPCS_Bls12_381::setup(num_vars, &mut rng).unwrap();
//         let comm = SamaritanMLPCS_Bls12_381::commit_G1(&srs, &mlp).unwrap();
//         // let srs = SamaritanMLPCS_Bn254::setup(num_vars, &mut rng).unwrap();
//         // let comm = SamaritanMLPCS_Bn254::commit_G1(&srs, &mlp).unwrap();
//         let point: Vec<_> = (0..num_vars).map(|_| Fr::rand(rng)).collect();
//         let eval = mlp.evaluate(&point);
//         let eval_proof = SamaritanMLPCS_Bls12_381::prove(&srs, &mlp, &point, eval, &mut rng).unwrap();
//         let valid = SamaritanMLPCS_Bls12_381::verify(&srs, &comm, &point, eval, &eval_proof).unwrap();
//         // let eval_proof = SamaritanMLPCS_Bn254::prove(&srs, &mlp, &point, eval, &mut rng).unwrap();
//         // let valid = SamaritanMLPCS_Bn254::verify(&srs, &comm, &point, eval, &eval_proof).unwrap();
//         assert_eq!(valid, true);
//     }
// }

// pub fn benchmark_hyperplonk(start_num_vars: usize, end_num_vars: usize) {
//     for num_vars in (start_num_vars..=end_num_vars).step_by(2) {
//         let n: usize = 1 << (num_vars - 1);
//         let mut rng = &mut test_rng();
//         let A: Vec<usize> = (0..n).map(|_| rng.gen_range(1..5)).collect();
//         let B: Vec<usize> = (0..n).map(|_| rng.gen_range(1..5)).collect();
//         let myckt = HyperPlonk_Bls12_381::generate_circuit_for_inner_product(&A, &B, n);
//         // let myckt = HyperPlonk_Bn254::generate_circuit_for_inner_product(&A, &B, n);

//         let mut w1_vec: Vec<_> = Vec::new();
//         let mut w2_vec: Vec<_> = Vec::new();
//         let mut w3_vec: Vec<_> = Vec::new();

//         for i in 0..n {
//             w1_vec.push(Fr::from(A[i] as u64));
//             w2_vec.push(Fr::from(B[i] as u64));
//             w3_vec.push(Fr::from((A[i] * B[i]) as u64));
//         }

//         for i in 0..n {
//             if i == 0 {
//                 w1_vec.push(w1_vec[0] * w2_vec[0]);
//             }
//             else{
//                 w1_vec.push(w1_vec[n + i - 1] + w2_vec[n + i -1]);
//             }
//             if i == n-1 {
//                 w2_vec.push(Fr::zero());
//             }
//             else{
//                 w2_vec.push(w1_vec[i + 1] * w2_vec[i + 1]);
//             }
//             w3_vec.push(w1_vec[n + i] + w2_vec[n + i]);
//         }

//         let w1 = DenseMultilinearExtension::from_evaluations_vec(num_vars, w1_vec);
//         let w2 = DenseMultilinearExtension::from_evaluations_vec(num_vars, w2_vec);
//         let w3 = DenseMultilinearExtension::from_evaluations_vec(num_vars, w3_vec);

//         let srs = SamaritanMLPCS_Bls12_381::setup(num_vars, &mut rng).unwrap();
//         let hyperplonk_proof = HyperPlonk_Bls12_381::prove(&myckt, &w1, &w2, &w3, &srs).unwrap();
//         let valid = HyperPlonk_Bls12_381::verify(&hyperplonk_proof, &myckt, &srs).unwrap();

//         // let srs = SamaritanMLPCS_Bn254::setup(num_vars, &mut rng).unwrap();
//         // let hyperplonk_proof = HyperPlonk_Bn254::prove(&myckt, &w1, &w2, &w3, &srs).unwrap();
//         // let valid = HyperPlonk_Bn254::verify(&hyperplonk_proof, &myckt, &srs).unwrap();
//         assert_eq!(valid, true);
//     }
// }

// pub fn benchmark_hybridplonk(start_num_vars: usize, end_num_vars: usize) {
//     for num_vars in (start_num_vars..=end_num_vars).step_by(2) {
//         let n: usize = 1 << (num_vars - 1);
//         let mut rng = &mut test_rng();
//         let A: Vec<usize> = (0..n).map(|_| rng.gen_range(1..5)).collect();
//         let B: Vec<usize> = (0..n).map(|_| rng.gen_range(1..5)).collect();
//         let myckt = HybridPlonk_Bls12_381::generate_circuit_for_inner_product(&A, &B, n);
//         // let myckt = HybridPlonk_Bn254::generate_circuit_for_inner_product(&A, &B, n);

//         let mut w1_vec: Vec<_> = Vec::new();
//         let mut w2_vec: Vec<_> = Vec::new();
//         let mut w3_vec: Vec<_> = Vec::new();

//         for i in 0..n {
//             w1_vec.push(Fr::from(A[i] as u64));
//             w2_vec.push(Fr::from(B[i] as u64));
//             w3_vec.push(Fr::from((A[i] * B[i]) as u64));
//         }

//         for i in 0..n {
//             if i == 0 {
//                 w1_vec.push(w1_vec[0] * w2_vec[0]);
//             }
//             else{
//                 w1_vec.push(w1_vec[n + i - 1] + w2_vec[n + i -1]);
//             }
//             if i == n-1 {
//                 w2_vec.push(Fr::zero());
//             }
//             else{
//                 w2_vec.push(w1_vec[i + 1] * w2_vec[i + 1]);
//             }
//             w3_vec.push(w1_vec[n + i] + w2_vec[n + i]);
//         }

//         let w1 = DenseMultilinearExtension::from_evaluations_vec(num_vars, w1_vec);
//         let w2 = DenseMultilinearExtension::from_evaluations_vec(num_vars, w2_vec);
//         let w3 = DenseMultilinearExtension::from_evaluations_vec(num_vars, w3_vec);

//         let srs = SamaritanMLPCS_Bls12_381::setup(num_vars, &mut rng).unwrap();
//         let hybridplonk_proof = HybridPlonk_Bls12_381::prove(&myckt, &w1, &w2, &w3, &srs).unwrap();
//         let valid = HybridPlonk_Bls12_381::verify(&hybridplonk_proof, &myckt, &srs).unwrap();

//         // let srs = SamaritanMLPCS_Bn254::setup(num_vars, &mut rng).unwrap();
//         // let hybridplonk_proof = HybridPlonk_Bn254::prove(&myckt, &w1, &w2, &w3, &srs).unwrap();
//         // let valid = HybridPlonk_Bn254::verify(&hybridplonk_proof, &myckt, &srs).unwrap();
//         assert_eq!(valid, true);
//     }
// }

fn main(){

//     let start_num_vars : usize = 16; 
//     let end_num_vars : usize = 24;

//     //println!("================================================================================================================================");
//     //println!("Benchmarking Prover time and Verifier time in Samaritan MLPCS with number_of_vars varied between {} and {}", start_num_vars, end_num_vars);
//     //println!("================================================================================================================================");
//     //benchmark_samaritan_mlpcs(start_num_vars, end_num_vars);

//     println!("================================================================================================================================");
//     println!("Benchmarking Prover time and Verifier time in HyperPlonk SNARK with number_of_vars varied between {} and {}", start_num_vars, end_num_vars);
//     println!("================================================================================================================================");
//     benchmark_hyperplonk(start_num_vars, end_num_vars);

//     println!("================================================================================================================================");
//     println!("Benchmarking Prover time and Verifier time in HybridPlonk SNARK with number_of_vars varied between {} and {}", start_num_vars, end_num_vars);
//     println!("================================================================================================================================");
//     benchmark_hybridplonk(start_num_vars, end_num_vars);
}
