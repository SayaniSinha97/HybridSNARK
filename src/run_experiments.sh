#!/bin/bash

cargo build
echo "Build done\n\n"

echo "\nRunning HybridSpartan over BLS12-381"
echo "============================="
for i in 14 16 
do
    V=$i RAYON_NUM_THREADS=1 RUSTFLAGS="-Awarnings" cargo test --release --features bls12_381 hybridspartan::tests::functionality_test -- --nocapture
    echo "\n-----------------------------------------------------------------------\n"
done


echo "\nRunning HybridSpartan over BN254"
echo "============================="
for i in 14 16 
do
    V=$i RAYON_NUM_THREADS=1 RUSTFLAGS="-Awarnings" cargo test --release --features bn254 hybridspartan::tests::functionality_test -- --nocapture
    echo "\n-----------------------------------------------------------------------\n"
done


echo "\nRunning HybridPlonk over BLS12-381"
echo "============================="
for i in 15 17 
do
    V=$i RAYON_NUM_THREADS=1 RUSTFLAGS="-Awarnings" cargo test --release --features bls12_381 hybridplonk::tests::functionality_test -- --nocapture
    echo "\n-----------------------------------------------------------------------\n"
done


echo "\nRunning HybridPlonk over BN254"
echo "============================="
for i in 15 17 
do
    V=$i RAYON_NUM_THREADS=1 RUSTFLAGS="-Awarnings" cargo test --release --features bn254 hybridplonk::tests::functionality_test -- --nocapture
    echo "\n-----------------------------------------------------------------------\n"
done