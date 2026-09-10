#!/bin/bash

cargo build
echo "Build done\n\n"

echo "\nRunning HybridSpartan"
echo "============================="
for i in 14 16 18 20 22 24
do
    V=$i RAYON_NUM_THREADS=1 RUSTFLAGS="-Awarnings" cargo test --release hybridspartan::tests::functionality_test -- --nocapture
    echo "\n-----------------------------------------------------------------------\n"
done

echo "\nRunning HybridPlonk"
echo "============================="
for i in 15 17 19 21 23 25 
do
    V=$i RAYON_NUM_THREADS=1 RUSTFLAGS="-Awarnings" cargo test --release hybridplonk::tests::functionality_test -- --nocapture
    echo "\n-----------------------------------------------------------------------\n"
done