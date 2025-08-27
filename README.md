# HybridPlonk
This repository contains an implementation of HybridPlonk, a SNARK with linear prover and sublogarithmic proof length. We also provide an implementation of HyperPlonk with SamaritanPCS as its underlying PCS, which serves as a baseline for comparison with HybridPlonk. Consequently, the repo contains the first implementation of SamaritanPCS as well.


The src folder contains \
                        (i) samaritan_mlpcs.rs : Implementation of Samaritan Multilinear Polynomial Commitment Scheme (https://eprint.iacr.org/2025/419), \
                        (ii) hyperplonk.rs: Implementation of HyperPlonk with Samaritan PCS as its base PCS, and \
                        (iii) hybridplonk.rs: Implementation of our proposed SNARK, HybridPlonk (which is also instantiated with Samaritan PCS), \
along with a few helper files.

# Testing functionality
To run the tests, please run:
```
cargo test --release
```
This leads to functionality tests of all three implementations.

# Run a specific instance
To run a specific instance of any of the above three programs (samaritan_mlpcs, hyperplonk, or hybridplonk) with your choice of number_of_variables (which is log(number_of_constraints)), please run:
```
cargo run --release -- <mode> <num_vars>
```

For example,
```
cargo run --release -- 3 16
```

will produce timing output for HybridPlonk with 16 variables as following:
```
Start:   HybridPlonk::prove with log_number_of_gates 16
··End:     HybridPlonk::prove with log_number_of_gates 16 ..........................4.190s
Start:   HybridPlonk::verify with multilinear polynomial
··End:     HybridPlonk::verify with multilinear polynomial .........................629.082ms
```

# Run benchmarks
To run the benchmark for hyperplonk (with Samaritan as underlying PCS), please run:
```
RUSTFLAGS="-C target_cpu=native" cargo bench --bench hyperplonk_bench
```

Similarly, to run the benchmark for hybridplonk, please run:
```
RUSTFLAGS="-C target_cpu=native" cargo bench --bench hybridplonk_bench
```
The output of running benchmarks looks like this (considering num_vars in {14,16}):
```
Benchmarking HybridPlonk_prove_benchmark/HybridPlonk_prove_14: Warming up for 3.0000 s
Warning: Unable to complete 10 samples in 5.0s. You may wish to increase target time to 10.9s.
HybridPlonk_prove_benchmark/HybridPlonk_prove_14
                        time:   [1.0972 s 1.1038 s 1.1099 s]
                        change: [-18.449% -17.368% -16.413%] (p = 0.00 < 0.05)
                        Performance has improved.

Benchmarking HybridPlonk_prove_benchmark/HybridPlonk_prove_16: Warming up for 3.0000 s
Warning: Unable to complete 10 samples in 5.0s. You may wish to increase target time to 39.8s.
HybridPlonk_prove_benchmark/HybridPlonk_prove_16
                        time:   [3.9564 s 3.9698 s 3.9836 s]
                        change: [-21.452% -19.672% -17.830%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 2 outliers among 10 measurements (20.00%)
  1 (10.00%) low mild
  1 (10.00%) high mild

Benchmarking HybridPlonk_verify_benchmark/HybridPlonk_verify_14: Warming up for 3.0000 s
Warning: Unable to complete 10 samples in 5.0s. You may wish to increase target time to 9.8s or enable flat sampling.
HybridPlonk_verify_benchmark/HybridPlonk_verify_14
                        time:   [171.83 ms 175.09 ms 179.20 ms]
                        change: [-21.902% -19.959% -17.935%] (p = 0.00 < 0.05)
                        Performance has improved.

Benchmarking HybridPlonk_verify_benchmark/HybridPlonk_verify_16: Warming up for 3.0000 s
Warning: Unable to complete 10 samples in 5.0s. You may wish to increase target time to 6.2s.
HybridPlonk_verify_benchmark/HybridPlonk_verify_16
                        time:   [603.51 ms 609.28 ms 615.01 ms]
                        change: [-18.695% -17.750% -16.815%] (p = 0.00 < 0.05)
                        Performance has improved.
```
By default, the benchmarks run for num_vars in {10, 12, 14, 16, 20}. One can change the values in the files benches/hyperplonk.rs or benches/hybridplonk.rs. Note that, benchmarking for higher values may take longer, since it considers multiple runs to provide the average. However, for higher values of num_vars one can check the output of ``cargo run --release -- <mode> <num_vars>``, which shows the timings of a single run.

