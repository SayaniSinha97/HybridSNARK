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
··End:     HybridPlonk::prove with log_number_of_gates 16 ..........................4.022s
Start:   HybridPlonk::verify with multilinear polynomial
··End:     HybridPlonk::verify with multilinear polynomial .........................17.028ms
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
The output of running benchmarks looks like this (considering num_vars in {14,16}), indicating prover time and verifier time of HybridPlonk to be 1.193s and 17.517ms for num_vars=14, and 4.533s and 17.713ms for num_vars=16:
```
Benchmarking HybridPlonk_prove_benchmark/HybridPlonk_prove_14: Warming up for 3.0000 s
Warning: Unable to complete 10 samples in 5.0s. You may wish to increase target time to 11.7s.
HybridPlonk_prove_benchmark/HybridPlonk_prove_14
                        time:   [1.1805 s 1.1929 s 1.2059 s]
                        change: [+0.0502% +1.2481% +2.5931%] (p = 0.10 > 0.05)
                        No change in performance detected.

Benchmarking HybridPlonk_prove_benchmark/HybridPlonk_prove_16: Warming up for 3.0000 s
Warning: Unable to complete 10 samples in 5.0s. You may wish to increase target time to 44.5s.
HybridPlonk_prove_benchmark/HybridPlonk_prove_16
                        time:   [4.4856 s 4.5327 s 4.5738 s]
                        change: [-0.1069% +1.3935% +2.9308%] (p = 0.09 > 0.05)
                        No change in performance detected.
Found 2 outliers among 10 measurements (20.00%)
  2 (20.00%) low mild

HybridPlonk_verify_benchmark/HybridPlonk_verify_14
                        time:   [17.415 ms 17.517 ms 17.677 ms]
                        change: [-91.551% -91.411% -91.256%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 1 outliers among 10 measurements (10.00%)
  1 (10.00%) high severe

HybridPlonk_verify_benchmark/HybridPlonk_verify_16
                        time:   [17.501 ms 17.713 ms 17.902 ms]
                        change: [-97.497% -97.463% -97.426%] (p = 0.00 < 0.05)
                        Performance has improved.
```
By default, the benchmarks run for num_vars in {10, 12, 14, 16, 20}. One can change the values in the files benches/hyperplonk.rs or benches/hybridplonk.rs. Note that, benchmarking for higher values may take longer, since it considers multiple runs to provide the average. However, for higher values of num_vars one can check the output of ``cargo run --release -- <mode> <num_vars>``, which shows the timings of a single run.

