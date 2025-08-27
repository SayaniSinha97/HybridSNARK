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

By default, the benchmarks run for num_vars in [10, 12, 14, 16, 20]. One can change the values in the files benches/hyperplonk.rs or benches/hybridplonk.rs. Note that, benchmarking for higher values may take longer, since it considers multiple runs to provide the average. However, for higher values of num_vars one can check the output of ``cargo run --release -- <mode> <num_vars>``, which shows the timings of a single run.

