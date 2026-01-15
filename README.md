# HybridPlonk
This repository contains an implementation of HybridPlonk, a SNARK with linear prover and sublogarithmic proof length. We also provide an implementation of HyperPlonk with SamaritanPCS as its underlying PCS, which serves as a baseline for comparison with HybridPlonk.


The src folder contains \
                        (i) hyperplonk.rs: Implementation of HyperPlonk with Samaritan PCS as its base PCS, and \
                        (ii) hybridplonk.rs: Implementation of our proposed SNARK, HybridPlonk (which is also instantiated with Samaritan PCS), \
                        (iii) improved_sumcheck.rs: Implements a sumcheck argument for a simple multivariate sumcheck instance and let us benchmark its performance against vaniila_sumcheck.rs.
along with a few helper files.

# Testing functional correctness
To run the tests, please run:
```
cargo test --release
```
This leads to functionality tests of all three implementations.

# Run benchmarks
To run the benchmark for hyperplonk (with Samaritan as underlying PCS), please run:
```
RUSTFLAGS="-C target_cpu=native" cargo bench --bench hyperplonk_bench
```

Similarly, to run the benchmark for hybridplonk, please run:
```
RUSTFLAGS="-C target_cpu=native" cargo bench --bench hybridplonk_bench
```

One can run the benchmarks for vanilla_sumcheck and improved_sumcheck similarly.
By default, the benchmarks run for num_vars in {14, 16, 18, 20, 22}. One can change the values in the files benches/hyperplonk.rs or benches/hybridplonk.rs.



