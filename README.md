# HybridPlonk
This repository contains an implementation of HybridPlonk, a SNARK with linear prover and sublogarithmic proof length. We also provide an implementation of HyperPlonk with SamaritanPCS as its underlying PCS, which serves as a baseline for comparison with HybridPlonk. Consequently, the repo contains the first implementation of SamaritanPCS as well.


The src folder contains \
                        (i) samaritan_mlpcs.rs : Implementation of Samaritan Multilinear Polynomial Commitment Scheme (https://eprint.iacr.org/2025/419), \
                        (ii) hyperplonk.rs: Implementation of HyperPlonk with Samaritan PCS as its base PCS, and \
                        (iii) hybridplonk.rs: Implementation of our proposed SNARK, HybridPlonk (which is also instantiated with Samaritan PCS), \
along with a few helper files.

To run the tests, please run:
``
cargo test --release
``

To run the benchmarks, please run:
``
RUSTFLAGS="-C target_cpu=native" cargo test
``
