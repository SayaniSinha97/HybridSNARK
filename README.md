# Improved Sumcheck and HybridSNARKs

This repository implements an **improved multivariate sumcheck protocol** achieving:

- **O(log log n)** communication  
- **O(n)** prover time  
- **O(log n)** verifier time  

Building on this protocol, the repository further provides implementations of:

- **HybridSpartan** — a prover-efficient SNARK with sublogarithmic proof size for R1CS constraints
- **HybridPlonk** — a prover-efficient SNARK with sublogarithmic proof size for Plonkish constraints

Both systems compile existing PIOP constructions with the improved sumcheck protocol and use the **Samaritan multilinear polynomial commitment scheme (PCS)** as the underlying commitment layer.

In updatable SRS settings, **HybridSpartan** and **HybridPlonk** achieve the shortest concrete proof sizes among prover-efficient state-of-the-art SNARKs for R1CS and Plonkish constraints, respectively.

---

## Implemented Protocols

### Sumcheck Protocol

- `generic_improved_sumcheck.rs`  
  Implementation of the proposed improved sumcheck protocol with sublogarithmic communication.

---

### SNARK Constructions

- `hybridspartan.rs`  
  Implementation of **HybridSpartan**, a SNARK for R1CS constraints obtained by compiling MicroSpartan with the improved sumcheck protocol.

- `hyperplonk.rs`  
  Implementation of **HyperPlonk** using the Samaritan PCS.  
  Serves as a baseline for comparison with HybridPlonk.

- `hybridplonk.rs`  
  Implementation of **HybridPlonk**, a SNARK for Plonkish constraints obtained by compiling HyperPlonk with the improved sumcheck protocol along with additional identity checks.

---

### Core Building Blocks

- `samaritan_mlpcs.rs`  
  Implementation of the Samaritan multilinear polynomial commitment scheme used across all protocols.

- `degree_check.rs`  
  Degree checking routines used by the SNARK constructions.

---

## Prerequisites

The artifact assumes a working installation of Rust and Cargo, as well as the standard system build dependencies required by Rust and its dependencies. The artifact has been tested with the Rust toolchain specified by the project configuration.

Users are expected to have these prerequisites installed and available in their system PATH before proceeding.

Verify the Rust and Cargo installations using:
```
rustc --version
cargo --version
```

---

## Quick Guide for Artifact Evaluation

Once the prerequisites are satisfied, please follow the following sequence of commands for artifact evaluation:

```bash
# 1. Clone the repository
git clone https://github.com/SayaniSinha97/HybridSNARK.git

# 2. Enter the repository
cd HybridSNARK

# 3. Build the artifact
cargo build --release

# 4. To run all functional tests over BN254 curve:
RUSTFLAGS="-Awarnings" cargo test --release --lib --features bn254

# 5. To run all functional tests over BLS12-381 curve:
RUSTFLAGS="-Awarnings" cargo test --release --lib --features bls12_381

# 6. Finally run the following script to find the prover and verifier times of
# both the proposed SNARKs (HybridSpartan and HybridPlonk) over BLS12-381 and BN254 curves
# for number_of_gates/number_of_constraints varying in the range {2^{16}, 2^{18}, 2^{20}, 2^{22}, 2^{24}},
# considering single-threaded execution:

sh run_experiments.sh

# Note that the accepted version of the paper reports prover times of HybridSpartan and HybridPlonk
# over BLS12-381 and BN254 curve in Table 4 and Table 5 respectively
# for the number_of_gates/number_of_constraints varying in the range {2^{18}, 2^{20}, 2^{22}, 2^{24}, 2^{26}}.
# The experiments were performed on an Intel(R) Xeon(R) Silver 4214R CPU with 2.40GHz of clock frequency,
# 48 cores, and 128 GB RAM, running Ubuntu 22.04. For fair comparison with state-of-the-art SNARKs,
# the accepted version reports timings for single-threaded execution. 

```

The major characteristics that should be reflected in the timing outcomes irrespective of the platform (for both HybridSpartan and HybridPlonk over BLS12-381 and BN254 curves) are the following:
- prover time is linearly dependent on number_of_gates ($n$). Thus prover time for $n=2^{20}$ is approximately four times than $n=2^{18}$, prover time for $n=2^{22}$ is approximately four times than $n=2^{20}$ and so on.
- verifier time is $O(\log{n})$. Thus verifier time is almost constant over the range $2^{16}, 2^{18}, 2^{20}, 2^{22}, 2^{24}$.

---

## Other Tests

### Running a Single Test with Timings

While the script (run_experiments.sh) reports prover and verifier times for both the SNARKs, the underlying improved_sumcheck protocol and the implementation of samaritan_mlpcs can be tested as following and their individual prover and verifier timings can be observed:

```
V=16 RUSTFLAGS="-Awarnings" cargo test --release --features bn254 generic_improved_sumcheck::tests::functionality_test -- --nocapture

V=16 RUSTFLAGS="-Awarnings" cargo test --release --features bls12_381 samaritan_mlpcs::tests::functionality_test -- --nocapture
```

Here, 'V' is the log(number_of_gates). One can try with varying value of 'V'. Also, one can vary over two different features 'bn254' and 'bls12-381' to see performances over BN254 and BLS12-381 curves.

To enforce single-threaded execution:

```
V=16 RUSTFLAGS="-Awarnings" RAYON_NUM_THREADS=1 cargo test --release --features bls12_381 generic_improved_sumcheck::tests::functionality_test -- --nocapture

V=16 RUSTFLAGS="-Awarnings" RAYON_NUM_THREADS=1 cargo test --release --features bn254 samaritan_mlpcs::tests::functionality_test -- --nocapture
```

---

## Benchmarks

The script (run_experiments.sh) reports the timing for a single execution. However, one can benchmark each of them over multiple executions using standard benchmarking procedure. Benchmark files are located in the benches/ directory, with one benchmark per protocol.

To benchmark the improved sumcheck protocol:

```
RUSTFLAGS="-C target_cpu=native -Awarnings" cargo bench --bench improved_sumcheck_bench
```

To benchmark HybridSpartan and HybridPlonk:

```
RUSTFLAGS="-C target_cpu=native -Awarnings" cargo bench --bench hybridspartan_bench

RUSTFLAGS="-C target_cpu=native -Awarnings" cargo bench --bench hybridplonk_bench
```

---

## Notes on Reproducibility

* The artifact is written in Rust and uses the **2024 Rust edition**.
* The cryptographic and polynomial-arithmetic components use the Arkworks ecosystem.
* Release-mode compilation (`--release`) should be used for performance measurements.
* For single-threaded measurements, set `RAYON_NUM_THREADS=1`.
* For benchmark measurements, `RUSTFLAGS="-C target_cpu=native"` enables optimizations for the evaluator's CPU.
* Benchmark timings are hardware-dependent and should therefore be interpreted relative to the machine on which the artifact is evaluated.
* For accepted version of the paper, single-threaded experiments were performed on an Intel(R) Xeon(R) Silver 4214R CPU with 2.40GHz of clock frequency, 48 cores, and 128 GB RAM, running Ubuntu 22.04.
* Though Table 4 and Table 5 in the accepted version of the paper report prover times of HybridSpartan and HybridPlonk for number_of_gates in the range {$2^{18}, 2^{20}, 2^{22}, 2^{24}, 2^{26}$} over BLS12-381 and BN254 curves, the script (run_experiments.sh) does not include number_of_gates=$2^{26}$, because it might take too long to run; thus making the evaluation process inconvenient. Hence, the script only includes the range {$2^{18}, 2^{20}, 2^{22}, 2^{24}$} for evaluation.
