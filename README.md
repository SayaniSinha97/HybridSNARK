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

## Testing

To run all functional tests:

```
cargo test --release
```

### Running a Single Test with Timings

To run a specific test and observe timing information:
```
cargo test --release generic_improved_sumcheck::tests::functionality_test -- --nocapture
```

To enforce single-threaded execution:
```
RAYON_NUM_THREADS=1 cargo test --release generic_improved_sumcheck::tests::functionality_test -- --nocapture
```
---

## Benchmarks

Benchmark files are located in the benches/ directory, with one benchmark per protocol.

To benchmark the improved sumcheck protocol:
```
RUSTFLAGS="-C target_cpu=native" cargo bench --bench improved_sumcheck_bench
```
To benchmark HybridSpartan:
```
RUSTFLAGS="-C target_cpu=native" cargo bench --bench hybridspartan_bench
```
Other benchmarks can be run analogously by specifying the corresponding benchmark file.
