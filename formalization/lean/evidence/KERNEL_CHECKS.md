# Kernel-checked numerical certificate

All 17 original `native_decide` tactic calls in `C3a/CertificateData.lean`
have been replaced. None are retained. The native version is preserved at
commit `5bbc2a5eb4d01eb3eb24fb909f819a8d220653f8`.
The source previously contained 18 textual occurrences, including one in
the docstring; there were 17 tactic calls.

## Trust base

Before:

```text
[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
```

After, for `C3a.c3a_gt_121418`:

```text
[propext, Classical.choice, Quot.sound]
```

`AxiomAudit.lean` reports the dependencies; its output is in `AXIOMS.txt`.
The theorem statement and Kleinwaks's definition of `MaskedDigit.C3a` are
unchanged. No `sorry`, `admit`, new `axiom`, or native decision is used in
`C3a/`.

## Measured attempts

Measurements were taken on 2026-10-29 with Lean 4.28.0. Each number below
is tactic-elaboration wall time, measured with `IO.monoNanosNow` in a
separate instrumented probe. It excludes import time and the kernel's
subsequent declaration check. The successful complete probe, including
those stages, exited 0 after 52.146 seconds. The production project was
then built separately, without the instrumentation.

| Original call | Direct attempt (s) | Final tactic (s) | Replacement |
|---|---:|---:|---|
| `data.digits_le` | 0.030 | 0.025 | Kernel decision |
| `mask_card` | 0.020 | 0.017 | Kernel decision |
| `sum_support` | 8.924 | 0.297 | Interval witnesses and omega |
| `diff_support` | 9.690 | 0.228 | Interval witnesses, symmetry, and omega |
| `sum_card` | 7.651 | 0.041 | Rewrite proved support; kernel decision |
| `diff_card` | 9.070 | 0.008 | Rewrite proved support; kernel decision |
| `cost_lower` | 1.642 | 1.613 | Kernel decision |
| `cost_witness` | 8.835 | 27.729 | Rewrite proved support; kernel decision |
| `minusPartition_bounds` | 8.991 | 0.028 | Exact rational identity; norm_num |
| `plusPartition_bounds` | 7.714 | 0.004 | Exact rational identity; norm_num |
| `meanCost_bounds` | 9.256 | 0.099 | Exact denominator; kernel decision |
| `count_sum` | 9.249 | 0.259 | Explicit intervals and exact denominator; kernel decision |
| `count_cost` | 9.014 | 0.227 | Explicit intervals and exact denominator; kernel decision |
| `count_positive` | 9.081 | 0.179 | Explicit intervals and exact denominator; kernel decision |
| `count_envelope` | 9.011 | 0.337 | Explicit intervals and exact denominator; kernel decision |
| `budget_exact` | 8.914 | 0.058 | Explicit intervals and exact denominator; kernel decision |
| `budget_bounds` | 8.925 | 0.004 | Rewrite exact budget; norm_num |

Only `data.digits_le`, `mask_card`, and `cost_lower` passed the initial
direct attempt unchanged. The remaining direct attempts failed on deeply
nested support reduction; the rational comparisons also reported stuck
decision instances. The complete direct probe took 164.918 seconds.
An earlier uninstrumented attempt was stopped at 300 seconds and supplies
no usable per-lemma timing.

An intermediate probe proved the support and rational facts, but the
kernel rejected count declarations for deep recursion. Replacing repeated
support enumeration inside the numerical definitions with the proved
explicit intervals removed that failure. These are the same support sets,
not relaxed count or arithmetic statements.

The final replacement uses two additional exact rational identities,
`minusPartition_exact` and `plusPartition_exact`; their tactic times were
0.075 and 0.076 seconds respectively. Kernel reduction proves each rational
sum equal to its displayed fraction. `norm_num` then proves its bounds.
The zero count is also exposed as `zeroCount_exact` for the paper.

## Reproduction

From `formalization/lean/`:

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

`decide +kernel`, `norm_num`, and the structural interval arguments all
produce proofs checked by Lean's kernel. No external arithmetic program
or timing instrumentation is part of the accepted proof.
