# Lean finite certificate for C₃ₐ > 1.21418

`C3a/Main.lean` proves the unconditional theorem:

```lean
theorem c3a_gt_121418 : (60709 / 50000 : ℝ) < MaskedDigit.C3a
```

`MaskedDigit.C3a` is exactly Logan Kleinwaks's definition, retained unchanged
in `RequestProject/GHRConstant.lean`. The proof development has no new axioms or unresolved proof holes.
`Challenge.lean` has one deliberate theorem placeholder for Comparator.

## Reproduce

Install elan, then from this directory:

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

Pinned versions: Lean 4.35.0-rc2 and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Palomar requires at least
Lean 4.35.0-rc2; this pair is also used by Kleinwaks's registered
`sum-difference` template. The manifest pins all dependencies.
The repository's Python verifier remains independent of this proof.

## Finite construction

- Alphabet `M = {0,4,5,8,9,10} ∪ [12,80]`.
- Tilts `x = 8149/10000` and `y = 42571/50000`.
- Depth `N = 10^13`.
- Symmetric nonzero counts `n_d = floor(N x^κ(d) / P₋(x))`.
- Zero count `n₀ = 1917647564302`; total cost `2L = 76435323145630`.
- Finite vector set `V` with letters in `M` and coordinate sum at most `L`.
- Finite type family `W ⊆ V-V`, counted exactly by a multinomial identity.
- Bertrand prime `p > |V-V| + 161`, with `p ≤ 2(|V-V| + 161)`.
- A linear map into `ZMod p` retains more than half of `W`.
- Least-nonnegative representatives, followed by dilation by two, supply a
  finite integer seed for the proved GHR principle.

This replaces the written proof's rescaling to force `max A = p-1`.
The bound `log(4 max A+1) ≤ log|V-V| + log 1296` absorbs the change.
`R = 249293/10000` is retained as source data but is not needed by the final
finite prime selection or inequality. No set of length `10^13`, factorial of
that size, or quotient prime is enumerated.

A common envelope `n_d ≤ (N+1000)x^κ(d)/P₋(x)` handles all floors. Effective
Stirling bounds then reduce the proof to five rational logarithm enclosures.
The final log-cardinality bounds are `log|W| ≥ 32160395000000`,
`log|V+V| ≤ 25272245000000`, and `log|V-V| ≤ 32160396000000`.

## Proof map

| File | Role |
|---|---|
| `CyclicCompression.lean` | Exact fiber counts, collision averaging, Cauchy–Schwarz |
| `IntegerCompression.lean` | Injective box reduction, quotient, integer lifts |
| `VectorWords.lean` | Two tilted upper bounds and finite type words |
| `CertificateData.lean` | Exact alphabet, minimum costs, counts, rational checks |
| `TypeEntropy.lean` | Finite multinomial lower bound with a common envelope |
| `LogNumerics.lean` | Rational Mercator logarithm bounds |
| `FiniteAssembly.lean` | Bertrand prime, lift, and GHR lower bound |
| `Main.lean` | Closed numerical bound for `MaskedDigit.C3a` |

## Trust and attribution

The main axiom list is:

```text
[propext, Classical.choice, Quot.sound]
```

All 17 original native checks now have kernel-checked proofs. Finite
decisions use `decide +kernel`; the support identities use interval
arguments, and exact rational identities feed `norm_num`. No native
computation or compiler trust axiom occurs in the main theorem. The same
three standard axioms suffice for the combinatorial and analytic lemmas.
See `evidence/KERNEL_CHECKS.md` for the per-call attempts and timings; the
native version remains at commit `5bbc2a5eb4d01eb3eb24fb909f819a8d220653f8`.
See `evidence/AXIOMS.txt`; regenerate it with `AxiomAudit.lean`.

All ten files under `RequestProject/` are copied from Logan Kleinwaks's
[masked-digit-sum-difference-bound](https://github.com/kleinwaks/masked-digit-sum-difference-bound),
commit `352ab86effecb7efce415507a8c781ec158b86e0`, under Apache-2.0.
Their mathematical content is unchanged; only module-system visibility
scaffolding was added. Their original
Apache-2.0 notices and `LICENSE-Kleinwaks` are preserved unchanged.
The license is included as `LICENSE-Kleinwaks`.
`VectorWords.lean` adapts his weighted-count and type-word arguments;
its header credits him. New work is by Carson Olafson with GPT-6 Astra assistance.

## Palomar layout

- `Challenge.lean` imports only Mathlib and restates the concrete definitions
  of `MaskedDigit.sumFinset`, `diffFinset`, `GHRAdmissible`, and `C3a`.
- `Solution.lean` proves `PalomarC3a.c3a_gt_121418` from the existing theorem.
- `comparator.json` selects that theorem. `definition_names` is empty:
  all definitions have concrete bodies checked in the theorem's statement
  closure, rather than definition holes that a solution may fill.
- `formalization.yaml` records sources, scope, AI contributions, and review.
- The root `.github/workflows/palomar-preflight.yml` runs the full pinned
  Palomar mechanical workflow on pushes to `palomar` and manual dispatches.
  Its project, Comparator, and metadata paths are repository-relative.

All project Lean files use `module`, public imports, and exposed public
interfaces. `lake build` includes Challenge, Solution, and all RequestProject
modules. The axiom audit also checks the compared theorem. The only intentional
`sorry` is the Challenge theorem; Solution does not import Challenge.

The root Apache-2.0 license covers Carson's material. Reused Kleinwaks files
retain their original Apache-2.0 notices. A passing mechanical preflight is
not a Palomar submission, editorial clearance, registration, or human review.
