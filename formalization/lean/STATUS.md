# Implementation status

Started 2026-10-29 15:43:20 UTC; six-hour deadline 21:43:20 UTC.

The theorem compiles without holes. `lake build` succeeds. Axiom output is in
`evidence/AXIOMS.txt`. Final handoff includes a separate clean-checkout build.

- [x] Read the referee plan and written proof.
- [x] Replay the exact Python numerical verifier.
- [x] Install Lean 4.28.0 and fetch the pinned Mathlib cache.
- [x] Compile the unchanged GHR lower-bound baseline.
- [x] Prove collision averaging and integer lifting.
- [x] Prove type words and both weighted vector bounds.
- [x] Prove finite counts, the Stirling envelope, and logarithm bounds.
- [x] Assemble the unconditional theorem and print its axioms.

The final proof simplifies the plan: dilation replaces rescaling, the prime
is chosen above `|V-V|+161`, and a common Gibbs envelope replaces separate
logarithm checks for every count. These changes are proved, not assumed.
No proof gap was found in the construction used here. No external publication,
push, pull request, or maintainer acceptance is implied by local verification.
