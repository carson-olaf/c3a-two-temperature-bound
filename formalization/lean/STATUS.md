# Implementation status

The finite proof and its kernel-checked numerical refinement are complete.
The native version is preserved at `5bbc2a5eb4d01eb3eb24fb909f819a8d220653f8`.

The theorem compiles without holes. `lake build` succeeds. Axiom output is in
`evidence/AXIOMS.txt`. The main theorem now depends only on `propext`, `Classical.choice`, and
`Quot.sound`. Per-check measurements are in `evidence/KERNEL_CHECKS.md`.
The final handoff includes a separate clean-checkout build.

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
