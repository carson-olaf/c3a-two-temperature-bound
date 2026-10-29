# C3a two-temperature cyclic-compression certificate

This package contains a Lean 4 finite-certificate proof, the original written
argument, and two exact arithmetic verifiers for

\[
C_{3a}>1.21418.
\]

## Construction

- Inner alphabet: `M = <4,5> intersect [0,80]`.
- Difference tilt: `x = 8149/10000`.
- Sum tilt: `y = 42571/50000`.
- Cyclic quotient rate: `R = 249293/10000`.
- Certified target: `1.21418 = 60709/50000`.

The proof is in `c3a_two_temperature_proof.md` and
`c3a_two_temperature_proof.pdf`.

Prepared by Carson Olafson, August 19, 2026, with extensive assistance from
ChatGPT. The original written argument remains available for external review.
The finite bound now has a Lean formalization; this is not a claim of external
referee acceptance.

## Lean finite certificate

[The formalization](formalization/lean/README.md) proves, with Kleinwaks's
unchanged definition of the GHR constant:

```lean
theorem c3a_gt_121418 : (60709 / 50000 : ℝ) < MaskedDigit.C3a
```

It uses a single finite type at depth `10^13`, with the same alphabet and
`x`, `y` as above. Bertrand's prime is chosen above `|V-V| + 161`; the
formalization uses dilation instead of the written proof's rescaling.
No limit argument is required. The finite checks use `native_decide`;
the axiom report includes `Lean.ofReduceBool` and `Lean.trustCompiler`.

Logan Kleinwaks's GHR principle, type-counting infrastructure, and analytic
bounds are reused under Apache-2.0 with attribution in every reused file.
See the [axiom audit](formalization/lean/evidence/AXIOMS.txt).

The two-temperature theorem builds on an earlier `1.2060` candidate and on
[Logan Kleinwaks's public review](https://github.com/teorth/optimizationproblems/pull/134#issuecomment-5299513691).
Its gapless specialization reproduces the independently announced `1.21356`
baseline; the structured alphabet above improves it to the certified target.
Kleinwaks's separate Lean-formalized controlled-carry result is available in
[PR #146](https://github.com/teorth/optimizationproblems/pull/146).

## Fast verification

Python 3, standard library only:

```bash
python3 verification/verify_c3a_two_temperature_121418.py --emit reconstructed
```

Independent C++20/GMP verifier:

```bash
g++ -O2 -std=c++20 verification/verify_c3a_two_temperature_121418_gmp.cpp \
  -lgmpxx -lgmp -o verify_gmp
./verify_gmp --emit reconstructed_gmp
```

On macOS, install GMP with `brew install gmp`; `reproduce.sh` detects its
Homebrew include and library paths. On Debian or Ubuntu, install
`build-essential` and `libgmp-dev`.

Both implementations reconstruct the mask, sum support, all minimum
difference-witness costs, exact finite Gibbs parameters, and rigorous rational
logarithm bounds from scratch.

Run the complete replay with:

```bash
./reproduce.sh
```

`INDEPENDENT_AUDIT_REPORT.md` records an independent review of the proof's main
logical and computational boundaries in neutral, publication-facing language.

## Trust boundary

The programs machine-check the finite combinatorial reconstruction, numerical
hypotheses, and finite-size correction. They do not formally verify the
human proof of the two-temperature cyclic-quotient theorem, Bertrand's
postulate, the method-of-types inequality, or the GHR finite-set lemma.

## AI-use disclosure

Carson Olafson used ChatGPT extensively to explore constructions, formulate the
two-temperature argument, draft and revise the proof, generate the verification
programs, and audit the resulting package. Carson selected the research
direction, ran and reviewed the verification outputs, and is the human
contributor responsible for the submission. References and externally sourced
claims were checked against the cited sources; independent review of the new
theorem is expressly invited.
