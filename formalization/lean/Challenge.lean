module

public import Mathlib

@[expose] public section

/-!
# A strict lower bound for the GHR sum-difference constant

For every real doubling bound `K > 1`, admissible exponents describe pairs of
nonempty finite integer sets with arbitrarily large first set, small sumset,
and a power-law lower bound on the difference set. The constant `C₃ₐ` is the
supremum of these exponents. We prove `C₃ₐ > 60709 / 50000 = 1.21418`.

These concrete definitions reproduce Logan Kleinwaks's Apache-2.0 definitions
from `masked-digit-sum-difference-bound`, commit
`352ab86effecb7efce415507a8c781ec158b86e0`, `RequestProject/GHRConstant.lean`.
Copyright (c) 2026 Logan Kleinwaks. See `LICENSE-Kleinwaks`.
The nonempty-set conditions and every quantifier are retained. No definition
is left for the Solution to choose.

The accompanying paper's sections 6–7 describe the finite proof. The general
limiting theorem in that paper is outside this comparison. The audience is
additive combinatorics, specifically extremal sumset/difference-set bounds.
-/

namespace MaskedDigit

/-- All sums of one element from each finite integer set. -/
def sumFinset (X Y : Finset ℤ) : Finset ℤ := Finset.image₂ (· + ·) X Y

/-- All differences of one element from each finite integer set. -/
def diffFinset (X Y : Finset ℤ) : Finset ℤ := Finset.image₂ (· - ·) X Y

/-- An exponent is admissible when every `K > 1` admits a positive constant
`c`, uniform over arbitrarily large nonempty finite integer sets `X`, with a
nonempty partner `Y`, such that `|X+Y| ≤ K|X|` and `c|X+Y|^theta ≤ |X-Y|`.
The constant may depend on `K` and the exponent, but not on the size bound. -/
def GHRAdmissible (theta : ℝ) : Prop :=
  ∀ K : ℝ, 1 < K → ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ X Y : Finset ℤ,
    X.Nonempty ∧ Y.Nonempty ∧
    N ≤ X.card ∧
    ((sumFinset X Y).card : ℝ) ≤ K * (X.card : ℝ) ∧
    c * ((sumFinset X Y).card : ℝ) ^ theta ≤ ((diffFinset X Y).card : ℝ)

/-- The supremum of the admissible real exponents. The proof development
also proves the admissible set is nonempty and bounded above. -/
noncomputable def C3a : ℝ := sSup {theta : ℝ | GHRAdmissible theta}

end MaskedDigit

namespace PalomarC3a

/-- The strict bound `C₃ₐ > 1.21418`, with no extra hypotheses. -/
theorem c3a_gt_121418 : (60709 / 50000 : ℝ) < MaskedDigit.C3a := by
  sorry

end PalomarC3a
