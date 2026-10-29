module

/-
Copyright (c) 2026 Logan Kleinwaks. All rights reserved.
Released under Apache 2.0 license; see LICENSE-Kleinwaks.
Reused from kleinwaks/masked-digit-sum-difference-bound,
commit 352ab86effecb7efce415507a8c781ec158b86e0.
-/
/- Modified by Carson Olafson with GPT-6 Astra: ported module visibility
for Lean 4.35.0-rc2; mathematical declarations and proofs are unchanged. -/
public import Mathlib
public import RequestProject.GHRDigits

@[expose] public section

/-!
# The Gyarmati--Hennecart--Ruzsa sum-difference constant `C₃ₐ`

This file formalizes Section 1 ("Introduction and the finite-set principle") of the source
article *Improved lower bound for the Gyarmati--Hennecart--Ruzsa sum-difference constant
using masked digits and controlled carries* (`masked_digit_bound.tex`).

It contains:

* the definition of the admissible exponent predicate and of `C₃ₐ` (the displayed definition
  at the beginning of Section 1 of the source);
* the Gyarmati--Hennecart--Ruzsa finite-set principle, equation (1) `eq:GHR` of the source
  (an external result quoted from [GHR2007]);
* the elementary dilation argument of Section 1 of the source leading to equation (2)
  `eq:GHR-dilated`.
-/

open scoped BigOperators Pointwise

namespace MaskedDigit

/-! ## Sumsets and difference sets -/

/-- The sumset `X + Y` of two finite sets of integers, as used in the definition of the
constant `C₃ₐ` in Section 1 of `masked_digit_bound.tex`. -/
def sumFinset (X Y : Finset ℤ) : Finset ℤ := Finset.image₂ (· + ·) X Y

/-- The difference set `X - Y` of two finite sets of integers, as used in the definition of
the constant `C₃ₐ` in Section 1 of `masked_digit_bound.tex`. -/
def diffFinset (X Y : Finset ℤ) : Finset ℤ := Finset.image₂ (· - ·) X Y

/-- The sumset `U + U` of finite sets of nonnegative integers.  In
`masked_digit_bound.tex` the finite-set principle of Gyarmati, Hennecart and Ruzsa is applied
to finite subsets `U ⊆ ℕ₀`, and this is the corresponding sumset. -/
def natSumFinset (U V : Finset ℕ) : Finset ℕ := Finset.image₂ (· + ·) U V

/-- The difference set `U - V` of finite sets of nonnegative integers, viewed inside `ℤ`.
This is the set denoted `U - U` in Section 1 of `masked_digit_bound.tex`. -/
def natDiffFinset (U V : Finset ℕ) : Finset ℤ :=
  Finset.image₂ (fun (a b : ℕ) => (a : ℤ) - (b : ℤ)) U V

/-- `sumFinset` is the pointwise sum of `Finset`s. -/
theorem sumFinset_eq_add (X Y : Finset ℤ) : sumFinset X Y = X + Y := by
  ext x
  simp [sumFinset, Finset.mem_image₂, Finset.mem_add]

/-- `diffFinset` is the pointwise difference of `Finset`s. -/
theorem diffFinset_eq_sub (X Y : Finset ℤ) : diffFinset X Y = X - Y := by
  ext x
  simp [diffFinset, Finset.mem_image₂, Finset.mem_sub]

/-! ## The constant `C₃ₐ` -/

/-- `GHRAdmissible θ` is the property defining the exponents `θ` whose supremum is the
Gyarmati--Hennecart--Ruzsa constant `C₃ₐ`.  It is the displayed property at the start of
Section 1 of `masked_digit_bound.tex`: for every `K > 1` there is `c(K) > 0` and there are
pairs of finite sets `X, Y ⊂ ℤ`, with `|X|` arbitrarily large, such that
`|X + Y| ≤ K |X|` and `|X - Y| ≥ c(K) |X + Y| ^ θ`.

The pairs of sets are required to be nonempty, as is implicit in the source.  Without that
requirement the property would be vacuous: taking `Y = ∅` makes `X + Y` and `X - Y` empty,
so that both displayed inequalities read `0 ≤ 0` and *every* exponent `θ > 0` would be
admissible.  (See `GHRAdmissible.le_three_halves` and `bddAbove_GHRAdmissible`: with the
nonemptiness requirement the set of admissible exponents is bounded above by `3/2`, so the
supremum `C₃ₐ` is a genuine real number.) -/
def GHRAdmissible (theta : ℝ) : Prop :=
  ∀ K : ℝ, 1 < K → ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ X Y : Finset ℤ,
    X.Nonempty ∧ Y.Nonempty ∧
    N ≤ X.card ∧
    ((sumFinset X Y).card : ℝ) ≤ K * (X.card : ℝ) ∧
    c * ((sumFinset X Y).card : ℝ) ^ theta ≤ ((diffFinset X Y).card : ℝ)

/-- The Gyarmati--Hennecart--Ruzsa sum-difference constant `C₃ₐ`, defined in Section 1 of
`masked_digit_bound.tex` as the supremum of the admissible exponents `θ`. -/
noncomputable def C3a : ℝ := sSup {theta : ℝ | GHRAdmissible theta}

/-! ## The supremum defining `C₃ₐ` is a genuine real number

Section 1 of `masked_digit_bound.tex` defines `C₃ₐ` as a supremum of exponents without
comment.  The three results below justify that definition: the exponent `θ = 1` is
admissible, every admissible exponent is at most `3/2`, and consequently
`1 ≤ C₃ₐ ≤ 3/2`. -/

/-- `|X| ≤ |X + Y|` for nonempty `Y`: translating `X` by a single element of `Y`. -/
theorem card_le_card_sumFinset_left {X Y : Finset ℤ} (hY : Y.Nonempty) :
    X.card ≤ (sumFinset X Y).card := by
  obtain ⟨y, hy⟩ := hY
  calc X.card = (X.image (· + y)).card :=
        (Finset.card_image_of_injective _ (add_left_injective y)).symm
    _ ≤ _ := Finset.card_le_card (by
        intro z hz
        simp only [Finset.mem_image] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        exact Finset.mem_image₂_of_mem hx hy)

/-- `|Y| ≤ |X + Y|` for nonempty `X`: translating `Y` by a single element of `X`. -/
theorem card_le_card_sumFinset_right {X Y : Finset ℤ} (hX : X.Nonempty) :
    Y.card ≤ (sumFinset X Y).card := by
  obtain ⟨x, hx⟩ := hX
  calc Y.card = (Y.image (x + ·)).card :=
        (Finset.card_image_of_injective _ (add_right_injective x)).symm
    _ ≤ _ := Finset.card_le_card (by
        intro z hz
        simp only [Finset.mem_image] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        exact Finset.mem_image₂_of_mem hx hy)

/-- The trivial bound `|X - Y| ≤ |X| |Y|`. -/
theorem card_diffFinset_le_mul (X Y : Finset ℤ) :
    (diffFinset X Y).card ≤ X.card * Y.card :=
  Finset.card_image₂_le _ _ _

/-- The sumset of two nonempty finite sets is nonempty. -/
theorem sumFinset_nonempty {X Y : Finset ℤ} (hX : X.Nonempty) (hY : Y.Nonempty) :
    (sumFinset X Y).Nonempty := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  exact ⟨x + y, Finset.mem_image₂_of_mem hx hy⟩

/-- **The exponent `θ = 1` is admissible.**  Taking `Y = {0}` and `X` an arbitrarily long
interval of integers gives `|X + Y| = |X - Y| = |X|`, so the defining property of Section 1
of `masked_digit_bound.tex` holds with `c(K) = 1`. -/
theorem GHRAdmissible_one : GHRAdmissible 1 := by
  intro K hK
  refine ⟨1, one_pos, fun N => ?_⟩
  set X : Finset ℤ := (Finset.range (N + 1)).image (fun n : ℕ => (n : ℤ)) with hXdef
  have hXcard : X.card = N + 1 := by
    rw [hXdef, Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h),
      Finset.card_range]
  have hXne : X.Nonempty := Finset.card_pos.1 (by omega)
  have hsum : sumFinset X {0} = X := by
    ext z
    simp [sumFinset]
  have hdiff : diffFinset X {0} = X := by
    ext z
    simp [diffFinset]
  refine ⟨X, {0}, hXne, ⟨0, Finset.mem_singleton_self 0⟩, by omega, ?_, ?_⟩
  · rw [hsum]
    nlinarith [Nat.cast_nonneg (α := ℝ) X.card]
  · rw [hsum, hdiff, Real.rpow_one, one_mul]

/-- **The Plünnecke--Ruzsa bound `|X - Y|² ≤ |X + Y|³`** for nonempty finite sets of
integers.  It combines Ruzsa's triangle inequality `|X - Y| |Y| ≤ |X + Y| |Y + Y|` with the
Plünnecke--Ruzsa inequality `|Y + Y| |X| ≤ |X + Y|²` and the trivial bound
`|X - Y| ≤ |X| |Y|`.  It is the quantitative reason why the supremum defining `C₃ₐ` in
Section 1 of `masked_digit_bound.tex` is finite. -/
theorem card_diffFinset_sq_le_card_sumFinset_cube {X Y : Finset ℤ} (hX : X.Nonempty)
    (hY : Y.Nonempty) : (diffFinset X Y).card ^ 2 ≤ (sumFinset X Y).card ^ 3 := by
  have hsum : sumFinset X Y = X + Y := rfl
  have hdif : diffFinset X Y = X - Y := rfl
  rw [hsum, hdif]
  have hR : (X - Y).card * Y.card ≤ (X + Y).card * (Y + Y).card :=
    Finset.ruzsa_triangle_inequality_sub_add_add X Y Y
  have hP : ((Y + Y).card : ℚ≥0)
      ≤ (((X + Y).card : ℚ≥0) / (X.card : ℚ≥0)) ^ 2 * (X.card : ℚ≥0) := by
    have := Finset.pluennecke_ruzsa_inequality_nsmul_add hX Y 2
    rwa [two_nsmul] at this
  have hxpos : (0 : ℚ≥0) < (X.card : ℚ≥0) := by exact_mod_cast Finset.card_pos.2 hX
  have hP' : (Y + Y).card * X.card ≤ (X + Y).card ^ 2 := by
    have h : ((Y + Y).card : ℚ≥0) * (X.card : ℚ≥0) ≤ ((X + Y).card : ℚ≥0) ^ 2 := by
      calc ((Y + Y).card : ℚ≥0) * (X.card : ℚ≥0)
          ≤ ((((X + Y).card : ℚ≥0) / (X.card : ℚ≥0)) ^ 2 * (X.card : ℚ≥0)) * (X.card : ℚ≥0) :=
            mul_le_mul_of_nonneg_right hP (by positivity)
        _ = ((X + Y).card : ℚ≥0) ^ 2 := by field_simp
    exact_mod_cast h
  have hd : (X - Y).card ≤ X.card * Y.card := Finset.card_sub_le
  nlinarith [hR, hP', hd, Finset.card_pos.2 hY, Finset.card_pos.2 hX]

/-- The real form of `card_diffFinset_sq_le_card_sumFinset_cube`: `|X - Y| ≤ |X + Y| ^ (3/2)`
for nonempty finite sets of integers. -/
theorem card_diffFinset_le_rpow {X Y : Finset ℤ} (hX : X.Nonempty) (hY : Y.Nonempty) :
    ((diffFinset X Y).card : ℝ) ≤ ((sumFinset X Y).card : ℝ) ^ (3 / 2 : ℝ) := by
  set d : ℝ := ((diffFinset X Y).card : ℝ) with hdd
  set s : ℝ := ((sumFinset X Y).card : ℝ) with hss
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have hsq : d ^ (2 : ℕ) ≤ s ^ (3 : ℕ) := by
    rw [hdd, hss]
    exact_mod_cast card_diffFinset_sq_le_card_sumFinset_cube hX hY
  have hdrw : (d ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) = d := by
    rw [← Real.rpow_natCast d 2, ← Real.rpow_mul hd0]
    norm_num
  have hsrw : (s ^ (3 : ℕ)) ^ ((1 : ℝ) / 2) = s ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast s 3, ← Real.rpow_mul hs0]
    norm_num
  calc d = (d ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) := hdrw.symm
    _ ≤ (s ^ (3 : ℕ)) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hsq (by norm_num)
    _ = s ^ (3 / 2 : ℝ) := hsrw

/-- **Every admissible exponent is at most `3/2`.**  Along an admissible family the sumset
cardinality `|X + Y| ≥ |X|` is arbitrarily large, while `c |X + Y| ^ θ ≤ |X - Y|` and
`|X - Y| ≤ |X + Y| ^ (3/2)`; so `θ ≤ 3/2`. -/
theorem GHRAdmissible.le_three_halves {theta : ℝ} (h : GHRAdmissible theta) : theta ≤ 3 / 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hc, hfam⟩ := h 2 one_lt_two
  set t : ℝ := theta - 3 / 2 with ht
  have ht0 : 0 < t := by simp only [ht]; linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / c < (N : ℝ) ^ t := by
    set a : ℝ := (1 / c) ^ (1 / t) with ha
    have ha0 : 0 ≤ a := Real.rpow_nonneg (by positivity) _
    refine ⟨⌈a⌉₊ + 1, ?_⟩
    have hlt : a < ((⌈a⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact lt_of_le_of_lt (Nat.le_ceil a) (by linarith)
    have h1 : a ^ t = 1 / c := by
      rw [ha, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / c), one_div t,
        inv_mul_cancel₀ (ne_of_gt ht0), Real.rpow_one]
    calc 1 / c = a ^ t := h1.symm
      _ < _ := Real.rpow_lt_rpow ha0 hlt ht0
  obtain ⟨X, Y, hX, hY, hcard, _, hdiff⟩ := hfam N
  set s : ℝ := ((sumFinset X Y).card : ℝ) with hs
  have hspos : 0 < s := by
    have := Finset.card_pos.2 (sumFinset_nonempty hX hY)
    simpa [hs] using (Nat.cast_pos (α := ℝ)).2 this
  have hXs : (X.card : ℝ) ≤ s := by
    rw [hs]
    exact_mod_cast card_le_card_sumFinset_left (X := X) hY
  have hNs : (N : ℝ) ≤ s := le_trans (by exact_mod_cast hcard) hXs
  have hsplit : s ^ theta = s ^ t * s ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hspos]
    congr 1
    simp only [ht]
    ring
  have hkey : c * (s ^ t * s ^ (3 / 2 : ℝ)) ≤ s ^ (3 / 2 : ℝ) := by
    rw [← hsplit]
    exact le_trans hdiff (card_diffFinset_le_rpow hX hY)
  have hpow : 0 < s ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hspos _
  have hst : c * s ^ t ≤ 1 := by nlinarith [hkey]
  have hmono : (N : ℝ) ^ t ≤ s ^ t :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hNs (le_of_lt ht0)
  have hlt2 : 1 / c < s ^ t := lt_of_lt_of_le hN hmono
  have := (div_lt_iff₀ hc).1 hlt2
  linarith

/-- The set of admissible exponents of Section 1 of `masked_digit_bound.tex` is bounded
above, so the supremum defining `C₃ₐ` is a genuine real number. -/
theorem bddAbove_GHRAdmissible : BddAbove {theta : ℝ | GHRAdmissible theta} :=
  ⟨3 / 2, fun _ h => GHRAdmissible.le_three_halves h⟩

/-- `C₃ₐ ≤ 3/2`, the elementary upper bound coming from `|X - Y|² ≤ |X + Y|³`. -/
theorem C3a_le_three_halves : C3a ≤ 3 / 2 :=
  csSup_le ⟨1, GHRAdmissible_one⟩ (fun _ h => GHRAdmissible.le_three_halves h)

/-- `C₃ₐ ≥ 1`.  This is the trivial lower bound recorded in Section 1 of
`masked_digit_bound.tex`: the exponent `θ = 1` is admissible. -/
theorem one_le_C3a : 1 ≤ C3a :=
  le_csSup bddAbove_GHRAdmissible GHRAdmissible_one

/-! ## The finite-set principle -/

/-- **The Gyarmati--Hennecart--Ruzsa finite-set principle**, equation (1) (`eq:GHR`) of
`masked_digit_bound.tex`, quoted there from [GHR2007, Lemma in Section 2]: if `U ⊆ ℕ₀` is
finite, contains zero, and satisfies the *strict* inequality `|U - U| < 2 max U + 1`, then
`C₃ₐ ≥ 1 + log(|U - U| / |U + U|) / log(2 max U + 1)`.

The source quotes this statement from the literature; it is proved here from first
principles, following the proof of the Lemma of Section 2 of [GHR2007].  The construction
(the base-`q` digit strings with digits in `U`, together with the diluting interval
`[1, L]`) is carried out in `RequestProject.GHRDigits`.

The hypotheses `0 ∈ U` and `|U - U| < 2 max U + 1` are part of the statement quoted by the
source and are kept here, but the proof given turns out not to need either of them: the
construction only uses `U ⊆ {0, …, max U}`, and the strict inequality (used in [GHR2007]
to absorb an error term `-d^k`) is avoided by bounding `|A - B|` below directly through the
disjointness of the translates `L + i q^k + (B - B)`. -/
theorem ghr_finite_set_lower_bound (U : Finset ℕ) (h0 : 0 ∈ U) (hne : U.Nonempty)
    (hstrict : ((natDiffFinset U U).card : ℤ) < 2 * (U.max' hne : ℤ) + 1) :
    1 + Real.log (((natDiffFinset U U).card : ℝ) / ((natSumFinset U U).card : ℝ)) /
        Real.log (2 * (U.max' hne : ℝ) + 1) ≤ C3a := by
  classical
  set a : ℕ := U.max' hne with hadef
  set Uz : Finset ℤ := U.image (fun n : ℕ => (n : ℤ)) with hUzdef
  have hUzne : Uz.Nonempty := hne.image _
  have hUzmem : ∀ u ∈ Uz, 0 ≤ u ∧ u ≤ (a : ℤ) := by
    intro u hu
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hu
    exact ⟨Int.natCast_nonneg n, by exact_mod_cast U.le_max' n hn⟩
  have hdiffeq : natDiffFinset U U = Uz - Uz := by
    ext x
    simp only [natDiffFinset, Finset.mem_image₂, Finset.mem_sub, hUzdef, Finset.mem_image]
    constructor
    · rintro ⟨n, hn, p, hp, rfl⟩
      exact ⟨(n : ℤ), ⟨n, hn, rfl⟩, (p : ℤ), ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨n, hn, rfl⟩, z, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨n, hn, p, hp, rfl⟩
  have hsumeq : Uz + Uz = (natSumFinset U U).image (fun n : ℕ => (n : ℤ)) := by
    ext x
    simp only [natSumFinset, Finset.mem_image₂, Finset.mem_add, hUzdef, Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨n, hn, rfl⟩, z, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨n + p, ⟨n, hn, p, hp, rfl⟩, by push_cast; ring⟩
    · rintro ⟨w, ⟨n, hn, p, hp, rfl⟩, rfl⟩
      exact ⟨(n : ℤ), ⟨n, hn, rfl⟩, (p : ℤ), ⟨p, hp, rfl⟩, by push_cast; ring⟩
  have hsumcard : (Uz + Uz).card = (natSumFinset U U).card := by
    rw [hsumeq, Finset.card_image_of_injective _ (fun m n h => by exact_mod_cast h)]
  rcases le_or_gt (1 + Real.log (((natDiffFinset U U).card : ℝ) /
      ((natSumFinset U U).card : ℝ)) / Real.log (2 * (a : ℝ) + 1)) 1 with hcase | hcase
  · exact le_trans hcase one_le_C3a
  · have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · exfalso
        rw [h] at hcase
        norm_num at hcase
      · exact h
    have hth : 1 + Real.log (((natDiffFinset U U).card : ℝ) /
        ((natSumFinset U U).card : ℝ)) / Real.log (2 * (a : ℝ) + 1) =
        1 + Real.log (((Uz - Uz).card : ℝ) / ((Uz + Uz).card : ℝ)) /
          Real.log (2 * (a : ℝ) + 1) := by
      rw [hdiffeq, hsumcard]
    have hadm : GHRAdmissible (1 + Real.log (((natDiffFinset U U).card : ℝ) /
        ((natSumFinset U U).card : ℝ)) / Real.log (2 * (a : ℝ) + 1)) := by
      intro K hK
      have hK1 : (0 : ℝ) < K - 1 := by linarith
      have hR : (0 : ℝ) < 3 * K / (2 * (K - 1)) := div_pos (by linarith) (by linarith)
      have hRp : (0 : ℝ) < (3 * K / (2 * (K - 1))) ^
          (1 + Real.log (((natDiffFinset U U).card : ℝ) /
            ((natSumFinset U U).card : ℝ)) / Real.log (2 * (a : ℝ) + 1)) :=
        Real.rpow_pos_of_pos hR _
      refine ⟨1 / (2 * (3 * K / (2 * (K - 1))) ^
        (1 + Real.log (((natDiffFinset U U).card : ℝ) /
          ((natSumFinset U U).card : ℝ)) / Real.log (2 * (a : ℝ) + 1))),
        div_pos one_pos (by linarith), fun N => ?_⟩
      obtain ⟨A, B, hA, hB, hNA, hsum', hdiff'⟩ :=
        MaskedDigit.Digits.exists_ghr_pair Uz a ha hUzne hUzmem _ (by linarith) hth K hK N
      exact ⟨A, B, hA, hB, hNA, by rwa [sumFinset_eq_add],
        by rwa [sumFinset_eq_add, diffFinset_eq_sub]⟩
    exact le_csSup bddAbove_GHRAdmissible hadm

/-! ## Dilation -/

section Dilation

variable (U : Finset ℕ)

/-- Dilation by `2` preserves the cardinality of the sumset: `|2U + 2U| = |U + U|`.
This is one of the three displayed identities of the dilation paragraph of Section 1 of
`masked_digit_bound.tex`. -/
theorem natSumFinset_dilation :
    (natSumFinset (U.image (fun a => 2 * a)) (U.image (fun a => 2 * a))).card =
      (natSumFinset U U).card := by
  have himg : natSumFinset (U.image (fun a => 2 * a)) (U.image (fun a => 2 * a)) =
      (natSumFinset U U).image (fun a => 2 * a) := by
    ext n
    simp only [natSumFinset, Finset.mem_image₂, Finset.mem_image]
    constructor
    · rintro ⟨a, ⟨a', ha', rfl⟩, b, ⟨b', hb', rfl⟩, rfl⟩
      exact ⟨a' + b', ⟨a', ha', b', hb', rfl⟩, by ring⟩
    · rintro ⟨m, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨2 * a, ⟨a, ha, rfl⟩, 2 * b, ⟨b, hb, rfl⟩, by ring⟩
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by omega)]

/-- Dilation by `2` preserves the cardinality of the difference set: `|2U - 2U| = |U - U|`.
This is one of the three displayed identities of the dilation paragraph of Section 1 of
`masked_digit_bound.tex`. -/
theorem natDiffFinset_dilation :
    (natDiffFinset (U.image (fun a => 2 * a)) (U.image (fun a => 2 * a))).card =
      (natDiffFinset U U).card := by
  have himg : natDiffFinset (U.image (fun a => 2 * a)) (U.image (fun a => 2 * a)) =
      (natDiffFinset U U).image (fun a => 2 * a) := by
    ext n
    simp only [natDiffFinset, Finset.mem_image₂, Finset.mem_image]
    constructor
    · rintro ⟨a, ⟨a', ha', rfl⟩, b, ⟨b', hb', rfl⟩, rfl⟩
      exact ⟨(a' : ℤ) - b', ⟨a', ha', b', hb', rfl⟩, by push_cast; ring⟩
    · rintro ⟨m, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨2 * a, ⟨a, ha, rfl⟩, 2 * b, ⟨b, hb, rfl⟩, by push_cast; ring⟩
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by omega)]

/-- Dilation by `2` doubles the maximum: `max (2U) = 2 max U`.  This is the third displayed
identity of the dilation paragraph of Section 1 of `masked_digit_bound.tex`. -/
theorem max'_dilation (hne : U.Nonempty) :
    (U.image (fun a => 2 * a)).max' (hne.image _) = 2 * U.max' hne := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact Nat.mul_le_mul_left 2 (U.le_max' a ha)
  · exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (U.max'_mem hne))

/-- The elementary containment `U - U ⊆ [-max U, max U]`, giving the *non-strict* bound
`|U - U| ≤ 2 max U + 1` recorded in the second paragraph of Section 1 of
`masked_digit_bound.tex`. -/
theorem natDiffFinset_card_le (hne : U.Nonempty) :
    ((natDiffFinset U U).card : ℤ) ≤ 2 * (U.max' hne : ℤ) + 1 := by
  have hsub : natDiffFinset U U ⊆ Finset.Icc (-(U.max' hne : ℤ)) (U.max' hne : ℤ) := by
    intro z hz
    simp only [natDiffFinset, Finset.mem_image₂] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    have ha' : (a : ℤ) ≤ (U.max' hne : ℤ) := by exact_mod_cast U.le_max' a ha
    have hb' : (b : ℤ) ≤ (U.max' hne : ℤ) := by exact_mod_cast U.le_max' b hb
    have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
    have hb0 : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
    simp only [Finset.mem_Icc]
    constructor <;> omega
  have := Finset.card_le_card hsub
  rw [Int.card_Icc] at this
  have h2 : ((Finset.Icc (-(U.max' hne : ℤ)) (U.max' hne : ℤ)).card : ℤ)
      = 2 * (U.max' hne : ℤ) + 1 := by
    rw [Int.card_Icc]
    omega
  omega

/-- **Dilation supplies strictness.**  If `U ⊆ ℕ₀` is nonempty with `max U > 0`, then the
dilated set `V = 2U` satisfies the strict hypothesis `|V - V| < 2 max V + 1` of the
finite-set principle (1) of `masked_digit_bound.tex`, whether or not `U` does. -/
theorem dilation_two_supplies_strictness (hne : U.Nonempty) (hmax : 0 < U.max' hne) :
    ((natDiffFinset (U.image (fun a => 2 * a)) (U.image (fun a => 2 * a))).card : ℤ) <
      2 * (((U.image (fun a => 2 * a)).max' (hne.image _) : ℕ) : ℤ) + 1 := by
  rw [natDiffFinset_dilation, max'_dilation U hne]
  have h1 := natDiffFinset_card_le U hne
  have : (0 : ℤ) < (U.max' hne : ℤ) := by exact_mod_cast hmax
  push_cast
  omega

end Dilation

/-- **The dilated finite-set principle**, equation (2) (`eq:GHR-dilated`) of
`masked_digit_bound.tex`.  For every finite `U ⊆ ℕ₀` containing zero with `max U > 0`,
`C₃ₐ ≥ 1 + log(|U - U| / |U + U|) / log(4 max U + 1)`.

Unlike the finite-set principle (1) itself, this version has no strictness hypothesis: the
strictness is supplied by passing to `V = 2U`, which has the same sumset and difference-set
cardinalities but twice the maximum. -/
theorem ghr_dilated_lower_bound (U : Finset ℕ) (h0 : 0 ∈ U) (hne : U.Nonempty)
    (hmax : 0 < U.max' hne) :
    1 + Real.log (((natDiffFinset U U).card : ℝ) / ((natSumFinset U U).card : ℝ)) /
        Real.log (4 * (U.max' hne : ℝ) + 1) ≤ C3a := by
  have hV := ghr_finite_set_lower_bound (U.image (fun a => 2 * a))
    (by rw [Finset.mem_image]; exact ⟨0, h0, rfl⟩) (hne.image _)
    (dilation_two_supplies_strictness U hne hmax)
  rw [natDiffFinset_dilation, natSumFinset_dilation, max'_dilation U hne] at hV
  have hcast : ((2 * U.max' hne : ℕ) : ℝ) = 2 * (U.max' hne : ℝ) := by push_cast; ring
  rw [hcast] at hV
  have : (2 : ℝ) * (2 * (U.max' hne : ℝ)) + 1 = 4 * (U.max' hne : ℝ) + 1 := by ring
  rwa [this] at hV

/-- A consistency check on the dilated finite-set principle (2) of
`masked_digit_bound.tex`: applied to the two-element set `U = {0, 1}`, for which
`|U - U| = |U + U| = 3`, it returns exactly the trivial bound `C₃ₐ ≥ 1` proved
unconditionally in `one_le_C3a`. -/
theorem ghr_dilated_two_element : 1 ≤ C3a := by
  have h0 : (0 : ℕ) ∈ ({0, 1} : Finset ℕ) := by decide
  have hne : ({0, 1} : Finset ℕ).Nonempty := ⟨0, h0⟩
  have hpos : 0 < ({0, 1} : Finset ℕ).max' hne :=
    lt_of_lt_of_le one_pos (Finset.le_max' _ 1 (by decide))
  have h := ghr_dilated_lower_bound ({0, 1} : Finset ℕ) h0 hne hpos
  have hd : (natDiffFinset ({0, 1} : Finset ℕ) ({0, 1} : Finset ℕ)).card = 3 := by decide
  have hs : (natSumFinset ({0, 1} : Finset ℕ) ({0, 1} : Finset ℕ)).card = 3 := by decide
  rw [hd, hs] at h
  norm_num at h
  exact h

end MaskedDigit
