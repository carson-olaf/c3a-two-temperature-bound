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

@[expose] public section

/-!
# Certified rational bounds for logarithms

`masked_digit_bound.tex` compares logarithms of explicit rational numbers with exact rational
arithmetic (Section 4.3 of the source uses a rational-arithmetic script for the final
exponent comparison, and Section 5 uses directed MPFR enclosures).  This file provides the
Lean counterpart of that rational logarithm checker: two-sided enclosures for `log (1 - x)`
obtained from the Mercator series with an explicit tail bound, from which the numerical
comparisons of the source are derived by exact rational arithmetic.
-/

namespace MaskedDigit

/-- Lower Mercator enclosure: `log (1 - x) ≥ -∑_{i<n} x^{i+1}/(i+1) - |x|^{n+1}/(1 - |x|)`
for `|x| < 1`.  This is the rigorous version of the truncated logarithm series used by the
rational checker of `masked_digit_bound.tex`. -/
theorem log_one_sub_lower {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - |x| ^ (n + 1) / (1 - |x|)
      ≤ Real.log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_le] at h
  linarith [h.1]

/-- Upper Mercator enclosure: `log (1 - x) ≤ -∑_{i<n} x^{i+1}/(i+1) + |x|^{n+1}/(1 - |x|)`
for `|x| < 1`. -/
theorem log_one_sub_upper {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    Real.log (1 - x)
      ≤ -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + |x| ^ (n + 1) / (1 - |x|) := by
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_le] at h
  linarith [h.2]

set_option maxRecDepth 8000

/-- A certified lower bound for `log (582117820 / 2^29)`, one of the three enclosures needed
for the exponent comparison of Section 4.3 of `masked_digit_bound.tex`. -/
theorem log_t1_lower : (0.08091518883 : ℝ) ≤ Real.log (145529455 / 134217728) := by
  have hx : |(-11311727 / 134217728 : ℝ)| < 1 := by
    rw [abs_lt]; norm_num
  have h := log_one_sub_lower hx 25
  have habs : |(-11311727 / 134217728 : ℝ)| = 11311727 / 134217728 := by
    rw [abs_of_nonpos] <;> norm_num
  rw [habs] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A certified upper bound for `log (79428331 / 2^26)`. -/
theorem log_t2_upper : Real.log (79428331 / 67108864) ≤ (0.16853898162 : ℝ) := by
  have hx : |(-12319467 / 67108864 : ℝ)| < 1 := by
    rw [abs_lt]; norm_num
  have h := log_one_sub_upper hx 25
  have habs : |(-12319467 / 67108864 : ℝ)| = 12319467 / 67108864 := by
    rw [abs_of_nonpos] <;> norm_num
  rw [habs] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A certified upper bound for `log (27022 / 2^15)`. -/
theorem log_t3_upper : Real.log (13511 / 16384) ≤ (-0.19280108037 : ℝ) := by
  have hx : |(2873 / 16384 : ℝ)| < 1 := by
    rw [abs_lt]; norm_num
  have h := log_one_sub_upper hx 25
  have habs : |(2873 / 16384 : ℝ)| = 2873 / 16384 := by
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2873 / 16384)]
  rw [habs] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The decomposition `log 582117820 = 29 log 2 + log (582117820 / 2^29)`. -/
theorem log_582117820_eq :
    Real.log 582117820 = 29 * Real.log 2 + Real.log (145529455 / 134217728) := by
  have hval : (582117820 : ℝ) = 2 ^ 29 * (145529455 / 134217728) := by norm_num
  rw [hval, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The decomposition `log 79428331 = 26 log 2 + log (79428331 / 2^26)`. -/
theorem log_79428331_eq :
    Real.log 79428331 = 26 * Real.log 2 + Real.log (79428331 / 67108864) := by
  have hval : (79428331 : ℝ) = 2 ^ 26 * (79428331 / 67108864) := by norm_num
  rw [hval, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The decomposition `log 27022 = 15 log 2 + log (27022 / 2^15)`. -/
theorem log_27022_eq : Real.log 27022 = 15 * Real.log 2 + Real.log (13511 / 16384) := by
  have hval : (27022 : ℝ) = 2 ^ 15 * (13511 / 16384) := by norm_num
  rw [hval, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- `log 27022 > 0`. -/
theorem log_27022_pos : 0 < Real.log 27022 := Real.log_pos (by norm_num)

/-- **The exponent comparison of Section 4.3 of `masked_digit_bound.tex`, in product form:**
`0.19519192 · log 27022 < log(582117820 / 79428331)`.  It is proved by exact rational
arithmetic from the three Mercator enclosures above and the standard enclosure of `log 2`. -/
theorem exponent_comparison :
    (0.19519192 : ℝ) * Real.log 27022 < Real.log ((582117820 : ℝ) / 79428331) := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hdiv : Real.log ((582117820 : ℝ) / 79428331)
      = Real.log 582117820 - Real.log 79428331 :=
    Real.log_div (by norm_num) (by norm_num)
  rw [hdiv, log_582117820_eq, log_79428331_eq, log_27022_eq]
  have h1 := log_t1_lower
  have h2' := log_t2_upper
  have h3 := log_t3_upper
  nlinarith [h1, h2', h3, h2]

/-! ## A Taylor enclosure for the exponential -/

/-- A five-term Taylor enclosure of `e^{-t}` for `0 ≤ t ≤ 1`, used to convert the fugacity
`x₀ = e^{-λ₀}` of Section 3 of `masked_digit_bound.tex` into certified rational bounds. -/
theorem exp_neg_enclosure {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |Real.exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24)| ≤ t ^ 5 / 100 := by
  have habs : |(-t)| ≤ 1 := by rw [abs_neg, abs_of_nonneg ht0]; exact ht1
  have h := Real.exp_bound habs (n := 5) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 5, (-t) ^ m / ((Nat.factorial m : ℕ) : ℝ)
      = 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  have habs5 : |(-t)| ^ 5 * (((Nat.succ 5 : ℕ) : ℝ) / (((Nat.factorial 5 : ℕ) : ℝ) * (5 : ℕ)))
      = t ^ 5 / 100 := by
    rw [abs_neg, abs_of_nonneg ht0]
    norm_num [Nat.factorial]
    ring
  rw [hsum] at h
  calc |Real.exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24)|
      ≤ |(-t)| ^ 5 * (((Nat.succ 5 : ℕ) : ℝ) / (((Nat.factorial 5 : ℕ) : ℝ) * (5 : ℕ))) := h
    _ = t ^ 5 / 100 := habs5

/-! ## The carry-free exponent comparison of Section 3 -/

/-- A certified upper bound for `log (34065 / 2^15)`, needed for the carry-free comparison of
Section 3 of `masked_digit_bound.tex`. -/
theorem log_t4_upper : Real.log (34065 / 32768) ≤ (0.038818035 : ℝ) := by
  have hx : |(-1297 / 32768 : ℝ)| < 1 := by
    rw [abs_lt]; norm_num
  have h := log_one_sub_upper hx 12
  have habs : |(-1297 / 32768 : ℝ)| = 1297 / 32768 := by
    rw [abs_of_nonpos] <;> norm_num
  rw [habs] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A certified lower bound for `log (7341727 / 2^3 · 10^6)`, needed for the carry-free
comparison of Section 3 of `masked_digit_bound.tex`. -/
theorem log_t5_lower : (-0.085867441 : ℝ) ≤ Real.log (7341727 / 8000000) := by
  have hx : |(658273 / 8000000 : ℝ)| < 1 := by
    rw [abs_lt]; norm_num
  have h := log_one_sub_lower hx 12
  have habs : |(658273 / 8000000 : ℝ)| = 658273 / 8000000 := by
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 658273 / 8000000)]
  rw [habs] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The decomposition `log 34065 = 15 log 2 + log (34065 / 2^15)`. -/
theorem log_34065_eq : Real.log 34065 = 15 * Real.log 2 + Real.log (34065 / 32768) := by
  have hval : (34065 : ℝ) = 2 ^ 15 * (34065 / 32768) := by norm_num
  rw [hval, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The decomposition `log (7341727/10^6) = 3 log 2 + log (7341727 / (8 · 10^6))`. -/
theorem log_7341727_eq :
    Real.log (7341727 / 1000000) = 3 * Real.log 2 + Real.log (7341727 / 8000000) := by
  have hval : (7341727 / 1000000 : ℝ) = 2 ^ 3 * (7341727 / 8000000) := by norm_num
  rw [hval, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- **The carry-free exponent comparison of Section 3 of `masked_digit_bound.tex`, in product
form:** `0.19102809 · log 34065 < log 7.341727`.  Equivalently, the certified fugacity ratio
`P₋(x₀)/P₊(x₀) > 7.341727` already exceeds `34065^{0.19102809}`. -/
theorem carryFree_exponent_comparison :
    (0.19102809 : ℝ) * Real.log 34065 < Real.log ((7341727 : ℝ) / 1000000) := by
  have h2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  rw [log_34065_eq, log_7341727_eq]
  have h4 := log_t4_upper
  have h5 := log_t5_lower
  nlinarith [h4, h5, h2lo, h2hi]

end MaskedDigit
