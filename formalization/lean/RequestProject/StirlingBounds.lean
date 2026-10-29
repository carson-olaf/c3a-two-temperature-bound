module

/-
Copyright (c) 2026 Logan Kleinwaks. All rights reserved.
Released under Apache 2.0 license; see LICENSE-Kleinwaks.
Reused from kleinwaks/masked-digit-sum-difference-bound,
commit 352ab86effecb7efce415507a8c781ec158b86e0.
-/
public import Mathlib

@[expose] public section

/-!
# Two-sided Stirling bounds for `log n!`

Section 5 of `masked_digit_bound.tex` estimates the multinomial count

`D_N = N! / (n₀! ∏_{d>0} (n_d!)²)`

by directed `512`-bit MPFR evaluation of the logarithms of all the factorials involved.  The
Lean counterpart of that evaluation needs two-sided effective Stirling bounds for `log n!`.

Mathlib provides the lower bound `Stirling.le_log_factorial_stirling`,

`n log n - n + (log n)/2 + (log 2π)/2 ≤ log n!`.

This file adds the matching effective upper bound

`log n! ≤ n log n - n + (log n)/2 + 1`,

which follows from the fact that Mathlib's Stirling sequence is antitone with first value
`e/√2`, together with the sum version used for the `16184` factorials of Section 5.  The two
bounds differ by `1 - (log 2π)/2 < 0.082` per factorial, which is far below the tolerance of
the finite-depth certificate.
-/

open scoped BigOperators

namespace MaskedDigit

/-- **Effective Stirling upper bound for the factorial**: `n! ≤ e √n (n/e)ⁿ` for `n ≥ 1`.
This is the companion of Mathlib's `Stirling.le_factorial_stirling`, obtained from the fact
that the Stirling sequence is antitone with `stirlingSeq 1 = e/√2`. -/
theorem factorial_le_stirling {n : ℕ} (hn : n ≠ 0) :
    (Nat.factorial n : ℝ) ≤ Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hanti : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 := by
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
    simpa using this
  rw [Stirling.stirlingSeq_one] at hanti
  have hden : (0 : ℝ) < Real.sqrt (2 * (m + 1 : ℕ)) * ((m + 1 : ℕ) / Real.exp 1) ^ (m + 1) := by
    have h1 : (0 : ℝ) < ((m : ℝ) + 1) := by positivity
    have : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [this]
    positivity
  have hss : Stirling.stirlingSeq (m + 1)
      = (Nat.factorial (m + 1) : ℝ) /
        (Real.sqrt (2 * (m + 1 : ℕ)) * ((m + 1 : ℕ) / Real.exp 1) ^ (m + 1)) := by
    rw [Stirling.stirlingSeq]
  rw [hss, div_le_iff₀ hden] at hanti
  refine hanti.trans (le_of_eq ?_)
  have h2 : Real.sqrt (2 * (m + 1 : ℕ)) = Real.sqrt 2 * Real.sqrt (m + 1 : ℕ) := by
    rw [← Real.sqrt_mul (by norm_num)]
  rw [h2]
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-- **Effective Stirling upper bound for `log n!`**: `log n! ≤ n log n - n + (log n)/2 + 1`
for `n ≥ 1`.  This is the upper counterpart of Mathlib's
`Stirling.le_log_factorial_stirling`, and is the bound used for the denominators of the
multinomial count `D_N` of Section 5 of `masked_digit_bound.tex`. -/
theorem log_factorial_le {n : ℕ} (hn : n ≠ 0) :
    Real.log (Nat.factorial n) ≤ n * Real.log n - n + Real.log n / 2 + 1 := by
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  have h := factorial_le_stirling hn
  have hpos : (0 : ℝ) < Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n := by positivity
  have hlog := Real.log_le_log (by positivity) h
  refine hlog.trans (le_of_eq ?_)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_div (ne_of_gt hn0) (by positivity), Real.log_exp, Real.log_sqrt hn0.le]
  ring

/-- The sum version of `log_factorial_le`, for the `16184` factorials of Section 5 of
`masked_digit_bound.tex`. -/
theorem sum_log_factorial_le {ι : Type*} (s : Finset ι) (n : ι → ℕ) (hn : ∀ i ∈ s, n i ≠ 0) :
    ∑ i ∈ s, Real.log (Nat.factorial (n i))
      ≤ (∑ i ∈ s, (n i : ℝ) * Real.log (n i)) - (∑ i ∈ s, (n i : ℝ))
        + (∑ i ∈ s, Real.log (n i)) / 2 + s.card := by
  have h : ∑ i ∈ s, Real.log (Nat.factorial (n i))
      ≤ ∑ i ∈ s, ((n i : ℝ) * Real.log (n i) - (n i : ℝ) + Real.log (n i) / 2 + 1) :=
    Finset.sum_le_sum fun i hi => log_factorial_le (hn i hi)
  refine h.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    Finset.sum_const, nsmul_eq_mul, mul_one]

end MaskedDigit
