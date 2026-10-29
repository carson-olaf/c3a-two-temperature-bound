module

/-
Copyright (c) 2026 Carson Olafson. Released under Apache 2.0.
Author: Carson Olafson, with GPT-6 Astra assistance.
Uses Logan Kleinwaks's GHR constant, finite-set principle, type counting,
and Stirling estimates under Apache-2.0; see LICENSE-Kleinwaks.
-/
public import C3a.VectorWords
public import C3a.TypeEntropy
public import C3a.FiniteAssembly
public import C3a.LogNumerics

@[expose] public section

/-! # The finite two-temperature bound

A single type at depth 10^13 supplies the finite certificate. Neither a
limit nor an assumed asymptotic principle is used. The theorem uses exactly
Logan Kleinwaks's definition of the GHR sum-difference constant.
-/
open scoped BigOperators Pointwise
open Finset

namespace C3a
attribute [local irreducible] minusPartition plusPartition count budget Vectors.V
set_option maxRecDepth 8000

private theorem minus_pos : (0 : ℝ) < (minusPartition : ℝ) := by
  apply Rat.cast_pos.mpr
  have := minusPartition_bounds.1
  linarith

private theorem type_log_lower (T : ℕ)
    (hT : T * (∏ d ∈ data.diffSupport, (count d).factorial) = depth.factorial) :
    (32160395000000 : ℝ) ≤ Real.log T := by
  have he (d : ℤ) (hd : d ∈ data.diffSupport) :
      (count d : ℝ) ≤ (depth + 1000 : ℝ) * (x : ℝ)^cost d / (minusPartition : ℝ) := by
    have ht := (Rat.cast_le (K := ℝ)).mpr (count_envelope d hd)
    push_cast at ht
    exact ht
  have ht := log_multinomial_lower data.diffSupport count cost depth (2 * budget) T
    (x : ℝ) (minusPartition : ℝ) 1000 (by norm_num [depth]) (by norm_num [x])
    minus_pos (by norm_num) count_positive count_sum count_cost he hT
  rw [diff_card, budget_exact] at ht
  have hN := log_depth_lt
  norm_num [depth] at ht hN
  nlinarith [log_minus_lower, log_x_bounds.2]

private theorem sum_log_upper :
    Real.log (Vectors.V data depth budget + Vectors.V data depth budget).card ≤
      (25272245000000 : ℝ) := by
  have hne : (Vectors.V data depth budget).Nonempty := ⟨0, Vectors.zero_mem_V data depth budget⟩
  have hw := Vectors.sum_card_weighted data depth budget (y : ℝ)
    (by norm_num [y]) (by norm_num [y])
  rw [Pplus_eq] at hw
  have hl := log_card_le_of_weight (card_pos.mpr (hne.add hne))
    (by norm_num [y] : (0 : ℝ) < y) hw
  rw [budget_exact] at hl
  norm_num [depth] at hl
  nlinarith [log_plus_upper, log_y_bounds.1]

private theorem diff_log_upper :
    Real.log (Vectors.V data depth budget - Vectors.V data depth budget).card ≤
      (32160396000000 : ℝ) := by
  have hne : (Vectors.V data depth budget).Nonempty := ⟨0, Vectors.zero_mem_V data depth budget⟩
  have hw := Vectors.diff_card_weighted data depth budget (x : ℝ)
    (by norm_num [x]) (by norm_num [x])
  rw [Pminus_eq] at hw
  have hl := log_card_le_of_weight (card_pos.mpr (hne.sub hne))
    (by norm_num [x] : (0 : ℝ) < x) hw
  rw [budget_exact] at hl
  norm_num [depth] at hl
  nlinarith [log_minus_upper, log_x_bounds.1]

private theorem overhead_log : Real.log (1296 : ℝ) < 8 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1296) (by norm_num : (1296 : ℝ) ≤ 2048)
  have he : Real.log (2048 : ℝ) = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2^11 by norm_num, Real.log_pow]; norm_num
  rw [he] at h
  linarith [Real.log_two_lt_d9]

/-- The strict finite-certificate bound for the GHR sum-difference constant. -/
theorem c3a_gt_121418 : (60709 / 50000 : ℝ) < MaskedDigit.C3a := by
  obtain ⟨W, hWV, hT, hB⟩ := Vectors.exists_type_family data count depth budget
    count_symm count_sum count_kappa
  have ha := type_log_lower W.card hT
  have hWpos : 0 < W.card := by
    have h := Nat.factorial_pos depth
    rw [← hT] at h
    exact Nat.pos_of_mul_pos_right h
  have hW2 : 2 ≤ W.card := by
    by_contra h
    have hw : W.card = 1 := by omega
    rw [hw] at ha
    norm_num at ha
  have h := finite_certificate (Vectors.V data depth budget) W 80
    (Vectors.zero_mem_V data depth budget) hWV hW2 hB (10709 / 50000)
    32160395000000 25272245000000 32160396000000 (by norm_num)
    ha sum_log_upper diff_log_upper (by
      norm_num only [Nat.cast_ofNat]
      have h4 : Real.log (4 : ℝ) < 2 := by
        have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
        rw [he]
        linarith [Real.log_two_lt_d9]
      have hc := overhead_log
      norm_num at hc ⊢
      linarith)
  norm_num at h
  exact h

end C3a

#print axioms C3a.c3a_gt_121418
