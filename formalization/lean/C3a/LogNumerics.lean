module

/-
Copyright (c) 2026 Carson Olafson. Released under Apache 2.0.
Author: Carson Olafson, with GPT-6 Astra assistance.
Uses the logarithm enclosure lemmas of Logan Kleinwaks, Apache-2.0.
-/
public import C3a.CertificateData
public import RequestProject.LogBounds

@[expose] public section

/-! # Rational logarithm bounds for the finite certificate -/
open scoped BigOperators

namespace C3a
attribute [local irreducible] minusPartition plusPartition count budget
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

/-- Bounds on log x from a finite Mercator series. -/
theorem log_x_bounds : (-0.204689873 : ℝ) ≤ Real.log (x : ℝ) ∧
    Real.log (x : ℝ) ≤ -0.204689872 := by
  have hl := MaskedDigit.log_one_sub_lower (x := (1851 / 10000 : ℝ)) (by norm_num) 16
  have hu := MaskedDigit.log_one_sub_upper (x := (1851 / 10000 : ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ, abs_of_pos] at hl hu
  norm_num [x]
  constructor <;> linarith

theorem log_y_bounds : (-0.160849736 : ℝ) ≤ Real.log (y : ℝ) ∧
    Real.log (y : ℝ) ≤ -0.160849734 := by
  have hl := MaskedDigit.log_one_sub_lower (x := (7429 / 50000 : ℝ)) (by norm_num) 16
  have hu := MaskedDigit.log_one_sub_upper (x := (7429 / 50000 : ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ, abs_of_pos] at hl hu
  norm_num [y]
  constructor <;> linarith

theorem log_minus_lower : (1.651485884 : ℝ) ≤ Real.log (minusPartition : ℝ) := by
  have h := MaskedDigit.log_one_sub_lower (x := (-607361276021 / 2000000000000 : ℝ))
    (by norm_num [abs_of_neg]) 24
  norm_num [Finset.sum_range_succ, abs_of_neg] at h
  have hd : Real.log (5214722552042 / 10^12 : ℝ) =
      2 * Real.log 2 + Real.log (2607361276021 / 2000000000000 : ℝ) := by
    have he : (5214722552042 / 10^12 : ℝ) = 2^2 * (2607361276021 / 2000000000000) := by norm_num
    rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hm : (5214722552042 / 10^12 : ℝ) < (minusPartition : ℝ) := by
    have ht := (Rat.cast_lt (K := ℝ)).mpr minusPartition_bounds.1
    push_cast at ht
    exact ht
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 5214722552042 / 10^12) hm.le
  rw [hd] at hh
  have h2 := Real.log_two_gt_d9
  linarith

theorem log_minus_upper : Real.log (minusPartition : ℝ) ≤ (1.651485887 : ℝ) := by
  have h := MaskedDigit.log_one_sub_upper (x := (-1214722552043 / 4000000000000 : ℝ))
    (by norm_num [abs_of_neg]) 24
  norm_num [Finset.sum_range_succ, abs_of_neg] at h
  have hd : Real.log (5214722552043 / 10^12 : ℝ) =
      2 * Real.log 2 + Real.log (5214722552043 / 4000000000000 : ℝ) := by
    have he : (5214722552043 / 10^12 : ℝ) = 2^2 * (5214722552043 / 4000000000000) := by norm_num
    rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hm : (minusPartition : ℝ) < (5214722552043 / 10^12 : ℝ) := by
    have ht := (Rat.cast_lt (K := ℝ)).mpr minusPartition_bounds.2
    push_cast at ht
    exact ht
  have hp : (0 : ℝ) < (minusPartition : ℝ) := by
    have := minusPartition_bounds.1
    exact_mod_cast (show (0 : ℚ) < minusPartition by linarith)
  have hh := Real.log_le_log hp hm.le
  rw [hd] at hh
  have h2 := Real.log_two_lt_d9
  linarith

theorem log_plus_upper : Real.log (plusPartition : ℝ) ≤ (1.297764247 : ℝ) := by
  have h := MaskedDigit.log_one_sub_upper (x := (169448906699 / 2000000000000 : ℝ))
    (by norm_num [abs_of_pos]) 12
  norm_num [Finset.sum_range_succ, abs_of_pos] at h
  have hd : Real.log (3661102186602 / 10^12 : ℝ) =
      2 * Real.log 2 + Real.log (1830551093301 / 2000000000000 : ℝ) := by
    have he : (3661102186602 / 10^12 : ℝ) = 2^2 * (1830551093301 / 2000000000000) := by norm_num
    rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hm : (plusPartition : ℝ) < (3661102186602 / 10^12 : ℝ) := by
    have ht := (Rat.cast_lt (K := ℝ)).mpr plusPartition_bounds.2
    push_cast at ht
    exact ht
  have hp : (0 : ℝ) < (plusPartition : ℝ) := by
    have := plusPartition_bounds.1
    exact_mod_cast (show (0 : ℚ) < plusPartition by linarith)
  have hh := Real.log_le_log hp hm.le
  rw [hd] at hh
  have h2 := Real.log_two_lt_d9
  linarith

/-- Coarse bound sufficient for the Stirling overhead at N=10^13. -/
theorem log_depth_lt : Real.log (depth : ℝ) < 40 := by
  have h10 : Real.log (10 : ℝ) < 3 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 10) (by norm_num : (10 : ℝ) ≤ 16)
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
    rw [h16] at h
    linarith [Real.log_two_lt_d9]
  have hd : Real.log (depth : ℝ) = 13 * Real.log 10 := by
    unfold depth
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  linarith

end C3a
