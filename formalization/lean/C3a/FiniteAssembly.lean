module

/-
Copyright (c) 2026 Carson Olafson. Released under Apache 2.0.
Author: Carson Olafson, with GPT-6 Astra assistance.
Uses Logan Kleinwaks's GHR definition and proved dilation principle,
Apache-2.0; see LICENSE-Kleinwaks.
-/
public import C3a.IntegerCompression

@[expose] public section

/-! # A finite certificate interface for the GHR constant

Bertrand's prime is chosen above `|V-V| + 2B + 1`. This avoids materializing
an enormous prime or computing a floor of an enormous real power.
-/
open scoped BigOperators Pointwise
open Finset MaskedDigit

namespace C3a

/-- Logs of weighted cardinality estimates. -/
theorem log_card_le_of_weight {m C N : ℕ} {x Z : ℝ}
    (hm : 0 < m) (hx : 0 < x)
    (h : (m : ℝ) * x ^ C ≤ Z ^ N) :
    Real.log m ≤ N * Real.log Z - C * Real.log x := by
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (m : ℝ) * x ^ C) h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hl
  linarith

/-- The purely finite reduction to log-cardinality inequalities. -/
theorem finite_certificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V W : Finset (ι → ℤ)) (B : ℕ) (h0 : 0 ∈ V)
    (hWV : W ⊆ V - V) (hW2 : 2 ≤ W.card)
    (hB : ∀ w ∈ W, ∀ i, |w i| ≤ (B : ℤ))
    (alpha a b r : ℝ) (ha : 0 < alpha)
    (hWa : a ≤ Real.log W.card)
    (hVb : Real.log (V + V).card ≤ b)
    (hVr : Real.log (V - V).card ≤ r)
    (hmargin : alpha * (r + Real.log (8 * (2 * B + 2) : ℝ)) + b + Real.log 4 < a) :
    1 + alpha < MaskedDigit.C3a := by
  classical
  have hV : V.Nonempty := ⟨0, h0⟩
  have hW : W.Nonempty := card_pos.mp (by omega)
  have hD : 0 < (V - V).card := card_pos.mpr (hV.sub hV)
  have hS : 0 < (V + V).card := card_pos.mpr (hV.add hV)
  obtain ⟨p, hp, hpgt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul
    ((V - V).card + 2 * B + 1) (by omega)
  letI : Fact p.Prime := ⟨hp⟩
  have hWp : W.card < p := lt_of_le_of_lt (card_le_card hWV) (by omega)
  obtain ⟨φ, hφ⟩ := exists_integer_compression W B p (by omega) hB hW hWp
  let A := representatives p V φ
  have hA0 : 0 ∈ A := by
    exact mem_image.mpr ⟨0, mem_image.mpr ⟨0, h0, map_zero φ⟩, ZMod.val_zero⟩
  have hA : A.Nonempty := ⟨0, hA0⟩
  have hds : W.card < 2 * (natDiffFinset A A).card :=
    hφ.trans_le (Nat.mul_le_mul_left 2 (representatives_diff_card p V W φ hWV))
  have hss : (natSumFinset A A).card ≤ 2 * (V + V).card := representatives_sum_card p V φ
  have hmax : 0 < A.max' hA := by
    by_contra h
    have hm : A.max' hA = 0 := by omega
    have hAeq : A = {0} := by
      apply eq_singleton_iff_unique_mem.mpr
      exact ⟨hA0, fun x hx => by have := A.le_max' x hx; omega⟩
    have hd : (natDiffFinset A A).card = 1 := by simp [hAeq, natDiffFinset]
    rw [hd] at hds
    omega
  have hmaxp : A.max' hA < p := by
    obtain ⟨z, hz, heq⟩ := mem_image.mp (A.max'_mem hA)
    rw [← heq]
    exact ZMod.val_lt z
  have hqpos : 0 < Real.log (4 * (A.max' hA : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast (show 1 < 4 * A.max' hA + 1 by omega))
  have hq : Real.log (4 * (A.max' hA : ℝ) + 1) ≤
      r + Real.log (8 * (2 * B + 2) : ℝ) := by
    have hbound : 4 * A.max' hA + 1 ≤ 8 * (2 * B + 2) * (V - V).card := by
      have h1 : 4 * A.max' hA + 1 ≤ 4 * p := by omega
      have h2 : 4 * p ≤ 8 * ((V - V).card + 2 * B + 1) := by omega
      have h3 : (V - V).card + 2 * B + 1 ≤ (2 * B + 2) * (V - V).card := by nlinarith
      nlinarith
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 4 * (A.max' hA : ℝ) + 1)
      (show 4 * (A.max' hA : ℝ) + 1 ≤ (8 * (2 * B + 2) : ℝ) * (V - V).card by exact_mod_cast hbound)
    rw [Real.log_mul (by positivity) (by positivity)] at hlog
    linarith
  have hdpos : 0 < (natDiffFinset A A).card := by omega
  have hspos : 0 < (natSumFinset A A).card := card_pos.mpr
    (hA.image₂ hA (f := fun a b : ℕ => a + b))
  have hld : Real.log W.card - Real.log 2 < Real.log (natDiffFinset A A).card := by
    have h := Real.log_lt_log (by exact_mod_cast (show 0 < W.card by omega))
      (show (W.card : ℝ) < 2 * (natDiffFinset A A).card by exact_mod_cast hds)
    rw [Real.log_mul (by norm_num) (by positivity)] at h
    linarith
  have hls : Real.log (natSumFinset A A).card ≤ Real.log 2 + b := by
    have h := Real.log_le_log (by exact_mod_cast hspos)
      (show ((natSumFinset A A).card : ℝ) ≤ 2 * (V + V).card by exact_mod_cast hss)
    rw [Real.log_mul (by norm_num) (by positivity)] at h
    linarith
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have hratio : alpha * Real.log (4 * (A.max' hA : ℝ) + 1) <
      Real.log (((natDiffFinset A A).card : ℝ) / (natSumFinset A A).card) := by
    rw [Real.log_div (by positivity) (by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hq ha.le
    rw [h4] at hmargin
    linarith
  have htarget : 1 + alpha < 1 +
      Real.log (((natDiffFinset A A).card : ℝ) / (natSumFinset A A).card) /
        Real.log (4 * (A.max' hA : ℝ) + 1) := by
    have := (lt_div_iff₀ hqpos).mpr hratio
    linarith
  exact htarget.trans_le (ghr_dilated_lower_bound A hA0 hA hmax)

end C3a
