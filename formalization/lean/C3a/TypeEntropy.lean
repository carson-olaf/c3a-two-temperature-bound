module

/-
Copyright (c) 2026 Carson Olafson. Released under Apache 2.0.
Author: Carson Olafson, with GPT-6 Astra assistance.
Uses Logan Kleinwaks's effective Stirling upper bound, Apache-2.0.
-/
public import RequestProject.StirlingBounds

@[expose] public section

/-! # A finite multinomial estimate from a common Gibbs envelope -/
open scoped BigOperators
open Finset

namespace C3a

/-- Finite type estimate. An envelope `(N+E) x^cost / Z` allows floors and
rounding at zero without evaluating one logarithm for every count. -/
theorem log_multinomial_lower {ι : Type*} (s : Finset ι) (n cost : ι → ℕ)
    (N C T : ℕ) (x Z E : ℝ)
    (hN : 0 < N) (hx : 0 < x) (hZ : 0 < Z) (hE : 0 ≤ E)
    (hn : ∀ i ∈ s, 0 < n i)
    (hsum : ∑ i ∈ s, n i = N)
    (hcost : ∑ i ∈ s, n i * cost i = C)
    (henv : ∀ i ∈ s, (n i : ℝ) ≤ (N + E) * x ^ cost i / Z)
    (hT : T * (∏ i ∈ s, (n i).factorial) = N.factorial) :
    (N : ℝ) * Real.log Z - C * Real.log x - E -
      (s.card : ℝ) * (Real.log N / 2 + 1) ≤ Real.log T := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNE : (0 : ℝ) < N + E := by positivity
  have hnle (i) (hi : i ∈ s) : n i ≤ N := by
    rw [← hsum]
    exact single_le_sum (fun _ _ => Nat.zero_le _) hi
  have hlog (i) (hi : i ∈ s) : Real.log (n i) ≤
      Real.log (N + E) + cost i * Real.log x - Real.log Z := by
    have h := Real.log_le_log (by exact_mod_cast hn i hi) (henv i hi)
    rwa [Real.log_div (by positivity) (ne_of_gt hZ),
      Real.log_mul (ne_of_gt hNE) (by positivity), Real.log_pow] at h
  have hsumlog : ∑ i ∈ s, (n i : ℝ) * Real.log (n i) ≤
      N * Real.log (N + E) + C * Real.log x - N * Real.log Z := by
    have h := sum_le_sum (s := s) (fun i hi =>
      mul_le_mul_of_nonneg_left (hlog i hi) (Nat.cast_nonneg (n i)))
    have heq : (∑ i ∈ s, (n i : ℝ) * (Real.log (N + E) +
        cost i * Real.log x - Real.log Z)) =
        N * Real.log (N + E) + C * Real.log x - N * Real.log Z := by
      simp only [mul_sub, mul_add, ← mul_assoc, sum_sub_distrib, sum_add_distrib,
        ← sum_mul, ← Nat.cast_mul, ← Nat.cast_sum, hsum, hcost]
    exact h.trans_eq heq
  have hsumsmall : ∑ i ∈ s, Real.log (n i) ≤ s.card * Real.log N := by
    calc
      (∑ i ∈ s, Real.log (n i)) ≤ ∑ _i ∈ s, Real.log N := by
        apply sum_le_sum
        intro i hi
        exact Real.log_le_log (by exact_mod_cast hn i hi) (by exact_mod_cast hnle i hi)
      _ = _ := by simp
  have hupper := MaskedDigit.sum_log_factorial_le s n (fun i hi => (hn i hi).ne')
  have hsumcast : (∑ i ∈ s, (n i : ℝ)) = N := by exact_mod_cast hsum
  rw [hsumcast] at hupper
  have hlower : (N : ℝ) * Real.log N - N ≤ Real.log N.factorial := by
    have h := Stirling.le_log_factorial_stirling hN.ne'
    have hlN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    have hlpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  have hTpos : 0 < T := by
    have := Nat.factorial_pos N
    rw [← hT] at this
    exact Nat.pos_of_mul_pos_right this
  have hTeq : Real.log T + ∑ i ∈ s, Real.log (n i).factorial = Real.log N.factorial := by
    have hcast : (T : ℝ) * ∏ i ∈ s, ((n i).factorial : ℝ) = N.factorial := by
      exact_mod_cast hT
    rw [← Real.log_prod (fun i _ => by positivity), ← Real.log_mul (by positivity) (by positivity), hcast]
  have hround : (N : ℝ) * (Real.log (N + E) - Real.log N) ≤ E := by
    have h := Real.log_le_sub_one_of_pos (div_pos hNE hNR)
    rw [Real.log_div hNE.ne' hNR.ne'] at h
    have h' := mul_le_mul_of_nonneg_left h hNR.le
    have he : (N : ℝ) * ((N + E) / N - 1) = E := by field_simp; ring
    rwa [he] at h'
  nlinarith

end C3a
