/-
Copyright (c) 2026 Logan Kleinwaks. All rights reserved.
Released under Apache 2.0 license; see LICENSE-Kleinwaks.
Reused from kleinwaks/masked-digit-sum-difference-bound,
commit 352ab86effecb7efce415507a8c781ec158b86e0.
-/
import Mathlib

/-!
# Product weights on words and a Chebyshev estimate

This file develops the elementary discrete probability needed for the construction proofs of
`masked_digit_bound.tex`.  In the source the counting is carried out with the method of types
and the multinomial estimate (5) (`eq:multinomial-estimate`); here the equivalent
concentration input is packaged as a second-moment (Chebyshev) estimate for the product
measure `w ↦ ∏ⱼ p (w j)` on words, which is the same Gibbs measure `p` of equation (7)
(`eq:gibbs`) of the source.

The main results are:

* `ProductWeights.sum_wt`: the product weights sum to one;
* `ProductWeights.sum_wt_sq_of_centered`: the exact second moment of a centred additive
  statistic;
* `ProductWeights.mass_deviation_le`: the Chebyshev bound for such a statistic.
-/

open scoped BigOperators

namespace MaskedDigit
namespace ProductWeights

variable {A : Type*} [Fintype A]

/-- The product weight `∏ⱼ p (w j)` of a word `w`, i.e. the Gibbs product measure used in the
construction proofs of `masked_digit_bound.tex`. -/
def wt (p : A → ℝ) {l : ℕ} (w : Fin l → A) : ℝ := ∏ j, p (w j)

omit [Fintype A] in
theorem wt_nonneg {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) {l : ℕ} (w : Fin l → A) : 0 ≤ wt p w :=
  Finset.prod_nonneg fun _ _ => hp _

/-- The product weights of a probability vector sum to one over all words; this is the normalization used by the method-of-types arguments of `masked_digit_bound.tex`. -/
theorem sum_wt (p : A → ℝ) (hsum : ∑ a, p a = 1) (l : ℕ) :
    ∑ w : Fin l → A, wt p w = 1 := by
  have := (Fintype.prod_sum (fun (_ : Fin l) (a : A) => p a)).symm
  simpa [wt, hsum] using this

/-- Expectation of a single-coordinate function under the product weights. -/
theorem sum_wt_single (p : A → ℝ) (hsum : ∑ a, p a = 1) (g : A → ℝ) {l : ℕ} (j₀ : Fin l) :
    ∑ w : Fin l → A, wt p w * g (w j₀) = ∑ a, p a * g a := by
  classical
  set F : Fin l → A → ℝ := fun j a => p a * (if j = j₀ then g a else 1) with hF
  have hprod : ∀ w : Fin l → A, ∏ j, F j (w j) = wt p w * g (w j₀) := by
    intro w
    simp only [hF, wt, Finset.prod_mul_distrib]
    congr 1
    simp
  have hsumF : ∀ j : Fin l, ∑ a, F j a = (if j = j₀ then (∑ a, p a * g a) else 1) := by
    intro j
    by_cases h : j = j₀ <;> simp [hF, h, hsum]
  calc ∑ w : Fin l → A, wt p w * g (w j₀)
      = ∑ w : Fin l → A, ∏ j, F j (w j) := (Finset.sum_congr rfl fun w _ => (hprod w).symm)
    _ = ∏ j, ∑ a, F j a := (Fintype.prod_sum F).symm
    _ = ∑ a, p a * g a := by simp [hsumF]

/-- Expectation of a product of two distinct coordinates under the product weights. -/
theorem sum_wt_pair (p : A → ℝ) (hsum : ∑ a, p a = 1) (g h : A → ℝ) {l : ℕ} {j₀ j₁ : Fin l}
    (hne : j₀ ≠ j₁) :
    ∑ w : Fin l → A, wt p w * (g (w j₀) * h (w j₁)) =
      (∑ a, p a * g a) * (∑ a, p a * h a) := by
  classical
  set F : Fin l → A → ℝ :=
    fun j a => p a * (if j = j₀ then g a else 1) * (if j = j₁ then h a else 1) with hF
  have hprod : ∀ w : Fin l → A, ∏ j, F j (w j) = wt p w * (g (w j₀) * h (w j₁)) := by
    intro w
    simp only [hF, wt, Finset.prod_mul_distrib]
    rw [Finset.prod_ite_eq' Finset.univ j₀ (fun j => g (w j)),
      Finset.prod_ite_eq' Finset.univ j₁ (fun j => h (w j))]
    simp [mul_assoc]
  have hsumF : ∀ j : Fin l, ∑ a, F j a =
      (if j = j₀ then (∑ a, p a * g a) else 1) * (if j = j₁ then (∑ a, p a * h a) else 1) := by
    intro j
    simp only [hF]
    by_cases h0 : j = j₀
    · simp [h0, hne]
    · by_cases h1 : j = j₁ <;> simp [h0, h1, hsum, Ne.symm hne]
  calc ∑ w : Fin l → A, wt p w * (g (w j₀) * h (w j₁))
      = ∑ w : Fin l → A, ∏ j, F j (w j) := (Finset.sum_congr rfl fun w _ => (hprod w).symm)
    _ = ∏ j, ∑ a, F j a := (Fintype.prod_sum F).symm
    _ = (∑ a, p a * g a) * (∑ a, p a * h a) := by
        rw [Finset.prod_congr rfl (fun j _ => hsumF j), Finset.prod_mul_distrib,
          Finset.prod_ite_eq' Finset.univ j₀ (fun _ => (∑ a, p a * g a)),
          Finset.prod_ite_eq' Finset.univ j₁ (fun _ => (∑ a, p a * h a))]
        simp

/-- **Exact second moment of a centred additive statistic.**  If `∑ₐ p a * g a = 0`, then the
statistic `w ↦ ∑ⱼ g (w j)` has second moment `l * ∑ₐ p a * g a ^ 2` under the product weights.
This replaces the variance computation implicit in the concentration step of the proofs of
Propositions 2 and 4 of `masked_digit_bound.tex`. -/
theorem sum_wt_sq_of_centered (p : A → ℝ) (hsum : ∑ a, p a = 1) (g : A → ℝ)
    (hg : ∑ a, p a * g a = 0) (l : ℕ) :
    ∑ w : Fin l → A, wt p w * (∑ j, g (w j)) ^ 2 = l * ∑ a, p a * g a ^ 2 := by
  classical
  have expand : ∀ w : Fin l → A, (∑ j, g (w j)) ^ 2 = ∑ j, ∑ j', g (w j) * g (w j') := by
    intro w
    rw [sq, Finset.sum_mul_sum]
  have step1 : ∑ w : Fin l → A, wt p w * (∑ j, g (w j)) ^ 2
      = ∑ w : Fin l → A, ∑ j : Fin l, ∑ j' : Fin l, wt p w * (g (w j) * g (w j')) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [expand w, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
  have step2 : ∑ w : Fin l → A, ∑ j : Fin l, ∑ j' : Fin l, wt p w * (g (w j) * g (w j'))
      = ∑ j : Fin l, ∑ j' : Fin l, ∑ w : Fin l → A, wt p w * (g (w j) * g (w j')) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [step1, step2]
  have step3 : ∀ j j' : Fin l, ∑ w : Fin l → A, wt p w * (g (w j) * g (w j'))
      = (if j = j' then (∑ a, p a * g a ^ 2) else 0) := by
    intro j j'
    by_cases hjj : j = j'
    · subst hjj
      rw [if_pos rfl]
      have := sum_wt_single p hsum (fun a => g a * g a) j
      simpa [sq] using this
    · rw [if_neg hjj, sum_wt_pair p hsum g g hjj, hg]
      ring
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => step3 j j'))]
  simp [Finset.sum_ite_eq]

/-- **Chebyshev's inequality for the product weights.**  The total weight of the words on
which a centred additive statistic deviates by at least `t` is at most `l V / t²`.  This is
the concentration input for the constructions of Propositions 2 and 4 of
`masked_digit_bound.tex`. -/
theorem mass_deviation_le (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (g : A → ℝ)
    (hg : ∑ a, p a * g a = 0) (l : ℕ) {t : ℝ} (ht : 0 < t) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin l → A => t ≤ |∑ j, g (w j)|), wt p w ≤
      (l * ∑ a, p a * g a ^ 2) / t ^ 2 := by
  classical
  set Bad := Finset.univ.filter (fun w : Fin l → A => t ≤ |∑ j, g (w j)|) with hBad
  have key : t ^ 2 * ∑ w ∈ Bad, wt p w ≤ ∑ w : Fin l → A, wt p w * (∑ j, g (w j)) ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ w ∈ Bad, t ^ 2 * wt p w
        ≤ ∑ w ∈ Bad, wt p w * (∑ j, g (w j)) ^ 2 := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hw' : t ≤ |∑ j, g (w j)| := by
            simpa [hBad] using (Finset.mem_filter.1 hw).2
          have hnn := wt_nonneg hp w
          have hsq : t ^ 2 ≤ (∑ j, g (w j)) ^ 2 := by
            nlinarith [sq_abs (∑ j, g (w j)), abs_nonneg (∑ j, g (w j))]
          rw [mul_comm (wt p w)]
          exact mul_le_mul_of_nonneg_right hsq hnn
      _ ≤ ∑ w : Fin l → A, wt p w * (∑ j, g (w j)) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro w _ _
          exact mul_nonneg (wt_nonneg hp w) (sq_nonneg _)
  rw [sum_wt_sq_of_centered p hsum g hg l] at key
  rw [le_div_iff₀ (by positivity)]
  linarith [key]

/-! ## The Gibbs weights -/

section Gibbs

variable [Nonempty A]

/-- The Gibbs weights `p(a) = x^{cost(a)} / Z` of equation (7) (`eq:gibbs`) of
`masked_digit_bound.tex`. -/
noncomputable def gibbs (x : ℝ) (cost : A → ℕ) (a : A) : ℝ := x ^ cost a / ∑ b, x ^ cost b

/-- The partition function `Z = ∑ₐ x^{cost(a)}` of `masked_digit_bound.tex` is positive. -/
theorem gibbs_partition_pos {x : ℝ} (hx : 0 < x) (cost : A → ℕ) : 0 < ∑ b, x ^ cost b :=
  Finset.sum_pos (fun _ _ => pow_pos hx _) Finset.univ_nonempty

/-- The Gibbs weights of equation (7) of `masked_digit_bound.tex` are nonnegative. -/
theorem gibbs_nonneg {x : ℝ} (hx : 0 < x) (cost : A → ℕ) (a : A) : 0 ≤ gibbs x cost a :=
  div_nonneg (le_of_lt (pow_pos hx _)) (le_of_lt (gibbs_partition_pos hx cost))

/-- The Gibbs weights of equation (7) of `masked_digit_bound.tex` are a probability
vector. -/
theorem sum_gibbs {x : ℝ} (hx : 0 < x) (cost : A → ℕ) : ∑ a, gibbs x cost a = 1 := by
  simp only [gibbs, ← Finset.sum_div]
  exact div_self (ne_of_gt (gibbs_partition_pos hx cost))

omit [Nonempty A] in
/-- The product Gibbs weight of a word is `x^{total cost} / Z^l`; this is the identity that
turns the weighted counting of `masked_digit_bound.tex` into a cardinality bound. -/
theorem wt_gibbs (x : ℝ) (cost : A → ℕ) {l : ℕ} (w : Fin l → A) :
    wt (gibbs x cost) w = x ^ (∑ j, cost (w j)) / (∑ b, x ^ cost b) ^ l := by
  simp only [wt, gibbs, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow_eq_pow_sum]

end Gibbs

end ProductWeights
end MaskedDigit
