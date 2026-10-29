module

/-
Copyright (c) 2026 Logan Kleinwaks. All rights reserved.
Released under Apache 2.0 license; see LICENSE-Kleinwaks.
Reused from kleinwaks/masked-digit-sum-difference-bound,
commit 352ab86effecb7efce415507a8c781ec158b86e0.
-/
/- Modified by Carson Olafson with GPT-6 Astra: ported module visibility
for Lean 4.35.0-rc2; mathematical declarations and proofs are unchanged. -/
public import RequestProject.CoreConstruction

@[expose] public section

/-!
# The carry-free masked-digit bound

This file formalizes Section 2 ("The masked-digit bound") of `masked_digit_bound.tex`:

* the carry-free injectivity statement used in the proof of Proposition 2 (a signed digit
  word with digits in `[-B, B]` is determined by its value in base `Q = 2B + 1`);
* Proposition 2 itself (`prop:masked`, equation (6) `eq:masked-bound`);
* the Remark "Recovery of Zheng's optimization", which computes `P₊` and `P₋` for the
  complete mask `M = {0, 1, …, B}`.
-/

open scoped BigOperators

namespace MaskedDigit

/-! ## Carry-free injectivity -/

/-- **Carry-free injectivity, sequence form.**  In the balanced base `q = 2B + 1`, a signed
digit sequence with digits in `[-B, B]` is determined by the integer it represents.  This is
the reduction-modulo-`Q` argument in the proof of Proposition 2 of
`masked_digit_bound.tex`. -/
theorem balanced_base_injective_range (B q : ℕ) (hq : q = 2 * B + 1) :
    ∀ (m : ℕ) (d e : ℕ → ℤ), (∀ i, |d i| ≤ (B : ℤ)) → (∀ i, |e i| ≤ (B : ℤ)) →
      (∑ i ∈ Finset.range m, d i * (q : ℤ) ^ i = ∑ i ∈ Finset.range m, e i * (q : ℤ) ^ i) →
      ∀ i < m, d i = e i := by
  intro m
  induction m with
  | zero => intro d e _ _ _ i hi; omega
  | succ n ih =>
    intro d e hd he hval i hi
    rw [Finset.sum_range_succ' (fun i => d i * (q : ℤ) ^ i) n,
      Finset.sum_range_succ' (fun i => e i * (q : ℤ) ^ i) n] at hval
    simp only [pow_succ, pow_zero, mul_one] at hval
    have hq0 : (0 : ℤ) < (q : ℤ) := by rw [hq]; positivity
    have hdvd : (q : ℤ) ∣ (d 0 - e 0) := by
      refine ⟨∑ i ∈ Finset.range n, e (i + 1) * (q : ℤ) ^ i -
        ∑ i ∈ Finset.range n, d (i + 1) * (q : ℤ) ^ i, ?_⟩
      have h1 : ∑ i ∈ Finset.range n, d (i + 1) * ((q : ℤ) ^ i * (q : ℤ)) =
          (∑ i ∈ Finset.range n, d (i + 1) * (q : ℤ) ^ i) * (q : ℤ) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      have h2 : ∑ i ∈ Finset.range n, e (i + 1) * ((q : ℤ) ^ i * (q : ℤ)) =
          (∑ i ∈ Finset.range n, e (i + 1) * (q : ℤ) ^ i) * (q : ℤ) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [h1, h2] at hval
      linarith [hval]
    have habs : |d 0 - e 0| < (q : ℤ) := by
      have h1 := hd 0
      have h2 := he 0
      rw [abs_le] at h1 h2
      rw [abs_lt]
      constructor <;> [skip; skip] <;> · rw [hq]; push_cast; omega
    have hzero : d 0 - e 0 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
    have hd0 : d 0 = e 0 := by omega
    -- cancel the constant term and divide by `q`
    have hshift : ∑ i ∈ Finset.range n, d (i + 1) * (q : ℤ) ^ i =
        ∑ i ∈ Finset.range n, e (i + 1) * (q : ℤ) ^ i := by
      have h1 : ∑ i ∈ Finset.range n, d (i + 1) * ((q : ℤ) ^ i * (q : ℤ)) =
          (∑ i ∈ Finset.range n, d (i + 1) * (q : ℤ) ^ i) * (q : ℤ) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      have h2 : ∑ i ∈ Finset.range n, e (i + 1) * ((q : ℤ) ^ i * (q : ℤ)) =
          (∑ i ∈ Finset.range n, e (i + 1) * (q : ℤ) ^ i) * (q : ℤ) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [h1, h2, hd0] at hval
      have := mul_right_cancel₀ (ne_of_gt hq0) (by linarith [hval] :
        (∑ i ∈ Finset.range n, d (i + 1) * (q : ℤ) ^ i) * (q : ℤ) =
          (∑ i ∈ Finset.range n, e (i + 1) * (q : ℤ) ^ i) * (q : ℤ))
      exact this
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · exact hd0
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      exact ih (fun t => d (t + 1)) (fun t => e (t + 1)) (fun t => hd _) (fun t => he _)
        hshift i' (by omega)

/-- **Carry-free injectivity, finite-vector form.**  This is the exact injectivity statement
used in the proof of Proposition 2 of `masked_digit_bound.tex`. -/
theorem balanced_base_injective (B q m : ℕ) (hq : q = 2 * B + 1) (d e : Fin m → ℤ)
    (hd : ∀ i, |d i| ≤ (B : ℤ)) (he : ∀ i, |e i| ≤ (B : ℤ))
    (hval : ∑ i, d i * (q : ℤ) ^ (i : ℕ) = ∑ i, e i * (q : ℤ) ^ (i : ℕ)) :
    d = e := by
  classical
  set d' : ℕ → ℤ := fun i => if h : i < m then d ⟨i, h⟩ else 0 with hd'
  set e' : ℕ → ℤ := fun i => if h : i < m then e ⟨i, h⟩ else 0 with he'
  have hd'b : ∀ i, |d' i| ≤ (B : ℤ) := by
    intro i
    by_cases h : i < m
    · simp only [hd', dif_pos h]; exact hd _
    · simp only [hd', dif_neg h, abs_zero]; positivity
  have he'b : ∀ i, |e' i| ≤ (B : ℤ) := by
    intro i
    by_cases h : i < m
    · simp only [he', dif_pos h]; exact he _
    · simp only [he', dif_neg h, abs_zero]; positivity
  have hconv : ∀ (f : Fin m → ℤ) (f' : ℕ → ℤ), (f' = fun i => if h : i < m then f ⟨i, h⟩ else 0) →
      ∑ i ∈ Finset.range m, f' i * (q : ℤ) ^ i = ∑ i, f i * (q : ℤ) ^ (i : ℕ) := by
    intro f f' hf
    rw [Finset.sum_range fun i => f' i * (q : ℤ) ^ i]
    exact Finset.sum_congr rfl fun i _ => by simp [hf, i.isLt]
  have hval' : ∑ i ∈ Finset.range m, d' i * (q : ℤ) ^ i =
      ∑ i ∈ Finset.range m, e' i * (q : ℤ) ^ i := by
    rw [hconv d d' hd', hconv e e' he']; exact hval
  funext i
  have := balanced_base_injective_range B q hq m d' e' hd'b he'b hval' i i.isLt
  simpa [hd', he', i.isLt] using this

namespace MaskData

variable (D : MaskData)

/-- In the carry-free base `q = 2B + 1` the difference digits have pairwise distinct residues
modulo `q`; this is the `k = 1` instance of the injectivity used in Proposition 2 of
`masked_digit_bound.tex`. -/
theorem diffSupport_eq_of_dvd_sub (hcarryfree : D.q = 2 * D.B + 1)
    {d e : ℤ} (hd : d ∈ D.diffSupport) (he : e ∈ D.diffSupport)
    (hdvd : ((D.q : ℤ)) ∣ (d - e)) : d = e := by
  have h1 := D.abs_le_of_mem_diffSupport hd
  have h2 := D.abs_le_of_mem_diffSupport he
  rw [abs_le] at h1 h2
  have hq : (D.q : ℤ) = 2 * (D.B : ℤ) + 1 := by rw [hcarryfree]; push_cast; ring
  have habs : |d - e| < (D.q : ℤ) := by
    rw [abs_lt]; omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

/-- **Proposition 2 (Masked-digit bound)** of `masked_digit_bound.tex`, equation (6)
(`eq:masked-bound`): in the carry-free base `Q = 2B + 1`, for every `x ∈ (0, 1)`,
`C₃ₐ ≥ 1 + (log P₋(x) - log P₊(x)) / log(2B + 1)`. -/
theorem masked_digit_bound (hcarryfree : D.q = 2 * D.B + 1) (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) :
    1 + (Real.log (D.Pminus x) - Real.log (D.Pplus x)) / Real.log D.q ≤ C3a := by
  classical
  set A := {d : ℤ // d ∈ D.diffSupport} with hA
  have hne : Nonempty A := ⟨⟨0, D.zero_mem_diffSupport⟩⟩
  set vec : A → Fin 1 → ℤ := fun a _ => (a : ℤ) with hvecdef
  have hvec : ∀ (a : A) (i : Fin 1), vec a i ∈ D.diffSupport := fun a _ => a.2
  set neg : A → A := fun a => ⟨-(a : ℤ), D.neg_mem_diffSupport a.2⟩ with hnegdef
  have hneginv : Function.Involutive neg := by
    intro a; apply Subtype.ext; simp [hnegdef]
  have hnegvec : ∀ a, vec (neg a) = -vec a := by
    intro a; funext i; simp [hvecdef, hnegdef]
  have hblock : ∀ a : A, D.blockVal 1 (vec a) = (a : ℤ) := by
    intro a; simp [blockVal, hvecdef]
  have hinj : Function.Injective fun a : A => ((D.blockVal 1 (vec a) : ℤ) : ZMod (D.q ^ 1)) := by
    intro a b hab
    simp only [hblock] at hab
    have hmod := (ZMod.intCast_eq_intCast_iff' (a : ℤ) (b : ℤ) (D.q ^ 1)).1 hab
    have hdvd : ((D.q : ℤ)) ∣ ((a : ℤ) - (b : ℤ)) := by
      have := Int.ModEq.dvd (Int.ModEq.symm hmod)
      simpa [pow_one] using this
    exact Subtype.ext (D.diffSupport_eq_of_dvd_sub hcarryfree a.2 b.2 hdvd)
  have hcost : ∀ a : A, D.blockCost 1 (vec a) = D.kappa (a : ℤ) := by
    intro a; simp [blockCost, hvecdef]
  have hZ : (∑ a : A, x ^ D.blockCost 1 (vec a)) = D.Pminus x := by
    rw [Pminus]
    rw [Finset.sum_congr rfl (fun a _ => by rw [hcost a] :
      ∀ a ∈ (Finset.univ : Finset A), x ^ D.blockCost 1 (vec a) = x ^ D.kappa (a : ℤ))]
    exact Finset.sum_attach D.diffSupport (fun d => x ^ D.kappa d)
  have := D.core_bound 1 one_pos vec hvec neg hneginv hnegvec hinj x hx0 hx1
    (D.Pplus x) 1 (D.Pplus_pos hx0) one_pos
    (fun m T => by simpa using D.sumSet_card_mul_pow_le x hx0 hx1 m T)
  rw [hZ] at this
  simpa using this

/-! ## Recovery of Zheng's optimization -/

/-- The complete mask `M = {0, 1, …, B}` of the Remark "Recovery of Zheng's optimization"
in `masked_digit_bound.tex`. -/
def completeMask (B : ℕ) (hB : 0 < B) : MaskData where
  B := B
  q := 2 * B + 1
  M := Finset.range (B + 1)
  B_pos := hB
  q_gt_B := by omega
  zero_mem := by simp
  digits_le := by intro a ha; simp at ha; omega
  B_mem := by simp

/-- For the complete mask, the sum support is `{0, 1, …, 2B}`, as recorded in the Remark
"Recovery of Zheng's optimization" of `masked_digit_bound.tex`. -/
theorem completeMask_sumSupport (B : ℕ) (hB : 0 < B) :
    (completeMask B hB).sumSupport = Finset.range (2 * B + 1) := by
  ext s
  simp only [mem_sumSupport, completeMask, Finset.mem_range]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    omega
  · intro hs
    rcases le_or_gt s B with h | h
    · exact ⟨s, by omega, 0, by omega, by omega⟩
    · exact ⟨B, by omega, s - B, by omega, by omega⟩

/-- For the complete mask, the difference support is `{-B, …, B}`, as in the Remark
"Recovery of Zheng's optimization" of `masked_digit_bound.tex`. -/
theorem completeMask_diffSupport (B : ℕ) (hB : 0 < B) :
    (completeMask B hB).diffSupport = Finset.Icc (-(B : ℤ)) (B : ℤ) := by
  ext d
  simp only [mem_diffSupport, completeMask, Finset.mem_Icc]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simp only [Finset.mem_range] at ha hb
    have : (a : ℤ) ≤ B := by exact_mod_cast Nat.lt_succ_iff.1 ha
    have : (b : ℤ) ≤ B := by exact_mod_cast Nat.lt_succ_iff.1 hb
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    rcases le_or_gt 0 d with h | h
    · refine ⟨d.toNat, ?_, 0, by simp, by push_cast; omega⟩
      simp only [Finset.mem_range]
      omega
    · refine ⟨0, by simp, (-d).toNat, ?_, by push_cast; omega⟩
      simp only [Finset.mem_range]
      omega

/-- For the complete mask, `κ(d) = |d|`; this underlies the formula
`P₋(x) = 1 + 2x + ⋯ + 2x^B` in the Remark "Recovery of Zheng's optimization" of
`masked_digit_bound.tex`. -/
theorem completeMask_kappa (B : ℕ) (hB : 0 < B) {d : ℤ} (hd : |d| ≤ (B : ℤ)) :
    ((completeMask B hB).kappa d : ℤ) = |d| := by
  set D := completeMask B hB with hD
  have hdmem : d ∈ D.diffSupport := by
    rw [completeMask_diffSupport B hB]
    rw [abs_le] at hd
    simp only [Finset.mem_Icc]
    exact ⟨hd.1, hd.2⟩
  have hle : (D.kappa d : ℤ) ≤ |d| := by
    rcases le_or_gt 0 d with h | h
    · have h1 : d.toNat ∈ D.M := by
        simp only [hD, completeMask, Finset.mem_range]
        rw [abs_le] at hd; omega
      have := D.kappa_le (d := d) h1 (show (0 : ℕ) ∈ D.M by simp [hD, completeMask])
        (by push_cast; omega)
      have h2 : ((d.toNat + 0 : ℕ) : ℤ) = |d| := by
        rw [abs_of_nonneg h]; push_cast; omega
      calc (D.kappa d : ℤ) ≤ ((d.toNat + 0 : ℕ) : ℤ) := by exact_mod_cast this
        _ = |d| := h2
    · have h1 : (-d).toNat ∈ D.M := by
        simp only [hD, completeMask, Finset.mem_range]
        rw [abs_le] at hd; omega
      have := D.kappa_le (d := d) (show (0 : ℕ) ∈ D.M by simp [hD, completeMask]) h1
        (by push_cast; omega)
      have h2 : ((0 + (-d).toNat : ℕ) : ℤ) = |d| := by
        rw [abs_of_neg h]; push_cast; omega
      calc (D.kappa d : ℤ) ≤ ((0 + (-d).toNat : ℕ) : ℤ) := by exact_mod_cast this
        _ = |d| := h2
  have hge : |d| ≤ (D.kappa d : ℤ) := by
    obtain ⟨a, _, b, _, hab, hsum⟩ := D.exists_min_witness hdmem
    have : |d| = |(a : ℤ) - b| := by rw [hab]
    rw [this, ← hsum]
    push_cast
    rw [abs_le]
    omega
  omega

end MaskData

end MaskedDigit
