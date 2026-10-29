/-
Copyright (c) 2026 Carson Olafson. Released under Apache 2.0.
Author: Carson Olafson, with GPT-6 Astra assistance.
Weighted counting proof adapted from Logan Kleinwaks, CoreConstruction.lean,
Apache-2.0; see LICENSE-Kleinwaks.
-/
import RequestProject.FiniteTypeWords

/-! # Finite vector words with a digit budget -/
open scoped BigOperators Pointwise
open Finset

namespace C3a

/-- Words in a finite alphabet satisfying a total cost bound. -/
noncomputable def boundedWords {α : Type*} [DecidableEq α]
    (s : Finset α) (cost : α → ℕ) (N L : ℕ) : Finset (Fin N → α) :=
  ((univ : Finset (Fin N → s)).filter (fun a => ∑ i, cost (a i) ≤ L)).image
    (fun a i => (a i : α))

theorem mem_boundedWords {α : Type*} [DecidableEq α]
    (s : Finset α) (cost : α → ℕ) (N L : ℕ) (a : Fin N → α) :
    a ∈ boundedWords s cost N L ↔ (∀ i, a i ∈ s) ∧ ∑ i, cost (a i) ≤ L := by
  classical
  constructor
  · intro h
    obtain ⟨b, hb, rfl⟩ := mem_image.mp h
    exact ⟨fun i => (b i).property, (mem_filter.mp hb).2⟩
  · rintro ⟨ha, hL⟩
    exact mem_image.mpr ⟨(fun i => ⟨a i, ha i⟩), mem_filter.mpr ⟨mem_univ _, hL⟩, rfl⟩

/-- A weighted count with an arbitrary finite alphabet and integer cost. -/
theorem boundedWords_card_mul_pow_le {α : Type*} [DecidableEq α]
    (s : Finset α) (cost : α → ℕ) (N L : ℕ)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ((boundedWords s cost N L).card : ℝ) * x ^ L ≤
      (∑ a ∈ s, x ^ cost a) ^ N := by
  classical
  let W := (univ : Finset (Fin N → s)).filter (fun a => ∑ i, cost (a i) ≤ L)
  have hcard : ((boundedWords s cost N L).card : ℝ) ≤ (W.card : ℝ) := by
    exact_mod_cast (card_image_le (s := W) (f := fun a i => (a i : α)))
  calc
    ((boundedWords s cost N L).card : ℝ) * x ^ L ≤ (W.card : ℝ) * x ^ L :=
      mul_le_mul_of_nonneg_right hcard (pow_nonneg hx0.le _)
    _ = ∑ _a ∈ W, x ^ L := by simp
    _ ≤ ∑ a ∈ W, x ^ (∑ i, cost (a i)) := by
      apply sum_le_sum
      intro a ha
      exact pow_le_pow_of_le_one hx0.le hx1.le (mem_filter.mp ha).2
    _ ≤ ∑ a : Fin N → s, x ^ (∑ i, cost (a i)) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro a _ _
      positivity
    _ = (∑ a ∈ s, x ^ cost a) ^ N := by
      rw [← sum_coe_sort s (fun a => x ^ cost a)]
      have hp : (∑ a : s, x ^ cost a) ^ N = ∏ _i : Fin N, (∑ a : s, x ^ cost a) := by simp
      rw [hp, Fintype.prod_sum]
      apply sum_congr rfl
      intro a ha
      exact (prod_pow_eq_pow_sum _ _ _).symm

namespace Vectors

variable (D : MaskedDigit.MaskData)

/-- Integer-valued version of the inner mask alphabet. -/
def alphabet : Finset ℤ := D.M.image (fun a : ℕ => (a : ℤ))

/-- The finite vector set to be compressed. -/
noncomputable def V (N L : ℕ) : Finset (Fin N → ℤ) :=
  boundedWords (alphabet D) Int.toNat N L

theorem mem_V (N L : ℕ) (a : Fin N → ℤ) :
    a ∈ V D N L ↔ (∀ i, a i ∈ alphabet D) ∧ ∑ i, (a i).toNat ≤ L :=
  mem_boundedWords _ _ _ _ _

theorem alphabet_nonneg {a : ℤ} (ha : a ∈ alphabet D) : 0 ≤ a := by
  obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
  exact Int.natCast_nonneg _

theorem alphabet_toNat {a : ℤ} (ha : a ∈ alphabet D) : a.toNat ∈ D.M := by
  obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
  simpa using hn

theorem zero_mem_V (N L : ℕ) : 0 ∈ V D N L := by
  rw [mem_V]
  constructor
  · intro i
    exact mem_image.mpr ⟨0, D.zero_mem, rfl⟩
  · simp

theorem diff_subset (N L : ℕ) :
    V D N L - V D N L ⊆ boundedWords D.diffSupport D.kappa N (2 * L) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sub.mp hz
  obtain ⟨ha, hLa⟩ := (mem_V D N L a).mp ha
  obtain ⟨hb, hLb⟩ := (mem_V D N L b).mp hb
  rw [mem_boundedWords]
  constructor
  · intro i
    exact D.mem_diffSupport.mpr ⟨(a i).toNat, alphabet_toNat D (ha i),
      (b i).toNat, alphabet_toNat D (hb i), by
        simp [Int.toNat_of_nonneg (alphabet_nonneg D (ha i)),
          Int.toNat_of_nonneg (alphabet_nonneg D (hb i))]⟩
  · have h := sum_le_sum (s := (univ : Finset (Fin N))) (fun i _ =>
        D.kappa_le (alphabet_toNat D (ha i)) (alphabet_toNat D (hb i))
          (show ((a i).toNat : ℤ) - (b i).toNat = (a - b) i by
            simp [Int.toNat_of_nonneg (alphabet_nonneg D (ha i)),
              Int.toNat_of_nonneg (alphabet_nonneg D (hb i))]))
    rw [sum_add_distrib] at h
    omega

theorem sum_subset (N L : ℕ) :
    V D N L + V D N L ⊆
      boundedWords (D.sumSupport.image (fun a : ℕ => (a : ℤ))) Int.toNat N (2 * L) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hz
  obtain ⟨ha, hLa⟩ := (mem_V D N L a).mp ha
  obtain ⟨hb, hLb⟩ := (mem_V D N L b).mp hb
  have hab (i : Fin N) : (a i + b i).toNat = (a i).toNat + (b i).toNat :=
    Int.toNat_add (alphabet_nonneg D (ha i)) (alphabet_nonneg D (hb i))
  rw [mem_boundedWords]
  constructor
  · intro i
    refine mem_image.mpr ⟨(a i).toNat + (b i).toNat,
      D.mem_sumSupport.mpr ⟨_, alphabet_toNat D (ha i), _, alphabet_toNat D (hb i), rfl⟩, ?_⟩
    simp [Int.toNat_of_nonneg (alphabet_nonneg D (ha i)),
      Int.toNat_of_nonneg (alphabet_nonneg D (hb i))]
  · simp only [Pi.add_apply, hab, sum_add_distrib]
    omega

theorem diff_card_weighted (N L : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ((V D N L - V D N L).card : ℝ) * x ^ (2 * L) ≤ D.Pminus x ^ N := by
  have hc : ((V D N L - V D N L).card : ℝ) ≤
      ((boundedWords D.diffSupport D.kappa N (2 * L)).card : ℝ) := by
    exact_mod_cast card_le_card (diff_subset D N L)
  exact (mul_le_mul_of_nonneg_right hc (pow_nonneg hx0.le _)).trans
    (boundedWords_card_mul_pow_le _ _ _ _ x hx0 hx1)

theorem sum_card_weighted (N L : ℕ) (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    ((V D N L + V D N L).card : ℝ) * y ^ (2 * L) ≤ D.Pplus y ^ N := by
  have hc : ((V D N L + V D N L).card : ℝ) ≤
      ((boundedWords (D.sumSupport.image (fun a : ℕ => (a : ℤ))) Int.toNat N (2 * L)).card : ℝ) := by
    exact_mod_cast card_le_card (sum_subset D N L)
  have hp : (∑ a ∈ D.sumSupport.image (fun a : ℕ => (a : ℤ)), y ^ a.toNat) = D.Pplus y := by
    rw [sum_image]
    · simp [MaskedDigit.MaskData.Pplus]
    · intro a _ b _ h
      change (a : ℤ) = (b : ℤ) at h
      omega
  have h := boundedWords_card_mul_pow_le
    (D.sumSupport.image (fun a : ℕ => (a : ℤ))) Int.toNat N (2 * L) y hy0 hy1
  rw [hp] at h
  exact (mul_le_mul_of_nonneg_right hc (pow_nonneg hy0.le _)).trans h

/-- A symmetric type supplies a finite family of differences with its exact
multinomial cardinality. Adapted from Kleinwaks's finite type-word proof. -/
theorem exists_type_family (n : ℤ → ℕ) (N L : ℕ)
    (hsymm : ∀ d, n (-d) = n d)
    (hN : ∑ d ∈ D.diffSupport, n d = N)
    (hL : ∑ d ∈ D.diffSupport, n d * D.kappa d = 2 * L) :
    ∃ W : Finset (Fin N → ℤ), W ⊆ V D N L - V D N L ∧
      W.card * (∏ d ∈ D.diffSupport, Nat.factorial (n d)) = Nat.factorial N ∧
      (∀ w ∈ W, ∀ i, |w i| ≤ (D.B : ℤ)) := by
  classical
  have hsum : ∑ i : D.diffSupport, n (i : ℤ) = N := by
    rw [sum_coe_sort]; exact hN
  obtain ⟨f, hf⟩ := TypeCount.exists_fun_fiberCard (fun i : D.diffSupport => n i) N hsum
  let W := (TypeCount.typeSet f).image (fun g i => (g i : ℤ))
  refine ⟨W, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hw
    have hfib : ∀ i, TypeCount.fiberCard g i = n (i : ℤ) := fun i =>
      (TypeCount.mem_typeSet.mp hg i).trans (hf i)
    let a : Fin N → ℕ := fun i => (D.wit (g i)).1
    let b : Fin N → ℕ := fun i => (D.wit (g i)).2
    have ha (i) : a i ∈ D.M := D.wit_fst_mem (g i).property
    have hb (i) : b i ∈ D.M := D.wit_snd_mem (g i).property
    have hab : (∑ i, a i) + (∑ i, b i) = 2 * L := by
      rw [← sum_add_distrib]
      rw [sum_congr rfl (fun i _ => D.wit_add (g i).property)]
      rw [D.sum_word_stat g n hfib (fun d => D.kappa d)]
      simpa [smul_eq_mul] using hL
    have hzero : ((∑ i, a i : ℕ) : ℤ) - ((∑ i, b i : ℕ) : ℤ) = 0 := by
      push_cast
      rw [← sum_sub_distrib]
      rw [sum_congr rfl (fun i _ => D.wit_sub (g i).property)]
      rw [D.sum_word_stat g n hfib (fun d => d)]
      exact D.sum_nsmul_diffSupport_eq_zero n hsymm
    have hAL : (∑ i, a i) = L := by omega
    have hBL : (∑ i, b i) = L := by omega
    refine mem_sub.mpr ⟨(fun i => (a i : ℤ)), ?_, (fun i => (b i : ℤ)), ?_, ?_⟩
    · rw [mem_V]
      exact ⟨fun i => mem_image.mpr ⟨a i, ha i, rfl⟩, by simpa using hAL.le⟩
    · rw [mem_V]
      exact ⟨fun i => mem_image.mpr ⟨b i, hb i, rfl⟩, by simpa using hBL.le⟩
    · funext i
      exact D.wit_sub (g i).property
  · have hcard : W.card = (TypeCount.typeSet f).card := by
      apply card_image_of_injective
      intro g g' h
      funext i
      exact Subtype.ext (congrFun h i)
    rw [hcard]
    have h := TypeCount.card_typeSet_mul_prod_factorial f
    simp only [Fintype.card_fin] at h
    rw [prod_congr rfl (fun i _ => congrArg Nat.factorial (hf i))] at h
    rw [show (∏ i : D.diffSupport, (n (i : ℤ)).factorial) =
      ∏ d ∈ D.diffSupport, (n d).factorial from
      prod_coe_sort D.diffSupport (fun d => (n d).factorial)] at h
    exact h
  · intro w hw i
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hw
    exact D.abs_le_of_mem_diffSupport (g i).property

end Vectors
end C3a
