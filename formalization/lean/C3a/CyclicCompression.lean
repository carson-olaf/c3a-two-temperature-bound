/-
Copyright (c) 2026 Carson Olafson. Released under Apache 2.0.
Author: Carson Olafson, with GPT-6 Astra assistance.
-/
import Mathlib

/-! # Finite-field compression by averaging collisions

The probabilistic step of Lemma 2.1 is expressed as finite counting. No
probability or unverified random-number generator enters the proof.
-/
open scoped BigOperators
open Finset

namespace C3a

/-- Ordered collision count, including diagonal pairs. -/
def energy {α β : Type*} [DecidableEq β] (W : Finset α) (f : α → β) : ℕ :=
  ∑ a ∈ W, ∑ b ∈ W, if f a = f b then 1 else 0

/-- Cauchy--Schwarz bounds the number of points lost by any map. -/
theorem card_sq_le_image_mul_energy {α β : Type*} [DecidableEq α] [DecidableEq β]
    (W : Finset α) (f : α → β) :
    W.card ^ 2 ≤ (W.image f).card * energy W f := by
  classical
  let n : β → ℕ := fun y => (W.filter fun a => f a = y).card
  have hn : ∑ y ∈ W.image f, n y = W.card :=
    (Finset.card_eq_sum_card_image f W).symm
  have he : energy W f = ∑ y ∈ W.image f, n y ^ 2 := by
    unfold energy
    calc
      (∑ a ∈ W, ∑ b ∈ W, if f a = f b then 1 else 0)
          = ∑ a ∈ W, n (f a) := by
            apply sum_congr rfl
            intro a ha
            simp only [n, card_eq_sum_ones, sum_filter, eq_comm]
      _ = ∑ y ∈ W.image f, ∑ a ∈ W with f a = y, n (f a) :=
        (sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem f ha) _).symm
      _ = ∑ y ∈ W.image f, n y ^ 2 := by
        apply sum_congr rfl
        intro y hy
        rw [sum_congr rfl (fun a ha => congrArg n (mem_filter.mp ha).2)]
        simp [n, pow_two]
  have h := sum_mul_sq_le_sq_mul_sq (W.image f) (fun _ => (1 : ℕ)) n
  simpa [hn, ← he] using h

/-- A linear functional determined by a vector. -/
def dotHom {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] (w : ι → F) : (ι → F) →+ F where
  toFun c := ∑ i, c i * w i
  map_zero' := by simp
  map_add' := by intro a b; simp [add_mul, sum_add_distrib]

/-- A nonzero coordinate makes the functional surjective. -/
theorem dotHom_surjective {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (w : ι → F) (hw : w ≠ 0) : Function.Surjective (dotHom w) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (funext h)
  intro y
  refine ⟨Pi.single j (y / w j), ?_⟩
  simp [dotHom, Pi.single_apply, hj]

/-- Each fiber of a surjective additive homomorphism has the same size. -/
theorem card_fiber_mul {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (univ.filter fun a => f a = y).card * Fintype.card H = Fintype.card G := by
  classical
  have heq (z : H) : (univ.filter fun a => f a = z).card =
      (univ.filter fun a => f a = y).card := by
    simpa only [Fintype.card_subtype, Set.mem_preimage, Set.mem_singleton_iff] using
      Fintype.card_congr (AddMonoidHom.fiberEquivOfSurjective hf z y)
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset G))
    (t := (univ : Finset H)) (f := f) (fun a _ => mem_univ (f a))
  rw [sum_congr rfl (fun z _ => heq z), sum_const] at h
  simpa [mul_comm] using h.symm

/-- Exact collision count for a pair of distinct vectors. -/
theorem dot_collision_count {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F]
    [DecidableEq F] (a b : ι → F) (hab : a ≠ b) :
    (univ.filter fun c => dotHom a c = dotHom b c).card * Fintype.card F =
      Fintype.card (ι → F) := by
  classical
  have hn : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h := card_fiber_mul (dotHom (a - b)) (dotHom_surjective _ hn) 0
  convert h using 2
  congr 1
  ext c
  simp [dotHom, mul_sub, sum_sub_distrib, sub_eq_zero]

/-- There is a linear functional with fewer than twice as many ordered
collisions as points, if the field is larger than the set. -/
theorem exists_low_energy {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F]
    [DecidableEq F] (W : Finset (ι → F)) (hW : W.Nonempty)
    (hcard : W.card < Fintype.card F) :
    ∃ c : ι → F, energy W (fun w => dotHom w c) < 2 * W.card := by
  classical
  let q := Fintype.card F
  let P := Fintype.card (ι → F)
  have hq : 0 < q := Fintype.card_pos
  have hP : 0 < P := Fintype.card_pos
  have hpair (a b : ι → F) :
      (∑ c : ι → F, if dotHom a c = dotHom b c then 1 else 0) * q =
        P + if a = b then P * (q - 1) else 0 := by
    by_cases hab : a = b
    · subst b
      simp only [ite_true, sum_const, card_univ, nsmul_eq_mul, mul_one]
      change P * q = P + P * (q - 1)
      have : q - 1 + 1 = q := Nat.sub_add_cancel hq
      nlinarith
    · have h := dot_collision_count a b hab
      rw [show (univ.filter fun c => dotHom a c = dotHom b c).card =
          ∑ c : ι → F, if dotHom a c = dotHom b c then 1 else 0 by
        simp only [card_eq_sum_ones, sum_filter]] at h
      simpa [hab, P, q] using h
  have hsum : (∑ c : ι → F, energy W (fun w => dotHom w c)) * q =
      W.card * (W.card * P + P * (q - 1)) := by
    simp only [energy, sum_mul]
    rw [sum_comm]
    calc
      (∑ a ∈ W, ∑ c : ι → F, ∑ b ∈ W,
          (if dotHom a c = dotHom b c then 1 else 0) * q)
          = ∑ a ∈ W, ∑ b ∈ W, (P + if a = b then P * (q - 1) else 0) := by
            apply sum_congr rfl
            intro a ha
            rw [sum_comm]
            apply sum_congr rfl
            intro b hb
            simpa only [sum_mul] using hpair a b
      _ = W.card * (W.card * P + P * (q - 1)) := by
        simp [sum_add_distrib, sum_ite_eq, mul_comm, mul_add]
  have hsmall : ∑ c : ι → F, energy W (fun w => dotHom w c) <
      ∑ _c : ι → F, 2 * W.card := by
    simp only [sum_const, card_univ, nsmul_eq_mul]
    apply (Nat.mul_lt_mul_right hq).mp
    rw [hsum]
    have hW0 : 0 < W.card := card_pos.mpr hW
    have ht : W.card + (q - 1) < 2 * q := by dsimp [q] at *; omega
    have hm := Nat.mul_lt_mul_of_pos_left ht (Nat.mul_pos hW0 hP)
    dsimp [P] at *
    nlinarith
  obtain ⟨c, _, hc⟩ := exists_lt_of_sum_lt hsmall
  exact ⟨c, hc⟩

/-- The finite-field form of the compression step: more than half the
points survive under some linear functional. -/
theorem exists_large_dot_image {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F]
    [DecidableEq F] (W : Finset (ι → F)) (hW : W.Nonempty)
    (hcard : W.card < Fintype.card F) :
    ∃ c : ι → F, W.card < 2 * (W.image (fun w => dotHom w c)).card := by
  classical
  obtain ⟨c, hc⟩ := exists_low_energy W hW hcard
  refine ⟨c, ?_⟩
  have hcs := card_sq_le_image_mul_energy W (fun w => dotHom w c)
  have hi : 0 < (W.image (fun w => dotHom w c)).card := card_pos.mpr (hW.image _)
  have hmul := Nat.mul_lt_mul_of_pos_left hc hi
  have hW0 : 0 < W.card := card_pos.mpr hW
  nlinarith

end C3a
