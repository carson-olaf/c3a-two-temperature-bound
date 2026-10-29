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
# Counting words with a prescribed type

This file provides the elementary "method of types" counting used in Section 5 of
`masked_digit_bound.tex`, where the number `D_N = N! / (n₀! ∏_{d>0} (n_d!)²)` of signed
difference words with a prescribed symmetric type is required.

Mathlib knows `Nat.multinomial` and the cardinality of the stabilizer of a function under the
permutation action (`DomMulAct.stabilizer_card`), but not the statement that the number of
functions with prescribed fibre sizes is the corresponding multinomial coefficient.  That is
what is proved here:

* `TypeCount.fiberCard g i` is `#{a : g a = i}`;
* `TypeCount.typeSet f` is the set of functions with the same fibre sizes as `f`;
* `TypeCount.card_typeSet_mul_prod_factorial` is the orbit–stabilizer identity
  `|typeSet f| · ∏ᵢ Nat.factorial (fiberCard f i) = (card α)!`;
* `TypeCount.exists_fun_fiberCard` produces a function with any prescribed fibre sizes.
-/

open scoped BigOperators
open Finset

namespace TypeCount

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-- The size of the fibre of `g` over `i`, i.e. the number of positions carrying the
letter `i`. -/
def fiberCard (g : α → ι) (i : ι) : ℕ := (Finset.univ.filter fun a => g a = i).card

omit [DecidableEq α] [Fintype ι] in
theorem fiberCard_eq_card_subtype (g : α → ι) (i : ι) :
    fiberCard g i = Fintype.card {a // g a = i} := by
  rw [fiberCard, Fintype.card_subtype]

/-- The set of words with the same type (fibre sizes) as `f`. -/
def typeSet (f : α → ι) : Finset (α → ι) :=
  Finset.univ.filter fun g => ∀ i, fiberCard g i = fiberCard f i

/-- Membership in the set of words of a fixed type: `g` has the same fibre sizes as `f`.  This is the type class of the method-of-types count used in Section 2 of `masked_digit_bound.tex`. -/
theorem mem_typeSet {f g : α → ι} : g ∈ typeSet f ↔ ∀ i, fiberCard g i = fiberCard f i := by
  simp [typeSet]

omit [DecidableEq α] [Fintype ι] in
/-- Precomposition with a permutation does not change the type. -/
theorem fiberCard_comp (f : α → ι) (sigma : Equiv.Perm α) (i : ι) :
    fiberCard (f ∘ sigma) i = fiberCard f i := by
  classical
  refine Finset.card_bij (fun a _ => sigma a) (fun a ha => ?_) (fun a _ b _ hab => ?_)
    (fun b hb => ?_)
  · simpa [fiberCard] using (Finset.mem_filter.1 ha).2
  · exact sigma.injective hab
  · refine ⟨sigma.symm b, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
      Equiv.apply_symm_apply]
    simpa using (Finset.mem_filter.1 hb).2

omit [DecidableEq α] [Fintype ι] in
/-- **Transitivity of the permutation action on words of a fixed type.** -/
theorem exists_perm_comp {f g : α → ι} (h : ∀ i, fiberCard g i = fiberCard f i) :
    ∃ sigma : Equiv.Perm α, f ∘ sigma = g := by
  classical
  have hcard : ∀ i, Fintype.card {a // g a = i} = Fintype.card {a // f a = i} := by
    intro i
    rw [← fiberCard_eq_card_subtype, ← fiberCard_eq_card_subtype]
    exact h i
  have e : ∀ i, {a // g a = i} ≃ {a // f a = i} := fun i => (Fintype.card_eq.1 (hcard i)).some
  refine ⟨(Equiv.sigmaFiberEquiv g).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv f)), ?_⟩
  funext a
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.sigmaFiberEquiv,
    Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Equiv.sigmaCongrRight_apply]
  exact (e (g a) ⟨a, rfl⟩).2

/-- The words of a fixed type are exactly the permutations of a single one. -/
theorem typeSet_eq_image (f : α → ι) :
    typeSet f = Finset.univ.image fun sigma : Equiv.Perm α => f ∘ sigma := by
  classical
  ext g
  simp only [mem_typeSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · exact fun h => exists_perm_comp h
  · rintro ⟨sigma, rfl⟩ i
    exact fiberCard_comp f sigma i

/-- The number of permutations carrying `f` to a fixed word of the same type is the product of
the factorials of the fibre sizes. -/
theorem card_fiber_perm {f h : α → ι} (hh : h ∈ typeSet f) :
    (Finset.univ.filter fun sigma : Equiv.Perm α => f ∘ sigma = h).card
      = ∏ i, Nat.factorial (fiberCard f i) := by
  classical
  obtain ⟨s0, hs0⟩ := exists_perm_comp (mem_typeSet.1 hh)
  have hbij : (Finset.univ.filter fun sigma : Equiv.Perm α => f ∘ sigma = h).card
      = (Finset.univ.filter fun tau : Equiv.Perm α => h ∘ tau = h).card := by
    refine Finset.card_bij (fun sigma _ => s0⁻¹ * sigma) (fun sigma hsigma => ?_)
      (fun a _ b _ hab => ?_) (fun tau htau => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hsigma ⊢
      funext a
      simp only [Function.comp_apply, Equiv.Perm.mul_apply]
      have h1 : h (s0⁻¹ (sigma a)) = f (s0 (s0⁻¹ (sigma a))) := by
        rw [← hs0]; rfl
      rw [h1, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
      exact congrFun hsigma a
    · have := congrArg (fun x => s0 * x) hab
      simpa [← mul_assoc] using this
    · refine ⟨s0 * tau, ?_, by simp [← mul_assoc]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at htau ⊢
      funext a
      simp only [Function.comp_apply, Equiv.Perm.mul_apply]
      have h1 : f (s0 (tau a)) = h (tau a) := by rw [← hs0]; rfl
      rw [h1]
      exact congrFun htau a
  rw [hbij]
  have hstab : (Finset.univ.filter fun tau : Equiv.Perm α => h ∘ tau = h).card
      = Fintype.card {g : Equiv.Perm α // h ∘ g = h} := (Fintype.card_subtype _).symm
  rw [hstab, DomMulAct.stabilizer_card h]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← fiberCard_eq_card_subtype, mem_typeSet.1 hh i]

/-- **The orbit–stabilizer count of words with a prescribed type**, the combinatorial content
of the multinomial coefficient `D_N` of Section 5 of `masked_digit_bound.tex`. -/
theorem card_typeSet_mul_prod_factorial (f : α → ι) :
    (typeSet f).card * ∏ i, Nat.factorial (fiberCard f i) = Nat.factorial (Fintype.card α) := by
  classical
  have hmaps : ∀ sigma ∈ (Finset.univ : Finset (Equiv.Perm α)), f ∘ sigma ∈ typeSet f := by
    intro sigma _
    exact mem_typeSet.2 fun i => fiberCard_comp f sigma i
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hconst : ∀ h ∈ typeSet f,
      (Finset.univ.filter fun sigma : Equiv.Perm α => f ∘ sigma = h).card
        = ∏ i, Nat.factorial (fiberCard f i) := fun h hh => card_fiber_perm hh
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul] at hsum
  rw [← hsum, Finset.card_univ, Fintype.card_perm]

/-- **Existence of a word with any prescribed type.** -/
theorem exists_fun_fiberCard {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (N : ℕ)
    (hsum : ∑ i, n i = N) : ∃ f : Fin N → ι, ∀ i, fiberCard f i = n i := by
  classical
  have hcard : Fintype.card (Σ i : ι, Fin (n i)) = N := by
    rw [Fintype.card_sigma]
    simpa using hsum
  obtain ⟨e⟩ : Nonempty (Fin N ≃ Σ i : ι, Fin (n i)) :=
    Fintype.card_eq.1 (by rw [hcard, Fintype.card_fin])
  refine ⟨fun t => (e t).1, fun i => ?_⟩
  rw [fiberCard_eq_card_subtype]
  have h1 : Fintype.card {t : Fin N // (e t).1 = i}
      = Fintype.card {s : (Σ i : ι, Fin (n i)) // s.1 = i} :=
    Fintype.card_congr (e.subtypeEquiv fun t => by simp)
  rw [h1]
  rw [Fintype.card_congr (Equiv.subtypeSigmaEquiv (fun j => Fin (n j)) (fun j => j = i))]
  simp
  rfl

end TypeCount
