/-
Copyright (c) 2026 Logan Kleinwaks. All rights reserved.
Released under Apache 2.0 license; see LICENSE-Kleinwaks.
Reused from kleinwaks/masked-digit-sum-difference-bound,
commit 352ab86effecb7efce415507a8c781ec158b86e0.
-/
import RequestProject.CoreConstruction
import RequestProject.MaskedCarryFree
import RequestProject.TypeCount

/-!
# Signed difference words with a prescribed symmetric type

This file formalizes the combinatorial step of Section 5 (\"A direct finite-depth
certificate\") of `masked_digit_bound.tex`:

> There are exactly `D_N = N! / (n₀! ∏_{d>0} (n_d!)²)` signed difference words
> `(d_0, …, d_{N-1})` having the prescribed counts.  Because `n_d = n_{-d}`, each such word
> satisfies `∑ᵢ dᵢ = 0`.  Replacing each `dᵢ` by its fixed witness `α_{dᵢ} - β_{dᵢ}` gives two
> mask words […] whose digit sums are both `L`.  They therefore encode two members of `U`,
> whose difference is `∑ᵢ dᵢ Qⁱ`.  Finally, the carry-free injectivity implies that two
> different signed words produce two different integers, so these `D_N` words give `D_N`
> distinct elements of `U - U`.

The main result is `MaskedDigit.MaskData.typeWords_card_le_natDiffFinset`, stated for an
arbitrary carry-free `MaskData` and an arbitrary symmetric type `n : ℤ → ℕ`.
-/

open scoped BigOperators

namespace TypeCount

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

omit [DecidableEq α] in
/-- An additive statistic of a word is the sum over letters of the statistic weighted by the
fibre sizes.  This is the elementary "method of types" bookkeeping used in Section 5 of
`masked_digit_bound.tex`. -/
theorem sum_comp_fiberCard {M : Type*} [AddCommMonoid M] (g : α → ι) (F : ι → M) :
    ∑ a, F (g a) = ∑ i, fiberCard g i • F i := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset α) g (fun a => F (g a))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F i)
      (fun a ha => by rw [(Finset.mem_filter.1 ha).2]), Finset.sum_const, fiberCard]

end TypeCount

namespace MaskedDigit

namespace MaskData

variable (D : MaskData)

/-! ## Splitting the difference support into `0` and `± d` -/

/-- The difference support `D = M - M` splits as `{0}` together with the pairs `{d, -d}` for
`d > 0`; this is the symmetry `n_{-d} = n_d` bookkeeping of Section 5 of
`masked_digit_bound.tex`, in multiplicative form. -/
@[to_additive /-- The difference support `D = M - M` splits as `{0}` together with the pairs
`{d, -d}` for `d > 0`; this is the symmetry `n_{-d} = n_d` bookkeeping of Section 5 of
`masked_digit_bound.tex`. -/]
theorem prod_diffSupport_symm {M : Type*} [CommMonoid M] (F : ℤ → M) :
    ∏ d ∈ D.diffSupport, F d
      = F 0 * ∏ d ∈ D.diffSupport.filter (fun d => 0 < d), (F d * F (-d)) := by
  classical
  have hsplit := Finset.prod_filter_mul_prod_filter_not D.diffSupport (fun d => 0 < d) F
  have hneg : D.diffSupport.filter (fun d => ¬ 0 < d)
      = insert 0 (D.diffSupport.filter (fun d => d < 0)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_insert, not_lt]
    constructor
    · rintro ⟨hd, hle⟩
      rcases lt_or_eq_of_le hle with h | h
      · exact Or.inr ⟨hd, h⟩
      · exact Or.inl h
    · rintro (rfl | ⟨hd, hlt⟩)
      · exact ⟨D.zero_mem_diffSupport, le_refl _⟩
      · exact ⟨hd, hlt.le⟩
  have hzero : (0 : ℤ) ∉ D.diffSupport.filter (fun d => d < 0) := by
    simp
  have hnegprod : ∏ d ∈ D.diffSupport.filter (fun d => d < 0), F d
      = ∏ d ∈ D.diffSupport.filter (fun d => 0 < d), F (-d) := by
    refine (Finset.prod_nbij' (fun d => -d) (fun d => -d) ?_ ?_ ?_ ?_ ?_).symm
    · intro a ha
      simp only [Finset.mem_filter] at ha ⊢
      exact ⟨D.neg_mem_diffSupport ha.1, by omega⟩
    · intro a ha
      simp only [Finset.mem_filter] at ha ⊢
      exact ⟨D.neg_mem_diffSupport ha.1, by omega⟩
    · intro a _; ring
    · intro a _; ring
    · intro a _; rfl
  rw [← hsplit, hneg, Finset.prod_insert hzero, hnegprod, Finset.prod_mul_distrib,
    mul_left_comm]

/-- For a symmetric type `n_{-d} = n_d`, the signed digit sum `∑_d n_d d` vanishes; this is
the observation "because `n_d = n_{-d}`, each such word satisfies `∑ᵢ dᵢ = 0`" of Section 5 of
`masked_digit_bound.tex`. -/
theorem sum_nsmul_diffSupport_eq_zero (n : ℤ → ℕ) (hsymm : ∀ d, n (-d) = n d) :
    ∑ d ∈ D.diffSupport, (n d) • d = (0 : ℤ) := by
  rw [D.sum_diffSupport_symm (fun d => (n d) • d)]
  have : ∀ d ∈ D.diffSupport.filter (fun d => 0 < d),
      (n d) • d + (n (-d)) • (-d) = (0 : ℤ) := by
    intro d _
    rw [hsymm d]
    simp
  rw [Finset.sum_congr rfl this]
  simp

/-! ## The words of a prescribed type -/

/-- An additive statistic of a signed difference word of prescribed type `n` is the
corresponding weighted sum over the difference support. -/
theorem sum_word_stat {M : Type*} [AddCommMonoid M] {N : ℕ}
    (g : Fin N → {d : ℤ // d ∈ D.diffSupport}) (n : ℤ → ℕ)
    (hfib : ∀ i, TypeCount.fiberCard g i = n (i : ℤ)) (F : ℤ → M) :
    ∑ t, F ((g t : ℤ)) = ∑ d ∈ D.diffSupport, (n d) • F d := by
  classical
  rw [TypeCount.sum_comp_fiberCard g (fun i => F (i : ℤ))]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hfib i])]
  exact Finset.sum_coe_sort D.diffSupport (fun d => (n d) • F d)

/-- **The difference count of Section 5 of `masked_digit_bound.tex`.**  In the carry-free base
`q = 2B + 1`, given a symmetric type `n` on the difference support with `∑_d n_d = N` and
`∑_d n_d κ(d) = 2L`, the multinomial number `N! / ∏_d n_d!` of signed difference words with
that type is a lower bound for `|U - U|`, where `U = U_N(L)` is the masked digit set of
equation (8) (`eq:Um`).

The proof is the one given in Section 5: each word is turned into a pair of mask words through
the minimum witnesses `(α_d, β_d)`, both of digit sum exactly `L`, and the carry-free
injectivity shows that distinct words give distinct differences. -/
theorem typeWords_card_le_natDiffFinset (hcf : D.q = 2 * D.B + 1) (n : ℤ → ℕ) (N L : ℕ)
    (hsymm : ∀ d, n (-d) = n d)
    (hN : ∑ d ∈ D.diffSupport, n d = N)
    (hL : ∑ d ∈ D.diffSupport, n d * D.kappa d = 2 * L)
    (DN : ℕ) (hDN : DN * (∏ d ∈ D.diffSupport, Nat.factorial (n d)) = Nat.factorial N) :
    DN ≤ (natDiffFinset (D.maskSet N L) (D.maskSet N L)).card := by
  classical
  -- a word of the prescribed type exists
  have hsum' : ∑ i : {d : ℤ // d ∈ D.diffSupport}, n (i : ℤ) = N := by
    rw [Finset.sum_coe_sort D.diffSupport n]; exact hN
  obtain ⟨f, hf⟩ := TypeCount.exists_fun_fiberCard (fun i : {d : ℤ // d ∈ D.diffSupport} =>
    n (i : ℤ)) N hsum'
  -- the multinomial count is the cardinality of the set of words of that type
  have hprod : ∏ i : {d : ℤ // d ∈ D.diffSupport}, Nat.factorial (TypeCount.fiberCard f i)
      = ∏ d ∈ D.diffSupport, Nat.factorial (n d) := by
    rw [Finset.prod_congr rfl (fun i _ => by rw [hf i])]
    exact Finset.prod_coe_sort D.diffSupport (fun d => Nat.factorial (n d))
  have hcard := TypeCount.card_typeSet_mul_prod_factorial f
  rw [Fintype.card_fin, hprod] at hcard
  have hpos : 0 < ∏ d ∈ D.diffSupport, Nat.factorial (n d) :=
    Finset.prod_pos fun d _ => Nat.factorial_pos _
  have hDNcard : DN = (TypeCount.typeSet f).card :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [hDN, hcard])
  rw [hDNcard]
  -- the map sending a word to the integer it represents
  refine Finset.card_le_card_of_injOn
    (fun g => ∑ t, ((g t : ℤ)) * (D.q : ℤ) ^ (t : ℕ)) ?_ ?_
  · -- every word of the prescribed type represents an element of `U - U`
    intro g hg
    have hfib : ∀ i, TypeCount.fiberCard g i = n (i : ℤ) := fun i =>
      (TypeCount.mem_typeSet.1 (by simpa using hg) i).trans (hf i)
    set alpha : Fin N → ℕ := fun t => (D.wit ((g t : ℤ))).1 with halpha
    set beta : Fin N → ℕ := fun t => (D.wit ((g t : ℤ))).2 with hbeta
    have hamem : ∀ t, alpha t ∈ D.M := fun t => D.wit_fst_mem (g t).2
    have hbmem : ∀ t, beta t ∈ D.M := fun t => D.wit_snd_mem (g t).2
    -- the two digit budgets
    have hcostsum : (∑ t, alpha t) + (∑ t, beta t) = 2 * L := by
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun t _ => D.wit_add (g t).2)]
      rw [D.sum_word_stat g n hfib (fun d => D.kappa d)]
      simpa [smul_eq_mul] using hL
    have hdiffsum : ((∑ t, alpha t : ℕ) : ℤ) - ((∑ t, beta t : ℕ) : ℤ) = 0 := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl (fun t _ => D.wit_sub (g t).2)]
      rw [D.sum_word_stat g n hfib (fun d => d)]
      exact D.sum_nsmul_diffSupport_eq_zero n hsymm
    have hAL : (∑ t, alpha t) = L := by omega
    have hBL : (∑ t, beta t) = L := by omega
    -- the two mask words
    have hAmem : D.flatInt N alpha ∈ D.maskSet N L :=
      D.flatInt_mem_maskSet alpha hamem (le_of_eq hAL)
    have hBmem : D.flatInt N beta ∈ D.maskSet N L :=
      D.flatInt_mem_maskSet beta hbmem (le_of_eq hBL)
    have hval : ((D.flatInt N alpha : ℕ) : ℤ) - ((D.flatInt N beta : ℕ) : ℤ)
        = ∑ t, ((g t : ℤ)) * (D.q : ℤ) ^ (t : ℕ) := by
      rw [D.flatInt_cast, D.flatInt_cast, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← sub_mul, D.wit_sub (g t).2]
    simp only [natDiffFinset, Finset.mem_coe]
    rw [← hval]
    exact Finset.mem_image₂_of_mem (f := fun (a b : ℕ) => (a : ℤ) - (b : ℤ)) hAmem hBmem
  · -- distinct words give distinct integers
    intro g _ g' _ hgg
    have hb : ∀ t : Fin N, |((g t : ℤ))| ≤ (D.B : ℤ) := fun t =>
      D.abs_le_of_mem_diffSupport (g t).2
    have hb' : ∀ t : Fin N, |((g' t : ℤ))| ≤ (D.B : ℤ) := fun t =>
      D.abs_le_of_mem_diffSupport (g' t).2
    have := balanced_base_injective D.B D.q N hcf (fun t => (g t : ℤ)) (fun t => (g' t : ℤ))
      hb hb' hgg
    funext t
    exact Subtype.ext (congrFun this t)

end MaskData

end MaskedDigit
