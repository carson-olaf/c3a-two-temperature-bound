/-
Copyright (c) 2026 Logan Kleinwaks. All rights reserved.
Released under Apache 2.0 license; see LICENSE-Kleinwaks.
Reused from kleinwaks/masked-digit-sum-difference-bound,
commit 352ab86effecb7efce415507a8c781ec158b86e0.
-/
import Mathlib

/-!
# The base-`q` digit construction behind the Gyarmati--Hennecart--Ruzsa finite-set principle

This file provides the combinatorial input needed to prove the finite-set principle,
equation (1) (`eq:GHR`) of `masked_digit_bound.tex`, which that source quotes from
[GHR2007] (K. Gyarmati, F. Hennecart, I. Z. Ruzsa, *Sums and differences of finite sets*).

The construction is the one used in the proof of the Lemma of Section 2 of [GHR2007]:
given a finite set `U ⊆ {0, 1, …, a}` of nonnegative integers and `q = 2a + 1`, one forms
the set of all `q`-adic digit strings of length `k` with digits in `U`,
`B = { u₀ + u₁ q + ⋯ + u_{k-1} q^{k-1} : u_j ∈ U }`.
Because `2a < q`, no carries occur, so `|B + B| = |U + U| ^ k` and `|B - B| = |U - U| ^ k`.

The file contains:

* `MaskedDigit.Digits.digitSet` — the set `B` above, defined by recursion on `k`;
* `MaskedDigit.Digits.digitSet_add`, `digitSet_sub` — the carry-free identities
  `B(S) + B(T) = B(S + T)` and `B(S) - B(T) = B(S - T)`;
* `MaskedDigit.Digits.card_digitSet` — `|B(S)| = |S| ^ k` for `q`-separated `S`;
* `MaskedDigit.Digits.bigA` — the set `A = [1, L] ∪ ⋃_{i=1}^m (L + i q^k + B)` of the
  construction, together with the estimates for `|A|`, `|A + B|` and `|A - B|`.
-/

open scoped Pointwise

namespace MaskedDigit.Digits

/-! ## `q`-separated sets -/

/-- A finite set of integers is `q`-*separated* when distinct elements are incongruent
modulo `q`.  This is the property that makes the base-`q` digit expansion of
`digitSet` unique. -/
def Sep (q : ℤ) (S : Finset ℤ) : Prop := ∀ a ∈ S, ∀ b ∈ S, q ∣ (a - b) → a = b

/-- A set contained in an interval of length `q` is `q`-separated. -/
theorem sep_of_bounded {q : ℤ} {S : Finset ℤ} {lo : ℤ}
    (h : ∀ x ∈ S, lo ≤ x ∧ x < lo + q) : Sep q S := by
  intro x hx y hy hdvd
  obtain ⟨hx1, hx2⟩ := h x hx
  obtain ⟨hy1, hy2⟩ := h y hy
  obtain ⟨c, hc⟩ := hdvd
  have hq : 0 < q := by omega
  have hc0 : c = 0 := by
    rcases lt_trichotomy c 0 with hlt | heq | hgt
    · have : q * c ≤ -q := by nlinarith
      omega
    · exact heq
    · have : q ≤ q * c := by nlinarith
      omega
  rw [hc0, mul_zero] at hc
  omega

/-! ## The digit set -/

/-- The set of `q`-adic digit strings of length `k` with digits in `S`:
`digitSet S q k = { u₀ + u₁ q + ⋯ + u_{k-1} q^{k-1} : u_j ∈ S }`.  For `S = U` a set of
digits in `{0, …, (q-1)/2}` this is the set `B` of the proof of the Lemma of Section 2 of
[GHR2007], quoted as equation (1) in `masked_digit_bound.tex`. -/
def digitSet (S : Finset ℤ) (q : ℤ) : ℕ → Finset ℤ
  | 0 => {0}
  | (k + 1) => Finset.image₂ (fun u b => u + q * b) S (digitSet S q k)

@[simp] theorem digitSet_zero (S : Finset ℤ) (q : ℤ) : digitSet S q 0 = {0} := rfl

theorem digitSet_succ (S : Finset ℤ) (q : ℤ) (k : ℕ) :
    digitSet S q (k + 1) = Finset.image₂ (fun u b => u + q * b) S (digitSet S q k) := rfl

theorem mem_digitSet_succ {S : Finset ℤ} {q : ℤ} {k : ℕ} {x : ℤ} :
    x ∈ digitSet S q (k + 1) ↔ ∃ u ∈ S, ∃ b ∈ digitSet S q k, u + q * b = x := by
  rw [digitSet_succ]
  simp [Finset.mem_image₂]

/-- The digit set of a nonempty digit alphabet is nonempty. -/
theorem digitSet_nonempty {S : Finset ℤ} (hS : S.Nonempty) (q : ℤ) (k : ℕ) :
    (digitSet S q k).Nonempty := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
      obtain ⟨u, hu⟩ := hS
      obtain ⟨b, hb⟩ := ih
      exact ⟨u + q * b, mem_digitSet_succ.2 ⟨u, hu, b, hb, rfl⟩⟩

/-- **Carry-free addition.**  Adding two digit strings adds the digits: no carry occurs
because the digit alphabet `S + T` still fits in one digit. -/
theorem digitSet_add (S T : Finset ℤ) (q : ℤ) (k : ℕ) :
    digitSet S q k + digitSet T q k = digitSet (S + T) q k := by
  induction k with
  | zero => simp [digitSet]
  | succ k ih =>
      ext x
      simp only [Finset.mem_add, mem_digitSet_succ]
      constructor
      · rintro ⟨y, ⟨u, hu, b, hb, rfl⟩, z, ⟨v, hv, c, hc, rfl⟩, rfl⟩
        refine ⟨u + v, ⟨u, hu, v, hv, rfl⟩, b + c, ?_, by ring⟩
        rw [← ih]
        exact Finset.add_mem_add hb hc
      · rintro ⟨w, ⟨u, hu, v, hv, rfl⟩, e, he, rfl⟩
        rw [← ih] at he
        obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 he
        exact ⟨u + q * b, ⟨u, hu, b, hb, rfl⟩, v + q * c, ⟨v, hv, c, hc, rfl⟩, by ring⟩

/-- **Carry-free subtraction.**  Subtracting two digit strings subtracts the digits. -/
theorem digitSet_sub (S T : Finset ℤ) (q : ℤ) (k : ℕ) :
    digitSet S q k - digitSet T q k = digitSet (S - T) q k := by
  induction k with
  | zero => simp [digitSet]
  | succ k ih =>
      ext x
      simp only [Finset.mem_sub, mem_digitSet_succ]
      constructor
      · rintro ⟨y, ⟨u, hu, b, hb, rfl⟩, z, ⟨v, hv, c, hc, rfl⟩, rfl⟩
        refine ⟨u - v, ⟨u, hu, v, hv, rfl⟩, b - c, ?_, by ring⟩
        rw [← ih]
        exact Finset.sub_mem_sub hb hc
      · rintro ⟨w, ⟨u, hu, v, hv, rfl⟩, e, he, rfl⟩
        rw [← ih] at he
        obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_sub.1 he
        exact ⟨u + q * b, ⟨u, hu, b, hb, rfl⟩, v + q * c, ⟨v, hv, c, hc, rfl⟩, by ring⟩

/-- **Uniqueness of the digit expansion**: `|digitSet S q k| = |S| ^ k` when the digit
alphabet `S` is `q`-separated. -/
theorem card_digitSet {S : Finset ℤ} {q : ℤ} (hq : q ≠ 0) (hS : Sep q S) (k : ℕ) :
    (digitSet S q k).card = S.card ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have himg : digitSet S q (k + 1) =
          (S ×ˢ digitSet S q k).image (fun p : ℤ × ℤ => p.1 + q * p.2) := by
        ext x
        simp only [mem_digitSet_succ, Finset.mem_image, Finset.mem_product, Prod.exists]
        constructor
        · rintro ⟨u, hu, b, hb, rfl⟩; exact ⟨u, b, ⟨hu, hb⟩, rfl⟩
        · rintro ⟨u, b, ⟨hu, hb⟩, rfl⟩; exact ⟨u, hu, b, hb, rfl⟩
      have hinj : Set.InjOn (fun p : ℤ × ℤ => p.1 + q * p.2)
          ((S ×ˢ digitSet S q k : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
        rintro ⟨u, b⟩ hp ⟨v, c⟩ hp' heq
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
        simp only at heq
        have hu : u = v := by
          refine hS u hp.1 v hp'.1 ⟨c - b, ?_⟩
          linarith [heq]
        subst hu
        have : q * b = q * c := by linarith
        have : b = c := by
          exact mul_left_cancel₀ hq this
        simp [this]
      rw [himg, Finset.card_image_of_injOn hinj, Finset.card_product, ih, pow_succ]
      ring

/-- Digit strings are nonnegative when the digits are. -/
theorem digitSet_nonneg {S : Finset ℤ} {q : ℤ} (hq : 0 ≤ q) (hS : ∀ u ∈ S, 0 ≤ u) (k : ℕ) :
    ∀ x ∈ digitSet S q k, 0 ≤ x := by
  induction k with
  | zero => simp
  | succ k ih =>
      intro x hx
      obtain ⟨u, hu, b, hb, rfl⟩ := mem_digitSet_succ.1 hx
      have := hS u hu
      have := ih b hb
      positivity

/-- Digit strings with digits of absolute value at most `(q-1)/2` have absolute value at
most `(q^k - 1)/2`. -/
theorem digitSet_abs_le {S : Finset ℤ} {q : ℤ} (hq : 1 ≤ q) (hS : ∀ u ∈ S, 2 * |u| ≤ q - 1)
    (k : ℕ) : ∀ x ∈ digitSet S q k, 2 * |x| ≤ q ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      intro x hx
      obtain ⟨u, hu, b, hb, rfl⟩ := mem_digitSet_succ.1 hx
      have h1 := hS u hu
      have h2 := ih b hb
      have habs : |u + q * b| ≤ |u| + q * |b| := by
        calc |u + q * b| ≤ |u| + |q * b| := abs_add_le _ _
          _ = |u| + q * |b| := by rw [abs_mul, abs_of_nonneg (by omega : (0:ℤ) ≤ q)]
      have : 2 * (|u| + q * |b|) ≤ (q - 1) + q * (q ^ k - 1) := by nlinarith
      calc 2 * |u + q * b| ≤ 2 * (|u| + q * |b|) := by omega
        _ ≤ (q - 1) + q * (q ^ k - 1) := this
        _ = q ^ (k + 1) - 1 := by ring

/-! ## The set `A` of the construction -/

/-- The set `A = [1, L] ∪ ⋃_{i=1}^m (L + i q^k + B)` of the proof of the Lemma of Section 2
of [GHR2007] (the finite-set principle quoted as equation (1) in `masked_digit_bound.tex`),
where `B = digitSet U q k`.  The translates are taken along the arithmetic progression
`L + i q^k`, which is spread out enough that the sets `L + i q^k + (B - B)` are pairwise
disjoint. -/
def bigA (U : Finset ℤ) (q : ℤ) (k L m : ℕ) : Finset ℤ :=
  Finset.Icc (1 : ℤ) (L : ℤ) ∪ (Finset.Icc 1 m).biUnion
    (fun i : ℕ => (digitSet U q k).image (fun b => (L : ℤ) + (i : ℤ) * q ^ k + b))

theorem mem_bigA_of {U : Finset ℤ} {q : ℤ} {k L m i : ℕ} (hi : i ∈ Finset.Icc 1 m)
    {b : ℤ} (hb : b ∈ digitSet U q k) :
    (L : ℤ) + (i : ℤ) * q ^ k + b ∈ bigA U q k L m :=
  Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image_of_mem _ hb⟩)

/-- `|A| ≥ L + 1`: the set `A` contains the interval `[1, L]` and at least one further
element. -/
theorem card_bigA_ge {U : Finset ℤ} {q : ℤ} {k L m : ℕ} (hm : 1 ≤ m)
    (hne : (digitSet U q k).Nonempty) (hnn : ∀ x ∈ digitSet U q k, 0 ≤ x)
    (hQ : 0 < q ^ k) : L + 1 ≤ (bigA U q k L m).card := by
  obtain ⟨b, hb⟩ := hne
  have hb0 : 0 ≤ b := hnn b hb
  set x0 : ℤ := (L : ℤ) + ((1 : ℕ) : ℤ) * q ^ k + b with hx0
  have hx0A : x0 ∈ bigA U q k L m := mem_bigA_of (by simp [hm]) hb
  have hnot : x0 ∉ Finset.Icc (1 : ℤ) (L : ℤ) := by
    simp only [Finset.mem_Icc, not_and, not_le, hx0]
    intro _
    push_cast
    linarith
  have hsub : insert x0 (Finset.Icc (1 : ℤ) (L : ℤ)) ⊆ bigA U q k L m := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hx0A
    · exact Finset.mem_union_left _ hz
  have hcard : (insert x0 (Finset.Icc (1 : ℤ) (L : ℤ))).card = L + 1 := by
    rw [Finset.card_insert_of_notMem hnot, Int.card_Icc]
    simp
  calc L + 1 = (insert x0 (Finset.Icc (1 : ℤ) (L : ℤ))).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The upper bound `|A + B| ≤ (L + M) + m |B + B|` for the set `A` of the construction,
where `M` bounds the elements of `B`.  This is the estimate `|A + B| = m s^k + t` with
`t = |[1,L] + B| ≤ L + q^k / 2` in the proof of the Lemma of Section 2 of [GHR2007]. -/
theorem card_bigA_add_le {U : Finset ℤ} {q : ℤ} {k L m M : ℕ}
    (hM : ∀ x ∈ digitSet U q k, 0 ≤ x ∧ x ≤ (M : ℤ)) :
    (bigA U q k L m + digitSet U q k).card ≤
      (L + M) + m * (digitSet U q k + digitSet U q k).card := by
  set B := digitSet U q k with hB
  have hsub : bigA U q k L m + B ⊆
      (Finset.Icc (1 : ℤ) ((L : ℤ) + (M : ℤ))) ∪
        (Finset.Icc 1 m).biUnion
          (fun i : ℕ => (B + B).image (fun z => (L : ℤ) + (i : ℤ) * q ^ k + z)) := by
    intro x hx
    obtain ⟨α, hα, b, hb, rfl⟩ := Finset.mem_add.1 hx
    obtain ⟨hb0, hbM⟩ := hM b hb
    rcases Finset.mem_union.1 hα with hα | hα
    · refine Finset.mem_union_left _ ?_
      rw [Finset.mem_Icc] at hα ⊢
      omega
    · obtain ⟨i, hi, hα⟩ := Finset.mem_biUnion.1 hα
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hα
      refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, ?_⟩)
      exact Finset.mem_image.2 ⟨b' + b, Finset.add_mem_add hb' hb, by ring⟩
  calc (bigA U q k L m + B).card
      ≤ ((Finset.Icc (1 : ℤ) ((L : ℤ) + (M : ℤ))) ∪
          (Finset.Icc 1 m).biUnion
            (fun i : ℕ => (B + B).image (fun z => (L : ℤ) + (i : ℤ) * q ^ k + z))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.Icc (1 : ℤ) ((L : ℤ) + (M : ℤ))).card +
          ((Finset.Icc 1 m).biUnion
            (fun i : ℕ => (B + B).image (fun z => (L : ℤ) + (i : ℤ) * q ^ k + z))).card :=
        Finset.card_union_le _ _
    _ ≤ (L + M) + m * (B + B).card := by
        gcongr
        · rw [Int.card_Icc]
          simp
        · calc ((Finset.Icc 1 m).biUnion
                  (fun i : ℕ => (B + B).image (fun z => (L : ℤ) + (i : ℤ) * q ^ k + z))).card
              ≤ ∑ _i ∈ Finset.Icc 1 m, (B + B).card :=
                le_trans Finset.card_biUnion_le
                  (Finset.sum_le_sum (fun i _ => Finset.card_image_le))
            _ = m * (B + B).card := by simp [Nat.card_Icc]

/-- The lower bound `|A - B| ≥ m |B - B|` for the set `A` of the construction: the `m`
translates `L + i q^k + (B - B)` are pairwise disjoint because `B - B` is contained in an
interval of length less than `q^k`.  This is the estimate `|A - B| = m d^k + t ≥ m d^k` in
the proof of the Lemma of Section 2 of [GHR2007]. -/
theorem card_bigA_sub_ge {U : Finset ℤ} {q : ℤ} {k L m : ℕ}
    (habs : ∀ x ∈ digitSet U q k - digitSet U q k, 2 * |x| ≤ q ^ k - 1) :
    m * (digitSet U q k - digitSet U q k).card ≤ (bigA U q k L m - digitSet U q k).card := by
  set B := digitSet U q k with hB
  have key : ((Finset.Icc 1 m) ×ˢ (B - B)).card ≤ (bigA U q k L m - B).card := by
    refine Finset.card_le_card_of_injOn (fun p : ℕ × ℤ => (L : ℤ) + (p.1 : ℤ) * q ^ k + p.2)
      ?_ ?_
    · rintro ⟨i, x⟩ hp
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp
      obtain ⟨hi, hx⟩ := hp
      obtain ⟨b, hb, b', hb', rfl⟩ := Finset.mem_sub.1 hx
      refine Finset.mem_sub.2 ⟨(L : ℤ) + (i : ℤ) * q ^ k + b, mem_bigA_of hi hb, b', hb', ?_⟩
      ring
    · rintro ⟨i, x⟩ hp ⟨j, y⟩ hp' heq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
      have hx := habs x hp.2
      have hy := habs y hp'.2
      have heq' : (i : ℤ) * q ^ k + x = (j : ℤ) * q ^ k + y := by
        simp only at heq; linarith
      have hax : |x| ≤ q ^ k - 1 := by have h := abs_nonneg x; omega
      have hay : |y| ≤ q ^ k - 1 := by have h := abs_nonneg y; omega
      have hxy : |y - x| ≤ q ^ k - 1 := by
        have h2 : |y - x| ≤ |y| + |x| := abs_sub _ _
        omega
      have hij : (i : ℤ) = (j : ℤ) := by
        by_contra hne
        have hdiff : ((i : ℤ) - (j : ℤ)) * q ^ k = y - x := by linarith
        have h1 : 1 ≤ |(i : ℤ) - (j : ℤ)| := by
          rcases lt_trichotomy ((i : ℤ)) ((j : ℤ)) with h | h | h
          · rw [abs_of_nonpos (by omega)]; omega
          · exact absurd h hne
          · rw [abs_of_nonneg (by omega)]; omega
        have hQpos : 0 < q ^ k := by
          have hnn := abs_nonneg (y - x)
          omega
        have : q ^ k ≤ |y - x| := by
          calc q ^ k = 1 * q ^ k := (one_mul _).symm
            _ ≤ |(i : ℤ) - (j : ℤ)| * q ^ k :=
                Int.mul_le_mul_of_nonneg_right h1 (le_of_lt hQpos)
            _ = |((i : ℤ) - (j : ℤ)) * q ^ k| := by
                rw [abs_mul, abs_of_nonneg (le_of_lt hQpos)]
            _ = |y - x| := by rw [hdiff]
        omega
      have hi : i = j := by exact_mod_cast hij
      have hxy' : x = y := by rw [hij] at heq'; linarith
      simp [hi, hxy']
  calc m * (B - B).card = ((Finset.Icc 1 m) ×ˢ (B - B)).card := by
        simp [Finset.card_product, Nat.card_Icc]
    _ ≤ _ := key

/-! ## The family of pairs produced by the construction -/

set_option maxHeartbeats 1000000 in
/-- **The construction of the Lemma of Section 2 of [GHR2007]** (the finite-set principle
quoted as equation (1), `eq:GHR`, in `masked_digit_bound.tex`).

Given a finite nonempty set `U` of integers contained in `{0, 1, …, a}` with `a ≥ 1`, put
`q = 2a + 1`, `s = |U + U|`, `d = |U - U|` and
`θ = 1 + log (d / s) / log q`.  Then for every `K > 1` there are pairs of finite nonempty
sets `A, B` of integers with `|A|` arbitrarily large,
`|A + B| ≤ K |A|` and `c(K) |A + B| ^ θ ≤ |A - B|`, where
`c(K) = 1 / (2 (3K / (2(K-1))) ^ θ) > 0`.

The sets are `B = digitSet U q k` (the base-`q` digit strings of length `k` with digits in
`U`) and `A = bigA U q k L m` for suitable `L` and `m`. -/
theorem exists_ghr_pair (U : Finset ℤ) (a : ℕ) (ha : 1 ≤ a) (hUne : U.Nonempty)
    (hU : ∀ u ∈ U, 0 ≤ u ∧ u ≤ (a : ℤ)) (theta : ℝ) (hth0 : 0 ≤ theta)
    (hth : theta = 1 + Real.log (((U - U).card : ℝ) / ((U + U).card : ℝ)) /
      Real.log (2 * (a : ℝ) + 1))
    (K : ℝ) (hK : 1 < K) (N : ℕ) :
    ∃ A B : Finset ℤ, A.Nonempty ∧ B.Nonempty ∧ N ≤ A.card ∧
      ((A + B).card : ℝ) ≤ K * (A.card : ℝ) ∧
      (1 / (2 * (3 * K / (2 * (K - 1))) ^ theta)) * ((A + B).card : ℝ) ^ theta ≤
        ((A - B).card : ℝ) := by
  classical
  set q : ℕ := 2 * a + 1 with hqdef
  have hq2 : 2 ≤ q := by omega
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  set s : ℕ := (U + U).card with hsdef
  set d : ℕ := (U - U).card with hddef
  have hs0 : 0 < s := Finset.card_pos.2 (hUne.add hUne)
  have hd0 : 0 < d := Finset.card_pos.2 (hUne.sub hUne)
  -- the digit alphabets are `q`-separated
  have hSepS : Sep (q : ℤ) (U + U) := by
    refine sep_of_bounded (lo := 0) ?_
    rintro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 hx
    obtain ⟨hu0, hua⟩ := hU u hu
    obtain ⟨hv0, hva⟩ := hU v hv
    have : ((q : ℕ) : ℤ) = 2 * (a : ℤ) + 1 := by push_cast [hqdef]; ring
    omega
  have hSepD : Sep (q : ℤ) (U - U) := by
    refine sep_of_bounded (lo := -(a : ℤ)) ?_
    rintro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.1 hx
    obtain ⟨hu0, hua⟩ := hU u hu
    obtain ⟨hv0, hva⟩ := hU v hv
    have : ((q : ℕ) : ℤ) = 2 * (a : ℤ) + 1 := by push_cast [hqdef]; ring
    omega
  -- `s ≤ q`
  have hsq : s ≤ q := by
    have hsub : U + U ⊆ Finset.Icc (0 : ℤ) (2 * (a : ℤ)) := by
      intro x hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 hx
      obtain ⟨hu0, hua⟩ := hU u hu
      obtain ⟨hv0, hva⟩ := hU v hv
      simp only [Finset.mem_Icc]
      omega
    have := Finset.card_le_card hsub
    rw [Int.card_Icc] at this
    simp only [hsdef]
    omega
  -- choose the length `k` of the digit strings
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, (N : ℝ) * (2 * (K - 1) / 3) < (q : ℝ) ^ k0 :=
    pow_unbounded_of_one_lt _ (by linarith : (1 : ℝ) < (q : ℝ))
  set k : ℕ := k0 + 1 with hkdef
  have hkN : (N : ℝ) * (2 * (K - 1) / 3) < (q : ℝ) ^ k := by
    refine lt_of_lt_of_le hk0 ?_
    exact pow_le_pow_right₀ (by linarith) (by omega)
  set Qn : ℕ := q ^ k with hQdef
  set Sk : ℕ := s ^ k with hSkdef
  set Dk : ℕ := d ^ k with hDkdef
  have hQpos : 0 < Qn := Nat.pow_pos (by omega)
  have hSkpos : 0 < Sk := Nat.pow_pos hs0
  have hDkpos : 0 < Dk := Nat.pow_pos hd0
  have hSkQ : Sk ≤ Qn := Nat.pow_le_pow_left hsq k
  -- the halved bound `M` on the digit strings
  obtain ⟨M, hM⟩ : ∃ M : ℕ, Qn = 2 * M + 1 := by
    have : Odd Qn := (by exact ⟨a, by omega⟩ : Odd q).pow
    obtain ⟨M, hM⟩ := this
    exact ⟨M, by omega⟩
  set m : ℕ := Qn / Sk with hmdef
  have hm1 : 1 ≤ m := Nat.one_le_div_iff hSkpos |>.2 hSkQ
  have hmS : m * Sk ≤ Qn := Nat.div_mul_le_self _ _
  have hQm : Qn ≤ 2 * (m * Sk) := by
    rw [mul_comm m Sk]
    have h1 : Sk * m + Qn % Sk = Qn := Nat.div_add_mod Qn Sk
    have h2 : Qn % Sk < Sk := Nat.mod_lt _ hSkpos
    have h3 : Sk ≤ Sk * m := Nat.le_mul_of_pos_right _ hm1
    omega
  set L : ℕ := ⌊(3 * (Qn : ℝ) / (2 * (K - 1)))⌋₊ with hLdef
  -- the two sets of the construction
  set B : Finset ℤ := digitSet U (q : ℤ) k with hBdef
  set A : Finset ℤ := bigA U (q : ℤ) k L m with hAdef
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hq2
  have hQZ : ((Qn : ℕ) : ℤ) = (q : ℤ) ^ k := by rw [hQdef]; push_cast; ring
  have hQZpos : (0 : ℤ) < (q : ℤ) ^ k := pow_pos hqZ k
  have hBne : B.Nonempty := digitSet_nonempty hUne _ _
  have hBnn : ∀ x ∈ B, 0 ≤ x := digitSet_nonneg hqZ.le (fun u hu => (hU u hu).1) k
  have hdigit : ∀ u ∈ U, 2 * |u| ≤ (q : ℤ) - 1 := by
    intro u hu
    obtain ⟨hu0, hua⟩ := hU u hu
    have hqa : ((q : ℕ) : ℤ) = 2 * (a : ℤ) + 1 := by rw [hqdef]; push_cast; ring
    rw [abs_of_nonneg hu0]
    omega
  have hBabs : ∀ x ∈ B, 2 * |x| ≤ (q : ℤ) ^ k - 1 :=
    digitSet_abs_le (by omega) hdigit k
  have hBM : ∀ x ∈ B, 0 ≤ x ∧ x ≤ (M : ℤ) := by
    intro x hx
    have h1 := hBnn x hx
    have h2 := hBabs x hx
    rw [abs_of_nonneg h1] at h2
    have h3 : ((Qn : ℕ) : ℤ) = 2 * (M : ℤ) + 1 := by rw [hM]; push_cast; ring
    rw [hQZ] at h3
    omega
  have hBB : B + B = digitSet (U + U) (q : ℤ) k := digitSet_add U U _ k
  have hBmB : B - B = digitSet (U - U) (q : ℤ) k := digitSet_sub U U _ k
  have hBBcard : (B + B).card = Sk := by
    rw [hBB, card_digitSet (by omega) hSepS k]
  have hBmBcard : (B - B).card = Dk := by
    rw [hBmB, card_digitSet (by omega) hSepD k]
  have hDabs : ∀ x ∈ B - B, 2 * |x| ≤ (q : ℤ) ^ k - 1 := by
    rw [hBmB]
    refine digitSet_abs_le (by omega) ?_ k
    intro w hw
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.1 hw
    obtain ⟨hu0, hua⟩ := hU u hu
    obtain ⟨hv0, hva⟩ := hU v hv
    have hqa : ((q : ℕ) : ℤ) = 2 * (a : ℤ) + 1 := by rw [hqdef]; push_cast; ring
    rcases abs_cases (u - v) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  -- the three cardinality estimates
  have hAcard : L + 1 ≤ A.card := card_bigA_ge hm1 hBne hBnn hQZpos
  have hABcard : (A + B).card ≤ (L + M) + m * Sk := by
    have := card_bigA_add_le (L := L) (m := m) hBM
    rwa [hBBcard] at this
  have hAmBcard : m * Dk ≤ (A - B).card := by
    have := card_bigA_sub_ge (L := L) (m := m) hDabs
    rwa [hBmBcard] at this
  -- real-number bookkeeping
  have hKm1 : (0 : ℝ) < K - 1 := by linarith
  have hQR : (0 : ℝ) < (Qn : ℝ) := by exact_mod_cast hQpos
  have hSkR : (0 : ℝ) < (Sk : ℝ) := by exact_mod_cast hSkpos
  have hDkR : (0 : ℝ) < (Dk : ℝ) := by exact_mod_cast hDkpos
  have hL1 : (L : ℝ) ≤ 3 * (Qn : ℝ) / (2 * (K - 1)) :=
    Nat.floor_le (by positivity)
  have hL2 : 3 * (Qn : ℝ) / (2 * (K - 1)) < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMR : 2 * (M : ℝ) + 1 = (Qn : ℝ) := by exact_mod_cast hM.symm
  have hmSR : (m : ℝ) * (Sk : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hmS
  have hQmR : (Qn : ℝ) ≤ 2 * ((m : ℝ) * (Sk : ℝ)) := by exact_mod_cast hQm
  have hAcardR : (L : ℝ) + 1 ≤ (A.card : ℝ) := by exact_mod_cast hAcard
  have hABcardR : ((A + B).card : ℝ) ≤ ((L : ℝ) + (M : ℝ)) + (m : ℝ) * (Sk : ℝ) := by
    exact_mod_cast hABcard
  have hAmBcardR : (m : ℝ) * (Dk : ℝ) ≤ ((A - B).card : ℝ) := by exact_mod_cast hAmBcard
  have hABsimple : ((A + B).card : ℝ) ≤ (L : ℝ) + 3 * (Qn : ℝ) / 2 := by linarith
  refine ⟨A, B, ?_, hBne, ?_, ?_, ?_⟩
  · exact Finset.card_pos.1 (by omega)
  · -- `|A|` is arbitrarily large
    have hNR : (N : ℝ) < (L : ℝ) + 1 := by
      have h1 : (N : ℝ) * (2 * (K - 1) / 3) < (Qn : ℝ) := by rw [hQdef]; push_cast; exact hkN
      have h2 : (N : ℝ) < 3 * (Qn : ℝ) / (2 * (K - 1)) := by
        rw [lt_div_iff₀ (by positivity)]
        nlinarith
      linarith
    have : N ≤ L := by
      have : (N : ℝ) < (L : ℝ) + 1 := hNR
      exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
    omega
  · -- the small-sumset condition `|A + B| ≤ K |A|`
    have hkey : 3 * (Qn : ℝ) < ((L : ℝ) + 1) * (2 * (K - 1)) :=
      (div_lt_iff₀ (by positivity)).1 hL2
    nlinarith
  · -- the lower bound on `|A - B|`
    set R : ℝ := 3 * K / (2 * (K - 1)) with hRdef
    have hR : (0 : ℝ) < R := by rw [hRdef]; positivity
    have hRpow : (0 : ℝ) < R ^ theta := Real.rpow_pos_of_pos hR _
    have hARQ : ((A + B).card : ℝ) ≤ R * (Qn : ℝ) := by
      have hid : R * (Qn : ℝ) = 3 * (Qn : ℝ) / (2 * (K - 1)) + 3 * (Qn : ℝ) / 2 := by
        rw [hRdef]; field_simp; ring
      linarith
    -- the value of `q ^ θ`
    have hqRpos : (0 : ℝ) < (q : ℝ) := by linarith
    have hlogq : Real.log (q : ℝ) ≠ 0 := by
      have : (1 : ℝ) < (q : ℝ) := by linarith
      exact ne_of_gt (Real.log_pos this)
    have hqcast : ((q : ℕ) : ℝ) = 2 * (a : ℝ) + 1 := by rw [hqdef]; push_cast; ring
    have hqtheta : (q : ℝ) ^ theta = (q : ℝ) * ((d : ℝ) / (s : ℝ)) := by
      have hds : (0 : ℝ) < (d : ℝ) / (s : ℝ) := by
        have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
        have : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
        positivity
      have hth' : theta = 1 + Real.log ((d : ℝ) / (s : ℝ)) / Real.log (q : ℝ) := by
        rw [hth, hqcast]
      have hcancel : Real.log (q : ℝ) * (Real.log ((d : ℝ) / (s : ℝ)) / Real.log (q : ℝ)) =
          Real.log ((d : ℝ) / (s : ℝ)) := by
        field_simp
      rw [hth', Real.rpow_add hqRpos, Real.rpow_one, Real.rpow_def_of_pos hqRpos, hcancel,
        Real.exp_log hds]
    have hQtheta : (Qn : ℝ) ^ theta = (Qn : ℝ) * (Dk : ℝ) / (Sk : ℝ) := by
      have hQq : (Qn : ℝ) = (q : ℝ) ^ (k : ℕ) := by rw [hQdef]; push_cast; ring
      have h1 : (Qn : ℝ) ^ theta = ((q : ℝ) ^ theta) ^ (k : ℕ) := by
        rw [hQq, ← Real.rpow_natCast (q : ℝ) k, ← Real.rpow_mul hqRpos.le,
          mul_comm (k : ℝ) theta, Real.rpow_mul hqRpos.le, Real.rpow_natCast]
      rw [h1, hqtheta, hQdef, hDkdef, hSkdef]
      push_cast
      rw [mul_pow, div_pow]
      ring
    have hstep : ((A + B).card : ℝ) ^ theta ≤ R ^ theta * ((Qn : ℝ) * (Dk : ℝ) / (Sk : ℝ)) := by
      calc ((A + B).card : ℝ) ^ theta ≤ (R * (Qn : ℝ)) ^ theta :=
            Real.rpow_le_rpow (by positivity) hARQ hth0
        _ = R ^ theta * (Qn : ℝ) ^ theta := Real.mul_rpow hR.le hQR.le
        _ = R ^ theta * ((Qn : ℝ) * (Dk : ℝ) / (Sk : ℝ)) := by rw [hQtheta]
    have hdivbd : (Qn : ℝ) * (Dk : ℝ) / (Sk : ℝ) ≤ 2 * ((m : ℝ) * (Dk : ℝ)) := by
      rw [div_le_iff₀ hSkR]
      nlinarith
    have hc : (0 : ℝ) < 1 / (2 * R ^ theta) := by positivity
    have hfield : ∀ X Y : ℝ, 0 < X → (1 / (2 * X)) * (X * Y) = Y / 2 := by
      intro X Y hX
      field_simp
    calc (1 / (2 * R ^ theta)) * ((A + B).card : ℝ) ^ theta
        ≤ (1 / (2 * R ^ theta)) * (R ^ theta * ((Qn : ℝ) * (Dk : ℝ) / (Sk : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep hc.le
      _ = ((Qn : ℝ) * (Dk : ℝ) / (Sk : ℝ)) / 2 := hfield _ _ hRpow
      _ ≤ (m : ℝ) * (Dk : ℝ) := by linarith
      _ ≤ ((A - B).card : ℝ) := hAmBcardR

end MaskedDigit.Digits
