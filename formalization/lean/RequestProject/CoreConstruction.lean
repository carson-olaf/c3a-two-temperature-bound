/-
Copyright (c) 2026 Logan Kleinwaks. All rights reserved.
Released under Apache 2.0 license; see LICENSE-Kleinwaks.
Reused from kleinwaks/masked-digit-sum-difference-bound,
commit 352ab86effecb7efce415507a8c781ec158b86e0.
-/
import RequestProject.MaskData
import RequestProject.ProductWeights

/-!
# The core digit construction

This file contains the combinatorial heart shared by Proposition 2 ("Masked-digit bound"),
Proposition 3 ("Controlled-carry block bound") and Proposition 5 ("Two-sided carry pressure")
of `masked_digit_bound.tex`.

All three are proved in the source by the same recipe:

* fix a finite alphabet of signed digit blocks, closed under negation, and give it the Gibbs
  weights of equation (7) (`eq:gibbs`);
* take a large number `l` of blocks and keep the words whose total minimum witness cost and
  whose total unweighted digit sum are close to their means;
* convert each such word into a difference of two elements of the digit set `U`
  (equation (8), `eq:Um`), using the minimum witnesses `(α_d, β_d)`;
* bound `|U + U|` by a weighted count of sum-digit words, and `max U` by a power of the base;
* apply the dilated finite-set principle (2) (`eq:GHR-dilated`) and let `l → ∞`.

`MaskedDigit.MaskData.core_bound` below is that recipe, stated once for an arbitrary
negation-closed alphabet of signed digit blocks whose residues modulo `q ^ k` are pairwise
distinct, and with the sum side supplied as a hypothesis so that the same theorem covers both
the crude bound by `P₊(x)` and the exact sum pressure of Section 4.1 of the source.
-/

open scoped BigOperators

namespace MaskedDigit

namespace MaskData

variable (D : MaskData)

/-! ## Minimum witnesses -/

/-- A choice of minimum witness pair `(α_d, β_d)` for each difference digit `d`, as fixed in
the proof of Proposition 2 of `masked_digit_bound.tex`: `α_d, β_d ∈ M`, `α_d - β_d = d` and
`α_d + β_d = κ(d)`. -/
noncomputable def wit (d : ℤ) : ℕ × ℕ :=
  if h : d ∈ D.diffSupport then
    ⟨(D.exists_min_witness h).choose,
      ((D.exists_min_witness h).choose_spec.2).choose⟩
  else ⟨0, 0⟩

theorem wit_spec {d : ℤ} (hd : d ∈ D.diffSupport) :
    (D.wit d).1 ∈ D.M ∧ (D.wit d).2 ∈ D.M ∧
      ((D.wit d).1 : ℤ) - (D.wit d).2 = d ∧ (D.wit d).1 + (D.wit d).2 = D.kappa d := by
  have h := D.exists_min_witness hd
  have h1 := h.choose_spec
  have h2 := h1.2.choose_spec
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [wit, dif_pos hd] <;>
    [exact h1.1; exact h2.1; exact h2.2.1; exact h2.2.2]

theorem wit_fst_mem {d : ℤ} (hd : d ∈ D.diffSupport) : (D.wit d).1 ∈ D.M := (D.wit_spec hd).1

theorem wit_snd_mem {d : ℤ} (hd : d ∈ D.diffSupport) : (D.wit d).2 ∈ D.M := (D.wit_spec hd).2.1

theorem wit_sub {d : ℤ} (hd : d ∈ D.diffSupport) :
    ((D.wit d).1 : ℤ) - (D.wit d).2 = d := (D.wit_spec hd).2.2.1

theorem wit_add {d : ℤ} (hd : d ∈ D.diffSupport) :
    (D.wit d).1 + (D.wit d).2 = D.kappa d := (D.wit_spec hd).2.2.2

/-! ## Digit strings -/

/-- The nonnegative integer with base-`q` digit array `a` of length `m`.  This is the generic
element of the set `U` of equation (8) (`eq:Um`) of `masked_digit_bound.tex`. -/
def flatInt (m : ℕ) (a : Fin m → ℕ) : ℕ := ∑ t, a t * D.q ^ (t : ℕ)

/-- The set `U` of equation (8) (`eq:Um`) of `masked_digit_bound.tex`: base-`q` integers with
`m` digits taken from the mask `M` and total digit sum at most `L`. -/
noncomputable def maskSet (m L : ℕ) : Finset ℕ :=
  ((Finset.univ : Finset (Fin m → {n : ℕ // n ∈ D.M})).filter
      (fun a => ∑ t, (a t : ℕ) ≤ L)).image (fun a => D.flatInt m (fun t => (a t : ℕ)))

/-- The set of integers with `m` base-`q` digits taken from the sum support `S = M + M` and
total digit sum at most `T`.  Every element of `U + U` arises this way, which is the
elementary sumset bound used in the proofs of Propositions 2, 4 and 6 of
`masked_digit_bound.tex`. -/
noncomputable def sumSet (m T : ℕ) : Finset ℕ :=
  ((Finset.univ : Finset (Fin m → {n : ℕ // n ∈ D.sumSupport})).filter
      (fun a => ∑ t, (a t : ℕ) ≤ T)).image (fun a => D.flatInt m (fun t => (a t : ℕ)))

/-- Expanding a power of a partition polynomial as a sum over digit words: this is the
elementary identity behind the weighted counting bounds of `masked_digit_bound.tex`. -/
theorem pow_sum_eq_sum_words (x : ℝ) (s : Finset ℕ) (m : ℕ) :
    (∑ v ∈ s, x ^ v) ^ m = ∑ a : Fin m → {n : ℕ // n ∈ s}, x ^ (∑ i, (a i : ℕ)) := by
  classical
  have h1 : (∑ v ∈ s, x ^ v) = ∑ v : {n : ℕ // n ∈ s}, x ^ (v : ℕ) := by
    rw [← Finset.sum_coe_sort s (fun v => x ^ v)]
  have h2 : ∏ _i : Fin m, (∑ v : {n : ℕ // n ∈ s}, x ^ (v : ℕ))
      = (∑ v : {n : ℕ // n ∈ s}, x ^ (v : ℕ)) ^ m := by simp
  rw [h1, ← h2, Fintype.prod_sum (fun (_ : Fin m) (v : {n : ℕ // n ∈ s}) => x ^ (v : ℕ))]
  exact Finset.sum_congr rfl fun a _ => Finset.prod_pow_eq_pow_sum _ _ _

/-- A weighted counting bound for a set of digit words with bounded digit sum: the number of
words, times `x` raised to the digit budget, is at most the corresponding power of the
partition polynomial.  This is the generic form of the estimate `N_m x^{2L} ≤ P₊(x)^m` used
in the proof of Proposition 2 of `masked_digit_bound.tex`. -/
theorem card_image_mul_pow_le (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (s : Finset ℕ) (m T : ℕ)
    (f : (Fin m → {n : ℕ // n ∈ s}) → ℕ) :
    (((Finset.univ.filter (fun a : Fin m → {n : ℕ // n ∈ s} => ∑ t, (a t : ℕ) ≤ T)).image
        f).card : ℝ) * x ^ T ≤ (∑ v ∈ s, x ^ v) ^ m := by
  classical
  set F := (Finset.univ : Finset (Fin m → {n : ℕ // n ∈ s})).filter
    (fun a => ∑ t, (a t : ℕ) ≤ T) with hF
  have hcard : ((F.image f).card : ℝ) ≤ (F.card : ℝ) := by
    exact_mod_cast Finset.card_image_le
  calc (((F.image f).card : ℝ)) * x ^ T ≤ (F.card : ℝ) * x ^ T := by
        have : (0:ℝ) ≤ x ^ T := le_of_lt (pow_pos hx0 T)
        exact mul_le_mul_of_nonneg_right hcard this
    _ = ∑ _a ∈ F, x ^ T := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ F, x ^ (∑ i, (a i : ℕ)) := by
        refine Finset.sum_le_sum fun a ha => ?_
        have : ∑ i, (a i : ℕ) ≤ T := by simpa [hF] using (Finset.mem_filter.1 ha).2
        exact pow_le_pow_of_le_one hx0.le hx1.le this
    _ ≤ ∑ a : Fin m → {n : ℕ // n ∈ s}, x ^ (∑ i, (a i : ℕ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro a _ _
        positivity
    _ = (∑ v ∈ s, x ^ v) ^ m := (pow_sum_eq_sum_words x s m).symm

/-- The crude weighted bound on the number of sum-digit outputs, used in the proof of
Proposition 2 of `masked_digit_bound.tex`: `N_m x^{2L} ≤ P₊(x)^m`. -/
theorem sumSet_card_mul_pow_le (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (m T : ℕ) :
    ((D.sumSet m T).card : ℝ) * x ^ T ≤ D.Pplus x ^ m :=
  card_image_mul_pow_le x hx0 hx1 D.sumSupport m T _

/-! ## Blocks -/

/-- The integer value `∑ᵢ vᵢ qⁱ` of a signed digit block of length `k`. -/
def blockVal (k : ℕ) (v : Fin k → ℤ) : ℤ := ∑ i, v i * (D.q : ℤ) ^ (i : ℕ)

/-- The total minimum witness cost `∑ᵢ κ(vᵢ)` of a signed digit block of length `k`. -/
noncomputable def blockCost (k : ℕ) (v : Fin k → ℤ) : ℕ := ∑ i, D.kappa (v i)

/-- The unweighted digit sum `∑ᵢ vᵢ` of a signed digit block; this is the quantity whose
vanishing makes the two digit budgets of `masked_digit_bound.tex` equal. -/
def blockSum (k : ℕ) (v : Fin k → ℤ) : ℤ := ∑ i, v i

/-! ## Words of blocks and their digit arrays -/

section Words

variable {A : Type*} (k : ℕ) (vec : A → Fin k → ℤ)

/-- The signed digit array of length `l * k` obtained by concatenating the `l` blocks of a
word `w`.  This is the digit array `(d_t)` of the proof of Proposition 2 of
`masked_digit_bound.tex`. -/
def wordDigits {l : ℕ} (w : Fin l → A) (t : Fin (l * k)) : ℤ :=
  vec (w (finProdFinEquiv.symm t).1) ((finProdFinEquiv.symm t).2)

@[simp] theorem wordDigits_apply {l : ℕ} (w : Fin l → A) (j : Fin l) (i : Fin k) :
    wordDigits k vec w (finProdFinEquiv (j, i)) = vec (w j) i := by
  simp [wordDigits]

/-- Any additive statistic of the digit array of a word is the sum over blocks of the
corresponding statistic of the block. -/
theorem sum_wordDigits {M : Type*} [AddCommMonoid M] (F : ℤ → M) {l : ℕ} (w : Fin l → A) :
    ∑ t, F (wordDigits k vec w t) = ∑ j, ∑ i, F (vec (w j) i) := by
  rw [← Equiv.sum_comp (finProdFinEquiv (m := l) (n := k))
      (fun t => F (wordDigits k vec w t)), Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    rw [wordDigits_apply]

/-- Splitting a base-`q` expansion of length `l * k` into `l` blocks of length `k`, i.e.
into a base-`q ^ k` expansion. -/
theorem sum_pow_decomp {R : Type*} [CommSemiring R] (q : R) (l : ℕ) (f : Fin (l * k) → R) :
    ∑ t, f t * q ^ (t : ℕ)
      = ∑ j : Fin l, (∑ i : Fin k, f (finProdFinEquiv (j, i)) * q ^ (i : ℕ)) * (q ^ k) ^ (j : ℕ) := by
  rw [← Equiv.sum_comp (finProdFinEquiv (m := l) (n := k)) (fun t => f t * q ^ (t : ℕ)),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((finProdFinEquiv (j, i) : Fin (l * k)) : ℕ) = (i : ℕ) + k * (j : ℕ) := rfl
  rw [h, pow_add, ← pow_mul]
  ring

end Words

/-- **Injectivity of block words.**  If the blocks of an alphabet have pairwise distinct
residues modulo `Q`, then a word of blocks is determined by the integer
`∑ⱼ val(wⱼ) Qʲ` it represents.  This is the general form of the carry-free injectivity used
in the proofs of Propositions 2, 4 and 6 of `masked_digit_bound.tex`. -/
theorem residue_word_injective_aux {A : Type*} (Q : ℕ) (hQ : 0 < Q) (val : A → ℤ)
    (hinj : Function.Injective fun a => ((val a : ℤ) : ZMod Q)) :
    ∀ (l : ℕ) (w w' : ℕ → A),
      (∑ j ∈ Finset.range l, val (w j) * (Q : ℤ) ^ j
        = ∑ j ∈ Finset.range l, val (w' j) * (Q : ℤ) ^ j) →
      ∀ j < l, w j = w' j := by
  intro l
  induction l with
  | zero => intro w w' _ j hj; omega
  | succ n ih =>
    intro w w' hval j hj
    rw [Finset.sum_range_succ' (fun j => val (w j) * (Q : ℤ) ^ j) n,
      Finset.sum_range_succ' (fun j => val (w' j) * (Q : ℤ) ^ j) n] at hval
    simp only [pow_succ, pow_zero, mul_one] at hval
    have hQ0 : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ
    have h1 : ∀ f : ℕ → A, ∑ i ∈ Finset.range n, val (f (i + 1)) * ((Q : ℤ) ^ i * (Q : ℤ))
        = (∑ i ∈ Finset.range n, val (f (i + 1)) * (Q : ℤ) ^ i) * (Q : ℤ) := by
      intro f; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1 w, h1 w'] at hval
    have hdvd : (Q : ℤ) ∣ (val (w 0) - val (w' 0)) :=
      ⟨(∑ i ∈ Finset.range n, val (w' (i + 1)) * (Q : ℤ) ^ i)
        - (∑ i ∈ Finset.range n, val (w (i + 1)) * (Q : ℤ) ^ i), by linarith [hval]⟩
    have hz : ((val (w 0) - val (w' 0) : ℤ) : ZMod Q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by exact_mod_cast hdvd)
    have h0 : w 0 = w' 0 := by
      apply hinj
      have h : ((val (w 0) : ℤ) : ZMod Q) - ((val (w' 0) : ℤ) : ZMod Q) = 0 := by
        push_cast at hz; linear_combination hz
      simpa [sub_eq_zero] using h
    have hshift : ∑ i ∈ Finset.range n, val (w (i + 1)) * (Q : ℤ) ^ i
        = ∑ i ∈ Finset.range n, val (w' (i + 1)) * (Q : ℤ) ^ i := by
      rw [h0] at hval
      exact mul_right_cancel₀ (ne_of_gt hQ0) (by linarith [hval])
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact h0
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact ih (fun t => w (t + 1)) (fun t => w' (t + 1)) hshift j' (by omega)

/-- **Injectivity of block words**, finite-vector form: see `residue_word_injective_aux`.
This is the injectivity used in the proofs of Propositions 2, 4 and 6 of
`masked_digit_bound.tex`. -/
theorem residue_word_injective {A : Type*} (Q : ℕ) (hQ : 0 < Q) (val : A → ℤ)
    (hinj : Function.Injective fun a => ((val a : ℤ) : ZMod Q)) (l : ℕ) :
    Function.Injective fun w : Fin l → A => ∑ j, val (w j) * (Q : ℤ) ^ (j : ℕ) := by
  intro w w' hval
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · funext j; exact absurd j.isLt (by omega)
  · classical
    set w1 : ℕ → A := fun j => if h : j < l then w ⟨j, h⟩ else w ⟨0, hl⟩ with hw1
    set w1' : ℕ → A := fun j => if h : j < l then w' ⟨j, h⟩ else w ⟨0, hl⟩ with hw1'
    have hconv : ∀ (f : Fin l → A) (g : ℕ → A), (∀ j (h : j < l), g j = f ⟨j, h⟩) →
        ∑ j ∈ Finset.range l, val (g j) * (Q : ℤ) ^ j = ∑ j, val (f j) * (Q : ℤ) ^ (j : ℕ) := by
      intro f g hg
      rw [Finset.sum_range fun j => val (g j) * (Q : ℤ) ^ j]
      exact Finset.sum_congr rfl fun j _ => by rw [hg j j.isLt]
    have h1 : ∑ j ∈ Finset.range l, val (w1 j) * (Q : ℤ) ^ j
        = ∑ j ∈ Finset.range l, val (w1' j) * (Q : ℤ) ^ j := by
      rw [hconv w w1 (fun j h => by simp [hw1, h]), hconv w' w1' (fun j h => by simp [hw1', h])]
      exact hval
    have h2 := residue_word_injective_aux Q hQ val hinj l w1 w1' h1
    funext j
    have h3 := h2 j j.isLt
    simpa [hw1, hw1', j.isLt] using h3

/-! ## Elementary properties of the digit sets -/

section DigitSets

/-- The value of a digit array, as an integer. -/
theorem flatInt_cast {m : ℕ} (a : Fin m → ℕ) :
    ((D.flatInt m a : ℕ) : ℤ) = ∑ t, (a t : ℤ) * (D.q : ℤ) ^ (t : ℕ) := by
  simp [flatInt]

theorem flatInt_add {m : ℕ} (a b : Fin m → ℕ) :
    D.flatInt m a + D.flatInt m b = D.flatInt m (fun t => a t + b t) := by
  simp only [flatInt, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- A digit array with digits in the mask and small digit sum represents an element of the
digit set `U` of equation (8) (`eq:Um`) of `masked_digit_bound.tex`. -/
theorem flatInt_mem_maskSet {m L : ℕ} (a : Fin m → ℕ) (ha : ∀ t, a t ∈ D.M)
    (hsum : ∑ t, a t ≤ L) : D.flatInt m a ∈ D.maskSet m L := by
  classical
  refine Finset.mem_image.2 ⟨fun t => ⟨a t, ha t⟩, ?_, rfl⟩
  simp [Finset.mem_filter, hsum]

theorem flatInt_mem_sumSet {m T : ℕ} (a : Fin m → ℕ) (ha : ∀ t, a t ∈ D.sumSupport)
    (hsum : ∑ t, a t ≤ T) : D.flatInt m a ∈ D.sumSet m T := by
  classical
  refine Finset.mem_image.2 ⟨fun t => ⟨a t, ha t⟩, ?_, rfl⟩
  simp [Finset.mem_filter, hsum]

/-- Membership in the digit set `U` in terms of digit arrays. -/
theorem mem_maskSet {m L : ℕ} {u : ℕ} (hu : u ∈ D.maskSet m L) :
    ∃ a : Fin m → ℕ, (∀ t, a t ∈ D.M) ∧ (∑ t, a t ≤ L) ∧ D.flatInt m a = u := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
  exact ⟨fun t => ((a t : ℕ)), fun t => (a t).2, by simpa using (Finset.mem_filter.1 ha).2, rfl⟩

/-- The sumset `U + U` consists of digit arrays with digits in `S = M + M` and digit sum at
most `2L`; this is the elementary sumset bound of the proofs of Propositions 2, 4 and 6 of
`masked_digit_bound.tex`. -/
theorem natSumFinset_maskSet_subset (m L : ℕ) :
    natSumFinset (D.maskSet m L) (D.maskSet m L) ⊆ D.sumSet m (2 * L) := by
  intro n hn
  simp only [natSumFinset, Finset.mem_image₂] at hn
  obtain ⟨u, hu, v, hv, rfl⟩ := hn
  obtain ⟨a, ha, hasum, rfl⟩ := D.mem_maskSet hu
  obtain ⟨b, hb, hbsum, rfl⟩ := D.mem_maskSet hv
  rw [flatInt_add]
  refine D.flatInt_mem_sumSet _ (fun t => D.mem_sumSupport.2 ⟨a t, ha t, b t, hb t, rfl⟩) ?_
  rw [Finset.sum_add_distrib]
  omega

/-- Every value of a digit array of length `m` with digits `< q` is smaller than `q ^ m`. -/
theorem flatInt_lt_pow {m : ℕ} (a : Fin m → ℕ) (ha : ∀ t, a t < D.q) :
    D.flatInt m a < D.q ^ m := by
  classical
  have hq0 : 0 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  set a' : ℕ → ℕ := fun t => if h : t < m then a ⟨t, h⟩ else 0 with ha'
  have ha'lt : ∀ t, a' t < D.q := by
    intro t
    by_cases h : t < m
    · simp only [ha', dif_pos h]; exact ha _
    · simpa only [ha', dif_neg h] using hq0
  have key : ∀ n : ℕ, ∑ t ∈ Finset.range n, a' t * D.q ^ t < D.q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have h1 : (a' n + 1) * D.q ^ n ≤ D.q * D.q ^ n :=
        Nat.mul_le_mul_right _ (ha'lt n)
      nlinarith [ih, h1, Nat.zero_le (D.q ^ n)]
  have hconv : D.flatInt m a = ∑ t ∈ Finset.range m, a' t * D.q ^ t := by
    rw [flatInt, ← Fin.sum_univ_eq_sum_range (fun t => a' t * D.q ^ t) m]
    exact Finset.sum_congr rfl fun t _ => by simp [ha', t.isLt]
  rw [hconv]
  exact key m

theorem maskSet_lt_pow {m L : ℕ} {u : ℕ} (hu : u ∈ D.maskSet m L) : u < D.q ^ m := by
  obtain ⟨a, ha, _, rfl⟩ := D.mem_maskSet hu
  exact D.flatInt_lt_pow a fun t => lt_of_le_of_lt (D.digits_le _ (ha t)) D.q_gt_B

theorem zero_mem_maskSet (m L : ℕ) : 0 ∈ D.maskSet m L := by
  have h := D.flatInt_mem_maskSet (m := m) (L := L) (fun _ => 0) (fun _ => D.zero_mem)
    (by simp)
  simpa [flatInt] using h

/-- The largest mask digit `B` belongs to the digit set `U` as soon as the budget allows it;
this is what makes `max U` positive in the applications of the dilated finite-set principle
of `masked_digit_bound.tex`. -/
theorem B_mem_maskSet {m L : ℕ} (hm : 0 < m) (hL : D.B ≤ L) : D.B ∈ D.maskSet m L := by
  classical
  set a : Fin m → ℕ := fun t => if (t : ℕ) = 0 then D.B else 0 with hadef
  have hne : ∀ t : Fin m, t ≠ (⟨0, hm⟩ : Fin m) → (t : ℕ) ≠ 0 := fun t ht h => ht (Fin.ext h)
  have hsum : ((∑ t, a t) = D.B) := by
    rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
    · simp [hadef]
    · intro t _ ht; simp [hadef, hne t ht]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hval : D.flatInt m a = D.B := by
    rw [flatInt, Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
    · simp [hadef]
    · intro t _ ht; simp [hadef, hne t ht]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h := D.flatInt_mem_maskSet (m := m) (L := L) a
    (fun t => by by_cases h : (t : ℕ) = 0 <;> simp [hadef, h, D.B_mem, D.zero_mem])
    (by rw [hsum]; exact hL)
  rwa [hval] at h

end DigitSets

/-! ## The witness arrays of a word -/

section WordWitness

variable {A : Type*} (k : ℕ) (vec : A → Fin k → ℤ)

/-- The array `(α_{d_t})` of first minimum witnesses of the digits of a word, as in the proof
of Proposition 2 of `masked_digit_bound.tex`. -/
noncomputable def wordAlpha {l : ℕ} (w : Fin l → A) (t : Fin (l * k)) : ℕ :=
  (D.wit (wordDigits k vec w t)).1

/-- The array `(β_{d_t})` of second minimum witnesses of the digits of a word, as in the
proof of Proposition 2 of `masked_digit_bound.tex`. -/
noncomputable def wordBeta {l : ℕ} (w : Fin l → A) (t : Fin (l * k)) : ℕ :=
  (D.wit (wordDigits k vec w t)).2

/-- The integer represented by a word of blocks, in base `q ^ k`. -/
def wordVal {l : ℕ} (w : Fin l → A) : ℤ :=
  ∑ j, D.blockVal k (vec (w j)) * ((D.q : ℤ) ^ k) ^ (j : ℕ)

variable (hvec : ∀ a i, vec a i ∈ D.diffSupport)
include hvec

theorem wordDigits_mem_diffSupport {l : ℕ} (w : Fin l → A) (t : Fin (l * k)) :
    wordDigits k vec w t ∈ D.diffSupport := hvec _ _

theorem wordAlpha_mem {l : ℕ} (w : Fin l → A) (t : Fin (l * k)) :
    D.wordAlpha k vec w t ∈ D.M := D.wit_fst_mem (hvec _ _)

theorem wordBeta_mem {l : ℕ} (w : Fin l → A) (t : Fin (l * k)) :
    D.wordBeta k vec w t ∈ D.M := D.wit_snd_mem (hvec _ _)

/-- The two witness digits differ by the signed digit: `α_d - β_d = d`. -/
theorem wordAlpha_sub_wordBeta {l : ℕ} (w : Fin l → A) (t : Fin (l * k)) :
    (D.wordAlpha k vec w t : ℤ) - (D.wordBeta k vec w t : ℤ) = wordDigits k vec w t :=
  D.wit_sub (hvec _ _)

/-- The two witness digits add up to the minimum witness cost: `α_d + β_d = κ(d)`. -/
theorem wordAlpha_add_wordBeta {l : ℕ} (w : Fin l → A) (t : Fin (l * k)) :
    D.wordAlpha k vec w t + D.wordBeta k vec w t = D.kappa (wordDigits k vec w t) :=
  D.wit_add (hvec _ _)

/-- The total digit sum of the two witness arrays is the total minimum witness cost of the
word; this is the first of the two digit budgets in the proof of Proposition 2 of
`masked_digit_bound.tex`. -/
theorem sum_wordAlpha_add_sum_wordBeta {l : ℕ} (w : Fin l → A) :
    (∑ t, D.wordAlpha k vec w t) + (∑ t, D.wordBeta k vec w t)
      = ∑ j, D.blockCost k (vec (w j)) := by
  rw [← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun t _ => D.wordAlpha_add_wordBeta k vec hvec w t),
    sum_wordDigits k vec (fun d => D.kappa d) w]
  rfl

/-- The difference of the digit sums of the two witness arrays is the unweighted digit sum
of the word; this is the second digit budget in the proof of Proposition 2 of
`masked_digit_bound.tex`. -/
theorem sum_wordAlpha_sub_sum_wordBeta {l : ℕ} (w : Fin l → A) :
    ((∑ t, D.wordAlpha k vec w t : ℕ) : ℤ) - ((∑ t, D.wordBeta k vec w t : ℕ) : ℤ)
      = ∑ j, blockSum k (vec (w j)) := by
  push_cast
  rw [← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun t _ => D.wordAlpha_sub_wordBeta k vec hvec w t),
    sum_wordDigits k vec (fun d => d) w]
  rfl

/-- The word is recovered as the difference of the two digit-array values: this is the map
`w ↦ u - v` with `u, v ∈ U` in the proof of Proposition 2 of `masked_digit_bound.tex`. -/
theorem flatInt_wordAlpha_sub_flatInt_wordBeta {l : ℕ} (w : Fin l → A) :
    ((D.flatInt (l * k) (D.wordAlpha k vec w) : ℕ) : ℤ)
        - ((D.flatInt (l * k) (D.wordBeta k vec w) : ℕ) : ℤ) = D.wordVal k vec w := by
  rw [flatInt_cast, flatInt_cast, ← Finset.sum_sub_distrib]
  have h1 : ∀ t : Fin (l * k),
      (D.wordAlpha k vec w t : ℤ) * (D.q : ℤ) ^ (t : ℕ)
        - (D.wordBeta k vec w t : ℤ) * (D.q : ℤ) ^ (t : ℕ)
      = wordDigits k vec w t * (D.q : ℤ) ^ (t : ℕ) := by
    intro t
    rw [← sub_mul, D.wordAlpha_sub_wordBeta k vec hvec w t]
  rw [Finset.sum_congr rfl (fun t _ => h1 t),
    sum_pow_decomp k (D.q : ℤ) l (wordDigits k vec w)]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [wordDigits_apply]

end WordWitness

/-! ## The finite-set principle applied to the masked digit set -/

/-- **The dilated finite-set principle for the masked digit set `U`.**  This packages the
application of equation (2) (`eq:GHR-dilated`) of `masked_digit_bound.tex` to `U = U_m(L)`:
given a lower bound `nd` for `|U - U|` and an upper bound `ns` for `|U + U|` with
`nd ≥ ns`, and using `max U < q^m`, one gets
`C₃ₐ ≥ 1 + log(nd/ns) / (log 5 + m log q)`. -/
theorem ghr_from_maskSet_estimates {m L : ℕ} (hm : 0 < m) (hL : D.B ≤ L)
    (nd ns : ℝ) (hnd0 : 0 < nd) (hns0 : 0 < ns)
    (hnd : nd ≤ ((natDiffFinset (D.maskSet m L) (D.maskSet m L)).card : ℝ))
    (hns : ((natSumFinset (D.maskSet m L) (D.maskSet m L)).card : ℝ) ≤ ns)
    (hratio : 1 ≤ nd / ns) :
    1 + Real.log (nd / ns) / (Real.log 5 + m * Real.log D.q) ≤ C3a := by
  classical
  set U := D.maskSet m L with hU
  have h0 : 0 ∈ U := D.zero_mem_maskSet m L
  have hne : U.Nonempty := ⟨0, h0⟩
  have hBmem : D.B ∈ U := D.B_mem_maskSet hm hL
  have hmaxB : D.B ≤ U.max' hne := Finset.le_max' _ _ hBmem
  have hmax : 0 < U.max' hne := lt_of_lt_of_le D.B_pos hmaxB
  have hmaxlt : U.max' hne < D.q ^ m := D.maskSet_lt_pow (U.max'_mem hne)
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hqR : (1 : ℝ) < (D.q : ℝ) := by exact_mod_cast hq1
  have hlogq : 0 < Real.log D.q := Real.log_pos hqR
  -- the two cardinalities
  set dc : ℝ := ((natDiffFinset U U).card : ℝ) with hdc
  set sc : ℝ := ((natSumFinset U U).card : ℝ) with hsc
  have hsc0 : 0 < sc := by
    have : (0 : ℕ) ∈ natSumFinset U U := by
      simp only [natSumFinset, Finset.mem_image₂]
      exact ⟨0, h0, 0, h0, rfl⟩
    have hcard : 0 < (natSumFinset U U).card := Finset.card_pos.2 ⟨0, this⟩
    rw [hsc]
    exact_mod_cast hcard
  -- the ratio comparison
  have hcmp : nd / ns ≤ dc / sc := by
    apply div_le_div₀ (le_trans hnd0.le hnd) hnd hsc0 hns
  have hlogcmp : Real.log (nd / ns) ≤ Real.log (dc / sc) :=
    Real.log_le_log (by positivity) hcmp
  have hlognn : 0 ≤ Real.log (nd / ns) := Real.log_nonneg hratio
  -- the denominator
  set Dn : ℝ := Real.log (4 * (U.max' hne : ℝ) + 1) with hDn
  have hmaxR : (1 : ℝ) ≤ (U.max' hne : ℝ) := by exact_mod_cast hmax
  have hDn0 : 0 < Dn := by
    rw [hDn]
    apply Real.log_pos
    linarith
  have hDnle : Dn ≤ Real.log 5 + m * Real.log D.q := by
    have h1 : 4 * (U.max' hne : ℝ) + 1 ≤ 5 * (D.q : ℝ) ^ m := by
      have h2 : ((U.max' hne : ℕ) : ℝ) + 1 ≤ ((D.q : ℝ) ^ m) := by
        have : (U.max' hne : ℕ) + 1 ≤ D.q ^ m := hmaxlt
        exact_mod_cast this
      nlinarith [pow_pos (lt_trans zero_lt_one hqR) m]
    calc Dn ≤ Real.log (5 * (D.q : ℝ) ^ m) := Real.log_le_log (by linarith) h1
      _ = Real.log 5 + m * Real.log D.q := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  -- apply the dilated principle
  have hghr := ghr_dilated_lower_bound U h0 hne hmax
  refine le_trans ?_ hghr
  have hstep1 : Real.log (nd / ns) / (Real.log 5 + m * Real.log D.q)
      ≤ Real.log (nd / ns) / Dn := by
    gcongr
  have hstep2 : Real.log (nd / ns) / Dn ≤ Real.log (dc / sc) / Dn := by
    gcongr
  linarith

/-- The elementary limit `(lK + c₀)/(c₅ + lM) → K/M` used to let the number of blocks tend to
infinity in the proofs of `masked_digit_bound.tex`. -/
theorem tendsto_affine_ratio (K c0 c5 M : ℝ) (hM : 0 < M) :
    Filter.Tendsto (fun l : ℕ => ((l : ℝ) * K + c0) / (c5 + (l : ℝ) * M))
      Filter.atTop (nhds (K / M)) := by
  have h1 : Filter.Tendsto (fun l : ℕ => (K + c0 / (l : ℝ)) / (c5 / (l : ℝ) + M))
      Filter.atTop (nhds ((K + 0) / (0 + M))) := by
    apply Filter.Tendsto.div
    · exact tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat c0)
    · exact (tendsto_const_div_atTop_nhds_zero_nat c5).add tendsto_const_nhds
    · simpa using ne_of_gt hM
  rw [show (K + 0) / (0 + M) = K / M by ring_nf] at h1
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with l hl
  have hl0 : ((l : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  field_simp

/-! ## The core construction theorem -/

set_option maxHeartbeats 4000000 in
/-- **The core digit construction.**  This is the common content of the proofs of
Proposition 2 (`prop:masked`), Proposition 3 (`prop:controlled-block`) and Proposition 5
(`prop:two-pressure`) of `masked_digit_bound.tex`.

Given a mask `D`, a block length `k ≥ 1` and a finite alphabet `A` of signed digit blocks
which is closed under negation (`neg`) and whose blocks have pairwise distinct residues
modulo `q ^ k`, together with a sum-side bound `Pp` in the sense of `hPp`, the partition sum
`Z = ∑_{a ∈ A} x ^ cost(a)` yields

`C₃ₐ ≥ 1 + (k⁻¹ log Z - log Pp) / log q`.

Taking `k = 1`, `q = 2B + 1`, `A = D = M - M` and `Pp = P₊(x)` gives Proposition 2, in which
`Z = P₋(x)`.  Taking `A` to be a system of minimum-cost representatives of the attainable
residues modulo `q ^ k` gives Proposition 3, and taking `Pp = W_l(x)^{1/l}` gives the
two-block bound (25) (`eq:finite-two-block-bound`). -/
theorem core_bound (k : ℕ) (hk : 0 < k) {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (vec : A → Fin k → ℤ) (hvec : ∀ a i, vec a i ∈ D.diffSupport)
    (neg : A → A) (hneginv : Function.Involutive neg)
    (hneg : ∀ a, vec (neg a) = -vec a)
    (hinj : Function.Injective fun a => (D.blockVal k (vec a) : ZMod (D.q ^ k)))
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (Pp C : ℝ) (hPp0 : 0 < Pp) (hC0 : 0 < C)
    (hPp : ∀ m T : ℕ, ((D.sumSet m T).card : ℝ) * x ^ T ≤ C * Pp ^ m) :
    1 + (Real.log (∑ a : A, x ^ D.blockCost k (vec a)) / k - Real.log Pp) /
        Real.log D.q ≤ C3a := by
  classical
  -- the cost and the digit sum of a block, the partition function and the Gibbs weights
  set c : A → ℕ := fun a => D.blockCost k (vec a) with hcdef
  set sd : A → ℤ := fun a => blockSum k (vec a) with hsddef
  set Z : ℝ := ∑ a, x ^ c a with hZdef
  have hZ0 : 0 < Z := ProductWeights.gibbs_partition_pos hx0 c
  set p : A → ℝ := ProductWeights.gibbs x c with hpdef
  have hp0 : ∀ a, 0 ≤ p a := fun a => ProductWeights.gibbs_nonneg hx0 c a
  have hpsum : ∑ a, p a = 1 := ProductWeights.sum_gibbs hx0 c
  set mu : ℝ := ∑ a, p a * (c a : ℝ) with hmudef
  have hmu0 : 0 ≤ mu := Finset.sum_nonneg fun a _ => mul_nonneg (hp0 a) (Nat.cast_nonneg _)
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hqR : (1 : ℝ) < (D.q : ℝ) := by exact_mod_cast hq1
  have hlogq : 0 < Real.log D.q := Real.log_pos hqR
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlogx : Real.log x < 0 := Real.log_neg hx0 hx1
  -- the two centred statistics of the construction
  set g1 : A → ℝ := fun a => (c a : ℝ) - mu with hg1def
  set g2 : A → ℝ := fun a => (sd a : ℝ) with hg2def
  have hg1c : ∑ a, p a * g1 a = 0 := by
    simp only [hg1def, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpsum, ← hmudef]
    ring
  have hcneg : ∀ a, c (neg a) = c a := by
    intro a
    simp only [hcdef, blockCost, hneg a, Pi.neg_apply]
    exact Finset.sum_congr rfl fun i _ => D.kappa_neg _
  have hsdneg : ∀ a, sd (neg a) = - sd a := by
    intro a
    simp [hsddef, blockSum, hneg a]
  have hpneg : ∀ a, p (neg a) = p a := by
    intro a; simp only [hpdef, ProductWeights.gibbs, hcneg a]
  have hg2c : ∑ a, p a * g2 a = 0 := by
    have h1 : ∑ a, p (neg a) * g2 (neg a) = ∑ a, p a * g2 a :=
      Equiv.sum_comp hneginv.toPerm (fun a => p a * g2 a)
    have h2 : ∀ a, p (neg a) * g2 (neg a) = -(p a * g2 a) := by
      intro a; rw [hpneg a]; simp only [hg2def, hsdneg a]; push_cast; ring
    rw [Finset.sum_congr rfl (fun a _ => h2 a), Finset.sum_neg_distrib] at h1
    linarith
  -- if the claimed bound does not exceed `1`, it is trivial
  rcases le_or_gt (Real.log Z / k - Real.log Pp) 0 with hdel | hdel
  · have h1 : (Real.log Z / k - Real.log Pp) / Real.log D.q ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hdel hlogq.le
    linarith [one_le_C3a]
  set delta : ℝ := Real.log Z / (k : ℝ) - Real.log Pp with hdeltadef
  have hdelta0 : 0 < delta := hdel
  -- the key estimate, for each admissible `ε`
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have claim : ∀ eps : ℝ, 0 < eps → 0 < (k : ℝ) * delta + 3 * eps * Real.log x →
      1 + ((k : ℝ) * delta + 3 * eps * Real.log x) / ((k : ℝ) * Real.log D.q) ≤ C3a := by
    intro eps heps0 hKpos
    set K : ℝ := (k : ℝ) * delta + 3 * eps * Real.log x with hKdef
    set c0 : ℝ := (2 + 2 * (D.B : ℝ)) * Real.log x - Real.log 2 - Real.log C with hc0def
    set V1 : ℝ := ∑ a, p a * g1 a ^ 2 with hV1def
    set V2 : ℝ := ∑ a, p a * g2 a ^ 2 with hV2def
    have hV1n : 0 ≤ V1 := Finset.sum_nonneg fun a _ => mul_nonneg (hp0 a) (sq_nonneg _)
    have hV2n : 0 ≤ V2 := Finset.sum_nonneg fun a _ => mul_nonneg (hp0 a) (sq_nonneg _)
    -- a word of blocks is determined by the integer it represents
    have hQpos : 0 < D.q ^ k := pow_pos (by omega) k
    have hwordinj : ∀ l : ℕ, Function.Injective (fun w : Fin l → A => D.wordVal k vec w) := by
      intro l w w' hww
      have h := residue_word_injective (D.q ^ k) hQpos (fun a => D.blockVal k (vec a)) hinj l
      have e : ∀ v : Fin l → A,
          (∑ j, D.blockVal k (vec (v j)) * ((D.q ^ k : ℕ) : ℤ) ^ (j : ℕ)) = D.wordVal k vec v := by
        intro v
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast
        ring
      exact h (by simpa only [e w, e w'] using hww)
    -- the estimate for all large numbers of blocks
    have key : ∀ᶠ l : ℕ in Filter.atTop,
        1 + ((l : ℝ) * K + c0) / (Real.log 5 + (l : ℝ) * ((k : ℝ) * Real.log D.q)) ≤ C3a := by
      obtain ⟨N1, hN1⟩ := exists_nat_gt (2 * (V1 + V2) / eps ^ 2)
      obtain ⟨N2, hN2⟩ := exists_nat_gt ((-c0) / K)
      rw [Filter.eventually_atTop]
      refine ⟨max (max N1 N2) 1, fun l hl => ?_⟩
      have hl1 : 1 ≤ l := le_trans (le_max_right _ _) hl
      have hl0 : 0 < l := hl1
      have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
      have hlN1 : 2 * (V1 + V2) / eps ^ 2 < (l : ℝ) := by
        refine lt_of_lt_of_le hN1 ?_
        have h : N1 ≤ l := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hl
        exact_mod_cast h
      have hlN2 : (-c0) / K < (l : ℝ) := by
        refine lt_of_lt_of_le hN2 ?_
        have h : N2 ≤ l := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hl
        exact_mod_cast h
      have hepsl : (0 : ℝ) < eps * (l : ℝ) := by positivity
      -- the good set of words
      set G : Finset (Fin l → A) := Finset.univ.filter
        (fun w => |∑ j, g1 (w j)| < eps * (l : ℝ) ∧ |∑ j, g2 (w j)| < eps * (l : ℝ)) with hGdef
      -- the good set carries at least half of the mass
      have hmass : (1 : ℝ) / 2 ≤ ∑ w ∈ G, ProductWeights.wt p w := by
        rw [hGdef]
        have hbad1 := ProductWeights.mass_deviation_le p hp0 hpsum g1 hg1c l hepsl
        have hbad2 := ProductWeights.mass_deviation_le p hp0 hpsum g2 hg2c l hepsl
        have htot : ∑ w : Fin l → A, ProductWeights.wt p w = 1 := ProductWeights.sum_wt p hpsum l
        have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin l → A))
          (fun w => |∑ j, g1 (w j)| < eps * (l : ℝ) ∧ |∑ j, g2 (w j)| < eps * (l : ℝ))
          (ProductWeights.wt p)
        have hnn : ∀ w : Fin l → A, 0 ≤ ProductWeights.wt p w :=
          fun w => ProductWeights.wt_nonneg hp0 w
        have hsub : Finset.univ.filter (fun w : Fin l → A =>
            ¬(|∑ j, g1 (w j)| < eps * (l : ℝ) ∧ |∑ j, g2 (w j)| < eps * (l : ℝ))) ⊆
            (Finset.univ.filter (fun w : Fin l → A => eps * (l : ℝ) ≤ |∑ j, g1 (w j)|)) ∪
            (Finset.univ.filter (fun w : Fin l → A => eps * (l : ℝ) ≤ |∑ j, g2 (w j)|)) := by
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and,
            not_and_or, not_lt] at hw ⊢
          tauto
        have h3 : ∑ w ∈ Finset.univ.filter (fun w : Fin l → A =>
              ¬(|∑ j, g1 (w j)| < eps * (l : ℝ) ∧ |∑ j, g2 (w j)| < eps * (l : ℝ))),
              ProductWeights.wt p w
            ≤ (∑ w ∈ Finset.univ.filter (fun w : Fin l → A => eps * (l : ℝ) ≤ |∑ j, g1 (w j)|),
                ProductWeights.wt p w)
              + ∑ w ∈ Finset.univ.filter (fun w : Fin l → A => eps * (l : ℝ) ≤ |∑ j, g2 (w j)|),
                ProductWeights.wt p w := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => hnn w)) ?_
          have hui := Finset.sum_union_inter
            (s₁ := Finset.univ.filter (fun w : Fin l → A => eps * (l : ℝ) ≤ |∑ j, g1 (w j)|))
            (s₂ := Finset.univ.filter (fun w : Fin l → A => eps * (l : ℝ) ≤ |∑ j, g2 (w j)|))
            (f := ProductWeights.wt p)
          have h4 : 0 ≤ ∑ w ∈ (Finset.univ.filter (fun w : Fin l → A =>
              eps * (l : ℝ) ≤ |∑ j, g1 (w j)|)) ∩
              (Finset.univ.filter (fun w : Fin l → A => eps * (l : ℝ) ≤ |∑ j, g2 (w j)|)),
              ProductWeights.wt p w := Finset.sum_nonneg fun w _ => hnn w
          linarith
        have hnum : ((l : ℝ) * V1) / (eps * (l : ℝ)) ^ 2 + ((l : ℝ) * V2) / (eps * (l : ℝ)) ^ 2
            ≤ 1 / 2 := by
          rw [← add_div, div_le_iff₀ (by positivity)]
          have h5 : 2 * (V1 + V2) < eps ^ 2 * (l : ℝ) := by
            rw [div_lt_iff₀ (by positivity)] at hlN1
            linarith
          nlinarith [hlR]
        linarith
      -- the digit budget
      set L : ℕ := ⌈(mu + 2 * eps) * (l : ℝ) / 2⌉₊ + D.B with hLdef
      have hLB : D.B ≤ L := Nat.le_add_left _ _
      have hyn : (0 : ℝ) ≤ (mu + 2 * eps) * (l : ℝ) / 2 := by
        apply div_nonneg _ (by norm_num)
        exact mul_nonneg (by linarith) hlR.le
      have hceil : ((⌈(mu + 2 * eps) * (l : ℝ) / 2⌉₊ : ℕ) : ℝ) < (mu + 2 * eps) * (l : ℝ) / 2 + 1 :=
        Nat.ceil_lt_add_one hyn
      have hceil' : (mu + 2 * eps) * (l : ℝ) / 2 ≤ ((⌈(mu + 2 * eps) * (l : ℝ) / 2⌉₊ : ℕ) : ℝ) :=
        Nat.le_ceil _
      -- the digit sums of a good word obey the budget
      have hg1sum : ∀ w : Fin l → A,
          ∑ j, g1 (w j) = ((∑ j, c (w j) : ℕ) : ℝ) - mu * (l : ℝ) := by
        intro w
        simp only [hg1def]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        push_cast
        ring
      have hg2sum : ∀ w : Fin l → A, ∑ j, g2 (w j) = ((∑ j, sd (w j) : ℤ) : ℝ) := by
        intro w
        simp only [hg2def]
        push_cast
        ring
      have hbudget : ∀ w ∈ G,
          (∑ t, D.wordAlpha k vec w t) ≤ L ∧ (∑ t, D.wordBeta k vec w t) ≤ L := by
        intro w hw
        rw [hGdef, Finset.mem_filter] at hw
        obtain ⟨-, hw1, hw2⟩ := hw
        rw [hg1sum w, abs_lt] at hw1
        rw [hg2sum w, abs_lt] at hw2
        obtain ⟨hw1a, hw1b⟩ := hw1
        obtain ⟨hw2a, hw2b⟩ := hw2
        have hcostid : (∑ t, D.wordAlpha k vec w t) + (∑ t, D.wordBeta k vec w t)
            = ∑ j, c (w j) := D.sum_wordAlpha_add_sum_wordBeta k vec hvec w
        have hdiffid : ((∑ t, D.wordAlpha k vec w t : ℕ) : ℤ)
            - ((∑ t, D.wordBeta k vec w t : ℕ) : ℤ) = ∑ j, sd (w j) :=
          D.sum_wordAlpha_sub_sum_wordBeta k vec hvec w
        have h1 : ((∑ t, D.wordAlpha k vec w t : ℕ) : ℝ) + ((∑ t, D.wordBeta k vec w t : ℕ) : ℝ)
            = ((∑ j, c (w j) : ℕ) : ℝ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcostid
        have h2 : ((∑ t, D.wordAlpha k vec w t : ℕ) : ℝ) - ((∑ t, D.wordBeta k vec w t : ℕ) : ℝ)
            = ((∑ j, sd (w j) : ℤ) : ℝ) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hdiffid
        have hLR : (L : ℝ) = ((⌈(mu + 2 * eps) * (l : ℝ) / 2⌉₊ : ℕ) : ℝ) + (D.B : ℝ) := by
          rw [hLdef]; push_cast; ring
        have hB0 : (0 : ℝ) ≤ (D.B : ℝ) := Nat.cast_nonneg _
        constructor
        · have hA : ((∑ t, D.wordAlpha k vec w t : ℕ) : ℝ) ≤ (L : ℝ) := by
            rw [hLR]; linarith
          exact_mod_cast hA
        · have hB : ((∑ t, D.wordBeta k vec w t : ℕ) : ℝ) ≤ (L : ℝ) := by
            rw [hLR]; linarith
          exact_mod_cast hB
      -- the good words inject into the difference set
      have hGdiff : (G.card : ℝ)
          ≤ ((natDiffFinset (D.maskSet (l * k) L) (D.maskSet (l * k) L)).card : ℝ) := by
        have hcard : G.card ≤ (natDiffFinset (D.maskSet (l * k) L) (D.maskSet (l * k) L)).card := by
          refine Finset.card_le_card_of_injOn (fun w => D.wordVal k vec w) ?_ ?_
          · intro w hw
            obtain ⟨hA, hB⟩ := hbudget w hw
            simp only [natDiffFinset, Finset.mem_coe]
            rw [← D.flatInt_wordAlpha_sub_flatInt_wordBeta k vec hvec w]
            exact Finset.mem_image₂_of_mem (f := fun (a b : ℕ) => (a : ℤ) - (b : ℤ))
              (D.flatInt_mem_maskSet _ (fun t => D.wordAlpha_mem k vec hvec w t) hA)
              (D.flatInt_mem_maskSet _ (fun t => D.wordBeta_mem k vec hvec w t) hB)
          · intro w _ w' _ h
            exact hwordinj l h
        exact_mod_cast hcard
      -- the lower bound for the difference set
      set nd : ℝ := Z ^ l / (2 * x ^ ((mu - eps) * (l : ℝ))) with hnddef
      have hxrpow : (0 : ℝ) < x ^ ((mu - eps) * (l : ℝ)) := Real.rpow_pos_of_pos hx0 _
      have hnd0 : 0 < nd := by rw [hnddef]; positivity
      have hcardnd : nd ≤ (G.card : ℝ) := by
        have hW0 : (0 : ℝ) < x ^ ((mu - eps) * (l : ℝ)) / Z ^ l := by positivity
        have hwtle : ∀ w ∈ G,
            ProductWeights.wt p w ≤ x ^ ((mu - eps) * (l : ℝ)) / Z ^ l := by
          intro w hw
          rw [hGdef, Finset.mem_filter] at hw
          obtain ⟨-, hw1, -⟩ := hw
          rw [hg1sum w, abs_lt] at hw1
          have hexp : (mu - eps) * (l : ℝ) ≤ ((∑ j, c (w j) : ℕ) : ℝ) := by linarith [hw1.1]
          have hpow : x ^ (((∑ j, c (w j) : ℕ)) : ℝ) ≤ x ^ ((mu - eps) * (l : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le hexp
          rw [Real.rpow_natCast] at hpow
          rw [hpdef, ProductWeights.wt_gibbs, ← hZdef]
          gcongr
        have hsumle : ∑ w ∈ G, ProductWeights.wt p w
            ≤ (G.card : ℝ) * (x ^ ((mu - eps) * (l : ℝ)) / Z ^ l) := by
          calc ∑ w ∈ G, ProductWeights.wt p w
              ≤ ∑ _w ∈ G, (x ^ ((mu - eps) * (l : ℝ)) / Z ^ l) := Finset.sum_le_sum hwtle
            _ = (G.card : ℝ) * (x ^ ((mu - eps) * (l : ℝ)) / Z ^ l) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        have hmul : nd * (x ^ ((mu - eps) * (l : ℝ)) / Z ^ l) = 1 / 2 := by
          rw [hnddef]
          field_simp
        refine le_of_mul_le_mul_right ?_ hW0
        rw [hmul]
        linarith
      -- the upper bound for the sumset
      set E : ℝ := (mu + 2 * eps) * (l : ℝ) + 2 + 2 * (D.B : ℝ) with hEdef
      have h2L : ((2 * L : ℕ) : ℝ) ≤ E := by
        rw [hLdef, hEdef]
        push_cast
        linarith
      have hxE : (0 : ℝ) < x ^ E := Real.rpow_pos_of_pos hx0 _
      set ns : ℝ := C * Pp ^ (l * k) / x ^ E with hnsdef
      have hns0 : 0 < ns := by rw [hnsdef]; positivity
      have hnsle : ((natSumFinset (D.maskSet (l * k) L) (D.maskSet (l * k) L)).card : ℝ) ≤ ns := by
        have h1 : ((natSumFinset (D.maskSet (l * k) L) (D.maskSet (l * k) L)).card : ℝ)
            ≤ ((D.sumSet (l * k) (2 * L)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (D.natSumFinset_maskSet_subset (l * k) L)
        have h2 := hPp (l * k) (2 * L)
        have h3 : x ^ E ≤ x ^ ((2 * L : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le h2L
        rw [Real.rpow_natCast] at h3
        have h4 : ((D.sumSet (l * k) (2 * L)).card : ℝ) ≤ C * Pp ^ (l * k) / x ^ (2 * L) := by
          rw [le_div_iff₀ (pow_pos hx0 _)]
          exact h2
        have h5 : C * Pp ^ (l * k) / x ^ (2 * L) ≤ ns := by
          rw [hnsdef]
          gcongr
        linarith
      -- the logarithm of the ratio
      have hlognd : Real.log nd
          = (l : ℝ) * Real.log Z - Real.log 2 - ((mu - eps) * (l : ℝ)) * Real.log x := by
        rw [hnddef, Real.log_div (by positivity) (by positivity), Real.log_pow,
          Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]
        ring
      have hlogns : Real.log ns
          = Real.log C + ((l * k : ℕ) : ℝ) * Real.log Pp - E * Real.log x := by
        rw [hnsdef, Real.log_div (by positivity) (by positivity),
          Real.log_mul (ne_of_gt hC0) (by positivity), Real.log_pow, Real.log_rpow hx0]
      have hlogval : Real.log (nd / ns) = (l : ℝ) * K + c0 := by
        rw [Real.log_div (ne_of_gt hnd0) (ne_of_gt hns0), hlognd, hlogns, hKdef, hc0def, hEdef,
          hdeltadef]
        push_cast
        field_simp
        ring
      have hnum0 : 0 ≤ (l : ℝ) * K + c0 := by
        rw [div_lt_iff₀ hKpos] at hlN2
        linarith
      have hratio : 1 ≤ nd / ns := by
        have hlog : 0 ≤ Real.log (nd / ns) := by rw [hlogval]; exact hnum0
        exact (Real.log_nonneg_iff (by positivity)).1 hlog
      have hfin := D.ghr_from_maskSet_estimates (m := l * k) (L := L)
        (Nat.mul_pos hl0 hk) hLB nd ns hnd0 hns0 (le_trans hcardnd hGdiff) hnsle hratio
      rw [hlogval] at hfin
      have hcast : ((l * k : ℕ) : ℝ) * Real.log D.q = (l : ℝ) * ((k : ℝ) * Real.log D.q) := by
        push_cast; ring
      rw [hcast] at hfin
      exact hfin
    have hlim : Filter.Tendsto
        (fun l : ℕ => 1 + ((l : ℝ) * K + c0) / (Real.log 5 + (l : ℝ) * ((k : ℝ) * Real.log D.q)))
        Filter.atTop (nhds (1 + K / ((k : ℝ) * Real.log D.q))) :=
      tendsto_const_nhds.add
        (tendsto_affine_ratio K c0 (Real.log 5) ((k : ℝ) * Real.log D.q) (mul_pos hkR hlogq))
    exact le_of_tendsto hlim key
  -- let `ε → 0`
  refine le_of_forall_pos_le_add ?_
  intro eta heta
  set lx : ℝ := -Real.log x with hlxdef
  have hlx0 : 0 < lx := by rw [hlxdef]; linarith
  set eps : ℝ := min ((k : ℝ) * delta / (6 * lx)) (eta * ((k : ℝ) * Real.log D.q) / (6 * lx))
    with hepsdef
  have heps0 : 0 < eps := by
    refine lt_min ?_ ?_
    · have : 0 < (k : ℝ) * delta := mul_pos hkR hdelta0
      positivity
    · have : 0 < eta * ((k : ℝ) * Real.log D.q) := by positivity
      positivity
  have h6lx : (0 : ℝ) < 6 * lx := by linarith
  have heps1 : eps * (6 * lx) ≤ (k : ℝ) * delta := by
    have := min_le_left ((k : ℝ) * delta / (6 * lx)) (eta * ((k : ℝ) * Real.log D.q) / (6 * lx))
    rw [← hepsdef] at this
    rwa [le_div_iff₀ h6lx] at this
  have heps2 : eps * (6 * lx) ≤ eta * ((k : ℝ) * Real.log D.q) := by
    have := min_le_right ((k : ℝ) * delta / (6 * lx)) (eta * ((k : ℝ) * Real.log D.q) / (6 * lx))
    rw [← hepsdef] at this
    rwa [le_div_iff₀ h6lx] at this
  have hK : 0 < (k : ℝ) * delta + 3 * eps * Real.log x := by
    have hkd : 0 < (k : ℝ) * delta := mul_pos hkR hdelta0
    have : 3 * eps * Real.log x = -(eps * (6 * lx)) / 2 := by rw [hlxdef]; ring
    rw [this]
    linarith
  have hmain := claim eps heps0 hK
  -- rewrite the bound and absorb the error into `η`
  have hQ0 : (0 : ℝ) < (k : ℝ) * Real.log D.q := mul_pos hkR hlogq
  have hsplit : ((k : ℝ) * delta + 3 * eps * Real.log x) / ((k : ℝ) * Real.log D.q)
      = delta / Real.log D.q - (3 * eps * lx) / ((k : ℝ) * Real.log D.q) := by
    rw [hlxdef]
    field_simp
    ring
  have hfrac : (3 * eps * lx) / ((k : ℝ) * Real.log D.q) ≤ eta := by
    rw [div_le_iff₀ hQ0]
    have hA : 0 < eps * lx := mul_pos heps0 hlx0
    linarith
  rw [hsplit] at hmain
  linarith

end MaskData

end MaskedDigit
