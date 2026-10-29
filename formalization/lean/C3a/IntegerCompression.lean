/-
Copyright (c) 2026 Carson Olafson. Released under Apache 2.0.
Author: Carson Olafson, with GPT-6 Astra assistance.
-/
import C3a.CyclicCompression
import RequestProject.GHRConstant

/-! # Lifting a finite-field compression to nonnegative integers

We use Kleinwaks's dilation form of the GHR principle. Therefore the image
need not be rescaled to contain -1, and no strict upper bound on the lifted
difference set is needed. Dilation costs only a fixed logarithmic term.
-/
open scoped BigOperators Pointwise
open Finset

namespace C3a

/-- Integer vectors reduced coordinatewise modulo a prime. -/
def reduceVec {ι : Type*} (p : ℕ) (w : ι → ℤ) : ι → ZMod p := fun i => w i

/-- Reduction is injective on a box narrower than the modulus. -/
theorem reduceVec_injOn {ι : Type*} (W : Finset (ι → ℤ)) (B p : ℕ)
    (hB : 2 * B < p) (hW : ∀ w ∈ W, ∀ i, |w i| ≤ (B : ℤ)) :
    Set.InjOn (reduceVec (ι := ι) p) W := by
  intro a ha b hb hab
  funext i
  have hd : (p : ℤ) ∣ b i - a i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun hab i)
  have hlt : (b i - a i).natAbs < (p : ℤ).natAbs := by
    have ha' := hW a ha i
    have hb' := hW b hb i
    rw [abs_le] at ha' hb'
    omega
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hlt
  omega

/-- The quotient map, as an additive homomorphism on integer vectors. -/
def quotientMap {ι : Type*} [Fintype ι] (p : ℕ) (c : ι → ZMod p) :
    (ι → ℤ) →+ ZMod p where
  toFun w := ∑ i, c i * (w i : ZMod p)
  map_zero' := by simp
  map_add' := by intro a b; simp [mul_add, sum_add_distrib]

/-- Controlled collisions for bounded integer vectors. -/
theorem exists_integer_compression {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Finset (ι → ℤ)) (B p : ℕ) [Fact p.Prime]
    (hB : 2 * B < p) (hW : ∀ w ∈ W, ∀ i, |w i| ≤ (B : ℤ))
    (hne : W.Nonempty) (hcard : W.card < p) :
    ∃ φ : (ι → ℤ) →+ ZMod p, W.card < 2 * (W.image φ).card := by
  classical
  have hi := reduceVec_injOn W B p hB hW
  have hc : (W.image (reduceVec p)).card = W.card := card_image_of_injOn hi
  obtain ⟨c, h⟩ := exists_large_dot_image (W.image (reduceVec p)) (hne.image _)
    (by simpa [hc, ZMod.card] using hcard)
  refine ⟨quotientMap p c, ?_⟩
  simpa only [hc, image_image, quotientMap, dotHom, reduceVec] using h

/-- A set in `[0,2p)` has at most twice as many elements as residues. -/
theorem card_le_two_mul_residue_image (S : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (hS : ∀ n ∈ S, n < 2 * p) :
    S.card ≤ 2 * (S.image fun n : ℕ => (n : ZMod p)).card := by
  classical
  let T := (S.image fun n : ℕ => (n : ZMod p)) ×ˢ range 2
  have h := card_le_card_of_injOn (s := S) (t := T)
    (fun n => ((n : ZMod p), n / p))
    (fun n hn => mem_product.mpr ⟨mem_image_of_mem _ hn,
      mem_range.mpr ((Nat.div_lt_iff_lt_mul hp).mpr (by simpa [mul_comm] using hS n hn))⟩)
    (by
      intro a ha b hb hab
      have h1 := congrArg Prod.fst hab
      have h2 := congrArg Prod.snd hab
      have hm : a % p = b % p := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
      change a / p = b / p at h2
      calc a = a % p + p * (a / p) := (Nat.mod_add_div a p).symm
           _ = b % p + p * (b / p) := by rw [hm, h2]
           _ = b := Nat.mod_add_div b p)
  simpa [T, card_product, mul_comm] using h

/-- Least-nonnegative representatives of a finite quotient image. -/
def representatives {G : Type*} (p : ℕ) (V : Finset G) (φ : G → ZMod p) : Finset ℕ :=
  (V.image φ).image ZMod.val

/-- Reducing representatives recovers the original quotient image. -/
theorem representatives_image {G : Type*} (p : ℕ) [NeZero p]
    (V : Finset G) (φ : G → ZMod p) :
    (representatives p V φ).image (fun n : ℕ => (n : ZMod p)) = V.image φ := by
  simp [representatives, image_image, Function.comp_def]

/-- Sum residues are the image of the original vector sumset. -/
theorem representatives_sum_image {G : Type*} [AddCommGroup G] [DecidableEq G]
    (p : ℕ) [NeZero p] (V : Finset G) (φ : G →+ ZMod p) :
    (MaskedDigit.natSumFinset (representatives p V φ) (representatives p V φ)).image
      (fun n : ℕ => (n : ZMod p)) = (V + V).image φ := by
  change _ = (image₂ (· + ·) V V).image φ
  simp only [MaskedDigit.natSumFinset, representatives, image₂_image_left,
    image₂_image_right, image_image₂, Nat.cast_add, ZMod.natCast_zmod_val,
    map_add]

/-- Difference residues are the image of the original vector difference set. -/
theorem representatives_diff_image {G : Type*} [AddCommGroup G] [DecidableEq G]
    (p : ℕ) [NeZero p] (V : Finset G) (φ : G →+ ZMod p) :
    (MaskedDigit.natDiffFinset (representatives p V φ) (representatives p V φ)).image
      (fun n : ℤ => (n : ZMod p)) = (V - V).image φ := by
  change _ = (image₂ (· - ·) V V).image φ
  simp only [MaskedDigit.natDiffFinset, representatives, image₂_image_left,
    image₂_image_right, image_image₂, Int.cast_sub, Int.cast_natCast,
    ZMod.natCast_zmod_val, map_sub]

/-- The factor of two for lifting sums from residues. -/
theorem representatives_sum_card {G : Type*} [AddCommGroup G] [DecidableEq G]
    (p : ℕ) [NeZero p] (V : Finset G) (φ : G →+ ZMod p) :
    (MaskedDigit.natSumFinset (representatives p V φ) (representatives p V φ)).card
      ≤ 2 * (V + V).card := by
  have hb : ∀ a ∈ representatives p V φ, a < p := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := mem_image.mp ha
    exact ZMod.val_lt z
  have h := card_le_two_mul_residue_image
    (MaskedDigit.natSumFinset (representatives p V φ) (representatives p V φ)) p
    (NeZero.pos p) (by
      intro n hn
      obtain ⟨a, ha, b, hb', rfl⟩ := mem_image₂.mp hn
      have := hb a ha
      have := hb b hb'
      omega)
  rw [representatives_sum_image] at h
  exact h.trans (Nat.mul_le_mul_left 2 card_image_le)

/-- Difference residues lift to actual integer differences. -/
theorem representatives_diff_card {G : Type*} [AddCommGroup G] [DecidableEq G]
    (p : ℕ) [NeZero p] (V W : Finset G) (φ : G →+ ZMod p)
    (hWV : W ⊆ V - V) :
    (W.image φ).card ≤
      (MaskedDigit.natDiffFinset (representatives p V φ) (representatives p V φ)).card := by
  have h := card_le_card (image_subset_image hWV : W.image φ ⊆ (V - V).image φ)
  rw [← representatives_diff_image p V φ] at h
  exact h.trans card_image_le

end C3a
