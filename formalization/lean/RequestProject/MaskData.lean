/-
Copyright (c) 2026 Logan Kleinwaks. All rights reserved.
Released under Apache 2.0 license; see LICENSE-Kleinwaks.
Reused from kleinwaks/masked-digit-sum-difference-bound,
commit 352ab86effecb7efce415507a8c781ec158b86e0.
-/
import RequestProject.GHRConstant

/-!
# Masks, minimum witness costs and partition polynomials

This file formalizes the finite data introduced at the beginning of Section 2
("The masked-digit bound") of `masked_digit_bound.tex`, and reused throughout the
controlled-carry sections:

* a mask `M ⊆ {0, …, B}` with `0 ∈ M` and `B = max M`, together with a base `q > B`
  (the carry-free case being `q = 2B + 1`);
* the sum support `S = M + M` and the difference support `D = M - M`;
* the minimum witness cost `κ(d) = min {a + b : a, b ∈ M, a - b = d}`, equation (3)
  (`eq:kappa`) of the source;
* the two partition polynomials `P₊` and `P₋` of equation (4) (`eq:partition-polys`).
-/

open scoped BigOperators

namespace MaskedDigit

/-- The finite data of the masked-digit construction of `masked_digit_bound.tex`: a base `q`,
a largest digit `B` and a mask `M ⊆ {0, …, B}` containing both `0` and `B`.  In Section 2 of
the source the base is the carry-free value `Q = 2B + 1`; from Section 4 ("Controlled
carries") on it is an arbitrary integer `q > B`. -/
structure MaskData where
  /-- The largest allowed digit, `B = max M` in the source. -/
  B : ℕ
  /-- The base `q`, required only to satisfy `q > B`. -/
  q : ℕ
  /-- The mask `M ⊆ {0, …, B}`. -/
  M : Finset ℕ
  /-- `B ≥ 1`, as required in Section 2 of the source. -/
  B_pos : 0 < B
  /-- `B < q`; this is *not* silently strengthened to `2B < q`. -/
  q_gt_B : B < q
  /-- `0 ∈ M`. -/
  zero_mem : 0 ∈ M
  /-- Every element of the mask is at most `B`. -/
  digits_le : ∀ a ∈ M, a ≤ B
  /-- `B ∈ M`, i.e. `B` really is the maximum of the mask. -/
  B_mem : B ∈ M

namespace MaskData

variable (D : MaskData)

/-- The sum support `S = M + M` of Section 2 of `masked_digit_bound.tex`. -/
def sumSupport : Finset ℕ := D.M.biUnion fun a => D.M.image fun b => a + b

/-- The difference support `D = M - M ⊆ [-B, B]` of Section 2 of
`masked_digit_bound.tex`. -/
def diffSupport : Finset ℤ :=
  D.M.biUnion fun a => D.M.image fun (b : ℕ) => (a : ℤ) - (b : ℤ)

@[simp] theorem mem_sumSupport {s : ℕ} :
    s ∈ D.sumSupport ↔ ∃ a ∈ D.M, ∃ b ∈ D.M, a + b = s := by
  simp [sumSupport, eq_comm]

@[simp] theorem mem_diffSupport {d : ℤ} :
    d ∈ D.diffSupport ↔ ∃ a ∈ D.M, ∃ b ∈ D.M, (a : ℤ) - b = d := by
  simp [diffSupport, eq_comm]

/-- The sum support `S = M + M` of Section 2 of `masked_digit_bound.tex` contains `0`, since `0 ∈ M`. -/
theorem zero_mem_sumSupport : 0 ∈ D.sumSupport :=
  D.mem_sumSupport.2 ⟨0, D.zero_mem, 0, D.zero_mem, rfl⟩

/-- The difference support `D = M - M` of Section 2 of `masked_digit_bound.tex` contains `0`, since `0 ∈ M`. -/
theorem zero_mem_diffSupport : (0 : ℤ) ∈ D.diffSupport :=
  D.mem_diffSupport.2 ⟨0, D.zero_mem, 0, D.zero_mem, by simp⟩

/-- The sum support `S = M + M` of Section 2 of `masked_digit_bound.tex` is nonempty. -/
theorem sumSupport_nonempty : D.sumSupport.Nonempty := ⟨0, D.zero_mem_sumSupport⟩

/-- The difference support `D = M - M` of Section 2 of `masked_digit_bound.tex` is nonempty. -/
theorem diffSupport_nonempty : D.diffSupport.Nonempty := ⟨0, D.zero_mem_diffSupport⟩

/-- `B ∈ D = M - M`, used in the source to see that the mean cost `μ` is positive. -/
theorem B_mem_diffSupport : (D.B : ℤ) ∈ D.diffSupport :=
  D.mem_diffSupport.2 ⟨D.B, D.B_mem, 0, D.zero_mem, by simp⟩

/-- Every difference digit satisfies `|d| ≤ B`, i.e. `D ⊆ [-B, B]`; this is the containment
used for the carry-free injectivity argument in Section 2 of `masked_digit_bound.tex`. -/
theorem abs_le_of_mem_diffSupport {d : ℤ} (hd : d ∈ D.diffSupport) : |d| ≤ (D.B : ℤ) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := D.mem_diffSupport.1 hd
  have ha' : (a : ℤ) ≤ (D.B : ℤ) := by exact_mod_cast D.digits_le a ha
  have hb' : (b : ℤ) ≤ (D.B : ℤ) := by exact_mod_cast D.digits_le b hb
  have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  have hb0 : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  rw [abs_le]; constructor <;> omega

/-- Every sum digit is at most `2B`; consequently, since `B < q`, the physical carry of a
digitwise sum lies in `{0, 1}` (see the conventions of Section 4 of
`masked_digit_bound.tex`). -/
theorem le_of_mem_sumSupport {s : ℕ} (hs : s ∈ D.sumSupport) : s ≤ 2 * D.B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := D.mem_sumSupport.1 hs
  have := D.digits_le a ha
  have := D.digits_le b hb
  omega

/-- The negation symmetry `d ∈ D ↔ -d ∈ D` of the difference support. -/
theorem neg_mem_diffSupport {d : ℤ} (hd : d ∈ D.diffSupport) : -d ∈ D.diffSupport := by
  obtain ⟨a, ha, b, hb, rfl⟩ := D.mem_diffSupport.1 hd
  exact D.mem_diffSupport.2 ⟨b, hb, a, ha, by ring⟩

/-! ## The minimum witness cost `κ` -/

/-- The set of witness costs `a + b` for a difference digit `d`, i.e. the set whose minimum
is `κ(d)` in equation (3) of `masked_digit_bound.tex`. -/
def witnessCosts (d : ℤ) : Set ℕ := {n : ℕ | ∃ a ∈ D.M, ∃ b ∈ D.M, (a : ℤ) - b = d ∧ a + b = n}

/-- The minimum witness cost `κ(d) = min {a + b : a, b ∈ M, a - b = d}` of equation (3)
(`eq:kappa`) of `masked_digit_bound.tex`.  For `d ∉ M - M` the value is `0` by convention;
this convention is never used, since `κ` is always applied to elements of `D = M - M`. -/
noncomputable def kappa (d : ℤ) : ℕ := sInf (D.witnessCosts d)

/-- Every difference digit `d ∈ D = M - M` admits at least one witness, so the set of witness costs entering `κ(d)` in equation (3) of `masked_digit_bound.tex` is nonempty. -/
theorem witnessCosts_nonempty {d : ℤ} (hd : d ∈ D.diffSupport) : (D.witnessCosts d).Nonempty := by
  obtain ⟨a, ha, b, hb, rfl⟩ := D.mem_diffSupport.1 hd
  exact ⟨a + b, a, ha, b, hb, rfl, rfl⟩

/-- Any witness bounds `κ` from above: if `a, b ∈ M` and `a - b = d` then `κ(d) ≤ a + b`. -/
theorem kappa_le {d : ℤ} {a b : ℕ} (ha : a ∈ D.M) (hb : b ∈ D.M) (hab : (a : ℤ) - b = d) :
    D.kappa d ≤ a + b :=
  Nat.sInf_le ⟨a, ha, b, hb, hab, rfl⟩

/-- **Existence of a minimum witness.**  Every `d ∈ D = M - M` has witnesses `a, b ∈ M` with
`a - b = d` and `a + b = κ(d)`; these are the pairs `(α_d, β_d)` chosen in the proof of
Proposition 2 of `masked_digit_bound.tex`. -/
theorem exists_min_witness {d : ℤ} (hd : d ∈ D.diffSupport) :
    ∃ a ∈ D.M, ∃ b ∈ D.M, (a : ℤ) - b = d ∧ a + b = D.kappa d :=
  Nat.sInf_mem (D.witnessCosts_nonempty hd)

/-- **`κ` is even**: `κ(-d) = κ(d)`, as stated just after equation (3) of
`masked_digit_bound.tex`. -/
theorem kappa_neg (d : ℤ) : D.kappa (-d) = D.kappa d := by
  have key : ∀ e : ℤ, D.witnessCosts (-e) = D.witnessCosts e := by
    intro e
    ext n
    constructor
    · rintro ⟨a, ha, b, hb, h1, h2⟩
      exact ⟨b, hb, a, ha, by omega, by omega⟩
    · rintro ⟨a, ha, b, hb, h1, h2⟩
      exact ⟨b, hb, a, ha, by omega, by omega⟩
  rw [kappa, kappa, key]

/-- `κ(0) = 0`, since `0 ∈ M` gives the witness pair `(0, 0)`. -/
theorem kappa_zero : D.kappa 0 = 0 :=
  Nat.le_zero.1 (by simpa using D.kappa_le D.zero_mem D.zero_mem (by simp))

/-- The minimum witness cost is at most `2B`. -/
theorem kappa_le_two_B {d : ℤ} (hd : d ∈ D.diffSupport) : D.kappa d ≤ 2 * D.B := by
  obtain ⟨a, ha, b, hb, hab⟩ := D.mem_diffSupport.1 hd
  have h1 := D.kappa_le ha hb hab
  have := D.digits_le a ha
  have := D.digits_le b hb
  omega

/-- The minimum witness cost of a nonzero difference digit is positive. -/
theorem kappa_pos {d : ℤ} (hd : d ∈ D.diffSupport) (hd0 : d ≠ 0) : 0 < D.kappa d := by
  rcases Nat.eq_zero_or_pos (D.kappa d) with h | h
  · obtain ⟨a, _, b, _, h1, h2⟩ := D.exists_min_witness hd
    rw [h] at h2
    exact absurd (by omega : d = 0) hd0
  · exact h

/-! ## The partition polynomials -/

/-- The sum-side partition polynomial `P₊(x) = ∑_{s ∈ S} xˢ` of equation (4)
(`eq:partition-polys`) of `masked_digit_bound.tex`. -/
noncomputable def Pplus (x : ℝ) : ℝ := ∑ s ∈ D.sumSupport, x ^ s

/-- The difference-side partition polynomial `P₋(x) = ∑_{d ∈ D} x^{κ(d)}` of equation (4)
(`eq:partition-polys`) of `masked_digit_bound.tex`. -/
noncomputable def Pminus (x : ℝ) : ℝ := ∑ d ∈ D.diffSupport, x ^ D.kappa d

/-- The sum-side partition polynomial `P₊(x)` of equation (4) of `masked_digit_bound.tex` is positive for `x > 0`. -/
theorem Pplus_pos {x : ℝ} (hx : 0 < x) : 0 < D.Pplus x :=
  Finset.sum_pos (fun s _ => pow_pos hx s) D.sumSupport_nonempty

/-- The difference-side partition polynomial `P₋(x)` of equation (4) of `masked_digit_bound.tex` is positive for `x > 0`. -/
theorem Pminus_pos {x : ℝ} (hx : 0 < x) : 0 < D.Pminus x :=
  Finset.sum_pos (fun _ _ => pow_pos hx _) D.diffSupport_nonempty

end MaskData

end MaskedDigit
