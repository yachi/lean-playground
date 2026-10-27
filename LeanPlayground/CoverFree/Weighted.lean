module

public import LeanPlayground.CoverFree.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

/-!
# A weighted covering inequality (Lemma 2.2)

Lemma 2.2 of Hu–Zhang: if a probability weighting `w` of the members of `H` gives every point
`x ∈ U` a positive total weight `p x`, then `κ² ≤ ∑_{x ∈ U} 1 / p x`, where `κ` is the covering
number of `U` by `H` (`CoverFree.weighted`).

The proof is by strong induction on `U`, as in the paper. It uses Stehlík's theorem, in the form
`CoverFree.StehlikBound`: a critical family with connected graph has `|U| ≥ 2κ - 1`. Here this is
a hypothesis here; `CoverFree.stehlikBound` proves it, and `CoverFree.weighted'` is the
unconditional statement.

Because `coverNum H W` counts members of `H` that need not lie in `W`, restricting to a subset `W`
keeps the same family and the same weights, and no down-closure is needed.
-/

namespace CoverFree

open Finset

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

/-- The total weight `p x` of the members of `H` that contain `x`. -/
noncomputable def weightAt (H : Finset (Finset α)) (w : Finset α → ℝ) (x : α) : ℝ :=
  ∑ S ∈ H with x ∈ S, w S

/-- Stehlík's theorem, in the dual form of Huang–Liu (Lemma 2.1 of Hu–Zhang): if every point of
`U` is covered, removing any point lowers the covering number, and the graph `G(H)` on `U` is
connected, then `|U| ≥ 2κ - 1`. -/
def StehlikBound (α : Type*) [DecidableEq α] : Prop :=
  ∀ (H : Finset (Finset α)) (U : Finset α), Covers H U →
    (∀ x ∈ U, coverNum H (U.erase x) + 1 = coverNum H U) → Connected H U →
    2 * coverNum H U ≤ U.card + 1

/-- The statement of Lemma 2.2 for the family `H` on the set `U`, for every weighting. -/
def WeightedIneq (H : Finset (Finset α)) (U : Finset α) : Prop :=
  ∀ w : Finset α → ℝ, (∀ S ∈ H, 0 ≤ w S) → ∑ S ∈ H, w S = 1 →
    (∀ x ∈ U, 0 < weightAt H w x) → (coverNum H U : ℝ) ^ 2 ≤ ∑ x ∈ U, (weightAt H w x)⁻¹

variable {H : Finset (Finset α)} {w : Finset α → ℝ} {U V : Finset α}

lemma weightAt_le_one (hw0 : ∀ S ∈ H, 0 ≤ w S) (hw1 : ∑ S ∈ H, w S = 1) (x : α) :
    weightAt H w x ≤ 1 :=
  hw1 ▸ sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S hS _ => hw0 S hS

lemma covers_of_pos (hp : ∀ x ∈ U, 0 < weightAt H w x) : Covers H U := by
  intro x hx
  by_contra h
  push Not at h
  have : weightAt H w x = 0 := sum_eq_zero fun S hS => absurd (mem_filter.1 hS).2
    (h S (mem_filter.1 hS).1)
  linarith [hp x hx]

lemma card_le_sum_inv (hw0 : ∀ S ∈ H, 0 ≤ w S) (hw1 : ∑ S ∈ H, w S = 1)
    (hp : ∀ x ∈ U, 0 < weightAt H w x) : (U.card : ℝ) ≤ ∑ x ∈ U, (weightAt H w x)⁻¹ := by
  rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact sum_le_sum fun x hx => (one_le_inv₀ (hp x hx)).2 (weightAt_le_one hw0 hw1 x)

/-- Restricting to `V`: reweighting the members that meet `V` by their total weight `ρ` turns
Lemma 2.2 for `V` into `κ(V)² ≤ ρ ∑_{x ∈ V} 1 / p x`. -/
lemma restrict_bound (hw0 : ∀ S ∈ H, 0 ≤ w S) (hp : ∀ x ∈ V, 0 < weightAt H w x)
    (hV : V.Nonempty) (ih : WeightedIneq H V) :
    0 < ∑ S ∈ H with (S ∩ V).Nonempty, w S ∧
      (coverNum H V : ℝ) ^ 2 ≤
        (∑ S ∈ H with (S ∩ V).Nonempty, w S) * ∑ x ∈ V, (weightAt H w x)⁻¹ := by
  set ρ := ∑ S ∈ H with (S ∩ V).Nonempty, w S
  have hle : ∀ x ∈ V, weightAt H w x ≤ ρ := fun x hx =>
    sum_le_sum_of_subset_of_nonneg
      (fun S hS => by
        rw [mem_filter] at hS ⊢
        exact ⟨hS.1, x, mem_inter.2 ⟨hS.2, hx⟩⟩)
      fun S hS _ => hw0 S (mem_filter.1 hS).1
  obtain ⟨x₀, hx₀⟩ := hV
  have hρ : 0 < ρ := (hp x₀ hx₀).trans_le (hle x₀ hx₀)
  refine ⟨hρ, ?_⟩
  set w' : Finset α → ℝ := fun S => if (S ∩ V).Nonempty then w S / ρ else 0
  have hw'0 : ∀ S ∈ H, 0 ≤ w' S := fun S hS => by
    simp only [w']
    split_ifs
    · exact div_nonneg (hw0 S hS) hρ.le
    · exact le_rfl
  have hw'1 : ∑ S ∈ H, w' S = 1 := by
    simp only [w']
    rw [← sum_filter, ← sum_div, div_self hρ.ne']
  have hw'x : ∀ x ∈ V, weightAt H w' x = weightAt H w x / ρ := fun x hx => by
    simp only [weightAt, sum_div]
    refine sum_congr rfl fun S hS => ?_
    have : (S ∩ V).Nonempty := ⟨x, mem_inter.2 ⟨(mem_filter.1 hS).2, hx⟩⟩
    simp [w', this]
  have := ih w' hw'0 hw'1 fun x hx => by rw [hw'x x hx]; exact div_pos (hp x hx) hρ
  calc (coverNum H V : ℝ) ^ 2 ≤ ∑ x ∈ V, (weightAt H w' x)⁻¹ := this
    _ = ρ * ∑ x ∈ V, (weightAt H w x)⁻¹ := by
        rw [mul_sum]
        refine sum_congr rfl fun x hx => ?_
        rw [hw'x x hx, inv_div, div_eq_mul_inv]

/-- The two-term Cauchy–Schwarz step of Case 2. -/
lemma cauchy_schwarz_two {k₁ k₂ ρ₁ ρ₂ s₁ s₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hρ : ρ₁ + ρ₂ ≤ 1)
    (h₁ : k₁ ^ 2 ≤ ρ₁ * s₁) (h₂ : k₂ ^ 2 ≤ ρ₂ * s₂) :
    (k₁ + k₂) ^ 2 ≤ s₁ + s₂ := by
  have hs₁ : 0 ≤ s₁ := nonneg_of_mul_nonneg_right ((sq_nonneg k₁).trans h₁) hρ₁
  have hs₂ : 0 ≤ s₂ := nonneg_of_mul_nonneg_right ((sq_nonneg k₂).trans h₂) hρ₂
  have hcross : ρ₁ * ρ₂ * (2 * k₁ * k₂) ≤ ρ₁ * ρ₂ * (ρ₂ * s₁ + ρ₁ * s₂) := by
    nlinarith [sq_nonneg (ρ₂ * k₁ - ρ₁ * k₂), mul_le_mul_of_nonneg_left h₁ (sq_nonneg ρ₂),
      mul_le_mul_of_nonneg_left h₂ (sq_nonneg ρ₁)]
  have hcross' : 2 * k₁ * k₂ ≤ ρ₂ * s₁ + ρ₁ * s₂ :=
    le_of_mul_le_mul_left hcross (mul_pos hρ₁ hρ₂)
  nlinarith

/-- **Lemma 2.2** (weighted covering inequality), given Stehlík's theorem. -/
theorem weighted (hst : StehlikBound α) (H : Finset (Finset α)) (U : Finset α) :
    WeightedIneq H U := by
  induction U using Finset.strongInduction with
  | H U ih =>
  intro w hw0 hw1 hp
  have hcov := covers_of_pos hp
  set k := coverNum H U with hk
  set C := ∑ x ∈ U, (weightAt H w x)⁻¹ with hC
  by_contra hlt
  push Not at hlt
  have hm : (U.card : ℝ) ≤ C := card_le_sum_inv hw0 hw1 hp
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    rw [this] at hlt
    have : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
    norm_num at hlt
    linarith
  -- `H` is critical on `U`.
  have hcrit : ∀ x ∈ U, coverNum H (U.erase x) + 1 = k := by
    intro x hx
    have h1 := coverNum_le_erase_add_one (x := x) hcov
    have h2 : coverNum H (U.erase x) ≤ k := coverNum_mono hcov (erase_subset _ _)
    have h3 : coverNum H (U.erase x) ≠ k := by
      intro heq
      have := ih (U.erase x) (erase_ssubset hx) w hw0 hw1 fun y hy => hp y (mem_of_mem_erase hy)
      rw [heq] at this
      have hsplit := sum_erase_add U (fun y => (weightAt H w y)⁻¹) hx
      have : 0 < (weightAt H w x)⁻¹ := inv_pos.2 (hp x hx)
      linarith
    omega
  by_cases hconn : Connected H U
  · -- Case 1: `G(H)` is connected.
    have h2k := hst H U hcov hcrit hconn
    have havg : ∑ S ∈ H, w S * ∑ x ∈ U with x ∈ S, (weightAt H w x)⁻¹ = U.card := by
      calc _ = ∑ S ∈ H, ∑ x ∈ U, if x ∈ S then w S * (weightAt H w x)⁻¹ else 0 := by
              refine sum_congr rfl fun S _ => ?_
              rw [mul_sum, sum_filter]
        _ = ∑ x ∈ U, ∑ S ∈ H, if x ∈ S then w S * (weightAt H w x)⁻¹ else 0 := sum_comm
        _ = ∑ x ∈ U, weightAt H w x * (weightAt H w x)⁻¹ := by
              refine sum_congr rfl fun x _ => ?_
              rw [← sum_filter, weightAt, sum_mul]
        _ = ∑ x ∈ U, (1 : ℝ) := sum_congr rfl fun x hx => mul_inv_cancel₀ (hp x hx).ne'
        _ = U.card := by simp
    obtain ⟨S, hS, hSm⟩ :
        ∃ S ∈ H, (U.card : ℝ) ≤ ∑ x ∈ U with x ∈ S, (weightAt H w x)⁻¹ := by
      by_contra hne
      push Not at hne
      obtain ⟨S₀, hS₀, hpos⟩ : ∃ S ∈ H, 0 < w S := by
        by_contra h
        push Not at h
        have : ∑ S ∈ H, w S ≤ 0 := sum_nonpos h
        linarith
      have : ∑ S ∈ H, w S * ∑ x ∈ U with x ∈ S, (weightAt H w x)⁻¹ <
          ∑ S ∈ H, w S * U.card :=
        sum_lt_sum (fun S hS => mul_le_mul_of_nonneg_left (hne S hS).le (hw0 S hS))
          ⟨S₀, hS₀, mul_lt_mul_of_pos_left (hne S₀ hS₀) hpos⟩
      rw [← sum_mul, hw1, one_mul, havg] at this
      exact lt_irrefl _ this
    have hsplit : ∑ x ∈ U with x ∈ S, (weightAt H w x)⁻¹ +
        ∑ x ∈ U \ S, (weightAt H w x)⁻¹ = C := by
      rw [sdiff_eq_filter]; exact sum_filter_add_sum_filter_not U (· ∈ S) _
    have hkm : (1 : ℝ) ≤ U.card := by exact_mod_cast hk1.trans (coverNum_le_card hcov)
    have hWss : U \ S ⊂ U := by
      rw [ssubset_iff_of_subset sdiff_subset]
      obtain ⟨x, hx⟩ : (U.filter (· ∈ S)).Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro h
        rw [h, sum_empty] at hSm
        linarith
      rw [mem_filter] at hx
      exact ⟨x, hx.1, fun h => (mem_sdiff.1 h).2 hx.2⟩
    have hkW : k ≤ coverNum H (U \ S) + 1 := coverNum_le_sdiff_add_one hS hcov
    have ihW := ih (U \ S) hWss w hw0 hw1 fun x hx => hp x (sdiff_subset hx)
    have hkW' : (k : ℝ) - 1 ≤ coverNum H (U \ S) := by
      have : (k : ℝ) ≤ coverNum H (U \ S) + 1 := by exact_mod_cast hkW
      linarith
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have h2k' : 2 * (k : ℝ) ≤ U.card + 1 := by exact_mod_cast h2k
    have hsq : ((k : ℝ) - 1) ^ 2 ≤ (coverNum H (U \ S) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hkW' 2
    nlinarith
  · -- Case 2: `G(H)` is disconnected.
    simp only [Connected, not_forall, not_exists, not_and, exists_prop] at hconn
    obtain ⟨V, hVU, hVne, hVneU, hsep⟩ := hconn
    have hV'ne : (U \ V).Nonempty :=
      sdiff_nonempty.2 fun h => hVneU (Subset.antisymm hVU h)
    have hVss : V ⊂ U := ssubset_of_subset_of_ne hVU hVneU
    have hV'ss : U \ V ⊂ U := sdiff_ssubset hVU hVne
    obtain ⟨hρ₁, h₁⟩ := restrict_bound hw0 (fun x hx => hp x (hVU hx)) hVne (ih V hVss)
    obtain ⟨hρ₂, h₂⟩ := restrict_bound hw0 (fun x hx => hp x (sdiff_subset hx)) hV'ne
      (ih _ hV'ss)
    have hρ : ∑ S ∈ H with (S ∩ V).Nonempty, w S +
        ∑ S ∈ H with (S ∩ (U \ V)).Nonempty, w S ≤ 1 := by
      rw [← sum_union (disjoint_filter.2 fun S hS h h' => hsep S hS h h'), ← hw1]
      exact sum_le_sum_of_subset_of_nonneg (union_subset (filter_subset _ _) (filter_subset _ _))
        fun S hS _ => hw0 S hS
    have hkV : k ≤ coverNum H V + coverNum H (U \ V) := by
      have := coverNum_union_le (hcov.mono hVU) (hcov.mono (sdiff_subset (t := V)))
      rwa [union_sdiff_of_subset hVU] at this
    have hCsplit : C = ∑ x ∈ V, (weightAt H w x)⁻¹ + ∑ x ∈ U \ V, (weightAt H w x)⁻¹ := by
      rw [← sum_union disjoint_sdiff, union_sdiff_of_subset hVU]
    have hcs := cauchy_schwarz_two hρ₁ hρ₂ hρ h₁ h₂
    have hkV' : (k : ℝ) ≤ coverNum H V + coverNum H (U \ V) := by exact_mod_cast hkV
    have hsq : (k : ℝ) ^ 2 ≤ ((coverNum H V : ℝ) + coverNum H (U \ V)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hkV' 2
    linarith

end CoverFree
