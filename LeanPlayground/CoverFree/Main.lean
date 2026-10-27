module

public import LeanPlayground.CoverFree.Stehlik
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

/-!
# The strong Erdős–Frankl–Füredi bound (Theorem 1.1)

An `r`-cover-free family on `n` points with more than `n` members has `n ≥ (r + 1)²`
(`CoverFree.sq_le_card_of_card_lt`).

As in the paper: the incidence vectors of the members are linearly dependent, so
`∑_{A ∈ P} a_A 1_A = ∑_{B ∈ N} b_B 1_B` with positive coefficients on disjoint subfamilies
`P`, `N` and `a = ∑ a_A ≥ b = ∑ b_B`. For `A ∈ P`, the members of `N` cover `A` but no `r` of
them do, so Lemma 2.2 with the weights `b_B / b` gives `(r + 1)² ≤ b ∑_{x ∈ A} 1 / M_x`, where
`M_x = ∑_{A ∋ x} a_A = ∑_{B ∋ x} b_B`. Summing with the weights `a_A` gives `(r + 1)² a ≤ b n`.
-/

namespace CoverFree

open Finset

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The core of Theorem 1.1, for a linear relation `∑_{A ∈ F} g_A 1_A = 0` whose positive part
`a` is at least its negative part `b`. -/
theorem sq_le_card_of_relation {r : ℕ} {F : Finset (Finset α)}
    (hF : IsCoverFree r F) (g : Finset α → ℝ) (hrel : ∀ x, ∑ A ∈ F with x ∈ A, g A = 0)
    {A₀ : Finset α} (hA₀ : A₀ ∈ F) (hgA₀ : g A₀ ≠ 0)
    (hab : ∑ A ∈ F with g A < 0, -g A ≤ ∑ A ∈ F with 0 < g A, g A) :
    (r + 1) ^ 2 ≤ Fintype.card α := by
  set P := F.filter (fun A => 0 < g A)
  set N := F.filter (fun A => g A < 0)
  set a := ∑ A ∈ P, g A
  set b := ∑ B ∈ N, -g B
  -- `M x`: both sides of the relation at `x`.
  set M : α → ℝ := fun x => ∑ A ∈ P with x ∈ A, g A
  have hM : ∀ x, M x = ∑ B ∈ N with x ∈ B, -g B := by
    intro x
    have h := hrel x
    simp only [M, P, N, sum_filter] at h ⊢
    rw [← sub_eq_zero, ← sum_sub_distrib, ← h]
    refine sum_congr rfl fun A _ => ?_
    split_ifs <;> linarith
  have hgP : ∀ A ∈ P, 0 < g A := fun A hA => (mem_filter.1 hA).2
  have hgN : ∀ B ∈ N, 0 < -g B := fun B hB => neg_pos.2 (mem_filter.1 hB).2
  have hMpos : ∀ A ∈ P, ∀ x ∈ A, g A ≤ M x := fun A hA x hx =>
    single_le_sum (f := g) (fun A' hA' => (hgP A' (mem_filter.1 hA').1).le)
      (mem_filter.2 ⟨hA, hx⟩)
  have hMle : ∀ x, M x ≤ b := fun x => by
    rw [hM]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun B hB _ => (hgN B hB).le
  -- `a > 0`, hence `P` is nonempty and `b > 0`.
  have ha : 0 < a := by
    rcases lt_or_gt_of_ne hgA₀ with h | h
    · refine lt_of_lt_of_le ?_ hab
      exact sum_pos (fun B hB => hgN B hB) ⟨A₀, mem_filter.2 ⟨hA₀, h⟩⟩
    · exact sum_pos (fun A hA => hgP A hA) ⟨A₀, mem_filter.2 ⟨hA₀, h⟩⟩
  obtain ⟨A₁, hA₁⟩ : P.Nonempty := by
    rw [nonempty_iff_ne_empty]; intro h; simp [a, h] at ha
  obtain ⟨x₁, hx₁⟩ := hF.nonempty (mem_filter.1 hA₁).1
  have hb : 0 < b := (hgP A₁ hA₁).trans_le ((hMpos A₁ hA₁ x₁ hx₁).trans (hMle x₁))
  -- The weights on `N`.
  set w : Finset α → ℝ := fun B => -g B / b
  have hw0 : ∀ B ∈ N, 0 ≤ w B := fun B hB => div_nonneg (hgN B hB).le hb.le
  have hw1 : ∑ B ∈ N, w B = 1 := by simp only [w]; rw [← sum_div, div_self hb.ne']
  have hwx : ∀ x, weightAt N w x = M x / b := fun x => by
    simp only [weightAt, w]; rw [← sum_div, hM]
  -- Lemma 2.2 for each `A ∈ P`.
  have hPA : ∀ A ∈ P, ((r : ℝ) + 1) ^ 2 ≤ b * ∑ x ∈ A, (M x)⁻¹ := by
    intro A hA
    have hpos : ∀ x ∈ A, 0 < weightAt N w x := fun x hx => by
      rw [hwx]; exact div_pos ((hgP A hA).trans_le (hMpos A hA x hx)) hb
    have hκ : r + 1 ≤ coverNum N A := by
      by_contra hlt
      obtain ⟨C, hCN, hcard, hcov⟩ := exists_cover (covers_of_pos hpos)
      refine hF A (mem_filter.1 hA).1 C (fun B hB => ?_) (by omega) hcov
      have hBN := hCN hB
      refine mem_erase.2 ⟨fun hBA => ?_, (mem_filter.1 hBN).1⟩
      subst hBA
      linarith [hgP _ hA, hgN _ hBN]
    have := weighted stehlikBound N A w hw0 hw1 hpos
    calc ((r : ℝ) + 1) ^ 2 ≤ (coverNum N A : ℝ) ^ 2 := by
          gcongr; exact_mod_cast hκ
      _ ≤ ∑ x ∈ A, (weightAt N w x)⁻¹ := this
      _ = b * ∑ x ∈ A, (M x)⁻¹ := by
          rw [mul_sum]; refine sum_congr rfl fun x _ => ?_
          rw [hwx, inv_div, div_eq_mul_inv]
  -- Sum over `P` with the weights `a_A`.
  have hsum : ∑ A ∈ P, g A * ∑ x ∈ A, (M x)⁻¹ ≤ Fintype.card α := by
    calc ∑ A ∈ P, g A * ∑ x ∈ A, (M x)⁻¹
        = ∑ A ∈ P, ∑ x, if x ∈ A then g A * (M x)⁻¹ else 0 := by
          refine sum_congr rfl fun A _ => ?_
          rw [mul_sum, ← sum_filter, filter_mem_eq_inter, univ_inter]
      _ = ∑ x, M x * (M x)⁻¹ := by
          rw [sum_comm]; refine sum_congr rfl fun x _ => ?_
          rw [show M x = ∑ A ∈ P with x ∈ A, g A from rfl, sum_mul]
          exact (sum_filter _ _).symm
      _ ≤ ∑ _x : α, (1 : ℝ) := sum_le_sum fun x _ => by
          rcases eq_or_ne (M x) 0 with h | h
          · simp [h]
          · rw [mul_inv_cancel₀ h]
      _ = Fintype.card α := by simp
  have hmain : ((r : ℝ) + 1) ^ 2 * a ≤ b * Fintype.card α := by
    calc ((r : ℝ) + 1) ^ 2 * a = ∑ A ∈ P, g A * ((r : ℝ) + 1) ^ 2 := by
          rw [mul_comm, sum_mul]
      _ ≤ ∑ A ∈ P, g A * (b * ∑ x ∈ A, (M x)⁻¹) :=
          sum_le_sum fun A hA => mul_le_mul_of_nonneg_left (hPA A hA) (hgP A hA).le
      _ = b * ∑ A ∈ P, g A * ∑ x ∈ A, (M x)⁻¹ := by
          rw [mul_sum]; refine sum_congr rfl fun A _ => by ring
      _ ≤ b * Fintype.card α := mul_le_mul_of_nonneg_left hsum hb.le
  have : ((r : ℝ) + 1) ^ 2 ≤ Fintype.card α := by
    by_contra hlt
    push Not at hlt
    have : b * Fintype.card α < ((r : ℝ) + 1) ^ 2 * b := by
      rw [mul_comm]; exact mul_lt_mul_of_pos_right hlt hb
    nlinarith [sq_nonneg ((r : ℝ) + 1)]
  exact_mod_cast this

/-- The incidence vector of a finite set. -/
def ind (A : Finset α) : α → ℝ := fun x => if x ∈ A then 1 else 0

omit [Fintype α] in
lemma ind_injective : Function.Injective (ind (α := α)) := by
  intro A B h
  ext x
  have := congrFun h x
  simp only [ind] at this
  split_ifs at this <;> simp_all

/-- **Theorem 1.1** (Hu–Zhang): an `r`-cover-free family on `n` points
with more than `n` members has `n ≥ (r + 1)²`. -/
theorem sq_le_card_of_card_lt {r : ℕ} {F : Finset (Finset α)}
    (hF : IsCoverFree r F) (hcard : Fintype.card α < F.card) :
    (r + 1) ^ 2 ≤ Fintype.card α := by
  have ht : Module.finrank ℝ (α → ℝ) < (F.image ind).card := by
    rwa [Module.finrank_fintype_fun_eq_card, card_image_of_injective _ ind_injective]
  obtain ⟨f, hf, v, hv, hfv⟩ := Module.exists_nontrivial_relation_of_finrank_lt_card ht
  obtain ⟨A₀, hA₀, rfl⟩ := mem_image.1 hv
  set g : Finset α → ℝ := fun A => f (ind A)
  rw [sum_image fun A _ B _ h => ind_injective h] at hf
  have hrel : ∀ x, ∑ A ∈ F with x ∈ A, g A = 0 := fun x => by
    have := congrFun hf x
    simp only [Finset.sum_apply, Pi.smul_apply, ind, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Pi.zero_apply] at this
    rw [sum_filter]; exact this
  rcases le_total (∑ A ∈ F with g A < 0, -g A) (∑ A ∈ F with 0 < g A, g A) with h | h
  · exact sq_le_card_of_relation hF g hrel hA₀ hfv h
  · refine sq_le_card_of_relation hF (fun A => -g A) (fun x => ?_) hA₀ (neg_ne_zero.2 hfv) ?_
    · rw [sum_neg_distrib, hrel, neg_zero]
    · simpa only [neg_neg, neg_lt_zero, neg_pos] using h

end CoverFree
