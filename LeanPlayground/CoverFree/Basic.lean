module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Cover-free families and covering numbers

Definitions for the formalization of Yanan Hu and Leilei Zhang, *A proof of the strong
Erdős–Frankl–Füredi cover-free conjecture*, <https://arxiv.org/abs/2610.24442> (October 2026).

* `CoverFree.IsCoverFree r F`: no member of `F` lies in the union of at most `r` other members.
  Taking no other members shows that every member is nonempty.
* `CoverFree.coverNum H W`: the least number of members of `H` whose union contains `W`. The
  paper's `κ(H)` is `coverNum H U` for `U` the union of `H`, and its `κ(H[W])` for a down-set `H`
  is `coverNum H W`; members need not lie inside `W`, so no restriction or down-closure is needed.
* `CoverFree.Connected H U`: the paper's graph `G(H)` on `U` is connected. We say this as: every
  nonempty proper subset `V` of `U` is met by some member of `H` that also meets `U \ V`.
-/

namespace CoverFree

set_option linter.unusedSectionVars false

open Finset

variable {α : Type*} [DecidableEq α]

/-- `F` is `r`-cover-free: no member lies in the union of at most `r` other members. -/
def IsCoverFree (r : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ⊆ F.erase A, B.card ≤ r → ¬ A ⊆ B.sup id

lemma IsCoverFree.nonempty {r : ℕ} {F : Finset (Finset α)} (hF : IsCoverFree r F) {A : Finset α}
    (hA : A ∈ F) : A.Nonempty := by
  have := hF A hA ∅ (empty_subset _) (by simp)
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  simp at this

/-- The covering number: the least size of a subfamily of `H` whose union contains `W`
(`0` if there is none). -/
noncomputable def coverNum (H : Finset (Finset α)) (W : Finset α) : ℕ :=
  sInf {k | ∃ C ⊆ H, C.card = k ∧ W ⊆ C.sup id}

/-- Every point of `W` lies in some member of `H`. -/
def Covers (H : Finset (Finset α)) (W : Finset α) : Prop := ∀ x ∈ W, ∃ S ∈ H, x ∈ S

/-- The graph `G(H)` on `U` is connected. -/
def Connected (H : Finset (Finset α)) (U : Finset α) : Prop :=
  ∀ V ⊆ U, V.Nonempty → V ≠ U → ∃ S ∈ H, (S ∩ V).Nonempty ∧ (S ∩ (U \ V)).Nonempty

variable {H : Finset (Finset α)} {W W' : Finset α}

lemma mem_sup_id {C : Finset (Finset α)} {x : α} : x ∈ C.sup id ↔ ∃ S ∈ C, x ∈ S := by
  simp [Finset.mem_sup]

lemma Covers.subset_sup (h : Covers H W) : W ⊆ H.sup id := fun x hx => mem_sup_id.2 (h x hx)

omit [DecidableEq α] in
lemma Covers.mono (h : Covers H W') (hW : W ⊆ W') : Covers H W := fun x hx => h x (hW hx)

lemma coverNum_le {C : Finset (Finset α)} (hC : C ⊆ H) (hW : W ⊆ C.sup id) :
    coverNum H W ≤ C.card :=
  Nat.sInf_le ⟨C, hC, rfl, hW⟩

lemma exists_cover (h : Covers H W) :
    ∃ C ⊆ H, C.card = coverNum H W ∧ W ⊆ C.sup id :=
  Nat.sInf_mem (s := {k | ∃ C ⊆ H, C.card = k ∧ W ⊆ C.sup id}) ⟨_, H, subset_rfl, rfl,
    h.subset_sup⟩

lemma coverNum_mono (h : Covers H W') (hW : W ⊆ W') : coverNum H W ≤ coverNum H W' := by
  obtain ⟨C, hC, hcard, hcov⟩ := exists_cover h
  exact hcard ▸ coverNum_le hC (hW.trans hcov)

lemma coverNum_union_le (h : Covers H W) (h' : Covers H W') :
    coverNum H (W ∪ W') ≤ coverNum H W + coverNum H W' := by
  obtain ⟨C, hC, hcard, hcov⟩ := exists_cover h
  obtain ⟨C', hC', hcard', hcov'⟩ := exists_cover h'
  calc coverNum H (W ∪ W') ≤ (C ∪ C').card := by
        refine coverNum_le (union_subset hC hC') ?_
        rw [sup_union]
        exact union_subset_union hcov hcov'
    _ ≤ _ := hcard ▸ hcard' ▸ card_union_le _ _

lemma coverNum_singleton_le {S : Finset α} (hS : S ∈ H) (hW : W ⊆ S) : coverNum H W ≤ 1 := by
  simpa using coverNum_le (C := {S}) (by simpa using hS) (by simpa using hW)

lemma coverNum_le_card (h : Covers H W) : coverNum H W ≤ W.card := by
  induction W using Finset.induction_on with
  | empty => simpa using coverNum_le (H := H) (W := ∅) (empty_subset _) (empty_subset _)
  | insert x W hx ih =>
    obtain ⟨S, hS, hxS⟩ := h x (mem_insert_self _ _)
    rw [card_insert_of_notMem hx, insert_eq]
    have hx' : Covers H {x} := h.mono (by simp)
    calc coverNum H ({x} ∪ W) ≤ coverNum H {x} + coverNum H W :=
          coverNum_union_le hx' (h.mono (subset_insert _ _))
      _ ≤ 1 + W.card := by
          gcongr
          · exact coverNum_singleton_le hS (by simpa using hxS)
          · exact ih (h.mono (subset_insert _ _))
      _ = W.card + 1 := add_comm _ _

/-- Removing one member's worth of points lowers the covering number by at most one. -/
lemma coverNum_le_sdiff_add_one {S : Finset α} (hS : S ∈ H) (h : Covers H W) :
    coverNum H W ≤ coverNum H (W \ S) + 1 := by
  obtain ⟨C, hC, hcard, hcov⟩ := exists_cover (W := W \ S) (h.mono sdiff_subset)
  calc coverNum H W ≤ (insert S C).card := by
        refine coverNum_le (insert_subset hS hC) fun x hx => ?_
        rw [sup_insert, id, sup_eq_union, mem_union]
        by_cases hxS : x ∈ S
        · exact Or.inl hxS
        · exact Or.inr (hcov (mem_sdiff.2 ⟨hx, hxS⟩))
    _ ≤ C.card + 1 := card_insert_le _ _
    _ = _ := by rw [hcard]

lemma coverNum_le_erase_add_one {x : α} (h : Covers H W) :
    coverNum H W ≤ coverNum H (W.erase x) + 1 := by
  by_cases hx : x ∈ W
  · obtain ⟨S, hS, hxS⟩ := h x hx
    calc coverNum H W ≤ coverNum H (W \ S) + 1 := coverNum_le_sdiff_add_one hS h
      _ ≤ _ := by
        gcongr
        exact coverNum_mono (h.mono (erase_subset _ _)) fun y hy =>
          mem_erase.2 ⟨fun hyx => (mem_sdiff.1 hy).2 (hyx ▸ hxS), (mem_sdiff.1 hy).1⟩
  · rw [erase_eq_of_notMem hx]; omega

end CoverFree
