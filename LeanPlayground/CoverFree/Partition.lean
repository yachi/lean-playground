module

public import LeanPlayground.CoverFree.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Good partitions

Tools for the proof of Stehlík's theorem (`LeanPlayground.CoverFree.Stehlik`).

A *good partition* of `W` (`CoverFree.IsPart H W P`) is a partition of `W` into nonempty blocks,
each contained in a member of `H`. These are the minimal covers of Stehlík's dual setting: the
covering number `coverNum H W` is the least number of blocks of a good partition
(`IsPart.coverNum_le`, `exists_isPart`).

The surgery lemma `IsPart.replace` swaps a set `A` of blocks for a good partition `B` of their
union; every construction in the proof of Stehlík's theorem is an instance of it.
-/

namespace CoverFree

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {α : Type*} [DecidableEq α] {H : Finset (Finset α)}

/-- `P` is a partition of `W` into nonempty blocks, each contained in a member of `H`. -/
structure IsPart (H : Finset (Finset α)) (W : Finset α) (P : Finset (Finset α)) : Prop where
  nonempty : ∀ p ∈ P, p.Nonempty
  good : ∀ p ∈ P, ∃ S ∈ H, p ⊆ S
  disj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p q
  cover : ∀ y, y ∈ W ↔ ∃ p ∈ P, y ∈ p

/-- The points of `U` that form a singleton block of `P`. -/
def sing (U : Finset α) (P : Finset (Finset α)) : Finset α := U.filter fun y => {y} ∈ P

variable {U W : Finset α} {P Q : Finset (Finset α)}

namespace IsPart

lemma subset (hP : IsPart H W P) {p : Finset α} (hp : p ∈ P) : p ⊆ W :=
  fun y hy => (hP.cover y).2 ⟨p, hp, hy⟩

lemma eq_of_mem (hP : IsPart H W P) {p q : Finset α} (hp : p ∈ P) (hq : q ∈ P) {y : α}
    (hyp : y ∈ p) (hyq : y ∈ q) : p = q := by
  by_contra h
  exact disjoint_left.1 (hP.disj p hp q hq h) hyp hyq

lemma exists_mem (hP : IsPart H W P) {y : α} (hy : y ∈ W) : ∃ p ∈ P, y ∈ p :=
  (hP.cover y).1 hy

lemma eq_singleton (hP : IsPart H W P) {y : α} (hy : {y} ∈ P) {p : Finset α} (hp : p ∈ P)
    (hyp : y ∈ p) : p = {y} :=
  hP.eq_of_mem hp hy hyp (mem_singleton_self y)

lemma mem_sing (hP : IsPart H W P) {y : α} : y ∈ sing W P ↔ {y} ∈ P := by
  simp only [sing, mem_filter, and_iff_right_iff_imp]
  exact fun h => hP.subset h (mem_singleton_self y)

/-- A good partition of `W` gives a cover of `W` by at most as many members of `H`. -/
lemma coverNum_le (hP : IsPart H W P) : coverNum H W ≤ P.card := by
  classical
  choose! f hf hfp using hP.good
  calc coverNum H W ≤ (P.image f).card := by
        refine CoverFree.coverNum_le (fun S hS => ?_) fun y hy => ?_
        · obtain ⟨p, hp, rfl⟩ := mem_image.1 hS
          exact hf p hp
        · obtain ⟨p, hp, hyp⟩ := hP.exists_mem hy
          exact mem_sup_id.2 ⟨f p, mem_image_of_mem f hp, hfp p hp hyp⟩
    _ ≤ P.card := card_image_le

lemma card_eq_sum (hP : IsPart H W P) : W.card = ∑ p ∈ P, p.card := by
  rw [← card_biUnion fun p hp q hq hpq => hP.disj p hp q hq hpq]
  congr 1
  ext y
  rw [hP.cover, mem_biUnion]

/-- **Surgery**: replacing a set `A` of blocks by a good partition `B` of their union gives a good
partition, with `|A|` blocks fewer and `|B|` blocks more. -/
lemma replace (hP : IsPart H U P) {A B : Finset (Finset α)} (hA : A ⊆ P) {W : Finset α}
    (hW : A.sup id = W) (hB : IsPart H W B) :
    IsPart H U ((P \ A) ∪ B) ∧ ((P \ A) ∪ B).card + A.card = P.card + B.card := by
  subst hW
  -- A block of `P` outside `A` misses the union of `A`.
  have hout : ∀ p ∈ P \ A, ∀ y ∈ p, y ∉ A.sup id := fun p hp y hyp hyA => by
    obtain ⟨a, ha, hya⟩ := mem_sup_id.1 hyA
    rw [mem_sdiff] at hp
    exact disjoint_left.1 (hP.disj p hp.1 a (hA ha) fun h => hp.2 (h ▸ ha)) hyp hya
  have hdisj : Disjoint (P \ A) B := by
    rw [disjoint_left]
    intro p hp hpB
    obtain ⟨y, hy⟩ := hB.nonempty p hpB
    exact hout p hp y hy (hB.subset hpB hy)
  refine ⟨⟨fun p hp => ?_, fun p hp => ?_, fun p hp q hq hpq => ?_, fun y => ?_⟩, ?_⟩
  · rcases mem_union.1 hp with hp | hp
    · exact hP.nonempty p (mem_sdiff.1 hp).1
    · exact hB.nonempty p hp
  · rcases mem_union.1 hp with hp | hp
    · exact hP.good p (mem_sdiff.1 hp).1
    · exact hB.good p hp
  · rcases mem_union.1 hp with hp | hp <;> rcases mem_union.1 hq with hq | hq
    · exact hP.disj p (mem_sdiff.1 hp).1 q (mem_sdiff.1 hq).1 hpq
    · exact disjoint_left.2 fun y hyp hyq => hout p hp y hyp (hB.subset hq hyq)
    · exact disjoint_right.2 fun y hyq hyp => hout q hq y hyq (hB.subset hp hyp)
    · exact hB.disj p hp q hq hpq
  · rw [hP.cover]
    constructor
    · rintro ⟨p, hp, hyp⟩
      by_cases hpA : p ∈ A
      · obtain ⟨q, hq, hyq⟩ := hB.exists_mem (mem_sup_id.2 ⟨p, hpA, hyp⟩)
        exact ⟨q, mem_union_right _ hq, hyq⟩
      · exact ⟨p, mem_union_left _ (mem_sdiff.2 ⟨hp, hpA⟩), hyp⟩
    · rintro ⟨p, hp, hyp⟩
      rcases mem_union.1 hp with hp | hp
      · exact ⟨p, (mem_sdiff.1 hp).1, hyp⟩
      · obtain ⟨a, ha, hya⟩ := mem_sup_id.1 (hB.subset hp hyp)
        exact ⟨a, hA ha, hya⟩
  · rw [card_union_of_disjoint hdisj, add_right_comm, card_sdiff_add_card_eq_card hA]

end IsPart

lemma isPart_singleton {W : Finset α} (hW : W.Nonempty) {S : Finset α} (hS : S ∈ H)
    (hWS : W ⊆ S) : IsPart H W {W} where
  nonempty p hp := by rw [mem_singleton.1 hp]; exact hW
  good p hp := ⟨S, hS, by rw [mem_singleton.1 hp]; exact hWS⟩
  disj p hp q hq hpq := absurd ((mem_singleton.1 hp).trans (mem_singleton.1 hq).symm) hpq
  cover y := by simp

lemma isPart_pair {W₁ W₂ : Finset α} (h₁ : W₁.Nonempty) (h₂ : W₂.Nonempty)
    (hd : Disjoint W₁ W₂) {S₁ S₂ : Finset α} (hS₁ : S₁ ∈ H) (hS₂ : S₂ ∈ H) (h₁S : W₁ ⊆ S₁)
    (h₂S : W₂ ⊆ S₂) : IsPart H (W₁ ∪ W₂) {W₁, W₂} where
  nonempty p hp := by
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact h₁
    · exact h₂
  good p hp := by
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact ⟨S₁, hS₁, h₁S⟩
    · exact ⟨S₂, hS₂, h₂S⟩
  disj p hp q hq hpq := by
    simp only [mem_insert, mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hpq
    · exact hd
    · exact hd.symm
    · exact absurd rfl hpq
  cover y := by simp

/-- Adding a new point as a singleton block. -/
lemma IsPart.insert_singleton (hP : IsPart H W P) {x : α} (hx : x ∉ W) {S : Finset α}
    (hS : S ∈ H) (hxS : x ∈ S) :
    IsPart H (insert x W) (insert {x} P) ∧ (insert {x} P).card = P.card + 1 := by
  have hxP : ({x} : Finset α) ∉ P := fun h => hx (hP.subset h (mem_singleton_self x))
  refine ⟨⟨fun p hp => ?_, fun p hp => ?_, fun p hp q hq hpq => ?_, fun y => ?_⟩,
    card_insert_of_notMem hxP⟩
  · rcases mem_insert.1 hp with rfl | hp
    · exact singleton_nonempty x
    · exact hP.nonempty p hp
  · rcases mem_insert.1 hp with rfl | hp
    · exact ⟨S, hS, singleton_subset_iff.2 hxS⟩
    · exact hP.good p hp
  · have key : ∀ q ∈ P, Disjoint {x} q := fun q hq =>
      disjoint_singleton_left.2 fun h => hx (hP.subset hq h)
    rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq
    · exact absurd rfl hpq
    · exact key q hq
    · exact (key p hp).symm
    · exact hP.disj p hp q hq hpq
  · simp only [mem_insert, exists_eq_or_imp, mem_singleton, hP.cover]

/-- From a cover by members of `H`, a good partition with at most as many blocks. -/
lemma exists_isPart_of_cover {C : Finset (Finset α)} (hC : C ⊆ H) :
    ∀ {W : Finset α}, W ⊆ C.sup id → ∃ P, IsPart H W P ∧ P.card ≤ C.card := by
  induction C using Finset.induction_on with
  | empty =>
    intro W hW
    have : W = ∅ := subset_empty.1 (by simpa using hW)
    subst this
    exact ⟨∅, ⟨by simp, by simp, by simp, by simp⟩, le_rfl⟩
  | insert S C hS ih =>
    intro W hW
    have hSH := hC (mem_insert_self S C)
    obtain ⟨P, hP, hcard⟩ := ih ((subset_insert S C).trans hC) (W := W \ S) fun y hy => by
      have := hW (mem_sdiff.1 hy).1
      rw [sup_insert, id, sup_eq_union, mem_union] at this
      exact this.resolve_left (mem_sdiff.1 hy).2
    by_cases hWS : (W ∩ S).Nonempty
    · have hnot : W ∩ S ∉ P := fun h => by
        obtain ⟨y, hy⟩ := hWS
        exact (mem_sdiff.1 (hP.subset h hy)).2 (mem_inter.1 hy).2
      refine ⟨insert (W ∩ S) P, ⟨fun p hp => ?_, fun p hp => ?_, fun p hp q hq hpq => ?_,
        fun y => ?_⟩, ?_⟩
      · rcases mem_insert.1 hp with rfl | hp
        · exact hWS
        · exact hP.nonempty p hp
      · rcases mem_insert.1 hp with rfl | hp
        · exact ⟨S, hSH, inter_subset_right⟩
        · exact hP.good p hp
      · have key : ∀ q ∈ P, Disjoint (W ∩ S) q := fun q hq => disjoint_left.2 fun y hy hyq =>
          (mem_sdiff.1 (hP.subset hq hyq)).2 (mem_inter.1 hy).2
        rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq
        · exact absurd rfl hpq
        · exact key q hq
        · exact (key p hp).symm
        · exact hP.disj p hp q hq hpq
      · simp only [mem_insert, exists_eq_or_imp, ← hP.cover, mem_inter, mem_sdiff]
        tauto
      · rw [card_insert_of_notMem hnot, card_insert_of_notMem hS]; omega
    · refine ⟨P, ⟨hP.nonempty, hP.good, hP.disj, fun y => ?_⟩, hcard.trans (card_le_card
        (subset_insert _ _))⟩
      rw [← hP.cover, mem_sdiff]
      refine ⟨fun hy => ⟨hy, fun hyS => hWS ⟨y, mem_inter.2 ⟨hy, hyS⟩⟩⟩, fun h => h.1⟩

/-- A good partition with exactly `coverNum H W` blocks. -/
lemma exists_isPart (h : Covers H W) : ∃ P, IsPart H W P ∧ P.card = coverNum H W := by
  obtain ⟨C, hC, hcard, hcov⟩ := exists_cover h
  obtain ⟨P, hP, hPC⟩ := exists_isPart_of_cover hC hcov
  exact ⟨P, hP, le_antisymm (hcard ▸ hPC) hP.coverNum_le⟩

end CoverFree
