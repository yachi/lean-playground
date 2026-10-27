module

public import LeanPlayground.CoverFree.Partition
public import LeanPlayground.CoverFree.Weighted
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

/-!
# Stehlík's theorem in the dual form (Lemma 2.1 of Hu–Zhang)

M. Stehlík, *Minimal connected τ-critical hypergraphs*, Graphs Combin. 22 (2006) 421–426,
Theorem 1, in the dual form of Huang–Liu: if every point of `U` is covered by `H`, removing any
point lowers the covering number `κ`, and the graph `G(H)` on `U` is connected, then
`|U| ≥ 2κ - 1` (`CoverFree.stehlikBound`).

We follow Stehlík's proof, dualised. A *galaxy* becomes a good partition of `U` (`IsPart`), and a
*1-star* a singleton block. A minimum good partition (`IsMin`) has `κ` blocks, and a `T`-extreme
one (`IsExt`) has as few singleton blocks as possible among those that keep the points of `T` as
singletons. For two good partitions `P`, `Q`, the graph `gam P Q` joins two points that share a
block of `P` or of `Q`; its components play the role of Stehlík's equivalence classes.

* Lemma 2 — `no_adj_sing`: two singleton blocks of a minimum partition never lie in one member of
  `H` (merge them).
* Lemma 4 — `not_reachable_sing`: in a `T`-extreme partition `P` (`|T| ≤ 1`), no two singleton
  blocks lie in one component of `gam P Q`. Stehlík picks a shortest path and cuts it at the first
  large block. We instead induct on the distance: the first step from the singleton `b` goes
  through a block `{b, w}` of `Q`; if the block `S` of `w` in `P` has `≥ 3` points, moving `w`
  into `{b, w}` removes a singleton; if it is a pair `{w, y}`, the same move turns `y` into the
  singleton, one step closer.
* Lemma 3 — `reachable_of_adj`, and the exchange of two partitions on a component
  (`swap_isMin`), which keeps the number of blocks.
* Lemma 5 — `exists_ext_of_adj`: an `a`-extreme partition can be moved to a `c`-extreme one with
  the same other singletons, for `a` and `c` in a common member.
* Theorem 1 — `ext_sing_eq`: by connectivity, an `x`-extreme partition has `{x}` as its only
  singleton block, so `|U| ≥ 1 + 2(κ - 1)`.
-/

namespace CoverFree

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {U : Finset α}

/-- A minimum good partition of `U`: it has `κ = coverNum H U` blocks. -/
def IsMin (H : Finset (Finset α)) (U : Finset α) (P : Finset (Finset α)) : Prop :=
  IsPart H U P ∧ P.card = coverNum H U

/-- A `T`-extreme partition: a minimum good partition in which the points of `T` are singleton
blocks, with the fewest singleton blocks among all such. -/
def IsExt (H : Finset (Finset α)) (U T : Finset α) (P : Finset (Finset α)) : Prop :=
  IsMin H U P ∧ T ⊆ sing U P ∧
    ∀ P', IsMin H U P' → T ⊆ sing U P' → (sing U P).card ≤ (sing U P').card

/-- The graph on points joining two points in a common block of `P` or of `Q`. -/
def gam (P Q : Finset (Finset α)) : SimpleGraph α :=
  SimpleGraph.fromRel fun a c => ∃ p ∈ P ∪ Q, a ∈ p ∧ c ∈ p

lemma gam_adj {P Q : Finset (Finset α)} {a c : α} :
    (gam P Q).Adj a c ↔ a ≠ c ∧ ∃ p ∈ P ∪ Q, a ∈ p ∧ c ∈ p := by
  rw [gam, SimpleGraph.fromRel_adj]
  refine and_congr_right fun _ => ⟨fun h => ?_, Or.inl⟩
  rcases h with h | ⟨p, hp, h1, h2⟩
  · exact h
  · exact ⟨p, hp, h2, h1⟩

lemma gam_comm (P Q : Finset (Finset α)) : gam P Q = gam Q P := by
  rw [gam, gam, union_comm]

variable {P Q : Finset (Finset α)}

lemma IsMin.card_le (hP : IsMin H U P) {P' : Finset (Finset α)} (hP' : IsPart H U P') :
    P.card ≤ P'.card :=
  hP.2 ▸ hP'.coverNum_le

/-- **Lemma 2.** Two singleton blocks of a minimum partition never lie in a common member of
`H`. -/
lemma no_adj_sing (hP : IsMin H U P) {y z : α} (hy : {y} ∈ P) (hz : {z} ∈ P) (hyz : y ≠ z)
    {S : Finset α} (hS : S ∈ H) (hyS : y ∈ S) (hzS : z ∈ S) : False := by
  have hA : ({{y}, {z}} : Finset (Finset α)) ⊆ P := by
    intro p hp; simp only [mem_insert, mem_singleton] at hp; rcases hp with rfl | rfl <;> assumption
  obtain ⟨hP', hcard⟩ := hP.1.replace hA rfl (isPart_singleton (by simp) hS
    (by simp [insert_subset_iff, hyS, hzS]))
  have h2 : ({{y}, {z}} : Finset (Finset α)).card = 2 := card_pair (by simpa using hyz)
  have := hP.card_le hP'
  rw [card_singleton, h2] at hcard
  omega

/-- A walk of `G` whose points all satisfy `good` is a walk of `G'`, if `G'` keeps the edges of
`G` between good points. -/
lemma exists_walk_transfer {G G' : SimpleGraph α} (good : α → Prop)
    (hadj : ∀ x y, good x → good y → G.Adj x y → G'.Adj x y) :
    ∀ {u v : α} (p : G.Walk u v), (∀ x ∈ p.support, good x) →
      ∃ q : G'.Walk u v, q.length = p.length
  | _, _, .nil, _ => ⟨.nil, rfl⟩
  | _, _, .cons h p, hp => by
    obtain ⟨q, hq⟩ := exists_walk_transfer good hadj p fun x hx =>
      hp x (SimpleGraph.Walk.support_cons _ _ ▸ List.mem_cons_of_mem _ hx)
    refine ⟨.cons (hadj _ _ (hp _ (by simp)) (hp _ (by simp)) h) q, by simp [hq]⟩

/-- The hole move used in Lemma 4: replace the singleton `{b}` and the block `S ∋ w` (with
`b ∉ S`, `|S| ≥ 2`) by `{b, w}` and `S \ {w}`, where `{b, w}` lies in a member of `H`. -/
lemma hole_move (hP : IsMin H U P) {b w : α} {S S₀ : Finset α} (hb : {b} ∈ P) (hS : S ∈ P)
    (hwS : w ∈ S) (hS2 : 2 ≤ S.card) (hS₀ : S₀ ∈ H) (hbS₀ : b ∈ S₀) (hwS₀ : w ∈ S₀) :
    IsMin H U ((P \ {{b}, S}) ∪ {{b, w}, S.erase w}) ∧ b ∉ S := by
  have hbS : b ∉ S := fun h => by
    have := hP.1.eq_singleton hb hS h
    rw [this, card_singleton] at hS2
    omega
  have hbw : b ≠ w := fun h => hbS (h ▸ hwS)
  have hA : ({{b}, S} : Finset (Finset α)) ⊆ P := by
    intro p hp; simp only [mem_insert, mem_singleton] at hp; rcases hp with rfl | rfl <;> assumption
  have hne : ({b} : Finset α) ≠ S := fun h => hbS (h ▸ mem_singleton_self b)
  obtain ⟨S₁, hS₁, hSS₁⟩ := hP.1.good S hS
  have hsup : ({{b}, S} : Finset (Finset α)).sup id = {b, w} ∪ S.erase w := by
    ext y
    simp only [sup_insert, sup_singleton, id, sup_eq_union, mem_union, mem_singleton,
      mem_insert, mem_erase]
    constructor
    · rintro (rfl | h)
      · exact Or.inl (Or.inl rfl)
      · by_cases hyw : y = w
        · exact Or.inl (Or.inr hyw)
        · exact Or.inr ⟨hyw, h⟩
    · rintro ((rfl | rfl) | ⟨_, h⟩)
      · exact Or.inl rfl
      · exact Or.inr hwS
      · exact Or.inr h
  have hB := isPart_pair (H := H) (W₁ := {b, w}) (W₂ := S.erase w) (insert_nonempty _ _)
    (by rw [← card_pos, card_erase_of_mem hwS]; omega)
    (by
      rw [disjoint_left]
      intro y hy hy'
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hbS (mem_of_mem_erase hy')
      · simp at hy')
    hS₀ hS₁ (by simp [insert_subset_iff, hbS₀, hwS₀]) ((erase_subset _ _).trans hSS₁)
  obtain ⟨hP', hcard⟩ := hP.1.replace hA hsup hB
  have h1 : ({{b}, S} : Finset (Finset α)).card = 2 := card_pair hne
  have h2 : ({{b, w}, S.erase w} : Finset (Finset α)).card = 2 := by
    refine card_pair fun h => ?_
    have : b ∈ S.erase w := h ▸ mem_insert_self b {w}
    exact hbS (mem_of_mem_erase this)
  refine ⟨⟨hP', ?_⟩, hbS⟩
  rw [h1, h2] at hcard
  rw [← hP.2]
  omega

lemma mem_hole_move {b w : α} {S Z : Finset α} :
    Z ∈ (P \ {{b}, S}) ∪ {{b, w}, S.erase w} ↔
      (Z ∈ P ∧ Z ≠ {b} ∧ Z ≠ S) ∨ Z = {b, w} ∨ Z = S.erase w := by
  simp only [mem_union, mem_sdiff, mem_insert, mem_singleton, not_or]

/-- The core of Lemma 4, by induction on the distance from `b` to `b'`. -/
lemma not_reachable_sing_aux (hQ : IsPart H U Q) {T : Finset α} {b' : α} (n : ℕ) :
    ∀ (P : Finset (Finset α)) (b : α), IsExt H U T P → {b} ∈ P → b ∉ T → {b'} ∈ P → b ≠ b' →
      (gam P Q).Reachable b b' → (gam P Q).dist b b' = n → False := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P b hext hb hbT hb' hbb' hreach hdist
  obtain ⟨⟨hP, hPcard⟩, hTP, hmin⟩ := hext
  have hPm : IsMin H U P := ⟨hP, hPcard⟩
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  cases p with
  | nil => exact hbb' rfl
  | cons h₁ p' =>
  rename_i w
  obtain ⟨hbw, r, hr, hbr, hwr⟩ := gam_adj.1 h₁
  have hrQ : r ∈ Q := by
    rcases mem_union.1 hr with hr | hr
    · exact absurd (by simpa [hP.eq_singleton hb hr hbr] using hwr) hbw.symm
    · exact hr
  obtain ⟨S₀, hS₀, hrS₀⟩ := hQ.good r hrQ
  have hwU : w ∈ U := hQ.subset hrQ hwr
  obtain ⟨S, hS, hwS⟩ := hP.exists_mem hwU
  -- `S` is not a singleton: otherwise merge `{b}` and `{w}`.
  have hS1 : S.card ≠ 1 := fun h => by
    obtain ⟨c, rfl⟩ := card_eq_one.1 h
    rw [← mem_singleton.1 hwS] at hS
    exact no_adj_sing hPm hb hS hbw (hS₀) (hrS₀ hbr) (hrS₀ hwr)
  have hS2 : 2 ≤ S.card := by
    have := card_pos.2 ⟨w, hwS⟩
    omega
  obtain ⟨hP'm, hbS⟩ := hole_move hPm hb hS hwS hS2 hS₀ (hrS₀ hbr) (hrS₀ hwr)
  set P' := (P \ {{b}, S}) ∪ {{b, w}, S.erase w}
  have hSb : S ≠ {b} := fun h => hbS (h ▸ mem_singleton_self b)
  -- Singleton blocks of `P` other than `{b}` survive.
  have hkeep : ∀ y, {y} ∈ P → y ≠ b → {y} ∈ P' := fun y hy hyb => by
    refine mem_hole_move.2 (Or.inl ⟨hy, by simpa using hyb, fun h => ?_⟩)
    rw [← h, card_singleton] at hS2
    omega
  have hTP' : T ⊆ sing U P' := fun t ht => by
    have ht' := hTP ht
    rw [hP.mem_sing] at ht'
    rw [hP'm.1.mem_sing]
    exact hkeep t ht' fun h => hbT (h ▸ ht)
  -- The singleton blocks of `P'` are those of `P` other than `{b}`, and possibly `S \ {w}`.
  have hsing' : ∀ y, {y} ∈ P' → ({y} ∈ P ∧ y ≠ b) ∨ {y} = S.erase w := fun y hy => by
    rcases mem_hole_move.1 hy with ⟨hy, hyb, -⟩ | hy | hy
    · exact Or.inl ⟨hy, by simpa using hyb⟩
    · have := congrArg card hy
      rw [card_singleton, card_pair hbw] at this
      omega
    · exact Or.inr hy
  rcases Nat.lt_or_ge 2 S.card with hS3 | hS3
  · -- `|S| ≥ 3`: `P'` has fewer singleton blocks.
    have hsub : sing U P' ⊆ (sing U P).erase b := fun y hy => by
      rw [hP'm.1.mem_sing] at hy
      rcases hsing' y hy with ⟨hy, hyb⟩ | hy
      · exact mem_erase.2 ⟨hyb, hP.mem_sing.2 hy⟩
      · have := congrArg card hy
        rw [card_singleton, card_erase_of_mem hwS] at this
        omega
    have hlt : (sing U P').card < (sing U P).card :=
      (card_le_card hsub).trans_lt (card_erase_lt_of_mem (hP.mem_sing.2 hb))
    exact absurd (hmin P' hP'm hTP') (not_le.2 hlt)
  · -- `S = {w, y}`: move the singleton to `y`, one step closer to `b'`.
    have hS2' : S.card = 2 := le_antisymm hS3 hS2
    obtain ⟨y, hy⟩ := card_eq_one.1 (by rw [card_erase_of_mem hwS, hS2'] : (S.erase w).card = 1)
    have hyS : y ∈ S := mem_of_mem_erase (hy ▸ mem_singleton_self y)
    have hyw : y ≠ w := ne_of_mem_erase (hy ▸ mem_singleton_self y)
    have hySw : ∀ v ∈ S, v ≠ w → v = y := fun v hv hvw =>
      mem_singleton.1 (hy ▸ mem_erase.2 ⟨hvw, hv⟩)
    have hyP : {y} ∉ P := fun h => by
      rw [hP.eq_singleton h hS hyS, card_singleton] at hS2'
      omega
    have hy' : {y} ∈ P' := mem_hole_move.2 (Or.inr (Or.inr hy.symm))
    have hyT : y ∉ T := fun h => hyP (hP.mem_sing.1 (hTP h))
    have hb'P' : {b'} ∈ P' := hkeep b' hb' hbb'.symm
    have hb'S : b' ∉ S := fun h => by
      rw [hP.eq_singleton hb' hS h, card_singleton] at hS2'
      omega
    have hyb' : y ≠ b' := fun h => hb'S (h ▸ hyS)
    have hext' : IsExt H U T P' := by
      refine ⟨hP'm, hTP', fun P'' hP'' hTP'' => ?_⟩
      refine le_trans ?_ (hmin P'' hP'' hTP'')
      have hsub : sing U P' ⊆ insert y ((sing U P).erase b) := fun z hz => by
        rw [hP'm.1.mem_sing] at hz
        rcases hsing' z hz with ⟨hz, hzb⟩ | hz
        · exact mem_insert_of_mem (mem_erase.2 ⟨hzb, hP.mem_sing.2 hz⟩)
        · rw [hy] at hz
          rw [singleton_inj.1 hz]
          exact mem_insert_self _ _
      calc (sing U P').card ≤ (insert y ((sing U P).erase b)).card := card_le_card hsub
        _ ≤ ((sing U P).erase b).card + 1 := card_insert_le _ _
        _ = (sing U P).card := card_erase_add_one (hP.mem_sing.2 hb)
    -- The walk continues from `w` to `y`.
    have hwb' : w ≠ b' := fun h => hb'S (h ▸ hwS)
    cases p' with
    | nil => exact hwb' rfl
    | cons h₂ p'' =>
    rename_i w₂
    have hlen : p''.length + 2 = n := by rw [← hdist, ← hp]; simp
    obtain ⟨hww₂, r₂, hr₂, hwr₂, hw₂r₂⟩ := gam_adj.1 h₂
    have hw₂ : y = w₂ := by
      rcases mem_union.1 hr₂ with hr₂ | hr₂
      · rw [hP.eq_of_mem hr₂ hS hwr₂ hwS] at hw₂r₂
        exact (hySw w₂ hw₂r₂ hww₂.symm).symm
      · exfalso
        rw [hQ.eq_of_mem hr₂ hrQ hwr₂ hwr] at hw₂r₂
        by_cases hbw₂ : b = w₂
        · subst hbw₂
          have := SimpleGraph.dist_le p''
          omega
        · have := SimpleGraph.dist_le
            (SimpleGraph.Walk.cons (gam_adj.2 ⟨hbw₂, r, hr, hbr, hw₂r₂⟩) p'')
          simp only [SimpleGraph.Walk.length_cons] at this
          omega
    subst hw₂
    -- Every point of the rest of the walk is closer to `b'` than `b` and `w` are.
    have hfar : ∀ v ∈ p''.support, (gam P Q).dist v b' ≤ p''.length := fun v hv =>
      (SimpleGraph.dist_le (p''.dropUntil v hv)).trans (p''.length_dropUntil_le_length hv)
    have hwfar : n ≤ (gam P Q).dist w b' + 1 := by
      obtain ⟨q, hq⟩ :=
        (SimpleGraph.Walk.reachable (SimpleGraph.Walk.cons h₂ p'')).exists_walk_length_eq_dist
      have := SimpleGraph.dist_le (SimpleGraph.Walk.cons h₁ q)
      simp only [SimpleGraph.Walk.length_cons] at this
      omega
    obtain ⟨q, hq⟩ := exists_walk_transfer (G := gam P Q) (G' := gam P' Q)
      (fun v => v ≠ b ∧ v ≠ w)
      (fun u v hu hv huv => by
        obtain ⟨huv, r', hr', hur', hvr'⟩ := gam_adj.1 huv
        refine gam_adj.2 ⟨huv, r', ?_, hur', hvr'⟩
        rcases mem_union.1 hr' with hr' | hr'
        · refine mem_union_left _ (mem_hole_move.2 (Or.inl ⟨hr', fun h => ?_, fun h => ?_⟩))
          · exact hu.1 (mem_singleton.1 (h ▸ hur'))
          · subst h
            exact huv ((hySw u hur' hu.2).trans (hySw v hvr' hv.2).symm)
        · exact mem_union_right _ hr')
      p'' fun v hv => by
        have := hfar v hv
        refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> omega
    have hdist' : (gam P' Q).dist y b' < n :=
      (SimpleGraph.dist_le q).trans_lt (by omega)
    exact ih _ hdist' P' y hext' hy' hyT hb'P' hyb' (SimpleGraph.Walk.reachable q) rfl

/-- **Lemma 4.** In a `T`-extreme partition `P` with `|T| ≤ 1`, no two singleton blocks lie in
one component of `gam P Q`, for any good partition `Q`. -/
lemma not_reachable_sing (hQ : IsPart H U Q) {T : Finset α} (hT : T.card ≤ 1)
    (hext : IsExt H U T P) {b b' : α} (hb : {b} ∈ P) (hb' : {b'} ∈ P) (hbb' : b ≠ b') :
    ¬ (gam P Q).Reachable b b' := by
  intro hreach
  by_cases hbT : b ∈ T
  · have hb'T : b' ∉ T := fun h => hbb' (card_le_one.1 hT b hbT b' h)
    exact not_reachable_sing_aux hQ _ P b' hext hb' hb'T hb hbb'.symm hreach.symm rfl
  · exact not_reachable_sing_aux hQ _ P b hext hb hbT hb' hbb' hreach rfl

/-! ### Exchanging two partitions on a closed set -/

/-- `X` is a union of blocks of `P` and also of `Q`. -/
def Closed (P Q : Finset (Finset α)) (X : Finset α) : Prop :=
  ∀ p ∈ P ∪ Q, p ⊆ X ∨ Disjoint p X

/-- The blocks of `P` inside `X`, together with the blocks of `Q` outside `X`. -/
def swap (P Q : Finset (Finset α)) (X : Finset α) : Finset (Finset α) :=
  (P \ P.filter (Disjoint · X)) ∪ Q.filter (Disjoint · X)

lemma mem_swap {X Z : Finset α} :
    Z ∈ swap P Q X ↔ (Z ∈ P ∧ ¬ Disjoint Z X) ∨ (Z ∈ Q ∧ Disjoint Z X) := by
  simp only [swap, mem_union, mem_sdiff, mem_filter]
  tauto

lemma singleton_mem_swap {X : Finset α} {y : α} :
    {y} ∈ swap P Q X ↔ ({y} ∈ P ∧ y ∈ X) ∨ ({y} ∈ Q ∧ y ∉ X) := by
  rw [mem_swap, disjoint_singleton_left, not_not]

lemma swap_isPart_card (hP : IsPart H U P) (hQ : IsPart H U Q) {X : Finset α}
    (hX : Closed P Q X) :
    IsPart H U (swap P Q X) ∧
      (swap P Q X).card + (P.filter (Disjoint · X)).card = P.card + (Q.filter (Disjoint · X)).card
    := by
  -- A point of `U` outside `X` lies in a block outside `X`.
  have hout : ∀ R, IsPart H U R → (∀ p ∈ R, p ⊆ X ∨ Disjoint p X) →
      ∀ y, y ∈ U \ X ↔ ∃ p ∈ R.filter (Disjoint · X), y ∈ p := fun R hR hRX y => by
    rw [mem_sdiff, hR.cover]
    constructor
    · rintro ⟨⟨p, hp, hyp⟩, hyX⟩
      refine ⟨p, mem_filter.2 ⟨hp, ?_⟩, hyp⟩
      exact (hRX p hp).resolve_left fun h => hyX (h hyp)
    · rintro ⟨p, hp, hyp⟩
      rw [mem_filter] at hp
      exact ⟨⟨p, hp.1, hyp⟩, disjoint_left.1 hp.2 hyp⟩
  have hPX : ∀ p ∈ P, p ⊆ X ∨ Disjoint p X := fun p hp => hX p (mem_union_left _ hp)
  have hQX : ∀ p ∈ Q, p ⊆ X ∨ Disjoint p X := fun p hp => hX p (mem_union_right _ hp)
  have hsup : (P.filter (Disjoint · X)).sup id = U \ X := by
    ext y; rw [mem_sup_id, hout P hP hPX]
  have hB : IsPart H (U \ X) (Q.filter (Disjoint · X)) :=
    ⟨fun p hp => hQ.nonempty p (mem_filter.1 hp).1, fun p hp => hQ.good p (mem_filter.1 hp).1,
      fun p hp q hq => hQ.disj p (mem_filter.1 hp).1 q (mem_filter.1 hq).1, hout Q hQ hQX⟩
  exact hP.replace (filter_subset _ _) hsup hB

/-- **Exchange.** Swapping two minimum partitions on a closed set gives a minimum partition. -/
lemma swap_isMin (hP : IsMin H U P) (hQ : IsMin H U Q) {X : Finset α} (hX : Closed P Q X) :
    IsMin H U (swap P Q X) := by
  have hX' : Closed Q P X := fun p hp => hX p (by rwa [union_comm])
  obtain ⟨h₁, c₁⟩ := swap_isPart_card hP.1 hQ.1 hX
  obtain ⟨h₂, c₂⟩ := swap_isPart_card hQ.1 hP.1 hX'
  have := hP.card_le h₁
  have := hP.card_le h₂
  have := hQ.2
  have := hP.2
  refine ⟨h₁, ?_⟩
  omega

/-- The component of `a` in `gam P Q`, inside `U`. -/
noncomputable def comp (P Q : Finset (Finset α)) (U : Finset α) (a : α) : Finset α :=
  open Classical in U.filter fun z => (gam P Q).Reachable a z

lemma mem_comp {a z : α} : z ∈ comp P Q U a ↔ z ∈ U ∧ (gam P Q).Reachable a z := by
  classical
  simp [comp]

lemma closed_comp (hP : IsPart H U P) (hQ : IsPart H U Q) (a : α) :
    Closed P Q (comp P Q U a) := by
  intro p hp
  by_cases h : Disjoint p (comp P Q U a)
  · exact Or.inr h
  · left
    obtain ⟨z, hzp, hzX⟩ := not_disjoint_iff.1 h
    have hpU : p ⊆ U := by
      rcases mem_union.1 hp with hp | hp
      · exact hP.subset hp
      · exact hQ.subset hp
    intro y hy
    refine mem_comp.2 ⟨hpU hy, ?_⟩
    rcases eq_or_ne z y with rfl | hzy
    · exact (mem_comp.1 hzX).2
    · exact (mem_comp.1 hzX).2.trans (gam_adj.2 ⟨hzy, p, hp, hzp, hy⟩).reachable

/-- **Lemma 3.** If `{a}` is a block of one minimum partition and `{c}` of another, with `a` and
`c` in a common member of `H`, they lie in one component. -/
lemma reachable_of_adj (hP : IsMin H U P) (hQ : IsMin H U Q) {a c : α} (ha : {a} ∈ P)
    (hc : {c} ∈ Q) (hac : a ≠ c) {S : Finset α} (hS : S ∈ H) (haS : a ∈ S) (hcS : c ∈ S) :
    (gam P Q).Reachable a c := by
  by_contra hr
  have hX := closed_comp hP.1 hQ.1 a
  have hR := swap_isMin hP hQ hX
  have haU : a ∈ U := hP.1.subset ha (mem_singleton_self a)
  refine no_adj_sing hR (singleton_mem_swap.2 (Or.inl ⟨ha, ?_⟩))
    (singleton_mem_swap.2 (Or.inr ⟨hc, ?_⟩)) hac hS haS hcS
  · exact mem_comp.2 ⟨haU, SimpleGraph.Reachable.refl a⟩
  · exact fun h => hr (mem_comp.1 h).2

/-! ### Extreme partitions -/

lemma exists_ext {T : Finset α} (h : ∃ P, IsMin H U P ∧ T ⊆ sing U P) :
    ∃ P, IsExt H U T P := by
  classical
  have hex : ∃ n, ∃ P, (IsMin H U P ∧ T ⊆ sing U P) ∧ (sing U P).card = n :=
    let ⟨P, hP⟩ := h; ⟨_, P, hP, rfl⟩
  obtain ⟨P, hP, hn⟩ := Nat.find_spec hex
  refine ⟨P, hP.1, hP.2, fun P' hP' hTP' => ?_⟩
  rw [hn]
  exact Nat.find_min' hex ⟨P', ⟨hP', hTP'⟩, rfl⟩

/-- By criticality, every point is a singleton block of some minimum partition. -/
lemma exists_isMin_singleton (hcov : Covers H U)
    (hcrit : ∀ x ∈ U, coverNum H (U.erase x) + 1 = coverNum H U) {x : α} (hx : x ∈ U) :
    ∃ P, IsMin H U P ∧ {x} ⊆ sing U P := by
  obtain ⟨P₀, hP₀, hcard⟩ := exists_isPart (hcov.mono (erase_subset x U))
  obtain ⟨S, hS, hxS⟩ := hcov x hx
  obtain ⟨hP, hc⟩ := hP₀.insert_singleton (notMem_erase x U) hS hxS
  rw [insert_erase hx] at hP
  refine ⟨_, ⟨hP, by rw [hc, hcard, hcrit x hx]⟩, ?_⟩
  rw [singleton_subset_iff, hP.mem_sing]
  exact mem_insert_self _ _

/-- The exchange in Lemma 5. If `{a}` is the only singleton block of `P` in the component `X`
and `{c}` the only one of `Q`, swapping `Q` into `P` on `X` moves the singleton from `a` to `c`.
-/
lemma swap_sing (hP : IsMin H U P) (hQ : IsMin H U Q) {X : Finset α} (hX : Closed Q P X)
    {a c : α} (haX : a ∈ X) (hcX : c ∈ X) (ha : {a} ∈ P) (hc : {c} ∈ Q)
    (hPX : ∀ y, {y} ∈ P → y ∈ X → y = a) (hQX : ∀ y, {y} ∈ Q → y ∈ X → y = c) :
    IsMin H U (swap Q P X) ∧ {c} ∈ swap Q P X ∧
      (sing U (swap Q P X)).erase c = (sing U P).erase a ∧
      (sing U (swap Q P X)).card = (sing U P).card := by
  have hR := swap_isMin hQ hP hX
  have hcR : {c} ∈ swap Q P X := singleton_mem_swap.2 (Or.inl ⟨hc, hcX⟩)
  have herase : (sing U (swap Q P X)).erase c = (sing U P).erase a := by
    ext y
    rw [mem_erase, mem_erase, hR.1.mem_sing, hP.1.mem_sing, singleton_mem_swap]
    constructor
    · rintro ⟨hyc, ⟨hy, hyX⟩ | ⟨hy, hyX⟩⟩
      · exact absurd (hQX y hy hyX) hyc
      · exact ⟨fun h => hyX (h ▸ haX), hy⟩
    · rintro ⟨hya, hy⟩
      have hyX : y ∉ X := fun h => hya (hPX y hy h)
      exact ⟨fun h => hyX (h ▸ hcX), Or.inr ⟨hy, hyX⟩⟩
  refine ⟨hR, hcR, herase, ?_⟩
  have h1 := card_erase_add_one (hR.1.mem_sing.2 hcR)
  have h2 := card_erase_add_one (hP.1.mem_sing.2 ha)
  rw [herase] at h1
  omega

/-- **Lemma 5.** If `P` is `a`-extreme and `a`, `c` lie in a common member of `H`, some
`c`-extreme partition has the same singleton blocks as `P` apart from `{a}` and `{c}`. -/
lemma exists_ext_of_adj (hcov : Covers H U)
    (hcrit : ∀ x ∈ U, coverNum H (U.erase x) + 1 = coverNum H U) {a c : α}
    (hP : IsExt H U {a} P) (hcU : c ∈ U) (hac : a ≠ c) {S : Finset α} (hS : S ∈ H)
    (haS : a ∈ S) (hcS : c ∈ S) :
    ∃ P', IsExt H U {c} P' ∧ (sing U P').erase c = (sing U P).erase a := by
  obtain ⟨Q, hQ⟩ := exists_ext (exists_isMin_singleton hcov hcrit hcU)
  have ha : {a} ∈ P := hP.1.1.mem_sing.1 (singleton_subset_iff.1 hP.2.1)
  have hc : {c} ∈ Q := hQ.1.1.mem_sing.1 (singleton_subset_iff.1 hQ.2.1)
  have hreach := reachable_of_adj hP.1 hQ.1 ha hc hac hS haS hcS
  set X := comp P Q U a
  have hX : Closed P Q X := closed_comp hP.1.1 hQ.1.1 a
  have hX' : Closed Q P X := fun p hp => hX p (by rwa [union_comm])
  have haX : a ∈ X := mem_comp.2 ⟨hP.1.1.subset ha (mem_singleton_self a),
    SimpleGraph.Reachable.refl a⟩
  have hcX : c ∈ X := mem_comp.2 ⟨hcU, hreach⟩
  have hPX : ∀ y, {y} ∈ P → y ∈ X → y = a := fun y hy hyX => by
    by_contra hya
    exact not_reachable_sing hQ.1.1 (card_singleton a).le hP ha hy (Ne.symm hya)
      (mem_comp.1 hyX).2
  have hQX : ∀ y, {y} ∈ Q → y ∈ X → y = c := fun y hy hyX => by
    by_contra hyc
    refine not_reachable_sing hP.1.1 (card_singleton c).le hQ hc hy (Ne.symm hyc) ?_
    rw [gam_comm]
    exact hreach.symm.trans (mem_comp.1 hyX).2
  obtain ⟨hR, hcR, herase, hcard⟩ := swap_sing hP.1 hQ.1 hX' haX hcX ha hc hPX hQX
  refine ⟨swap Q P X, ⟨hR, singleton_subset_iff.2 (hR.1.mem_sing.2 hcR), fun P' hP' hcP' => ?_⟩,
    herase⟩
  refine le_trans ?_ (hQ.2.2 P' hP' hcP')
  -- Otherwise swapping the other way would beat `P`.
  by_contra hlt
  push Not at hlt
  obtain ⟨hR', haR', -, hcard'⟩ := swap_sing hQ.1 hP.1 hX hcX haX hc ha hQX hPX
  have := hP.2.2 _ hR' (singleton_subset_iff.2 (hR'.1.mem_sing.2 haR'))
  omega

/-- **Theorem 1** (Stehlík), the key step: in a critical family with connected graph, an
`x`-extreme partition has `{x}` as its only singleton block. -/
lemma ext_sing_eq (hcov : Covers H U)
    (hcrit : ∀ x ∈ U, coverNum H (U.erase x) + 1 = coverNum H U) (hconn : Connected H U)
    {x : α} (hP : IsExt H U {x} P) {y : α} (hy : {y} ∈ P) : y = x := by
  classical
  by_contra hyx
  set R := U.filter fun z => ∃ P', IsExt H U {z} P' ∧ (sing U P').erase z = (sing U P).erase x
  have hxU : x ∈ U := hP.1.1.subset (hP.1.1.mem_sing.1 (singleton_subset_iff.1 hP.2.1))
    (mem_singleton_self x)
  have hyU : y ∈ U := hP.1.1.subset hy (mem_singleton_self y)
  have hxR : x ∈ R := mem_filter.2 ⟨hxU, P, hP, rfl⟩
  have hRU : R = U := by
    by_contra hne
    obtain ⟨S, hS, ⟨a, haS⟩, ⟨c, hcS⟩⟩ := hconn R (filter_subset _ _) ⟨x, hxR⟩ hne
    rw [mem_inter] at haS hcS
    obtain ⟨hcU, hcR⟩ := mem_sdiff.1 hcS.2
    obtain ⟨-, Pa, hPa, hPaE⟩ := mem_filter.1 haS.2
    have hac : a ≠ c := fun h => hcR (h ▸ haS.2)
    obtain ⟨Pc, hPc, hPcE⟩ := exists_ext_of_adj hcov hcrit hPa hcU hac hS haS.1 hcS.1
    exact hcR (mem_filter.2 ⟨hcU, Pc, hPc, hPcE.trans hPaE⟩)
  have hyne : ({y} : Finset α) ≠ U := fun h => hyx (by
    have := h ▸ hxU
    exact (mem_singleton.1 this).symm)
  obtain ⟨S, hS, ⟨y', hy'⟩, ⟨z, hz⟩⟩ := hconn {y} (singleton_subset_iff.2 hyU)
    (singleton_nonempty y) hyne
  rw [mem_inter, mem_singleton] at hy'
  obtain ⟨hzS, hzU⟩ := mem_inter.1 hz
  obtain ⟨hzU, hzy⟩ := mem_sdiff.1 hzU
  have hzR : z ∈ R := hRU ▸ hzU
  obtain ⟨-, Pz, hPz, hPzE⟩ := mem_filter.1 hzR
  have hyPz : y ∈ (sing U Pz).erase z := by
    rw [hPzE]
    exact mem_erase.2 ⟨hyx, hP.1.1.mem_sing.2 hy⟩
  have hzPz : {z} ∈ Pz := hPz.1.1.mem_sing.1 (singleton_subset_iff.1 hPz.2.1)
  exact no_adj_sing hPz.1 (hPz.1.1.mem_sing.1 (mem_of_mem_erase hyPz)) hzPz
    (fun h => hzy (by rw [h]; exact mem_singleton_self z)) hS (hy'.2 ▸ hy'.1) hzS

/-- **Stehlík's theorem** (dual form): a critical family with connected graph has
`|U| ≥ 2κ - 1`. -/
theorem stehlikBound : StehlikBound α := by
  intro H U hcov hcrit hconn
  rcases U.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · have := CoverFree.coverNum_le (H := H) (W := ∅) (empty_subset _) (empty_subset _)
    simp at this
    simp [this]
  obtain ⟨P, hP⟩ := exists_ext (exists_isMin_singleton hcov hcrit hx)
  have hxP : {x} ∈ P := hP.1.1.mem_sing.1 (singleton_subset_iff.1 hP.2.1)
  have hbig : ∀ p ∈ P.erase {x}, 2 ≤ p.card := fun p hp => by
    obtain ⟨hpx, hp⟩ := mem_erase.1 hp
    have hpos := card_pos.2 (hP.1.1.nonempty p hp)
    by_contra h
    obtain ⟨y, rfl⟩ := card_eq_one.1 (by omega : p.card = 1)
    exact hpx (by rw [ext_sing_eq hcov hcrit hconn hP hp])
  have hsum := hP.1.1.card_eq_sum
  rw [← sum_erase_add _ _ hxP, card_singleton] at hsum
  have h2 : 2 * (P.erase {x}).card ≤ ∑ p ∈ P.erase {x}, p.card := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum hbig
  have h3 := card_erase_add_one hxP
  rw [← hP.1.2]
  omega

/-- **Lemma 2.2** of Hu–Zhang, unconditionally. -/
theorem weighted' (H : Finset (Finset α)) (U : Finset α) : WeightedIneq H U :=
  weighted stehlikBound H U

end CoverFree
