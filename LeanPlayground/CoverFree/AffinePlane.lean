module

public import LeanPlayground.CoverFree.Main
public import Mathlib.FieldTheory.Finite.GaloisField

@[expose] public section

/-!
# The affine-plane construction and `T(r)` (Corollary 1.2)

`T(r)` is the least `n` such that some `r`-cover-free family on `n` points has more than `n`
members (`CoverFree.T`).

For a finite field `K` of order `q`, the `q² + q` lines of the affine plane `K²` form a
`(q - 1)`-cover-free family on `q²` points (Erdős–Frankl–Füredi): each line has `q` points and two
lines share at most one, so `q - 1` other lines miss a point of it. So `T(r) ≤ q²` for every
prime power `q > r` (`CoverFree.T_le`). With Theorem 1.1, `T(r) = (r + 1)²` when `r + 1` is a
prime power (`CoverFree.T_eq`).
-/

namespace CoverFree

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-- Some `r`-cover-free family on `[n]` has more than `n` members, i.e. `f(n, r) > n`. -/
def HasLarge (r n : ℕ) : Prop :=
  ∃ F : Finset (Finset (Fin n)), IsCoverFree r F ∧ n < F.card

/-- `T(r)`: the least `n` with `f(n, r) > n`. -/
noncomputable def T (r : ℕ) : ℕ := sInf {n | HasLarge r n}

section Transport

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma IsCoverFree.mono {r r' : ℕ} {F : Finset (Finset α)} (hF : IsCoverFree r' F) (h : r ≤ r') :
    IsCoverFree r F := fun A hA B hB hcard => hF A hA B hB (hcard.trans h)

/-- Cover-freeness is preserved by an injective relabelling of the points. -/
lemma IsCoverFree.map {r : ℕ} {F : Finset (Finset α)} (hF : IsCoverFree r F) (f : α ↪ β) :
    IsCoverFree r (F.map (mapEmbedding f).toEmbedding) := by
  intro A' hA' B' hB' hcard hcov
  obtain ⟨A, hA, rfl⟩ := mem_map.1 hA'
  set B := F.filter (fun B => B.map f ∈ B')
  have hBcard : B.card ≤ B'.card := by
    refine card_le_card_of_injOn (fun B => B.map f) (fun B hB => (mem_filter.1 hB).2) ?_
    intro B₁ _ B₂ _ h
    exact map_injective f h
  refine hF A hA B (fun C hC => ?_) (hBcard.trans hcard) fun x hx => ?_
  · rw [mem_filter] at hC
    refine mem_erase.2 ⟨fun hCA => ?_, hC.1⟩
    subst hCA
    exact (mem_erase.1 (hB' hC.2)).1 rfl
  · obtain ⟨C', hC', hfx⟩ := mem_sup_id.1 (hcov (mem_map_of_mem f hx))
    obtain ⟨C, hC, rfl⟩ := mem_map.1 (mem_of_mem_erase (hB' hC'))
    exact mem_sup_id.2 ⟨C, mem_filter.2 ⟨hC, hC'⟩, by simpa using hfx⟩

/-- A large cover-free family on any type of size `n` gives one on `[n]`. -/
lemma hasLarge_of_fintype [Fintype α] {r : ℕ} {F : Finset (Finset α)} (hF : IsCoverFree r F)
    (hcard : Fintype.card α < F.card) : HasLarge r (Fintype.card α) :=
  ⟨_, hF.map (Fintype.equivFin α).toEmbedding, by simpa using hcard⟩

end Transport

section Linear

variable {α : Type*} [DecidableEq α]

/-- A family of `q`-sets, any two of which share at most one point, is `(q - 1)`-cover-free. -/
lemma isCoverFree_of_linear {q : ℕ} (hq : 0 < q) {F : Finset (Finset α)}
    (hcard : ∀ A ∈ F, A.card = q) (hint : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≤ 1) :
    IsCoverFree (q - 1) F := by
  intro A hA B hB hBcard hcov
  have hsub : A ⊆ B.biUnion (fun C => A ∩ C) := fun x hx => by
    obtain ⟨C, hC, hxC⟩ := mem_sup_id.1 (hcov hx)
    exact mem_biUnion.2 ⟨C, hC, mem_inter.2 ⟨hx, hxC⟩⟩
  have : A.card ≤ B.card :=
    calc A.card ≤ (B.biUnion (fun C => A ∩ C)).card := card_le_card hsub
      _ ≤ ∑ C ∈ B, (A ∩ C).card := card_biUnion_le
      _ ≤ ∑ _C ∈ B, 1 := sum_le_sum fun C hC => by
          have hC' := mem_erase.1 (hB hC)
          exact hint A hA C hC'.2 (Ne.symm hC'.1)
      _ = B.card := by simp
  rw [hcard A hA] at this
  omega

end Linear

section Affine

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- The lines of the affine plane `K²`: `y = m x + c` for `(some m, c)`, and `x = c` for
`(none, c)`. -/
def line : Option K × K → Finset (K × K)
  | (some m, c) =>
    univ.map ⟨fun x => (x, m * x + c), fun x y h => by simpa using congrArg Prod.fst h⟩
  | (none, c) => univ.map ⟨fun y => (c, y), fun x y h => by simpa using congrArg Prod.snd h⟩

variable {K}

lemma mem_line_some {m c : K} {p : K × K} : p ∈ line K (some m, c) ↔ p.2 = m * p.1 + c := by
  simp only [line, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩; rfl
  · intro h; exact ⟨p.1, Prod.ext rfl h.symm⟩

lemma mem_line_none {c : K} {p : K × K} : p ∈ line K (none, c) ↔ p.1 = c := by
  simp only [line, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨y, rfl⟩; rfl
  · intro h; exact ⟨p.2, Prod.ext h.symm rfl⟩

lemma card_line (i : Option K × K) : (line K i).card = Fintype.card K := by
  rcases i with ⟨_ | m, c⟩ <;> simp [line]

/-- Two distinct lines share at most one point. -/
lemma eq_of_mem_line {i j : Option K × K} (hij : i ≠ j) {p p' : K × K} (hpi : p ∈ line K i)
    (hpj : p ∈ line K j) (hp'i : p' ∈ line K i) (hp'j : p' ∈ line K j) : p = p' := by
  obtain ⟨x, y⟩ := p
  obtain ⟨x', y'⟩ := p'
  rcases i with ⟨_ | m, c⟩ <;> rcases j with ⟨_ | m', c'⟩ <;>
    simp only [mem_line_some, mem_line_none] at hpi hpj hp'i hp'j
  · exact absurd (by rw [← hpi, hpj]) hij
  · subst hpi hp'i; simp_all
  · subst hpj hp'j; simp_all
  · by_cases hx : x = x'
    · subst hx; simp_all
    · have hm : m = m' := by
        have : (m - m') * (x - x') = 0 := by linear_combination hpj - hpi - hp'j + hp'i
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hx))
      subst hm
      have : c = c' := by linear_combination hpj - hpi
      exact absurd (by rw [this]) hij

lemma card_inter_line_le {i j : Option K × K} (hij : i ≠ j) :
    (line K i ∩ line K j).card ≤ 1 :=
  card_le_one.2 fun _ hp _ hp' =>
    eq_of_mem_line hij (mem_inter.1 hp).1 (mem_inter.1 hp).2 (mem_inter.1 hp').1
      (mem_inter.1 hp').2

lemma line_injective : Function.Injective (line K) := by
  intro i j h
  by_contra hij
  have h1 := card_inter_line_le hij
  rw [h, inter_self, card_line] at h1
  have := Fintype.one_lt_card (α := K)
  omega

/-- The lines of the affine plane over `K`. -/
def lines (K : Type*) [Field K] [Fintype K] [DecidableEq K] : Finset (Finset (K × K)) :=
  univ.image (line K)

lemma card_lines : (lines K).card = Fintype.card K ^ 2 + Fintype.card K := by
  rw [lines, card_image_of_injective _ line_injective, card_univ, Fintype.card_prod,
    Fintype.card_option]
  ring

lemma isCoverFree_lines : IsCoverFree (Fintype.card K - 1) (lines K) := by
  refine isCoverFree_of_linear Fintype.card_pos (fun A hA => ?_) fun A hA B hB hAB => ?_
  · obtain ⟨i, -, rfl⟩ := mem_image.1 hA
    exact card_line i
  · obtain ⟨i, -, rfl⟩ := mem_image.1 hA
    obtain ⟨j, -, rfl⟩ := mem_image.1 hB
    exact card_inter_line_le fun h => hAB (h ▸ rfl)

/-- `f(q², q - 1) > q²` for the order `q` of a finite field. -/
lemma hasLarge_field : HasLarge (Fintype.card K - 1) (Fintype.card K ^ 2) := by
  have := hasLarge_of_fintype (isCoverFree_lines (K := K)) (by
    rw [card_lines, Fintype.card_prod]
    have := Fintype.card_pos (α := K)
    nlinarith)
  rwa [Fintype.card_prod, ← sq] at this

end Affine

/-- `f(q², r) > q²` for every prime power `q > r`. -/
lemma hasLarge_primePow {r q : ℕ} (hq : IsPrimePow q) (hrq : r < q) : HasLarge r (q ^ 2) := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hq
  have := Fact.mk hp
  classical
  let : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p k) = p ^ k := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p k hk.ne']
  have h := hasLarge_field (K := GaloisField p k)
  rw [hcard] at h
  obtain ⟨F, hF, hFc⟩ := h
  exact ⟨F, hF.mono (by omega), hFc⟩

lemma T_le {r q : ℕ} (hq : IsPrimePow q) (hrq : r < q) : T r ≤ q ^ 2 :=
  Nat.sInf_le (hasLarge_primePow hq hrq)

lemma hasLarge_T (r : ℕ) : HasLarge r (T r) := by
  obtain ⟨p, hp, hp'⟩ := Nat.exists_infinite_primes (r + 1)
  exact Nat.sInf_mem (s := {n | HasLarge r n}) ⟨_, hasLarge_primePow hp'.isPrimePow (by omega)⟩

/-- **Theorem 1.1**, for `T`: `T(r) ≥ (r + 1)²`. -/
theorem sq_le_T (r : ℕ) : (r + 1) ^ 2 ≤ T r := by
  obtain ⟨F, hF, hcard⟩ := hasLarge_T r
  simpa using sq_le_card_of_card_lt hF (by simpa using hcard)

/-- **Corollary 1.2**: if `r + 1` is a prime power, `T(r) = (r + 1)²`. -/
theorem T_eq {r : ℕ} (hr : IsPrimePow (r + 1)) :
    T r = (r + 1) ^ 2 :=
  le_antisymm (T_le hr (Nat.lt_succ_self r)) (sq_le_T r)

end CoverFree
