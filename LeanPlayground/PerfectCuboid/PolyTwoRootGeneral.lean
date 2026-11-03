module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolyCharP
public import LeanPlayground.PerfectCuboid.PolyNegOne
public import LeanPlayground.PerfectCuboid.PolyPythagoras
public import LeanPlayground.PerfectCuboid.PolyGenusOne
public import LeanPlayground.PerfectCuboid.PolyQuadraticEdge

/-! # An edge with two distinct roots forces proportionality (characteristic 0; round 19, brief 2)

Cuboids over `K[X]` (`PolyCharP.IsCuboid`): nonzero `a, b, c` with `a² + b²`, `a² + c²`,
`b² + c²`, `a² + b² + c²` squares. Here: an edge with **at most two distinct roots, arbitrary
multiplicities, no coprimality hypothesis**.

## Main results (all `[CharZero K]`)

* `exists_parallel_of_edge_X_pow_mul_X_sub_one_pow` (core, no nondegeneracy): in a cuboid with
  edge `a = κ Xʲ (X − 1)ᵏ` (`κ ≠ 0`, `j, k` arbitrary) and `f² = b² + c²`, one of `b`, `c`, `f` is
  a constant multiple of `a`. `exists_parallel_of_two_root_edge`: the same for
  `a = α (X − r)ʲ (X − s)ᵏ`, `r ≠ s` (normalised by `X ↦ (s − r) X + r`).
* `IsNondegCuboid.proportional_of_two_root_edge`: a nondegenerate cuboid with edge
  `α (X − r)ʲ (X − s)ᵏ` (`α ≠ 0`, `r ≠ s`) is `Proportional`;
  `IsCuboid.proportional_of_two_root_edge` under `¬ IsSquare (-1 : K)` instead of nondegeneracy;
  `IsPolyCuboid.exists_isPerfectCuboid_of_two_root_edge`: over `ℚ[X]` such a polynomial cuboid
  yields an integer perfect cuboid.
* `IsNondegCuboid.proportional_of_splits_roots_card_le_two` (edge splits, `≤ 2` distinct roots)
  and `IsNondegCuboid.proportional_of_roots_card_le_two` (`[IsAlgClosed K]`, e.g. `ℂ`): over `ℂ`,
  every edge of a nondegenerate non-proportional cuboid has `≥ 3` distinct affine roots (this is
  what is formalised; `∞` is not counted). The `ℙ¹`-invariant reading — the hyperplane
  `{edge = 0}` meets the rational curve in `≥ 4` points of `ℙ¹` — follows on paper by a Möbius
  reparametrisation sending one zero to `∞`, which is not formalised here.
  (`[DecidableEq K]` appears only to state `a.roots.toFinset`.)
* `IsNondegCuboid.proportional_of_two_root_space_diag`: the same for a space diagonal
  `g = α (X − r)ʲ (X − s)ᵏ`, via `AlgebraicClosure K`, `PolyPythagoras.isNondegCuboid_space_swap`
  (`(g, i b, i c)` is a nondegenerate cuboid) and descent (`exists_C_mul_of_map`).

## Method

For a face `a² + x² = y²`, `(y − x)(y + x) = a²` (`PolyQuadraticEdge.face_identity`), so
`y − x = u Xⁱ (X − 1)ˡ` and `(2x)² + 2a² = w B(P) + (κ⁴/w) B(mir P)` with
`B (i, l) = X^{2i} (X − 1)^{2l}`, `mir (i, l) = (2j − i, 2k − l)`; the centre `P = (j, k)` is
exactly `x ∥ a`, otherwise `P` is oriented into the lexicographic lower half (`leg_shape`).
From `b² + c² = f²`: `T_b + T_c − T_f = 2κ² B(j, k)` (seven terms). Lemmas:
* **L1/L2** (`level_card_fst`, `level_card_snd`): in any relation `Σ_{s ∈ S} c_s B(s) = 0` with all
  `c_s ≠ 0`, the minimal level of either coordinate has `≥ 3` points (coefficients of `X^{2m}`,
  `X^{2m+1}`; the second is `−2l`, and **characteristic 0 is used exactly here**, to cancel
  `c (l₁ − l₂)`; L2 by `X ↦ 1 − X`).
* **Mirror property** (`pair_iff`): unless all three legs coincide, the support of the relation is
  mirror-symmetric; the all-coincide case is `three_point`.
* **Counting** (`half_count`, `count_false`): a mirror-symmetric set of `≤ 7` points containing the
  centre with the level properties in both coordinates cannot exist. Together: `no_relation`.

## Hypotheses are needed

The degenerate `(X(X − 1), b, i d)` (`g = 0`, `f = i a`) shows the core statement's third
alternative is sharp and the nondegeneracy hypothesis is needed for proportionality. No
characteristic-free proof is known: the planner's numerics find no counterexample to the key
linear statement mod 3, 5, 7, 11, 13 for `(j, k) ≤ (3, 3)`, but **nothing is claimed in
characteristic `p`** (the char-`p` non-proportional cuboids — Frobenius, `𝔽₅`, `𝔽₇` — have
edges with `≥ 3` distinct roots anyway).

## Literature

Degrees are unbounded, so this is outside the Stoll–Testa classification of curves of degree
`≤ 6` on the cuboid surface; round 18's `PolyTwoRootEdge` needed the edge coprime to the others
and `−1 ∉ K²`. As far as we know the statement is new. Not done: replacing `[CharZero K]` by the
explicit hypothesis on small integers (stretch (a)); three distinct roots (out of scope). -/

@[expose] public section

open Polynomial

namespace PerfectCuboid.PolyTwoRootGeneral

variable {K : Type*} [Field K]

open PolyCharP PolyQuadraticEdge

/-! ## The monomials `B (i, l) = X^{2i} (X − 1)^{2l}` and the level lemma -/

/-- `B (i, l) = X^{2i} (X − 1)^{2l}`. -/
noncomputable def B (s : ℕ × ℕ) : K[X] := X ^ (2 * s.1) * (X - 1) ^ (2 * s.2)

theorem coeff_B_two_mul {s : ℕ × ℕ} {m : ℕ} (hm : m ≤ s.1) :
    (B s : K[X]).coeff (2 * m) = if s.1 = m then 1 else 0 := by
  rw [B, coeff_X_pow_mul_X_sub_one_pow]
  by_cases h : s.1 = m
  · subst h; simp
  · simp only [show ¬ (2 * s.1 ≤ 2 * m) by omega, h, ite_false]

theorem coeff_B_two_mul_add_one {s : ℕ × ℕ} {m : ℕ} (hm : m ≤ s.1) :
    (B s : K[X]).coeff (2 * m + 1) = if s.1 = m then -(2 * (s.2 : K)) else 0 := by
  rw [B, coeff_X_pow_mul_X_sub_one_pow]
  by_cases h : s.1 = m
  · subst h
    simp only [show 2 * s.1 ≤ 2 * s.1 + 1 by omega, ite_true,
      show 2 * s.1 + 1 - 2 * s.1 = 1 by omega, Nat.choose_one_right]
    rcases Nat.eq_zero_or_pos s.2 with h0 | hpos
    · simp [h0]
    · rw [Odd.neg_one_pow ⟨s.2 - 1, by omega⟩]; push_cast; ring
  · simp only [show ¬ (2 * s.1 ≤ 2 * m + 1) by omega, h, ite_false]

/-- **Level lemma (L1).** In a relation `Σ_{s ∈ S} C (c s) * B s = 0` with all `c s ≠ 0`, the
set of points of `S` on a level `s.1 = m` below all of `S` has neither one nor two elements.
(Coefficients of `X^{2m}` and `X^{2m+1}`; characteristic 0 separates the second coordinates.) -/
theorem level_card_fst [CharZero K] {S : Finset (ℕ × ℕ)} {c : ℕ × ℕ → K}
    (hc : ∀ s ∈ S, c s ≠ 0) (hrel : ∑ s ∈ S, C (c s) * (B s : K[X]) = 0) {m : ℕ}
    (hm : ∀ s ∈ S, m ≤ s.1) :
    (S.filter (fun s => s.1 = m)).card ≠ 1 ∧ (S.filter (fun s => s.1 = m)).card ≠ 2 := by
  have h0 : ∑ s ∈ S.filter (fun s => s.1 = m), c s = 0 := by
    have := congrArg (fun p => coeff p (2 * m)) hrel
    simp only [finsetSum_coeff, coeff_C_mul, coeff_zero] at this
    rw [Finset.sum_filter]
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [coeff_B_two_mul (hm s hs)]; split_ifs <;> simp
  have h1 : ∑ s ∈ S.filter (fun s => s.1 = m), c s * (s.2 : K) = 0 := by
    have := congrArg (fun p => coeff p (2 * m + 1)) hrel
    simp only [finsetSum_coeff, coeff_C_mul, coeff_zero] at this
    have h2 : (2 : K) ≠ 0 := two_ne_zero
    have e : ∑ s ∈ S, c s * (B s : K[X]).coeff (2 * m + 1) =
        -2 * ∑ s ∈ S.filter (fun s => s.1 = m), c s * (s.2 : K) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [coeff_B_two_mul_add_one (hm s hs)]; split_ifs <;> ring
    rw [e] at this
    exact (mul_eq_zero.1 this).resolve_left (by norm_num)
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Finset.card_eq_one.1 h
    rw [ht, Finset.sum_singleton] at h0
    have : t ∈ S.filter (fun s => s.1 = m) := by rw [ht]; exact Finset.mem_singleton_self t
    exact hc t (Finset.mem_filter.1 this).1 h0
  · intro h
    obtain ⟨x, y, hxy, hxy'⟩ := Finset.card_eq_two.1 h
    have hx : x ∈ S.filter (fun s => s.1 = m) := by rw [hxy']; simp
    have hy : y ∈ S.filter (fun s => s.1 = m) := by rw [hxy']; simp
    rw [Finset.mem_filter] at hx hy
    rw [hxy', Finset.sum_pair hxy] at h0 h1
    have h2 : x.2 ≠ y.2 := fun e => hxy (Prod.ext (by rw [hx.2, hy.2]) e)
    have : c x * ((x.2 : K) - y.2) = 0 := by linear_combination h1 - (y.2 : K) * h0
    rcases mul_eq_zero.1 this with h3 | h3
    · exact hc x hx.1 h3
    · exact h2 (by exact_mod_cast sub_eq_zero.1 h3)

theorem B_comp_one_sub (s : ℕ × ℕ) : (B s : K[X]).comp (1 - X) = B s.swap := by
  simp only [B, mul_comp, pow_comp, X_comp, sub_comp, one_comp, Prod.fst_swap, Prod.snd_swap]
  rw [pow_mul, pow_mul, pow_mul, pow_mul]
  have e1 : ((1 : K[X]) - X) ^ 2 = (X - 1) ^ 2 := by ring
  have e2 : ((1 : K[X]) - X - 1) ^ 2 = X ^ 2 := by ring
  rw [e1, e2, mul_comm]

/-- **Level lemma (L2)**, second coordinate (transpose by `X ↦ 1 − X`). -/
theorem level_card_snd [CharZero K] {S : Finset (ℕ × ℕ)} {c : ℕ × ℕ → K}
    (hc : ∀ s ∈ S, c s ≠ 0) (hrel : ∑ s ∈ S, C (c s) * (B s : K[X]) = 0) {m : ℕ}
    (hm : ∀ s ∈ S, m ≤ s.2) :
    (S.filter (fun s => s.2 = m)).card ≠ 1 ∧ (S.filter (fun s => s.2 = m)).card ≠ 2 := by
  have hinj : Function.Injective (Prod.swap : ℕ × ℕ → ℕ × ℕ) := Prod.swap_injective
  have hrel' : ∑ s ∈ S.image Prod.swap, C (c s.swap) * (B s : K[X]) = 0 := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    have := congrArg (fun p => p.comp (1 - X)) hrel
    simp only [sum_comp, mul_comp, C_comp, B_comp_one_sub, zero_comp] at this
    simpa using this
  have hc' : ∀ s ∈ S.image Prod.swap, c s.swap ≠ 0 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    simp [hc t ht]
  have hm' : ∀ s ∈ S.image Prod.swap, m ≤ s.1 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    simpa using hm t ht
  have key := level_card_fst hc' hrel' hm'
  have hcard : ((S.image Prod.swap).filter (fun s => s.1 = m)).card =
      (S.filter (fun s => s.2 = m)).card := by
    rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]
    rfl
  rwa [hcard] at key

/-! ## Counting (pure combinatorics) -/

/-- Shorthand for the level property furnished by `level_card_fst` / `level_card_snd`. -/
def LevelProp (S : Finset (ℕ × ℕ)) (p : ℕ × ℕ → ℕ) : Prop :=
  ∀ m, (∀ s ∈ S, m ≤ p s) → (S.filter (fun s => p s = m)).card ≠ 1 ∧
    (S.filter (fun s => p s = m)).card ≠ 2

theorem exists_min_level {S : Finset (ℕ × ℕ)} {p : ℕ × ℕ → ℕ} (hL : LevelProp S p) {z : ℕ × ℕ}
    (hz : z ∈ S) : ∃ m, (∀ s ∈ S, m ≤ p s) ∧ 3 ≤ (S.filter (fun s => p s = m)).card := by
  obtain ⟨s0, hs0, hmin⟩ := S.exists_min_image p ⟨z, hz⟩
  refine ⟨p s0, hmin, ?_⟩
  have hne : (S.filter (fun s => p s = p s0)).card ≠ 0 := by
    rw [Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    exact ⟨s0, Finset.mem_filter.2 ⟨hs0, rfl⟩⟩
  have := hL _ hmin
  omega

/-- A relation supported on three points `{x, y, z}` (with `z` present) has all three on the
same level. -/
theorem three_point {S : Finset (ℕ × ℕ)} (p : ℕ × ℕ → ℕ) (hL : LevelProp S p) {x y z : ℕ × ℕ}
    (hsub : S ⊆ {x, y, z}) (hz : z ∈ S) : p x = p z := by
  obtain ⟨m, hm, h3⟩ := exists_min_level hL hz
  have hF : S.filter (fun s => p s = m) = {x, y, z} :=
    Finset.eq_of_subset_of_card_le ((Finset.filter_subset _ _).trans hsub)
      (Finset.card_le_three.trans h3)
  have hx : x ∈ S.filter (fun s => p s = m) := by rw [hF]; simp
  have hz' : z ∈ S.filter (fun s => p s = m) := by rw [hF]; simp
  rw [(Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hz').2]

/-- **Half of the counting lemma.** With a mirror symmetry `p (mir s) = 2J − p s` on `S`, at most
seven points, and level properties in both coordinates: there is a level `m < J` with at least
three points, and every point other than `z` lies on level `m` or `2J − m`. -/
theorem half_count {S : Finset (ℕ × ℕ)} (p q : ℕ × ℕ → ℕ)
    (hinj : ∀ s t, p s = p t → q s = q t → s = t) {z : ℕ × ℕ} (hz : z ∈ S) {J : ℕ}
    (hzJ : p z = J) (hcard : S.card ≤ 7) (mir : ℕ × ℕ → ℕ × ℕ) (hmirS : ∀ s ∈ S, mir s ∈ S)
    (hmirp : ∀ s ∈ S, p (mir s) + p s = 2 * J) (hmir2 : ∀ s ∈ S, mir (mir s) = s)
    (hLp : LevelProp S p) (hLq : LevelProp S q) :
    ∃ m < J, (∀ s ∈ S, s ≠ z → p s = m ∨ p s = 2 * J - m) ∧
      3 ≤ (S.filter (fun s => p s = m)).card := by
  obtain ⟨m, hm, h3⟩ := exists_min_level hLp hz
  have hmJ : m ≤ J := hzJ ▸ hm z hz
  have hup : ∀ s ∈ S, p s ≤ 2 * J - m := by
    intro s hs
    have := hm _ (hmirS s hs); have := hmirp s hs; omega
  rcases Nat.lt_or_ge m J with hlt | hge
  · refine ⟨m, hlt, ?_, h3⟩
    set L := S.filter (fun s => p s = m)
    set U := S.filter (fun s => p s = 2 * J - m)
    have hLU : L.card ≤ U.card := by
      refine Finset.card_le_card_of_injOn mir (fun s hs => ?_) (fun s hs t ht hst => ?_)
      · have hs' := Finset.mem_filter.1 hs
        have := hmirp s hs'.1
        exact Finset.mem_filter.2 ⟨hmirS s hs'.1, by omega⟩
      · have hs' := (Finset.mem_filter.1 hs).1
        have ht' := (Finset.mem_filter.1 ht).1
        rw [← hmir2 s hs', ← hmir2 t ht', hst]
    have hdisj : Disjoint L U := by
      rw [Finset.disjoint_left]
      intro s hs hs'
      have := (Finset.mem_filter.1 hs).2; have := (Finset.mem_filter.1 hs').2
      omega
    have hzLU : z ∉ L ∪ U := by
      intro hz'
      rcases Finset.mem_union.1 hz' with h | h <;>
        · have := (Finset.mem_filter.1 h).2; omega
    have hsub : insert z (L ∪ U) ⊆ S := by
      intro s hs
      rcases Finset.mem_insert.1 hs with rfl | hs
      · exact hz
      · rcases Finset.mem_union.1 hs with h | h
        · exact (Finset.mem_filter.1 h).1
        · exact (Finset.mem_filter.1 h).1
    have hcard' : (insert z (L ∪ U)).card = L.card + U.card + 1 := by
      rw [Finset.card_insert_of_notMem hzLU, Finset.card_union_of_disjoint hdisj]
    have heq : insert z (L ∪ U) = S :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    intro s hs hsz
    rw [← heq] at hs
    rcases Finset.mem_insert.1 hs with h | hs
    · exact absurd h hsz
    · rcases Finset.mem_union.1 hs with h | h
      · exact Or.inl (Finset.mem_filter.1 h).2
      · exact Or.inr (Finset.mem_filter.1 h).2
  · exfalso
    have hall : ∀ s ∈ S, p s = J := by
      intro s hs; have := hm s hs; have := hup s hs; omega
    obtain ⟨n, -, h3'⟩ := exists_min_level hLq hz
    have : (S.filter (fun s => q s = n)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro s hs t ht
      have hs' := Finset.mem_filter.1 hs
      have ht' := Finset.mem_filter.1 ht
      exact hinj s t (by rw [hall s hs'.1, hall t ht'.1]) (by rw [hs'.2, ht'.2])
    omega

/-- The mirror `(i, l) ↦ (2j − i, 2k − l)` of the box `[0, 2j] × [0, 2k]`. -/
def mir (j k : ℕ) (s : ℕ × ℕ) : ℕ × ℕ := (2 * j - s.1, 2 * k - s.2)

/-- **Counting lemma (L3, combinatorial core).** A set of at most seven points of the box,
containing the centre `(j, k)`, closed under the mirror, with the level properties in both
coordinates, does not exist. -/
theorem count_false {S : Finset (ℕ × ℕ)} {j k : ℕ} (hz : (j, k) ∈ S) (hcard : S.card ≤ 7)
    (hbox : ∀ s ∈ S, s.1 ≤ 2 * j ∧ s.2 ≤ 2 * k) (hmirS : ∀ s ∈ S, mir j k s ∈ S)
    (hL1 : LevelProp S Prod.fst) (hL2 : LevelProp S Prod.snd) : False := by
  have hmir2 : ∀ s ∈ S, mir j k (mir j k s) = s := by
    intro s hs; have := hbox s hs
    simp only [mir]; ext <;> simp <;> omega
  obtain ⟨m, hmj, hm, h3⟩ := half_count Prod.fst Prod.snd (fun s t h1 h2 => Prod.ext h1 h2) hz
    rfl hcard (mir j k) hmirS (fun s hs => by have := hbox s hs; simp only [mir]; omega) hmir2
    hL1 hL2
  obtain ⟨n, hnk, hn, -⟩ := half_count Prod.snd Prod.fst (fun s t h1 h2 => Prod.ext h2 h1) hz
    rfl hcard (mir j k) hmirS (fun s hs => by have := hbox s hs; simp only [mir]; omega) hmir2
    hL2 hL1
  have hsub : S.filter (fun s => s.1 = m) ⊆ {(m, n), (m, 2 * k - n)} := by
    intro s hs
    have hs' := Finset.mem_filter.1 hs
    have hsz : s ≠ (j, k) := fun h => by rw [h] at hs'; simp at hs'; omega
    rcases hn s hs'.1 hsz with h | h
    · simp [Prod.ext_iff, hs'.2, h]
    · simp [Prod.ext_iff, hs'.2, h]
  have := (Finset.card_le_card hsub).trans Finset.card_le_two
  omega

/-! ## The seven-term relation -/

/-- "Lower half" of the box: strictly before the centre `(j, k)` in lexicographic order. -/
def Lower (j k : ℕ) (s : ℕ × ℕ) : Prop := s.1 < j ∨ (s.1 = j ∧ s.2 < k)

theorem Lower.ne_center {j k : ℕ} {s : ℕ × ℕ} (h : Lower j k s) : s ≠ (j, k) := by
  rintro rfl; rcases h with h | h <;> simp at h

theorem Lower.mir_ne_center {j k : ℕ} {s : ℕ × ℕ} (h : Lower j k s) (hb : s.2 ≤ 2 * k) :
    mir j k s ≠ (j, k) := by
  intro e; simp only [mir, Prod.ext_iff] at e; rcases h with h | h <;> omega

theorem Lower.ne_mir {j k : ℕ} {s t : ℕ × ℕ} (hs : Lower j k s) (ht : Lower j k t)
    (hb : t.2 ≤ 2 * k) : s ≠ mir j k t := by
  intro e; simp only [mir, Prod.ext_iff] at e; rcases hs with h | h <;> rcases ht with h' | h' <;>
    omega

theorem mir_inj {j k : ℕ} {s t : ℕ × ℕ} (hs : s.1 ≤ 2 * j ∧ s.2 ≤ 2 * k)
    (ht : t.1 ≤ 2 * j ∧ t.2 ≤ 2 * k) : mir j k s = mir j k t ↔ s = t := by
  constructor
  · intro e; simp only [mir, Prod.ext_iff] at e; ext <;> omega
  · rintro rfl; rfl

theorem mir_mir {j k : ℕ} {s : ℕ × ℕ} (hs : s.1 ≤ 2 * j ∧ s.2 ≤ 2 * k) :
    mir j k (mir j k s) = s := by
  simp only [mir]; ext <;> simp <;> omega

theorem mir_box {j k : ℕ} (s : ℕ × ℕ) : (mir j k s).1 ≤ 2 * j ∧ (mir j k s).2 ≤ 2 * k := by
  simp only [mir]; omega

theorem Lower.box {j k : ℕ} {s : ℕ × ℕ} (h : Lower j k s) (hb : s.2 ≤ 2 * k) :
    s.1 ≤ 2 * j ∧ s.2 ≤ 2 * k := by
  rcases h with h | h <;> omega

/-- The two-slot contribution of a leg: `w B P + (K4 / w) B (mir P)`. -/
noncomputable def legTerm (j k : ℕ) (K4 w : K) (P : ℕ × ℕ) : K[X] :=
  C w * B P + C (K4 / w) * B (mir j k P)

/-- The coefficient of the relation at a point `s`. -/
noncomputable def coef (j k : ℕ) (K4 d w₁ w₂ w₃ : K) (P₁ P₂ P₃ : ℕ × ℕ) (s : ℕ × ℕ) : K :=
  ((if s = P₁ then w₁ else 0) + (if s = P₂ then w₂ else 0) - (if s = P₃ then w₃ else 0)) +
  ((if s = mir j k P₁ then K4 / w₁ else 0) + (if s = mir j k P₂ then K4 / w₂ else 0) -
    (if s = mir j k P₃ then K4 / w₃ else 0)) - (if s = (j, k) then d else 0)

/-- Mirror property of the coefficients, when not all three legs coincide. -/
theorem pair_iff {K4 w₁ w₂ w₃ : K} (hK4 : K4 ≠ 0) (h₁ : w₁ ≠ 0) (h₂ : w₂ ≠ 0) (h₃ : w₃ ≠ 0)
    (A B' C' : Prop) [Decidable A] [Decidable B'] [Decidable C'] (hn : ¬ (A ∧ B' ∧ C')) :
    ((if A then w₁ else 0) + (if B' then w₂ else 0) - (if C' then w₃ else 0) = 0) ↔
    ((if A then K4 / w₁ else 0) + (if B' then K4 / w₂ else 0) -
      (if C' then K4 / w₃ else 0) = 0) := by
  have e12 : K4 / w₁ + K4 / w₂ = K4 / (w₁ * w₂) * (w₁ + w₂) := by field_simp; ring
  have e13 : K4 / w₁ - K4 / w₃ = K4 / (w₁ * w₃) * (w₃ - w₁) := by field_simp
  have e23 : K4 / w₂ - K4 / w₃ = K4 / (w₂ * w₃) * (w₃ - w₂) := by field_simp
  have k12 : K4 / (w₁ * w₂) ≠ 0 := div_ne_zero hK4 (mul_ne_zero h₁ h₂)
  have k13 : K4 / (w₁ * w₃) ≠ 0 := div_ne_zero hK4 (mul_ne_zero h₁ h₃)
  have k23 : K4 / (w₂ * w₃) ≠ 0 := div_ne_zero hK4 (mul_ne_zero h₂ h₃)
  by_cases hA : A <;> by_cases hB : B' <;> by_cases hC : C' <;>
    simp only [hA, hB, hC, ite_true, ite_false, zero_add, add_zero, sub_zero, zero_sub,
      neg_eq_zero, div_eq_zero_iff, hK4, h₁, h₂, h₃, or_self, and_true,
      not_true_eq_false, and_false, not_false_eq_true] at hn ⊢
  · rw [e12, mul_eq_zero, or_iff_right k12]
  · rw [e13, mul_eq_zero, or_iff_right k13, sub_eq_zero, sub_eq_zero, eq_comm]
  · rw [e23, mul_eq_zero, or_iff_right k23, sub_eq_zero, sub_eq_zero, eq_comm]

/-- **No seven-term relation (L3).** Three legs `(wₜ, Pₜ)` with `Pₜ` in the lower half of the box
cannot satisfy `T₁ + T₂ − T₃ = d · B (j, k)`, `d ≠ 0`, in characteristic 0. -/
theorem no_relation [CharZero K] {j k : ℕ} {K4 d : K} (hK4 : K4 ≠ 0) (hd : d ≠ 0)
    {w₁ w₂ w₃ : K} (h₁ : w₁ ≠ 0) (h₂ : w₂ ≠ 0) (h₃ : w₃ ≠ 0) {P₁ P₂ P₃ : ℕ × ℕ}
    (hl₁ : Lower j k P₁) (hl₂ : Lower j k P₂) (hl₃ : Lower j k P₃)
    (hb₁ : P₁.2 ≤ 2 * k) (hb₂ : P₂.2 ≤ 2 * k) (hb₃ : P₃.2 ≤ 2 * k)
    (hrel : legTerm j k K4 w₁ P₁ + legTerm j k K4 w₂ P₂ - legTerm j k K4 w₃ P₃ -
      C d * B (j, k) = 0) : False := by
  let _ : DecidableEq K := Classical.decEq K
  set cf := coef j k K4 d w₁ w₂ w₃ P₁ P₂ P₃ with hcf
  set T₀ : Finset (ℕ × ℕ) := {P₁, P₂, P₃, mir j k P₁, mir j k P₂, mir j k P₃, (j, k)} with hT₀
  have hsum0 : ∑ s ∈ T₀, C (cf s) * (B s : K[X]) = 0 := by
    rw [← hrel]
    simp only [hcf, coef, legTerm, map_add, map_sub, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, apply_ite C, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
      hT₀, Finset.mem_insert, Finset.mem_singleton, true_or, or_true, ite_true]
    ring
  set S := T₀.filter (fun s => cf s ≠ 0) with hS
  have hc : ∀ s ∈ S, cf s ≠ 0 := fun s hs => (Finset.mem_filter.1 hs).2
  have hrelS : ∑ s ∈ S, C (cf s) * (B s : K[X]) = 0 := by
    rw [hS, Finset.sum_filter_of_ne]
    · exact hsum0
    · intro x _ hx h0; rw [h0, map_zero, zero_mul] at hx; exact hx rfl
  have hL1 : LevelProp S Prod.fst := fun m hm => level_card_fst hc hrelS hm
  have hL2 : LevelProp S Prod.snd := fun m hm => level_card_snd hc hrelS hm
  -- evaluation of the coefficient
  have hbx₁ := hl₁.box hb₁
  have hbx₂ := hl₂.box hb₂
  have hbx₃ := hl₃.box hb₃
  have hcz : cf (j, k) = -d := by
    simp only [hcf, coef, hl₁.ne_center.symm, hl₂.ne_center.symm, hl₃.ne_center.symm,
      (hl₁.mir_ne_center hb₁).symm, (hl₂.mir_ne_center hb₂).symm, (hl₃.mir_ne_center hb₃).symm,
      ite_true, ite_false]
    ring
  have hzS : (j, k) ∈ S := Finset.mem_filter.2 ⟨by simp [hT₀], by rw [hcz]; exact neg_ne_zero.2 hd⟩
  have hT₀box : ∀ s ∈ T₀, s.1 ≤ 2 * j ∧ s.2 ≤ 2 * k := by
    intro s hs
    simp only [hT₀, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | exact mir_box _ | omega
  have hcard : S.card ≤ 7 := by
    refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
    rw [hT₀]
    iterate 6 refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
    simp
  have hbox : ∀ s ∈ S, s.1 ≤ 2 * j ∧ s.2 ≤ 2 * k :=
    fun s hs => hT₀box s (Finset.mem_filter.1 hs).1
  by_cases h3 : P₁ = P₂ ∧ P₂ = P₃
  · -- all three legs coincide: the support lies in `{P₁, mir P₁, (j, k)}`
    obtain ⟨rfl, rfl⟩ := h3
    have hsub : S ⊆ {P₁, mir j k P₁, (j, k)} := by
      intro s hs
      have := (Finset.mem_filter.1 hs).1
      simp only [hT₀, Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]
    have e1 : P₁.1 = j := three_point (S := S) (x := P₁) (y := mir j k P₁) (z := (j, k))
      Prod.fst hL1 hsub hzS
    have e2 : P₁.2 = k := three_point (S := S) (x := P₁) (y := mir j k P₁) (z := (j, k))
      Prod.snd hL2 hsub hzS
    exact hl₁.ne_center (Prod.ext e1 e2)
  -- evaluation at a lower point and at its mirror
  have hlow : ∀ s, Lower j k s → s.2 ≤ 2 * k →
      cf s = (if s = P₁ then w₁ else 0) + (if s = P₂ then w₂ else 0) -
        (if s = P₃ then w₃ else 0) ∧
      cf (mir j k s) = (if s = P₁ then K4 / w₁ else 0) + (if s = P₂ then K4 / w₂ else 0) -
        (if s = P₃ then K4 / w₃ else 0) := by
    intro s hs hsb
    have hsbx := hs.box hsb
    constructor
    · simp only [hcf, coef, hs.ne_mir hl₁ hb₁, hs.ne_mir hl₂ hb₂, hs.ne_mir hl₃ hb₃,
        hs.ne_center, ite_false]
      ring
    · have n₁ : mir j k s ≠ P₁ := fun e => hl₁.ne_mir hs hsb e.symm
      have n₂ : mir j k s ≠ P₂ := fun e => hl₂.ne_mir hs hsb e.symm
      have n₃ : mir j k s ≠ P₃ := fun e => hl₃.ne_mir hs hsb e.symm
      simp only [hcf, coef, n₁, n₂, n₃, hs.mir_ne_center hsb, mir_inj hsbx hbx₁,
        mir_inj hsbx hbx₂, mir_inj hsbx hbx₃, ite_false]
      ring
  have hpair : ∀ s, Lower j k s → s.2 ≤ 2 * k → (cf s ≠ 0 ↔ cf (mir j k s) ≠ 0) := by
    intro s hs hsb
    obtain ⟨e1, e2⟩ := hlow s hs hsb
    rw [e1, e2, Ne, Ne, pair_iff hK4 h₁ h₂ h₃ (s = P₁) (s = P₂) (s = P₃)]
    rintro ⟨rfl, rfl, rfl⟩; exact h3 ⟨rfl, rfl⟩
  have hmirS : ∀ s ∈ S, mir j k s ∈ S := by
    intro s hs
    have hs' := Finset.mem_filter.1 hs
    have hmem := hs'.1
    simp only [hT₀, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.2 ⟨by simp [hT₀], (hpair _ hl₁ hb₁).1 hs'.2⟩
    · exact Finset.mem_filter.2 ⟨by simp [hT₀], (hpair _ hl₂ hb₂).1 hs'.2⟩
    · exact Finset.mem_filter.2 ⟨by simp [hT₀], (hpair _ hl₃ hb₃).1 hs'.2⟩
    · rw [mir_mir hbx₁]; exact Finset.mem_filter.2 ⟨by simp [hT₀], (hpair _ hl₁ hb₁).2 hs'.2⟩
    · rw [mir_mir hbx₂]; exact Finset.mem_filter.2 ⟨by simp [hT₀], (hpair _ hl₂ hb₂).2 hs'.2⟩
    · rw [mir_mir hbx₃]; exact Finset.mem_filter.2 ⟨by simp [hT₀], (hpair _ hl₃ hb₃).2 hs'.2⟩
    · have : mir j k (j, k) = (j, k) := by simp only [mir]; ext <;> simp <;> omega
      rw [this]; exact hs
  exact count_false hzS hcard hbox hmirS hL1 hL2

/-! ## Shape of a leg and the core theorem -/

/-- Divisors of `X^n (X − 1)^m` (generalising `PolyQuadraticEdge.split_divisor`). -/
theorem split_divisor_general {p : K[X]} {n m : ℕ} (h : p ∣ X ^ n * (X - 1) ^ m) :
    ∃ i ≤ n, ∃ l ≤ m, ∃ u : K, u ≠ 0 ∧ p = C u * (X ^ i * (X - 1) ^ l) := by
  obtain ⟨p1, p2, h1, h2, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
  have hZ : Prime (X - 1 : K[X]) := by simpa using prime_X_sub_C (1 : K)
  obtain ⟨i, hi, u, hu, rfl⟩ := exists_C_mul_of_dvd_prime_pow prime_X h1
  obtain ⟨l, hl, w, hw, rfl⟩ := exists_C_mul_of_dvd_prime_pow hZ h2
  exact ⟨i, hi, l, hl, u * w, mul_ne_zero hu hw, by rw [C_mul]; ring⟩

/-- **Shape of a leg.** If `a² + x² = y²` with `a = κ Xʲ (X − 1)ᵏ`, then either `x ∥ a`, or
`(2x)² + 2a² = w B P + (κ⁴/w) B (mir P)` with `P` in the lower half of the box. -/
theorem leg_shape (h2 : (2 : K) ≠ 0) {κ : K} (hκ : κ ≠ 0) {j k : ℕ} {x y : K[X]}
    (h : (C κ * (X ^ j * (X - 1) ^ k)) ^ 2 + x ^ 2 = y ^ 2) :
    (∃ β : K, x = C β * (C κ * (X ^ j * (X - 1) ^ k))) ∨
    ∃ w : K, w ≠ 0 ∧ ∃ P : ℕ × ℕ, Lower j k P ∧ P.2 ≤ 2 * k ∧
      (2 * x) ^ 2 + 2 * (C κ * (X ^ j * (X - 1) ^ k)) ^ 2 = legTerm j k (κ ^ 4) w P := by
  obtain ⟨hpq, hx, hT⟩ := face_identity h
  have ha2 : (C κ * (X ^ j * (X - 1) ^ k)) ^ 2 = C (κ ^ 2) * (X ^ (2 * j) * (X - 1) ^ (2 * k)) := by
    rw [C_pow]; ring
  have hdvd : y - x ∣ X ^ (2 * j) * (X - 1) ^ (2 * k) := by
    have : y - x ∣ C (κ ^ 2) * (X ^ (2 * j) * (X - 1) ^ (2 * k)) := ⟨y + x, by rw [← ha2, hpq]⟩
    exact (IsUnit.dvd_mul_left (isUnit_C.2 (pow_ne_zero 2 hκ).isUnit)).1 this
  obtain ⟨i, hi, l, hl, u, hu, hp⟩ := split_divisor_general hdvd
  have hZ : (X - 1 : K[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : K)
  have hD : (X ^ i * (X - 1) ^ l : K[X]) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hZ)
  have hq : y + x = C u⁻¹ * (C (κ ^ 2) * (X ^ (2 * j - i) * (X - 1) ^ (2 * k - l))) := by
    apply cofactor hu hD hp
    rw [hpq, ha2]
    have e1 : (X : K[X]) ^ i * X ^ (2 * j - i) = X ^ (2 * j) := by
      rw [← pow_add, Nat.add_sub_cancel' hi]
    have e2 : (X - 1 : K[X]) ^ l * (X - 1) ^ (2 * k - l) = (X - 1) ^ (2 * k) := by
      rw [← pow_add, Nat.add_sub_cancel' hl]
    rw [← e1, ← e2]; ring
  by_cases hc : i = j ∧ l = k
  · left
    obtain ⟨rfl, rfl⟩ := hc
    refine ⟨(u⁻¹ * κ ^ 2 - u) / κ / 2, eq_C_mul_of_two_mul h2 ?_⟩
    rw [hx, hq, hp]
    have hk : C ((u⁻¹ * κ ^ 2 - u) / κ) * C κ = C u⁻¹ * C (κ ^ 2) - C u := by
      rw [← C_mul, div_mul_cancel₀ _ hκ, C_sub, C_mul]
    rw [show 2 * i - i = i by omega, show 2 * l - l = l by omega]
    linear_combination (-(X ^ i * (X - 1) ^ l)) * hk
  · right
    have e : (2 * x) ^ 2 + 2 * (C κ * (X ^ j * (X - 1) ^ k)) ^ 2 =
        C (u ^ 2) * B (i, l) + C ((u⁻¹ * κ ^ 2) ^ 2) * B (2 * j - i, 2 * k - l) := by
      rw [hT, hp, hq]
      simp only [B, C_pow, C_mul]; ring
    have hmir : mir j k (2 * j - i, 2 * k - l) = (i, l) := by
      simp only [mir]; ext <;> simp <;> omega
    by_cases hlow : Lower j k (i, l)
    · refine ⟨u ^ 2, pow_ne_zero 2 hu, (i, l), hlow, hl, ?_⟩
      rw [e, legTerm]
      congr 3
      field_simp
    · refine ⟨(u⁻¹ * κ ^ 2) ^ 2, pow_ne_zero 2 (mul_ne_zero (inv_ne_zero hu) (pow_ne_zero 2 hκ)),
        (2 * j - i, 2 * k - l), ?_, by simp, ?_⟩
      · simp only [Lower, not_or, not_and, not_lt] at hlow ⊢
        omega
      · rw [e, legTerm, hmir, add_comm]
        congr 3
        field_simp

/-- **Core theorem (characteristic 0, no nondegeneracy).** In a cuboid with edge
`a = κ Xʲ (X − 1)ᵏ` (`j, k` arbitrary), one of `b`, `c`, `f` (`f² = b² + c²`) is a constant
multiple of `a`. -/
theorem exists_parallel_of_edge_X_pow_mul_X_sub_one_pow [CharZero K] {κ : K} (hκ : κ ≠ 0)
    {j k : ℕ} {b c f : K[X]} (h : IsCuboid (C κ * (X ^ j * (X - 1) ^ k)) b c)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    (∃ β : K, b = C β * (C κ * (X ^ j * (X - 1) ^ k))) ∨
      (∃ γ : K, c = C γ * (C κ * (X ^ j * (X - 1) ^ k))) ∨
      (∃ φ : K, f = C φ * (C κ * (X ^ j * (X - 1) ^ k))) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  set a := C κ * (X ^ j * (X - 1) ^ k) with ha
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨g, hg⟩ := h.sq_abc
  rw [← sq] at hd he hg
  have hg' : a ^ 2 + f ^ 2 = g ^ 2 := by rw [← hg, ← hf]; ring
  rcases leg_shape h2 hκ hd with hb | ⟨w₁, hw₁, P₁, hl₁, hb₁, hB⟩
  · exact Or.inl hb
  rcases leg_shape h2 hκ he with hc | ⟨w₂, hw₂, P₂, hl₂, hb₂, hC⟩
  · exact Or.inr (Or.inl hc)
  rcases leg_shape h2 hκ hg' with hF | ⟨w₃, hw₃, P₃, hl₃, hb₃, hF⟩
  · exact Or.inr (Or.inr hF)
  exfalso
  have hA : 2 * a ^ 2 = C (2 * κ ^ 2) * B (j, k) := by
    rw [ha]; simp only [B, C_mul, C_pow]
    rw [show (C 2 : K[X]) = 2 from map_ofNat C 2]; ring
  refine no_relation (pow_ne_zero 4 hκ) (mul_ne_zero h2 (pow_ne_zero 2 hκ)) hw₁ hw₂ hw₃
    hl₁ hl₂ hl₃ hb₁ hb₂ hb₃ ?_
  linear_combination -hB - hC + hF + 4 * hf + hA

/-! ## Headline theorems -/

/-- Normalisation `X ↦ (s − r) X + r` of a two-root edge. -/
theorem two_root_comp (α r s : K) (j k : ℕ) :
    (C α * ((X - C r) ^ j * (X - C s) ^ k)).comp (C (s - r) * X + C r) =
      C (α * (s - r) ^ (j + k)) * (X ^ j * (X - 1) ^ k) := by
  simp only [mul_comp, pow_comp, sub_comp, X_comp, C_comp, C_mul, C_pow, C_sub]
  have e2 : ((C s - C r) * X + C r - C s : K[X]) = (C s - C r) * (X - 1) := by ring
  have e3 : ((C s - C r) * X + C r - C r : K[X]) = (C s - C r) * X := by ring
  rw [e2, e3, mul_pow, mul_pow, pow_add]
  ring

/-- **Parallel form for two distinct roots, any multiplicities (characteristic 0).** -/
theorem exists_parallel_of_two_root_edge [CharZero K] {α r s : K} (hα : α ≠ 0) (hrs : r ≠ s)
    {j k : ℕ} {b c f : K[X]} (h : IsCuboid (C α * ((X - C r) ^ j * (X - C s) ^ k)) b c)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    (∃ β : K, b = C β * (C α * ((X - C r) ^ j * (X - C s) ^ k))) ∨
      (∃ γ : K, c = C γ * (C α * ((X - C r) ^ j * (X - C s) ^ k))) ∨
      (∃ φ : K, f = C φ * (C α * ((X - C r) ^ j * (X - C s) ^ k))) := by
  have hl : s - r ≠ 0 := sub_ne_zero.2 (Ne.symm hrs)
  have ha' := two_root_comp α r s j k
  have h' := isCuboid_comp_linear h (r := r) hl
  rw [ha'] at h'
  have hfc : (b.comp (C (s - r) * X + C r)) ^ 2 + (c.comp (C (s - r) * X + C r)) ^ 2 =
      (f.comp (C (s - r) * X + C r)) ^ 2 := by
    rw [← pow_comp, ← pow_comp, ← add_comp, hf, pow_comp]
  exact parallel_of_comp hl ha'
    (exists_parallel_of_edge_X_pow_mul_X_sub_one_pow (mul_ne_zero hα (pow_ne_zero _ hl)) h' hfc)

/-- **Headline (characteristic 0).** A nondegenerate cuboid over `K[X]` with an edge
`α (X − r)ʲ (X − s)ᵏ` (`r ≠ s`, any multiplicities) is proportional. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_two_root_edge [CharZero K]
    {α r s : K} (hα : α ≠ 0) (hrs : r ≠ s) {j k : ℕ} {b c : K[X]}
    (h : IsNondegCuboid (C α * ((X - C r) ^ j * (X - C s) ^ k)) b c) :
    Proportional (C α * ((X - C r) ^ j * (X - C s) ^ k)) b c := by
  obtain ⟨f, hf⟩ := h.sq_bc
  rw [← sq] at hf
  exact proportional_of_parallel two_ne_zero h hf
    (exists_parallel_of_two_root_edge hα hrs h.toIsCuboid hf)

/-- **Headline (characteristic 0, `−1 ∉ K²`).** A cuboid with a two-root edge is proportional. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_two_root_edge [CharZero K]
    (hK : ¬ IsSquare (-1 : K)) {α r s : K} (hα : α ≠ 0) (hrs : r ≠ s) {j k : ℕ} {b c : K[X]}
    (h : IsCuboid (C α * ((X - C r) ^ j * (X - C s) ^ k)) b c) :
    Proportional (C α * ((X - C r) ^ j * (X - C s) ^ k)) b c :=
  (h.isNondegCuboid hK).proportional_of_two_root_edge hα hrs

/-- A nonzero split polynomial with at most two distinct roots has the form
`α (X − r)ʲ (X − s)ᵏ` with `r ≠ s`. -/
theorem exists_two_root_form [DecidableEq K] {a : K[X]} (ha : a ≠ 0) (hs : a.Splits)
    (hcard : a.roots.toFinset.card ≤ 2) :
    ∃ α r s : K, α ≠ 0 ∧ r ≠ s ∧ ∃ j k : ℕ, a = C α * ((X - C r) ^ j * (X - C s) ^ k) := by
  classical
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C (splits_iff_card_roots.1 hs)
  rw [Finset.prod_multiset_map_count] at hprod
  have hlc : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 ha
  rcases (show a.roots.toFinset.card = 0 ∨ a.roots.toFinset.card = 1 ∨
      a.roots.toFinset.card = 2 by omega) with h0 | h1 | h2
  · rw [Finset.card_eq_zero.1 h0, Finset.prod_empty, mul_one] at hprod
    exact ⟨_, 0, 1, hlc, zero_ne_one, 0, 0, by rw [← hprod]; simp⟩
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.1 h1
    rw [hr, Finset.prod_singleton] at hprod
    exact ⟨_, r, r + 1, hlc, by simp, Multiset.count r a.roots, 0, by
      rw [pow_zero, mul_one]; exact hprod.symm⟩
  · obtain ⟨r, s, hrs, hr⟩ := Finset.card_eq_two.1 h2
    rw [hr, Finset.prod_pair hrs] at hprod
    exact ⟨_, r, s, hlc, hrs, _, _, hprod.symm⟩

/-- **Headline (characteristic 0, split edge).** A nondegenerate cuboid whose edge `a` splits
with at most two distinct roots is proportional. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_splits_roots_card_le_two
    [CharZero K] [DecidableEq K] {a b c : K[X]} (h : IsNondegCuboid a b c) (hs : a.Splits)
    (ha : a.roots.toFinset.card ≤ 2) : Proportional a b c := by
  obtain ⟨α, r, s, hα, hrs, j, k, rfl⟩ := exists_two_root_form h.ne_a hs ha
  exact h.proportional_of_two_root_edge hα hrs

/-- **Headline (algebraically closed, characteristic 0, e.g. `ℂ`).** A nondegenerate cuboid with
an edge having at most two distinct roots is proportional: every edge of a nondegenerate
non-proportional cuboid over `ℂ[X]` has at least three distinct affine roots (`∞` not counted;
"at least four points of `ℙ¹`" needs a Möbius reparametrisation, not formalised). -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_roots_card_le_two
    [IsAlgClosed K] [CharZero K] [DecidableEq K] {a b c : K[X]} (h : IsNondegCuboid a b c)
    (ha : a.roots.toFinset.card ≤ 2) : Proportional a b c :=
  h.proportional_of_splits_roots_card_le_two (IsAlgClosed.splits a) ha

/-- **`ℚ[X]`:** a polynomial cuboid with an edge `α (X − r)ʲ (X − s)ᵏ` (`r ≠ s`) gives an integer
perfect cuboid. -/
theorem _root_.PerfectCuboid.Poly.IsPolyCuboid.exists_isPerfectCuboid_of_two_root_edge
    {α r s : ℚ} (hα : α ≠ 0) (hrs : r ≠ s) {j k : ℕ} {b c : ℚ[X]}
    (h : Poly.IsPolyCuboid (C α * ((X - C r) ^ j * (X - C s) ^ k)) b c) :
    ∃ A B C : ℕ, IsPerfectCuboid A B C := by
  obtain ⟨q, α', β, γ, h1, h2, h3⟩ := (isCuboid_of_isPolyCuboid h).proportional_of_two_root_edge
    not_isSquare_neg_one_rat hα hrs
  exact h.exists_isPerfectCuboid_of_proportional h1 h2 h3

/-! ## Space diagonal with two roots (via `AlgebraicClosure K`) -/

/-- Field embeddings preserve nondegenerate cuboids. -/
theorem isNondegCuboid_map {L : Type*} [Field L] (φ : K →+* L) {a b c : K[X]}
    (h : IsNondegCuboid a b c) : IsNondegCuboid (a.map φ) (b.map φ) (c.map φ) := by
  have hφ : Function.Injective φ := φ.injective
  have mapne : ∀ {x : K[X]}, x ≠ 0 → x.map φ ≠ 0 := fun hx =>
    (Polynomial.map_ne_zero_iff hφ).mpr hx
  have mapsq : ∀ {x : K[X]}, IsSquare x → IsSquare (x.map φ) := by
    rintro x ⟨r, rfl⟩; exact ⟨r.map φ, Polynomial.map_mul _⟩
  have e2 : ∀ x y : K[X], (x ^ 2 + y ^ 2).map φ = (x.map φ) ^ 2 + (y.map φ) ^ 2 := by
    intro x y; simp only [Polynomial.map_add, Polynomial.map_pow]
  have e3 : ∀ x y z : K[X], (x ^ 2 + y ^ 2 + z ^ 2).map φ =
      (x.map φ) ^ 2 + (y.map φ) ^ 2 + (z.map φ) ^ 2 := by
    intro x y z; simp only [Polynomial.map_add, Polynomial.map_pow]
  exact
    { ne_a := mapne h.ne_a, ne_b := mapne h.ne_b, ne_c := mapne h.ne_c
      sq_ab := e2 a b ▸ mapsq h.sq_ab, sq_ac := e2 a c ▸ mapsq h.sq_ac
      sq_bc := e2 b c ▸ mapsq h.sq_bc, sq_abc := e3 a b c ▸ mapsq h.sq_abc
      ne_ab := e2 a b ▸ mapne h.ne_ab, ne_ac := e2 a c ▸ mapne h.ne_ac
      ne_bc := e2 b c ▸ mapne h.ne_bc, ne_abc := e3 a b c ▸ mapne h.ne_abc }

/-- Descent of "constant multiple" along a field embedding. -/
theorem exists_C_mul_of_map {L : Type*} [Field L] (φ : K →+* L) {x y : K[X]} (hy : y ≠ 0)
    {μ : L} (h : x.map φ = C μ * y.map φ) : ∃ μ' : K, x = C μ' * y := by
  have hφ : Function.Injective φ := φ.injective
  refine ⟨x.leadingCoeff / y.leadingCoeff, Polynomial.map_injective φ hφ ?_⟩
  have hly : φ y.leadingCoeff ≠ 0 := (map_ne_zero φ).2 (leadingCoeff_ne_zero.2 hy)
  have hlc := congrArg leadingCoeff h
  rw [leadingCoeff_map, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_map] at hlc
  rw [Polynomial.map_mul, map_C, h, map_div₀, hlc, mul_div_cancel_right₀ _ hly]

/-- **Headline (characteristic 0, space diagonal).** A nondegenerate cuboid whose space diagonal
is `α (X − r)ʲ (X − s)ᵏ` (`r ≠ s`) is proportional. Proof: over `AlgebraicClosure K` the cuboid
`(g, i b, i c)` (`isNondegCuboid_space_swap`) has a two-root edge, so is proportional; then
`a² = g² − b² − c²` is a constant times the same square, and proportionality descends to `K`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_two_root_space_diag
    [CharZero K] {α r s : K} (hα : α ≠ 0) (hrs : r ≠ s) {j k : ℕ} {a b c : K[X]}
    (h : IsNondegCuboid a b c)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = (C α * ((X - C r) ^ j * (X - C s) ^ k)) ^ 2) :
    Proportional a b c := by
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  have hφ : Function.Injective φ := φ.injective
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : L) two_pos
  have hi0 : i ≠ 0 := by rintro rfl; norm_num at hi
  set g := C α * ((X - C r) ^ j * (X - C s) ^ k) with hgdef
  have hL := isNondegCuboid_map φ h
  have hgL : (a.map φ) ^ 2 + (b.map φ) ^ 2 + (c.map φ) ^ 2 = (g.map φ) ^ 2 := by
    have := congrArg (Polynomial.map φ) hg
    simpa only [Polynomial.map_add, Polynomial.map_pow] using this
  have hsw := PolyPythagoras.isNondegCuboid_space_swap hi hL hgL
  have hG : g.map φ = C (φ α) * ((X - C (φ r)) ^ j * (X - C (φ s)) ^ k) := by
    simp only [hgdef, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  rw [hG] at hsw
  have hprop := hsw.proportional_of_two_root_edge ((map_ne_zero φ).2 hα)
    (fun e => hrs (hφ e))
  rw [← hG] at hprop
  obtain ⟨q, γ₀, β₀, δ₀, hg0, hb0, hc0⟩ := hprop
  have hgne : g.map φ ≠ 0 := by rw [hG]; exact hsw.ne_a
  have hq : q ≠ 0 := by rintro rfl; rw [mul_zero] at hg0; exact hgne hg0
  have hCi : (C i⁻¹ : L[X]) * C i = 1 := by rw [← C_mul, inv_mul_cancel₀ hi0, C_1]
  have hb' : b.map φ = C (i⁻¹ * β₀) * q := by
    rw [C_mul, mul_assoc, ← hb0, ← mul_assoc, hCi, one_mul]
  have hc' : c.map φ = C (i⁻¹ * δ₀) * q := by
    rw [C_mul, mul_assoc, ← hc0, ← mul_assoc, hCi, one_mul]
  have hsq : (a.map φ) ^ 2 = C (γ₀ ^ 2 - (i⁻¹ * β₀) ^ 2 - (i⁻¹ * δ₀) ^ 2) * q ^ 2 := by
    rw [hb', hc', hg0] at hgL
    simp only [C_sub, C_pow]
    linear_combination hgL
  obtain ⟨μ, ha'⟩ := PolyGenusOne.exists_C_mul_of_sq_eq hq hsq
  have hμ : μ ≠ 0 := by
    rintro rfl; rw [C_0, zero_mul] at ha'
    exact (Polynomial.map_ne_zero_iff hφ).mpr h.ne_a ha'
  have hq' : q = C μ⁻¹ * a.map φ := by
    rw [ha', ← mul_assoc, ← C_mul, inv_mul_cancel₀ hμ, C_1, one_mul]
  obtain ⟨β', hβ⟩ := exists_C_mul_of_map φ h.ne_a (μ := i⁻¹ * β₀ * μ⁻¹)
    (by rw [hb', hq', ← mul_assoc, ← C_mul])
  obtain ⟨γ', hγ⟩ := exists_C_mul_of_map φ h.ne_a (μ := i⁻¹ * δ₀ * μ⁻¹)
    (by rw [hc', hq', ← mul_assoc, ← C_mul])
  exact ⟨a, 1, β', γ', by rw [C_1, one_mul], hβ, hγ⟩

end PerfectCuboid.PolyTwoRootGeneral
