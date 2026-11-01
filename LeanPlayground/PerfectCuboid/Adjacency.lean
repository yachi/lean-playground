module

public import Mathlib
public import LeanPlayground.PerfectCuboid.Basic
public import LeanPlayground.PerfectCuboid.FaceCuboid
public import LeanPlayground.PerfectCuboid.LeechEdge

/-!
# Pythagorean adjacency: a triple plus a number adjacent to all three of its sides

Call two positive integers `z, t` *adjacent* (`IsAdjacent z t`) if they are a leg and the
hypotenuse of a right triangle with positive integer sides, i.e. `|z² − t²|` is a nonzero square.
A perfect cuboid is a configuration in this relation (`g` is adjacent to `a, b, c, d, e, f`).
We classify the smallest such configuration: a Pythagorean triple `u² + v² = w²` (`u, v > 0`)
together with a positive `z` adjacent to each of `u, v, w` (`IsTripleAdjacent u v w z`).

## Main results

* `classification`: a triple-adjacent configuration is exactly one of
  - (I, `z > w`) a perfect cuboid `(u, v, r)` with space diagonal `z`, `r² = z² − w²`;
  - (II, `z < u, v`) a **type A** object `(x, y, z)` with `x² = u² − z²`, `y² = v² − z²`;
  - (III, `u, v < z < w`) a **type B** object `(u, r, p)` with `p² = z² − u²`, `r² = w² − z²`;
  - (IV, `u < z < v` or `v < z < u`) a type A object `(p, q, u)` (resp. `(p, q, v)`).
* `IsTypeA x y c`: a face cuboid (`IsFaceCuboid x y c`, `c` the common edge of the two square
  faces) with the extra condition `x² + y² + 2c² = □`, i.e. `g² + c² = □`.
* `IsTypeB u r p`: a face cuboid `IsFaceCuboid u r p` with `r < u` and `u² − r² = □`.
* Converses: `isTripleAdjacent_of_isPerfectCuboid`, `isTripleAdjacent_of_isTypeA`,
  `isTripleAdjacent_of_isTypeB`.
* Fermat kills: `not_isSquare_hyp_sq_add_leg_sq` (`x² + y² = z²`, `x, y > 0` ⇒ `z² + x² ≠ □`,
  since `z⁴ − x⁴ = (y h)²`), hence `IsTypeA.not_isSquare_face` and `IsTypeB.not_isSquare_face`:
  neither type is ever a perfect cuboid; they are genuine face cuboids.
* `IsPerfectCuboid.face_diag_sq_add_ne_sq`: in a perfect cuboid none of `d² + e²`, `d² + f²`,
  `e² + f²` is a square (`d² + e² = g² + a²` and `(a, f, g)` is a right triangle).
* Signed cuboids: `isPerfectCuboid_of_signed_pmm` (pattern `(+,−,−)` is a perfect cuboid seen
  from its space diagonal) and `isTypeA_of_signed_ppm` (pattern `(+,+,−)` is type A).

Degenerate configurations are excluded by `0 < s` in `IsAdjacent` (so `z ∉ {u, v, w}`) and by
`0 < u, v, z`. None of the 126 known primitive face cuboids is of type A or B, and no type-A or
type-B box has common edge `≤ 10⁷`; their arithmetic (twist primes `≡ 1 (mod 8)`, 2-adic shape,
Leech tables) is in `AdjacencyNearMiss.lean`, where they are called `IsBoxA`, `IsBoxB`.
The corollary `face_diag_sq_add_ne_sq` is an easy consequence of Fermat's `z⁴ − x⁴ ≠ □`; we
know no earlier statement of it, but it is not deep.
-/

@[expose] public section

namespace PerfectCuboid.Adjacency

/-- `z` and `t` are a leg and the hypotenuse (in some order) of a right triangle with positive
integer sides. -/
def IsAdjacent (z t : ℕ) : Prop :=
  ∃ s : ℕ, 0 < s ∧ (z ^ 2 = t ^ 2 + s ^ 2 ∨ t ^ 2 = z ^ 2 + s ^ 2)

/-- A Pythagorean triple `(u, v, w)` together with a fourth positive number `z` adjacent to all
three sides. -/
def IsTripleAdjacent (u v w z : ℕ) : Prop :=
  0 < u ∧ 0 < v ∧ 0 < z ∧ u ^ 2 + v ^ 2 = w ^ 2 ∧ IsAdjacent z u ∧ IsAdjacent z v ∧
    IsAdjacent z w

/-- **Type A**: a face cuboid `(x, y, c)` (`c` the common edge of the two square faces) whose
space diagonal `g` is adjacent to `c`: `x² + y² + 2c² = g² + c²` is a square. -/
structure IsTypeA (x y c : ℕ) : Prop extends IsFaceCuboid x y c where
  sq_g_c : IsSquare (x ^ 2 + y ^ 2 + 2 * c ^ 2)

/-- **Type B**: a face cuboid `(u, r, p)` (`p` the common edge) whose two other edges are
adjacent: `r < u` and `u² − r²` is a square. -/
structure IsTypeB (u r p : ℕ) : Prop extends IsFaceCuboid u r p where
  sq_u_r : IsSquare (u ^ 2 - r ^ 2) ∧ r < u

lemma isSquare_of_eq {n m : ℕ} (h : n = m ^ 2) : IsSquare n := ⟨m, by rw [h, sq]⟩

lemma eq_sq_of_isSquare {n : ℕ} (h : IsSquare n) : ∃ m, n = m ^ 2 := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, by rw [hm, sq]⟩

lemma pos_of_sq_eq {v n : ℕ} (h : v ^ 2 = n) (hn : 0 < n) : 0 < v := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp at h; omega
  · exact hv

/-- **Fermat kill.** If `x² + y² = z²` with `x, y > 0`, then `z² + x²` is not a square:
otherwise `z⁴ − x⁴ = (z² − x²)(z² + x²) = (y h)²`, contradicting Fermat (`fermat_sub`). -/
theorem not_isSquare_hyp_sq_add_leg_sq {x y z : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : ¬ IsSquare (z ^ 2 + x ^ 2) := by
  intro hs
  obtain ⟨m, hm⟩ := eq_sq_of_isSquare hs
  have hz : ((z : ℤ)) ^ 4 - (x : ℤ) ^ 4 = ((y * m : ℕ) : ℤ) ^ 2 := by
    have h1 : ((x : ℤ)) ^ 2 + (y : ℤ) ^ 2 = (z : ℤ) ^ 2 := by exact_mod_cast h
    have h2 : ((z : ℤ)) ^ 2 + (x : ℤ) ^ 2 = (m : ℤ) ^ 2 := by exact_mod_cast hm
    push_cast
    linear_combination -((z : ℤ) ^ 2 + (x : ℤ) ^ 2) * h1 + (y : ℤ) ^ 2 * h2
  have hm0 : 0 < m := pos_of_sq_eq hm.symm (by positivity)
  have hz0 : 0 < z := pos_of_sq_eq h.symm (by positivity)
  rcases fermat_sub hz with h0 | h0 | h0
  · omega
  · omega
  · have : y * m = 0 := by exact_mod_cast h0
    rcases Nat.mul_eq_zero.mp this with h' | h' <;> omega

/-! ### The classification -/

/-- **Classification of triple-adjacent configurations.** Exactly the four orderings of `z`
relative to `u, v, w` occur, giving a perfect cuboid (I), a type A object (II, IV) or a type B
object (III). -/
theorem classification {u v w z : ℕ} (H : IsTripleAdjacent u v w z) :
    (∃ r, 0 < r ∧ IsPerfectCuboid u v r ∧ w ^ 2 + r ^ 2 = z ^ 2) ∨
    (∃ x y, IsTypeA x y z ∧ x ^ 2 + z ^ 2 = u ^ 2 ∧ y ^ 2 + z ^ 2 = v ^ 2) ∨
    (∃ p r, IsTypeB u r p ∧ u ^ 2 + p ^ 2 = z ^ 2 ∧ z ^ 2 + r ^ 2 = w ^ 2) ∨
    (∃ p q, IsTypeA p q u ∧ u ^ 2 + p ^ 2 = z ^ 2 ∧ z ^ 2 + q ^ 2 = v ^ 2) ∨
    (∃ p q, IsTypeA p q v ∧ v ^ 2 + p ^ 2 = z ^ 2 ∧ z ^ 2 + q ^ 2 = u ^ 2) := by
  obtain ⟨hu, hv, hz, h, ⟨s₁, hs₁, h₁⟩, ⟨s₂, hs₂, h₂⟩, ⟨s₃, hs₃, h₃⟩⟩ := H
  have hu2 : 0 < u ^ 2 := by positivity
  have hv2 : 0 < v ^ 2 := by positivity
  have hz2 : 0 < z ^ 2 := by positivity
  have p₁ : 0 < s₁ ^ 2 := by positivity
  have p₂ : 0 < s₂ ^ 2 := by positivity
  have p₃ : 0 < s₃ ^ 2 := by positivity
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rcases h₃ with h₃ | h₃
  · -- (I) z > u, v, w: a perfect cuboid
    left
    refine ⟨s₃, hs₃, ⟨⟨hu, hv, hs₃, isSquare_of_eq h, isSquare_of_eq (m := s₁) ?_,
      isSquare_of_eq (m := s₂) ?_⟩, isSquare_of_eq (m := z) ?_⟩, ?_⟩ <;> linarith
  · -- (III) u, v < z < w: type B
    right; right; left
    have hq : u ^ 2 - s₃ ^ 2 = s₂ ^ 2 := by omega
    have hlt : s₃ < u := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (by omega)
    refine ⟨s₁, s₃, ⟨⟨hu, hs₃, hs₁, isSquare_of_eq (m := z) ?_, isSquare_of_eq (m := v) ?_,
      isSquare_of_eq (m := w) ?_⟩, isSquare_of_eq hq, hlt⟩, ?_, ?_⟩ <;> linarith
  · exfalso; linarith
  · -- (IV) u < z < v: type A with common edge u
    right; right; right; left
    refine ⟨s₁, s₂, ⟨⟨hs₁, hs₂, hu, isSquare_of_eq (m := z) ?_, isSquare_of_eq (m := s₃) ?_,
      isSquare_of_eq (m := v) ?_⟩, isSquare_of_eq (m := w) ?_⟩, ?_, ?_⟩ <;> linarith
  · exfalso; linarith
  · -- (IV') v < z < u: type A with common edge v
    right; right; right; right
    refine ⟨s₂, s₁, ⟨⟨hs₂, hs₁, hv, isSquare_of_eq (m := z) ?_, isSquare_of_eq (m := s₃) ?_,
      isSquare_of_eq (m := u) ?_⟩, isSquare_of_eq (m := w) ?_⟩, ?_, ?_⟩ <;> linarith
  · exfalso; linarith
  · -- (II) z < u, v (hence z < w): type A with common edge z
    right; left
    refine ⟨s₁, s₂, ⟨⟨hs₁, hs₂, hz, isSquare_of_eq (m := u) ?_, isSquare_of_eq (m := v) ?_,
      isSquare_of_eq (m := s₃) ?_⟩, isSquare_of_eq (m := w) ?_⟩, ?_, ?_⟩ <;> linarith

/-! ### Converses -/

/-- A perfect cuboid `(a, b, c)` with face diagonal `d` and space diagonal `g` gives the
triple-adjacent configuration `(a, b, d; g)` (type I). -/
theorem isTripleAdjacent_of_isPerfectCuboid {a b c : ℕ} (H : IsPerfectCuboid a b c) :
    ∃ d g, a ^ 2 + b ^ 2 = d ^ 2 ∧ a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 ∧ IsTripleAdjacent a b d g := by
  obtain ⟨d, hd⟩ := eq_sq_of_isSquare H.sq_ab
  obtain ⟨e, he⟩ := eq_sq_of_isSquare H.sq_ca
  obtain ⟨f, hf⟩ := eq_sq_of_isSquare H.sq_bc
  obtain ⟨g, hg⟩ := eq_sq_of_isSquare H.sq_abc
  have ha := H.pos_a; have hb := H.pos_b; have hc := H.pos_c
  have he0 : 0 < e := pos_of_sq_eq he.symm (by positivity)
  have hf0 : 0 < f := pos_of_sq_eq hf.symm (by positivity)
  have hg0 : 0 < g := pos_of_sq_eq hg.symm (by positivity)
  refine ⟨d, g, hd, hg, ha, hb, hg0, hd, ⟨f, hf0, Or.inl ?_⟩, ⟨e, he0, Or.inl ?_⟩,
    ⟨c, hc, Or.inl ?_⟩⟩ <;> linarith

/-- A type A object `(x, y, c)` gives the triple-adjacent configuration
`(√(x² + c²), √(y² + c²), √(g² + c²); c)` (type II). -/
theorem isTripleAdjacent_of_isTypeA {x y c : ℕ} (H : IsTypeA x y c) :
    ∃ u v w, x ^ 2 + c ^ 2 = u ^ 2 ∧ y ^ 2 + c ^ 2 = v ^ 2 ∧ IsTripleAdjacent u v w c := by
  obtain ⟨u, hu⟩ := eq_sq_of_isSquare H.sq_ac
  obtain ⟨v, hv⟩ := eq_sq_of_isSquare H.sq_bc
  obtain ⟨g, hg⟩ := eq_sq_of_isSquare H.sq_abc
  obtain ⟨w, hw⟩ := eq_sq_of_isSquare H.sq_g_c
  have hx := H.pos_a; have hy := H.pos_b; have hc := H.pos_c
  have hu0 : 0 < u := pos_of_sq_eq hu.symm (by positivity)
  have hv0 : 0 < v := pos_of_sq_eq hv.symm (by positivity)
  have hg0 : 0 < g := pos_of_sq_eq hg.symm (by positivity)
  refine ⟨u, v, w, hu, hv, hu0, hv0, hc, ?_, ⟨x, hx, Or.inr ?_⟩, ⟨y, hy, Or.inr ?_⟩,
    ⟨g, hg0, Or.inr ?_⟩⟩ <;> linarith

/-- A type B object `(u, r, p)` gives the triple-adjacent configuration
`(u, √(p² + r²), √(u² + p² + r²); √(u² + p²))` (type III). -/
theorem isTripleAdjacent_of_isTypeB {u r p : ℕ} (H : IsTypeB u r p) :
    ∃ v w z, u ^ 2 + p ^ 2 = z ^ 2 ∧ r ^ 2 + p ^ 2 = v ^ 2 ∧ IsTripleAdjacent u v w z := by
  obtain ⟨z, hz⟩ := eq_sq_of_isSquare H.sq_ac
  obtain ⟨v, hv⟩ := eq_sq_of_isSquare H.sq_bc
  obtain ⟨w, hw⟩ := eq_sq_of_isSquare H.sq_abc
  obtain ⟨q, hq⟩ := eq_sq_of_isSquare H.sq_u_r.1
  have hlt := H.sq_u_r.2
  have hu := H.pos_a; have hr := H.pos_b; have hp := H.pos_c
  have hr2 : r ^ 2 < u ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
  have hq' : u ^ 2 = r ^ 2 + q ^ 2 := by omega
  have hq0 : 0 < q := pos_of_sq_eq hq.symm (by omega)
  have hz0 : 0 < z := pos_of_sq_eq hz.symm (by positivity)
  have hv0 : 0 < v := pos_of_sq_eq hv.symm (by positivity)
  refine ⟨v, w, z, hz, hv, hu, hv0, hz0, ?_, ⟨p, hp, Or.inl ?_⟩, ⟨q, hq0, Or.inl ?_⟩,
    ⟨r, hr, Or.inr ?_⟩⟩ <;> linarith

/-! ### Fermat kills: types A and B are never perfect cuboids -/

/-- A type A object is never a perfect cuboid: if `x² + y² = d²` then `(c, d, g)` is a right
triangle and `g² + c² = x² + y² + 2c²` would be a square. -/
theorem IsTypeA.not_isSquare_face {x y c : ℕ} (H : IsTypeA x y c) : ¬ IsSquare (x ^ 2 + y ^ 2) := by
  intro hs
  obtain ⟨d, hd⟩ := eq_sq_of_isSquare hs
  obtain ⟨g, hg⟩ := eq_sq_of_isSquare H.sq_abc
  have hx := H.pos_a; have hc := H.pos_c
  have hd0 : 0 < d := pos_of_sq_eq hd.symm (by positivity)
  have htri : c ^ 2 + d ^ 2 = g ^ 2 := by linarith
  apply not_isSquare_hyp_sq_add_leg_sq hc hd0 htri
  have : g ^ 2 + c ^ 2 = x ^ 2 + y ^ 2 + 2 * c ^ 2 := by linarith
  rw [this]; exact H.sq_g_c

/-- A type B object is never a perfect cuboid: `u² − r² = q²` makes `(r, q, u)` a right triangle,
and `u² + r²` would be a square (`u⁴ − r⁴ = □`). -/
theorem IsTypeB.not_isSquare_face {u r p : ℕ} (H : IsTypeB u r p) : ¬ IsSquare (u ^ 2 + r ^ 2) := by
  obtain ⟨q, hq⟩ := eq_sq_of_isSquare H.sq_u_r.1
  have hr := H.pos_b
  have hr2 : r ^ 2 < u ^ 2 := Nat.pow_lt_pow_left H.sq_u_r.2 (by norm_num)
  have hq0 : 0 < q := pos_of_sq_eq hq.symm (by omega)
  exact not_isSquare_hyp_sq_add_leg_sq hr hq0 (by omega)

/-- Types A and B are not perfect cuboids (restatement with `IsPerfectCuboid`). -/
theorem IsTypeA.not_isPerfectCuboid {x y c : ℕ} (H : IsTypeA x y c) : ¬ IsPerfectCuboid x y c :=
  fun h ↦ H.not_isSquare_face h.sq_ab

theorem IsTypeB.not_isPerfectCuboid {u r p : ℕ} (H : IsTypeB u r p) : ¬ IsPerfectCuboid u r p :=
  fun h ↦ H.not_isSquare_face h.sq_ab

/-- In a triple-adjacent configuration with `z < w` (cases II–IV), `u, v, ·` never extend to a
perfect cuboid with space diagonal `z`: the only perfect-cuboid case is `z > w`. Equivalently:
every triple-adjacent configuration is either a perfect cuboid or a genuine (non-perfect) face
cuboid of type A or B. -/
theorem classification' {u v w z : ℕ} (H : IsTripleAdjacent u v w z) :
    (∃ r, 0 < r ∧ IsPerfectCuboid u v r) ∨
    (∃ x y c, IsTypeA x y c ∧ ¬ IsSquare (x ^ 2 + y ^ 2)) ∨
    (∃ a b c, IsTypeB a b c ∧ ¬ IsSquare (a ^ 2 + b ^ 2)) := by
  rcases classification H with ⟨r, hr, hp, -⟩ | ⟨x, y, hA, -⟩ | ⟨p, r, hB, -⟩ |
      ⟨p, q, hA, -⟩ | ⟨p, q, hA, -⟩
  · exact Or.inl ⟨r, hr, hp⟩
  · exact Or.inr (Or.inl ⟨x, y, z, hA, hA.not_isSquare_face⟩)
  · exact Or.inr (Or.inr ⟨u, r, p, hB, hB.not_isSquare_face⟩)
  · exact Or.inr (Or.inl ⟨p, q, u, hA, hA.not_isSquare_face⟩)
  · exact Or.inr (Or.inl ⟨p, q, v, hA, hA.not_isSquare_face⟩)

/-! ### Signed cuboids

A *signed cuboid* asks that `|ε₁a² + ε₂b²|`, `|ε₁a² + ε₃c²|`, `|ε₂b² + ε₃c²|`,
`|ε₁a² + ε₂b² + ε₃c²|` be nonzero squares (`εᵢ = ±1`). Up to overall sign and permutation the
patterns are `(+,+,+)` (perfect cuboid), `(+,−,−)` and `(+,+,−)`. We state the two non-trivial
reductions with explicit natural-number witnesses. -/

/-- Pattern `(+,−,−)` is a perfect cuboid seen from its space diagonal: `a² − b² = p²`,
`a² − c² = q²`, `b² + c² = f²`, `a² − b² − c² = h²` (`h > 0`) give the perfect cuboid `(b, c, h)`
with space diagonal `a`. -/
theorem isPerfectCuboid_of_signed_pmm {a b c p q f h : ℕ} (hb : 0 < b) (hc : 0 < c) (hh0 : 0 < h)
    (hp : a ^ 2 = b ^ 2 + p ^ 2) (hq : a ^ 2 = c ^ 2 + q ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hh : a ^ 2 = b ^ 2 + c ^ 2 + h ^ 2) : IsPerfectCuboid b c h :=
  ⟨⟨hb, hc, hh0, isSquare_of_eq hf, isSquare_of_eq (m := p) (by linarith),
    isSquare_of_eq (m := q) (by linarith)⟩, isSquare_of_eq (m := a) (by linarith)⟩

/-- Pattern `(+,+,−)` is type A: `a² + b² = m²`, `a² − c² = x²`, `b² − c² = y²`,
`a² + b² − c² = n²` give the type A object `(x, y, c)`. -/
theorem isTypeA_of_signed_ppm {a b c x y m n : ℕ} (hc : 0 < c) (hx0 : 0 < x) (hy0 : 0 < y)
    (hm : a ^ 2 + b ^ 2 = m ^ 2) (hx : a ^ 2 = c ^ 2 + x ^ 2) (hy : b ^ 2 = c ^ 2 + y ^ 2)
    (hn : a ^ 2 + b ^ 2 = c ^ 2 + n ^ 2) : IsTypeA x y c :=
  ⟨⟨hx0, hy0, hc, isSquare_of_eq (m := a) (by linarith), isSquare_of_eq (m := b) (by linarith),
    isSquare_of_eq (m := n) (by linarith)⟩, isSquare_of_eq (m := m) (by linarith)⟩

end PerfectCuboid.Adjacency

namespace PerfectCuboid

open Adjacency in
/-- **Sums of two squared face diagonals.** In a perfect cuboid with face diagonals
`d² = a² + b²`, `e² = c² + a²`, `f² = b² + c²`, none of `d² + e²`, `d² + f²`, `e² + f²` is a
square: e.g. `d² + e² = g² + a²` and `(a, f, g)` is a right triangle
(`Adjacency.not_isSquare_hyp_sq_add_leg_sq`). -/
theorem IsPerfectCuboid.face_diag_sq_add_ne_sq {a b c d e f : ℕ} (H : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : c ^ 2 + a ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    ¬ IsSquare (d ^ 2 + e ^ 2) ∧ ¬ IsSquare (d ^ 2 + f ^ 2) ∧ ¬ IsSquare (e ^ 2 + f ^ 2) := by
  obtain ⟨g, hg⟩ := eq_sq_of_isSquare H.sq_abc
  have ha := H.pos_a; have hb := H.pos_b; have hc := H.pos_c
  have hd0 : 0 < d := pos_of_sq_eq hd.symm (by positivity)
  have he0 : 0 < e := pos_of_sq_eq he.symm (by positivity)
  have hf0 : 0 < f := pos_of_sq_eq hf.symm (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have := not_isSquare_hyp_sq_add_leg_sq (z := g) ha hf0 (by linarith)
    rwa [show g ^ 2 + a ^ 2 = d ^ 2 + e ^ 2 by linarith] at this
  · have := not_isSquare_hyp_sq_add_leg_sq (z := g) hb he0 (by linarith)
    rwa [show g ^ 2 + b ^ 2 = d ^ 2 + f ^ 2 by linarith] at this
  · have := not_isSquare_hyp_sq_add_leg_sq (z := g) hc hd0 (by linarith)
    rwa [show g ^ 2 + c ^ 2 = e ^ 2 + f ^ 2 by linarith] at this

end PerfectCuboid

