module

public import LeanPlayground.PerfectCuboid.CongruentNumber
public import LeanPlayground.PerfectCuboid.LeechEdge
public import Mathlib.NumberTheory.FLT.Four

/-!
# Square lengths and square products in a perfect cuboid

Which of the seven lengths `a, b, c, d, e, f, g` of a perfect cuboid
(`d² = a² + b²`, `e² = a² + c²`, `f² = b² + c²`, `g² = a² + b² + c²`) can be perfect squares,
and which products of two of them?

The seven lengths lie in six Pythagorean triangles `(a, b, d)`, `(a, c, e)`, `(b, c, f)`,
`(a, f, g)`, `(b, e, g)`, `(c, d, g)`, and every pair of lengths except `{d, e}`, `{d, f}`,
`{e, f}` lies in one of them (`18` pairs). For a single Pythagorean triangle `x² + y² = z²` with
positive legs, Fermat's quartics give:

* `not_isSquare_mul_legs`: `x y` is not a square. If `x y = s²` then
  `x⁴ + s⁴ = x²(x² + y²) = (x z)²`, against `not_fermat_42`.
* `not_isSquare_mul_leg_hyp`: `x z` is not a square. If `x z = s²` then
  `z⁴ − s⁴ = z²(z² − x²) = (y z)²`, against `LeechEdge.fermat_sub`. This works for the odd and
  the even leg alike; no parametrization of the triangle is needed.
* `not_isSquare_two_mul_legs`: `2 x y` is not a square (Fermat's right triangle theorem,
  `FermatTriangle.not_isSqAreaTriangle`).
* Consequently (`not_isSquare_legs`, `not_isSquare_leg_hyp`) two lengths of one triangle are
  never both squares.
* `not_isCongruent_two`: `2` is not a congruent number (`a b = 4`, `a² + b² = c²` gives
  `u⁴ + (2v)⁴ = w²` for `a = u/v`).

For a perfect cuboid (`namespace PerfectCuboid`):

* `IsPerfectCuboid.not_isSquare_mul_legs`, `.not_isSquare_mul_leg_hyp`,
  `.not_isSquare_two_mul_legs`: none of the `18` products of two lengths in a common triangle,
  and none of the `6` doubled leg products, is a square.
* `IsPerfectCuboid.not_isSquare_of_isSquare_a` … `_g`: if one length is a square, no length
  sharing a triangle with it is. So at most three lengths are squares, and two square lengths
  are two face diagonals: `IsPerfectCuboid.squares_le_three`.
* `IsPerfectCuboid.abcg_ne_two_mul_sq`, `IsPerfectCuboid.abcg_ne_sq`: `abcg ≠ 2s²` and
  `abcg ≠ s²` (since `abcg/2` is congruent, `IsPerfectCuboid.isCongruent`, while `1` and `2`
  are not).

## Near misses

All statements above use one triangle each (except the `abcg` ones, which use the whole cuboid),
so they hold for Euler bricks too. Bricks can have one square length: the edge `4900 = 70²` of
`(4900, 17157, 23760)` (`isEulerBrick_4900_17157_23760`), the face diagonal `15625 = 125²` of
`(10296, 11753, 16800)` (`isEulerBrick_10296_11753_16800`), the face diagonal `2500 = 50²` of
`(429, 880, 2340)`. Hence "no square edge" or "no square face diagonal" cannot be proved for
perfect cuboids by one-triangle arguments. Whether two face diagonals (`d e = □`, needs
`(de)² = (ag)² + (bc)²`) can both be squares is open.
-/

@[expose] public section

namespace PerfectCuboid.SquareLengths

open CongruentRank

/-- **Fermat.** `2` is not a congruent number: there is no rational right triangle of area `2`.
If `a b = 4` and `a² + b² = c²` then `a⁴ + 16 = (a c)²`; writing `a = u / v` gives
`u⁴ + (2v)⁴ = w²` with `w = a c v² ∈ ℤ`, against `not_fermat_42`. -/
theorem not_isCongruent_two : ¬ IsCongruent 2 := by
  rintro ⟨a, b, c, ha, hb, h1, h2⟩
  have key : a ^ 4 + 16 = (a * c) ^ 2 := by
    linear_combination a ^ 2 * h1 - (a * b + 4) * h2
  set u : ℤ := a.num with hu
  set v : ℕ := a.den with hv
  have hav : a * v = u := Rat.mul_den_eq_num a
  have hu0 : u ≠ 0 := (Rat.num_pos.mpr ha).ne'
  have hv0 : (v : ℤ) ≠ 0 := by have := a.den_pos; omega
  have hsq : IsSquare (((u ^ 4 + (2 * v) ^ 4 : ℤ)) : ℚ) :=
    ⟨a * c * v ^ 2, by push_cast; rw [← hav]; linear_combination (v : ℚ) ^ 4 * key⟩
  obtain ⟨w, hw⟩ := Rat.isSquare_intCast_iff.mp hsq
  exact not_fermat_42 hu0 (mul_ne_zero two_ne_zero hv0) (by rw [hw]; ring)

/-- The hypotenuse of a Pythagorean triangle with a positive leg is positive. -/
theorem hyp_pos {x y z : ℕ} (hx : 0 < x) (h : x ^ 2 + y ^ 2 = z ^ 2) : 0 < z := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · have : 0 < x ^ 2 := by positivity
    simp at h; omega
  · exact hz

/-- The product of the two legs of a Pythagorean triangle is never a square:
`x y = s²` gives `x⁴ + s⁴ = (x z)²`. -/
theorem not_isSquare_mul_legs {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (h : x ^ 2 + y ^ 2 = z ^ 2) :
    ¬ IsSquare (x * y) := by
  rintro ⟨s, hs⟩
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    omega
  have h' : (x : ℤ) ^ 2 + y ^ 2 = z ^ 2 := by exact_mod_cast h
  have hs' : (x : ℤ) * y = s * s := by exact_mod_cast hs
  exact not_fermat_42 (a := (x : ℤ)) (b := (s : ℤ)) (c := (x : ℤ) * z) (by positivity)
    (by exact_mod_cast hs0) (by linear_combination (x : ℤ) ^ 2 * h' - (x * y + s * s) * hs')

/-- A leg times the hypotenuse of a Pythagorean triangle is never a square:
`x z = s²` gives `z⁴ − s⁴ = (y z)²`. -/
theorem not_isSquare_mul_leg_hyp {x y z : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : ¬ IsSquare (x * z) := by
  rintro ⟨s, hs⟩
  have hz := hyp_pos hx h
  have h' : (x : ℤ) ^ 2 + y ^ 2 = z ^ 2 := by exact_mod_cast h
  have hs' : (x : ℤ) * z = s * s := by exact_mod_cast hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    omega
  rcases fermat_sub (x := (z : ℤ)) (y := (s : ℤ)) (z := (y : ℤ) * z)
    (by linear_combination (-(z : ℤ) ^ 2) * h' + (x * z + s * s) * hs') with h0 | h0 | h0
  · omega
  · omega
  · rcases mul_eq_zero.mp h0 with h0 | h0 <;> omega

/-- The other leg times the hypotenuse is never a square. -/
theorem not_isSquare_mul_leg_hyp' {x y z : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : ¬ IsSquare (y * z) :=
  not_isSquare_mul_leg_hyp hy hx (by rw [← h]; ring)

/-- **Fermat's right triangle theorem.** Twice the product of the legs of a Pythagorean
triangle is never a square (`2 x y = s²` makes the area `x y / 2 = (s/2)²` a square). -/
theorem not_isSquare_two_mul_legs {x y z : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : ¬ IsSquare (2 * (x * y)) := by
  rintro ⟨s, hs⟩
  have h2 : 2 ∣ s := by
    have : 2 ∣ s * s := ⟨x * y, hs.symm⟩
    rcases Nat.prime_two.dvd_mul.mp this with h | h <;> exact h
  obtain ⟨t, rfl⟩ := h2
  have ht : x * y = 2 * (t * t) := by linarith
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
    omega
  apply FermatTriangle.not_isSqAreaTriangle x y z t
  refine ⟨by exact_mod_cast hx, by exact_mod_cast hy, by positivity, by exact_mod_cast h, ?_⟩
  have : ((x * y : ℕ) : ℤ) = ((2 * (t * t) : ℕ) : ℤ) := by rw [ht]
  push_cast at this
  linear_combination this

/-- Two legs of a Pythagorean triangle are never both squares (`x⁴ + y⁴ ≠ z²`). -/
theorem not_isSquare_legs {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (h : x ^ 2 + y ^ 2 = z ^ 2) :
    ¬ (IsSquare x ∧ IsSquare y) := fun ⟨hx', hy'⟩ ↦
  not_isSquare_mul_legs hx hy h (hx'.mul hy')

/-- A leg and the hypotenuse of a Pythagorean triangle are never both squares
(`z⁴ − x⁴ ≠ y²`). -/
theorem not_isSquare_leg_hyp {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (h : x ^ 2 + y ^ 2 = z ^ 2) :
    ¬ (IsSquare x ∧ IsSquare z) := fun ⟨hx', hz'⟩ ↦
  not_isSquare_mul_leg_hyp hx hy h (hx'.mul hz')

/-- If `p q` is not a square and `p` is, then `q` is not. -/
theorem not_isSquare_right {p q : ℕ} (h : ¬ IsSquare (p * q)) (hp : IsSquare p) :
    ¬ IsSquare q := fun hq ↦ h (hp.mul hq)

/-- If `p q` is not a square and `q` is, then `p` is not. -/
theorem not_isSquare_left {p q : ℕ} (h : ¬ IsSquare (p * q)) (hq : IsSquare q) :
    ¬ IsSquare p := fun hp ↦ h (hp.mul hq)

/-- All one-triangle facts at once: for positive legs `x, y` and hypotenuse `z`, none of
`x y`, `x z`, `y z`, `2 x y` is a square. -/
theorem triangle {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (h : x ^ 2 + y ^ 2 = z ^ 2) :
    ¬ IsSquare (x * y) ∧ ¬ IsSquare (x * z) ∧ ¬ IsSquare (y * z) ∧ ¬ IsSquare (2 * (x * y)) :=
  ⟨not_isSquare_mul_legs hx hy h, not_isSquare_mul_leg_hyp hx hy h,
    not_isSquare_mul_leg_hyp' hx hy h, not_isSquare_two_mul_legs hx hy h⟩

/-! ### Near-miss examples -/

/-- An Euler brick with a square edge: `4900 = 70²`. Face diagonals `17843, 24260, 29307`. -/
theorem isEulerBrick_4900_17157_23760 : IsEulerBrick 4900 17157 23760 where
  pos_a := by norm_num
  pos_b := by norm_num
  pos_c := by norm_num
  sq_ab := ⟨17843, by norm_num⟩
  sq_bc := ⟨29307, by norm_num⟩
  sq_ca := ⟨24260, by norm_num⟩

example : IsSquare 4900 := ⟨70, by norm_num⟩

/-- An Euler brick with a square face diagonal: `√(10296² + 11753²) = 15625 = 125²`. -/
theorem isEulerBrick_10296_11753_16800 : IsEulerBrick 10296 11753 16800 where
  pos_a := by norm_num
  pos_b := by norm_num
  pos_c := by norm_num
  sq_ab := ⟨15625, by norm_num⟩
  sq_bc := ⟨20503, by norm_num⟩
  sq_ca := ⟨19704, by norm_num⟩

example : 10296 ^ 2 + 11753 ^ 2 = (125 ^ 2) ^ 2 := by norm_num

/-- A face cuboid (`a² + c²`, `b² + c²`, `a² + b² + c²` squares) with a square space diagonal:
`(468, 4180, 399)`, `g = 4225 = 65²`. -/
example : 468 ^ 2 + 399 ^ 2 = 615 ^ 2 ∧ 4180 ^ 2 + 399 ^ 2 = 4199 ^ 2 ∧
    468 ^ 2 + 4180 ^ 2 + 399 ^ 2 = (65 ^ 2) ^ 2 := by norm_num

end PerfectCuboid.SquareLengths

namespace PerfectCuboid

open SquareLengths CongruentRank

variable {a b c d e f g : ℕ}

/-- The six Pythagorean triangles of a perfect cuboid, with positivity of all seven lengths. -/
theorem IsPerfectCuboid.six_triangles (h : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧
      a ^ 2 + f ^ 2 = g ^ 2 ∧ b ^ 2 + e ^ 2 = g ^ 2 ∧ c ^ 2 + d ^ 2 = g ^ 2 := by
  have ha := h.pos_a; have hb := h.pos_b; have hc := h.pos_c
  have h1 : a ^ 2 + f ^ 2 = g ^ 2 := by rw [← hg, ← hf]; ring
  have h2 : b ^ 2 + e ^ 2 = g ^ 2 := by rw [← hg, ← he]; ring
  have h3 : c ^ 2 + d ^ 2 = g ^ 2 := by rw [← hg, ← hd]; ring
  exact ⟨ha, hb, hc, hyp_pos ha hd, hyp_pos ha he, hyp_pos hb hf, hyp_pos ha h1, h1, h2, h3⟩

/-- **Leg·leg products.** In a perfect cuboid none of the six products of the two legs of one
of its right triangles (`a b`, `a c`, `b c`, `a f`, `b e`, `c d`) is a square. -/
theorem IsPerfectCuboid.not_isSquare_mul_legs (h : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    ¬ IsSquare (a * b) ∧ ¬ IsSquare (a * c) ∧ ¬ IsSquare (b * c) ∧
      ¬ IsSquare (a * f) ∧ ¬ IsSquare (b * e) ∧ ¬ IsSquare (c * d) := by
  obtain ⟨ha, hb, hc, hd0, he0, hf0, -, h1, h2, h3⟩ := h.six_triangles hd he hf hg
  exact ⟨(triangle ha hb hd).1, (triangle ha hc he).1, (triangle hb hc hf).1,
    (triangle ha hf0 h1).1, (triangle hb he0 h2).1, (triangle hc hd0 h3).1⟩

/-- **Twice the leg·leg products** (`2ab`, `2ac`, `2bc`, `2af`, `2be`, `2cd`) are never squares
in a perfect cuboid (Fermat's right triangle theorem). -/
theorem IsPerfectCuboid.not_isSquare_two_mul_legs (h : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    ¬ IsSquare (2 * (a * b)) ∧ ¬ IsSquare (2 * (a * c)) ∧ ¬ IsSquare (2 * (b * c)) ∧
      ¬ IsSquare (2 * (a * f)) ∧ ¬ IsSquare (2 * (b * e)) ∧ ¬ IsSquare (2 * (c * d)) := by
  obtain ⟨ha, hb, hc, hd0, he0, hf0, -, h1, h2, h3⟩ := h.six_triangles hd he hf hg
  exact ⟨(triangle ha hb hd).2.2.2, (triangle ha hc he).2.2.2, (triangle hb hc hf).2.2.2,
    (triangle ha hf0 h1).2.2.2, (triangle hb he0 h2).2.2.2, (triangle hc hd0 h3).2.2.2⟩

/-- **Leg·hypotenuse products.** In a perfect cuboid none of the twelve products of a leg and the
hypotenuse of one of its right triangles is a square: `a d`, `b d`, `a e`, `c e`, `b f`, `c f`,
`a g`, `f g`, `b g`, `e g`, `c g`, `d g`. -/
theorem IsPerfectCuboid.not_isSquare_mul_leg_hyp (h : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    ¬ IsSquare (a * d) ∧ ¬ IsSquare (b * d) ∧ ¬ IsSquare (a * e) ∧ ¬ IsSquare (c * e) ∧
      ¬ IsSquare (b * f) ∧ ¬ IsSquare (c * f) ∧ ¬ IsSquare (a * g) ∧ ¬ IsSquare (f * g) ∧
      ¬ IsSquare (b * g) ∧ ¬ IsSquare (e * g) ∧ ¬ IsSquare (c * g) ∧ ¬ IsSquare (d * g) := by
  obtain ⟨ha, hb, hc, hd0, he0, hf0, -, h1, h2, h3⟩ := h.six_triangles hd he hf hg
  exact ⟨(triangle ha hb hd).2.1, (triangle ha hb hd).2.2.1,
    (triangle ha hc he).2.1, (triangle ha hc he).2.2.1,
    (triangle hb hc hf).2.1, (triangle hb hc hf).2.2.1,
    (triangle ha hf0 h1).2.1, (triangle ha hf0 h1).2.2.1,
    (triangle hb he0 h2).2.1, (triangle hb he0 h2).2.2.1,
    (triangle hc hd0 h3).2.1, (triangle hc hd0 h3).2.2.1⟩

/-- If the edge `a` of a perfect cuboid is a square, no other length is. -/
theorem IsPerfectCuboid.not_isSquare_of_isSquare_a (h : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (ha : IsSquare a) :
    ¬ IsSquare b ∧ ¬ IsSquare c ∧ ¬ IsSquare d ∧ ¬ IsSquare e ∧ ¬ IsSquare f ∧
      ¬ IsSquare g := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := h.not_isSquare_mul_legs hd he hf hg
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩ :=
    h.not_isSquare_mul_leg_hyp hd he hf hg
  exact ⟨not_isSquare_right p1 ha, not_isSquare_right p2 ha, not_isSquare_right q1 ha,
    not_isSquare_right q3 ha, not_isSquare_right p4 ha, not_isSquare_right q7 ha⟩

/-- If the edge `b` of a perfect cuboid is a square, no other length is. -/
theorem IsPerfectCuboid.not_isSquare_of_isSquare_b (h : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (hb : IsSquare b) :
    ¬ IsSquare a ∧ ¬ IsSquare c ∧ ¬ IsSquare d ∧ ¬ IsSquare e ∧ ¬ IsSquare f ∧
      ¬ IsSquare g := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := h.not_isSquare_mul_legs hd he hf hg
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩ :=
    h.not_isSquare_mul_leg_hyp hd he hf hg
  exact ⟨not_isSquare_left p1 hb, not_isSquare_right p3 hb, not_isSquare_right q2 hb,
    not_isSquare_right p5 hb, not_isSquare_right q5 hb, not_isSquare_right q9 hb⟩

/-- If the edge `c` of a perfect cuboid is a square, no other length is. -/
theorem IsPerfectCuboid.not_isSquare_of_isSquare_c (h : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (hc : IsSquare c) :
    ¬ IsSquare a ∧ ¬ IsSquare b ∧ ¬ IsSquare d ∧ ¬ IsSquare e ∧ ¬ IsSquare f ∧
      ¬ IsSquare g := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := h.not_isSquare_mul_legs hd he hf hg
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩ :=
    h.not_isSquare_mul_leg_hyp hd he hf hg
  exact ⟨not_isSquare_left p2 hc, not_isSquare_left p3 hc, not_isSquare_right p6 hc,
    not_isSquare_right q4 hc, not_isSquare_right q6 hc, not_isSquare_right q11 hc⟩

/-- If the face diagonal `d` of a perfect cuboid is a square, none of `a, b, c, g` is (the
other face diagonals `e, f` share no right triangle with `d`). -/
theorem IsPerfectCuboid.not_isSquare_of_isSquare_d (h : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (hd' : IsSquare d) :
    ¬ IsSquare a ∧ ¬ IsSquare b ∧ ¬ IsSquare c ∧ ¬ IsSquare g := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := h.not_isSquare_mul_legs hd he hf hg
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩ :=
    h.not_isSquare_mul_leg_hyp hd he hf hg
  exact ⟨not_isSquare_left q1 hd', not_isSquare_left q2 hd', not_isSquare_left p6 hd',
    not_isSquare_right q12 hd'⟩

/-- If the face diagonal `e` of a perfect cuboid is a square, none of `a, b, c, g` is. -/
theorem IsPerfectCuboid.not_isSquare_of_isSquare_e (h : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (he' : IsSquare e) :
    ¬ IsSquare a ∧ ¬ IsSquare b ∧ ¬ IsSquare c ∧ ¬ IsSquare g := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := h.not_isSquare_mul_legs hd he hf hg
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩ :=
    h.not_isSquare_mul_leg_hyp hd he hf hg
  exact ⟨not_isSquare_left q3 he', not_isSquare_left p5 he', not_isSquare_left q4 he',
    not_isSquare_right q10 he'⟩

/-- If the face diagonal `f` of a perfect cuboid is a square, none of `a, b, c, g` is. -/
theorem IsPerfectCuboid.not_isSquare_of_isSquare_f (h : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (hf' : IsSquare f) :
    ¬ IsSquare a ∧ ¬ IsSquare b ∧ ¬ IsSquare c ∧ ¬ IsSquare g := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := h.not_isSquare_mul_legs hd he hf hg
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩ :=
    h.not_isSquare_mul_leg_hyp hd he hf hg
  exact ⟨not_isSquare_left p4 hf', not_isSquare_left q5 hf', not_isSquare_left q6 hf',
    not_isSquare_right q8 hf'⟩

/-- If the space diagonal `g` of a perfect cuboid is a square, no other length is. -/
theorem IsPerfectCuboid.not_isSquare_of_isSquare_g (h : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (hg' : IsSquare g) :
    ¬ IsSquare a ∧ ¬ IsSquare b ∧ ¬ IsSquare c ∧ ¬ IsSquare d ∧ ¬ IsSquare e ∧
      ¬ IsSquare f := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩ :=
    h.not_isSquare_mul_leg_hyp hd he hf hg
  exact ⟨not_isSquare_left q7 hg', not_isSquare_left q9 hg', not_isSquare_left q11 hg',
    not_isSquare_left q12 hg', not_isSquare_left q10 hg', not_isSquare_left q8 hg'⟩

/-- **At most three of the seven lengths of a perfect cuboid are squares**, and if two are
squares, both are face diagonals (`not_isSquare_of_isSquare_a` … `_g`). -/
theorem IsPerfectCuboid.squares_le_three (h : IsPerfectCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    [a, b, c, d, e, f, g].countP (fun n ↦ decide (IsSquare n)) ≤ 3 := by
  by_cases ha : IsSquare a
  · obtain ⟨n1, n2, n3, n4, n5, n6⟩ := h.not_isSquare_of_isSquare_a hd he hf hg ha
    simp [ha, n1, n2, n3, n4, n5, n6]
  by_cases hb : IsSquare b
  · obtain ⟨n1, n2, n3, n4, n5, n6⟩ := h.not_isSquare_of_isSquare_b hd he hf hg hb
    simp [hb, n1, n2, n3, n4, n5, n6]
  by_cases hc : IsSquare c
  · obtain ⟨n1, n2, n3, n4, n5, n6⟩ := h.not_isSquare_of_isSquare_c hd he hf hg hc
    simp [hc, n1, n2, n3, n4, n5, n6]
  by_cases hg' : IsSquare g
  · obtain ⟨n1, n2, n3, n4, n5, n6⟩ := h.not_isSquare_of_isSquare_g hd he hf hg hg'
    simp [hg', n1, n2, n3, n4, n5, n6]
  simp only [List.countP_cons, List.countP_nil, ha, hb, hc, hg', decide_false]
  split_ifs <;> (try contradiction) <;> omega

/-- **`abcg/2` is not a square** in a perfect cuboid: `abcg ≠ 2 s²`. Indeed `abcg/2` is a
congruent number (`IsPerfectCuboid.isCongruent`) and no nonzero square is (Fermat). -/
theorem IsPerfectCuboid.abcg_ne_two_mul_sq (h : IsPerfectCuboid a b c)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (s : ℕ) : a * b * c * g ≠ 2 * s ^ 2 := by
  intro hs
  obtain ⟨-, -, g', -, hg', -, -, hcong, -⟩ := h.isCongruent
  obtain rfl : g' = g := Nat.pow_left_injective (n := 2) (by norm_num) (hg'.trans hg)
  have ha := h.pos_a; have hb := h.pos_b; have hc := h.pos_c
  have hg0 : 0 < g' := by
    rcases Nat.eq_zero_or_pos g' with h0 | h0
    · rw [h0] at hg'
      have : 0 < a ^ 2 := by positivity
      simp at hg'
      omega
    · exact h0
  have hs0 : (s : ℚ) ≠ 0 := by
    rintro h0
    have h0' : s = 0 := by exact_mod_cast h0
    subst h0'
    have : 0 < a * b * c * g' := by positivity
    omega
  have hq : ((a * b * c * g' : ℕ) : ℚ) = 2 * (s : ℚ) ^ 2 := by exact_mod_cast hs
  push_cast at hq
  rw [hq, mul_div_cancel_left₀ _ two_ne_zero] at hcong
  exact not_isCongruent_sq hs0 hcong

/-- **`abcg` is not a square** in a perfect cuboid: `abcg = s²` would make
`abcg/2 = (s/2)²·2` congruent, i.e. `2` congruent (`not_isCongruent_two`). -/
theorem IsPerfectCuboid.abcg_ne_sq (h : IsPerfectCuboid a b c)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (s : ℕ) : a * b * c * g ≠ s ^ 2 := by
  intro hs
  obtain ⟨-, -, g', -, hg', -, -, hcong, -⟩ := h.isCongruent
  obtain rfl : g' = g := Nat.pow_left_injective (n := 2) (by norm_num) (hg'.trans hg)
  have ha := h.pos_a; have hb := h.pos_b; have hc := h.pos_c
  have hg0 : 0 < g' := by
    rcases Nat.eq_zero_or_pos g' with h0 | h0
    · rw [h0] at hg'
      have : 0 < a ^ 2 := by positivity
      simp at hg'
      omega
    · exact h0
  have hs0 : (s : ℚ) / 2 ≠ 0 := by
    rintro h0
    have h0' : s = 0 := by
      have : (s : ℚ) = 0 := by linarith
      exact_mod_cast this
    subst h0'
    have : 0 < a * b * c * g' := by positivity
    simp at hs
    omega
  have hq : ((a * b * c * g' : ℕ) : ℚ) = (s : ℚ) ^ 2 := by exact_mod_cast hs
  push_cast at hq
  have : (a * b * c * g' : ℚ) / 2 = ((s : ℚ) / 2) ^ 2 * 2 := by rw [hq]; ring
  rw [this, isCongruent_mul_sq_iff hs0] at hcong
  exact not_isCongruent_two hcong

end PerfectCuboid
