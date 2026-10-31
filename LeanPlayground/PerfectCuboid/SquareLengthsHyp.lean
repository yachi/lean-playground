module

public import LeanPlayground.PerfectCuboid.SquareLengths

/-!
# Twice a leg times the hypotenuse is never a square

Complement to `SquareLengths.lean`. For a Pythagorean triangle `x² + y² = z²` with positive legs,
`2 x z` (and by symmetry `2 y z`) is never a perfect square.

*Proof.* If `2 x z = w²` then `(z² + x²)² − (z² − x²)² = 4x²z² = w⁴` and `z² − x² = y²`, so
`y⁴ + w⁴ = (x² + z²)²` with `y, w ≠ 0`, against Fermat's quartic theorem (`not_fermat_42`).

The two "Fermat quartic" routes for products of lengths of one right triangle are therefore
* `z⁴ − x⁴ = (y z)²` (used in `SquareLengths.not_isSquare_mul_leg_hyp`, via `fermat_sub`), and
* `y⁴ + (2 x z)² = (x² + z²)²` (used here, via `not_fermat_42`).

Together with `SquareLengths` this settles `u v` and `2 u v` for every pair `{u, v}` of lengths of
one right triangle. The products `d e`, `d f`, `e f` of two face diagonals of a cuboid do not lie
in a common triangle and are not reachable by this method.

For a perfect cuboid: `IsPerfectCuboid.two_mul_leg_hyp_ne_sq` (all twelve `2·leg·hyp` products
of its six right triangles are non-squares). The statements are one-triangle statements, so they
hold verbatim for Euler bricks and face cuboids wherever the triangle exists, and the degenerate
box `(a, b, 0)` is excluded only by the positivity of the legs.
-/

@[expose] public section

namespace PerfectCuboid.SquareLengthsHyp

open SquareLengths

/-- **`2·leg·hyp` is never a square:** `2 x z = w²` gives `y⁴ + w⁴ = (x² + z²)²`. -/
theorem not_isSquare_two_mul_leg_hyp {x y z : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : ¬ IsSquare (2 * x * z) := by
  rintro ⟨w, hw⟩
  have hz := hyp_pos hx h
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
    omega
  have h' : (x : ℤ) ^ 2 + y ^ 2 = z ^ 2 := by exact_mod_cast h
  have hw' : 2 * (x : ℤ) * z = w * w := by exact_mod_cast hw
  exact not_fermat_42 (a := (y : ℤ)) (b := (w : ℤ)) (c := (x : ℤ) ^ 2 + z ^ 2) (by positivity)
    (by exact_mod_cast hw0)
    (by linear_combination ((y : ℤ) ^ 2 + z ^ 2 - x ^ 2) * h' - (w * w + 2 * x * z) * hw')

/-- The other leg: `2 y z` is never a square. -/
theorem not_isSquare_two_mul_leg_hyp' {x y z : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : ¬ IsSquare (2 * y * z) :=
  not_isSquare_two_mul_leg_hyp hy hx (by rw [← h]; ring)

end PerfectCuboid.SquareLengthsHyp

namespace PerfectCuboid

open SquareLengthsHyp

/-- **All twelve `2·leg·hyp` products of a perfect cuboid are non-squares:** `2ad`, `2bd`,
`2ae`, `2ce`, `2bf`, `2cf`, `2ag`, `2fg`, `2bg`, `2eg`, `2cg`, `2dg`. -/
theorem IsPerfectCuboid.two_mul_leg_hyp_ne_sq {a b c : ℕ} (h : IsPerfectCuboid a b c)
    {d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    ¬ IsSquare (2 * a * d) ∧ ¬ IsSquare (2 * b * d) ∧ ¬ IsSquare (2 * a * e) ∧
      ¬ IsSquare (2 * c * e) ∧ ¬ IsSquare (2 * b * f) ∧ ¬ IsSquare (2 * c * f) ∧
      ¬ IsSquare (2 * a * g) ∧ ¬ IsSquare (2 * f * g) ∧ ¬ IsSquare (2 * b * g) ∧
      ¬ IsSquare (2 * e * g) ∧ ¬ IsSquare (2 * c * g) ∧ ¬ IsSquare (2 * d * g) := by
  obtain ⟨ha, hb, hc, hd0, he0, hf0, -, h1, h2, h3⟩ := h.six_triangles hd he hf hg
  exact ⟨not_isSquare_two_mul_leg_hyp ha hb hd, not_isSquare_two_mul_leg_hyp' ha hb hd,
    not_isSquare_two_mul_leg_hyp ha hc he, not_isSquare_two_mul_leg_hyp' ha hc he,
    not_isSquare_two_mul_leg_hyp hb hc hf, not_isSquare_two_mul_leg_hyp' hb hc hf,
    not_isSquare_two_mul_leg_hyp ha hf0 h1, not_isSquare_two_mul_leg_hyp' ha hf0 h1,
    not_isSquare_two_mul_leg_hyp hb he0 h2, not_isSquare_two_mul_leg_hyp' hb he0 h2,
    not_isSquare_two_mul_leg_hyp hc hd0 h3, not_isSquare_two_mul_leg_hyp' hc hd0 h3⟩

end PerfectCuboid
