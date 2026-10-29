module

public import LeanPlayground.PerfectCuboid.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.Real.Irrational

/-!
# The elliptic curve of a perfect cuboid has non-real `j`-invariant

Stoll–Testa (arXiv:1009.0388, §4) identify the cuboid surface over `ℚ(i)` with a quotient of
`X(8) × X(8)`. In those coordinates a cuboid `(a, b, c)` with space diagonal `g` gives the point
`ξ = (a + g)/(b − i c)` of `X(4) = ℙ¹`, and hence the Legendre curve `E_ξ` with full level-`4`
structure, whose `j`-invariant is the octahedral function

  `j(ξ) = 16 (ξ⁸ + 14 ξ⁴ + 1)³ / (ξ⁴ (ξ⁴ − 1)⁴)`.

`j(ξ)` is real exactly when `j(ξ) = j(ξ̄)`, i.e. when `ξ̄ = γ(ξ)` for one of the `24` octahedral
Möbius maps `γ`. Writing `u = ξ`, `v = ξ̄` (`octJ_identity`):

  `N(u) D(v) − N(v) D(u) = (u − v) · S(u + v, u v)`,

where `S(s₁, s₂)` is an explicit product of twelve factors (`octS`). For a cuboid,
`s₁ = 2 x`, `s₂ = x² + y²` with `x = (a+g) b/(b² + c²)` and `y = (a+g) c/(b² + c²)`, and each factor
vanishes only on a degenerate locus: `c = 0` (from `u − v`), `b = 0`, `a = 0`, `a = b`, `b = c`,
`a = c`, or nowhere at all. Two equal edges are impossible because `√2` is irrational.

* `IsPerfectCuboid.octJ_im_ne_zero`: for a perfect cuboid, `j(ξ)` is not real; in particular
  `j(ξ) ∉ ℚ`, so the curve `E_ξ` is not a base change from `ℚ` (nor from any real field).
  Degenerate cuboids (`c = 0`) have `ξ ∈ ℚ` and so `j(ξ) ∈ ℚ`.

See `fable-new-frameworks-round6.md` (round 6, Brief 4).
-/

@[expose] public section

namespace PerfectCuboid

open Complex ComplexConjugate

/-- The octahedral `j`-function: `j` of the Legendre curve with `λ = ((t² + 1)/(2t))²`. -/
noncomputable def octJ (t : ℂ) : ℂ :=
  16 * (t ^ 8 + 14 * t ^ 4 + 1) ^ 3 / (t ^ 4 * (t ^ 4 - 1) ^ 4)

/-- One of the two quartic factors of `octS` (four octahedral maps with no real fixed locus). -/
def octQ₁ {R : Type*} [CommRing R] (s₁ s₂ : R) : R :=
  s₁ ^ 4 - 2 * s₁ ^ 3 * s₂ + 2 * s₁ ^ 3 + 2 * s₁ ^ 2 * s₂ ^ 2 - 8 * s₁ ^ 2 * s₂ + 2 * s₁ ^ 2 -
    2 * s₁ * s₂ ^ 3 + 6 * s₁ * s₂ ^ 2 - 6 * s₁ * s₂ + 2 * s₁ + s₂ ^ 4 + 14 * s₂ ^ 2 + 1

/-- The other quartic factor of `octS`: `octQ₂ s₁ s₂ = octQ₁ (-s₁) s₂`. -/
def octQ₂ {R : Type*} [CommRing R] (s₁ s₂ : R) : R :=
  s₁ ^ 4 + 2 * s₁ ^ 3 * s₂ - 2 * s₁ ^ 3 + 2 * s₁ ^ 2 * s₂ ^ 2 - 8 * s₁ ^ 2 * s₂ + 2 * s₁ ^ 2 +
    2 * s₁ * s₂ ^ 3 - 6 * s₁ * s₂ ^ 2 + 6 * s₁ * s₂ - 2 * s₁ + s₂ ^ 4 + 14 * s₂ ^ 2 + 1

/-- The symmetric factor of `j(u) − j(v)`, as a polynomial in `s₁ = u + v` and `s₂ = u v`. -/
def octS {R : Type*} [CommRing R] (s₁ s₂ : R) : R :=
  (s₂ - 1) * (s₂ ^ 2 + 1) * (s₂ + 1) * s₁ * (s₁ - s₂ + 1) * (s₁ + s₂ - 1) * (s₁ ^ 2 - 2 * s₂) *
    (s₁ ^ 2 - s₂ ^ 2 - 6 * s₂ - 1) * (s₁ ^ 2 + s₂ ^ 2 - 6 * s₂ + 1) *
    (s₁ ^ 2 + s₂ ^ 2 + 2 * s₂ + 1) *
    octQ₁ s₁ s₂ * octQ₂ s₁ s₂

/-- `N(u) D(v) − N(v) D(u) = (u − v) S(u + v, u v)` with `N(t) = (t⁸ + 14t⁴ + 1)³` and
`D(t) = t⁴ (t⁴ − 1)⁴`. -/
theorem octJ_identity {R : Type*} [CommRing R] (u v : R) :
    (u ^ 8 + 14 * u ^ 4 + 1) ^ 3 * (v ^ 4 * (v ^ 4 - 1) ^ 4) -
        (v ^ 8 + 14 * v ^ 4 + 1) ^ 3 * (u ^ 4 * (u ^ 4 - 1) ^ 4) =
      (u - v) * octS (u + v) (u * v) := by
  unfold octS octQ₁ octQ₂; ring

theorem octS_ofReal (s₁ s₂ : ℝ) : ((octS s₁ s₂ : ℝ) : ℂ) = octS (s₁ : ℂ) (s₂ : ℂ) := by
  simp only [octS, octQ₁, octQ₂]; push_cast; ring

theorem octJ_conj (t : ℂ) : octJ (conj t) = conj (octJ t) := by
  simp [octJ, map_div₀, map_ofNat]

/-- If `j(x + y i)` is real with `y ≠ 0`, then `S(2x, x² + y²) = 0`. -/
theorem octS_eq_zero_of_im {x y : ℝ} (hy : y ≠ 0)
    (hD : ((x : ℂ) + y * I) ^ 4 * (((x : ℂ) + y * I) ^ 4 - 1) ^ 4 ≠ 0)
    (h : (octJ ((x : ℂ) + y * I)).im = 0) : octS (2 * x) (x ^ 2 + y ^ 2) = 0 := by
  set z : ℂ := (x : ℂ) + y * I with hz
  have hc : conj z = (x : ℂ) - y * I := by simp [hz, sub_eq_add_neg]
  have h1 : octJ z = octJ (conj z) := by rw [octJ_conj]; exact (Complex.conj_eq_iff_im.2 h).symm
  have hD' : conj z ^ 4 * (conj z ^ 4 - 1) ^ 4 ≠ 0 := by
    intro h0; apply hD
    have := congrArg conj h0
    simpa using this
  unfold octJ at h1
  rw [div_eq_div_iff hD hD'] at h1
  have key := octJ_identity z (conj z)
  have hsum : z + conj z = ((2 * x : ℝ) : ℂ) := by rw [hc, hz]; push_cast; ring
  have hprod : z * conj z = ((x ^ 2 + y ^ 2 : ℝ) : ℂ) := by
    rw [hc, hz]; push_cast; ring_nf; rw [I_sq]; ring
  have hdiff : z - conj z ≠ 0 := by
    rw [hc, hz]; ring_nf
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hy) I_ne_zero) two_ne_zero
  rw [hsum, hprod, ← octS_ofReal] at key
  have : (z - conj z) * ((octS (2 * x) (x ^ 2 + y ^ 2) : ℝ) : ℂ) = 0 := by
    rw [← key]; linear_combination h1 / 16
  exact_mod_cast (mul_eq_zero.1 this).resolve_left hdiff

theorem octQ₁_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < octQ₁ (2 * x) (x ^ 2 + y ^ 2) := by
  have e : octQ₁ (2 * x) (x ^ 2 + y ^ 2) = ((x ^ 2 + y ^ 2 - x - y) ^ 2 + (x + y + 1) ^ 2) *
      ((x ^ 2 + y ^ 2 - x + y) ^ 2 + (y - x - 1) ^ 2) := by unfold octQ₁; ring
  rw [e]
  refine mul_pos (by positivity) ?_
  by_contra hB
  have h1 : y - x - 1 = 0 := by nlinarith [sq_nonneg (x ^ 2 + y ^ 2 - x + y)]
  have h2 : x ^ 2 + y ^ 2 - x + y = 0 := by nlinarith [sq_nonneg (y - x - 1)]
  obtain rfl : y = x + 1 := by linarith
  nlinarith

theorem octQ₂_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < octQ₂ (2 * x) (x ^ 2 + y ^ 2) := by
  have e : octQ₂ (2 * x) (x ^ 2 + y ^ 2) = ((x ^ 2 + y ^ 2 + x - y) ^ 2 + (y - x + 1) ^ 2) *
      ((x ^ 2 + y ^ 2 + x + y) ^ 2 + (x + y - 1) ^ 2) := by unfold octQ₂; ring
  rw [e]
  refine mul_pos ?_ (by positivity)
  by_contra hA
  have h1 : y - x + 1 = 0 := by nlinarith [sq_nonneg (x ^ 2 + y ^ 2 + x - y)]
  have h2 : x ^ 2 + y ^ 2 + x - y = 0 := by nlinarith [sq_nonneg (y - x + 1)]
  obtain rfl : x = y + 1 := by linarith
  nlinarith

/-- `d² = 2a²` has no solution with `a > 0`. -/
theorem sq_ne_two_mul_sq {d a : ℕ} (ha : 0 < a) : d ^ 2 ≠ 2 * a ^ 2 := by
  intro h
  apply irrational_sqrt_two.ne_rat ((d : ℚ) / a)
  have h' : ((d : ℝ) / a) ^ 2 = 2 := by
    rw [div_pow, div_eq_iff (by positivity)]; exact_mod_cast h
  push_cast
  rw [← h', Real.sqrt_sq (by positivity)]

/-- **The `j`-invariant of a perfect cuboid is not real.** With `ξ = (a + g)/(b − i c)`, the
octahedral `j(ξ)` (the `j`-invariant of the Legendre curve attached to the cuboid by the
Stoll–Testa isomorphism) has nonzero imaginary part.

Scope: the proof uses only positivity, `d, e, f ∈ ℕ` (to rule out `a = b`, `b = c`, `a = c` by
irrationality of `√2`) and `g` as the real root, so it holds for every box with distinct positive
edges, not only for perfect cuboids. -/
theorem IsPerfectCuboid.octJ_im_ne_zero {a b c : ℕ} (h : IsPerfectCuboid a b c) {d e f g : ℕ}
    (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    (octJ (((a : ℂ) + g) / ((b : ℂ) - c * I))).im ≠ 0 := by
  have ha : (0 : ℝ) < a := by exact_mod_cast h.pos_a
  have hb : (0 : ℝ) < b := by exact_mod_cast h.pos_b
  have hc : (0 : ℝ) < c := by exact_mod_cast h.pos_c
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hgR : (g : ℝ) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by exact_mod_cast hg
  have hn : (0 : ℝ) < b ^ 2 + c ^ 2 := by positivity
  set x : ℝ := (a + g) * b / (b ^ 2 + c ^ 2) with hxdef
  set y : ℝ := (a + g) * c / (b ^ 2 + c ^ 2) with hydef
  have hx : 0 < x := by positivity
  have hy : 0 < y := by positivity
  have hxn : x * (b ^ 2 + c ^ 2) = (a + g) * b := by rw [hxdef]; field_simp
  have hyn : y * (b ^ 2 + c ^ 2) = (a + g) * c := by rw [hydef]; field_simp
  have hσn : (x ^ 2 + y ^ 2) * (b ^ 2 + c ^ 2) = ((a : ℝ) + g) ^ 2 := by
    rw [hxdef, hydef]; field_simp
  have hre : x * b + y * c = a + g := by rw [hxdef, hydef]; field_simp
  have him : y * b - x * c = 0 := by rw [hxdef, hydef]; field_simp; ring
  clear_value x y
  have hξ : ((a : ℂ) + g) / ((b : ℂ) - c * I) = (x : ℂ) + y * I := by
    have hq : (b : ℂ) - c * I ≠ 0 := by
      intro h0
      have : (b : ℝ) = 0 := by simpa using congrArg Complex.re h0
      linarith
    rw [div_eq_iff hq]
    apply Complex.ext <;> simp <;> linarith
  have hp : (0 : ℝ) < a + g := by positivity
  -- `x² + y² = (a+g)²/(b²+c²) > 1`
  have hσ1 : x ^ 2 + y ^ 2 ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hσn
    have h2 : ((a : ℝ) + g) ^ 2 - (b ^ 2 + c ^ 2) = 2 * a * (a + g) := by linear_combination hgR
    have : (0 : ℝ) < 2 * a * (a + g) := by positivity
    linarith
  rw [hξ]
  intro h0
  have hD : ((x : ℂ) + y * I) ^ 4 * (((x : ℂ) + y * I) ^ 4 - 1) ^ 4 ≠ 0 := by
    have hns : Complex.normSq ((x : ℂ) + y * I) = x ^ 2 + y ^ 2 := by
      rw [Complex.normSq_add_mul_I]
    refine mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
    · intro h1
      have := congrArg Complex.normSq h1
      rw [hns, map_zero] at this
      have : 0 < x ^ 2 + y ^ 2 := by positivity
      linarith
    · intro h1
      rw [sub_eq_zero] at h1
      have := congrArg Complex.normSq h1
      rw [map_pow, hns, map_one] at this
      exact hσ1 ((pow_eq_one_iff_of_nonneg (by positivity) four_ne_zero).1 this)
  have hS := octS_eq_zero_of_im hy.ne' hD h0
  simp only [octS, mul_eq_zero] at hS
  rcases hS with ((((((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11) | h12
  · exact hσ1 (sub_eq_zero.1 h1)
  · have : 0 < (x ^ 2 + y ^ 2) ^ 2 + 1 := by positivity
    linarith
  · have : 0 < x ^ 2 + y ^ 2 + 1 := by positivity
    linarith
  · rcases h4 with h4 | h4
    · norm_num at h4
    · linarith
  · -- `a = b`
    have hE : ((a : ℝ) - b) * (a + g) = 0 := by
      linear_combination (-1 / 2 : ℝ) * (b ^ 2 + c ^ 2) * h5 + hxn - (1 / 2 : ℝ) * hσn -
        (1 / 2 : ℝ) * hgR
    have hab : a = b := by
      have : (a : ℝ) = b := by
        rcases mul_eq_zero.1 hE with hE | hE <;> linarith
      exact_mod_cast this
    exact sq_ne_two_mul_sq h.pos_a (d := d) (by rw [hd, ← hab]; ring)
  · have hE : ((a : ℝ) + b) * (a + g) = 0 := by
      linear_combination (1 / 2 : ℝ) * (b ^ 2 + c ^ 2) * h6 - hxn - (1 / 2 : ℝ) * hσn -
        (1 / 2 : ℝ) * hgR
    have : (0 : ℝ) < (a + b) * (a + g) := by positivity
    linarith
  · -- `b = c`
    have hxy : x = y := by
      have hE : (x - y) * (x + y) = 0 := by linear_combination h7 / 2
      rcases mul_eq_zero.1 hE with hE | hE <;> linarith
    have hE : ((a : ℝ) + g) * (b - c) = 0 := by
      linear_combination -hxn + hyn + (b ^ 2 + c ^ 2) * hxy
    have hbc : b = c := by
      have : (b : ℝ) = c := by
        rcases mul_eq_zero.1 hE with hE | hE <;> linarith
      exact_mod_cast this
    exact sq_ne_two_mul_sq h.pos_b (d := f) (by rw [hf, ← hbc]; ring)
  · have : (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * y ^ 2 = 0 := by linear_combination -h8
    have : 0 < (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * y ^ 2 := by positivity
    linarith
  · -- `a = c`
    have hE : 4 * ((a : ℝ) + g) ^ 2 * ((a - c) * (a + c)) = 0 := by
      linear_combination (b ^ 2 + c ^ 2) ^ 2 * h9 -
        4 * (x * (b ^ 2 + c ^ 2) + (a + g) * b) * hxn -
        ((x ^ 2 + y ^ 2) * (b ^ 2 + c ^ 2) + (a + g) ^ 2 - 6 * (b ^ 2 + c ^ 2)) * hσn -
        (3 * a ^ 2 + 4 * a * g - b ^ 2 - c ^ 2 + g ^ 2) * hgR
    have hac : a = c := by
      have : (a : ℝ) = c := by
        have h4 : (0 : ℝ) < 4 * (a + g) ^ 2 := by positivity
        rcases mul_eq_zero.1 hE with hE | hE
        · linarith
        · rcases mul_eq_zero.1 hE with hE | hE <;> linarith
      exact_mod_cast this
    exact sq_ne_two_mul_sq h.pos_a (d := e) (by rw [he, ← hac]; ring)
  · have : 0 < (2 * x) ^ 2 + (x ^ 2 + y ^ 2) ^ 2 + 2 * (x ^ 2 + y ^ 2) + 1 := by positivity
    linarith
  · exact (octQ₁_pos hx hy).ne' h11
  · exact (octQ₂_pos hx hy).ne' h12

end PerfectCuboid
