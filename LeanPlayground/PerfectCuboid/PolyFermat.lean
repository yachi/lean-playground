module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolyCharP

/-!
# Fermat quartics over `K[X]` in every characteristic `≠ 2`, and their cuboid consequences

Let `K` be any field with `2 ≠ 0`.

* **Fermat quartics** (`quartic_coprime_gen`, `quartic_coprime`, `quartic_add_coprime`,
  `quartic_sub_coprime`): if `ε x⁴ + κ y⁴ = μ z²` with `ε κ μ ≠ 0`, `x, y ∈ K[X]` nonzero and
  coprime, then `x` and `y` are constants. This is the case `(p, q, r) = (4, 4, 2)` of Mathlib's
  polynomial Fermat–Catalan theorem `Polynomial.flt_catalan` (Mason–Stothers plus Frobenius descent
  `expand`/`contract` in characteristic `p`), whose hypothesis `qr + rp + pq ≤ pqr` holds with
  equality (`8 + 8 + 16 = 32`); the only extra case is `z = 0`.
* **Without coprimality** (`quartic_proportional_gen`, `quartic_proportional`,
  `quartic_add_proportional`, `quartic_sub_proportional`, `quartic_two_sq`): `x` and `y` are
  constant multiples of one polynomial (`gcd x y`).
* **Right triangles** `x² + y² = z²` (`IsPropTriangle x y z`: all three sides are constant multiples
  of one polynomial). Each of the following forces a proportional triangle, in every
  characteristic `≠ 2` (the `K[X]`-analogues of `SquareLengths`, `SquareLengthsHyp`, `Adjacency`):
  - `x z = κ s²` (leg · hypotenuse, `isPropTriangle_of_leg_hyp_sq`), via
    `y⁴ + 4κ² s⁴ = (z² + x²)²`;
  - `x y = κ s²` (leg · leg, `isPropTriangle_of_leg_leg_sq`), via `z⁴ − 4κ² s⁴ = (x² − y²)²`;
  - `x = κ₁ p²`, `z = κ₂ q²` (`isPropTriangle_of_two_sq`) or `x = κ₁ p²`, `y = κ₂ q²`
    (`isPropTriangle_of_two_sq_legs`);
  - `z² + x² = w²` (`isPropTriangle_of_hyp_sq_add_leg_sq`), via `z⁴ − x⁴ = (y w)²`.
* **Cuboids** (`PolyCharP.IsCuboid`): if `d² + e²` is a square then the edge `a` and the space
  diagonal `g` are proportional (`IsCuboid.proportional_of_isSquare_face_sum`); a face with two
  lengths that are constants times squares, or with `edge · edge` or `edge · face diagonal` a
  constant times a square, is a proportional triangle (`IsCuboid.not_face_two_sq`,
  `IsCuboid.not_face_two_sq'`, `IsCuboid.not_edge_mul_faceDiag_sq`,
  `IsCuboid.not_edge_mul_edge_sq`).
* **Consistency with the Frobenius cuboid** (`frobenius_face_sum_not_isSquare`): on the Frobenius
  cuboid in characteristic `p` (`deg a = p`, `deg g = p + 1`) the sum `d² + e²` is never a square.

Everything holds for proportional cuboids `(α q, β q, γ q)` (which are `K`-points of the cuboid
surface, e.g. integer perfect cuboids if any exist), so the conclusions are proportionality
statements, never non-existence.
-/

@[expose] public section

open Polynomial

namespace PerfectCuboid.PolyFermat

variable {K : Type*} [Field K]

/-! ## Fermat quartics -/

theorem four_ne_zero_of_two (h2 : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have : (4 : K) = 2 * 2 := by norm_num
  rw [this]; exact mul_ne_zero h2 h2

/-- **Core (general coefficients).** `ε x⁴ + κ y⁴ = μ z²` with `x, y` nonzero and coprime forces
`x, y` constant. Any field with `2 ≠ 0`; the case `z ≠ 0` is Mathlib's `Polynomial.flt_catalan`
with exponents `(4, 4, 2)`. -/
theorem quartic_coprime_gen (h2 : (2 : K) ≠ 0) {ε κ μ : K} (hε : ε ≠ 0) (hκ : κ ≠ 0)
    (hμ : μ ≠ 0) {x y z : K[X]} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : IsCoprime x y)
    (h : C ε * x ^ 4 + C κ * y ^ 4 = C μ * z ^ 2) :
    x.natDegree = 0 ∧ y.natDegree = 0 := by
  by_cases hz : z = 0
  · subst hz
    have h' : C ε * x ^ 4 + C κ * y ^ 4 = 0 := by simpa using h
    have hk1 : C κ⁻¹ * C κ = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hκ, C_1]
    have he1 : C ε⁻¹ * C ε = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hε, C_1]
    have hy4 : y ^ 4 = (-(C κ⁻¹ * C ε)) * x ^ 4 := by
      linear_combination (C κ⁻¹) * h' - y ^ 4 * hk1
    have hx4 : x ^ 4 = (-(C ε⁻¹ * C κ)) * y ^ 4 := by
      linear_combination (C ε⁻¹) * h' - x ^ 4 * he1
    refine ⟨natDegree_eq_zero_of_isUnit
      ((hxy.pow_right (n := 4)).isUnit_of_dvd' dvd_rfl ?_),
      natDegree_eq_zero_of_isUnit ((hxy.pow_left (m := 4)).isUnit_of_dvd' ?_ dvd_rfl)⟩
    · rw [hy4]; exact Dvd.dvd.mul_left (dvd_pow_self x (by norm_num)) _
    · rw [hx4]; exact Dvd.dvd.mul_left (dvd_pow_self y (by norm_num)) _
  · have heq : C ε * x ^ 4 + C κ * y ^ 4 + C (-μ) * z ^ 2 = 0 := by
      rw [C_neg]; linear_combination h
    have h4 : ((4 : ℕ) : K) ≠ 0 := by exact_mod_cast four_ne_zero_of_two h2
    have h2' : ((2 : ℕ) : K) ≠ 0 := by exact_mod_cast h2
    obtain ⟨h1, h2'', -⟩ := Polynomial.flt_catalan (p := 4) (q := 4) (r := 2) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h4 h4 h2' hx hy hz hxy hε hκ
      (neg_ne_zero.mpr hμ) heq
    exact ⟨h1, h2''⟩

/-- **Core.** `x⁴ + κ y⁴ = μ z²` with `x, y` nonzero and coprime forces `x, y` constant
(any field with `2 ≠ 0`). -/
theorem quartic_coprime (h2 : (2 : K) ≠ 0) {κ μ : K} (hκ : κ ≠ 0) (hμ : μ ≠ 0) {x y z : K[X]}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : IsCoprime x y) (h : x ^ 4 + C κ * y ^ 4 = C μ * z ^ 2) :
    x.natDegree = 0 ∧ y.natDegree = 0 :=
  quartic_coprime_gen h2 one_ne_zero hκ hμ hx hy hxy (by rw [C_1, one_mul]; exact h)

theorem quartic_add_coprime (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : IsCoprime x y) (h : x ^ 4 + y ^ 4 = z ^ 2) : x.natDegree = 0 ∧ y.natDegree = 0 :=
  quartic_coprime h2 one_ne_zero one_ne_zero hx hy hxy (by rw [C_1, one_mul, one_mul]; exact h)

theorem quartic_sub_coprime (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : IsCoprime x y) (h : x ^ 4 - y ^ 4 = z ^ 2) : x.natDegree = 0 ∧ y.natDegree = 0 :=
  quartic_coprime h2 (neg_ne_zero.mpr one_ne_zero) one_ne_zero hx hy hxy (z := z)
    (by rw [C_neg, C_1]; linear_combination h)

/-- **Without coprimality (general coefficients):** `ε x⁴ + κ y⁴ = μ z²` with `x, y ≠ 0` forces
`x, y` to be constant multiples of one polynomial. -/
theorem quartic_proportional_gen (h2 : (2 : K) ≠ 0) {ε κ μ : K} (hε : ε ≠ 0) (hκ : κ ≠ 0)
    (hμ : μ ≠ 0) {x y z : K[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : C ε * x ^ 4 + C κ * y ^ 4 = C μ * z ^ 2) :
    ∃ (q : K[X]) (α β : K), x = C α * q ∧ y = C β * q := by
  classical
  obtain ⟨x', y', hx', hy', hu⟩ := extract_gcd x y
  set d := gcd x y
  have hd : d ≠ 0 := by intro h0; rw [h0, zero_mul] at hx'; exact hx hx'
  have hx0 : x' ≠ 0 := by rintro rfl; rw [mul_zero] at hx'; exact hx hx'
  have hy0 : y' ≠ 0 := by rintro rfl; rw [mul_zero] at hy'; exact hy hy'
  have hcop : IsCoprime x' y' := (gcd_isUnit_iff x' y').mp hu
  have hE : C μ * z ^ 2 = (d ^ 2) ^ 2 * (C ε * x' ^ 4 + C κ * y' ^ 4) := by
    rw [← h, hx', hy']; ring
  have hdvd : (d ^ 2) ^ 2 ∣ z ^ 2 := by
    have h1 : (d ^ 2) ^ 2 ∣ C μ * z ^ 2 := ⟨_, hE⟩
    have hμ1 : C μ⁻¹ * C μ = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hμ, C_1]
    have : z ^ 2 = C μ⁻¹ * (C μ * z ^ 2) := by rw [← mul_assoc, hμ1, one_mul]
    rw [this]; exact Dvd.dvd.mul_left h1 _
  obtain ⟨z', hz'⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp hdvd
  have heq : C ε * x' ^ 4 + C κ * y' ^ 4 = C μ * z' ^ 2 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero 2 hd)) ?_
    rw [← hE, hz']; ring
  obtain ⟨h1, h2'⟩ := quartic_coprime_gen h2 hε hκ hμ hx0 hy0 hcop heq
  obtain ⟨α, hα⟩ := natDegree_eq_zero.mp h1
  obtain ⟨β, hβ⟩ := natDegree_eq_zero.mp h2'
  exact ⟨d, α, β, by rw [hx', ← hα, mul_comm], by rw [hy', ← hβ, mul_comm]⟩

/-- **Without coprimality:** `x⁴ + κ y⁴ = μ z²` with `x, y ≠ 0` forces `x, y` to be constant
multiples of one polynomial. -/
theorem quartic_proportional (h2 : (2 : K) ≠ 0) {κ μ : K} (hκ : κ ≠ 0) (hμ : μ ≠ 0)
    {x y z : K[X]} (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ 4 + C κ * y ^ 4 = C μ * z ^ 2) :
    ∃ (q : K[X]) (α β : K), x = C α * q ∧ y = C β * q :=
  quartic_proportional_gen h2 one_ne_zero hκ hμ hx hy (by rw [C_1, one_mul]; exact h)

theorem quartic_add_proportional (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 4 + y ^ 4 = z ^ 2) : ∃ (q : K[X]) (α β : K), x = C α * q ∧ y = C β * q :=
  quartic_proportional h2 one_ne_zero one_ne_zero hx hy (by rw [C_1, one_mul, one_mul]; exact h)

theorem quartic_sub_proportional (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 4 - y ^ 4 = z ^ 2) : ∃ (q : K[X]) (α β : K), x = C α * q ∧ y = C β * q :=
  quartic_proportional h2 (neg_ne_zero.mpr one_ne_zero) one_ne_zero hx hy (z := z)
    (by rw [C_neg, C_1]; linear_combination h)

/-- `x⁴ + y⁴ = 2 z²` (the `K[X]`-analogue of the repo's `fermat_two_sq`): `x, y` proportional.
(Directly the case `κ = 1`, `μ = 2` of `quartic_proportional`.) -/
theorem quartic_two_sq (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 4 + y ^ 4 = C 2 * z ^ 2) : ∃ (q : K[X]) (α β : K), x = C α * q ∧ y = C β * q :=
  quartic_proportional h2 one_ne_zero h2 hx hy (by rw [C_1, one_mul]; exact h)

/-! ## Square roots of constant multiples -/

/-- If `P² = c Q²` with `Q ≠ 0`, then `P` is a constant multiple of `Q`. -/
theorem eq_C_mul_of_sq_eq {P Q : K[X]} {c : K} (hQ : Q ≠ 0) (h : P ^ 2 = C c * Q ^ 2) :
    ∃ ν : K, P = C ν * Q := by
  have hdvd : Q ^ 2 ∣ P ^ 2 := ⟨C c, by rw [h, mul_comm]⟩
  obtain ⟨R, hR⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp hdvd
  have hR2 : R ^ 2 = C c := by
    have : Q ^ 2 * R ^ 2 = Q ^ 2 * C c := by rw [← mul_pow, ← hR, h, mul_comm]
    exact mul_left_cancel₀ (pow_ne_zero 2 hQ) this
  have hdeg : R.natDegree = 0 := by
    have := congrArg natDegree hR2
    rw [natDegree_pow, natDegree_C] at this
    omega
  obtain ⟨r, hr⟩ := natDegree_eq_zero.mp hdeg
  exact ⟨r, by rw [hR, ← hr, mul_comm]⟩

theorem C_two_inv_mul (h2 : (2 : K) ≠ 0) : C (2⁻¹ : K) * 2 = (1 : K[X]) := by
  rw [← C_ofNat, ← C_mul, inv_mul_cancel₀ h2, C_1]

/-- Solving `P + Q = u r`, `P − Q = v r` for `P` and `Q` (needs `2 ≠ 0`). -/
theorem half_combo (h2 : (2 : K) ≠ 0) {P Q r : K[X]} {u v : K} (h1 : P + Q = C u * r)
    (h2' : P - Q = C v * r) : P = C (2⁻¹ * (u + v)) * r ∧ Q = C (2⁻¹ * (u - v)) * r := by
  have h := C_two_inv_mul h2
  rw [C_mul, C_add, C_mul, C_sub]
  constructor
  · linear_combination C 2⁻¹ * (h1 + h2') - P * h
  · linear_combination C 2⁻¹ * (h1 - h2') - Q * h

/-! ## Right triangles -/

/-- A *proportional triangle*: all three sides are constant multiples of one polynomial. -/
def IsPropTriangle (x y z : K[X]) : Prop :=
  ∃ (q : K[X]) (α β γ : K), x = C α * q ∧ y = C β * q ∧ z = C γ * q

theorem isPropTriangle_of_sq {x y z q : K[X]} (hq : q ≠ 0) {a b c : K}
    (hx : x ^ 2 = C a * q ^ 2) (hy : y ^ 2 = C b * q ^ 2) (hz : z ^ 2 = C c * q ^ 2) :
    IsPropTriangle x y z := by
  obtain ⟨α, rfl⟩ := eq_C_mul_of_sq_eq hq hx
  obtain ⟨β, rfl⟩ := eq_C_mul_of_sq_eq hq hy
  obtain ⟨γ, rfl⟩ := eq_C_mul_of_sq_eq hq hz
  exact ⟨q, α, β, γ, rfl, rfl, rfl⟩

/-- A degenerate triangle `x² + y² = 0` (only possible if `−1` is a square) is proportional. -/
theorem isPropTriangle_of_hyp_eq_zero {x y : K[X]} (hx : x ≠ 0) (h : x ^ 2 + y ^ 2 = 0) :
    IsPropTriangle x y 0 :=
  isPropTriangle_of_sq hx (a := 1) (b := -1) (c := 0) (by rw [C_1, one_mul])
    (by rw [C_neg, C_1]; linear_combination h) (by rw [C_0]; ring)

/-- **Leg · hypotenuse** (`SquareLengths.not_isSquare_mul_leg_hyp` and
`SquareLengthsHyp.not_isSquare_two_mul_leg_hyp` over `K[X]`): if `x² + y² = z²` and
`x z = κ s²`, the triangle is proportional. Via `y⁴ + 4κ² s⁴ = (z² + x²)²`. -/
theorem isPropTriangle_of_leg_hyp_sq (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hx : x ≠ 0)
    (hy : y ≠ 0) (h : x ^ 2 + y ^ 2 = z ^ 2) {κ : K} (hκ : κ ≠ 0) {s : K[X]}
    (hs : x * z = C κ * s ^ 2) : IsPropTriangle x y z := by
  by_cases hz : z = 0
  · subst hz; exact isPropTriangle_of_hyp_eq_zero hx (by rw [h]; ring)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, mul_zero] at hs
    exact (mul_ne_zero hx hz) hs
  have h4 : (4 : K) * κ ^ 2 ≠ 0 := mul_ne_zero (four_ne_zero_of_two h2) (pow_ne_zero 2 hκ)
  have hq : y ^ 4 + C (4 * κ ^ 2) * s ^ 4 = C 1 * (z ^ 2 + x ^ 2) ^ 2 := by
    rw [C_1, C_mul, C_pow, C_ofNat]
    linear_combination (y ^ 2 + z ^ 2 - x ^ 2) * h - 4 * (C κ * s ^ 2 + x * z) * hs
  obtain ⟨q, α, β, hyq, hsq⟩ := quartic_proportional h2 h4 one_ne_zero hy hs0 hq
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hyq; exact hy hyq
  have hw : (z ^ 2 + x ^ 2) ^ 2 = y ^ 4 + C (4 * κ ^ 2) * s ^ 4 := by rw [hq, C_1, one_mul]
  obtain ⟨ν, hν⟩ := eq_C_mul_of_sq_eq (pow_ne_zero 2 hq0) (P := z ^ 2 + x ^ 2)
    (c := α ^ 4 + 4 * κ ^ 2 * β ^ 4) (by
      rw [hw, hyq, hsq]; simp only [map_add, map_mul, map_pow]; ring)
  have hd : z ^ 2 - x ^ 2 = C (α ^ 2) * q ^ 2 := by
    rw [C_pow]; linear_combination -h + (y + C α * q) * hyq
  obtain ⟨hz2, hx2⟩ := half_combo h2 hν hd
  exact isPropTriangle_of_sq hq0 (b := α ^ 2) hx2 (by rw [hyq, C_pow]; ring) hz2

/-- **Leg · leg** (`SquareLengths.not_isSquare_mul_legs` over `K[X]`): if `x² + y² = z²` and
`x y = κ s²`, the triangle is proportional. Via `z⁴ − 4κ² s⁴ = (x² − y²)²`. -/
theorem isPropTriangle_of_leg_leg_sq (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hx : x ≠ 0)
    (hy : y ≠ 0) (h : x ^ 2 + y ^ 2 = z ^ 2) {κ : K} (hκ : κ ≠ 0) {s : K[X]}
    (hs : x * y = C κ * s ^ 2) : IsPropTriangle x y z := by
  by_cases hz : z = 0
  · subst hz; exact isPropTriangle_of_hyp_eq_zero hx (by rw [h]; ring)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, mul_zero] at hs
    exact (mul_ne_zero hx hy) hs
  have h4 : -((4 : K) * κ ^ 2) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (four_ne_zero_of_two h2) (pow_ne_zero 2 hκ))
  have hq : z ^ 4 + C (-(4 * κ ^ 2)) * s ^ 4 = C 1 * (x ^ 2 - y ^ 2) ^ 2 := by
    rw [C_1, C_neg, C_mul, C_pow, C_ofNat]
    linear_combination -(x ^ 2 + y ^ 2 + z ^ 2) * h + 4 * (x * y + C κ * s ^ 2) * hs
  obtain ⟨q, α, β, hzq, hsq⟩ := quartic_proportional h2 h4 one_ne_zero hz hs0 hq
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hzq; exact hz hzq
  have hw : (x ^ 2 - y ^ 2) ^ 2 = z ^ 4 + C (-(4 * κ ^ 2)) * s ^ 4 := by
    rw [hq, C_1, one_mul]
  obtain ⟨ν, hν⟩ := eq_C_mul_of_sq_eq (pow_ne_zero 2 hq0) (P := x ^ 2 - y ^ 2)
    (c := α ^ 4 - 4 * κ ^ 2 * β ^ 4) (by
      rw [hw, hzq, hsq]; simp only [map_sub, map_neg, map_mul, map_pow]; ring)
  have hsum : x ^ 2 + y ^ 2 = C (α ^ 2) * q ^ 2 := by rw [h, hzq, C_pow]; ring
  obtain ⟨hx2, hy2⟩ := half_combo h2 hsum hν
  exact isPropTriangle_of_sq hq0 (c := α ^ 2) hx2 hy2 (by rw [hzq, C_pow]; ring)

/-- **Leg and hypotenuse both constant multiples of squares**: the triangle is proportional.
Via `κ₂² q⁴ − κ₁² p⁴ = y²`. -/
theorem isPropTriangle_of_two_sq (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hx : x ≠ 0)
    (_hy : y ≠ 0) (h : x ^ 2 + y ^ 2 = z ^ 2) {κ₁ κ₂ : K} {p q : K[X]}
    (hx' : x = C κ₁ * p ^ 2) (hz' : z = C κ₂ * q ^ 2) : IsPropTriangle x y z := by
  by_cases hz : z = 0
  · subst hz; exact isPropTriangle_of_hyp_eq_zero hx (by rw [h]; ring)
  have hκ₁ : κ₁ ≠ 0 := by rintro rfl; rw [C_0, zero_mul] at hx'; exact hx hx'
  have hκ₂ : κ₂ ≠ 0 := by rintro rfl; rw [C_0, zero_mul] at hz'; exact hz hz'
  have hp0 : p ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero, mul_zero] at hx'; exact hx hx'
  have hq0 : q ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero, mul_zero] at hz'; exact hz hz'
  have heq : C (κ₂ ^ 2) * q ^ 4 + C (-(κ₁ ^ 2)) * p ^ 4 = C 1 * y ^ 2 := by
    rw [C_1, C_neg, C_pow, C_pow]
    rw [hx', hz'] at h
    linear_combination -h
  obtain ⟨r, α, β, hqr, hpr⟩ := quartic_proportional_gen h2 (pow_ne_zero 2 hκ₂)
    (neg_ne_zero.mpr (pow_ne_zero 2 hκ₁)) one_ne_zero hq0 hp0 heq
  have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero] at hpr; exact hp0 hpr
  have hy2 : y ^ 2 = z ^ 2 - x ^ 2 := by linear_combination h
  refine isPropTriangle_of_sq (q := r ^ 2) (pow_ne_zero 2 hr0)
    (a := (κ₁ * β ^ 2) ^ 2) (b := (κ₂ * α ^ 2) ^ 2 - (κ₁ * β ^ 2) ^ 2) (c := (κ₂ * α ^ 2) ^ 2)
    ?_ ?_ ?_
  · rw [hx', hpr]; simp only [map_mul, map_pow]; ring
  · rw [hy2, hx', hz', hpr, hqr]; simp only [map_sub, map_mul, map_pow]; ring
  · rw [hz', hqr]; simp only [map_mul, map_pow]; ring

/-- **Both legs constant multiples of squares**: the triangle is proportional.
Via `κ₁² p⁴ + κ₂² q⁴ = z²`. -/
theorem isPropTriangle_of_two_sq_legs (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hx : x ≠ 0)
    (hy : y ≠ 0) (h : x ^ 2 + y ^ 2 = z ^ 2) {κ₁ κ₂ : K} {p q : K[X]}
    (hx' : x = C κ₁ * p ^ 2) (hy' : y = C κ₂ * q ^ 2) : IsPropTriangle x y z := by
  have hκ₁ : κ₁ ≠ 0 := by rintro rfl; rw [C_0, zero_mul] at hx'; exact hx hx'
  have hκ₂ : κ₂ ≠ 0 := by rintro rfl; rw [C_0, zero_mul] at hy'; exact hy hy'
  have hp0 : p ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero, mul_zero] at hx'; exact hx hx'
  have hq0 : q ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero, mul_zero] at hy'; exact hy hy'
  have heq : C (κ₁ ^ 2) * p ^ 4 + C (κ₂ ^ 2) * q ^ 4 = C 1 * z ^ 2 := by
    rw [C_1, C_pow, C_pow]
    rw [hx', hy'] at h
    linear_combination h
  obtain ⟨r, α, β, hpr, hqr⟩ := quartic_proportional_gen h2 (pow_ne_zero 2 hκ₁)
    (pow_ne_zero 2 hκ₂) one_ne_zero hp0 hq0 heq
  have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero] at hpr; exact hp0 hpr
  refine isPropTriangle_of_sq (q := r ^ 2) (pow_ne_zero 2 hr0)
    (a := (κ₁ * α ^ 2) ^ 2) (b := (κ₂ * β ^ 2) ^ 2) (c := (κ₁ * α ^ 2) ^ 2 + (κ₂ * β ^ 2) ^ 2)
    ?_ ?_ ?_
  · rw [hx', hpr]; simp only [map_mul, map_pow]; ring
  · rw [hy', hqr]; simp only [map_mul, map_pow]; ring
  · rw [← h, hx', hy', hpr, hqr]; simp only [map_add, map_mul, map_pow]; ring

/-- **Hypotenuse² + leg² a square** (`Adjacency.not_isSquare_hyp_sq_add_leg_sq` over `K[X]`):
if `x² + y² = z²` and `z² + x² = w²`, the triangle is proportional. Via `z⁴ − x⁴ = (y w)²`. -/
theorem isPropTriangle_of_hyp_sq_add_leg_sq (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hx : x ≠ 0)
    (_hy : y ≠ 0) (h : x ^ 2 + y ^ 2 = z ^ 2) {w : K[X]} (hw : z ^ 2 + x ^ 2 = w ^ 2) :
    IsPropTriangle x y z := by
  by_cases hz : z = 0
  · subst hz; exact isPropTriangle_of_hyp_eq_zero hx (by rw [h]; ring)
  obtain ⟨q, α, β, hzq, hxq⟩ := quartic_sub_proportional h2 hz hx (z := y * w)
    (by linear_combination -(z ^ 2 + x ^ 2) * h + y ^ 2 * hw)
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hzq; exact hz hzq
  refine isPropTriangle_of_sq hq0 (a := β ^ 2) (b := α ^ 2 - β ^ 2) (c := α ^ 2) ?_ ?_ ?_
  · rw [hxq, C_pow]; ring
  · rw [C_sub, C_pow, C_pow]; linear_combination h + (z + C α * q) * hzq - (x + C β * q) * hxq
  · rw [hzq, C_pow]; ring

/-! ## Cuboid consequences -/

/-- `x² + y² = z²` and `z² + x² = w²` with `x ≠ 0` (`y` may vanish): `x` and `z` proportional. -/
theorem proportional_of_hyp_sq_add_leg_sq (h2 : (2 : K) ≠ 0) {x y z w : K[X]} (hx : x ≠ 0)
    (h : x ^ 2 + y ^ 2 = z ^ 2) (hw : z ^ 2 + x ^ 2 = w ^ 2) :
    ∃ (q : K[X]) (α β : K), x = C α * q ∧ z = C β * q := by
  by_cases hy0 : y = 0
  · subst hy0
    obtain ⟨ν, hν⟩ := eq_C_mul_of_sq_eq (P := z) (c := 1) hx
      (by rw [C_1, one_mul]; linear_combination -h)
    exact ⟨x, 1, ν, by rw [C_1, one_mul], hν⟩
  · obtain ⟨q, α, -, γ, hxq, -, hzq⟩ := isPropTriangle_of_hyp_sq_add_leg_sq h2 hx hy0 h hw
    exact ⟨q, α, γ, hxq, hzq⟩

/-- **`d² + e²` square ⇒ `a` and `g` proportional** (`Adjacency` over `K[X]`, any `K` with
`2 ≠ 0`): `d² + e² = g² + a²` and `g² − a² = f²`, so `g⁴ − a⁴ = (f w)²`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_isSquare_face_sum
    {a b c : K[X]} (h : PolyCharP.IsCuboid a b c) (h2 : (2 : K) ≠ 0) {d e : K[X]}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hsq : IsSquare (d ^ 2 + e ^ 2)) :
    ∃ (q : K[X]) (α β : K), a = C α * q ∧
      (∃ g, a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 ∧ g = C β * q) := by
  obtain ⟨g, hg⟩ := h.sq_abc
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨w, hw⟩ := hsq
  obtain ⟨q, α, β, ha, hgq⟩ := proportional_of_hyp_sq_add_leg_sq h2 h.ne_a (y := f) (z := g)
    (w := w)
    (by linear_combination hg - hf) (by linear_combination -hg + hd + he + hw)
  exact ⟨q, α, β, ha, g, by rw [hg]; ring, hgq⟩

/-- **`d² + f²` square ⇒ `b` and `g` proportional** (`d² = a² + b²`, `f² = b² + c²`). -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_isSquare_face_sum_b
    {a b c : K[X]} (h : PolyCharP.IsCuboid a b c) (h2 : (2 : K) ≠ 0) {d f : K[X]}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hsq : IsSquare (d ^ 2 + f ^ 2)) :
    ∃ (q : K[X]) (α β : K), b = C α * q ∧
      (∃ g, a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 ∧ g = C β * q) := by
  obtain ⟨g, hg⟩ := h.sq_abc
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨w, hw⟩ := hsq
  obtain ⟨q, α, β, hb, hgq⟩ := proportional_of_hyp_sq_add_leg_sq h2 h.ne_b (y := e) (z := g)
    (w := w)
    (by linear_combination hg - he) (by linear_combination -hg + hd + hf + hw)
  exact ⟨q, α, β, hb, g, by rw [hg]; ring, hgq⟩

/-- **`e² + f²` square ⇒ `c` and `g` proportional** (`e² = a² + c²`, `f² = b² + c²`). -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_isSquare_face_sum_c
    {a b c : K[X]} (h : PolyCharP.IsCuboid a b c) (h2 : (2 : K) ≠ 0) {e f : K[X]}
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hsq : IsSquare (e ^ 2 + f ^ 2)) :
    ∃ (q : K[X]) (α β : K), c = C α * q ∧
      (∃ g, a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 ∧ g = C β * q) := by
  obtain ⟨g, hg⟩ := h.sq_abc
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨w, hw⟩ := hsq
  obtain ⟨q, α, β, hc, hgq⟩ := proportional_of_hyp_sq_add_leg_sq h2 h.ne_c (y := d) (z := g)
    (w := w)
    (by linear_combination hg - hd) (by linear_combination -hg + he + hf + hw)
  exact ⟨q, α, β, hc, g, by rw [hg]; ring, hgq⟩

/-- **Both edges of a face constant multiples of squares** ⇒ that face is a proportional
triangle. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.not_face_two_sq {a b c : K[X]}
    (h : PolyCharP.IsCuboid a b c) (h2 : (2 : K) ≠ 0) {d : K[X]} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    {κ₁ κ₂ : K} {p q : K[X]} (ha : a = C κ₁ * p ^ 2) (hb : b = C κ₂ * q ^ 2) :
    IsPropTriangle a b d :=
  isPropTriangle_of_two_sq_legs h2 h.ne_a h.ne_b hd ha hb

/-- **An edge and the face diagonal of a face through it both constant multiples of squares** ⇒
that face is a proportional triangle. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.not_face_two_sq' {a b c : K[X]}
    (h : PolyCharP.IsCuboid a b c) (h2 : (2 : K) ≠ 0) {d : K[X]} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    {κ₁ κ₂ : K} {p q : K[X]} (ha : a = C κ₁ * p ^ 2) (hd' : d = C κ₂ * q ^ 2) :
    IsPropTriangle a b d :=
  isPropTriangle_of_two_sq h2 h.ne_a h.ne_b hd ha hd'

/-- **Edge · face diagonal a constant times a square** ⇒ that face is a proportional triangle. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.not_edge_mul_faceDiag_sq {a b c : K[X]}
    (h : PolyCharP.IsCuboid a b c) (h2 : (2 : K) ≠ 0) {d : K[X]} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    {κ : K} (hκ : κ ≠ 0) {s : K[X]} (hs : a * d = C κ * s ^ 2) : IsPropTriangle a b d :=
  isPropTriangle_of_leg_hyp_sq h2 h.ne_a h.ne_b hd hκ hs

/-- **Edge · edge a constant times a square** ⇒ that face is a proportional triangle. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.not_edge_mul_edge_sq {a b c : K[X]}
    (h : PolyCharP.IsCuboid a b c) (h2 : (2 : K) ≠ 0) {d : K[X]} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    {κ : K} (hκ : κ ≠ 0) {s : K[X]} (hs : a * b = C κ * s ^ 2) : IsPropTriangle a b d :=
  isPropTriangle_of_leg_leg_sq h2 h.ne_a h.ne_b hd hκ hs

/-! ## Consistency with the Frobenius cuboid -/

/-- On the Frobenius cuboid `(X − X^p, i (X + X^p), X^(p+1) + 1)` (characteristic `p` odd,
`i² = −1`) the sum `d² + e²` of the two face diagonals through `a` is **never** a square: else
`a` (degree `p`) and `g = ±(X^(p+1) − 1)` (degree `p + 1`) would be proportional. -/
theorem frobenius_face_sum_not_isSquare {p : ℕ} [hp : Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {i : K} (hi : i ^ 2 = -1) {d e : K[X]}
    (hd : (X - X ^ p) ^ 2 + (C i * (X + X ^ p)) ^ 2 = d ^ 2)
    (he : (X - X ^ p) ^ 2 + (X ^ (p + 1) + 1) ^ 2 = e ^ 2) : ¬ IsSquare (d ^ 2 + e ^ 2) := by
  intro hsq
  have hc := (PolyCharP.isNondegCuboid_frobenius (K := K) hp2 hi).toIsCuboid
  have hp1 : 2 ≤ p := hp.out.two_le
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    have := Nat.le_of_dvd two_pos this
    omega
  obtain ⟨q, α, β, ha, g, hg, hgq⟩ := hc.proportional_of_isSquare_face_sum h2K hd he hsq
  have hI : (C i : K[X]) ^ 2 = -1 := PolyCharP.C_sq_eq_neg_one hi
  have e4 : (X - X ^ p) ^ 2 + (C i * (X + X ^ p)) ^ 2 + (X ^ (p + 1) + 1) ^ 2 =
      (X ^ (p + 1) - 1 : K[X]) ^ 2 := by
    linear_combination (X + X ^ p) ^ 2 * hI
  have hdegs : (X ^ (p + 1) - 1 : K[X]).natDegree = p + 1 := by
    rw [← C_1]; exact natDegree_X_pow_sub_C
  have hg2 : g.natDegree = p + 1 := by
    have := congrArg natDegree (hg.symm.trans e4)
    rw [natDegree_pow, natDegree_pow, hdegs] at this
    omega
  have hadeg : (X - X ^ p : K[X]).natDegree = p := by
    rw [natDegree_sub_eq_right_of_natDegree_lt] <;> simp; omega
  have hα : α ≠ 0 := by rintro rfl; rw [C_0, zero_mul] at ha; exact hc.ne_a ha
  have hqdeg : q.natDegree = p := by rw [← hadeg, ha, natDegree_C_mul hα]
  have : g.natDegree ≤ p := by rw [hgq, ← hqdeg]; exact natDegree_C_mul_le β q
  omega

/-! ## The genus-two curve `y² = x (x⁴ − 1)` over `K(X)` -/

/-- In `K[X]`, if `a b = u V²` with `a, b` coprime and `u ≠ 0`, then `a` is a constant times a
square. -/
theorem exists_C_mul_sq_of_mul {a b V : K[X]} {u : K} (hu : u ≠ 0) (hab : IsCoprime a b)
    (h : a * b = C u * V ^ 2) : ∃ (κ : K) (m : K[X]), a = C κ * m ^ 2 := by
  have hU : IsUnit (C u⁻¹) := isUnit_C.mpr (inv_ne_zero hu).isUnit
  have hcop : IsCoprime a (b * C u⁻¹) := (isCoprime_mul_unit_right_right hU a b).mpr hab
  have hu1 : C u⁻¹ * C u = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hu, C_1]
  obtain ⟨m, v, hv⟩ := exists_associated_pow_of_mul_eq_pow' hcop (k := 2) (c := V)
    (by linear_combination C u⁻¹ * h + V ^ 2 * hu1)
  obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp v.isUnit
  exact ⟨r, m, by rw [← hv, ← hr, mul_comm]⟩

/-- **Genus two** (the `K[X]`-analogue of `GaussianQuartic.genus_two`): if
`p q (p⁴ − q⁴) = u V²` with `p, q ≠ 0`, `u ≠ 0`, then `p, q` are constant multiples of one
polynomial. Any field with `2 ≠ 0`. -/
theorem genus_two_poly (h2 : (2 : K) ≠ 0) {p q V : K[X]} {u : K} (hu : u ≠ 0) (hp : p ≠ 0)
    (hq : q ≠ 0) (h : p * q * (p ^ 4 - q ^ 4) = C u * V ^ 2) :
    ∃ (r : K[X]) (α β : K), p = C α * r ∧ q = C β * r := by
  classical
  obtain ⟨p', q', hp', hq', hun⟩ := extract_gcd p q
  set d := gcd p q
  have hd : d ≠ 0 := by intro h0; rw [h0, zero_mul] at hp'; exact hp hp'
  have hp0 : p' ≠ 0 := by rintro rfl; rw [mul_zero] at hp'; exact hp hp'
  have hq0 : q' ≠ 0 := by rintro rfl; rw [mul_zero] at hq'; exact hq hq'
  have hcop : IsCoprime p' q' := (gcd_isUnit_iff p' q').mp hun
  have hE : C u * V ^ 2 = (d ^ 3) ^ 2 * (p' * q' * (p' ^ 4 - q' ^ 4)) := by
    rw [← h, hp', hq']; ring
  have hdvd : (d ^ 3) ^ 2 ∣ V ^ 2 := by
    have h1 : (d ^ 3) ^ 2 ∣ C u * V ^ 2 := ⟨_, hE⟩
    have hu1 : C u⁻¹ * C u = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hu, C_1]
    have : V ^ 2 = C u⁻¹ * (C u * V ^ 2) := by rw [← mul_assoc, hu1, one_mul]
    rw [this]; exact Dvd.dvd.mul_left h1 _
  obtain ⟨V', hV'⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp hdvd
  have heq : p' * q' * (p' ^ 4 - q' ^ 4) = C u * V' ^ 2 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero 3 hd)) ?_
    rw [← hE, hV']; ring
  by_cases hF : p' ^ 4 - q' ^ 4 = 0
  · obtain ⟨ν, hν⟩ := eq_C_mul_of_sq_eq (P := p' ^ 2) (c := 1) (pow_ne_zero 2 hq0)
      (by rw [C_1, one_mul]; linear_combination hF)
    obtain ⟨ν', hν'⟩ := eq_C_mul_of_sq_eq (P := p') (c := ν) hq0 hν
    exact ⟨q, ν', 1, by rw [hp', hν', hq']; ring, by rw [C_1, one_mul]⟩
  set F := p' ^ 4 - q' ^ 4 with hFdef
  have hpF : IsCoprime p' F := by
    have := (hcop.pow_right (n := 4)).neg_right.add_mul_left_right (p' ^ 3)
    convert this using 1; rw [hFdef]; ring
  have hqF : IsCoprime q' F := by
    have := (hcop.symm.pow_right (n := 4)).add_mul_left_right (-q' ^ 3)
    convert this using 1; rw [hFdef]; ring
  obtain ⟨κ₁, m, hm⟩ := exists_C_mul_sq_of_mul hu (hcop.mul_right hpF) (b := q' * F) (V := V')
    (by rw [← heq]; ring)
  obtain ⟨κ₂, n, hn⟩ := exists_C_mul_sq_of_mul hu (hcop.symm.mul_right hqF) (b := p' * F)
    (V := V') (by rw [← heq]; ring)
  obtain ⟨κ₃, t, ht⟩ := exists_C_mul_sq_of_mul hu (hpF.symm.mul_right hqF.symm) (b := p' * q')
    (V := V') (by rw [← heq]; ring)
  have hκ₁ : κ₁ ≠ 0 := by rintro rfl; rw [C_0, zero_mul] at hm; exact hp0 hm
  have hκ₂ : κ₂ ≠ 0 := by rintro rfl; rw [C_0, zero_mul] at hn; exact hq0 hn
  have hκ₃ : κ₃ ≠ 0 := by rintro rfl; rw [C_0, zero_mul] at ht; exact hF ht
  have hm0 : m ^ 2 ≠ 0 := by intro h0; rw [h0, mul_zero] at hm; exact hp0 hm
  have hn0 : n ^ 2 ≠ 0 := by intro h0; rw [h0, mul_zero] at hn; exact hq0 hn
  have hquart : C (κ₁ ^ 4) * (m ^ 2) ^ 4 + C (-(κ₂ ^ 4)) * (n ^ 2) ^ 4 = C κ₃ * t ^ 2 := by
    rw [← ht, hFdef, hm, hn, C_neg, C_pow, C_pow]; ring
  obtain ⟨r, α, β, hmr, hnr⟩ := quartic_proportional_gen h2 (pow_ne_zero 4 hκ₁)
    (neg_ne_zero.mpr (pow_ne_zero 4 hκ₂)) hκ₃ hm0 hn0 hquart
  refine ⟨d * r, κ₁ * α, κ₂ * β, ?_, ?_⟩
  · rw [hp', hm, hmr, C_mul]; ring
  · rw [hq', hn, hnr, C_mul]; ring

/-! ## Near-miss examples -/

local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The `𝔽₅` Frobenius cuboid `(X − X⁵, 2 (X + X⁵), X⁶ + 1)` (`i = 2`): `d² + e²` is not a
square, for any choice of face diagonals `d, e`. -/
example {d e : (ZMod 5)[X]}
    (hd : (X - X ^ 5) ^ 2 + (C 2 * (X + X ^ 5)) ^ 2 = d ^ 2)
    (he : (X - X ^ 5) ^ 2 + (X ^ (5 + 1) + 1) ^ 2 = e ^ 2) : ¬ IsSquare (d ^ 2 + e ^ 2) :=
  frobenius_face_sum_not_isSquare (K := ZMod 5) (p := 5) (i := 2) (by norm_num) (by decide) hd he

/-- The same over `𝔽₁₃` (`i = 5`). -/
example {d e : (ZMod 13)[X]}
    (hd : (X - X ^ 13) ^ 2 + (C 5 * (X + X ^ 13)) ^ 2 = d ^ 2)
    (he : (X - X ^ 13) ^ 2 + (X ^ (13 + 1) + 1) ^ 2 = e ^ 2) : ¬ IsSquare (d ^ 2 + e ^ 2) :=
  frobenius_face_sum_not_isSquare (K := ZMod 13) (p := 13) (i := 5) (by norm_num) (by decide) hd he

/-- A proportional cuboid `(α q, β q, γ q)` has every face a proportional triangle: the
conclusions above are compatible with it. -/
example (q : K[X]) (α β δ : K) :
    IsPropTriangle (C α * q) (C β * q) (C δ * q) := ⟨q, α, β, δ, rfl, rfl, rfl⟩

end PerfectCuboid.PolyFermat
