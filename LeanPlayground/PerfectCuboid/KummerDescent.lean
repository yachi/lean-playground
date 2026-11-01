module

public import LeanPlayground.PerfectCuboid.Torsion
public import LeanPlayground.PerfectCuboid.TwistRigidity

/-!
# 2-descent on `E_N`: Ingram's step replaced by a square condition

The repository proves Asiryan's rank-one reduction unconditionally (`rankOneReduction_of_pos`):
a positive cuboid configuration in a subgroup `ℤG + E_N[2]` can be brought to the pattern
`Q₁ = aG`, `Q₂ = bG + T`, `Q₃ = cG + U` with `a, b` odd, `c` even, `c > 0` (`Pattern`). Asiryan
(arXiv:2610.10643, §6) then uses Ingram's primitive-divisor theorem, which `CongruentRank.lean`
keeps as the hypothesis `PrimitiveDivisorStep`. This file replaces it by a square condition.

## Kummer classes

For `P = (x, y) ∈ E_N(ℚ)` the Kummer map is `κ(P) = (x, x − N, x + N)` in `(ℚ*/ℚ*²)³`.

* `hasX_two_smul`, `two_smul_sub_eq`, `two_smul_add_eq`, `two_smul_classes`: for `y ≠ 0`,
  `x(2R) = ((x² + N²)/(2y))²`, `x(2R) ∓ N = ((x² ∓ 2Nx − N²)/(2y))²`, so a point of `2E_N(ℚ)` has
  all three classes trivial.
* `add_S_classes`, `add_T_classes`, `add_U_classes`: translation by `S`, `T`, `U` multiplies the
  classes by `κ(S) = (−1, −N, N)`, `κ(T) = (N, 2, 2N)`, `κ(U) = (−N, −2N, 2)`.
* `two_smul_hasX`, `two_smul_add_S`, `two_smul_add_T`, `two_smul_add_U`: the classes of each of
  the four cosets `R₀ + 2E_N(ℚ)`, `R₀ ∈ E_N[2]`; `egg_not_two_smul`: an egg point (`−N < x < 0`)
  lies in neither `2E_N(ℚ)` nor `T + 2E_N(ℚ)`.

## Ingram replaced

* `IsQuarterX N x`: `−N·x` and `−2N·(x − N)` are rational squares.
* `pattern_quarter`: in the pattern, `c` even gives `Q₃ = 2((c/2)G) + U ∈ U + 2E_N(ℚ)`, so the
  third point is a quarter point (and `2(x₃ + N)` is a square too).
* `QuarterFree N`: no positive configuration `IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃` has `x₃` a quarter
  abscissa (by `IsConfigPts.swap₁₂`, `swap₂₃` this covers every position).
* **`not_inRankOne_of_quarterFree`**: `QuarterFree N` implies that no positive configuration on
  `E_N` lies in a subgroup of rank one. No hypothesis besides `QuarterFree N`; only `propext`,
  `Classical.choice`, `Quot.sound`.

## The cuboid side

* `IsRatCuboid.quarter_iff` (and `quarter_iff₁`, `quarter_iff₂` for the other two derived
  triangles): for a rational perfect cuboid, the third configuration point
  `x₃ = −N·cg/(ef + ab)` is a quarter point iff `cg(ef + ab)` and `2(ef + ab)(ef + ab + cg)` are
  squares. (The factor `2` is needed: in half-angle form `ef + ab = k(m + n)²`,
  `cg = k(m² − n²)`, `ef + ab + cg = 2km(m + n)`, the conditions read `(m − n)(m + n) = □` and
  `m(m + n) = □`.)
* `IsConfigPts.exists_cuboid` (**round trip**): every positive configuration is the configuration
  `isConfigPts_of_cuboid` of a rational perfect cuboid with the same `N` (edges `|Uᵢ|`,
  `s = |U₁U₂U₃|/(2N)`); the abscissas agree because `x ↦ edge²` is injective on the egg
  (`eq_of_edge_sq_eq`).
* `quarterFree_iff`, `quarterFree_iff₁`, `quarterFree_iff₂`: **`QuarterFree N` is equivalent to
  "no rational perfect cuboid with `abcg = 2Ns²` satisfies the two square conditions"**, for any
  one of the three derived triangles; `not_inRankOne_of_cuboid` packages the consequence.
* `inRankOne_pair` (pigeonhole): in a rank-one configuration some difference `Qᵢ − Qⱼ` lies in
  `E_N[2] + 2E_N(ℚ)`.

Near-miss remark. The degenerate box `(a, b, 0)` gives `X₁ = X₂ = X₃ = −N`, the point `U` itself,
which satisfies the quarter condition trivially (`−N·(−N) = N²`, `−2N·(−2N) = (2N)²`); it is
excluded only by `IsConfig.lt₃ : −N < x₃`. So `QuarterFree N` cannot be proved by congruences: a
proof must use `c > 0` globally.
-/

@[expose] public section

namespace PerfectCuboid.Kummer

open PerfectCuboid.CongruentRank WeierstrassCurve WeierstrassCurve.Affine

variable {N : ℚ}

/-! ### Doubling -/

/-- Doubling on `E_N`: if `y ≠ 0` then `x(2R) = ((x² + N²)/(2y))²`. -/
theorem hasX_two_smul (hN : N ≠ 0) {x y : ℚ} (h : (curve N).Nonsingular x y) (hy : y ≠ 0) :
    HasX (2 • Point.some x y h) (((x ^ 2 + N ^ 2) / (2 * y)) ^ 2) := by
  have hy2 := (nonsingular_iff hN).mp h
  have hne : y ≠ (curve N).negY x y := by
    simp only [curve, negY, zero_mul, sub_zero]
    intro h'; apply hy; linarith
  rw [two_nsmul, Point.add_self_of_Y_ne hne]
  apply hasX_some
  rw [addX, slope_of_Y_ne rfl hne]
  simp only [curve, negY, zero_mul, sub_zero, mul_zero, add_zero]
  rw [show y - -y = 2 * y by ring]
  field_simp
  linear_combination (-8 * x) * hy2

theorem two_smul_sub_eq (hN : N ≠ 0) {x y : ℚ} (h : (curve N).Nonsingular x y) (hy : y ≠ 0) :
    ((x ^ 2 + N ^ 2) / (2 * y)) ^ 2 - N = ((x ^ 2 - 2 * N * x - N ^ 2) / (2 * y)) ^ 2 := by
  have hy2 := (nonsingular_iff hN).mp h
  field_simp
  linear_combination (-4 * N) * hy2

theorem two_smul_add_eq (hN : N ≠ 0) {x y : ℚ} (h : (curve N).Nonsingular x y) (hy : y ≠ 0) :
    ((x ^ 2 + N ^ 2) / (2 * y)) ^ 2 + N = ((x ^ 2 + 2 * N * x - N ^ 2) / (2 * y)) ^ 2 := by
  have hy2 := (nonsingular_iff hN).mp h
  field_simp
  linear_combination (4 * N) * hy2


/-- A nonzero double has all three Kummer coordinates trivial: `x`, `x − N`, `x + N` are squares. -/
theorem two_smul_classes (hN : N ≠ 0) (R : (curve N).Point) (h2 : 2 • R ≠ 0) :
    ∃ x, HasX (2 • R) x ∧ IsSquare x ∧ IsSquare (x - N) ∧ IsSquare (x + N) := by
  cases R with
  | zero => exact (h2 (nsmul_zero 2)).elim
  | @some x y h =>
    by_cases hy : y = 0
    · subst hy
      refine absurd ?_ h2
      rw [two_nsmul]
      exact Point.add_self_of_Y_eq (by simp [curve, negY])
    · exact ⟨_, hasX_two_smul hN h hy, ⟨_, sq _⟩,
        ⟨_, (two_smul_sub_eq hN h hy).trans (sq _)⟩, ⟨_, (two_smul_add_eq hN h hy).trans (sq _)⟩⟩

/-! ### Translation by the `2`-torsion -/

/-- Translation by `U` multiplies the classes by `κ(U) = (−N, −2N, 2)`. -/
theorem add_U_classes (hN : N ≠ 0) {P : (curve N).Point} {x : ℚ} (h : HasX P x) (hx : x ≠ -N)
    (h1 : IsSquare x) (h2 : IsSquare (x - N)) (h3 : IsSquare (x + N)) :
    ∃ x', HasX (P + U hN) x' ∧ IsSquare (-N * x') ∧ IsSquare (-2 * N * (x' - N)) ∧
      IsSquare (2 * (x' + N)) := by
  obtain ⟨r₁, hr₁⟩ := h1
  obtain ⟨r₂, hr₂⟩ := h2
  obtain ⟨r₃, hr₃⟩ := h3
  have hx' : x + N ≠ 0 := by rw [← sub_neg_eq_add]; exact sub_ne_zero.mpr hx
  refine ⟨_, h.add_U hN hx, ⟨N * r₂ * r₃ / (x + N), ?_⟩, ⟨2 * N * r₁ * r₃ / (x + N), ?_⟩,
    ⟨2 * N * r₃ / (x + N), ?_⟩⟩
  · field_simp
    linear_combination (x - N) * hr₃ + r₃ ^ 2 * hr₂
  · field_simp
    linear_combination 2 * x * hr₃ + 2 * r₃ ^ 2 * hr₁
  · field_simp
    linear_combination 2 * N * hr₃

/-- Translation by `S` multiplies the classes by `κ(S) = (−1, −N, N)`. -/
theorem add_S_classes (hN : N ≠ 0) {P : (curve N).Point} {x : ℚ} (h : HasX P x) (hx : x ≠ 0)
    (h1 : IsSquare x) (h2 : IsSquare (x - N)) (h3 : IsSquare (x + N)) :
    ∃ x', HasX (S hN + P) x' ∧ IsSquare (-x') ∧ IsSquare (-N * (x' - N)) ∧
      IsSquare (N * (x' + N)) := by
  obtain ⟨r₁, hr₁⟩ := h1
  obtain ⟨r₂, hr₂⟩ := h2
  obtain ⟨r₃, hr₃⟩ := h3
  refine ⟨_, h.S_add hN hx, ⟨N * r₁ / x, ?_⟩, ⟨N * r₁ * r₃ / x, ?_⟩, ⟨N * r₁ * r₂ / x, ?_⟩⟩
  · field_simp
    linear_combination hr₁
  · field_simp
    linear_combination x * hr₃ + r₃ ^ 2 * hr₁
  · field_simp
    linear_combination x * hr₂ + r₂ ^ 2 * hr₁

/-- Translation by `T` multiplies the classes by `κ(T) = (N, 2, 2N)`. -/
theorem add_T_classes (hN : N ≠ 0) {P : (curve N).Point} {x : ℚ} (h : HasX P x) (hx : x ≠ N)
    (h1 : IsSquare x) (h2 : IsSquare (x - N)) (h3 : IsSquare (x + N)) :
    ∃ x', HasX (P + T hN) x' ∧ IsSquare (N * x') ∧ IsSquare (2 * (x' - N)) ∧
      IsSquare (2 * N * (x' + N)) := by
  obtain ⟨r₁, hr₁⟩ := h1
  obtain ⟨r₂, hr₂⟩ := h2
  obtain ⟨r₃, hr₃⟩ := h3
  have hx' : x - N ≠ 0 := sub_ne_zero.mpr hx
  refine ⟨_, h.add_T hN hx, ⟨N * r₂ * r₃ / (x - N), ?_⟩, ⟨2 * N * r₂ / (x - N), ?_⟩,
    ⟨2 * N * r₁ * r₂ / (x - N), ?_⟩⟩
  · field_simp
    linear_combination (x - N) * hr₃ + r₃ ^ 2 * hr₂
  · field_simp
    linear_combination 2 * N * hr₂
  · field_simp
    linear_combination 2 * x * hr₂ + 2 * r₂ ^ 2 * hr₁


/-! ### The quarter condition -/

/-- The quarter condition on an abscissa: `−N·x` and `−2N·(x − N)` are rational squares, i.e. the
Kummer classes of the point are those of `U + 2E_N(ℚ)`. -/
def IsQuarterX (N x : ℚ) : Prop := IsSquare (-N * x) ∧ IsSquare (-2 * N * (x - N))

/-- Every point of `U + 2E_N(ℚ)`, `U` itself included, has a quarter abscissa (and `2(x + N)` is a
square). -/
theorem two_smul_add_U (hN : 0 < N) (R : (curve N).Point) {x : ℚ}
    (h : HasX (2 • R + U hN.ne') x) : IsQuarterX N x ∧ IsSquare (2 * (x + N)) := by
  by_cases h0 : 2 • R = 0
  · rw [h0, zero_add] at h
    have := h.unique ⟨_, _, rfl⟩
    subst this
    -- `x = −N`: `−N·(−N) = N²`, `−2N·(−2N) = (2N)²`, `2·0 = 0²`.
    exact ⟨⟨⟨N, by ring⟩, ⟨2 * N, by ring⟩⟩, ⟨0, by ring⟩⟩
  · obtain ⟨x₀, hx₀, h1, h2, h3⟩ := two_smul_classes hN.ne' R h0
    have hne : x₀ ≠ -N := by
      rintro rfl
      obtain ⟨r, hr⟩ := h1
      nlinarith [mul_self_nonneg r]
    obtain ⟨x', hx', q1, q2, q3⟩ := add_U_classes hN.ne' hx₀ hne h1 h2 h3
    obtain rfl := hx'.unique h
    exact ⟨⟨q1, q2⟩, q3⟩

/-- **Pattern ⇒ quarter point.** In Asiryan's rank-one pattern `(aG, bG + T, cG + U)` with `c`
even, the third point is `2((c/2)G) + U ∈ U + 2E_N(ℚ)`, so its abscissa is a quarter abscissa. -/
theorem pattern_quarter (hN : 0 < N) (hp : Pattern N hN) :
    ∃ x₁ x₂ x₃ y₁ y₂ y₃, IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃ ∧ IsQuarterX N x₃ := by
  obtain ⟨G, a, b, c, x₁, x₂, x₃, hc, g₁, g₂, g₃, -, -, ⟨r, rfl⟩, -⟩ := hp
  have hq : IsQuarterX N x₃ := by
    rw [add_nsmul, ← two_nsmul] at g₃
    exact (two_smul_add_U hN _ g₃).1
  obtain ⟨y₁, hy₁, -⟩ := g₁
  obtain ⟨y₂, hy₂, -⟩ := g₂
  obtain ⟨y₃, hy₃, -⟩ := g₃
  exact ⟨x₁, x₂, x₃, y₁, y₂, y₃, ⟨hc, (nonsingular_iff hN.ne').mp hy₁,
    (nonsingular_iff hN.ne').mp hy₂, (nonsingular_iff hN.ne').mp hy₃⟩, hq⟩

/-- No positive configuration has a quarter point in third position. Since configurations can be
permuted (`IsConfigPts.swap₁₂`, `IsConfigPts.swap₂₃`), this says that no point of any positive
configuration on `E_N` is a quarter point. -/
def QuarterFree (N : ℚ) : Prop :=
  ∀ ⦃x₁ x₂ x₃ y₁ y₂ y₃ : ℚ⦄, IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃ → ¬ IsQuarterX N x₃

/-- **Ingram replaced.** If `E_N` has no positive configuration with a quarter point, then no
positive configuration on `E_N` lies in a subgroup `ℤG + E_N[2]` of rank one. -/
theorem not_inRankOne_of_quarterFree {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃)
    (hq : QuarterFree N) {Q₁ Q₂ Q₃ : (curve N).Point} (h₁ : HasX Q₁ x₁) (h₂ : HasX Q₂ x₂)
    (h₃ : HasX Q₃ x₃) : ¬ InRankOne Q₁ Q₂ Q₃ := by
  intro hQ
  obtain ⟨G, a, b, c, y₁, y₂, y₃, hc', g₁, g₂, g₃, ha, hb, hcev, hc0⟩ :=
    rankOneReduction_of_pos hc.pos hc h₁ h₂ h₃ hQ
  obtain ⟨_, _, _, _, _, _, hcp, hqx⟩ :=
    pattern_quarter hc.pos ⟨G, a, b, c, y₁, y₂, y₃, hc', g₁, g₂, g₃, ha, hb, hcev, hc0⟩
  exact hq hcp hqx


/-! ### The quarter condition on the cuboid side -/

theorem isSquare_mul_sq_iff {q r : ℚ} (hr : r ≠ 0) : IsSquare (q * r ^ 2) ↔ IsSquare q := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t / r, by field_simp; linear_combination ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t * r, by ring⟩

/-- For `x = −N·u/D`: `x` is a quarter abscissa iff `uD` and `2D(D + u)` are squares. -/
theorem isQuarterX_frac_iff (hN : N ≠ 0) {u D : ℚ} (hD : D ≠ 0) :
    IsQuarterX N (-N * u / D) ↔ IsSquare (u * D) ∧ IsSquare (2 * D * (D + u)) := by
  have e1 : -N * (-N * u / D) = u * D * (N / D) ^ 2 := by field_simp
  have e2 : -2 * N * (-N * u / D - N) = 2 * D * (D + u) * (N / D) ^ 2 := by field_simp; ring
  have hND : N / D ≠ 0 := div_ne_zero hN hD
  rw [IsQuarterX, e1, e2, isSquare_mul_sq_iff hND, isSquare_mul_sq_iff hND]

section Cuboid

variable {a b c d e f g : ℚ}

/-- **Cuboid side, third derived triangle `(cg, ab, ef)`.** The third configuration point of a
rational perfect cuboid is a quarter point iff `cg(ef + ab)` and `2(ef + ab)(ef + ab + cg)` are
rational squares. In half-angle form `ef + ab = k(m + n)²`, `cg = k(m² − n²)` (odd-leg case) the
two conditions read `(m − n)(m + n) = □` and `m(m + n) = □`. -/
theorem IsRatCuboid.quarter_iff (h : IsRatCuboid a b c d e f g) (hN : 0 < N) :
    IsQuarterX N (-N * (c * g) / (e * f + a * b)) ↔
      IsSquare (c * g * (e * f + a * b)) ∧
        IsSquare (2 * (e * f + a * b) * (e * f + a * b + c * g)) := by
  have := h.pos_a; have := h.pos_b; have := h.pos_e; have := h.pos_f
  exact isQuarterX_frac_iff hN.ne' (by positivity)

/-- Cuboid side, first derived triangle `(ag, bc, de)`. -/
theorem IsRatCuboid.quarter_iff₁ (h : IsRatCuboid a b c d e f g) (hN : 0 < N) :
    IsQuarterX N (-N * (a * g) / (d * e + b * c)) ↔
      IsSquare (a * g * (d * e + b * c)) ∧
        IsSquare (2 * (d * e + b * c) * (d * e + b * c + a * g)) := by
  have := h.pos_b; have := h.pos_c; have := h.pos_d; have := h.pos_e
  exact isQuarterX_frac_iff hN.ne' (by positivity)

/-- Cuboid side, second derived triangle `(bg, ac, df)`. -/
theorem IsRatCuboid.quarter_iff₂ (h : IsRatCuboid a b c d e f g) (hN : 0 < N) :
    IsQuarterX N (-N * (b * g) / (d * f + a * c)) ↔
      IsSquare (b * g * (d * f + a * c)) ∧
        IsSquare (2 * (d * f + a * c) * (d * f + a * c + b * g)) := by
  have := h.pos_a; have := h.pos_c; have := h.pos_d; have := h.pos_f
  exact isQuarterX_frac_iff hN.ne' (by positivity)

/-- Relabelling `(a, b, c) ↦ (b, c, a)`. -/
theorem IsRatCuboid.cycle (h : IsRatCuboid a b c d e f g) : IsRatCuboid b c a f d e g :=
  ⟨h.pos_b, h.pos_c, h.pos_a, h.pos_f, h.pos_d, h.pos_e, h.pos_g, h.hf,
    by linear_combination h.hd, by linear_combination h.he, by linear_combination h.hg⟩

/-- Relabelling `(a, b, c) ↦ (a, c, b)`. -/
theorem IsRatCuboid.swap (h : IsRatCuboid a b c d e f g) : IsRatCuboid a c b e d f g :=
  ⟨h.pos_a, h.pos_c, h.pos_b, h.pos_e, h.pos_d, h.pos_f, h.pos_g, h.he, h.hd,
    by linear_combination h.hf, by linear_combination h.hg⟩

end Cuboid

/-! ### The round trip: configuration → cuboid → the same configuration -/

/-- On the egg `−N < x < 0` the abscissa is determined by `x/(N² − x²)`, hence by `edge²`. -/
theorem eq_of_edge_sq_eq (hN : 0 < N) {x x' y y' : ℚ} (hx : x < 0) (hxN : -N < x) (hx' : x' < 0)
    (hxN' : -N < x') (hy : y ^ 2 = x ^ 3 - N ^ 2 * x) (hy' : y' ^ 2 = x' ^ 3 - N ^ 2 * x')
    (he : edge N x y ^ 2 = edge N x' y' ^ 2) : x = x' := by
  rw [edge_sq hN hx hxN hy, edge_sq hN hx' hxN' hy'] at he
  have h1 := (sub_sq_pos hN hx hxN).ne'
  have h2 := (sub_sq_pos hN hx' hxN').ne'
  field_simp at he
  have hpos : 0 < N ^ 2 + x * x' := by nlinarith
  have : (x - x') * (N ^ 2 + x * x') = 0 := by linear_combination -he
  linarith [(mul_eq_zero.mp this).resolve_right hpos.ne']

/-- **Round trip.** Every positive configuration is the configuration of a rational perfect cuboid
(`isConfigPts_of_cuboid`) with the same `N`: the cuboid with edges `|Uᵢ|` of
`IsConfigPts.exists_isRatCuboid`, with `s = |U₁U₂U₃|/(2N)`. -/
theorem IsConfigPts.exists_cuboid {x₁ x₂ x₃ y₁ y₂ y₃ : ℚ} (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) :
    ∃ a b c d e f g s : ℚ, IsRatCuboid a b c d e f g ∧ a * b * c * g = 2 * N * s ^ 2 ∧
      -N * (a * g) / (d * e + b * c) = x₁ ∧ -N * (b * g) / (d * f + a * c) = x₂ ∧
      -N * (c * g) / (e * f + a * b) = x₃ := by
  have hN := hc.pos
  obtain ⟨d, e, f, g, h⟩ := hc.exists_isRatCuboid
  set U₁ := edge N x₁ y₁ with hU₁
  set U₂ := edge N x₂ y₂ with hU₂
  set U₃ := edge N x₃ y₃ with hU₃
  have hsp := hc.space
  have hg : g = |U₁| * |U₂| * |U₃| / (2 * N) := by
    have h1 : g ^ 2 = (|U₁| * |U₂| * |U₃| / (2 * N)) ^ 2 := by
      rw [h.hg, sq_abs, sq_abs, sq_abs, div_pow, mul_pow, mul_pow, sq_abs, sq_abs, sq_abs,
        ← mul_pow, ← mul_pow, ← div_pow]
      exact hsp
    have h2 : 0 ≤ |U₁| * |U₂| * |U₃| / (2 * N) := by positivity
    exact (pow_left_inj₀ h.pos_g.le h2 two_ne_zero).mp h1
  set s := |U₁| * |U₂| * |U₃| / (2 * N) with hs_def
  have hs : |U₁| * |U₂| * |U₃| * g = 2 * N * s ^ 2 := by
    rw [hg, hs_def]; field_simp
  have hcfg := isConfigPts_of_cuboid h hN hs
  have hN0 := hN.ne'
  have ha := h.pos_a.ne'; have hb := h.pos_b.ne'; have hcc := h.pos_c.ne'
  have := h.pos_a; have := h.pos_b; have := h.pos_c; have := h.pos_d; have := h.pos_e
  have := h.pos_f; have := h.pos_g
  refine ⟨_, _, _, d, e, f, g, s, h, hs, ?_, ?_, ?_⟩
  · refine (eq_of_edge_sq_eq hN hcfg.neg₁ hcfg.lt₁ hc.neg₁ hc.lt₁ hcfg.hy₁ hc.hy₁ ?_)
    rw [edge_of_cuboid h.hd h.he h.hg hN0 hb hcc (by positivity), ← sq_abs U₁, hs_def]
    field_simp
  · have hd' : d ^ 2 = |U₂| ^ 2 + |U₁| ^ 2 := by linear_combination h.hd
    have hg' : g ^ 2 = |U₂| ^ 2 + |U₁| ^ 2 + |U₃| ^ 2 := by linear_combination h.hg
    refine (eq_of_edge_sq_eq hN hcfg.neg₂ hcfg.lt₂ hc.neg₂ hc.lt₂ hcfg.hy₂ hc.hy₂ ?_)
    rw [edge_of_cuboid hd' h.hf hg' hN0 ha hcc (by positivity), ← sq_abs U₂, hs_def]
    field_simp
  · have he' : e ^ 2 = |U₃| ^ 2 + |U₁| ^ 2 := by linear_combination h.he
    have hf' : f ^ 2 = |U₃| ^ 2 + |U₂| ^ 2 := by linear_combination h.hf
    have hg' : g ^ 2 = |U₃| ^ 2 + |U₁| ^ 2 + |U₂| ^ 2 := by linear_combination h.hg
    refine (eq_of_edge_sq_eq hN hcfg.neg₃ hcfg.lt₃ hc.neg₃ hc.lt₃ hcfg.hy₃ hc.hy₃ ?_)
    rw [edge_of_cuboid he' hf' hg' hN0 ha hb (by positivity), ← sq_abs U₃, hs_def]
    field_simp


/-! ### `QuarterFree` as a statement about rational perfect cuboids -/

/-- **`QuarterFree N` is a statement about rational perfect cuboids** (third derived triangle):
`E_N` has no positive configuration with a quarter point iff no rational perfect cuboid with
`abcg = 2Ns²` has `cg(ef + ab)` and `2(ef + ab)(ef + ab + cg)` both squares. -/
theorem quarterFree_iff (hN : 0 < N) :
    QuarterFree N ↔ ∀ ⦃a b c d e f g s : ℚ⦄, IsRatCuboid a b c d e f g →
      a * b * c * g = 2 * N * s ^ 2 →
      ¬ (IsSquare (c * g * (e * f + a * b)) ∧
        IsSquare (2 * (e * f + a * b) * (e * f + a * b + c * g))) := by
  constructor
  · intro hq a b c d e f g s h hs hsq
    exact hq (isConfigPts_of_cuboid h hN hs) ((IsRatCuboid.quarter_iff h hN).mpr hsq)
  · intro H x₁ x₂ x₃ y₁ y₂ y₃ hc hx
    obtain ⟨a, b, c, d, e, f, g, s, h, hs, -, -, h3⟩ := IsConfigPts.exists_cuboid hc
    rw [← h3] at hx
    exact H h hs ((IsRatCuboid.quarter_iff h hN).mp hx)

/-- The same with the first derived triangle `(ag, bc, de)`. -/
theorem quarterFree_iff₁ (hN : 0 < N) :
    QuarterFree N ↔ ∀ ⦃a b c d e f g s : ℚ⦄, IsRatCuboid a b c d e f g →
      a * b * c * g = 2 * N * s ^ 2 →
      ¬ (IsSquare (a * g * (d * e + b * c)) ∧
        IsSquare (2 * (d * e + b * c) * (d * e + b * c + a * g))) := by
  rw [quarterFree_iff hN]
  constructor
  · intro H a b c d e f g s h hs
    exact H (IsRatCuboid.cycle h) (s := s) (by linear_combination hs)
  · intro H a b c d e f g s h hs
    exact H (IsRatCuboid.cycle (IsRatCuboid.cycle h)) (s := s) (by linear_combination hs)

/-- The same with the second derived triangle `(bg, ac, df)`. -/
theorem quarterFree_iff₂ (hN : 0 < N) :
    QuarterFree N ↔ ∀ ⦃a b c d e f g s : ℚ⦄, IsRatCuboid a b c d e f g →
      a * b * c * g = 2 * N * s ^ 2 →
      ¬ (IsSquare (b * g * (d * f + a * c)) ∧
        IsSquare (2 * (d * f + a * c) * (d * f + a * c + b * g))) := by
  rw [quarterFree_iff hN]
  constructor
  · intro H a b c d e f g s h hs
    exact H (IsRatCuboid.swap h) (s := s) (by linear_combination hs)
  · intro H a b c d e f g s h hs
    exact H (IsRatCuboid.swap h) (s := s) (by linear_combination hs)

/-- **Rank one excluded by a cuboid-side square condition.** If no rational perfect cuboid with
`abcg = 2Ns²` has `cg(ef + ab)` and `2(ef + ab)(ef + ab + cg)` both squares, then no positive
configuration on `E_N` lies in a subgroup of rank one. -/
theorem not_inRankOne_of_cuboid {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃)
    (H : ∀ ⦃a b c d e f g s : ℚ⦄, IsRatCuboid a b c d e f g →
      a * b * c * g = 2 * N * s ^ 2 →
      ¬ (IsSquare (c * g * (e * f + a * b)) ∧
        IsSquare (2 * (e * f + a * b) * (e * f + a * b + c * g))))
    {Q₁ Q₂ Q₃ : (curve N).Point} (h₁ : HasX Q₁ x₁) (h₂ : HasX Q₂ x₂) (h₃ : HasX Q₃ x₃) :
    ¬ InRankOne Q₁ Q₂ Q₃ :=
  not_inRankOne_of_quarterFree hc ((quarterFree_iff hc.pos).mpr H) h₁ h₂ h₃

/-! ### The other cosets of `2E_N(ℚ)` -/

/-- Points of `2E_N(ℚ)`: all three classes trivial. -/
theorem two_smul_hasX (hN : N ≠ 0) (R : (curve N).Point) {x : ℚ} (h : HasX (2 • R) x) :
    IsSquare x ∧ IsSquare (x - N) ∧ IsSquare (x + N) := by
  obtain ⟨x₀, hx₀, h1, h2, h3⟩ := two_smul_classes hN R h.ne_zero
  obtain rfl := hx₀.unique h
  exact ⟨h1, h2, h3⟩

/-- Points of `S + 2E_N(ℚ)`: classes `(−1, −N, N)`. -/
theorem two_smul_add_S (hN : 0 < N) (R : (curve N).Point) {x : ℚ}
    (h : HasX (S hN.ne' + 2 • R) x) :
    IsSquare (-x) ∧ IsSquare (-N * (x - N)) ∧ IsSquare (N * (x + N)) := by
  by_cases h0 : 2 • R = 0
  · rw [h0, add_zero] at h
    rw [h.unique ⟨_, _, rfl⟩]
    exact ⟨⟨0, by ring⟩, ⟨N, by ring⟩, ⟨N, by ring⟩⟩
  · obtain ⟨x₀, hx₀, h1, h2, h3⟩ := two_smul_classes hN.ne' R h0
    have hne : x₀ ≠ 0 := by
      rintro rfl
      obtain ⟨r, hr⟩ := h3
      obtain ⟨t, ht⟩ := h2
      nlinarith [mul_self_nonneg r, mul_self_nonneg t]
    obtain ⟨x', hx', q1, q2, q3⟩ := add_S_classes hN.ne' hx₀ hne h1 h2 h3
    obtain rfl := hx'.unique h
    exact ⟨q1, q2, q3⟩

/-- Points of `T + 2E_N(ℚ)`: classes `(N, 2, 2N)`. -/
theorem two_smul_add_T (hN : 0 < N) (R : (curve N).Point) {x : ℚ}
    (h : HasX (2 • R + T hN.ne') x) :
    IsSquare (N * x) ∧ IsSquare (2 * (x - N)) ∧ IsSquare (2 * N * (x + N)) := by
  by_cases h0 : 2 • R = 0
  · rw [h0, zero_add] at h
    rw [h.unique ⟨_, _, rfl⟩]
    exact ⟨⟨N, by ring⟩, ⟨0, by ring⟩, ⟨2 * N, by ring⟩⟩
  · obtain ⟨x₀, hx₀, h1, h2, h3⟩ := two_smul_classes hN.ne' R h0
    have hne : x₀ ≠ N := by
      rintro rfl
      obtain ⟨r, hr⟩ := h1
      obtain ⟨t, ht⟩ := h2
      -- `N` and `0` squares are fine; but then `2N = x₀ + N` is a square and `N` too: `2 = □`
      obtain ⟨u, hu⟩ := h3
      have hr0 : r ≠ 0 := by rintro rfl; exact hN.ne' (by rw [hr]; ring)
      have : (u / r) ^ 2 = 2 := by
        field_simp
        linear_combination -hu + 2 * hr
      exact sq_ne_two _ this
    obtain ⟨x', hx', q1, q2, q3⟩ := add_T_classes hN.ne' hx₀ hne h1 h2 h3
    obtain rfl := hx'.unique h
    exact ⟨q1, q2, q3⟩

/-- An egg point (`−N < x < 0`) is neither in `2E_N(ℚ)` nor in `T + 2E_N(ℚ)`. -/
theorem egg_not_two_smul (hN : 0 < N) {x : ℚ} (hx : x < 0) (R : (curve N).Point) :
    ¬ HasX (2 • R) x ∧ ¬ HasX (2 • R + T hN.ne') x := by
  constructor
  · intro h
    obtain ⟨⟨r, hr⟩, -, -⟩ := two_smul_hasX hN.ne' R h
    nlinarith [mul_self_nonneg r]
  · intro h
    obtain ⟨⟨r, hr⟩, -, -⟩ := two_smul_add_T hN R h
    nlinarith [mul_self_nonneg r, mul_pos hN (neg_pos.mpr hx)]

/-! ### Pigeonhole: a pair relation in every rank-one configuration -/

theorem sub_mem_of_even {G R₁ R₂ : (curve N).Point} {k₁ k₂ : ℤ} (hR₁ : R₁ + R₁ = 0)
    (hR₂ : R₂ + R₂ = 0) (hk : Even (k₁ - k₂)) :
    ∃ W R : (curve N).Point, R + R = 0 ∧ (k₁ • G + R₁) - (k₂ • G + R₂) = 2 • W + R := by
  obtain ⟨m, hm⟩ := hk
  refine ⟨m • G, R₁ - R₂, ?_, ?_⟩
  · have : R₁ - R₂ + (R₁ - R₂) = (R₁ + R₁) - (R₂ + R₂) := by abel
    rw [this, hR₁, hR₂, sub_zero]
  · have : k₁ = k₂ + (m + m) := by omega
    rw [this, add_zsmul, add_zsmul, two_nsmul]
    abel

/-- **Pair relation (point level).** If `Q₁, Q₂, Q₃ ∈ ℤG + E_N[2]`, then for some pair `i ≠ j`,
`Qᵢ − Qⱼ ∈ E_N[2] + 2E_N(ℚ)`: two of the three indices have the same parity. -/
theorem inRankOne_pair {Q₁ Q₂ Q₃ : (curve N).Point} (hQ : InRankOne Q₁ Q₂ Q₃) :
    ∃ W R : (curve N).Point, R + R = 0 ∧
      (Q₁ - Q₂ = 2 • W + R ∨ Q₁ - Q₃ = 2 • W + R ∨ Q₂ - Q₃ = 2 • W + R) := by
  obtain ⟨G, k₁, k₂, k₃, R₁, R₂, R₃, hR₁, hR₂, hR₃, rfl, rfl, rfl⟩ := hQ
  by_cases h12 : Even (k₁ - k₂)
  · obtain ⟨W, R, hR, h⟩ := sub_mem_of_even (G := G) hR₁ hR₂ h12
    exact ⟨W, R, hR, .inl h⟩
  by_cases h13 : Even (k₁ - k₃)
  · obtain ⟨W, R, hR, h⟩ := sub_mem_of_even (G := G) hR₁ hR₃ h13
    exact ⟨W, R, hR, .inr (.inl h)⟩
  have h23 : Even (k₂ - k₃) := by
    rw [Int.even_sub] at *
    tauto
  obtain ⟨W, R, hR, h⟩ := sub_mem_of_even (G := G) hR₂ hR₃ h23
  exact ⟨W, R, hR, .inr (.inr h)⟩

end PerfectCuboid.Kummer
