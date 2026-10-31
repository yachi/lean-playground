module

public import LeanPlayground.PerfectCuboid.CongruentRank

/-!
# From a positive cuboid configuration back to a cuboid

`CongruentRank.lean` maps a perfect cuboid to a *positive cuboid configuration*: three points of
`E_N : Y² = X³ − N²X` with `−N < Xᵢ < 0` and `X₁X₂ + X₁X₃ + X₂X₃ = N²` (Asiryan,
arXiv:2610.10643, Proposition 1; Paulsen–West, Proposition 3.1). This file goes back.

Each point `(x, y)` of a configuration gives the right triangle with legs `U = 2Ny/(N² − x²)`,
`V = 2N/U` and hypotenuse `H = −y(N² + x²)/(x(N² − x²))` (`edge`, `hyp`), of area `N`. For a
configuration that comes from a cuboid with edges `a, b, c`, space diagonal `g` and
`abcg = 2Ns²`, the legs are `Uᵢ = 2Ns/(bc) = ag/s`, `bg/s`, `cg/s` (`edge_of_cuboid`), so the
configuration recovers the shape of the cuboid. In general:

* `IsConfigPts.space`: `U₁² + U₂² + U₃² = (U₁U₂U₃/(2N))²`, so the box with edges `|Uᵢ|` always has
  a rational space diagonal;
* `IsConfigPts.face₁₃`, `IsConfigPts.face₂₃`: `(U₁² + U₃²) H₂² = (U₁² + U₂²) H₃²` and
  `(U₂² + U₃²) H₁² = (U₁² + U₂²) H₃²`, so if one face diagonal is rational, all three are.

So a configuration gives a rational perfect cuboid **exactly when `U₁² + U₂²` is a square**
(`IsConfigPts.isRatCuboid_iff`). This square condition does not follow from these identities
alone, but it always holds: `TwistRigidity.lean` proves `IsConfigPts.isSquare_twist`, hence
`IsConfigPts.exists_isRatCuboid` and `exists_isPerfectCuboid_iff_exists_isConfigPts` (no square
condition). With the condition stated explicitly, the correspondence reads:

* `exists_isPerfectCuboid_iff`: a perfect cuboid exists if and only if, for some `N > 0`, `E_N`
  has a positive cuboid configuration with `U₁² + U₂²` a square.

All identities are polynomial identities modulo the curve equations and the compatibility
condition; the one behind `face₁₃` has the factor
`(N² + x₂x₃)(x₂ − x₃)(x₁x₂x₃ − N²(x₁ + x₂ + x₃))`.
-/

@[expose] public section

namespace PerfectCuboid.CongruentRank

variable {N : ℚ}

/-- The leg `U = 2Ny/(N² − x²)` of the right triangle of area `N` attached to `(x, y)`. -/
def edge (N x y : ℚ) : ℚ := 2 * N * y / (N ^ 2 - x ^ 2)

/-- The hypotenuse `H = −y(N² + x²)/(x(N² − x²))` of the same triangle. -/
def hyp (N x y : ℚ) : ℚ := -y * (N ^ 2 + x ^ 2) / (x * (N ^ 2 - x ^ 2))

section Point

variable {x y : ℚ}

theorem sub_sq_pos (hN : 0 < N) (hx : x < 0) (hxN : -N < x) : 0 < N ^ 2 - x ^ 2 := by
  nlinarith

theorem edge_sq (hN : 0 < N) (hx : x < 0) (hxN : -N < x) (hy : y ^ 2 = x ^ 3 - N ^ 2 * x) :
    edge N x y ^ 2 = -4 * N ^ 2 * x / (N ^ 2 - x ^ 2) := by
  have hD := (sub_sq_pos hN hx hxN).ne'
  rw [edge, div_pow, div_eq_div_iff (pow_ne_zero 2 hD) hD, mul_pow, hy]
  ring

theorem hyp_sq (hN : 0 < N) (hx : x < 0) (hxN : -N < x) (hy : y ^ 2 = x ^ 3 - N ^ 2 * x) :
    hyp N x y ^ 2 = -(N ^ 2 + x ^ 2) ^ 2 / (x * (N ^ 2 - x ^ 2)) := by
  have hD := (sub_sq_pos hN hx hxN).ne'
  rw [hyp, div_pow, neg_mul, neg_sq, mul_pow, hy]
  field_simp
  ring

theorem y_ne_zero (hN : 0 < N) (hx : x < 0) (hxN : -N < x) (hy : y ^ 2 = x ^ 3 - N ^ 2 * x) :
    y ≠ 0 := by
  rintro rfl
  have := sub_sq_pos hN hx hxN
  have : x ^ 3 - N ^ 2 * x = -x * (N ^ 2 - x ^ 2) := by ring
  nlinarith

theorem edge_ne_zero (hN : 0 < N) (hx : x < 0) (hxN : -N < x)
    (hy : y ^ 2 = x ^ 3 - N ^ 2 * x) : edge N x y ≠ 0 :=
  div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hN.ne') (y_ne_zero hN hx hxN hy))
    (sub_sq_pos hN hx hxN).ne'

theorem hyp_ne_zero (hN : 0 < N) (hx : x < 0) (hxN : -N < x) (hy : y ^ 2 = x ^ 3 - N ^ 2 * x) :
    hyp N x y ≠ 0 := by
  have : 0 < N ^ 2 + x ^ 2 := by positivity
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (y_ne_zero hN hx hxN hy)) this.ne')
    (mul_ne_zero hx.ne (sub_sq_pos hN hx hxN).ne')

end Point

section Config

variable {x₁ x₂ x₃ y₁ y₂ y₃ : ℚ}

/-- The polynomial identity behind `IsConfig.space`. -/
theorem space_poly (h : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = N ^ 2) :
    x₁ * (N ^ 2 - x₂ ^ 2) * (N ^ 2 - x₃ ^ 2) + x₂ * (N ^ 2 - x₁ ^ 2) * (N ^ 2 - x₃ ^ 2) +
      x₃ * (N ^ 2 - x₁ ^ 2) * (N ^ 2 - x₂ ^ 2) = 4 * N ^ 2 * (x₁ * x₂ * x₃) := by
  linear_combination (x₁ * x₂ * x₃ - N ^ 2 * (x₁ + x₂ + x₃)) * h

/-- The polynomial identity behind `IsConfig.face₁₃`. -/
theorem face_poly (h : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = N ^ 2) :
    x₃ * (x₁ * (N ^ 2 - x₃ ^ 2) + x₃ * (N ^ 2 - x₁ ^ 2)) * (N ^ 2 + x₂ ^ 2) ^ 2 =
      x₂ * (x₁ * (N ^ 2 - x₂ ^ 2) + x₂ * (N ^ 2 - x₁ ^ 2)) * (N ^ 2 + x₃ ^ 2) ^ 2 := by
  linear_combination
    (-(N ^ 2 + x₂ * x₃) * (x₂ - x₃) * (x₁ * x₂ * x₃ - N ^ 2 * (x₁ + x₂ + x₃))) * h

/-- The three points of a positive configuration, with their `Y`-coordinates. -/
structure IsConfigPts (N x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) : Prop extends IsConfig N x₁ x₂ x₃ where
  hy₁ : y₁ ^ 2 = x₁ ^ 3 - N ^ 2 * x₁
  hy₂ : y₂ ^ 2 = x₂ ^ 3 - N ^ 2 * x₂
  hy₃ : y₃ ^ 2 = x₃ ^ 3 - N ^ 2 * x₃

namespace IsConfigPts

variable (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃)
include hc

/-- Swapping the second and third point. -/
theorem swap₂₃ : IsConfigPts N x₁ x₃ x₂ y₁ y₃ y₂ :=
  ⟨⟨hc.pos, hc.lt₁, hc.lt₃, hc.lt₂, hc.neg₁, hc.neg₃, hc.neg₂,
    by linear_combination hc.compat⟩, hc.hy₁, hc.hy₃, hc.hy₂⟩

/-- Swapping the first and second point. -/
theorem swap₁₂ : IsConfigPts N x₂ x₁ x₃ y₂ y₁ y₃ :=
  ⟨⟨hc.pos, hc.lt₂, hc.lt₁, hc.lt₃, hc.neg₂, hc.neg₁, hc.neg₃,
    by linear_combination hc.compat⟩, hc.hy₂, hc.hy₁, hc.hy₃⟩

/-- **The space diagonal is always rational:** `U₁² + U₂² + U₃² = (U₁U₂U₃/(2N))²`. -/
theorem space :
    edge N x₁ y₁ ^ 2 + edge N x₂ y₂ ^ 2 + edge N x₃ y₃ ^ 2 =
      (edge N x₁ y₁ * edge N x₂ y₂ * edge N x₃ y₃ / (2 * N)) ^ 2 := by
  have hN := hc.pos
  have hD₁ := (sub_sq_pos hN hc.neg₁ hc.lt₁).ne'
  have hD₂ := (sub_sq_pos hN hc.neg₂ hc.lt₂).ne'
  have hD₃ := (sub_sq_pos hN hc.neg₃ hc.lt₃).ne'
  rw [div_pow, mul_pow, mul_pow, edge_sq hN hc.neg₁ hc.lt₁ hc.hy₁,
    edge_sq hN hc.neg₂ hc.lt₂ hc.hy₂, edge_sq hN hc.neg₃ hc.lt₃ hc.hy₃]
  set D₁ := N ^ 2 - x₁ ^ 2
  set D₂ := N ^ 2 - x₂ ^ 2
  set D₃ := N ^ 2 - x₃ ^ 2
  have e₁ : -4 * N ^ 2 * x₁ / D₁ + -4 * N ^ 2 * x₂ / D₂ + -4 * N ^ 2 * x₃ / D₃ =
      -4 * N ^ 2 * (x₁ * D₂ * D₃ + x₂ * D₁ * D₃ + x₃ * D₁ * D₂) / (D₁ * D₂ * D₃) := by
    field_simp
    ring
  have e₂ : -4 * N ^ 2 * x₁ / D₁ * (-4 * N ^ 2 * x₂ / D₂) * (-4 * N ^ 2 * x₃ / D₃) /
      (2 * N) ^ 2 = -4 * N ^ 2 * (4 * N ^ 2 * (x₁ * x₂ * x₃)) / (D₁ * D₂ * D₃) := by
    field_simp
    ring
  rw [e₁, e₂, space_poly hc.compat]

/-- `(U₁² + U₃²) H₂² = (U₁² + U₂²) H₃²`. -/
theorem face₁₃ :
    (edge N x₁ y₁ ^ 2 + edge N x₃ y₃ ^ 2) * hyp N x₂ y₂ ^ 2 =
      (edge N x₁ y₁ ^ 2 + edge N x₂ y₂ ^ 2) * hyp N x₃ y₃ ^ 2 := by
  have hN := hc.pos
  have hD₁ := (sub_sq_pos hN hc.neg₁ hc.lt₁).ne'
  have hD₂ := (sub_sq_pos hN hc.neg₂ hc.lt₂).ne'
  have hD₃ := (sub_sq_pos hN hc.neg₃ hc.lt₃).ne'
  have hx₂ := hc.neg₂.ne
  have hx₃ := hc.neg₃.ne
  rw [edge_sq hN hc.neg₁ hc.lt₁ hc.hy₁, edge_sq hN hc.neg₂ hc.lt₂ hc.hy₂,
    edge_sq hN hc.neg₃ hc.lt₃ hc.hy₃, hyp_sq hN hc.neg₂ hc.lt₂ hc.hy₂,
    hyp_sq hN hc.neg₃ hc.lt₃ hc.hy₃]
  set D₁ := N ^ 2 - x₁ ^ 2
  set D₂ := N ^ 2 - x₂ ^ 2
  set D₃ := N ^ 2 - x₃ ^ 2
  have e₁ : (-4 * N ^ 2 * x₁ / D₁ + -4 * N ^ 2 * x₃ / D₃) * (-(N ^ 2 + x₂ ^ 2) ^ 2 / (x₂ * D₂)) =
      4 * N ^ 2 * ((x₁ * D₃ + x₃ * D₁) * (N ^ 2 + x₂ ^ 2) ^ 2) / (D₁ * D₃ * (x₂ * D₂)) := by
    field_simp
    ring
  have e₂ : (-4 * N ^ 2 * x₁ / D₁ + -4 * N ^ 2 * x₂ / D₂) * (-(N ^ 2 + x₃ ^ 2) ^ 2 / (x₃ * D₃)) =
      4 * N ^ 2 * ((x₁ * D₂ + x₂ * D₁) * (N ^ 2 + x₃ ^ 2) ^ 2) / (D₁ * D₂ * (x₃ * D₃)) := by
    field_simp
    ring
  rw [e₁, e₂, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination 4 * N ^ 2 * (D₁ * D₂ * D₃) * face_poly hc.compat

/-- `(U₂² + U₃²) H₁² = (U₁² + U₂²) H₃²`. -/
theorem face₂₃ :
    (edge N x₂ y₂ ^ 2 + edge N x₃ y₃ ^ 2) * hyp N x₁ y₁ ^ 2 =
      (edge N x₁ y₁ ^ 2 + edge N x₂ y₂ ^ 2) * hyp N x₃ y₃ ^ 2 := by
  have := hc.swap₁₂.face₁₃
  linear_combination this

end IsConfigPts

end Config

/-- A rational perfect cuboid: positive rational edges `a, b, c` with rational face diagonals
`d, e, f` and space diagonal `g`. -/
structure IsRatCuboid (a b c d e f g : ℚ) : Prop where
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  pos_d : 0 < d
  pos_e : 0 < e
  pos_f : 0 < f
  pos_g : 0 < g
  hd : d ^ 2 = a ^ 2 + b ^ 2
  he : e ^ 2 = a ^ 2 + c ^ 2
  hf : f ^ 2 = b ^ 2 + c ^ 2
  hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2

/-- **Configuration to cuboid.** The box with edges `|U₁|, |U₂|, |U₃|` of a positive configuration
is a rational perfect cuboid if and only if `U₁² + U₂²` is a square. -/
theorem IsConfigPts.isRatCuboid_iff {x₁ x₂ x₃ y₁ y₂ y₃ : ℚ}
    (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) :
    (∃ d e f g, IsRatCuboid |edge N x₁ y₁| |edge N x₂ y₂| |edge N x₃ y₃| d e f g) ↔
      IsSquare (edge N x₁ y₁ ^ 2 + edge N x₂ y₂ ^ 2) := by
  have hN := hc.pos
  have hU₁ := edge_ne_zero hN hc.neg₁ hc.lt₁ hc.hy₁
  have hU₂ := edge_ne_zero hN hc.neg₂ hc.lt₂ hc.hy₂
  have hU₃ := edge_ne_zero hN hc.neg₃ hc.lt₃ hc.hy₃
  have hH₁ := hyp_ne_zero hN hc.neg₁ hc.lt₁ hc.hy₁
  have hH₂ := hyp_ne_zero hN hc.neg₂ hc.lt₂ hc.hy₂
  have hH₃ := hyp_ne_zero hN hc.neg₃ hc.lt₃ hc.hy₃
  constructor
  · rintro ⟨d, e, f, g, h⟩
    exact ⟨d, by rw [← sq, h.hd, sq_abs, sq_abs]⟩
  · rintro ⟨d, hd⟩
    rw [← sq] at hd
    set U₁ := edge N x₁ y₁
    set U₂ := edge N x₂ y₂
    set U₃ := edge N x₃ y₃
    set H₁ := hyp N x₁ y₁
    set H₂ := hyp N x₂ y₂
    set H₃ := hyp N x₃ y₃
    have hd0 : d ≠ 0 := by
      rintro rfl
      have : 0 < U₁ ^ 2 + U₂ ^ 2 := by positivity
      rw [hd] at this
      simp at this
    have he : (d * H₃ / H₂) ^ 2 = U₁ ^ 2 + U₃ ^ 2 := by
      have := hc.face₁₃
      field_simp
      linear_combination -this - H₃ ^ 2 * hd
    have hf : (d * H₃ / H₁) ^ 2 = U₂ ^ 2 + U₃ ^ 2 := by
      have := hc.face₂₃
      field_simp
      linear_combination -this - H₃ ^ 2 * hd
    refine ⟨|d|, |d * H₃ / H₂|, |d * H₃ / H₁|, |U₁ * U₂ * U₃ / (2 * N)|,
      ⟨by positivity, by positivity, by positivity, by positivity, by positivity,
        by positivity, by positivity, ?_, ?_, ?_, ?_⟩⟩
    · rw [sq_abs, sq_abs, sq_abs, hd]
    · rw [sq_abs, sq_abs, sq_abs, he]
    · rw [sq_abs, sq_abs, sq_abs, hf]
    · rw [sq_abs, sq_abs, sq_abs, sq_abs, ← hc.space]

end PerfectCuboid.CongruentRank

namespace PerfectCuboid.CongruentRank

section Cuboid

variable {a b c d e f g s : ℚ}

/-- The leg `U` of the point that Proposition 1 attaches to the edge `a` is `2Ns/(bc)`. -/
theorem edge_of_cuboid (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) (hN : N ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hh : d * e + b * c ≠ 0) :
    edge N (-N * (a * g) / (d * e + b * c)) (N ^ 2 * (2 * s) / (d * e + b * c)) =
      2 * N * s / (b * c) := by
  have key := sq_sub_sq_eq hd he hg
  have hD : N ^ 2 - (-N * (a * g) / (d * e + b * c)) ^ 2 =
      N ^ 2 * (2 * (b * c) * (d * e + b * c)) / (d * e + b * c) ^ 2 := by
    rw [← key]
    field_simp
  rw [edge, hD]
  field_simp

/-- **Asiryan, Proposition 1, with the points named.** A rational perfect cuboid with
`abcg = 2Ns²` gives the configuration `Xᵢ = −N·ag/(de + bc), −N·bg/(df + ac), −N·cg/(ef + ab)`,
`Yᵢ = 2N²s/(de + bc), …`. -/
theorem isConfigPts_of_cuboid (h : IsRatCuboid a b c d e f g) (hN : 0 < N)
    (hs : a * b * c * g = 2 * N * s ^ 2) :
    IsConfigPts N (-N * (a * g) / (d * e + b * c)) (-N * (b * g) / (d * f + a * c))
      (-N * (c * g) / (e * f + a * b)) (N ^ 2 * (2 * s) / (d * e + b * c))
      (N ^ 2 * (2 * s) / (d * f + a * c)) (N ^ 2 * (2 * s) / (e * f + a * b)) := by
  have := h.pos_a; have := h.pos_b; have := h.pos_c; have := h.pos_d; have := h.pos_e
  have := h.pos_f; have := h.pos_g
  have h₁ : 0 < d * e + b * c := by positivity
  have h₂ : 0 < d * f + a * c := by positivity
  have h₃ : 0 < e * f + a * b := by positivity
  have hd' : d ^ 2 = b ^ 2 + a ^ 2 := by linear_combination h.hd
  have hg₂ : g ^ 2 = b ^ 2 + a ^ 2 + c ^ 2 := by linear_combination h.hg
  have hg₃ : g ^ 2 = c ^ 2 + a ^ 2 + b ^ 2 := by linear_combination h.hg
  have he' : e ^ 2 = c ^ 2 + a ^ 2 := by linear_combination h.he
  have hf' : f ^ 2 = c ^ 2 + b ^ 2 := by linear_combination h.hf
  have hs₂ : b * a * c * g = 2 * N * s ^ 2 := by linear_combination hs
  have hs₃ : c * a * b * g = 2 * N * s ^ 2 := by linear_combination hs
  have b₁ := cuboid_point_bounds h.pos_a h.pos_b h.pos_c h.pos_d h.pos_e h.pos_g hN h.hd h.he h.hg
  have b₂ := cuboid_point_bounds h.pos_b h.pos_a h.pos_c h.pos_d h.pos_f h.pos_g hN hd' h.hf hg₂
  have b₃ := cuboid_point_bounds h.pos_c h.pos_a h.pos_b h.pos_e h.pos_f h.pos_g hN he' hf' hg₃
  refine ⟨⟨hN, b₁.1, b₂.1, b₃.1, b₁.2, b₂.2, b₃.2, ?_⟩,
    cuboid_point_eq h.hd h.he h.hg hs h₁.ne', cuboid_point_eq hd' h.hf hg₂ hs₂ h₂.ne',
    cuboid_point_eq he' hf' hg₃ hs₃ h₃.ne'⟩
  have key := cuboid_compat h.hd h.he h.hf h.hg
  field_simp
  linear_combination key

/-- A rational perfect cuboid gives an integer one, by clearing denominators. -/
theorem IsRatCuboid.exists_isPerfectCuboid (h : IsRatCuboid a b c d e f g) :
    ∃ A B C : ℕ, IsPerfectCuboid A B C := by
  set M : ℕ := a.den * b.den * c.den * d.den * e.den * f.den * g.den with hMdef
  have hM : 0 < M := by positivity
  have nat {q : ℚ} (hq : 0 < q) (k : ℕ) (hk : M = q.den * k) :
      ∃ n : ℕ, 0 < n ∧ (n : ℚ) = M * q := by
    have hn := Rat.num_pos.mpr hq
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h0
      · omega
      · exact h0
    refine ⟨k * q.num.toNat, Nat.mul_pos hk0 (by omega), ?_⟩
    have h1 : ((q.num.toNat : ℕ) : ℚ) = q.num := by exact_mod_cast Int.toNat_of_nonneg hn.le
    rw [hk]
    push_cast
    rw [h1, ← Rat.mul_den_eq_num]
    ring
  obtain ⟨A, hA0, hA⟩ := nat h.pos_a (b.den * c.den * d.den * e.den * f.den * g.den)
    (by rw [hMdef]; ring)
  obtain ⟨B, hB0, hB⟩ := nat h.pos_b (a.den * c.den * d.den * e.den * f.den * g.den)
    (by rw [hMdef]; ring)
  obtain ⟨C, hC0, hC⟩ := nat h.pos_c (a.den * b.den * d.den * e.den * f.den * g.den)
    (by rw [hMdef]; ring)
  obtain ⟨D, -, hD⟩ := nat h.pos_d (a.den * b.den * c.den * e.den * f.den * g.den)
    (by rw [hMdef]; ring)
  obtain ⟨E, -, hE⟩ := nat h.pos_e (a.den * b.den * c.den * d.den * f.den * g.den)
    (by rw [hMdef]; ring)
  obtain ⟨F, -, hF⟩ := nat h.pos_f (a.den * b.den * c.den * d.den * e.den * g.den)
    (by rw [hMdef]; ring)
  obtain ⟨G, -, hG⟩ := nat h.pos_g (a.den * b.den * c.den * d.den * e.den * f.den)
    (by rw [hMdef]; ring)
  refine ⟨A, B, C, ⟨hA0, hB0, hC0, ⟨D, ?_⟩, ⟨F, ?_⟩, ⟨E, ?_⟩⟩, ⟨G, ?_⟩⟩
  · exact_mod_cast (show (A : ℚ) ^ 2 + B ^ 2 = D * D by
      rw [hA, hB, hD]; linear_combination (M : ℚ) ^ 2 * (-h.hd))
  · exact_mod_cast (show (B : ℚ) ^ 2 + C ^ 2 = F * F by
      rw [hB, hC, hF]; linear_combination (M : ℚ) ^ 2 * (-h.hf))
  · exact_mod_cast (show (C : ℚ) ^ 2 + A ^ 2 = E * E by
      rw [hC, hA, hE]; linear_combination (M : ℚ) ^ 2 * (-h.he))
  · exact_mod_cast (show (A : ℚ) ^ 2 + B ^ 2 + C ^ 2 = G * G by
      rw [hA, hB, hC, hG]; linear_combination (M : ℚ) ^ 2 * (-h.hg))

end Cuboid

/-- **The cuboid correspondence as an equivalence.** A perfect cuboid exists if and only if, for
some `N > 0`, the curve `E_N` has a positive cuboid configuration whose legs satisfy
`U₁² + U₂² = □`. The square condition is automatic (`CongruentRank.IsConfigPts.isSquare_twist`
in `TwistRigidity.lean`), see `exists_isPerfectCuboid_iff_exists_isConfigPts`. -/
theorem exists_isPerfectCuboid_iff :
    (∃ a b c : ℕ, IsPerfectCuboid a b c) ↔
      ∃ N x₁ x₂ x₃ y₁ y₂ y₃ : ℚ, IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃ ∧
        IsSquare (edge N x₁ y₁ ^ 2 + edge N x₂ y₂ ^ 2) := by
  constructor
  · rintro ⟨a, b, c, h⟩
    obtain ⟨d, hd⟩ := h.sq_ab
    obtain ⟨f, hf⟩ := h.sq_bc
    obtain ⟨e, he⟩ := h.sq_ca
    obtain ⟨g, hg⟩ := h.sq_abc
    have pos {r m : ℕ} (hm : 0 < m) (hr : m = r * r) : (0 : ℚ) < r := by
      rcases Nat.eq_zero_or_pos r with rfl | hr' <;> [simp at hr; exact_mod_cast hr']
      omega
    have ha : (0 : ℚ) < a := by exact_mod_cast h.pos_a
    have hb : (0 : ℚ) < b := by exact_mod_cast h.pos_b
    have hc : (0 : ℚ) < c := by exact_mod_cast h.pos_c
    have := h.pos_a; have := h.pos_b
    have R : IsRatCuboid a b c d e f g :=
      ⟨ha, hb, hc, pos (by positivity) hd, pos (by positivity) he, pos (by positivity) hf,
        pos (by positivity) hg,
        by rw [sq]; exact_mod_cast hd.symm,
        by rw [sq]; linear_combination (by exact_mod_cast he.symm : (e : ℚ) * e = c ^ 2 + a ^ 2),
        by rw [sq]; exact_mod_cast hf.symm, by rw [sq]; exact_mod_cast hg.symm⟩
    -- take `N = abcg/2` and `s = 1`
    set N : ℚ := a * b * c * g / 2
    have hN : 0 < N := by have := R.pos_g; positivity
    have hs : (a : ℚ) * b * c * g = 2 * N * 1 ^ 2 := by simp only [N]; ring
    have hc' := isConfigPts_of_cuboid R hN hs
    refine ⟨_, _, _, _, _, _, _, hc', d * g, ?_⟩
    have hd' : (d : ℚ) ^ 2 = b ^ 2 + a ^ 2 := by linear_combination R.hd
    have hg₂ : (g : ℚ) ^ 2 = b ^ 2 + a ^ 2 + c ^ 2 := by linear_combination R.hg
    have hde : (0 : ℚ) < d * e + b * c := by have := R.pos_d; have := R.pos_e; positivity
    have hdf : (0 : ℚ) < d * f + a * c := by have := R.pos_d; have := R.pos_f; positivity
    rw [edge_of_cuboid R.hd R.he R.hg hN.ne' hb.ne' hc.ne' hde.ne',
      edge_of_cuboid hd' R.hf hg₂ hN.ne' ha.ne' hc.ne' hdf.ne']
    have e₁ : 2 * N * 1 / (b * c) = a * g := by simp only [N]; field_simp
    have e₂ : 2 * N * 1 / (a * c) = b * g := by simp only [N]; field_simp
    rw [e₁, e₂]
    linear_combination (-(g : ℚ) ^ 2) * R.hd
  · rintro ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc, hsq⟩
    obtain ⟨d, e, f, g, h⟩ := hc.isRatCuboid_iff.mpr hsq
    exact h.exists_isPerfectCuboid

end PerfectCuboid.CongruentRank
