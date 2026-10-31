module

public import LeanPlayground.PerfectCuboid.TwistedCuboid

/-!
# The twist of a configuration is `−X₁X₂X₃`

`TwistedCuboid.lean` shows that a positive cuboid configuration `(X₁, Y₁), (X₂, Y₂), (X₃, Y₃)` on
`E_N : Y² = X³ − N²X` is a `k`-twisted perfect cuboid with `k = U₁² + U₂²`, where
`Uᵢ = 2NYᵢ/(N² − Xᵢ²)`, and that it is a perfect cuboid exactly when `k` is a square. This file
computes the class of `k` in `ℚ*/ℚ*²` from the `X`-coordinates alone:

  `U₁² + U₂² = −X₁X₂X₃ · (2N(X₁ + X₂)/(Y₁Y₂))²`  (`IsConfigPts.twist_class`).

So **`k ≡ −X₁X₂X₃ (mod ℚ*²)`**. The proof: `Uᵢ² = −4N²Xᵢ/(N² − Xᵢ²)`, `Yᵢ² = −Xᵢ(N² − Xᵢ²)`, and
the compatibility condition `X₃(X₁ + X₂) = N² − X₁X₂` turns `X₁(N² − X₂²) + X₂(N² − X₁²)` into
`X₃(X₁ + X₂)²`.

* `IsConfigPts.isTwistedCuboid_iff_isSquare`: the box with edges `|U₁|, |U₂|, |U₃|` is a
  `k`-twisted perfect cuboid if and only if `k > 0` and `k · (−X₁X₂X₃)` is a square.
* `IsConfigPts.isRatCuboid_iff_isSquare`: it is a rational perfect cuboid if and only if
  `−X₁X₂X₃` is a square.
* `exists_isPerfectCuboid_iff'`: a perfect cuboid exists if and only if some `E_N` has a positive
  configuration with `−X₁X₂X₃ = □`. This replaces the condition `U₁² + U₂² = □` of
  `exists_isPerfectCuboid_iff`, which involves the `Y`-coordinates, by one on the `X`-coordinates.
* `exists_config_iff_exists_twistedCuboid'`: the same for every twist `k`.

In cuboid coordinates the identity reads

  `2(kde + bc)(kdf + ac)(kef + ab) = k g² (af + be + cd)²`  (`IsTwistedCuboid.twist_identity`),

and for a perfect cuboid `2(de + bc)(df + ac)(ef + ab) = g²(af + be + cd)²`
(`IsRatCuboid.twist_identity`). With it, the configuration that Asiryan's Proposition 1 attaches
to a `k`-twisted cuboid has `k · (−X₁X₂X₃) = (2N²s/(af + be + cd))²`
(`twist_class_of_twistedCuboid`).

Interpretation (not formalized here). On `E_N` the map `α(X, Y) = X mod ℚ*²` (with `α(T₀) = −1`
at `T₀ = (0, 0)`) is the connecting map of the `2`-isogeny descent, a homomorphism
`E_N(ℚ) → ℚ*/ℚ*²` with kernel `φ̂(E'_N(ℚ))`, `E'_N : Y² = X³ + 4N²X`. So the twist is
`k ≡ α(Q₁ + Q₂ + Q₃ + T₀)`, and a configuration is a perfect cuboid exactly when
`Q₁ + Q₂ + Q₃ + T₀ ∈ φ̂(E'_N(ℚ))`: a single `𝔽₂`-linear condition on Mordell–Weil coordinates.
It never excludes a configuration on its own; it says which twist class each configuration lands
in. By twist rigidity (`TwistRigidity.lean`, `IsConfigPts.isSquare_neg_prod`) every positive
configuration lands in the trivial class, so `Q₁ + Q₂ + Q₃ + T₀ ∈ φ̂(E'_N(ℚ))` is a consequence of
the configuration equations, not an extra constraint.
-/

@[expose] public section

namespace PerfectCuboid.CongruentRank

section Config

variable {N x₁ x₂ x₃ y₁ y₂ y₃ : ℚ}

/-- `−X₁X₂X₃ > 0` for a positive configuration. -/
theorem IsConfigPts.neg_prod_pos (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) :
    0 < -(x₁ * x₂ * x₃) := by
  have := mul_pos_of_neg_of_neg hc.neg₁ hc.neg₂
  have := mul_neg_of_pos_of_neg this hc.neg₃
  linarith

/-- The factor `2N(X₁ + X₂)/(Y₁Y₂)` of `IsConfigPts.twist_class` is nonzero. -/
theorem IsConfigPts.twist_factor_ne_zero (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) :
    2 * N * (x₁ + x₂) / (y₁ * y₂) ≠ 0 := by
  have hy₁ := y_ne_zero hc.pos hc.neg₁ hc.lt₁ hc.hy₁
  have hy₂ := y_ne_zero hc.pos hc.neg₂ hc.lt₂ hc.hy₂
  have : x₁ + x₂ ≠ 0 := by linarith [hc.neg₁, hc.neg₂]
  have := hc.pos.ne'
  positivity

/-- **The twist class.** For a positive configuration,
`U₁² + U₂² = −X₁X₂X₃ · (2N(X₁ + X₂)/(Y₁Y₂))²`, so `k ≡ −X₁X₂X₃ (mod ℚ*²)`. -/
theorem IsConfigPts.twist_class (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) :
    edge N x₁ y₁ ^ 2 + edge N x₂ y₂ ^ 2 =
      -(x₁ * x₂ * x₃) * (2 * N * (x₁ + x₂) / (y₁ * y₂)) ^ 2 := by
  have hN := hc.pos
  have hD₁ := (sub_sq_pos hN hc.neg₁ hc.lt₁).ne'
  have hD₂ := (sub_sq_pos hN hc.neg₂ hc.lt₂).ne'
  have hy₁ := y_ne_zero hN hc.neg₁ hc.lt₁ hc.hy₁
  have hy₂ := y_ne_zero hN hc.neg₂ hc.lt₂ hc.hy₂
  have hx₁ := hc.neg₁.ne
  have hx₂ := hc.neg₂.ne
  rw [edge_sq hN hc.neg₁ hc.lt₁ hc.hy₁, edge_sq hN hc.neg₂ hc.lt₂ hc.hy₂, div_pow, mul_pow y₁,
    hc.hy₁, hc.hy₂]
  have e₁ : x₁ ^ 3 - N ^ 2 * x₁ = -x₁ * (N ^ 2 - x₁ ^ 2) := by ring
  have e₂ : x₂ ^ 3 - N ^ 2 * x₂ = -x₂ * (N ^ 2 - x₂ ^ 2) := by ring
  rw [e₁, e₂]
  field_simp
  linear_combination 4 * (x₁ + x₂) * hc.compat

/-- **Configuration to `k`-twisted cuboid, by `−X₁X₂X₃`.** The box with edges `|U₁|, |U₂|, |U₃|`
of a positive configuration is a `k`-twisted perfect cuboid if and only if `k > 0` and
`k · (−X₁X₂X₃)` is a square. -/
theorem IsConfigPts.isTwistedCuboid_iff_isSquare (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) (k : ℚ) :
    (∃ d e f g, IsTwistedCuboid k |edge N x₁ y₁| |edge N x₂ y₂| |edge N x₃ y₃| d e f g) ↔
      0 < k ∧ IsSquare (k * -(x₁ * x₂ * x₃)) := by
  have hm := hc.neg_prod_pos
  have hr := hc.twist_factor_ne_zero
  have ht := hc.twist_class
  set m := -(x₁ * x₂ * x₃)
  set r := 2 * N * (x₁ + x₂) / (y₁ * y₂)
  clear_value m r
  constructor
  · rintro ⟨d, e, f, g, h⟩
    have hd := h.hd
    rw [sq_abs, sq_abs, ht] at hd
    refine ⟨h.pos_k, k * d / r, ?_⟩
    field_simp
    linear_combination -k * hd
  · rintro ⟨hk, s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      have : 0 < k * m := mul_pos hk hm
      rw [hs] at this
      simp at this
    have hkr : edge N x₁ y₁ ^ 2 + edge N x₂ y₂ ^ 2 = k * (s * r / k) ^ 2 := by
      rw [ht]
      field_simp
      linear_combination hs
    have h := hc.isTwistedCuboid
    rw [hkr] at h
    exact ⟨_, _, _, _, h.of_mul_sq (by have := hk.ne'; positivity)⟩

/-- **Configuration to perfect cuboid, by `−X₁X₂X₃`.** The box with edges `|U₁|, |U₂|, |U₃|` of a
positive configuration is a rational perfect cuboid if and only if `−X₁X₂X₃` is a square. -/
theorem IsConfigPts.isRatCuboid_iff_isSquare (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) :
    (∃ d e f g, IsRatCuboid |edge N x₁ y₁| |edge N x₂ y₂| |edge N x₃ y₃| d e f g) ↔
      IsSquare (-(x₁ * x₂ * x₃)) := by
  simp_rw [← isTwistedCuboid_one_iff, hc.isTwistedCuboid_iff_isSquare, one_mul]
  simp

end Config

/-- **The perfect cuboid problem in terms of `−X₁X₂X₃`.** A perfect cuboid exists if and only if,
for some `N > 0`, the curve `E_N` has a positive cuboid configuration with `−X₁X₂X₃` a square. -/
theorem exists_isPerfectCuboid_iff' :
    (∃ a b c : ℕ, IsPerfectCuboid a b c) ↔
      ∃ N x₁ x₂ x₃ y₁ y₂ y₃ : ℚ, IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃ ∧ IsSquare (-(x₁ * x₂ * x₃)) := by
  rw [exists_isPerfectCuboid_iff]
  constructor
  · rintro ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc, hsq⟩
    exact ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc,
      hc.isRatCuboid_iff_isSquare.mp (hc.isRatCuboid_iff.mpr hsq)⟩
  · rintro ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc, hsq⟩
    exact ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc,
      hc.isRatCuboid_iff.mp (hc.isRatCuboid_iff_isSquare.mpr hsq)⟩

/-- **Configurations with a given twist, by `−X₁X₂X₃`.** For every `k > 0`: some `E_N` has a
positive cuboid configuration with `k · (−X₁X₂X₃)` a square if and only if a `k`-twisted perfect
cuboid exists. For `k ∉ ℚ*²` both sides are false (`TwistRigidity.lean`). -/
theorem exists_config_iff_exists_twistedCuboid' {k : ℚ} (hk : 0 < k) :
    (∃ N x₁ x₂ x₃ y₁ y₂ y₃ : ℚ, IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃ ∧
        IsSquare (k * -(x₁ * x₂ * x₃))) ↔
      ∃ a b c d e f g : ℚ, IsTwistedCuboid k a b c d e f g := by
  constructor
  · rintro ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc, hsq⟩
    obtain ⟨d, e, f, g, h⟩ := (hc.isTwistedCuboid_iff_isSquare k).mpr ⟨hk, hsq⟩
    exact ⟨_, _, _, _, _, _, _, h⟩
  · intro h
    obtain ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, r, hc, hr, hkr⟩ :=
      (exists_config_iff_exists_twistedCuboid k).mpr h
    have h' := hc.isTwistedCuboid
    rw [hkr] at h'
    exact ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc,
      ((hc.isTwistedCuboid_iff_isSquare k).mp ⟨_, _, _, _, h'.of_mul_sq hr⟩).2⟩

section Cuboid

variable {k a b c d e f g N s : ℚ}

/-- **The twist identity in cuboid coordinates.** For a `k`-twisted perfect cuboid,
`2(kde + bc)(kdf + ac)(kef + ab) = k g² (af + be + cd)²`. -/
theorem IsTwistedCuboid.twist_identity (h : IsTwistedCuboid k a b c d e f g) :
    2 * (k * d * e + b * c) * (k * d * f + a * c) * (k * e * f + a * b) =
      k * g ^ 2 * (a * f + b * e + c * d) ^ 2 := by
  linear_combination
    (2 * a * b * e * f * k - c ^ 2 * g ^ 2 + 2 * e ^ 2 * f ^ 2 * k ^ 2) * h.hd
    + (2 * a ^ 2 * f ^ 2 * k + 2 * a * c * d * f * k + 2 * b ^ 2 * f ^ 2 * k - b ^ 2 * g ^ 2) * h.he
    + (2 * a ^ 4 + 2 * a ^ 2 * b ^ 2 + 2 * a ^ 2 * c ^ 2 - a ^ 2 * g ^ 2 + 2 * b ^ 2 * c ^ 2
      + 2 * b * c * d * e * k) * h.hf
    - 2 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + a * b * e * f * k + a * c * d * f * k + b ^ 2 * c ^ 2
      + b * c * d * e * k) * h.hg

/-- **The twist identity for a perfect cuboid:**
`2(de + bc)(df + ac)(ef + ab) = g² (af + be + cd)²`. -/
theorem IsRatCuboid.twist_identity (h : IsRatCuboid a b c d e f g) :
    2 * (d * e + b * c) * (d * f + a * c) * (e * f + a * b) =
      g ^ 2 * (a * f + b * e + c * d) ^ 2 := by
  have := (isTwistedCuboid_one_iff.mpr h).twist_identity
  linear_combination this

/-- **The twist class from the cuboid side.** The configuration that Asiryan's Proposition 1
attaches to a `k`-twisted perfect cuboid with `abcg = 2Ns²` (`isConfigPts_of_twistedCuboid`)
has `k · (−X₁X₂X₃) = (2N²s/(af + be + cd))²`. -/
theorem twist_class_of_twistedCuboid (h : IsTwistedCuboid k a b c d e f g)
    (hs : a * b * c * g = 2 * N * s ^ 2) :
    k * -(-N * (a * g) / (k * d * e + b * c) * (-N * (b * g) / (k * d * f + a * c)) *
        (-N * (c * g) / (k * e * f + a * b))) =
      (2 * N ^ 2 * s / (a * f + b * e + c * d)) ^ 2 := by
  have := h.pos_k; have := h.pos_a; have := h.pos_b; have := h.pos_c; have := h.pos_d
  have := h.pos_e; have := h.pos_f; have := h.pos_g
  have h₁ : 0 < k * d * e + b * c := by positivity
  have h₂ : 0 < k * d * f + a * c := by positivity
  have h₃ : 0 < k * e * f + a * b := by positivity
  have hP : 0 < a * f + b * e + c * d := by positivity
  have ht := h.twist_identity
  field_simp
  linear_combination k * N ^ 3 * g ^ 2 * (a * f + b * e + c * d) ^ 2 * hs - 2 * N ^ 4 * s ^ 2 * ht

end Cuboid

end PerfectCuboid.CongruentRank
