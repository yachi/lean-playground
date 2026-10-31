module

public import LeanPlayground.PerfectCuboid.ConfigCuboid
public import Mathlib.NumberTheory.SumTwoSquares
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Cuboid configurations are twisted perfect cuboids

`ConfigCuboid.lean` shows that a positive cuboid configuration on `E_N : Y² = X³ − N²X` gives a
rational perfect cuboid exactly when its legs satisfy `U₁² + U₂² = □`. This file names what a
configuration is without that condition; `TwistRigidity.lean` then shows the condition is automatic
(`IsConfigPts.isSquare_twist`).

A **`k`-twisted perfect cuboid** (`IsTwistedCuboid k a b c d e f g`) is a box with positive
rational edges `a, b, c` and rational space diagonal `g`, whose three face diagonals are rational
up to the same factor `√k`:

  `a² + b² = k d²`,  `a² + c² = k e²`,  `b² + c² = k f²`,  `a² + b² + c² = g²`.

Only the class of `k` in `ℚ*/ℚ*²` matters (`IsTwistedCuboid.of_mul_sq`), and `k = 1` is a rational
perfect cuboid (`isTwistedCuboid_one_iff`).

* `IsConfigPts.isTwistedCuboid`: a positive configuration is a `k`-twisted perfect cuboid with
  `k = U₁² + U₂²`.
* `isConfigPts_of_twistedCuboid`: Asiryan's Proposition 1 works verbatim for twisted cuboids,
  with the products `de, df, ef` of face diagonals replaced by `kde, kdf, kef`.
* `exists_config_iff_exists_twistedCuboid`: for every `k`, `E_N` has a positive configuration with
  `U₁² + U₂² ∈ k·ℚ*²` for some `N` if and only if a `k`-twisted perfect cuboid exists.
* `exists_config_iff`: a positive configuration exists if and only if a `k`-twisted perfect cuboid
  exists for some `k`.
* `exists_isPerfectCuboid_iff_twisted`: a perfect cuboid exists if and only if a `1`-twisted one
  does. So the extra condition `U₁² + U₂² = □` of `exists_isPerfectCuboid_iff` is exactly `k = 1`.
  By twist rigidity (`TwistRigidity.lean`: `IsTwistedCuboid.isSquare_twist`,
  `not_exists_isTwistedCuboid_of_not_isSquare`) no `k`-twisted perfect cuboid with `k ∉ ℚ*²`
  exists, so the condition is automatic and `exists_isPerfectCuboid_iff_exists_isConfigPts` holds
  without it.
* `IsTwistedCuboid.even_padicValRat`: every prime `q ≡ 3 (mod 4)` divides `k` to an even power,
  because `k = (a/d)² + (b/d)²` is a sum of two squares. So the squarefree part of `k` is a product
  of `2` and primes `≡ 1 (mod 4)`.

A computer search over all boxes with integer edges up to `6000` found no twisted perfect cuboid
with `k ≠ 1`; this is now a theorem (`TwistRigidity.twist_rigidity`: three equal twists force
`k = 1`).

Literature note. Asiryan (arXiv:2610.10643, Definition 1) defines a configuration with no square
condition, and Corollary 1 credits the configuration-to-cuboid direction to Paulsen–West
(Houston J. Math. 48 (2022), Proposition 3.1). By the results here a configuration gives a
`k`-twisted cuboid with `k = U₁² + U₂²`, and `TwistRigidity.lean` shows `k` is always a square,
so the Paulsen–West direction holds unconditionally by an elementary argument (we did not check
whether their Proposition 3.1 proves the square condition).
-/

@[expose] public section

namespace PerfectCuboid.CongruentRank

/-- A `k`-twisted perfect cuboid: positive rational edges `a, b, c`, positive rational space
diagonal `g`, and face diagonals `√k·d`, `√k·e`, `√k·f` with `d, e, f` positive rationals. -/
structure IsTwistedCuboid (k a b c d e f g : ℚ) : Prop where
  pos_k : 0 < k
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  pos_d : 0 < d
  pos_e : 0 < e
  pos_f : 0 < f
  pos_g : 0 < g
  hd : k * d ^ 2 = a ^ 2 + b ^ 2
  he : k * e ^ 2 = a ^ 2 + c ^ 2
  hf : k * f ^ 2 = b ^ 2 + c ^ 2
  hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2

section Twisted

variable {k a b c d e f g r : ℚ}

/-- A `1`-twisted perfect cuboid is a rational perfect cuboid. -/
theorem isTwistedCuboid_one_iff : IsTwistedCuboid 1 a b c d e f g ↔ IsRatCuboid a b c d e f g := by
  constructor
  · intro h
    exact ⟨h.pos_a, h.pos_b, h.pos_c, h.pos_d, h.pos_e, h.pos_f, h.pos_g,
      by linear_combination h.hd, by linear_combination h.he, by linear_combination h.hf, h.hg⟩
  · intro h
    exact ⟨one_pos, h.pos_a, h.pos_b, h.pos_c, h.pos_d, h.pos_e, h.pos_f, h.pos_g,
      by linear_combination h.hd, by linear_combination h.he, by linear_combination h.hf, h.hg⟩

/-- Only the square class of `k` matters. -/
theorem IsTwistedCuboid.of_mul_sq (h : IsTwistedCuboid (k * r ^ 2) a b c d e f g) (hr : r ≠ 0) :
    IsTwistedCuboid k a b c (|r| * d) (|r| * e) (|r| * f) g := by
  have hk : 0 < k := by
    have := h.pos_k
    have : 0 < r ^ 2 := by positivity
    exact pos_of_mul_pos_left ‹0 < k * r ^ 2› this.le
  have := h.pos_d; have := h.pos_e; have := h.pos_f
  refine ⟨hk, h.pos_a, h.pos_b, h.pos_c, by positivity, by positivity, by positivity, h.pos_g,
    ?_, ?_, ?_, h.hg⟩ <;> rw [mul_pow, sq_abs]
  · linear_combination h.hd
  · linear_combination h.he
  · linear_combination h.hf

/-- With `h = kde + bc`: `h² − a²g² = 2bch`. -/
theorem IsTwistedCuboid.key₁ (h : IsTwistedCuboid k a b c d e f g) :
    (k * d * e + b * c) ^ 2 - (a * g) ^ 2 = 2 * (b * c) * (k * d * e + b * c) := by
  linear_combination (-a ^ 2) * h.hg + e ^ 2 * k * h.hd + (a ^ 2 + b ^ 2) * h.he

/-- With `h = kdf + ac`: `h² − b²g² = 2ach`. -/
theorem IsTwistedCuboid.key₂ (h : IsTwistedCuboid k a b c d e f g) :
    (k * d * f + a * c) ^ 2 - (b * g) ^ 2 = 2 * (a * c) * (k * d * f + a * c) := by
  linear_combination (-b ^ 2) * h.hg + f ^ 2 * k * h.hd + (a ^ 2 + b ^ 2) * h.hf

/-- With `h = kef + ab`: `h² − c²g² = 2abh`. -/
theorem IsTwistedCuboid.key₃ (h : IsTwistedCuboid k a b c d e f g) :
    (k * e * f + a * b) ^ 2 - (c * g) ^ 2 = 2 * (a * b) * (k * e * f + a * b) := by
  linear_combination (-c ^ 2) * h.hg + f ^ 2 * k * h.he + (a ^ 2 + c ^ 2) * h.hf

/-- The compatibility condition of Proposition 1, for a twisted cuboid. -/
theorem IsTwistedCuboid.compat (h : IsTwistedCuboid k a b c d e f g) :
    a * g * (b * g) * (k * e * f + a * b) + a * g * (c * g) * (k * d * f + a * c) +
      b * g * (c * g) * (k * d * e + b * c) =
        (k * d * e + b * c) * (k * d * f + a * c) * (k * e * f + a * b) := by
  linear_combination (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + a * b * e * f * k + a * c * d * f * k
      + b ^ 2 * c ^ 2 + b * c * d * e * k) * h.hg
    + (-a * b * e * f * k - e ^ 2 * f ^ 2 * k ^ 2) * h.hd
    + (-a ^ 2 * f ^ 2 * k - a * c * d * f * k - b ^ 2 * f ^ 2 * k) * h.he
    + (-a ^ 4 - a ^ 2 * b ^ 2 - a ^ 2 * c ^ 2 - b ^ 2 * c ^ 2 - b * c * d * e * k) * h.hf

end Twisted

section Point

variable {N a b c g s D : ℚ}

/-- The point `(−N·ag/h, N²·2s/h)` lies on `E_N` when `h² − a²g² = 2bch` and `abcg = 2Ns²`. -/
theorem twist_point_eq (key : D ^ 2 - (a * g) ^ 2 = 2 * (b * c) * D)
    (hs : a * b * c * g = 2 * N * s ^ 2) (hD : D ≠ 0) :
    (N ^ 2 * (2 * s) / D) ^ 2 = (-N * (a * g) / D) ^ 3 - N ^ 2 * (-N * (a * g) / D) := by
  field_simp
  linear_combination (-(N ^ 3 * a * g) * key) - 2 * N ^ 3 * D * hs

/-- Its `X`-coordinate lies in `(−N, 0)`. -/
theorem twist_point_bounds (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hg : 0 < g) (hN : 0 < N)
    (hD : 0 < D) (key : D ^ 2 - (a * g) ^ 2 = 2 * (b * c) * D) :
    -N < -N * (a * g) / D ∧ -N * (a * g) / D < 0 := by
  have hag := mul_pos ha hg
  have hbcD : 0 < 2 * (b * c) * D := by positivity
  have hlt : a * g < D := by nlinarith
  constructor
  · rw [lt_div_iff₀ hD]
    nlinarith
  · apply div_neg_of_neg_of_pos _ hD
    nlinarith

/-- Its leg `U` is `2Ns/(bc)`. -/
theorem twist_edge (key : D ^ 2 - (a * g) ^ 2 = 2 * (b * c) * D) (hN : N ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hD : D ≠ 0) :
    edge N (-N * (a * g) / D) (N ^ 2 * (2 * s) / D) = 2 * N * s / (b * c) := by
  have hD' : N ^ 2 - (-N * (a * g) / D) ^ 2 = N ^ 2 * (2 * (b * c) * D) / D ^ 2 := by
    rw [← key]
    field_simp
  rw [edge, hD']
  field_simp

end Point

section Correspondence

variable {k a b c d e f g N s : ℚ}

/-- **Asiryan, Proposition 1, for twisted cuboids.** A `k`-twisted perfect cuboid with
`abcg = 2Ns²` gives the configuration `Xᵢ = −N·ag/(kde + bc), −N·bg/(kdf + ac), −N·cg/(kef + ab)`,
`Yᵢ = 2N²s/(kde + bc), …`. -/
theorem isConfigPts_of_twistedCuboid (h : IsTwistedCuboid k a b c d e f g) (hN : 0 < N)
    (hs : a * b * c * g = 2 * N * s ^ 2) :
    IsConfigPts N (-N * (a * g) / (k * d * e + b * c)) (-N * (b * g) / (k * d * f + a * c))
      (-N * (c * g) / (k * e * f + a * b)) (N ^ 2 * (2 * s) / (k * d * e + b * c))
      (N ^ 2 * (2 * s) / (k * d * f + a * c)) (N ^ 2 * (2 * s) / (k * e * f + a * b)) := by
  have := h.pos_k; have := h.pos_a; have := h.pos_b; have := h.pos_c; have := h.pos_d
  have := h.pos_e; have := h.pos_f
  have h₁ : 0 < k * d * e + b * c := by positivity
  have h₂ : 0 < k * d * f + a * c := by positivity
  have h₃ : 0 < k * e * f + a * b := by positivity
  have hs₂ : b * a * c * g = 2 * N * s ^ 2 := by linear_combination hs
  have hs₃ : c * a * b * g = 2 * N * s ^ 2 := by linear_combination hs
  have b₁ := twist_point_bounds h.pos_a h.pos_b h.pos_c h.pos_g hN h₁ h.key₁
  have b₂ := twist_point_bounds h.pos_b h.pos_a h.pos_c h.pos_g hN h₂ h.key₂
  have b₃ := twist_point_bounds h.pos_c h.pos_a h.pos_b h.pos_g hN h₃ h.key₃
  refine ⟨⟨hN, b₁.1, b₂.1, b₃.1, b₁.2, b₂.2, b₃.2, ?_⟩,
    twist_point_eq h.key₁ hs h₁.ne', twist_point_eq h.key₂ hs₂ h₂.ne',
    twist_point_eq h.key₃ hs₃ h₃.ne'⟩
  have key := h.compat
  field_simp
  linear_combination key

/-- **Configuration to twisted cuboid.** The box with edges `|U₁|, |U₂|, |U₃|` of a positive
configuration is a `k`-twisted perfect cuboid for `k = U₁² + U₂²`, with face diagonals
`√k·1`, `√k·|H₃/H₂|`, `√k·|H₃/H₁|` and space diagonal `|U₁U₂U₃/(2N)|`. -/
theorem IsConfigPts.isTwistedCuboid {x₁ x₂ x₃ y₁ y₂ y₃ : ℚ}
    (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) :
    IsTwistedCuboid (edge N x₁ y₁ ^ 2 + edge N x₂ y₂ ^ 2) |edge N x₁ y₁| |edge N x₂ y₂|
      |edge N x₃ y₃| 1 |hyp N x₃ y₃ / hyp N x₂ y₂| |hyp N x₃ y₃ / hyp N x₁ y₁|
      |edge N x₁ y₁ * edge N x₂ y₂ * edge N x₃ y₃ / (2 * N)| := by
  have hN := hc.pos
  have hU₁ := edge_ne_zero hN hc.neg₁ hc.lt₁ hc.hy₁
  have hU₂ := edge_ne_zero hN hc.neg₂ hc.lt₂ hc.hy₂
  have hU₃ := edge_ne_zero hN hc.neg₃ hc.lt₃ hc.hy₃
  have hH₁ := hyp_ne_zero hN hc.neg₁ hc.lt₁ hc.hy₁
  have hH₂ := hyp_ne_zero hN hc.neg₂ hc.lt₂ hc.hy₂
  have hH₃ := hyp_ne_zero hN hc.neg₃ hc.lt₃ hc.hy₃
  have f₁₃ := hc.face₁₃
  have f₂₃ := hc.face₂₃
  have sp := hc.space
  set U₁ := edge N x₁ y₁
  set U₂ := edge N x₂ y₂
  set U₃ := edge N x₃ y₃
  set H₁ := hyp N x₁ y₁
  set H₂ := hyp N x₂ y₂
  set H₃ := hyp N x₃ y₃
  refine ⟨by positivity, by positivity, by positivity, by positivity, one_pos, by positivity,
    by positivity, by positivity, ?_, ?_, ?_, ?_⟩
  · rw [sq_abs, sq_abs]
    ring
  · rw [sq_abs, sq_abs, sq_abs]
    field_simp
    linear_combination -f₁₃
  · rw [sq_abs, sq_abs, sq_abs]
    field_simp
    linear_combination -f₂₃
  · rw [sq_abs, sq_abs, sq_abs, sq_abs, ← sp]

/-- **Configurations with a given twist.** For every `k`: some `E_N` has a positive cuboid
configuration whose legs satisfy `U₁² + U₂² = k r²` with `r ≠ 0` if and only if a `k`-twisted
perfect cuboid exists. -/
theorem exists_config_iff_exists_twistedCuboid (k : ℚ) :
    (∃ N x₁ x₂ x₃ y₁ y₂ y₃ r : ℚ, IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃ ∧ r ≠ 0 ∧
        edge N x₁ y₁ ^ 2 + edge N x₂ y₂ ^ 2 = k * r ^ 2) ↔
      ∃ a b c d e f g : ℚ, IsTwistedCuboid k a b c d e f g := by
  constructor
  · rintro ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, r, hc, hr, hk⟩
    have h := hc.isTwistedCuboid
    rw [hk] at h
    exact ⟨_, _, _, _, _, _, _, h.of_mul_sq hr⟩
  · rintro ⟨a, b, c, d, e, f, g, h⟩
    have := h.pos_k; have := h.pos_a; have := h.pos_b; have := h.pos_c; have := h.pos_d
    have := h.pos_e; have := h.pos_f; have := h.pos_g
    -- take `N = abcg/2` and `s = 1`
    set N : ℚ := a * b * c * g / 2
    have hN : 0 < N := by positivity
    have hs : a * b * c * g = 2 * N * 1 ^ 2 := by simp only [N]; ring
    have hc' := isConfigPts_of_twistedCuboid h hN hs
    refine ⟨_, _, _, _, _, _, _, g * d, hc', by positivity, ?_⟩
    have h₁ : 0 < k * d * e + b * c := by positivity
    have h₂ : 0 < k * d * f + a * c := by positivity
    rw [twist_edge h.key₁ hN.ne' (by positivity) (by positivity) h₁.ne',
      twist_edge h.key₂ hN.ne' (by positivity) (by positivity) h₂.ne']
    have e₁ : 2 * N * 1 / (b * c) = a * g := by simp only [N]; field_simp
    have e₂ : 2 * N * 1 / (a * c) = b * g := by simp only [N]; field_simp
    rw [e₁, e₂]
    linear_combination (-(g : ℚ) ^ 2) * h.hd

/-- **Every configuration is a twisted cuboid.** A positive cuboid configuration exists on some
`E_N` if and only if a `k`-twisted perfect cuboid exists for some `k`. -/
theorem exists_config_iff :
    (∃ N x₁ x₂ x₃ y₁ y₂ y₃ : ℚ, IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) ↔
      ∃ k a b c d e f g : ℚ, IsTwistedCuboid k a b c d e f g := by
  constructor
  · rintro ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc⟩
    exact ⟨_, _, _, _, _, _, _, _, hc.isTwistedCuboid⟩
  · rintro ⟨k, h⟩
    obtain ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, -, hc, -⟩ := (exists_config_iff_exists_twistedCuboid k).mpr h
    exact ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc⟩

/-- **Perfect cuboids are the `1`-twisted ones.** Together with `exists_config_iff`, this says
that the square condition `U₁² + U₂² = □` of `exists_isPerfectCuboid_iff` is the twist `k = 1`. -/
theorem exists_isPerfectCuboid_iff_twisted :
    (∃ A B C : ℕ, IsPerfectCuboid A B C) ↔
      ∃ a b c d e f g : ℚ, IsTwistedCuboid 1 a b c d e f g := by
  rw [exists_isPerfectCuboid_iff, ← exists_config_iff_exists_twistedCuboid]
  constructor
  · rintro ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc, r, hr⟩
    refine ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, r, hc, ?_, by rw [hr]; ring⟩
    rintro rfl
    have hU₁ := edge_ne_zero hc.pos hc.neg₁ hc.lt₁ hc.hy₁
    have : 0 < edge N x₁ y₁ ^ 2 + edge N x₂ y₂ ^ 2 := by positivity
    rw [hr] at this
    simp at this
  · rintro ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, r, hc, -, hr⟩
    exact ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc, r, by rw [hr]; ring⟩

end Correspondence

section Arithmetic

/-- A nonzero sum of two rational squares has even `q`-adic valuation at every prime
`q ≡ 3 (mod 4)`. -/
theorem even_padicValRat_sq_add_sq {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3) (x y : ℚ)
    (h : x ^ 2 + y ^ 2 ≠ 0) : Even (padicValRat q (x ^ 2 + y ^ 2)) := by
  set X : ℤ := x.num * y.den
  set Y : ℤ := y.num * x.den
  set m : ℕ := x.den * y.den
  have hm : (m : ℚ) ≠ 0 := by positivity
  set n : ℕ := X.natAbs ^ 2 + Y.natAbs ^ 2
  have hX : (X : ℚ) = x * m := by
    simp only [X, m, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, ← Rat.mul_den_eq_num]
    ring
  have hY : (Y : ℚ) = y * m := by
    simp only [Y, m, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, ← Rat.mul_den_eq_num]
    ring
  have hn : (n : ℚ) = (m : ℚ) ^ 2 * (x ^ 2 + y ^ 2) := by
    simp only [n, Nat.cast_add, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs, hX, hY]
    ring
  have hn0 : (n : ℚ) ≠ 0 := by rw [hn]; positivity
  have hsum : x ^ 2 + y ^ 2 = (n : ℚ) / (m : ℚ) ^ 2 := by
    rw [hn]
    field_simp
  rw [hsum, padicValRat.div hn0 (by positivity), padicValRat.pow, padicValRat.of_nat,
    padicValRat.of_nat]
  have hev : Even (padicValNat q n) := by
    by_cases hqn : q ∈ n.primeFactors
    · exact Nat.eq_sq_add_sq_iff.mp ⟨_, _, rfl⟩ q hqn hq
    · rw [padicValNat.eq_zero_of_not_dvd]
      · exact Even.zero
      · intro hdvd
        exact hqn (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, by exact_mod_cast hn0⟩)
  obtain ⟨t, ht⟩ := hev
  exact ⟨t - padicValNat q m, by push_cast [ht]; ring⟩

/-- **The twist is a sum of two squares.** Every prime `q ≡ 3 (mod 4)` divides the twist `k` of a
twisted perfect cuboid to an even power. -/
theorem IsTwistedCuboid.even_padicValRat {k a b c d e f g : ℚ} (h : IsTwistedCuboid k a b c d e f g)
    {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3) : Even (padicValRat q k) := by
  have hd := h.pos_d.ne'
  have hk : k = (a / d) ^ 2 + (b / d) ^ 2 := by
    field_simp
    linear_combination h.hd
  have := h.pos_k
  rw [hk]
  exact even_padicValRat_sq_add_sq hq _ _ (by rw [← hk]; positivity)

end Arithmetic

end PerfectCuboid.CongruentRank
