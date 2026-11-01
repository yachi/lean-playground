module

public import LeanPlayground.PerfectCuboid.Torsion
public import LeanPlayground.PerfectCuboid.TwistRigidity

/-!
# The Kummer addition identity on `E_N` and the rank-one square system

On `E_N : y² = x³ − N²x` the Kummer map `κ(P) = (x, x − N, x + N) ∈ (ℚ*/ℚ*²)³` is a homomorphism
vanishing on `2E_N(ℚ)`. This file proves the explicit identities behind that statement and reads
them on Asiryan's rank-one pattern `(aG, bG + T, cG + U)` (`Pattern`, reached unconditionally by
`rankOneReduction_of_pos`). Nothing here uses heights, Selmer groups or Ingram's theorem.

## Main results

* `add_identity` (A1): for `x₁ ≠ x₂` and a root `e ∈ {0, N, −N}`,
  `(x₁ − e)(x₂ − e)(x₃ − e) = ((y₁(x₂ − e) − y₂(x₁ − e))/(x₂ − x₁))²`, `x₃ = x(P₁ + P₂)`;
  instances `add_identity_zero`, `add_identity_N`, `add_identity_negN`; on points `kappa_add`.
* `double_identity`, `kappa_double`: `x(2R) − e = ((x² − 2ex + N² − 2e²)/(2y))²`.
* `classes_add_two_smul` (A2): `κ(P + 2R) = κ(P)` whenever `P` and `P + 2R` have order `> 2`.
* `pattern_pair` (A3): in the pattern `κ(Q₁)κ(Q₂) = κ(T) = (N, 2, 2N)`:
  `N x₁x₂`, `2(x₁ − N)(x₂ − N)`, `2N(x₁ + N)(x₂ + N)` are squares.
* `pattern_single`: `κ(Q₃) = κ(U) = (−N, −2N, 2)`.
* `pattern_sum` (A4): `κ(Q₁)κ(Q₂)κ(Q₃) = κ(S) = (−1, −N, N)`.
* `rankOne_relations`: a positive configuration in `ℤG + E[2]` gives (via
  `rankOneReduction_of_pos`) a positive configuration with the pair and single-point relations.
* `inRankOne_dichotomy` (A5), sharp form `inRankOne_dichotomy'`: directly from `InRankOne`, one
  `xᵢ` has a torsion Kummer class (`IsTorsionClass`: the `S`- or `U`-class) or `κ(Q₁)κ(Q₂)` is a
  torsion class (`IsTorsionPair`: the `0`- or `T`-class); the other classes die by sign.
* `pattern_system`, `pattern_tt`: equation (24) together with all Kummer relations, in the
  abscissas `X_a, X_b, X_c` and in Asiryan's variables `t = −X/N`.
* `IsRatCuboid.pair_iff` (A6): the pair relation in the edges and diagonals of a cuboid.
-/

@[expose] public section

namespace PerfectCuboid.KummerAdd

open PerfectCuboid.CongruentRank WeierstrassCurve WeierstrassCurve.Affine

variable {N : ℚ}

/-! ### The addition and doubling identities -/

/-- The polynomial core of the addition identity: for a root `e` of `x³ − N²x`, after clearing the
denominator `(x₂ − x₁)²`. -/
theorem add_identity_poly {x₁ y₁ x₂ y₂ e : ℚ} (h₁ : y₁ ^ 2 = x₁ ^ 3 - N ^ 2 * x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - N ^ 2 * x₂) (he : e * (e - N) * (e + N) = 0) :
    (x₁ - e) * (x₂ - e) * ((y₁ - y₂) ^ 2 - (x₁ + x₂ + e) * (x₁ - x₂) ^ 2) =
      (y₁ * (x₂ - e) - y₂ * (x₁ - e)) ^ 2 := by
  linear_combination (x₂ - x₁) * (-(x₂ - e) * h₁ + (x₁ - e) * h₂) - (x₁ - x₂) ^ 2 * he

/-- **A1. The addition identity.** For `x₁ ≠ x₂` and a root `e ∈ {0, N, −N}`:
`(x₁ − e)(x₂ − e)(x₃ − e) = ((y₁(x₂ − e) − y₂(x₁ − e))/(x₂ − x₁))²`, `x₃ = x(P₁ + P₂)`. -/
theorem add_identity (hN : N ≠ 0) {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve N).Nonsingular x₁ y₁)
    (h₂ : (curve N).Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) {e : ℚ} (he : e * (e - N) * (e + N) = 0) :
    (x₁ - e) * (x₂ - e) * ((curve N).addX x₁ x₂ ((curve N).slope x₁ x₂ y₁ y₂) - e) =
      ((y₁ * (x₂ - e) - y₂ * (x₁ - e)) / (x₂ - x₁)) ^ 2 := by
  have key := add_identity_poly ((nonsingular_iff hN).mp h₁) ((nonsingular_iff hN).mp h₂) he
  have hx' : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hx'' : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr hx.symm
  rw [slope_of_X_ne hx]
  simp only [addX, curve, zero_mul, add_zero, sub_zero]
  rw [div_pow, div_pow, eq_div_iff (pow_ne_zero 2 hx''), ← key]
  field_simp
  ring

theorem add_identity_zero (hN : N ≠ 0) {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve N).Nonsingular x₁ y₁)
    (h₂ : (curve N).Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    x₁ * x₂ * (curve N).addX x₁ x₂ ((curve N).slope x₁ x₂ y₁ y₂) =
      ((y₁ * x₂ - y₂ * x₁) / (x₂ - x₁)) ^ 2 := by
  simpa using add_identity hN h₁ h₂ hx (e := 0) (by ring)

theorem add_identity_N (hN : N ≠ 0) {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve N).Nonsingular x₁ y₁)
    (h₂ : (curve N).Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    (x₁ - N) * (x₂ - N) * ((curve N).addX x₁ x₂ ((curve N).slope x₁ x₂ y₁ y₂) - N) =
      ((y₁ * (x₂ - N) - y₂ * (x₁ - N)) / (x₂ - x₁)) ^ 2 :=
  add_identity hN h₁ h₂ hx (by ring)

theorem add_identity_negN (hN : N ≠ 0) {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve N).Nonsingular x₁ y₁)
    (h₂ : (curve N).Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    (x₁ + N) * (x₂ + N) * ((curve N).addX x₁ x₂ ((curve N).slope x₁ x₂ y₁ y₂) + N) =
      ((y₁ * (x₂ + N) - y₂ * (x₁ + N)) / (x₂ - x₁)) ^ 2 := by
  simpa [sub_neg_eq_add] using add_identity hN h₁ h₂ hx (e := -N) (by ring)

/-- **The doubling identity.** For `y ≠ 0` and a root `e`:
`x(2R) − e = ((x² − 2ex + N² − 2e²)/(2y))²`. -/
theorem double_identity (hN : N ≠ 0) {x y : ℚ} (h : (curve N).Nonsingular x y) (hy : y ≠ 0)
    {e : ℚ} (he : e * (e - N) * (e + N) = 0) :
    (curve N).addX x x ((curve N).slope x x y y) - e =
      ((x ^ 2 - 2 * e * x + N ^ 2 - 2 * e ^ 2) / (2 * y)) ^ 2 := by
  have h2 := (nonsingular_iff hN).mp h
  have hy' : y ≠ (curve N).negY x y := by
    simp only [curve, negY, zero_mul, sub_zero]
    intro h'; apply hy; linarith
  rw [slope_of_Y_ne rfl hy']
  simp only [addX, curve, negY, zero_mul, add_zero, sub_zero, mul_zero]
  field_simp
  linear_combination (-32 * x - 16 * e) * h2 - 16 * (2 * x + e) * he


/-! ### Square-class helpers -/

theorem isSquare_of_mul_sq {q r : ℚ} (hr : r ≠ 0) (h : IsSquare (q * r ^ 2)) : IsSquare q := by
  have := h.div (IsSquare.sq r)
  rwa [mul_div_assoc, div_self (pow_ne_zero 2 hr), mul_one] at this

theorem isSquare_mul_sq_iff {q r : ℚ} (hr : r ≠ 0) : IsSquare (q * r ^ 2) ↔ IsSquare q :=
  ⟨isSquare_of_mul_sq hr, fun h => h.mul (IsSquare.sq r)⟩

/-- A negative rational is not a square (the sign kill). -/
theorem not_isSquare_of_neg {q : ℚ} (hq : q < 0) : ¬IsSquare q := fun h => h.nonneg.not_gt hq

/-! ### The Kummer map on points: addition and doubling -/

/-- **Doubling.** If `R + R` is an affine point with abscissa `x'`, then `x' − e` is a square for
every root `e ∈ {0, N, −N}`: `κ(2R)` is trivial. -/
theorem isSquare_double (hN : N ≠ 0) {R : (curve N).Point} {x' : ℚ} (h : HasX (R + R) x')
    {e : ℚ} (he : e * (e - N) * (e + N) = 0) : IsSquare (x' - e) := by
  cases R with
  | zero => exact (h.ne_zero (zero_add _)).elim
  | @some x y hR =>
    by_cases hy : y = 0
    · subst hy
      rw [Point.add_self_of_Y_eq (by simp [curve, negY])] at h
      exact (h.ne_zero rfl).elim
    have hy' : y ≠ (curve N).negY x y := by
      simp only [curve, negY, zero_mul, sub_zero]
      intro h'; apply hy; linarith
    rw [Point.add_self_of_Y_ne hy'] at h
    rw [← (hasX_some rfl).unique h, double_identity hN hR hy he]
    exact IsSquare.sq _

/-- If `2R` is not `2`-torsion, `x(2R) − e ≠ 0`. -/
theorem double_sub_ne (hN : N ≠ 0) {R : (curve N).Point} {x' : ℚ} (h : HasX (R + R) x')
    (hR : R + R + (R + R) ≠ 0) {e : ℚ} (he : e * (e - N) * (e + N) = 0) : x' - e ≠ 0 := by
  intro h0
  rw [sub_eq_zero] at h0
  subst h0
  exact hR (h.add_self_eq_zero hN he)

/-- **`kappa_double`.** For `P` of order `> 2`, `x(2P)`, `x(2P) − N`, `x(2P) + N` are squares. The
doubling identity is re-proved here (`double_identity`); `KummerDescent.lean` (round 16, brief 1)
proves the same statement in its own namespace. -/
theorem kappa_double (hN : N ≠ 0) {P : (curve N).Point} (hP : P + P ≠ 0) :
    ∃ x', HasX (P + P) x' ∧ IsSquare x' ∧ IsSquare (x' - N) ∧ IsSquare (x' + N) := by
  obtain ⟨x', h⟩ := exists_hasX hP
  refine ⟨x', h, ?_, isSquare_double hN h (by ring), ?_⟩
  · simpa using isSquare_double hN h (e := 0) (by ring)
  · simpa using isSquare_double hN h (e := -N) (by ring)

/-- **`kappa_add`** for a root `e`: if `x₁ ≠ x₂` then `(x₁ − e)(x₂ − e)(x₃ − e)` is a square,
`x₃ = x(P₁ + P₂)`. -/
theorem kappa_add_e (hN : N ≠ 0) {P₁ P₂ : (curve N).Point} {x₁ x₂ : ℚ} (h₁ : HasX P₁ x₁)
    (h₂ : HasX P₂ x₂) (hx : x₁ ≠ x₂) {e : ℚ} (he : e * (e - N) * (e + N) = 0) :
    ∃ x₃, HasX (P₁ + P₂) x₃ ∧ IsSquare ((x₁ - e) * (x₂ - e) * (x₃ - e)) := by
  obtain ⟨y₁, hy₁, rfl⟩ := h₁
  obtain ⟨y₂, hy₂, rfl⟩ := h₂
  rw [Point.add_of_X_ne hx]
  exact ⟨_, hasX_some rfl, by rw [add_identity hN hy₁ hy₂ hx he]; exact IsSquare.sq _⟩

/-- **`kappa_add`.** For `x₁ ≠ x₂`: `κ(P₁)κ(P₂)κ(P₁ + P₂) = 1` coordinatewise, in explicit form. -/
theorem kappa_add (hN : N ≠ 0) {P₁ P₂ : (curve N).Point} {x₁ x₂ : ℚ} (h₁ : HasX P₁ x₁)
    (h₂ : HasX P₂ x₂) (hx : x₁ ≠ x₂) :
    ∃ x₃, HasX (P₁ + P₂) x₃ ∧ IsSquare (x₁ * x₂ * x₃) ∧
      IsSquare ((x₁ - N) * (x₂ - N) * (x₃ - N)) ∧ IsSquare ((x₁ + N) * (x₂ + N) * (x₃ + N)) := by
  obtain ⟨x₃, h₃, s₀⟩ := kappa_add_e hN h₁ h₂ hx (e := 0) (by ring)
  obtain ⟨x₃', h₃', sN⟩ := kappa_add_e hN h₁ h₂ hx (e := N) (by ring)
  obtain ⟨x₃'', h₃'', sM⟩ := kappa_add_e hN h₁ h₂ hx (e := -N) (by ring)
  obtain rfl := h₃.unique h₃'
  obtain rfl := h₃.unique h₃''
  exact ⟨x₃, h₃, by simpa using s₀, sN, by simpa using sM⟩

/-- **A2. Multiplicativity on cosets of `2E`.** If `P` and `P + 2R` both have order `> 2`, then
`(x(P) − e)(x(P + 2R) − e)` is a square for every root `e`: `κ(P + 2R) = κ(P)`. -/
theorem classes_add_two_smul (hN : N ≠ 0) {P R : (curve N).Point} {x x' : ℚ} (h : HasX P x)
    (hP : P + P ≠ 0) (h' : HasX (P + (R + R)) x') {e : ℚ} (he : e * (e - N) * (e + N) = 0) :
    IsSquare ((x - e) * (x' - e)) := by
  by_cases hD : R + R + (R + R) = 0
  · rw [add_self_eq_zero_of_four hN hD, add_zero] at h'
    rw [h.unique h']
    exact IsSquare.mul_self _
  obtain ⟨xD, hxD⟩ := exists_hasX (fun h0 : R + R = 0 => hD (by rw [h0, add_zero]))
  obtain ⟨s, hs⟩ := isSquare_double hN hxD he
  have nD := double_sub_ne hN hxD hD he
  have hs0 : s ≠ 0 := by rintro rfl; exact nD (by rw [hs, mul_zero])
  obtain ⟨yD, hyD, eD⟩ := hxD
  obtain ⟨y, hy, rfl⟩ := h
  rw [eD] at h'
  by_cases hx : x = xD
  · subst hx
    by_cases hyy : y = (curve N).negY x yD
    · rw [Point.add_of_Y_eq rfl hyy] at h'
      exact (h'.ne_zero rfl).elim
    obtain rfl := Y_eq_of_Y_ne hy.1 hyD.1 rfl hyy
    exact (show IsSquare (x - e) from ⟨s, hs⟩).mul (isSquare_double hN h' he)
  · rw [Point.add_of_X_ne hx] at h'
    have key := add_identity hN hy hyD hx he
    rw [(hasX_some rfl).unique h', hs] at key
    apply isSquare_of_mul_sq hs0
    rw [show (x - e) * (x' - e) * s ^ 2 = (x - e) * (s * s) * (x' - e) by ring, key]
    exact IsSquare.sq _

/-! ### Torsion translates of doubles: the single-point classes -/

/-- A double `2R` of order `> 2`: its abscissa `x_D` and the nonzero squares `x_D`, `x_D ∓ N`. -/
theorem double_data (hN : N ≠ 0) {R : (curve N).Point} (hD : R + R + (R + R) ≠ 0) :
    ∃ xD, HasX (R + R) xD ∧ IsSquare xD ∧ IsSquare (xD - N) ∧ IsSquare (xD + N) ∧
      xD ≠ 0 ∧ xD - N ≠ 0 ∧ xD + N ≠ 0 := by
  obtain ⟨xD, h⟩ := exists_hasX (fun h0 : R + R = 0 => hD (by rw [h0, add_zero]))
  refine ⟨xD, h, by simpa using isSquare_double hN h (e := 0) (by ring),
    isSquare_double hN h (by ring), by simpa using isSquare_double hN h (e := -N) (by ring),
    by simpa using double_sub_ne hN h hD (e := 0) (by ring), double_sub_ne hN h hD (by ring),
    by simpa using double_sub_ne hN h hD (e := -N) (by ring)⟩

/-- If an egg point is `R₀ + 2R` with `R₀ ∈ E[2]`, then `2R` has order `> 2`. -/
theorem double_ne_of_egg (hN : 0 < N) {Q R₀ R : (curve N).Point} {x : ℚ} (h : HasX Q x)
    (h1 : -N < x) (h2 : x < 0) (hR₀ : R₀ + R₀ = 0) (hQ : Q = R₀ + (R + R)) :
    R + R + (R + R) ≠ 0 := by
  intro hD
  rw [add_self_eq_zero_of_four hN.ne' hD, add_zero] at hQ
  exact h.add_self_ne_zero hN h1 h2 (by rw [hQ, hR₀])

/-- An egg point (`x < 0`) is never in `2E`. -/
theorem not_egg_double (hN : 0 < N) {Q R : (curve N).Point} {x : ℚ} (h : HasX Q x) (h2 : x < 0)
    (hQ : Q = R + R) : False := by
  subst hQ
  have := isSquare_double hN.ne' h (e := 0) (by ring)
  rw [sub_zero] at this
  exact not_isSquare_of_neg h2 this

/-- An egg point is never in `T + 2E` (sign kill: `x(T + 2R) = N(x_D + N)/(x_D − N) ≥ 0`). -/
theorem not_egg_T_add_double (hN : 0 < N) {Q R : (curve N).Point} {x : ℚ} (h : HasX Q x)
    (h1 : -N < x) (h2 : x < 0) (hQ : Q = T hN.ne' + (R + R)) : False := by
  have hD := double_ne_of_egg hN h h1 h2 (T_add_T hN.ne') hQ
  obtain ⟨xD, hxD, -, sN, sM, -, nN, -⟩ := double_data hN.ne' hD
  rw [hQ, add_comm] at h
  have hx := h.unique (hxD.add_T hN.ne' (sub_ne_zero.mp nN))
  have : 0 ≤ x := by
    rw [hx]
    exact div_nonneg (mul_nonneg hN.le sM.nonneg) sN.nonneg
  linarith

/-- **Single point in `S + 2E`:** `κ(Q) = κ(S) = (−1, −N)`. -/
theorem single_of_S (hN : 0 < N) {Q R : (curve N).Point} {x : ℚ} (h : HasX Q x)
    (h1 : -N < x) (h2 : x < 0) (hQ : Q = S hN.ne' + (R + R)) :
    IsSquare (-x) ∧ IsSquare (-N * (x - N)) := by
  have hD := double_ne_of_egg hN h h1 h2 (S_add_S hN.ne') hQ
  obtain ⟨xD, hxD, s0, -, sM, n0, -, nM⟩ := double_data hN.ne' hD
  rw [hQ] at h
  have hx := h.unique (hxD.S_add hN.ne' n0)
  subst hx
  constructor
  · rw [show -(-N ^ 2 / xD) = N ^ 2 / xD by ring]
    exact (IsSquare.sq N).div s0
  · rw [show -N * (-N ^ 2 / xD - N) = N ^ 2 * (xD + N) / xD by field_simp; ring]
    exact ((IsSquare.sq N).mul sM).div s0

theorem U_add_U (hN : N ≠ 0) : U hN + U hN = 0 :=
  Point.add_self_of_Y_eq (by simp [curve, negY])

/-- **Single point in `U + 2E`:** `κ(Q) = κ(U) = (−N, −2N, 2)`. -/
theorem single_of_U (hN : 0 < N) {Q R : (curve N).Point} {x : ℚ} (h : HasX Q x)
    (h1 : -N < x) (h2 : x < 0) (hQ : Q = U hN.ne' + (R + R)) :
    IsSquare (-N * x) ∧ IsSquare (-2 * N * (x - N)) ∧ IsSquare (2 * (x + N)) := by
  have hD := double_ne_of_egg hN h h1 h2 (U_add_U hN.ne') hQ
  obtain ⟨xD, hxD, s0, sN, sM, -, -, nM⟩ := double_data hN.ne' hD
  rw [hQ, add_comm] at h
  have hx := h.unique (hxD.add_U hN.ne' (fun h0 => nM (by rw [h0]; ring)))
  subst hx
  refine ⟨?_, ?_, ?_⟩
  · rw [show -N * (-N * (xD - N) / (xD + N)) = N ^ 2 * (xD - N) / (xD + N) by ring]
    exact ((IsSquare.sq N).mul sN).div sM
  · rw [show -2 * N * (-N * (xD - N) / (xD + N) - N) = (2 * N) ^ 2 * xD / (xD + N) by
      field_simp; ring]
    exact ((IsSquare.sq _).mul s0).div sM
  · rw [show 2 * (-N * (xD - N) / (xD + N) + N) = (2 * N) ^ 2 / (xD + N) by field_simp; ring]
    exact (IsSquare.sq _).div sM

/-- `κ(x) ∈ κ(E[2])` for an egg point: by sign only the `S`- and `U`-classes can occur. -/
def IsTorsionClass (N x : ℚ) : Prop :=
  (IsSquare (-x) ∧ IsSquare (-N * (x - N))) ∨ (IsSquare (-N * x) ∧ IsSquare (-2 * N * (x - N)))

/-- `κ(x)κ(x') ∈ κ(E[2])` for two egg points: by sign only the `0`- and `T`-classes can occur. -/
def IsTorsionPair (N x x' : ℚ) : Prop :=
  (IsSquare (x * x') ∧ IsSquare ((x - N) * (x' - N))) ∨
    (IsSquare (N * x * x') ∧ IsSquare (2 * (x - N) * (x' - N)))

/-- **Single-point relation.** An egg point in `E[2] + 2E` has a torsion Kummer class
(`S` or `U`; the classes of `0` and `T` are excluded by sign). -/
theorem torsionClass_of_double (hN : 0 < N) {Q R₀ R : (curve N).Point} {x : ℚ} (h : HasX Q x)
    (h1 : -N < x) (h2 : x < 0) (hR₀ : R₀ + R₀ = 0) (hQ : Q = R₀ + (R + R)) :
    IsTorsionClass N x := by
  rcases two_torsion hN.ne' hR₀ with rfl | rfl | rfl | rfl
  · rw [zero_add] at hQ
    exact (not_egg_double hN h h2 hQ).elim
  · exact .inl (single_of_S hN h h1 h2 hQ)
  · exact (not_egg_T_add_double hN h h1 h2 hQ).elim
  · have := single_of_U hN h h1 h2 hQ
    exact .inr ⟨this.1, this.2.1⟩

/-! ### The pair relation -/

/-- The third Kummer coordinate is determined by the other two: for points off `E[2]`,
`A·x₁x₂ = □` and `B·(x₁ − N)(x₂ − N) = □` give `AB·(x₁ + N)(x₂ + N) = □`. -/
theorem isSquare_plus_pair {x₁ x₂ y₁ y₂ A B : ℚ} (hy₁ : y₁ ^ 2 = x₁ ^ 3 - N ^ 2 * x₁)
    (hy₂ : y₂ ^ 2 = x₂ ^ 3 - N ^ 2 * x₂) (h₁0 : y₁ ≠ 0) (h₂0 : y₂ ≠ 0)
    (hA : IsSquare (A * (x₁ * x₂))) (hB : IsSquare (B * ((x₁ - N) * (x₂ - N)))) :
    IsSquare (A * B * ((x₁ + N) * (x₂ + N))) := by
  have d₁ : x₁ ^ 3 - N ^ 2 * x₁ ≠ 0 := by rw [← hy₁]; exact pow_ne_zero 2 h₁0
  have d₂ : x₂ ^ 3 - N ^ 2 * x₂ ≠ 0 := by rw [← hy₂]; exact pow_ne_zero 2 h₂0
  have : A * B * ((x₁ + N) * (x₂ + N)) = (A * (x₁ * x₂)) * (B * ((x₁ - N) * (x₂ - N))) *
      ((x₁ + N) * (x₂ + N) / (y₁ * y₂)) ^ 2 := by
    rw [div_pow, mul_pow (y₁), hy₁, hy₂, ← mul_div_assoc, eq_div_iff (mul_ne_zero d₁ d₂)]
    ring
  rw [this]
  exact (hA.mul hB).mul (IsSquare.sq _)

/-- `(Q + R₀) + (Q + R₀) = Q + Q` for `R₀ ∈ E[2]`. -/
theorem add_two_torsion_ne (hN : 0 < N) {Q R₀ : (curve N).Point} {x : ℚ} (h : HasX Q x)
    (h1 : -N < x) (h2 : x < 0) (hR₀ : R₀ + R₀ = 0) : Q + R₀ + (Q + R₀) ≠ 0 := by
  rw [add_add_add_comm, hR₀, add_zero]
  exact h.add_self_ne_zero hN h1 h2

/-- **Pair relation, difference in `2E`:** `κ(Q₁) = κ(Q₂)`. -/
theorem pair_of_zero (hN : 0 < N) {Q₁ Q₂ R : (curve N).Point} {x₁ x₂ : ℚ} (h₁ : HasX Q₁ x₁)
    (h₂ : HasX Q₂ x₂) (h1₂ : -N < x₂) (h2₂ : x₂ < 0) (hQ : Q₁ = Q₂ + (R + R)) :
    IsSquare (x₁ * x₂) ∧ IsSquare ((x₁ - N) * (x₂ - N)) ∧ IsSquare ((x₁ + N) * (x₂ + N)) := by
  have hP := h₂.add_self_ne_zero hN h1₂ h2₂
  rw [hQ] at h₁
  have c0 := classes_add_two_smul hN.ne' h₂ hP h₁ (e := 0) (by ring)
  have cN := classes_add_two_smul hN.ne' h₂ hP h₁ (e := N) (by ring)
  have cM := classes_add_two_smul hN.ne' h₂ hP h₁ (e := -N) (by ring)
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_zero, sub_zero, mul_comm] at c0; exact c0
  · rw [mul_comm] at cN; exact cN
  · rw [sub_neg_eq_add, sub_neg_eq_add, mul_comm] at cM; exact cM

/-- **Pair relation, difference in `T + 2E`:** `κ(Q₁)κ(Q₂) = κ(T) = (N, 2, 2N)`. -/
theorem pair_of_T (hN : 0 < N) {Q₁ Q₂ R : (curve N).Point} {x₁ x₂ : ℚ} (h₁ : HasX Q₁ x₁)
    (h₂ : HasX Q₂ x₂) (h1₁ : -N < x₁) (h2₁ : x₁ < 0) (h1₂ : -N < x₂) (h2₂ : x₂ < 0)
    (hQ : Q₁ = Q₂ + T hN.ne' + (R + R)) :
    IsSquare (N * x₁ * x₂) ∧ IsSquare (2 * (x₁ - N) * (x₂ - N)) ∧
      IsSquare (2 * N * (x₁ + N) * (x₂ + N)) := by
  have hN' := hN.ne'
  have hP := add_two_torsion_ne hN h₂ h1₂ h2₂ (T_add_T hN')
  have n₂ : x₂ - N ≠ 0 := by intro h0; linarith
  have m₂ : x₂ + N ≠ 0 := by intro h0; linarith
  have hxP := h₂.add_T hN' (sub_ne_zero.mp n₂)
  rw [hQ] at h₁
  have c0 := classes_add_two_smul hN' hxP hP h₁ (e := 0) (by ring)
  have cN := classes_add_two_smul hN' hxP hP h₁ (e := N) (by ring)
  obtain ⟨y₁, hy₁, -⟩ := h₁
  obtain ⟨y₂, hy₂, -⟩ := h₂
  have hy₁' := (nonsingular_iff hN').mp hy₁
  have hy₂' := (nonsingular_iff hN').mp hy₂
  have A : IsSquare (N * x₁ * x₂) := by
    have e : N * x₁ * x₂ = ((N * (x₂ + N) / (x₂ - N) - 0) * (x₁ - 0)) * (y₂ / (x₂ + N)) ^ 2 := by
      rw [div_pow, hy₂']
      field_simp
      ring
    rw [e]
    exact c0.mul (IsSquare.sq _)
  have B : IsSquare (2 * (x₁ - N) * (x₂ - N)) := by
    have e : 2 * (x₁ - N) * (x₂ - N) =
        ((N * (x₂ + N) / (x₂ - N) - N) * (x₁ - N)) * ((x₂ - N) / N) ^ 2 := by
      field_simp
      ring
    rw [e]
    exact cN.mul (IsSquare.sq _)
  refine ⟨A, B, ?_⟩
  have C := isSquare_plus_pair hy₁' hy₂' (y_ne_zero hN h2₁ h1₁ hy₁') (y_ne_zero hN h2₂ h1₂ hy₂')
    (A := N) (B := 2) (by rw [← mul_assoc]; exact A) (by rw [← mul_assoc]; exact B)
  rw [show N * 2 * ((x₁ + N) * (x₂ + N)) = 2 * N * (x₁ + N) * (x₂ + N) by ring] at C
  exact C

/-- A difference in `S + 2E` is impossible for two egg points (sign kill). -/
theorem not_pair_of_S (hN : 0 < N) {Q₁ Q₂ R : (curve N).Point} {x₁ x₂ : ℚ} (h₁ : HasX Q₁ x₁)
    (h₂ : HasX Q₂ x₂) (h2₁ : x₁ < 0) (h1₂ : -N < x₂) (h2₂ : x₂ < 0)
    (hQ : Q₁ = Q₂ + S hN.ne' + (R + R)) : False := by
  have hN' := hN.ne'
  have hP := add_two_torsion_ne hN h₂ h1₂ h2₂ (S_add_S hN')
  have hxP := h₂.S_add hN' h2₂.ne
  rw [add_comm] at hxP
  rw [hQ] at h₁
  have c0 := classes_add_two_smul hN' hxP hP h₁ (e := 0) (by ring)
  rw [sub_zero, sub_zero] at c0
  refine not_isSquare_of_neg (mul_neg_of_pos_of_neg ?_ h2₁) c0
  exact div_pos_of_neg_of_neg (by nlinarith) h2₂

/-- A difference in `U + 2E` is impossible for two egg points (sign kill). -/
theorem not_pair_of_U (hN : 0 < N) {Q₁ Q₂ R : (curve N).Point} {x₁ x₂ : ℚ} (h₁ : HasX Q₁ x₁)
    (h₂ : HasX Q₂ x₂) (h2₁ : x₁ < 0) (h1₂ : -N < x₂) (h2₂ : x₂ < 0)
    (hQ : Q₁ = Q₂ + U hN.ne' + (R + R)) : False := by
  have hN' := hN.ne'
  have hP := add_two_torsion_ne hN h₂ h1₂ h2₂ (U_add_U hN')
  have hxP := h₂.add_U hN' (by intro h0; linarith)
  rw [hQ] at h₁
  have c0 := classes_add_two_smul hN' hxP hP h₁ (e := 0) (by ring)
  rw [sub_zero, sub_zero] at c0
  refine not_isSquare_of_neg (mul_neg_of_pos_of_neg ?_ h2₁) c0
  exact div_pos (by nlinarith) (by linarith)

/-- **Pair relation.** Two egg points whose difference lies in `E[2] + 2E` have `κ(Q₁)κ(Q₂)` in
`κ(E[2])` (`0` or `T`; the classes of `S` and `U` are excluded by sign). -/
theorem torsionPair_of_double (hN : 0 < N) {Q₁ Q₂ R₀ R : (curve N).Point} {x₁ x₂ : ℚ}
    (h₁ : HasX Q₁ x₁) (h₂ : HasX Q₂ x₂) (h1₁ : -N < x₁) (h2₁ : x₁ < 0) (h1₂ : -N < x₂)
    (h2₂ : x₂ < 0) (hR₀ : R₀ + R₀ = 0) (hQ : Q₁ = Q₂ + R₀ + (R + R)) : IsTorsionPair N x₁ x₂ := by
  rcases two_torsion hN.ne' hR₀ with rfl | rfl | rfl | rfl
  · rw [add_zero] at hQ
    have := pair_of_zero hN h₁ h₂ h1₂ h2₂ hQ
    exact .inl ⟨this.1, this.2.1⟩
  · exact (not_pair_of_S hN h₁ h₂ h2₁ h1₂ h2₂ hQ).elim
  · have := pair_of_T hN h₁ h₂ h1₁ h2₁ h1₂ h2₂ hQ
    exact .inr ⟨this.1, this.2.1⟩
  · exact (not_pair_of_U hN h₁ h₂ h2₁ h1₂ h2₂ hQ).elim

/-! ### A5: the general dichotomy for a rank-one configuration -/

/-- **A5, sharp form.** If the three points of a positive configuration lie in `ℤG + E[2]`, then one
of them has a torsion Kummer class, or `κ(Q₁)κ(Q₂)` is a torsion class. (Parity pigeonhole on the
indices: an even index puts `Qᵢ` in `E[2] + 2E`; if all are odd, `Q₁ − Q₂ ∈ E[2] + 2E`.) -/
theorem inRankOne_dichotomy' {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃)
    {Q₁ Q₂ Q₃ : (curve N).Point} (h₁ : HasX Q₁ x₁) (h₂ : HasX Q₂ x₂) (h₃ : HasX Q₃ x₃)
    (hQ : InRankOne Q₁ Q₂ Q₃) :
    IsTorsionClass N x₁ ∨ IsTorsionClass N x₂ ∨ IsTorsionClass N x₃ ∨ IsTorsionPair N x₁ x₂ := by
  obtain ⟨G, k₁, k₂, k₃, R₁, R₂, R₃, hR₁, hR₂, hR₃, e₁, e₂, e₃⟩ := hQ
  have hN := hc.pos
  have even_case {Q R : (curve N).Point} {k : ℤ} {x : ℚ} (h : HasX Q x) (h1 : -N < x) (h2 : x < 0)
      (hR : R + R = 0) (e : Q = k • G + R) (hk : Even k) : IsTorsionClass N x := by
    obtain ⟨m, rfl⟩ := hk
    exact torsionClass_of_double hN h h1 h2 hR (R := m • G) (by rw [e, add_zsmul]; abel)
  rcases Int.even_or_odd k₁ with hk₁ | hk₁
  · exact .inl (even_case h₁ hc.lt₁ hc.neg₁ hR₁ e₁ hk₁)
  rcases Int.even_or_odd k₂ with hk₂ | hk₂
  · exact .inr (.inl (even_case h₂ hc.lt₂ hc.neg₂ hR₂ e₂ hk₂))
  rcases Int.even_or_odd k₃ with hk₃ | hk₃
  · exact .inr (.inr (.inl (even_case h₃ hc.lt₃ hc.neg₃ hR₃ e₃ hk₃)))
  refine .inr (.inr (.inr ?_))
  obtain ⟨m, hm⟩ := hk₁.sub_odd hk₂
  have hk : k₁ = k₂ + (m + m) := by linarith
  refine torsionPair_of_double hN h₁ h₂ hc.lt₁ hc.neg₁ hc.lt₂ hc.neg₂
    (R₀ := R₁ + R₂) (by rw [add_add_add_comm, hR₁, hR₂, add_zero]) (R := m • G) ?_
  rw [e₁, e₂, hk, add_zsmul,
    show k₂ • G + R₂ + (R₁ + R₂) + (m • G + m • G) =
      k₂ • G + (m • G + m • G) + R₁ + (R₂ + R₂) by abel, hR₂, add_zero, add_zsmul]

/-- **A5 (as stated in the brief).** Some `Qⱼ ∈ E[2] + 2E` or some pair `Qᵢ − Qⱼ ∈ E[2] + 2E`, in
explicit square form. -/
theorem inRankOne_dichotomy {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃)
    {Q₁ Q₂ Q₃ : (curve N).Point} (h₁ : HasX Q₁ x₁) (h₂ : HasX Q₂ x₂) (h₃ : HasX Q₃ x₃)
    (hQ : InRankOne Q₁ Q₂ Q₃) :
    IsTorsionClass N x₁ ∨ IsTorsionClass N x₂ ∨ IsTorsionClass N x₃ ∨
      IsTorsionPair N x₁ x₂ ∨ IsTorsionPair N x₁ x₃ ∨ IsTorsionPair N x₂ x₃ := by
  rcases inRankOne_dichotomy' hc h₁ h₂ h₃ hQ with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))

/-! ### A3, A4: the Kummer relations of the rank-one pattern -/

/-- The Kummer relations of the pattern `(aG, bG + T, cG + U)`, `a, b` odd, `c` even:
`κ(Q₁)κ(Q₂) = κ(T) = (N, 2, 2N)` (since `Q₁ − Q₂ − T = (a − b)G ∈ 2E`) and
`κ(Q₃) = κ(U) = (−N, −2N, 2)` (since `Q₃ − U = cG ∈ 2E`). -/
theorem pattern_relations (hN : 0 < N) {G : (curve N).Point} {a b c : ℕ} {x₁ x₂ x₃ : ℚ}
    (hc : IsConfig N x₁ x₂ x₃) (h₁ : HasX (a • G) x₁) (h₂ : HasX (b • G + T hN.ne') x₂)
    (h₃ : HasX (c • G + U hN.ne') x₃) (ha : Odd a) (hb : Odd b) (hcev : Even c) :
    (IsSquare (N * x₁ * x₂) ∧ IsSquare (2 * (x₁ - N) * (x₂ - N)) ∧
      IsSquare (2 * N * (x₁ + N) * (x₂ + N))) ∧
    (IsSquare (-N * x₃) ∧ IsSquare (-2 * N * (x₃ - N)) ∧ IsSquare (2 * (x₃ + N))) := by
  constructor
  · obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    refine pair_of_T hN h₁ h₂ hc.lt₁ hc.neg₁ hc.lt₂ hc.neg₂ (R := ((i : ℤ) - j) • G) ?_
    rw [add_assoc (_ • G), T_add_T, add_zero, ← natCast_zsmul, ← natCast_zsmul, ← add_zsmul,
      ← add_zsmul]
    congr 1
    push_cast
    ring
  · obtain ⟨k, rfl⟩ := hcev
    exact single_of_U hN h₃ hc.lt₃ hc.neg₃ (R := k • G) (by rw [add_nsmul, add_comm])

/-- Points with abscissas `x₁, x₂, x₃` of a configuration give `IsConfigPts`. -/
theorem exists_isConfigPts {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃) {P₁ P₂ P₃ : (curve N).Point}
    (h₁ : HasX P₁ x₁) (h₂ : HasX P₂ x₂) (h₃ : HasX P₃ x₃) :
    ∃ y₁ y₂ y₃, IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃ := by
  obtain ⟨y₁, hy₁, -⟩ := h₁
  obtain ⟨y₂, hy₂, -⟩ := h₂
  obtain ⟨y₃, hy₃, -⟩ := h₃
  have hN := hc.pos.ne'
  exact ⟨y₁, y₂, y₃, ⟨hc, (nonsingular_iff hN).mp hy₁, (nonsingular_iff hN).mp hy₂,
    (nonsingular_iff hN).mp hy₃⟩⟩

/-- **A3 (pair relation).** In the rank-one pattern, `κ(Q₁)κ(Q₂) = κ(T) = (N, 2, 2N)`. -/
theorem pattern_pair (hN : 0 < N) (hp : Pattern N hN) :
    ∃ x₁ x₂ x₃ y₁ y₂ y₃, IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃ ∧
      IsSquare (N * x₁ * x₂) ∧ IsSquare (2 * (x₁ - N) * (x₂ - N)) ∧
      IsSquare (2 * N * (x₁ + N) * (x₂ + N)) := by
  obtain ⟨G, a, b, c, x₁, x₂, x₃, hc, g₁, g₂, g₃, ha, hb, hcev, -⟩ := hp
  obtain ⟨y₁, y₂, y₃, hcp⟩ := exists_isConfigPts hc g₁ g₂ g₃
  exact ⟨x₁, x₂, x₃, y₁, y₂, y₃, hcp, (pattern_relations hN hc g₁ g₂ g₃ ha hb hcev).1⟩

/-- **Single-point relation of the pattern.** `κ(Q₃) = κ(U) = (−N, −2N, 2)`. -/
theorem pattern_single (hN : 0 < N) (hp : Pattern N hN) :
    ∃ x₁ x₂ x₃ y₁ y₂ y₃, IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃ ∧
      IsSquare (-N * x₃) ∧ IsSquare (-2 * N * (x₃ - N)) ∧ IsSquare (2 * (x₃ + N)) := by
  obtain ⟨G, a, b, c, x₁, x₂, x₃, hc, g₁, g₂, g₃, ha, hb, hcev, -⟩ := hp
  obtain ⟨y₁, y₂, y₃, hcp⟩ := exists_isConfigPts hc g₁ g₂ g₃
  exact ⟨x₁, x₂, x₃, y₁, y₂, y₃, hcp, (pattern_relations hN hc g₁ g₂ g₃ ha hb hcev).2⟩

/-- **A4 (sum relation).** In the rank-one pattern, `κ(Q₁)κ(Q₂)κ(Q₃) = κ(S) = (−1, −N, N)`, i.e.
`Q₁ + Q₂ + Q₃ − S ∈ 2E` read through `κ`. The first coordinate is also
`IsConfigPts.isSquare_neg_prod` (true for every configuration). -/
theorem pattern_sum (hN : 0 < N) (hp : Pattern N hN) :
    ∃ x₁ x₂ x₃ y₁ y₂ y₃, IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃ ∧
      IsSquare (-(x₁ * x₂ * x₃)) ∧ IsSquare (-N * (x₁ - N) * (x₂ - N) * (x₃ - N)) ∧
      IsSquare (N * (x₁ + N) * (x₂ + N) * (x₃ + N)) := by
  obtain ⟨G, a, b, c, x₁, x₂, x₃, hc, g₁, g₂, g₃, ha, hb, hcev, -⟩ := hp
  obtain ⟨y₁, y₂, y₃, hcp⟩ := exists_isConfigPts hc g₁ g₂ g₃
  obtain ⟨⟨A₀, AN, AM⟩, B₀, BN, BM⟩ := pattern_relations hN hc g₁ g₂ g₃ ha hb hcev
  have hN' := hN.ne'
  refine ⟨x₁, x₂, x₃, y₁, y₂, y₃, hcp, ?_, ?_, ?_⟩
  · rw [show -(x₁ * x₂ * x₃) = N * x₁ * x₂ * (-N * x₃) / N ^ 2 by field_simp]
    exact (A₀.mul B₀).div (IsSquare.sq N)
  · rw [show -N * (x₁ - N) * (x₂ - N) * (x₃ - N) =
      2 * (x₁ - N) * (x₂ - N) * (-2 * N * (x₃ - N)) / 2 ^ 2 by ring]
    exact (AN.mul BN).div (IsSquare.sq 2)
  · rw [show N * (x₁ + N) * (x₂ + N) * (x₃ + N) =
      2 * N * (x₁ + N) * (x₂ + N) * (2 * (x₃ + N)) / 2 ^ 2 by ring]
    exact (AM.mul BM).div (IsSquare.sq 2)

/-- A positive configuration in a subgroup of rank one yields the pattern (Asiryan, Lemmas 2–3,
unconditional in the repo: `rankOneReduction_of_pos`). -/
theorem pattern_of_inRankOne {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃)
    {Q₁ Q₂ Q₃ : (curve N).Point} (h₁ : HasX Q₁ x₁) (h₂ : HasX Q₂ x₂) (h₃ : HasX Q₃ x₃)
    (hQ : InRankOne Q₁ Q₂ Q₃) : Pattern N hc.pos :=
  rankOneReduction_of_pos hc.pos hc h₁ h₂ h₃ hQ

/-- **Rank one forces the Kummer relations.** If a positive configuration lies in `ℤG + E[2]`, then
some (possibly different) positive configuration satisfies the pair relation `κ(Q₁)κ(Q₂) = κ(T)`,
the single-point relation `κ(Q₃) = κ(U)` and hence the sum relation `κ(Q₁)κ(Q₂)κ(Q₃) = κ(S)`. -/
theorem rankOne_relations {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃)
    {Q₁ Q₂ Q₃ : (curve N).Point} (h₁ : HasX Q₁ x₁) (h₂ : HasX Q₂ x₂) (h₃ : HasX Q₃ x₃)
    (hQ : InRankOne Q₁ Q₂ Q₃) :
    ∃ z₁ z₂ z₃ y₁ y₂ y₃, IsConfigPts N z₁ z₂ z₃ y₁ y₂ y₃ ∧
      IsSquare (N * z₁ * z₂) ∧ IsSquare (2 * (z₁ - N) * (z₂ - N)) ∧
      IsSquare (-N * z₃) ∧ IsSquare (-2 * N * (z₃ - N)) := by
  obtain ⟨G, a, b, c, z₁, z₂, z₃, hc', g₁, g₂, g₃, ha, hb, hcev, -⟩ :=
    pattern_of_inRankOne hc h₁ h₂ h₃ hQ
  obtain ⟨y₁, y₂, y₃, hcp⟩ := exists_isConfigPts hc' g₁ g₂ g₃
  obtain ⟨⟨A₀, AN, -⟩, B₀, BN, -⟩ := pattern_relations hc.pos hc' g₁ g₂ g₃ ha hb hcev
  exact ⟨z₁, z₂, z₃, y₁, y₂, y₃, hcp, A₀, AN, B₀, BN⟩

/-- Consistency check: the first coordinate of `pattern_sum` is the general
`IsConfigPts.isSquare_neg_prod`. -/
example {x₁ x₂ x₃ y₁ y₂ y₃ : ℚ} (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) :
    IsSquare (-(x₁ * x₂ * x₃)) := hc.isSquare_neg_prod

/-- **The full rank-one square system** in Asiryan's abscissas `X_a = x(aG) = x₁`, `X_b = x(bG)`,
`X_c = x(cG)`: equation (24) together with `κ(aG) = κ(bG)` (odd multiples) and `κ(cG) = 1`
(even multiple). -/
theorem pattern_system (hN : 0 < N) {G : (curve N).Point} {a b c : ℕ} {x₁ x₂ x₃ Xb Xc : ℚ}
    (hc : IsConfig N x₁ x₂ x₃) (h₁ : HasX (a • G) x₁) (h₂ : HasX (b • G + T hN.ne') x₂)
    (h₃ : HasX (c • G + U hN.ne') x₃) (hXb : HasX (b • G) Xb) (hXc : HasX (c • G) Xc)
    (ha : Odd a) (hb : Odd b) (hcev : Even c) :
    x₁ * Xb + x₁ * Xc - Xb * Xc + N ^ 2 = 0 ∧
      IsSquare (x₁ * Xb) ∧ IsSquare ((x₁ - N) * (Xb - N)) ∧ IsSquare ((x₁ + N) * (Xb + N)) ∧
      IsSquare Xc ∧ IsSquare (Xc - N) ∧ IsSquare (Xc + N) := by
  have hN' := hN.ne'
  have e24 := eq24 hc hXb hXc h₂ h₃
  have hP : b • G + b • G ≠ 0 := by
    have := h₂.add_self_ne_zero hN hc.lt₂ hc.neg₂
    intro h0
    apply this
    rw [show b • G + T hN' + (b • G + T hN') = b • G + b • G + (T hN' + T hN') by abel, T_add_T,
      add_zero]
    exact h0
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have e : (2 * i + 1) • G = (2 * j + 1) • G + (((i : ℤ) - j) • G + ((i : ℤ) - j) • G) := by
    rw [← natCast_zsmul, ← natCast_zsmul, ← add_zsmul, ← add_zsmul]
    congr 1
    push_cast
    ring
  rw [e] at h₁
  have c0 := classes_add_two_smul hN' hXb hP h₁ (e := 0) (by ring)
  have cN := classes_add_two_smul hN' hXb hP h₁ (e := N) (by ring)
  have cM := classes_add_two_smul hN' hXb hP h₁ (e := -N) (by ring)
  obtain ⟨k, rfl⟩ := hcev
  rw [add_nsmul] at hXc
  refine ⟨e24, ?_, ?_, ?_, ?_, isSquare_double hN' hXc (by ring), ?_⟩
  · rw [sub_zero, sub_zero, mul_comm] at c0; exact c0
  · rw [mul_comm] at cN; exact cN
  · rw [sub_neg_eq_add, sub_neg_eq_add, mul_comm] at cM; exact cM
  · simpa using isSquare_double hN' hXc (e := 0) (by ring)
  · simpa using isSquare_double hN' hXc (e := -N) (by ring)

/-- **The rank-one system in Asiryan's variables** `t_a = −X_a/N`, `t_b = −X_b/N`. Equation (24)
gives `X_c (t_a − t_b) = N(1 + t_a t_b)`, and the Kummer relations become
`t_a t_b = □`, `(1 + t_a)(1 + t_b) = □`, `(1 − t_a)(1 − t_b) = □`, `N(1 + t_a t_b)(t_a − t_b) = □`,
`N(1 + t_b − t_a + t_a t_b)(t_a − t_b) = □` and `N(1 + t_a − t_b + t_a t_b)(t_a − t_b) = □`
(the last three are `X_c`, `X_c − N`, `X_c + N` times `(t_a − t_b)²`). -/
theorem pattern_tt (hN : 0 < N) {G : (curve N).Point} {a b c : ℕ} {x₁ x₂ x₃ Xb Xc ta tb : ℚ}
    (hc : IsConfig N x₁ x₂ x₃) (h₁ : HasX (a • G) x₁) (h₂ : HasX (b • G + T hN.ne') x₂)
    (h₃ : HasX (c • G + U hN.ne') x₃) (hXb : HasX (b • G) Xb) (hXc : HasX (c • G) Xc)
    (ha : Odd a) (hb : Odd b) (hcev : Even c) (hta : x₁ = -N * ta) (htb : Xb = -N * tb) :
    IsSquare (ta * tb) ∧ IsSquare ((1 + ta) * (1 + tb)) ∧ IsSquare ((1 - ta) * (1 - tb)) ∧
      IsSquare (N * (1 + ta * tb) * (ta - tb)) ∧
      IsSquare (N * (1 + tb - ta + ta * tb) * (ta - tb)) ∧
      IsSquare (N * (1 + ta - tb + ta * tb) * (ta - tb)) := by
  obtain ⟨e24, s₀, sN, sM, c₀, cN, cM⟩ :=
    pattern_system hN hc h₁ h₂ h₃ hXb hXc ha hb hcev
  have hN' := hN.ne'
  subst hta htb
  have hXc' : Xc * (ta - tb) = N * (1 + ta * tb) := by
    apply (mul_right_inj' hN').mp
    linear_combination -e24
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show ta * tb = -N * ta * (-N * tb) / N ^ 2 by field_simp]
    exact s₀.div (IsSquare.sq N)
  · rw [show (1 + ta) * (1 + tb) = (-N * ta - N) * (-N * tb - N) / N ^ 2 by field_simp; ring]
    exact sN.div (IsSquare.sq N)
  · rw [show (1 - ta) * (1 - tb) = (-N * ta + N) * (-N * tb + N) / N ^ 2 by field_simp; ring]
    exact sM.div (IsSquare.sq N)
  · have e : N * (1 + ta * tb) * (ta - tb) = Xc * (ta - tb) ^ 2 := by
      linear_combination (tb - ta) * hXc'
    rw [e]
    exact c₀.mul (IsSquare.sq _)
  · have e : N * (1 + tb - ta + ta * tb) * (ta - tb) = (Xc - N) * (ta - tb) ^ 2 := by
      linear_combination (tb - ta) * hXc'
    rw [e]
    exact cN.mul (IsSquare.sq _)
  · have e : N * (1 + ta - tb + ta * tb) * (ta - tb) = (Xc + N) * (ta - tb) ^ 2 := by
      linear_combination (tb - ta) * hXc'
    rw [e]
    exact cM.mul (IsSquare.sq _)

/-! ### A6: the pair relation in cuboid coordinates -/

/-- **A6.** For a rational perfect cuboid, with `x₁ = −N·ag/(de + bc)` and `x₂ = −N·bg/(df + ac)`
(`isConfigPts_of_cuboid`), the two pair conditions read in the edges and diagonals. -/
theorem IsRatCuboid.pair_iff {a b c d e f g : ℚ} (h : IsRatCuboid a b c d e f g) (hN : 0 < N) :
    (IsSquare (N * (-N * (a * g) / (d * e + b * c)) * (-N * (b * g) / (d * f + a * c))) ↔
      IsSquare (N * (a * b) * ((d * e + b * c) * (d * f + a * c)))) ∧
    (IsSquare (2 * (-N * (a * g) / (d * e + b * c) - N) * (-N * (b * g) / (d * f + a * c) - N)) ↔
      IsSquare (2 * ((d * e + b * c + a * g) * (d * f + a * c + b * g)) *
        ((d * e + b * c) * (d * f + a * c)))) := by
  have := h.pos_a; have := h.pos_b; have := h.pos_c; have := h.pos_d; have := h.pos_e
  have := h.pos_f; have := h.pos_g
  have h₁ : 0 < d * e + b * c := by positivity
  have h₂ : 0 < d * f + a * c := by positivity
  constructor
  · rw [show N * (-N * (a * g) / (d * e + b * c)) * (-N * (b * g) / (d * f + a * c)) =
      N * (a * b) * ((d * e + b * c) * (d * f + a * c)) *
        (N * g / ((d * e + b * c) * (d * f + a * c))) ^ 2 by field_simp]
    exact isSquare_mul_sq_iff (by positivity)
  · rw [show 2 * (-N * (a * g) / (d * e + b * c) - N) * (-N * (b * g) / (d * f + a * c) - N) =
      2 * ((d * e + b * c + a * g) * (d * f + a * c + b * g)) *
        ((d * e + b * c) * (d * f + a * c)) * (N / ((d * e + b * c) * (d * f + a * c))) ^ 2 by
      field_simp; ring]
    exact isSquare_mul_sq_iff (by positivity)

end PerfectCuboid.KummerAdd
