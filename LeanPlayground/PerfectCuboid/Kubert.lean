module

public import LeanPlayground.PerfectCuboid.Fiber
public import LeanPlayground.PerfectCuboid.FiberPairs
public import LeanPlayground.PerfectCuboid.FermatTriangle
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The curve `E″` of a fiber, Kubert's `ℤ/2 × ℤ/8` curve

On the fiber `(m, n)`, with `U = m² − n²`, `V = 2mn`, `W = m² + n²`, a perfect cuboid is a
rational `t` (the ratio of the third edge to the common factor of the two edges `U k`, `V k`)
with `t² + U²`, `t² + V²` and `t² + W²` all squares. The genus-5 curve of these `t` has five
elliptic quotients: the three pair curves of `LeanPlayground.PerfectCuboid.FiberPairs`, a curve
`E′` that always has positive rank, and

  `E″ : Y² = (X + V²W²)(X + U²W²)(X + U²V²)`,

which a perfect cuboid meets at `X = (UVW/t)²` (compare Cipollini, arXiv:2609.14526; Fable
round 5, `fable-new-frameworks-round5.md`, F3). This file formalizes what is
uniform in `(m, n)` about `E″`.

## Main results

* `onEpp_of_sq`, `IsPerfectCuboid.exists_onEpp` — a perfect cuboid on the fiber gives a point of
  `E″` with `X > 0` at which all three factors (and `X` itself) are squares, so the point is
  twice a rational point.
* `isSol_sq`, `IsPerfectCuboid.isSol_sq` — moving the root `−U²V²` to `0` makes `E″` the pair
  curve `y² = x (x + U⁴)(x + V⁴)` of `Descent.IsSol (U²) (V²)`; the cuboid gives a solution with
  `M² ≠ U²V² e²`. The solutions with `M² = U²V² e²` come from a point of order `4` of `E″` that is
  twice a rational point, so a descent on `E″` must allow them (unlike the descents for the
  three pair curves).
* `isSol_isogeny`, `IsPerfectCuboid.not_onFiber_of_isogeny` — `E″` is `2`-isogenous to the pair
  curve `(2UV, W²)`, which is the pair `(V, W)` of the fiber `(U, V)`: a cuboid on the fiber
  `(m, n)` gives the solution `M = UVW²e²`, `e = M s` of `IsSol (2UV) (W²)`.
* `IsPerfectCuboid.not_onFiber_of_sq` — the same through `IsSol (U²) (V²)`, when its only
  solutions have `M² = U²V² e²`.
* `kubertChange_smul` — `E″` is Kubert's curve `y² + (1 − c)xy − by = x³ − bx²`,
  `b = (2τ − 1)(τ − 1)`, `c = b/τ`, at `τ = m(m + n)/(m² + 2mn − n²)`; the change of variables
  sends the point `P₈ = (4m²n(m − n)(m + n)²W, …)` of order `8` to `(0, 0)`. So the torsion of
  `E″(ℚ)` contains `ℤ/2 × ℤ/8`, which by Mazur is all of it (Mazur is not used below).
* `torsionPts`, `onEpp_of_mem_torsionPts` — the fifteen affine points of that group.
* `not_isSquare_of_mem_torsionPts` — **the uniform torsion lemma**: for `0 < n < m`, no torsion
  point with `X > 0` is twice a rational point. The only torsion points with `X > 0` are `±P₈`,
  and `X(P₈) + U²V² = 4m³n(m − n)(m + n)³` is not a square by Fermat's right triangle theorem.
* `IsPerfectCuboid.not_onFiber_of_torsionOnly` — hence if `E″(ℚ)` is its torsion (rank `0`),
  no perfect cuboid lies on the fiber.

## What is not formalized

`TorsionOnly m n` (rank `E″(ℚ) = 0`) is a hypothesis, like `E3Trivial` in
`LeanPlayground.PerfectCuboid.Fiber`. PARI/GP proves rank `0` for `112` of the `331` fibers with
`m ≤ 40`, among them `(8, 3)`, where `Ш(E″)[2] ≠ 0`.
-/

@[expose] public section

namespace PerfectCuboid

namespace Kubert

open Fiber

variable (m n : ℚ)

/-- `(X, Y)` is an affine rational point of `E″ : Y² = (X + V²W²)(X + U²W²)(X + U²V²)`. -/
def OnEpp (X Y : ℚ) : Prop :=
  Y ^ 2 = (X + V m n ^ 2 * W m n ^ 2) * (X + U m n ^ 2 * W m n ^ 2) * (X + U m n ^ 2 * V m n ^ 2)

/-- `E″` as a Weierstrass curve over `ℚ`. -/
def epp : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := V m n ^ 2 * W m n ^ 2 + U m n ^ 2 * W m n ^ 2 + U m n ^ 2 * V m n ^ 2
  a₃ := 0
  a₄ := V m n ^ 2 * W m n ^ 2 * (U m n ^ 2 * W m n ^ 2) +
    V m n ^ 2 * W m n ^ 2 * (U m n ^ 2 * V m n ^ 2) +
    U m n ^ 2 * W m n ^ 2 * (U m n ^ 2 * V m n ^ 2)
  a₆ := V m n ^ 2 * W m n ^ 2 * (U m n ^ 2 * W m n ^ 2) * (U m n ^ 2 * V m n ^ 2)

theorem epp_equation_iff (X Y : ℚ) : (epp m n).toAffine.Equation X Y ↔ OnEpp m n X Y := by
  rw [WeierstrassCurve.Affine.equation_iff, OnEpp]
  simp only [epp]
  constructor <;> intro h <;> linear_combination h

variable {m n}

/-! ### The point of a perfect cuboid -/

/-- **Three squares give a point of `2E″`.** If `t² + U² = a²`, `t² + V² = b²` and
`t² + W² = c²`, then `X = (UVW/t)²` is a point of `E″` with `X + V²W² = (VWa/t)²`,
`X + U²W² = (UWb/t)²` and `X + U²V² = (UVc/t)²`. -/
theorem onEpp_of_sq {t a b c : ℚ} (ht : t ≠ 0) (ha : t ^ 2 + U m n ^ 2 = a ^ 2)
    (hb : t ^ 2 + V m n ^ 2 = b ^ 2) (hc : t ^ 2 + W m n ^ 2 = c ^ 2) :
    (U m n * V m n * W m n / t) ^ 2 + V m n ^ 2 * W m n ^ 2 = (V m n * W m n * a / t) ^ 2 ∧
    (U m n * V m n * W m n / t) ^ 2 + U m n ^ 2 * W m n ^ 2 = (U m n * W m n * b / t) ^ 2 ∧
    (U m n * V m n * W m n / t) ^ 2 + U m n ^ 2 * V m n ^ 2 = (U m n * V m n * c / t) ^ 2 ∧
    OnEpp m n ((U m n * V m n * W m n / t) ^ 2)
      (V m n * W m n * a / t * (U m n * W m n * b / t) * (U m n * V m n * c / t)) := by
  have h1 : (U m n * V m n * W m n / t) ^ 2 + V m n ^ 2 * W m n ^ 2 =
      (V m n * W m n * a / t) ^ 2 := by
    rw [div_pow, div_pow, div_add' _ _ _ (pow_ne_zero 2 ht), div_left_inj' (pow_ne_zero 2 ht)]
    linear_combination V m n ^ 2 * W m n ^ 2 * ha
  have h2 : (U m n * V m n * W m n / t) ^ 2 + U m n ^ 2 * W m n ^ 2 =
      (U m n * W m n * b / t) ^ 2 := by
    rw [div_pow, div_pow, div_add' _ _ _ (pow_ne_zero 2 ht), div_left_inj' (pow_ne_zero 2 ht)]
    linear_combination U m n ^ 2 * W m n ^ 2 * hb
  have h3 : (U m n * V m n * W m n / t) ^ 2 + U m n ^ 2 * V m n ^ 2 =
      (U m n * V m n * c / t) ^ 2 := by
    rw [div_pow, div_pow, div_add' _ _ _ (pow_ne_zero 2 ht), div_left_inj' (pow_ne_zero 2 ht)]
    linear_combination U m n ^ 2 * V m n ^ 2 * hc
  refine ⟨h1, h2, h3, ?_⟩
  rw [OnEpp, h1, h2, h3]
  ring

namespace IsPerfectCuboid

variable {X Y Z : ℕ}

/-- **A perfect cuboid on the fiber `(m, n)` gives a point of `2E″` with `X > 0`.** If
`Z U = X V` with `U ≠ 0`, then `t = U Y / X` has `t² + U²`, `t² + V²`, `t² + W²` squares
(`U/X` times the diagonals of the faces `XY`, `YZ` and the space diagonal), and `onEpp_of_sq`
applies. -/
theorem exists_onEpp (h : IsPerfectCuboid X Y Z) (hf : (Z : ℚ) * U m n = X * V m n)
    (hU : U m n ≠ 0) :
    ∃ x y, OnEpp m n x y ∧ 0 < x ∧ IsSquare x ∧ IsSquare (x + V m n ^ 2 * W m n ^ 2) ∧
      IsSquare (x + U m n ^ 2 * W m n ^ 2) ∧ IsSquare (x + U m n ^ 2 * V m n ^ 2) := by
  obtain ⟨⟨hX, hY, hZ, ⟨d, hd⟩, ⟨e, he⟩, -⟩, ⟨f, hf'⟩⟩ := h
  have hd' : (d : ℚ) ^ 2 = X ^ 2 + Y ^ 2 := by exact_mod_cast (by rw [hd]; ring)
  have he' : (e : ℚ) ^ 2 = Y ^ 2 + Z ^ 2 := by exact_mod_cast (by rw [he]; ring)
  have hf'' : (f : ℚ) ^ 2 = X ^ 2 + Y ^ 2 + Z ^ 2 := by exact_mod_cast (by rw [hf']; ring)
  have hX0 : (X : ℚ) ≠ 0 := by positivity
  have hY0 : (Y : ℚ) ≠ 0 := by positivity
  have hV : V m n ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hf
    rcases mul_eq_zero.mp hf with h1 | h1
    · exact (show (Z : ℚ) ≠ 0 by positivity) h1
    · exact hU h1
  have hW : W m n ≠ 0 := by
    intro h0
    have := W_sq m n
    rw [h0] at this
    have : U m n ^ 2 = 0 := by nlinarith [sq_nonneg (U m n), sq_nonneg (V m n)]
    exact hU (pow_eq_zero_iff two_ne_zero |>.mp this)
  have hVX : V m n ^ 2 * X ^ 2 = U m n ^ 2 * Z ^ 2 := by
    linear_combination -(X * V m n + Z * U m n) * hf
  have hX2 : (X : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hX0
  set t : ℚ := U m n * Y / X with ht
  have ht0 : t ≠ 0 := by positivity
  obtain ⟨h1, h2, h3, hE⟩ := onEpp_of_sq (m := m) (n := n) (t := t) (a := U m n * d / X)
    (b := U m n * e / X) (c := U m n * f / X) ht0
    (by
      rw [div_pow, div_pow, div_add' _ _ _ hX2, div_left_inj' hX2]
      linear_combination -U m n ^ 2 * hd')
    (by
      rw [div_pow, div_pow, div_add' _ _ _ hX2, div_left_inj' hX2]
      linear_combination hVX - U m n ^ 2 * he')
    (by
      rw [W_sq, div_pow, div_pow, div_add' _ _ _ hX2, div_left_inj' hX2]
      linear_combination hVX - U m n ^ 2 * hf'')
  refine ⟨_, _, hE, by positivity, ⟨_, sq _⟩, ⟨_, by rw [h1, sq]⟩, ⟨_, by rw [h2, sq]⟩,
    ⟨_, by rw [h3, sq]⟩⟩

end IsPerfectCuboid

/-! ### `E″` as the pair curve of `(U², V²)`, and its `2`-isogeny to the pair curve `(2UV, W²)` -/

/-- **`E″` is the pair curve of `(U², V²)`.** With `x = X + U²V²` the curve `E″` becomes
`y² = x (x + U⁴)(x + V⁴)`, and a solution `(M, e)` of the three pairs of a fiber gives the
solution `(UVs, M)` of `IsSol (U²) (V²)`, with `(UVs)² − U²V²M² = (UVWe)² ≠ 0`. -/
theorem isSol_sq {U V W M e r s t : ℤ} (hU : U ≠ 0) (hV : V ≠ 0) (hW : U ^ 2 + V ^ 2 = W ^ 2)
    (h1 : Descent.IsSol V W M e r s) (h2 : Descent.IsSol U W M e t s) :
    Descent.IsSol (U ^ 2) (V ^ 2) (U * V * s) M (U * W * r) (V * W * t) ∧
      (U * V * s) ^ 2 - U ^ 2 * V ^ 2 * M ^ 2 = (U * V * W * e) ^ 2 := by
  obtain ⟨hM, he, hr, hs⟩ := h1
  obtain ⟨-, -, ht, -⟩ := h2
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : 0 < M ^ 2 + W ^ 2 * e ^ 2 := by
      have := pow_pos (sq_pos_of_ne_zero hM) 1
      positivity
    nlinarith
  refine ⟨⟨mul_ne_zero (mul_ne_zero hU hV) hs0, hM, ?_, ?_⟩, ?_⟩
  · linear_combination -U ^ 2 * V ^ 2 * hs + U ^ 2 * W ^ 2 * hr + U ^ 2 * M ^ 2 * hW
  · linear_combination -U ^ 2 * V ^ 2 * hs + V ^ 2 * W ^ 2 * ht + V ^ 2 * M ^ 2 * hW
  · linear_combination -U ^ 2 * V ^ 2 * hs

/-- **The `2`-isogeny `E″ → E″/⟨(0, 0)⟩`.** The quotient of `y² = x (x + U⁴)(x + V⁴)` by the
point `(0, 0)` is the pair curve `y² = x (x + (2UV)²)(x + W⁴)`, and the image of the cuboid
point is the solution `M' = UVW²e²`, `e' = Ms` of `IsSol (2UV) (W²)`:
`M'² + (2UV)² e'² = (UV (2M² + W² e²))²` and `M'² + W⁴ e'² = (W² r t)²`. -/
theorem isSol_isogeny {U V W M e r s t : ℤ} (hU : U ≠ 0) (hV : V ≠ 0) (hW : U ^ 2 + V ^ 2 = W ^ 2)
    (h1 : Descent.IsSol V W M e r s) (h2 : Descent.IsSol U W M e t s) :
    Descent.IsSol (2 * U * V) (W ^ 2) (U * V * W ^ 2 * e ^ 2) (M * s)
      (U * V * (2 * M ^ 2 + W ^ 2 * e ^ 2)) (W ^ 2 * r * t) := by
  obtain ⟨hM, he, hr, hs⟩ := h1
  obtain ⟨-, -, ht, -⟩ := h2
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : 0 < M ^ 2 + W ^ 2 * e ^ 2 := by
      have := pow_pos (sq_pos_of_ne_zero hM) 1
      positivity
    nlinarith
  have hW0 : W ≠ 0 := by
    rintro rfl
    nlinarith [pow_pos (sq_pos_of_ne_zero hU) 1, sq_nonneg V]
  refine ⟨mul_ne_zero (mul_ne_zero (mul_ne_zero hU hV) (pow_ne_zero 2 hW0)) (pow_ne_zero 2 he),
    mul_ne_zero hM hs0, ?_, ?_⟩
  · linear_combination -4 * U ^ 2 * V ^ 2 * M ^ 2 * hs
  · linear_combination W ^ 4 * (-M ^ 2 * e ^ 2 * hW - M ^ 2 * hs + (M ^ 2 + U ^ 2 * e ^ 2) * hr +
      r ^ 2 * ht)

/-- A perfect cuboid with `U X = V Z` gives a solution of `IsSol (U²) (V²)` with
`M² ≠ U²V² e²`, and a solution of `IsSol (2UV) (W²)`. -/
theorem IsPerfectCuboid.isSol_sq {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) {U V W : ℤ}
    (hU : U ≠ 0) (hV : V ≠ 0) (hW : U ^ 2 + V ^ 2 = W ^ 2) (hf : U * X = V * Z) :
    (∃ M e r s, Descent.IsSol (U ^ 2) (V ^ 2) M e r s ∧ M ^ 2 ≠ U ^ 2 * V ^ 2 * e ^ 2) ∧
      ∃ M e r s, Descent.IsSol (2 * U * V) (W ^ 2) M e r s := by
  obtain ⟨r, s, t, h1, h2, -⟩ := h.isSol_three_pairs hV hW hf
  obtain ⟨hsol, hdiff⟩ := Kubert.isSol_sq hU hV hW h1 h2
  refine ⟨⟨_, _, _, _, hsol, fun h0 ↦ ?_⟩, ⟨_, _, _, _, Kubert.isSol_isogeny hU hV hW h1 h2⟩⟩
  have hW0 : W ≠ 0 := by
    rintro rfl
    nlinarith [pow_pos (sq_pos_of_ne_zero hU) 1, sq_nonneg V]
  have hX : (X : ℤ) ≠ 0 := by exact_mod_cast h.pos_a.ne'
  have : (U * V * W * X) ^ 2 = 0 := by linear_combination -hdiff + h0
  exact pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (mul_ne_zero hU hV) hW0) hX) this

/-- **The fiber `(m, n)` through the `(V, W)` pair of the fiber `(U, V)`.** If
`IsSol (2UV) (W²)` has no solution (for instance by `Descent.not_isSol` for the pair `(V, W)` of
the fiber `(max(U, V), min(U, V))`), then no perfect cuboid has `U X = V Z`. -/
theorem IsPerfectCuboid.not_onFiber_of_isogeny {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z)
    {U V W : ℤ} (hU : U ≠ 0) (hV : V ≠ 0) (hW : U ^ 2 + V ^ 2 = W ^ 2)
    (hpair : ∀ M e r s, ¬ Descent.IsSol (2 * U * V) (W ^ 2) M e r s) : U * X ≠ V * Z := by
  intro hf
  obtain ⟨-, M, e, r, s, hs⟩ := IsPerfectCuboid.isSol_sq h hU hV hW hf
  exact hpair M e r s hs

/-- **The fiber `(U, V)` through `E″` itself.** If every solution of `IsSol (U²) (V²)` has
`M² = U²V² e²` (for instance by `Descent.sq_eq_of_isSol_of_casesOKT`), then no perfect cuboid
has `U X = V Z`. -/
theorem IsPerfectCuboid.not_onFiber_of_sq {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z)
    {U V W : ℤ} (hU : U ≠ 0) (hV : V ≠ 0) (hW : U ^ 2 + V ^ 2 = W ^ 2)
    (hpair : ∀ M e r s, Descent.IsSol (U ^ 2) (V ^ 2) M e r s → M ^ 2 = U ^ 2 * V ^ 2 * e ^ 2) :
    U * X ≠ V * Z := by
  intro hf
  obtain ⟨⟨M, e, r, s, hs, hne⟩, -⟩ := IsPerfectCuboid.isSol_sq h hU hV hW hf
  exact hne (hpair M e r s hs)

/-! ### Kubert's form -/

/-- The Tate normal form `E(b, c) : y² + (1 − c) x y − b y = x³ − b x²`, on which `(0, 0)` is a
rational point. -/
def tateNormal (b c : ℚ) : WeierstrassCurve ℚ := ⟨1 - c, -b, -b, 0, 0⟩

/-- **Kubert's curve** with rational `ℤ/2 × ℤ/8` torsion: `E(b, c)` with `b = (2τ − 1)(τ − 1)` and
`c = b/τ`, where `(0, 0)` has order `8` (Kubert, Proc. London Math. Soc. 33 (1976)). -/
def kubertCurve (τ : ℚ) : WeierstrassCurve ℚ :=
  tateNormal ((2 * τ - 1) * (τ - 1)) ((2 * τ - 1) * (τ - 1) / τ)

variable (m n) in
/-- The Kubert parameter of `E″`: `τ = m(m + n)/(m² + 2mn − n²)`. -/
def tau : ℚ := m * (m + n) / (m ^ 2 + 2 * m * n - n ^ 2)

variable (m n) in
/-- `X(P₈) = 4m²n(m − n)(m + n)²(m² + n²) = UVW(U + V + W)`, the abscissa of a point of order `8`
of `E″`. -/
def x8 : ℚ := 4 * m ^ 2 * n * (m - n) * (m + n) ^ 2 * (m ^ 2 + n ^ 2)

variable (m n) in
/-- `Y(P₈) = 4m³n(m − n)(m + n)³(m² + n²)(m² + 2mn − n²)`. -/
def y8 : ℚ := 4 * m ^ 3 * n * (m - n) * (m + n) ^ 3 * (m ^ 2 + n ^ 2) * (m ^ 2 + 2 * m * n - n ^ 2)

variable (m n) in
/-- The change of variables `(X, Y) = (u²x + X(P₈), u³y + u²sx + Y(P₈))` from Kubert's form to
`E″`, with `u = 2m(m + n)(m² + 2mn − n²)` and `s = m⁴ + 4m³n − n⁴` (the slope of the tangent at
`P₈`): it moves `P₈` to `(0, 0)` and its tangent to `y = 0`. -/
def kubertChange (hu : 2 * m * (m + n) * (m ^ 2 + 2 * m * n - n ^ 2) ≠ 0) :
    WeierstrassCurve.VariableChange ℚ :=
  ⟨Units.mk0 _ hu, x8 m n, m ^ 4 + 4 * m ^ 3 * n - n ^ 4, y8 m n⟩

/-- **`E″` is Kubert's `ℤ/2 × ℤ/8` curve** at `τ = m(m + n)/(m² + 2mn − n²)`. -/
theorem kubertChange_smul (hm : m ≠ 0) (hmn : m + n ≠ 0) (hd : m ^ 2 + 2 * m * n - n ^ 2 ≠ 0) :
    kubertChange m n (by simp [hm, hmn, hd]) • epp m n = kubertCurve (tau m n) := by
  have hd2 : m * (m + 2 * n) - n ^ 2 ≠ 0 := by contrapose! hd; linear_combination hd
  ext <;> simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆, kubertChange, Units.val_inv_eq_inv_val, Units.val_mk0,
    epp, kubertCurve, tateNormal, tau, x8, y8, U, V, W] <;> field_simp <;> ring

/-! ### The torsion points and the uniform torsion lemma -/

variable (m n) in
/-- The fifteen affine points of the subgroup `ℤ/2 × ℤ/8` of `E″(ℚ)` (with the point at infinity
the sixteenth): `±P₈`, `±3P₈`, `±P₈ + T`, `±3P₈ + T` of order `8` (abscissas `X(P₈)`,
`−4mn²(m − n)²(m + n)W`, `−4mn²(m − n)(m + n)²W`, `−4m²n(m − n)²(m + n)W`), `±2P₈`, `±2P₈ + T` of
order `4` (abscissas `0` and `−2U²V²`) and the three points of order `2`. -/
def torsionPts : List (ℚ × ℚ) :=
  [(x8 m n, y8 m n), (x8 m n, -y8 m n),
   (-4 * m * n ^ 2 * (m - n) ^ 2 * (m + n) * (m ^ 2 + n ^ 2),
     4 * m * n ^ 3 * (m - n) ^ 3 * (m + n) * (m ^ 2 + n ^ 2) * (m ^ 2 + 2 * m * n - n ^ 2)),
   (-4 * m * n ^ 2 * (m - n) ^ 2 * (m + n) * (m ^ 2 + n ^ 2),
     -(4 * m * n ^ 3 * (m - n) ^ 3 * (m + n) * (m ^ 2 + n ^ 2) * (m ^ 2 + 2 * m * n - n ^ 2))),
   (-4 * m * n ^ 2 * (m - n) * (m + n) ^ 2 * (m ^ 2 + n ^ 2),
     4 * m * n ^ 3 * (m - n) * (m + n) ^ 3 * (m ^ 2 + n ^ 2) * (m ^ 2 - 2 * m * n - n ^ 2)),
   (-4 * m * n ^ 2 * (m - n) * (m + n) ^ 2 * (m ^ 2 + n ^ 2),
     -(4 * m * n ^ 3 * (m - n) * (m + n) ^ 3 * (m ^ 2 + n ^ 2) * (m ^ 2 - 2 * m * n - n ^ 2))),
   (-4 * m ^ 2 * n * (m - n) ^ 2 * (m + n) * (m ^ 2 + n ^ 2),
     4 * m ^ 3 * n * (m - n) ^ 3 * (m + n) * (m ^ 2 + n ^ 2) * (m ^ 2 - 2 * m * n - n ^ 2)),
   (-4 * m ^ 2 * n * (m - n) ^ 2 * (m + n) * (m ^ 2 + n ^ 2),
     -(4 * m ^ 3 * n * (m - n) ^ 3 * (m + n) * (m ^ 2 + n ^ 2) * (m ^ 2 - 2 * m * n - n ^ 2))),
   (0, U m n ^ 2 * V m n ^ 2 * W m n ^ 2), (0, -(U m n ^ 2 * V m n ^ 2 * W m n ^ 2)),
   (-2 * U m n ^ 2 * V m n ^ 2, U m n ^ 2 * V m n ^ 2 * (U m n ^ 2 - V m n ^ 2)),
   (-2 * U m n ^ 2 * V m n ^ 2, -(U m n ^ 2 * V m n ^ 2 * (U m n ^ 2 - V m n ^ 2))),
   (-(V m n ^ 2 * W m n ^ 2), 0), (-(U m n ^ 2 * W m n ^ 2), 0), (-(U m n ^ 2 * V m n ^ 2), 0)]

theorem onEpp_of_mem_torsionPts {P : ℚ × ℚ} (hP : P ∈ torsionPts m n) : OnEpp m n P.1 P.2 := by
  simp only [torsionPts, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp only [OnEpp, x8, y8, U, V, W] <;> ring

/-- **The uniform torsion lemma.** For `0 < n < m`, no torsion point of `E″` with `X > 0` has
`X + U²V²` a square, so none is twice a rational point. The only torsion points with `X > 0` are
`±P₈`, and `X(P₈) + U²V² = (2m(m + n))² · mn(m² − n²)` with `mn(m² − n²)` not a square by
Fermat's right triangle theorem (`FermatTriangle.not_isSquare_mul_mul_sq_sub_sq`). -/
theorem not_isSquare_of_mem_torsionPts {m n : ℕ} (hn : 0 < n) (hnm : n < m) {P : ℚ × ℚ}
    (hP : P ∈ torsionPts m n) (hX : 0 < P.1) :
    ¬ IsSquare (P.1 + U m n ^ 2 * V m n ^ 2) := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hmn : (0 : ℚ) < m - n := by
    have : (n : ℚ) < m := by exact_mod_cast hnm
    linarith
  have hm' : (0 : ℚ) < m := by linarith
  have hA : (0 : ℚ) < 4 * m * n * (m - n) * (m + n) * (m ^ 2 + n ^ 2) := by
    have := add_pos hm' hn'
    have : (0 : ℚ) < m ^ 2 + n ^ 2 := by positivity
    positivity
  simp only [torsionPts, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  -- `±P₈`
  · rintro ⟨s, hs⟩
    apply FermatTriangle.not_isSquare_mul_mul_sq_sub_sq hn hnm
    rw [← Rat.isSquare_natCast_iff]
    have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm.le 2
    refine ⟨s / (2 * m * (m + n)), ?_⟩
    push_cast [hle]
    field_simp
    simp only [x8, U, V] at hs
    linear_combination hs
  · rintro ⟨s, hs⟩
    apply FermatTriangle.not_isSquare_mul_mul_sq_sub_sq hn hnm
    rw [← Rat.isSquare_natCast_iff]
    have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm.le 2
    refine ⟨s / (2 * m * (m + n)), ?_⟩
    push_cast [hle]
    field_simp
    simp only [x8, U, V] at hs
    linear_combination hs
  -- the other abscissas are `≤ 0`
  all_goals
    exfalso
    simp only at hX
    nlinarith [mul_pos hA (mul_pos hn' hmn), mul_pos hA (mul_pos hn' (add_pos hm' hn')),
      mul_pos hA (mul_pos hm' hmn), sq_nonneg (U m n * V m n), sq_nonneg (V m n * W m n),
      sq_nonneg (U m n * W m n)]

/-- **Rank `0` of `E″`**, stated as: every affine rational point of `E″` is one of the fifteen
points of `torsionPts`. PARI/GP proves this for `112` of the `331` fibers with `m ≤ 40`. -/
def TorsionOnly (m n : ℚ) : Prop := ∀ X Y, OnEpp m n X Y → (X, Y) ∈ torsionPts m n

/-- **No perfect cuboid on a fiber where `E″` has rank `0`**, uniformly in `(m, n)`. A perfect
cuboid would give a point of `E″` with `X > 0` and `X + U²V²` a square
(`IsPerfectCuboid.exists_onEpp`), which by `TorsionOnly` is a torsion point, contradicting the
uniform torsion lemma `not_isSquare_of_mem_torsionPts`. -/
theorem IsPerfectCuboid.not_onFiber_of_torsionOnly {m n : ℕ} (hn : 0 < n) (hnm : n < m)
    (hT : TorsionOnly m n) {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) :
    (Z : ℚ) * U m n ≠ X * V m n := by
  intro hf
  have hU : U (m : ℚ) n ≠ 0 := by
    have : (n : ℚ) < m := by exact_mod_cast hnm
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    simp only [U]
    nlinarith
  obtain ⟨x, y, hE, hx, -, -, -, h3⟩ := IsPerfectCuboid.exists_onEpp h hf hU
  exact not_isSquare_of_mem_torsionPts hn hnm (hT x y hE) hx h3

end Kubert

end PerfectCuboid
