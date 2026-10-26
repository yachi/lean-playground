module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.Nat.Squarefree
public import LeanPlayground.PerfectCuboid.Basic

/-!
# Perfect cuboids and congruent-number curves of rank at least two

Paulsen and West (*On perfect cuboids and CN-elliptic curves*, Houston J. Math. 48 (2022)) turn a
perfect cuboid into three rational points on the congruent-number curve `E_N : Y² = X³ − N²X`,
`N = sf(abcg/2)`, and claim that `E_N` must then have rank at least two. Asiryan
([*On the Rank Condition for Perfect Cuboids*](https://arxiv.org/abs/2610.10643), arXiv 2026-10)
points out a gap in their proof and repairs it. This file formalizes the parts of Asiryan's argument
that need no machinery beyond Mathlib's group law on Weierstrass curves.

The paper works on `D_N : Nη² = t − t³`; we use the isomorphic curve `E_N` with `X = −Nt`, so the
conditions `0 < t < 1` become `−N < X < 0`, and the `2`-torsion points `S, T, U` of `D_N` (with
`t = 0, −1, 1`) become `(0, 0)`, `(N, 0)`, `(−N, 0)`.

## Main results

* `IsPerfectCuboid.exists_config` (Proposition 1): a perfect cuboid gives a *positive cuboid
  configuration* `IsConfig` on `E_N` for a squarefree `N`: three points with `−N < Xᵢ < 0` and
  `X₁X₂ + X₁X₃ + X₂X₃ = N²`. The paper uses a half-angle argument; here the compatibility
  condition is a polynomial identity (`cuboid_compat`).
* `add_add_ne_S` (Lemma 1): three points of a positive configuration never add up to `S`, for any
  choice of signs. Asiryan uses Riemann–Roch; here it is Vieta's formulas for the line through
  `P₁`, `P₂` and `−(P₁ + P₂)`, which turn `P₁ + P₂ + P₃ = S` into
  `(X₁² − N²)(X₂² − N²)(X₃² − N²) = 0`.
* `A_add_T_ne_B_of_even` (Proposition 2): the step of Paulsen–West that swaps the two sequences
  `A_k(G)`, `B_k(G)` by replacing `G` with `G + T` is false at every even index, for every `G`.
  This is the gap in their proof.
* `eq24`, `not_pattern` (§6.1, §6.4): in the rank-one pattern `(aG, bG + T, cG + S + T)`, the
  compatibility condition is equation (24), and `b = a + c` or `c = a + b` is impossible.
* `not_rankOne` (Theorem 1, rank-one case): no positive configuration lies in a subgroup of rank
  one, **conditional** on two inputs that Mathlib cannot state or prove yet (see the last
  section): the division-polynomial reduction (Lemmas 2, 3) and Ingram's primitive-divisor
  theorem.
-/

@[expose] public section

namespace PerfectCuboid.CongruentRank

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

/-- The congruent-number curve `E_N : Y² = X³ − N²X` over `ℚ`. -/
def curve (N : ℚ) : WeierstrassCurve.Affine ℚ := ⟨0, 0, 0, -N ^ 2, 0⟩

variable {N : ℚ}

theorem curve_Δ (N : ℚ) : (curve N).Δ = 64 * N ^ 6 := by
  simp only [curve, Δ, b₂, b₄, b₆, b₈]
  ring

theorem equation_iff {x y : ℚ} : (curve N).Equation x y ↔ y ^ 2 = x ^ 3 - N ^ 2 * x := by
  rw [Affine.equation_iff]
  simp only [curve]
  constructor <;> intro h <;> linear_combination h

theorem nonsingular_iff (hN : N ≠ 0) {x y : ℚ} :
    (curve N).Nonsingular x y ↔ y ^ 2 = x ^ 3 - N ^ 2 * x := by
  rw [← equation_iff_nonsingular_of_Δ_ne_zero (by rw [curve_Δ]; positivity), equation_iff]

/-- `P` is an affine point with `X`-coordinate `x`. -/
def HasX (P : (curve N).Point) (x : ℚ) : Prop := ∃ y h, P = .some x y h

theorem HasX.neg {P : (curve N).Point} {x : ℚ} (h : HasX P x) : HasX (-P) x := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨_, _, Point.neg_some hy⟩

/-- The `2`-torsion point `S = (0, 0)`. -/
def S (hN : N ≠ 0) : (curve N).Point := .some 0 0 ((nonsingular_iff hN).mpr (by ring))

/-- If `x₁`, `x₂`, `x'` are the `X`-coordinates of `P₁`, `P₂` and `P₁ + P₂`, they are the roots of
`X³ − N²X − (ℓX + c)²` for the line `Y = ℓX + c` through the three points; eliminating `ℓ` and `c`
from Vieta's formulas gives `(e₂ + N²)² = 4 e₁ e₃`. -/
theorem vieta_add {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve N).Nonsingular x₁ y₁)
    (h₂ : (curve N).Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = (curve N).negY x₂ y₂)) {x' : ℚ}
    (hx' : (curve N).addX x₁ x₂ ((curve N).slope x₁ x₂ y₁ y₂) = x') :
    (x₁ * x₂ + x₁ * x' + x₂ * x' + N ^ 2) ^ 2 = 4 * (x₁ + x₂ + x') * (x₁ * x₂ * x') := by
  have h := (curve N).addPolynomial_slope h₁.1 h₂.1 hxy
  rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective, hx'] at h
  generalize (curve N).slope x₁ x₂ y₁ y₂ = ℓ at h
  simp only [Cubic.mk.injEq, curve] at h
  obtain ⟨-, hb, hc, hd⟩ := h
  -- `e₁ = ℓ²`, `e₂ = −2ℓc − N²`, `e₃ = c²` with `c = y₁ − ℓx₁`
  have hb' : x₁ + x₂ + x' = ℓ ^ 2 := by linear_combination hb
  have hc' : x₁ * x₂ + x₁ * x' + x₂ * x' + N ^ 2 = -2 * ℓ * (y₁ - ℓ * x₁) := by
    linear_combination -hc
  have hd' : x₁ * x₂ * x' = (y₁ - ℓ * x₁) ^ 2 := by linear_combination hd
  rw [hc', hb', hd']
  ring

theorem hasX_some {x y x' : ℚ} {h : (curve N).Nonsingular x y} (hx : x = x') :
    HasX (.some x y h) x' := by
  subst hx
  exact ⟨y, h, rfl⟩

theorem HasX.ne_zero {P : (curve N).Point} {x : ℚ} (h : HasX P x) : P ≠ 0 := by
  obtain ⟨y, hy, rfl⟩ := h
  exact Point.some_ne_zero hy

/-- Translation by `S = (0, 0)` sends `X` to `−N²/X`. -/
theorem HasX.S_add (hN : N ≠ 0) {P : (curve N).Point} {x : ℚ} (h : HasX P x) (hx : x ≠ 0) :
    HasX (S hN + P) (-N ^ 2 / x) := by
  obtain ⟨y, hy, rfl⟩ := h
  have hy2 := (nonsingular_iff hN).mp hy
  rw [S, Point.add_of_X_ne hx.symm]
  apply hasX_some
  simp only [addX, slope_of_X_ne hx.symm, curve]
  field_simp
  linear_combination x * hy2

/-- A *positive cuboid configuration* on `E_N`, in `X`-coordinates `Xᵢ = −N tᵢ`: the conditions
`0 < tᵢ < 1` and `t₁t₂ + t₁t₃ + t₂t₃ = 1` of Asiryan, Definition 1. -/
structure IsConfig (N x₁ x₂ x₃ : ℚ) : Prop where
  pos : 0 < N
  lt₁ : -N < x₁
  lt₂ : -N < x₂
  lt₃ : -N < x₃
  neg₁ : x₁ < 0
  neg₂ : x₂ < 0
  neg₃ : x₃ < 0
  compat : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = N ^ 2

/-- **Asiryan, Lemma 1.** Three points of a positive cuboid configuration never add up to the
`2`-torsion point `S`. Since `−P` has the same `X`-coordinate as `P`, this covers every choice of
signs `σ₁Q₁ + σ₂Q₂ + σ₃Q₃ ≠ S`. -/
theorem add_add_ne_S {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃) {P₁ P₂ P₃ : (curve N).Point}
    (h₁ : HasX P₁ x₁) (h₂ : HasX P₂ x₂) (h₃ : HasX P₃ x₃) :
    P₁ + P₂ + P₃ ≠ S hc.pos.ne' := by
  intro h
  have hN := hc.pos.ne'
  have h₃' := h₃.neg.S_add hN hc.neg₃.ne
  rw [← eq_sub_iff_add_eq, sub_eq_add_neg] at h
  obtain ⟨y₁, hy₁, rfl⟩ := h₁
  obtain ⟨y₂, hy₂, rfl⟩ := h₂
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curve N).negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2] at h
    exact h₃'.ne_zero h.symm
  rw [Point.add_some hxy] at h
  obtain ⟨y', hy', h'⟩ := h₃'
  rw [← h, Point.some.injEq] at h'
  have hv := vieta_add hy₁ hy₂ hxy h'.1
  set x' := -N ^ 2 / x₃
  have hH : x' * x₃ = -N ^ 2 := div_mul_cancel₀ _ hc.neg₃.ne
  have key : (x₁ ^ 2 - N ^ 2) * (x₂ ^ 2 - N ^ 2) * (x₃ ^ 2 - N ^ 2) = 0 := by
    linear_combination x₃ ^ 2 * hv
      - (-N^2*x₁^2 + 2*N^2*x₁*x₂ + 2*N^2*x₁*x₃ - N^2*x₂^2 + 2*N^2*x₂*x₃ - 2*x₁^2*x₂*x₃
        + x₁^2*x₃*x' - 2*x₁*x₂^2*x₃ - 2*x₁*x₂*x₃*x' + x₂^2*x₃*x') * hH
      - N ^ 2 * (-N ^ 2 + x₁ * x₂ + x₁ * x₃ + x₂ * x₃) * hc.compat
  have f₁ : x₁ ^ 2 - N ^ 2 < 0 := by nlinarith [hc.lt₁, hc.neg₁]
  have f₂ : x₂ ^ 2 - N ^ 2 < 0 := by nlinarith [hc.lt₂, hc.neg₂]
  have f₃ : x₃ ^ 2 - N ^ 2 < 0 := by nlinarith [hc.lt₃, hc.neg₃]
  have : (x₁ ^ 2 - N ^ 2) * (x₂ ^ 2 - N ^ 2) * (x₃ ^ 2 - N ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg f₁ f₂) f₃
  exact this.ne key

/-! ### From a perfect cuboid to a positive cuboid configuration -/

section Cuboid

variable {a b c d e f g s : ℚ}

/-- The identity behind Asiryan, Proposition 1: with `h = de + bc`, `h² − a²g² = 2bch`. -/
theorem sq_sub_sq_eq (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    (d * e + b * c) ^ 2 - (a * g) ^ 2 = 2 * (b * c) * (d * e + b * c) := by
  linear_combination e ^ 2 * hd + (a ^ 2 + b ^ 2) * he - a ^ 2 * hg

/-- The point `(−N·ag/(de + bc), N²·2s/(de + bc))` lies on `E_N` when `abcg = 2Ns²`. -/
theorem cuboid_point_eq (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) (hs : a * b * c * g = 2 * N * s ^ 2)
    (hh : d * e + b * c ≠ 0) :
    (N ^ 2 * (2 * s) / (d * e + b * c)) ^ 2 =
      (-N * (a * g) / (d * e + b * c)) ^ 3 - N ^ 2 * (-N * (a * g) / (d * e + b * c)) := by
  have key := sq_sub_sq_eq hd he hg
  field_simp
  linear_combination (-(N ^ 3 * a * g) * key) - 2 * N ^ 3 * (d * e + b * c) * hs

/-- The `X`-coordinate lies in `(−N, 0)`. -/
theorem cuboid_point_bounds (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd0 : 0 < d) (he0 : 0 < e)
    (hg0 : 0 < g) (hN : 0 < N) (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    -N < -N * (a * g) / (d * e + b * c) ∧ -N * (a * g) / (d * e + b * c) < 0 := by
  have hh : 0 < d * e + b * c := by positivity
  have key := sq_sub_sq_eq hd he hg
  have hlt : a * g < d * e + b * c := by nlinarith [mul_pos ha hg0, mul_pos hb hc]
  constructor
  · rw [lt_div_iff₀ hh]
    nlinarith
  · apply div_neg_of_neg_of_pos _ hh
    have := mul_pos ha hg0
    nlinarith

/-- The compatibility condition `t₁t₂ + t₁t₃ + t₂t₃ = 1` of Asiryan, Proposition 1, for
`t₁ = ag/(de + bc)`, `t₂ = bg/(df + ac)`, `t₃ = cg/(ef + ab)`. The paper proves it with the
half-angle formula; here it is a polynomial identity modulo the four Pythagorean relations. -/
theorem cuboid_compat (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hf : f ^ 2 = b ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    a * g * (b * g) * (e * f + a * b) + a * g * (c * g) * (d * f + a * c) +
      b * g * (c * g) * (d * e + b * c) = (d * e + b * c) * (d * f + a * c) * (e * f + a * b) := by
  linear_combination (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + a * b * e * f + a * c * d * f + b ^ 2 * c ^ 2
      + b * c * d * e) * hg - e * f * (a * b + e * f) * hd
    - f * (a ^ 2 * f + a * c * d + b ^ 2 * f) * he
    + (-a ^ 4 - a ^ 2 * b ^ 2 - a ^ 2 * c ^ 2 - b ^ 2 * c ^ 2 - b * c * d * e) * hf

/-- **Asiryan, Proposition 1** (in `X`-coordinates). A rational box with rational face diagonals
`d, e, f` and space diagonal `g` gives three points of `E_N` that form a positive cuboid
configuration, for every `N > 0` with `abcg = 2Ns²`. -/
theorem exists_config (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd0 : 0 < d) (he0 : 0 < e)
    (hf0 : 0 < f) (hg0 : 0 < g) (hN : 0 < N) (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2)
    (hs : a * b * c * g = 2 * N * s ^ 2) :
    ∃ x₁ x₂ x₃ : ℚ, ∃ P₁ P₂ P₃ : (curve N).Point,
      HasX P₁ x₁ ∧ HasX P₂ x₂ ∧ HasX P₃ x₃ ∧ IsConfig N x₁ x₂ x₃ := by
  have h₁ : 0 < d * e + b * c := by positivity
  have h₂ : 0 < d * f + a * c := by positivity
  have h₃ : 0 < e * f + a * b := by positivity
  have hd' : d ^ 2 = b ^ 2 + a ^ 2 := by linear_combination hd
  have hg₂ : g ^ 2 = b ^ 2 + a ^ 2 + c ^ 2 := by linear_combination hg
  have hg₃ : g ^ 2 = c ^ 2 + a ^ 2 + b ^ 2 := by linear_combination hg
  have he' : e ^ 2 = c ^ 2 + a ^ 2 := by linear_combination he
  have hf' : f ^ 2 = c ^ 2 + b ^ 2 := by linear_combination hf
  have hs₂ : b * a * c * g = 2 * N * s ^ 2 := by linear_combination hs
  have hs₃ : c * a * b * g = 2 * N * s ^ 2 := by linear_combination hs
  have e₁ := cuboid_point_eq hd he hg hs h₁.ne'
  have e₂ := cuboid_point_eq hd' hf hg₂ hs₂ h₂.ne'
  have e₃ := cuboid_point_eq he' hf' hg₃ hs₃ h₃.ne'
  have b₁ := cuboid_point_bounds ha hb hc hd0 he0 hg0 hN hd he hg
  have b₂ := cuboid_point_bounds hb ha hc hd0 hf0 hg0 hN hd' hf hg₂
  have b₃ := cuboid_point_bounds hc ha hb he0 hf0 hg0 hN he' hf' hg₃
  refine ⟨_, _, _, .some _ _ ((nonsingular_iff hN.ne').mpr e₁),
    .some _ _ ((nonsingular_iff hN.ne').mpr e₂), .some _ _ ((nonsingular_iff hN.ne').mpr e₃),
    hasX_some rfl, hasX_some rfl, hasX_some rfl,
    ⟨hN, b₁.1, b₂.1, b₃.1, b₁.2, b₂.2, b₃.2, ?_⟩⟩
  have key := cuboid_compat hd he hf hg
  field_simp
  linear_combination key

/-- **Asiryan, Proposition 1, for a perfect cuboid.** A perfect cuboid with edges `a, b, c` and
space diagonal `g` gives a positive cuboid configuration on `E_N` for the squarefree number
`N = sf(abcg/2)`, that is, `abcg/2 = N s²`. -/
theorem _root_.PerfectCuboid.IsPerfectCuboid.exists_config {a b c : ℕ} (h : IsPerfectCuboid a b c) :
    ∃ N : ℕ, Squarefree N ∧ ∃ (g : ℕ) (s : ℚ), g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 ∧
      (a * b * c * g : ℚ) / 2 = N * s ^ 2 ∧
      ∃ x₁ x₂ x₃ : ℚ, ∃ P₁ P₂ P₃ : (curve N).Point,
        HasX P₁ x₁ ∧ HasX P₂ x₂ ∧ HasX P₃ x₃ ∧ IsConfig N x₁ x₂ x₃ := by
  have ha := h.pos_a
  have hb := h.pos_b
  have hc := h.pos_c
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨e, he⟩ := h.sq_ca
  obtain ⟨g, hg⟩ := h.sq_abc
  have pos {r m : ℕ} (hm : 0 < m) (hr : m = r * r) : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr' <;> [simp at hr; exact hr']
    omega
  have hd0 := pos (by positivity) hd
  have he0 := pos (by positivity) he
  have hf0 := pos (by positivity) hf
  have hg0 := pos (by positivity) hg
  obtain ⟨N, k, hN, hk, hkN, hsq⟩ := Nat.sq_mul_squarefree_of_pos
    (show 0 < 2 * (a * b * c * g) by positivity)
  have hs : (a * b * c * g : ℚ) = 2 * N * ((k : ℚ) / 2) ^ 2 := by
    have : ((k ^ 2 * N : ℕ) : ℚ) = ((2 * (a * b * c * g) : ℕ) : ℚ) := by rw [hkN]
    push_cast at this
    linear_combination -this / 2
  refine ⟨N, hsq, g, k / 2, by rw [sq]; exact hg.symm, by linear_combination hs / 2, ?_⟩
  exact CongruentRank.exists_config (a := a) (b := b) (c := c) (d := d) (e := e) (f := f) (g := g)
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc) (by exact_mod_cast hd0)
    (by exact_mod_cast he0) (by exact_mod_cast hf0) (by exact_mod_cast hg0) (by exact_mod_cast hN)
    (by rw [sq]; exact_mod_cast hd.symm)
    (by rw [sq]; linear_combination (by exact_mod_cast he.symm : (e : ℚ) * e = c ^ 2 + a ^ 2))
    (by rw [sq]; exact_mod_cast hf.symm) (by rw [sq]; exact_mod_cast hg.symm) hs

end Cuboid

/-! ### The `2`-torsion points and translation by them -/

/-- The `2`-torsion point `T = (N, 0)` (the point `t = −1` of `D_N`). -/
def T (hN : N ≠ 0) : (curve N).Point := .some N 0 ((nonsingular_iff hN).mpr (by ring))

/-- The `2`-torsion point `U = (−N, 0)` (the point `t = 1` of `D_N`). -/
def U (hN : N ≠ 0) : (curve N).Point := .some (-N) 0 ((nonsingular_iff hN).mpr (by ring))

theorem S_add_S (hN : N ≠ 0) : S hN + S hN = 0 :=
  Point.add_self_of_Y_eq (by simp [curve, negY])

theorem T_add_T (hN : N ≠ 0) : T hN + T hN = 0 :=
  Point.add_self_of_Y_eq (by simp [curve, negY])

theorem neg_S (hN : N ≠ 0) : -S hN = S hN := neg_eq_of_add_eq_zero_left (S_add_S hN)

theorem neg_T (hN : N ≠ 0) : -T hN = T hN := neg_eq_of_add_eq_zero_left (T_add_T hN)

theorem T_ne_zero (hN : N ≠ 0) : T hN ≠ 0 := Point.some_ne_zero _

theorem S_add_T (hN : N ≠ 0) : S hN + T hN = U hN := by
  rw [S, T, U, Point.add_of_X_ne hN.symm]
  simp [curve, addX, addY, negY, negAddY, slope_of_X_ne hN.symm]

/-- Translation by `T` sends `X` to `N(X + N)/(X − N)`. -/
theorem HasX.add_T (hN : N ≠ 0) {P : (curve N).Point} {x : ℚ} (h : HasX P x) (hx : x ≠ N) :
    HasX (P + T hN) (N * (x + N) / (x - N)) := by
  obtain ⟨y, hy, rfl⟩ := h
  have hy2 := (nonsingular_iff hN).mp hy
  have hx' : x - N ≠ 0 := sub_ne_zero.mpr hx
  rw [T, Point.add_of_X_ne hx]
  apply hasX_some
  simp only [addX, slope_of_X_ne hx, curve]
  field_simp
  linear_combination hy2

/-- Translation by `U = S + T` sends `X` to `−N(X − N)/(X + N)`. -/
theorem HasX.add_U (hN : N ≠ 0) {P : (curve N).Point} {x : ℚ} (h : HasX P x) (hx : x ≠ -N) :
    HasX (P + U hN) (-N * (x - N) / (x + N)) := by
  obtain ⟨y, hy, rfl⟩ := h
  have hy2 := (nonsingular_iff hN).mp hy
  have hx' : x + N ≠ 0 := by rw [← sub_neg_eq_add]; exact sub_ne_zero.mpr hx
  rw [U, Point.add_of_X_ne hx]
  apply hasX_some
  simp only [addX, slope_of_X_ne hx, curve]
  field_simp
  linear_combination (x + N) * hy2

/-! ### The gap in Paulsen–West (Asiryan, §3)

Paulsen and West split the multiples of a base point `G` into two sequences,
`A_k(G) = kG + ε(k)S` and `B_k(G) = A_k(G) + T`, where `ε(k) = 0` for odd `k` and `1` for even
`k`, and claim that replacing `G` by `G + T` makes the two sequences trade places. That holds for
odd `k` only (`A_add_T_of_odd`). For even `k` both sequences stay where they are (`A_add_T_of_even`), so
the claimed interchange fails for **every** base point `G` (`A_add_T_ne_B_of_even`); this is the
gap that Asiryan's paper closes. It fails on abscissas too: `A_k(G)` and `B_k(G)` never have the
same `X`-coordinate (`HasX.ne_of_add_T`), because that would need `√2 ∈ ℚ`. -/

/-- The sequence `A_k(G) = kG + ε(k)S`. -/
def A (hN : N ≠ 0) (k : ℕ) (G : (curve N).Point) : (curve N).Point :=
  k • G + if Even k then S hN else 0

/-- The sequence `B_k(G) = A_k(G) + T`. -/
def B (hN : N ≠ 0) (k : ℕ) (G : (curve N).Point) : (curve N).Point := A hN k G + T hN

theorem nsmul_T_of_even (hN : N ≠ 0) {k : ℕ} (hk : Even k) : k • T hN = 0 := by
  obtain ⟨m, rfl⟩ := hk
  rw [add_nsmul, ← nsmul_add, T_add_T, nsmul_zero]

theorem nsmul_T_of_odd (hN : N ≠ 0) {k : ℕ} (hk : Odd k) : k • T hN = T hN := by
  obtain ⟨m, rfl⟩ := hk
  rw [add_nsmul, nsmul_T_of_even hN (even_two_mul m), zero_add, one_nsmul]

/-- **Asiryan, Proposition 2** (odd `k`): `A_k(G + T) = B_k(G)`. -/
theorem A_add_T_of_odd (hN : N ≠ 0) {k : ℕ} (hk : Odd k) (G : (curve N).Point) :
    A hN k (G + T hN) = B hN k G := by
  unfold B A
  rw [nsmul_add, nsmul_T_of_odd hN hk, ite_eq_right (Nat.not_even_iff_odd.mpr hk)]
  abel

/-- **Asiryan, Proposition 2** (odd `k`): `B_k(G + T) = A_k(G)`. -/
theorem B_add_T_of_odd (hN : N ≠ 0) {k : ℕ} (hk : Odd k) (G : (curve N).Point) :
    B hN k (G + T hN) = A hN k G := by
  rw [B, A_add_T_of_odd hN hk, B, add_assoc, T_add_T, add_zero]

/-- **Asiryan, Proposition 2** (even `k`): `A_k(G + T) = A_k(G)`. -/
theorem A_add_T_of_even (hN : N ≠ 0) {k : ℕ} (hk : Even k) (G : (curve N).Point) :
    A hN k (G + T hN) = A hN k G := by
  unfold A
  rw [nsmul_add, nsmul_T_of_even hN hk, add_zero]

/-- **Asiryan, Proposition 2** (even `k`): `B_k(G + T) = B_k(G)`. -/
theorem B_add_T_of_even (hN : N ≠ 0) {k : ℕ} (hk : Even k) (G : (curve N).Point) :
    B hN k (G + T hN) = B hN k G := by
  rw [B, A_add_T_of_even hN hk, B]

/-- The interchange claimed in the proof of Paulsen–West, Theorem 4.2, is false at every even
index, for every base point. -/
theorem A_add_T_ne_B_of_even (hN : N ≠ 0) {k : ℕ} (hk : Even k) (G : (curve N).Point) :
    A hN k (G + T hN) ≠ B hN k G := by
  rw [A_add_T_of_even hN hk, B]
  intro h
  exact T_ne_zero hN (left_eq_add.mp h)

theorem sq_ne_two (q : ℚ) : q ^ 2 ≠ 2 := by
  intro h
  apply irrational_sqrt_two.ne_rat |q|
  have h' : ((q : ℝ)) ^ 2 = 2 := by exact_mod_cast h
  rw [Rat.cast_abs, ← h', Real.sqrt_sq_eq_abs]

/-- `P` and `P + T` never share an `X`-coordinate: in Asiryan's words, `A_k(G) ≠ B_k(G)`, since
equality would give a rational root of `t² + 2t − 1`. -/
theorem HasX.ne_of_add_T (hN : N ≠ 0) {P : (curve N).Point} {x x' : ℚ} (h : HasX P x)
    (h' : HasX (P + T hN) x') : x ≠ x' := by
  rintro rfl
  by_cases hx : x = N
  · obtain ⟨y, hy, rfl⟩ := h
    have hy0 : y = 0 := by
      have := (nonsingular_iff hN).mp hy
      rw [hx] at this
      exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by linear_combination this)
    subst hx hy0
    exact h'.ne_zero (T_add_T hN)
  obtain ⟨y', hy', e'⟩ := h.add_T hN hx
  obtain ⟨y'', hy'', e''⟩ := h'
  rw [e'', Point.some.injEq] at e'
  have hx' : x - N ≠ 0 := sub_ne_zero.mpr hx
  have key : x * (x - N) = N * (x + N) := by
    have := e'.1
    field_simp at this
    linear_combination this
  apply sq_ne_two ((x - N) / N)
  field_simp
  linear_combination key

/-! ### The rank-one pattern (Asiryan, §6)

Asiryan reduces a positive configuration inside a subgroup of rank one to the pattern
`Q₁ = aG`, `Q₂ = bG + T`, `Q₃ = cG + S + T` with `a, b` odd and `c` even (Lemma 3; that step uses
the division polynomials and is not formalized here). The theorems below are the parts of §6 that
need no further input: the compatibility condition becomes equation (24), which rules out `a = b`,
and the relations `b = a + c` or `c = a + b` (which Ingram's primitive-divisor theorem forces) clash
with Lemma 1. -/

/-- **Asiryan, equation (24).** For the pattern `(aG, bG + T, cG + U)`, the compatibility
condition reads `X_a X_b + X_a X_c − X_b X_c + N² = 0`. -/
theorem eq24 {G : (curve N).Point} {b c : ℕ} {x₁ x₂ x₃ Xb Xc : ℚ} (hc : IsConfig N x₁ x₂ x₃)
    (hXb : HasX (b • G) Xb) (hXc : HasX (c • G) Xc)
    (h₂ : HasX (b • G + T hc.pos.ne') x₂) (h₃ : HasX (c • G + U hc.pos.ne') x₃) :
    x₁ * Xb + x₁ * Xc - Xb * Xc + N ^ 2 = 0 := by
  have hN := hc.pos.ne'
  -- `Xb ≠ N` and `Xc ≠ −N`, since otherwise the translate is `0`
  have hb : Xb ≠ N := by
    rintro rfl
    obtain ⟨y, hy, e⟩ := hXb
    have hy0 : y = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp
      (by linear_combination (nonsingular_iff hN).mp hy)
    subst hy0
    exact h₂.ne_zero (by rw [e]; exact T_add_T hN)
  have hc' : Xc ≠ -N := by
    rintro rfl
    obtain ⟨y, hy, e⟩ := hXc
    have hy0 : y = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp
      (by linear_combination (nonsingular_iff hN).mp hy)
    subst hy0
    exact h₃.ne_zero (by rw [e]; exact Point.add_self_of_Y_eq (by simp [curve, negY]))
  obtain ⟨y₂, hy₂, e₂⟩ := hXb.add_T hN hb
  obtain ⟨y₂', hy₂', e₂'⟩ := h₂
  rw [e₂', Point.some.injEq] at e₂
  obtain ⟨y₃, hy₃, e₃⟩ := hXc.add_U hN hc'
  obtain ⟨y₃', hy₃', e₃'⟩ := h₃
  rw [e₃', Point.some.injEq] at e₃
  have hb' : Xb - N ≠ 0 := sub_ne_zero.mpr hb
  have hc'' : Xc + N ≠ 0 := by rw [← sub_neg_eq_add]; exact sub_ne_zero.mpr hc'
  have key := hc.compat
  rw [e₂.1, e₃.1] at key
  field_simp at key
  have h2N : 2 * N ≠ 0 := by have := hc.pos; positivity
  apply (mul_right_inj' h2N).mp
  linear_combination key

/-- In the pattern, `a ≠ b`: equation (24) with `X_a = X_b` would give `X_a² + N² = 0`. -/
theorem eq24_ne {Xa Xb Xc : ℚ} (hN : 0 < N) (h : Xa * Xb + Xa * Xc - Xb * Xc + N ^ 2 = 0) :
    Xa ≠ Xb := by
  rintro rfl
  nlinarith [sq_nonneg Xa]

/-- **Asiryan, §6.4.** A positive configuration of the form `(aG, bG + T, cG + S + T)` cannot
have `b = a + c` or `c = a + b`: either relation gives `Q₁ ∓ Q₂ ± Q₃ = S`, contradicting
Lemma 1. -/
theorem not_pattern {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃) (G : (curve N).Point)
    {a b c : ℕ} (h₁ : HasX (a • G) x₁) (h₂ : HasX (b • G + T hc.pos.ne') x₂)
    (h₃ : HasX (c • G + U hc.pos.ne') x₃) (h : b = a + c ∨ c = a + b) : False := by
  have hN := hc.pos.ne'
  rcases h with rfl | rfl
  · apply add_add_ne_S hc h₁ h₂.neg h₃
    rw [← S_add_T hN, add_nsmul, neg_add, ← neg_T hN]
    abel
  · apply add_add_ne_S hc h₁ h₂ h₃.neg
    rw [← neg_S hN, ← S_add_T hN, add_nsmul]
    abel

/-! ### What is left: the two analytic inputs

Asiryan's Theorem 1 says the three points of a positive configuration generate a subgroup of rank
at least two. Rank zero is ruled out because `E_N(ℚ)_tors = {0, S, T, U}` (Remark 1), and rank one
is ruled out in three steps:

1. **Reduction (Lemmas 2, 3).** A configuration inside `ℤG + E_N[2]` can be brought to the pattern
   `(aG, bG + T, cG + U)` with `a, b` odd and `c` even. The proof writes `x(kG)` with the division
   polynomials and uses their degrees and leading coefficients (`deg Φ_k = k²`, `lc Ψ²_k = k²`)
   with the rational root theorem. Mathlib has those degrees (`WeierstrassCurve.natDegree_Φ`,
   `WeierstrassCurve.leadingCoeff_ΨSq`) but not yet the formula `x(kP) = Φ_k(x)/Ψ²_k(x)`.
2. **Primitive divisors (§6.2, §6.3).** Ingram's theorem gives a prime of good reduction that
   divides the denominator of `x(mG)` for the largest index `m` and of no earlier one; reducing
   equation (24) modulo it forces `b = a + c` or `c = a + b`. Mathlib has neither Ingram's theorem
   (it needs canonical heights) nor the reduction map on points.
3. **Positivity (§6.4).** Proved here: `not_pattern`.

`not_rankOne` records this dependency: with steps 1 and 2 as hypotheses, no positive
configuration lies in a subgroup of rank one. -/

/-- The points `Q₁, Q₂, Q₃` lie in `ℤG + E_N[2]` for a single point `G`. -/
def InRankOne (Q₁ Q₂ Q₃ : (curve N).Point) : Prop :=
  ∃ (G : (curve N).Point) (k₁ k₂ k₃ : ℤ) (R₁ R₂ R₃ : (curve N).Point),
    R₁ + R₁ = 0 ∧ R₂ + R₂ = 0 ∧ R₃ + R₃ = 0 ∧
    Q₁ = k₁ • G + R₁ ∧ Q₂ = k₂ • G + R₂ ∧ Q₃ = k₃ • G + R₃

/-- Step 1 (Asiryan, Lemmas 2 and 3), as a hypothesis: a positive configuration in a subgroup of
rank one can be brought to the pattern `(aG, bG + T, cG + U)`. -/
def RankOneReduction (N : ℚ) (hN : 0 < N) : Prop :=
  ∀ ⦃x₁ x₂ x₃ : ℚ⦄ ⦃Q₁ Q₂ Q₃ : (curve N).Point⦄, IsConfig N x₁ x₂ x₃ →
    HasX Q₁ x₁ → HasX Q₂ x₂ → HasX Q₃ x₃ → InRankOne Q₁ Q₂ Q₃ →
    ∃ (G : (curve N).Point) (a b c : ℕ) (y₁ y₂ y₃ : ℚ), IsConfig N y₁ y₂ y₃ ∧
      HasX (a • G) y₁ ∧ HasX (b • G + T hN.ne') y₂ ∧ HasX (c • G + U hN.ne') y₃ ∧
      Odd a ∧ Odd b ∧ Even c ∧ 0 < c

/-- Step 2 (Asiryan, §6.2–6.3, from Ingram's primitive-divisor theorem), as a hypothesis. -/
def PrimitiveDivisorStep (N : ℚ) (hN : 0 < N) : Prop :=
  ∀ ⦃G : (curve N).Point⦄ ⦃a b c : ℕ⦄ ⦃y₁ y₂ y₃ : ℚ⦄, IsConfig N y₁ y₂ y₃ →
    HasX (a • G) y₁ → HasX (b • G + T hN.ne') y₂ → HasX (c • G + U hN.ne') y₃ →
    Odd a → Odd b → Even c → 0 < c → b = a + c ∨ c = a + b

/-- **Asiryan, Theorem 1 (rank-one case), conditional on steps 1 and 2.** No positive cuboid
configuration lies in a subgroup of rank one. -/
theorem not_rankOne {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃)
    (hred : RankOneReduction N hc.pos) (hprim : PrimitiveDivisorStep N hc.pos)
    {Q₁ Q₂ Q₃ : (curve N).Point} (h₁ : HasX Q₁ x₁) (h₂ : HasX Q₂ x₂) (h₃ : HasX Q₃ x₃) :
    ¬InRankOne Q₁ Q₂ Q₃ := by
  intro hQ
  obtain ⟨G, a, b, c, y₁, y₂, y₃, hc', g₁, g₂, g₃, ha, hb, hcev, hc0⟩ := hred hc h₁ h₂ h₃ hQ
  exact not_pattern hc' G g₁ g₂ g₃ (hprim hc' g₁ g₂ g₃ ha hb hcev hc0)

end PerfectCuboid.CongruentRank
