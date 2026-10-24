module

public import LeanPlayground.PerfectCuboid.MasterTupleGcd

/-!
# Perfect cuboids on a master-tuple fiber

This file formalizes the reduction behind René Peschmann, *A torsion-intersection proof of
perfect-cuboid nonexistence on 1,072 explicit master-tuple fibers*,
<https://arxiv.org/abs/2604.28072> (2026), §§3–4.

## Fibers

Every primitive Euler brick has a master tuple `(a, b, m, n)` (`IsEulerBrick.exists_masterTuple`),
and its edges `X, Z` are in the ratio `X : Z = (m² − n²) : 2mn`. The *fiber* `(m, n)` is the set
of bricks with that ratio. So "no perfect cuboid on the fiber `(m, n)`" just says: **no perfect
cuboid has two edges in the ratio `(m² − n²) : 2mn`**. For `(m, n) = (2, 1)` the ratio is `3 : 4`.
`IsPerfectCuboid.exists_fiber` proves that every perfect cuboid lies on some fiber.

## The curves

Write `U = m² − n²`, `V = 2mn`, `W = m² + n²`. Peschmann's genus-3 curve is

  `H_{m,n} : y² = P(t²) Q(t²)`,
  `P(s) = V² s² + (4U² − 2V²) s + V²`,  `Q(s) = W² s² + 2(U² − V²) s + W²`,

with the two elliptic quotients (in quartic form)

  `E₃   : y² = (V² w² + 4U²)(W² w² + 4U²)`,         `w = t − 1/t`,
  `E_uV : y² = (V² u² + 4(U² − V²))(W² u² − 4V²)`,  `u = t + 1/t`.

A perfect cuboid `(X, Y, Z)` on the fiber gives the point `t = (X + d)/Y` of `H_{m,n}`, where
`d = √(X² + Y²)`; then `w = 2X/Y` and `u = 2d/Y`. In fact both factors of `E₃` are squares
separately: `V² w² + 4U² = (2U e / Y)²` and `W² w² + 4U² = (2U f / Y)²`, where `e = √(Y² + Z²)` and
`f = √(X² + Y² + Z²)` is the space diagonal.

## Main results

* `onH_zero`, `onH_of_sq_eq_one` — Lemma 4.1: the trivial points `t = 0, ±1` of `H_{m,n}`.
* `OnH.neg`, `OnH.inv` — the Klein four-group `t ↦ −t`, `t ↦ 1/t` acting on `H_{m,n}`.
* `onH_iff_onE3`, `OnH.toEuV` — the quotient maps `H_{m,n} → E₃` and `H_{m,n} → E_uV`.
* `ne_neg_inv` — Lemma 4.3: `t ↦ −1/t` (the involution with quotient `E₃`) has no rational fixed
  point.
* `IsPerfectCuboid.onH` — a perfect cuboid on the fiber is a rational point of `H_{m,n}` with
  `t > 1`, so it is not one of the trivial points.
* `eq_trivial_of_e3Trivial`, `eq_trivial_of_euvLiftTrivial` — Theorem 4.5 (a) and (b)/(c): if `E₃`
  has no rational point with `w ≠ 0`, or if no rational point of `E_uV` with `u ≠ ±2` has
  `u² − 4` a square, then every rational point of `H_{m,n}` has `t ∈ {0, 1, −1}`.
* `IsPerfectCuboid.not_onFiber_of_e3Trivial`, `IsPerfectCuboid.not_onFiber_of_euvLiftTrivial` —
  hence no perfect cuboid lies on the fiber.
* `not_isPerfectCuboid_of_forall` — if one of the two hypotheses holds on every fiber, there is
  no perfect cuboid at all.

## What is *not* formalized

The hypotheses `E3Trivial m n` and `EuVLiftTrivial m n` are where the arithmetic of elliptic
curves enters. `E3Trivial m n` holds exactly when `E₃(ℚ)` has rank `0` and torsion of order `4`
(the four points `(0, ±4U²)` and the two points at infinity, which are always there). Peschmann
checks this, and its `E_uV` analogue, for 1,072 explicit fibers with `max(m, n) ≤ 100` using
PARI's `ellrank`, and where that is inconclusive the modularity theorem, Kolyvagin's theorem and
an exact modular-symbol computation of `L(E, 1)/Ω`. None of that is available in Mathlib, so
here those hypotheses stay hypotheses: the theorems below are the full argument *given* them.
-/

@[expose] public section

namespace PerfectCuboid

namespace Fiber

variable (m n : ℚ)

/-- `U = m² − n²` -/
def U : ℚ := m ^ 2 - n ^ 2
/-- `V = 2mn` -/
def V : ℚ := 2 * m * n
/-- `W = m² + n²` -/
def W : ℚ := m ^ 2 + n ^ 2

theorem W_sq : W m n ^ 2 = U m n ^ 2 + V m n ^ 2 := by
  simp only [U, V, W]
  ring

/-- `P(s) = V² s² + (4U² − 2V²) s + V²` -/
def P (s : ℚ) : ℚ := V m n ^ 2 * s ^ 2 + (4 * U m n ^ 2 - 2 * V m n ^ 2) * s + V m n ^ 2

/-- `Q(s) = W² s² + 2(U² − V²) s + W²` -/
def Q (s : ℚ) : ℚ := W m n ^ 2 * s ^ 2 + 2 * (U m n ^ 2 - V m n ^ 2) * s + W m n ^ 2

/-- `(t, y)` is an affine rational point of Peschmann's genus-3 curve
`H_{m,n} : y² = P(t²) Q(t²)`. -/
def OnH (t y : ℚ) : Prop := y ^ 2 = P m n (t ^ 2) * Q m n (t ^ 2)

/-- `(w, y)` is an affine rational point of the elliptic quotient
`E₃ : y² = (V² w² + 4U²)(W² w² + 4U²)`. -/
def OnE3 (w y : ℚ) : Prop :=
  y ^ 2 = (V m n ^ 2 * w ^ 2 + 4 * U m n ^ 2) * (W m n ^ 2 * w ^ 2 + 4 * U m n ^ 2)

/-- `(u, y)` is an affine rational point of the elliptic quotient
`E_uV : y² = (V² u² + 4(U² − V²))(W² u² − 4V²)`. -/
def OnEuV (u y : ℚ) : Prop :=
  y ^ 2 = (V m n ^ 2 * u ^ 2 + 4 * (U m n ^ 2 - V m n ^ 2)) * (W m n ^ 2 * u ^ 2 - 4 * V m n ^ 2)

/-- The hypothesis of Theorem 4.5 (a): every affine rational point of `E₃` has `w = 0`.
Equivalently, `E₃(ℚ)` has rank `0` and exactly the four torsion points `(0, ±4U²)`, `∞±`. -/
def E3Trivial : Prop := ∀ w y, OnE3 m n w y → w = 0

/-- The hypothesis of Theorem 4.5 (b)/(c): the only affine rational points of `E_uV` that lift
to `H_{m,n}` (those with `u² − 4` a square) are the ramification points `u = ±2`. -/
def EuVLiftTrivial : Prop := ∀ u y, OnEuV m n u y → IsSquare (u ^ 2 - 4) → u = 2 ∨ u = -2

variable {m n}

/-! ### Lemma 4.1: the trivial points -/

/-- The trivial points `(0, ±VW)` of `H_{m,n}`. -/
theorem onH_zero {y : ℚ} (hy : y ^ 2 = (V m n * W m n) ^ 2) : OnH m n 0 y := by
  rw [OnH, hy, P, Q]
  ring

/-- The trivial points `(±1, ±4U²)` of `H_{m,n}`. -/
theorem onH_of_sq_eq_one {t y : ℚ} (ht : t ^ 2 = 1) (hy : y ^ 2 = (4 * U m n ^ 2) ^ 2) :
    OnH m n t y := by
  rw [OnH, ht, hy, P, Q, W_sq]
  ring

/-! ### The Klein four-group and the quotient maps -/

theorem OnH.neg {t y : ℚ} (h : OnH m n t y) : OnH m n (-t) y := by
  rwa [OnH, neg_sq]

theorem P_inv {t : ℚ} (ht : t ≠ 0) : P m n (t⁻¹ ^ 2) = P m n (t ^ 2) / t ^ 4 := by
  simp only [P]
  field_simp
  ring

theorem Q_inv {t : ℚ} (ht : t ≠ 0) : Q m n (t⁻¹ ^ 2) = Q m n (t ^ 2) / t ^ 4 := by
  simp only [Q]
  field_simp
  ring

/-- The involution `σ₂ : (t, y) ↦ (1/t, y/t⁴)` of `H_{m,n}`. -/
theorem OnH.inv {t y : ℚ} (ht : t ≠ 0) (h : OnH m n t y) : OnH m n t⁻¹ (y / t ^ 4) := by
  rw [OnH, P_inv ht, Q_inv ht, div_pow, h]
  field_simp

theorem P_eq {t : ℚ} (ht : t ≠ 0) :
    P m n (t ^ 2) = t ^ 2 * (V m n ^ 2 * (t - t⁻¹) ^ 2 + 4 * U m n ^ 2) := by
  simp only [P]
  field_simp
  ring

theorem Q_eq {t : ℚ} (ht : t ≠ 0) :
    Q m n (t ^ 2) = t ^ 2 * (W m n ^ 2 * (t - t⁻¹) ^ 2 + 4 * U m n ^ 2) := by
  simp only [Q]
  field_simp
  rw [W_sq]
  ring

/-- The quotient map `π₃ : (t, y) ↦ (t − 1/t, y/t²)` from `H_{m,n}` to `E₃` (for `t ≠ 0`), and
conversely every point of `E₃` of this shape comes from `H_{m,n}`. -/
theorem onH_iff_onE3 {t y : ℚ} (ht : t ≠ 0) : OnH m n t y ↔ OnE3 m n (t - t⁻¹) (y / t ^ 2) := by
  rw [OnH, OnE3, P_eq ht, Q_eq ht, div_pow]
  have : (t ^ 2) ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    rw [div_eq_iff this] at h
    linear_combination h

/-- The quotient map `π_uV : (t, y) ↦ (t + 1/t, y/t²)` from `H_{m,n}` to `E_uV`. Its image lies
in the points with `u² − 4 = (t − 1/t)²` a square. -/
theorem OnH.toEuV {t y : ℚ} (ht : t ≠ 0) (h : OnH m n t y) :
    OnEuV m n (t + t⁻¹) (y / t ^ 2) ∧ IsSquare ((t + t⁻¹) ^ 2 - 4) := by
  refine ⟨?_, t - t⁻¹, ?_⟩
  · rw [OnEuV, div_pow, h, P, Q, W_sq]
    field_simp
    ring
  · field_simp
    ring

/-- **Lemma 4.3** for `E₃`: the involution `σ₁σ₂ : t ↦ −1/t` has no rational fixed point,
because `t² = −1` has no rational solution. -/
theorem ne_neg_inv {t : ℚ} (ht : t ≠ 0) : t ≠ -t⁻¹ := by
  intro h
  have : t ^ 2 = -1 := by
    rw [sq]
    nth_rw 2 [h]
    field_simp
  nlinarith [sq_nonneg t]

/-! ### Theorem 4.5: the conditional main theorem -/

/-- **Theorem 4.5 (a).** If `E₃` has no rational point with `w ≠ 0`, then every rational point of
`H_{m,n}` is trivial: `t ∈ {0, 1, −1}`. -/
theorem eq_trivial_of_e3Trivial (hE : E3Trivial m n) {t y : ℚ} (h : OnH m n t y) :
    t = 0 ∨ t = 1 ∨ t = -1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · exact Or.inl rfl
  have hw := hE _ _ ((onH_iff_onE3 ht).mp h)
  have : (t - 1) * (t + 1) = 0 := by
    field_simp at hw
    linear_combination hw
  rcases mul_eq_zero.mp this with h' | h'
  · exact Or.inr (Or.inl (by linear_combination h'))
  · exact Or.inr (Or.inr (by linear_combination h'))

/-- **Theorem 4.5 (b)/(c).** If the only rational points of `E_uV` that lift to `H_{m,n}` are the
ramification points `u = ±2`, then every rational point of `H_{m,n}` has `t ∈ {0, 1, −1}`. -/
theorem eq_trivial_of_euvLiftTrivial (hE : EuVLiftTrivial m n) {t y : ℚ} (h : OnH m n t y) :
    t = 0 ∨ t = 1 ∨ t = -1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · exact Or.inl rfl
  obtain ⟨h1, h2⟩ := h.toEuV ht
  have key : (t - 1) ^ 2 = 0 ∨ (t + 1) ^ 2 = 0 := by
    rcases hE _ _ h1 h2 with hu | hu
    · left
      field_simp at hu
      linear_combination hu
    · right
      field_simp at hu
      linear_combination hu
  rcases key with hk | hk
  · exact Or.inr (Or.inl (by linear_combination (exp := 2) hk))
  · exact Or.inr (Or.inr (by linear_combination (exp := 2) hk))

end Fiber

open Fiber

/-! ### Perfect cuboids on a fiber -/

namespace IsPerfectCuboid

variable {m n : ℚ} {X Y Z : ℕ}

/-- The swap `(X, Y, Z) ↦ (Z, Y, X)` of a perfect cuboid. -/
theorem swap (h : IsPerfectCuboid X Y Z) : IsPerfectCuboid Z Y X := by
  obtain ⟨⟨hX, hY, hZ, hXY, hYZ, hZX⟩, hXYZ⟩ := h
  refine ⟨⟨hZ, hY, hX, ?_, ?_, ?_⟩, ?_⟩
  · rwa [add_comm]
  · rwa [add_comm]
  · rwa [add_comm]
  · convert hXYZ using 1
    ring

/-- **A perfect cuboid on the fiber `(m, n)` is a nontrivial point of `H_{m,n}`.** If
`Z (m² − n²) = X · 2mn`, then `t = (X + d)/Y` with `d = √(X² + Y²)` is a rational point of
`H_{m,n}` with `t > 1`. -/
theorem onH (h : IsPerfectCuboid X Y Z) (hf : (Z : ℚ) * U m n = X * V m n) :
    ∃ t y, OnH m n t y ∧ 1 < t := by
  obtain ⟨⟨hX, hY, hZ, ⟨d, hd⟩, ⟨e, he⟩, -⟩, ⟨f, hf'⟩⟩ := h
  have hYd : Y < d := by
    apply Nat.mul_self_lt_mul_self_iff.mp
    rw [← hd]
    nlinarith
  have hd' : (d : ℚ) ^ 2 = X ^ 2 + Y ^ 2 := by exact_mod_cast (by rw [hd]; ring)
  have he' : (e : ℚ) ^ 2 = Y ^ 2 + Z ^ 2 := by exact_mod_cast (by rw [he]; ring)
  have hf'' : (f : ℚ) ^ 2 = X ^ 2 + Y ^ 2 + Z ^ 2 := by exact_mod_cast (by rw [hf']; ring)
  have hY0 : (Y : ℚ) ≠ 0 := by positivity
  have hXd : (X : ℚ) + d ≠ 0 := by positivity
  set t : ℚ := (X + d) / Y with ht
  have ht0 : t ≠ 0 := by positivity
  have hw : t - t⁻¹ = 2 * X / Y := by
    rw [ht, inv_div]
    field_simp
    linear_combination hd'
  refine ⟨t, t ^ 2 * (4 * U m n ^ 2 * e * f / Y ^ 2), ?_, ?_⟩
  · rw [onH_iff_onE3 ht0, mul_div_cancel_left₀ _ (by positivity), hw, OnE3]
    have hVX : V m n ^ 2 * X ^ 2 = U m n ^ 2 * Z ^ 2 := by
      linear_combination -(X * V m n + Z * U m n) * hf
    have h1 : V m n ^ 2 * (2 * X / Y) ^ 2 + 4 * U m n ^ 2 = 4 * U m n ^ 2 * e ^ 2 / Y ^ 2 := by
      field_simp
      linear_combination 4 * hVX - 4 * U m n ^ 2 * he'
    have h2 : W m n ^ 2 * (2 * X / Y) ^ 2 + 4 * U m n ^ 2 = 4 * U m n ^ 2 * f ^ 2 / Y ^ 2 := by
      rw [W_sq]
      field_simp
      linear_combination 4 * hVX - 4 * U m n ^ 2 * hf''
    rw [h1, h2]
    ring
  · rw [ht, one_lt_div (by positivity)]
    have : (Y : ℚ) < d := by exact_mod_cast hYd
    linarith [(Nat.cast_nonneg X : (0 : ℚ) ≤ X)]

/-- **No perfect cuboid on the fiber `(m, n)` if `E₃` is trivial** (Peschmann, Theorem 4.5 (a)
and Corollary 4.10): if `E₃(ℚ)` has no point with `w ≠ 0`, then no perfect cuboid has two edges
`X, Z` with `Z (m² − n²) = X · 2mn`. -/
theorem not_onFiber_of_e3Trivial (hE : E3Trivial m n) (h : IsPerfectCuboid X Y Z) :
    (Z : ℚ) * U m n ≠ X * V m n := by
  intro hf
  obtain ⟨t, y, hH, ht⟩ := h.onH hf
  rcases eq_trivial_of_e3Trivial hE hH with rfl | rfl | rfl <;> norm_num at ht

/-- **No perfect cuboid on the fiber `(m, n)` if `E_uV` has no nontrivial lift** (Peschmann,
Theorem 4.5 (b)/(c)). -/
theorem not_onFiber_of_euvLiftTrivial (hE : EuVLiftTrivial m n) (h : IsPerfectCuboid X Y Z) :
    (Z : ℚ) * U m n ≠ X * V m n := by
  intro hf
  obtain ⟨t, y, hH, ht⟩ := h.onH hf
  rcases eq_trivial_of_euvLiftTrivial hE hH with rfl | rfl | rfl <;> norm_num at ht

end IsPerfectCuboid

/-! ### Every perfect cuboid lies on a fiber -/

/-- **Every Euler brick lies on a fiber.** For an Euler brick `(X, Y, Z)` there are coprime
`m > n > 0` of opposite parity such that `Z (m² − n²) = X · 2mn` or `X (m² − n²) = Z · 2mn`. -/
theorem IsEulerBrick.exists_fiber {X Y Z : ℕ} (h : IsEulerBrick X Y Z) :
    ∃ m n : ℕ, 0 < n ∧ n < m ∧ Nat.Coprime m n ∧ (m + n) % 2 = 1 ∧
      ((Z : ℚ) * U m n = X * V m n ∨ (X : ℚ) * U m n = Z * V m n) := by
  -- the face `(X, Z)` is a multiple of a primitive Pythagorean triple
  obtain ⟨u, v, hcop, hXe, hZe⟩ := Nat.exists_coprime X Z
  set e := Nat.gcd X Z
  have he0 : 0 < e := Nat.gcd_pos_of_pos_left _ h.pos_a
  have hu : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; have := h.pos_a; simp_all)
  have hv : 0 < v := Nat.pos_of_ne_zero (by rintro rfl; have := h.pos_c; simp_all)
  have hsq : IsSquare (u ^ 2 + v ^ 2) := by
    apply isSquare_of_sq_mul he0
    have : e ^ 2 * (u ^ 2 + v ^ 2) = Z ^ 2 + X ^ 2 := by rw [hXe, hZe]; ring
    rw [this]
    exact h.sq_ca
  obtain ⟨m, n, hn, hnm, hmn, hpar, huv⟩ := exists_euclidLegs hu hv hcop hsq
  refine ⟨m, n, hn, hnm, hmn, hpar, ?_⟩
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm.le 2
  have hX : (X : ℚ) = u * e := by exact_mod_cast hXe
  have hZ : (Z : ℚ) = v * e := by exact_mod_cast hZe
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    rw [hX, hZ, U, V]
    push_cast [hle]
    ring
  · right
    rw [hX, hZ, U, V]
    push_cast [hle]
    ring

/-- **The fibers cover everything.** If on every fiber `(m, n)` (coprime, `m > n > 0`, opposite
parity) one of Peschmann's two hypotheses holds, then no perfect cuboid exists. -/
theorem not_isPerfectCuboid_of_forall
    (hE : ∀ m n : ℕ, 0 < n → n < m → Nat.Coprime m n → (m + n) % 2 = 1 →
      E3Trivial m n ∨ EuVLiftTrivial m n)
    {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) : False := by
  obtain ⟨m, n, hn, hnm, hmn, hpar, hf | hf⟩ := h.toIsEulerBrick.exists_fiber
  · rcases hE m n hn hnm hmn hpar with h' | h'
    · exact h.not_onFiber_of_e3Trivial h' hf
    · exact h.not_onFiber_of_euvLiftTrivial h' hf
  · rcases hE m n hn hnm hmn hpar with h' | h'
    · exact h.swap.not_onFiber_of_e3Trivial h' hf
    · exact h.swap.not_onFiber_of_euvLiftTrivial h' hf

/-! ### The fiber `(2, 1)` -/

/-- On the fiber `(2, 1)` the curve `E₃` is `y² = (16w² + 36)(25w² + 36)`, as in Peschmann §4.6. -/
example (w y : ℚ) : OnE3 2 1 w y ↔ y ^ 2 = (16 * w ^ 2 + 36) * (25 * w ^ 2 + 36) := by
  simp only [OnE3, U, V, W]
  norm_num

/-- On the fiber `(2, 1)` the curve `H_{2,1}` is
`y² = 400t⁸ − 124t⁶ + 744t⁴ − 124t² + 400`, as in Peschmann §4.6. -/
example (t y : ℚ) :
    OnH 2 1 t y ↔ y ^ 2 = 400 * t ^ 8 - 124 * t ^ 6 + 744 * t ^ 4 - 124 * t ^ 2 + 400 := by
  simp only [OnH, P, Q, U, V, W]
  constructor <;> intro h <;> linear_combination h

/-- The fiber `(2, 1)` is "two edges in the ratio `3 : 4`": conditionally on `E₃` for `(2, 1)`
(rank `0` and torsion of order `4`, which Peschmann verifies with PARI), no perfect cuboid has
two edges `X, Z` with `3Z = 4X`. `FiberTwoOne.lean` proves this unconditionally
(`not_isPerfectCuboid_three_four`) by a descent by hand. -/
theorem IsPerfectCuboid.three_mul_ne_of_e3Trivial (hE : E3Trivial 2 1) {X Y Z : ℕ}
    (h : IsPerfectCuboid X Y Z) : 3 * Z ≠ 4 * X := by
  intro h34
  apply h.not_onFiber_of_e3Trivial hE
  simp only [U, V]
  have : (3 * Z : ℚ) = 4 * X := by exact_mod_cast h34
  linear_combination this

end PerfectCuboid
