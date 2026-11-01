module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolynomialCuboid
public import LeanPlayground.PerfectCuboid.PolySpecialize

/-!
# Polynomial Euler bricks over `ℚ[X]`

A **polynomial Euler brick** (`IsPolyBrick a b c`) is a triple of nonzero polynomials over `ℚ`,
not all constant, such that the three face sums `a² + b²`, `a² + c²`, `b² + c²` are squares in
`ℚ[X]` (the space diagonal is not required). Unlike polynomial cuboids, these **exist**:
Saunderson's family with `m = X`, `n = 1` gives the non-proportional brick
`isPolyBrick_saunderson` with edge degrees `(6, 5, 5)`. So the structure theorems are of the
form "… ⇒ the edges are proportional".

## Main results

* `IsPolyCuboid.toIsPolyBrick`, `IsPolyBrick.swap_ab/swap_bc/swap_ac`,
  `IsPolyBrick.natDegree_pos` (no edge is constant), `IsPolyBrick.comp_X_add_C`.
* `IsPolyBrick.rat_of_proportional`, `IsPolyBrick.exists_isEulerBrick_of_proportional`.
* `IsPolyBrick.exists_isEulerBrick`: every polynomial brick specializes to an integer Euler brick.
* `isPolyBrick_saunderson`: an explicit non-proportional polynomial brick.
* `not_isSquare_two_rat`, `not_isSquare_two_mul_sq`.
* **Linear edge**: `IsPolyBrick.proportional_of_linear_edge` (`(αX, b, c)` forces `b = βX`,
  `c = γX`) and `IsPolyBrick.exists_isEulerBrick_of_natDegree_eq_one'`.
* **Quadratic monomial edge**: `IsPolyBrick.proportional_of_quadratic_monomial_edge`
  (`(αX², b, c)` forces `b = βX²`, `c = γX²`), no coprimality assumed.
* **Mason–Stothers, radical form**: `natDegree_hyp_add_one_le_radical`
  (`deg z + 1 ≤ deg rad x + deg rad y` for coprime `x² + y² = z²`) and
  `IsPolyBrick.radical_sum_bound` for pairwise coprime bricks.

The monomial edge `α X^k` for `k ≥ 3` is open for bricks (a five-term square problem).
-/
@[expose] public section

open Polynomial

namespace PerfectCuboid.Poly

/-- A polynomial Euler brick over `ℚ`: nonzero edges, not all constant, three square faces. -/
structure IsPolyBrick (a b c : ℚ[X]) : Prop where
  ne_a : a ≠ 0
  ne_b : b ≠ 0
  ne_c : c ≠ 0
  nonconst : ¬ (a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0)
  sq_ab : IsSquare (a ^ 2 + b ^ 2)
  sq_ac : IsSquare (a ^ 2 + c ^ 2)
  sq_bc : IsSquare (b ^ 2 + c ^ 2)

/-! ### Basics -/

theorem IsPolyCuboid.toIsPolyBrick {a b c : ℚ[X]} (h : IsPolyCuboid a b c) :
    IsPolyBrick a b c :=
  ⟨h.ne_a, h.ne_b, h.ne_c, h.nonconst, h.sq_ab, h.sq_ac, h.sq_bc⟩

theorem IsPolyBrick.swap_ab {a b c : ℚ[X]} (h : IsPolyBrick a b c) : IsPolyBrick b a c where
  ne_a := h.ne_b
  ne_b := h.ne_a
  ne_c := h.ne_c
  nonconst := fun ⟨h1, h2, h3⟩ => h.nonconst ⟨h2, h1, h3⟩
  sq_ab := by convert h.sq_ab using 1; ring
  sq_ac := h.sq_bc
  sq_bc := h.sq_ac

theorem IsPolyBrick.swap_bc {a b c : ℚ[X]} (h : IsPolyBrick a b c) : IsPolyBrick a c b where
  ne_a := h.ne_a
  ne_b := h.ne_c
  ne_c := h.ne_b
  nonconst := fun ⟨h1, h2, h3⟩ => h.nonconst ⟨h1, h3, h2⟩
  sq_ab := h.sq_ac
  sq_ac := h.sq_ab
  sq_bc := by convert h.sq_bc using 1; ring

theorem IsPolyBrick.swap_ac {a b c : ℚ[X]} (h : IsPolyBrick a b c) : IsPolyBrick c b a where
  ne_a := h.ne_c
  ne_b := h.ne_b
  ne_c := h.ne_a
  nonconst := fun ⟨h1, h2, h3⟩ => h.nonconst ⟨h3, h2, h1⟩
  sq_ab := by convert h.sq_bc using 1; ring
  sq_ac := by convert h.sq_ac using 1; ring
  sq_bc := by convert h.sq_ab using 1; ring

/-- No edge of a polynomial brick is constant (each edge lies on two faces). -/
theorem IsPolyBrick.natDegree_pos {a b c : ℚ[X]} (h : IsPolyBrick a b c) :
    0 < a.natDegree ∧ 0 < b.natDegree ∧ 0 < c.natDegree := by
  obtain ⟨d, hd⟩ := eq_sq_of_isSquare h.sq_ab
  obtain ⟨e, he⟩ := eq_sq_of_isSquare h.sq_ac
  obtain ⟨f, hf⟩ := eq_sq_of_isSquare h.sq_bc
  refine ⟨Nat.pos_of_ne_zero fun ha => ?_, Nat.pos_of_ne_zero fun hb => ?_,
    Nat.pos_of_ne_zero fun hc => ?_⟩
  · exact h.nonconst ⟨ha, (natDegree_eq_zero_of_leg h.ne_a ha hd).1,
      (natDegree_eq_zero_of_leg h.ne_a ha he).1⟩
  · exact h.nonconst ⟨(natDegree_eq_zero_of_leg h.ne_b hb (by rw [← hd]; ring)).1, hb,
      (natDegree_eq_zero_of_leg h.ne_b hb hf).1⟩
  · exact h.nonconst ⟨(natDegree_eq_zero_of_leg h.ne_c hc (by rw [← he]; ring)).1,
      (natDegree_eq_zero_of_leg h.ne_c hc (by rw [← hf]; ring)).1, hc⟩

/-- Translation `X ↦ X + r` maps polynomial bricks to polynomial bricks. -/
theorem IsPolyBrick.comp_X_add_C {a b c : ℚ[X]} (h : IsPolyBrick a b c) (r : ℚ) :
    IsPolyBrick (a.comp (X + C r)) (b.comp (X + C r)) (c.comp (X + C r)) := by
  have hne : ∀ p : ℚ[X], p ≠ 0 → p.comp (X + C r) ≠ 0 := by
    intro p hp h0
    apply hp
    rw [← comp_X_add_C_comp_X_sub_C p r, h0, zero_comp]
  have hdeg : ∀ p : ℚ[X], (p.comp (X + C r)).natDegree = p.natDegree := by
    intro p
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have hsq : ∀ p : ℚ[X], IsSquare p → IsSquare (p.comp (X + C r)) := by
    intro p hp
    simpa [coe_compRingHom_apply] using hp.map (compRingHom (X + C r))
  refine ⟨hne a h.ne_a, hne b h.ne_b, hne c h.ne_c, ?_, ?_, ?_, ?_⟩
  · rw [hdeg, hdeg, hdeg]; exact h.nonconst
  · simpa [add_comp, pow_comp] using hsq _ h.sq_ab
  · simpa [add_comp, pow_comp] using hsq _ h.sq_ac
  · simpa [add_comp, pow_comp] using hsq _ h.sq_bc

/-- Proportional edges give a rational Euler brick. -/
theorem IsPolyBrick.rat_of_proportional {a b c : ℚ[X]} (h : IsPolyBrick a b c) {α β γ : ℚ}
    {q : ℚ[X]} (ha : a = C α * q) (hb : b = C β * q) (hc : c = C γ * q) :
    IsSquare (α ^ 2 + β ^ 2) ∧ IsSquare (α ^ 2 + γ ^ 2) ∧ IsSquare (β ^ 2 + γ ^ 2) := by
  have hq : q ≠ 0 := by
    rintro rfl
    exact h.ne_a (by rw [ha, mul_zero])
  obtain ⟨d, hd⟩ := eq_sq_of_isSquare h.sq_ab
  obtain ⟨e, he⟩ := eq_sq_of_isSquare h.sq_ac
  obtain ⟨f, hf⟩ := eq_sq_of_isSquare h.sq_bc
  subst ha hb hc
  refine ⟨isSquare_of_C_mul_sq (s := d) hq ?_, isSquare_of_C_mul_sq (s := e) hq ?_,
    isSquare_of_C_mul_sq (s := f) hq ?_⟩
  · rw [← hd]; simp only [map_add, map_pow]; ring
  · rw [← he]; simp only [map_add, map_pow]; ring
  · rw [← hf]; simp only [map_add, map_pow]; ring

/-- **Specialization for bricks.** Every polynomial Euler brick gives an integer Euler brick. -/
theorem IsPolyBrick.exists_isEulerBrick {a b c : ℚ[X]} (h : IsPolyBrick a b c) :
    ∃ A B C : ℕ, IsEulerBrick A B C := by
  obtain ⟨r, ha, hb, hc⟩ := exists_eval_ne_zero h.ne_a h.ne_b h.ne_c
  have hab := isSquare_eval h.sq_ab r
  have hac := isSquare_eval h.sq_ac r
  have hbc := isSquare_eval h.sq_bc r
  simp only [eval_add, eval_pow] at hab hac hbc
  exact exists_isEulerBrick_of_rat (abs_pos.mpr ha) (abs_pos.mpr hb) (abs_pos.mpr hc)
    (by simpa only [sq_abs] using hab) (by simpa only [sq_abs] using hac)
    (by simpa only [sq_abs] using hbc)

/-- A polynomial brick with proportional edges gives an integer Euler brick. -/
theorem IsPolyBrick.exists_isEulerBrick_of_proportional {a b c : ℚ[X]} (h : IsPolyBrick a b c)
    {α β γ : ℚ} {q : ℚ[X]} (ha : a = C α * q) (hb : b = C β * q) (hc : c = C γ * q) :
    ∃ A B C : ℕ, IsEulerBrick A B C := by
  obtain ⟨h1, h2, h3⟩ := h.rat_of_proportional ha hb hc
  have hα : α ≠ 0 := by rintro rfl; exact h.ne_a (by rw [ha]; simp)
  have hβ : β ≠ 0 := by rintro rfl; exact h.ne_b (by rw [hb]; simp)
  have hγ : γ ≠ 0 := by rintro rfl; exact h.ne_c (by rw [hc]; simp)
  exact exists_isEulerBrick_of_rat (abs_pos.mpr hα) (abs_pos.mpr hβ) (abs_pos.mpr hγ)
    (by simpa only [sq_abs] using h1) (by simpa only [sq_abs] using h2)
    (by simpa only [sq_abs] using h3)

/-- Conversely an integer Euler brick `(p, q, r)` gives the polynomial brick `(pX, qX, rX)`. -/
theorem _root_.PerfectCuboid.IsEulerBrick.isPolyBrick {p q r : ℕ} (h : IsEulerBrick p q r) :
    IsPolyBrick (C (p : ℚ) * X) (C (q : ℚ) * X) (C (r : ℚ) * X) := by
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast h.pos_a.ne'
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast h.pos_b.ne'
  have hr : (r : ℚ) ≠ 0 := by exact_mod_cast h.pos_c.ne'
  have sq2 : ∀ x y : ℕ, IsSquare (x ^ 2 + y ^ 2) →
      IsSquare ((C (x : ℚ) * X) ^ 2 + (C (y : ℚ) * X) ^ 2) := by
    rintro x y ⟨s, hs⟩
    have hs' : (x : ℚ) ^ 2 + (y : ℚ) ^ 2 = (s : ℚ) * s := by exact_mod_cast hs
    refine ⟨C (s : ℚ) * X, ?_⟩
    have : (C (x : ℚ) * X) ^ 2 + (C (y : ℚ) * X) ^ 2 = C ((x : ℚ) ^ 2 + (y : ℚ) ^ 2) * X ^ 2 := by
      simp only [map_add, map_pow]; ring
    rw [this, hs', map_mul]; ring
  refine ⟨by simpa using hp, by simpa using hq, by simpa using hr, ?_, sq2 p q h.sq_ab,
    ?_, sq2 q r h.sq_bc⟩
  · rintro ⟨h1, -, -⟩
    rw [natDegree_C_mul_X _ hp] at h1
    exact one_ne_zero h1
  · have := sq2 r p h.sq_ca
    convert this using 1; ring

/-! ### An explicit non-proportional polynomial brick (Saunderson, `m = X`, `n = 1`) -/

/-- **Saunderson's polynomial Euler brick.** With `u = X² − 1`, `v = 2X`, `w = X² + 1`, the
edges `u (4v² − w²)`, `v (4u² − w²)`, `4uvw` (degrees `6, 5, 5`) have face diagonals `w³`,
`u (4v² + w²)`, `v (4u² + w²)`. The edges are not proportional (`a / c` is non-constant). -/
theorem isPolyBrick_saunderson :
    IsPolyBrick ((X ^ 2 - 1) * (4 * (2 * X) ^ 2 - (X ^ 2 + 1) ^ 2))
      (2 * X * (4 * (X ^ 2 - 1) ^ 2 - (X ^ 2 + 1) ^ 2))
      (4 * (X ^ 2 - 1) * (2 * X) * (X ^ 2 + 1)) where
  ne_a := by
    intro h
    have := congrArg (eval 2) h
    norm_num at this
  ne_b := by
    intro h
    have := congrArg (eval 1) h
    norm_num at this
  ne_c := by
    intro h
    have := congrArg (eval 2) h
    norm_num at this
  nonconst := by
    rintro ⟨-, -, h⟩
    have h0 := eq_C_of_natDegree_eq_zero h
    have e2 := congrArg (eval 2) h0
    have e1 := congrArg (eval 1) h0
    simp only [eval_C] at e1 e2
    rw [← e1] at e2
    norm_num at e2
  sq_ab := ⟨(X ^ 2 + 1) ^ 3, by ring⟩
  sq_ac := ⟨(X ^ 2 - 1) * (4 * (2 * X) ^ 2 + (X ^ 2 + 1) ^ 2), by ring⟩
  sq_bc := ⟨2 * X * (4 * (X ^ 2 - 1) ^ 2 + (X ^ 2 + 1) ^ 2), by ring⟩

/-- Saunderson's brick is not proportional: no constants make `a = α q` and `c = γ q` with
`q` the same polynomial and both `α, γ ≠ 0` unless `γ a = α c`, which fails at `X = 2` and
`X = 3`. -/
theorem saunderson_not_proportional :
    ¬ ∃ α γ : ℚ, (α ≠ 0 ∨ γ ≠ 0) ∧ C γ * ((X ^ 2 - 1) * (4 * (2 * X) ^ 2 - (X ^ 2 + 1) ^ 2)) =
      C α * (4 * (X ^ 2 - 1) * (2 * X) * (X ^ 2 + 1)) := by
  rintro ⟨α, γ, hne, h⟩
  have e2 := congrArg (eval 2) h
  have e3 := congrArg (eval 3) h
  simp only [eval_mul, eval_C, eval_sub, eval_pow, eval_X, eval_add, eval_one,
    eval_ofNat] at e2 e3
  norm_num at e2 e3
  rcases hne with hne | hne
  · apply hne; linarith
  · apply hne; linarith

/-! ### `2` is not a square -/

theorem not_isSquare_two_rat : ¬ IsSquare (2 : ℚ) := by
  intro h
  rw [Rat.isSquare_iff] at h
  have h2 : IsSquare ((2 : ℕ) : ℤ) := by simpa using h.1
  rw [Int.isSquare_natCast_iff] at h2
  obtain ⟨k, hk⟩ := h2
  have hk2 : k ≤ 2 := by nlinarith
  interval_cases k <;> omega

theorem not_isSquare_two_mul_sq {p : ℚ[X]} (hp : p ≠ 0) : ¬ IsSquare (C 2 * p ^ 2) := by
  rintro ⟨s, hs⟩
  exact not_isSquare_two_rat (isSquare_of_C_mul_sq (s := s) hp (by rw [hs]; ring))

/-- If `(α q)² + (β q)²` is a square with `β² = α²` and `α q ≠ 0`, contradiction. -/
theorem false_of_sq_eq_sq {α β : ℚ} {q d : ℚ[X]} (hq : C α * q ≠ 0) (hβ : β ^ 2 = α ^ 2)
    (h : (C α * q) ^ 2 + (C β * q) ^ 2 = d ^ 2) : False := by
  apply not_isSquare_two_mul_sq hq
  refine ⟨d, ?_⟩
  have hC : C β ^ 2 = C α ^ 2 := by rw [← C_pow, ← C_pow, hβ]
  rw [show (C 2 : ℚ[X]) = 2 from map_ofNat C 2]
  linear_combination h - q ^ 2 * hC

/-! ### Auxiliary square computations -/

/-- Mixed face: `(β Xⁿ)² + c²` square with `2c = v X^{2n} − u` forces `β² = uv`. -/
theorem mixed_face {β u v : ℚ} {n : ℕ} (hn : 0 < n) (hv : v ≠ 0) (hβ : β ≠ 0) {c f : ℚ[X]}
    (hc : 2 * c = C v * X ^ (2 * n) - C u) (hf : (C β * X ^ n) ^ 2 + c ^ 2 = f ^ 2) :
    β ^ 2 = u * v := by
  have key : (2 * f) ^ 2 = C (v ^ 2) * X ^ (2 * (2 * n)) + C (4 * β ^ 2 - 2 * (u * v)) *
      X ^ (2 * n) + C (u ^ 2) := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    linear_combination (-4 : ℚ[X]) * hf + (2 * c + (C v * X ^ (2 * n) - C u)) * hc
  have hd := quad_disc (by omega) (pow_ne_zero 2 hv) key
  have h1 : β ^ 2 * (β ^ 2 - u * v) = 0 := by linear_combination hd / 16
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hβ
  · linear_combination h

/-- Two coprime-type legs: `2b = v Xⁿ − u`, `2c = v' Xⁿ − u'` with `uv = u'v' = α² ≠ 0` and
`b² + c²` a square is impossible. -/
theorem false_of_two_legs {α u v u' v' : ℚ} {n : ℕ} (hn : 0 < n) (hα : α ≠ 0)
    (huv : u * v = α ^ 2) (huv' : u' * v' = α ^ 2) {b c f : ℚ[X]} (hb0 : b ≠ 0)
    (hb : 2 * b = C v * X ^ n - C u) (hc : 2 * c = C v' * X ^ n - C u')
    (hf : b ^ 2 + c ^ 2 = f ^ 2) : False := by
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα
  have hu : u ≠ 0 := by rintro rfl; rw [zero_mul] at huv; exact hα2 huv.symm
  have hv : v ≠ 0 := by rintro rfl; rw [mul_zero] at huv; exact hα2 huv.symm
  have key : (2 * f) ^ 2 = C (v ^ 2 + v' ^ 2) * X ^ (2 * n) +
      C (-(2 * (u * v) + 2 * (u' * v'))) * X ^ n + C (u ^ 2 + u' ^ 2) := by
    simp only [map_add, map_neg, map_mul, map_pow, map_ofNat]
    linear_combination (-4 : ℚ[X]) * hf + (2 * b + (C v * X ^ n - C u)) * hb +
      (2 * c + (C v' * X ^ n - C u')) * hc
  have hA : v ^ 2 + v' ^ 2 ≠ 0 := by positivity
  have hd := quad_disc hn hA key
  have e0 : (v * u' - v' * u) ^ 2 = 0 := by linear_combination (-1 / 4 : ℚ) * hd
  have e1 : v * u' = v' * u := by
    have := pow_eq_zero_iff two_ne_zero |>.mp e0
    linear_combination this
  have e2 : u * v = u' * v' := by rw [huv, huv']
  have hv2 : v' ^ 2 = v ^ 2 := by
    have : (v' ^ 2 - v ^ 2) * u = 0 := by linear_combination (-v') * e1 - v * e2
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h hu
  have hu2 : u' ^ 2 = u ^ 2 := by
    have : (u' ^ 2 - u ^ 2) * v ^ 2 = 0 := by
      linear_combination (v * u' + v' * u) * e1 + u ^ 2 * hv2
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hv
  have c1 : C v' ^ 2 = C v ^ 2 := by rw [← C_pow, ← C_pow, hv2]
  have c2 : C u' ^ 2 = C u ^ 2 := by rw [← C_pow, ← C_pow, hu2]
  have c3 : C u' * C v' = C u * C v := by rw [← C_mul, ← C_mul, e2]
  have hcb : (2 * c) ^ 2 = (2 * b) ^ 2 := by
    rw [hb, hc]
    linear_combination X ^ (2 * n) * c1 + c2 - 2 * X ^ n * c3
  have h2b : 2 * b ≠ 0 := mul_ne_zero two_ne_zero hb0
  apply not_isSquare_two_mul_sq h2b
  refine ⟨2 * f, ?_⟩
  rw [show (C 2 : ℚ[X]) = 2 from map_ofNat C 2]
  linear_combination (4 : ℚ[X]) * hf - hcb

/-- Removing a common factor `X` from a face. -/
theorem face_div_X {p q f : ℚ[X]} (h : (X * p) ^ 2 + (X * q) ^ 2 = f ^ 2) :
    ∃ f₁, p ^ 2 + q ^ 2 = f₁ ^ 2 := by
  have hXf : X ∣ f := by
    apply prime_X.dvd_of_dvd_pow (n := 2)
    rw [← h]
    exact ⟨X * p ^ 2 + X * q ^ 2, by ring⟩
  obtain ⟨f₁, rfl⟩ := hXf
  refine ⟨f₁, ?_⟩
  have : X ^ 2 * (p ^ 2 + q ^ 2) = X ^ 2 * f₁ ^ 2 := by linear_combination h
  exact mul_left_cancel₀ (pow_ne_zero 2 X_ne_zero) this

/-! ### Linear edge -/

/-- **Linear edge forces proportional edges (bricks).** If `(α X, b, c)` is a polynomial Euler
brick, then `b = β X` and `c = γ X`. -/
theorem IsPolyBrick.proportional_of_linear_edge {α : ℚ} {b c : ℚ[X]}
    (h : IsPolyBrick (C α * X) b c) : ∃ β γ : ℚ, b = C β * X ∧ c = C γ * X := by
  have hα : α ≠ 0 := by rintro rfl; exact h.ne_a (by simp)
  have hαX : C α * X ≠ 0 := h.ne_a
  obtain ⟨d, hd⟩ := eq_sq_of_isSquare h.sq_ab
  obtain ⟨e, he⟩ := eq_sq_of_isSquare h.sq_ac
  obtain ⟨f, hf⟩ := eq_sq_of_isSquare h.sq_bc
  have hd' : (C α * X ^ 1) ^ 2 + b ^ 2 = d ^ 2 := by rw [pow_one]; exact hd
  have he' : (C α * X ^ 1) ^ 2 + c ^ 2 = e ^ 2 := by rw [pow_one]; exact he
  have hv0 : ∀ u v : ℚ, u * v = α ^ 2 → v ≠ 0 := by
    rintro u v huv rfl
    rw [mul_zero] at huv
    exact pow_ne_zero 2 hα huv.symm
  by_cases hb : X ∣ b <;> by_cases hc : X ∣ c
  · obtain ⟨β, hβ⟩ := linear_leg_of_X_dvd hα hd hb
    obtain ⟨γ, hγ⟩ := linear_leg_of_X_dvd hα he hc
    exact ⟨β, γ, hβ, hγ⟩
  · exfalso
    obtain ⟨β, rfl⟩ := linear_leg_of_X_dvd hα hd hb
    have hβ : β ≠ 0 := by rintro rfl; exact h.ne_b (by simp)
    obtain ⟨u, v, huv, hc2⟩ := monomial_leg hα (isCoprime_C_mul_X_of_not_dvd hα hc) he'
    have := mixed_face one_pos (hv0 u v huv) hβ hc2 (by rw [pow_one]; exact hf)
    exact false_of_sq_eq_sq hαX (by rw [this, huv]) hd
  · exfalso
    obtain ⟨γ, rfl⟩ := linear_leg_of_X_dvd hα he hc
    have hγ : γ ≠ 0 := by rintro rfl; exact h.ne_c (by simp)
    obtain ⟨u, v, huv, hb2⟩ := monomial_leg hα (isCoprime_C_mul_X_of_not_dvd hα hb) hd'
    have := mixed_face one_pos (hv0 u v huv) hγ hb2 (by rw [pow_one, ← hf]; ring)
    exact false_of_sq_eq_sq hαX (by rw [this, huv]) he
  · exfalso
    obtain ⟨u, v, huv, hb2⟩ := monomial_leg hα (isCoprime_C_mul_X_of_not_dvd hα hb) hd'
    obtain ⟨u', v', huv', hc2⟩ := monomial_leg hα (isCoprime_C_mul_X_of_not_dvd hα hc) he'
    exact false_of_two_legs (by norm_num) hα huv huv' h.ne_b hb2 hc2 hf

/-- A polynomial brick with an edge of degree one gives an integer Euler brick (and conversely,
`IsEulerBrick.isPolyBrick`); its edges are then proportional after a translation. -/
theorem IsPolyBrick.exists_isEulerBrick_of_natDegree_eq_one {a b c : ℚ[X]}
    (h : IsPolyBrick a b c) (ha : a.natDegree = 1) : ∃ A B C : ℕ, IsEulerBrick A B C := by
  obtain ⟨α, r, hr⟩ := exists_comp_eq_C_mul_X ha
  have h' := h.comp_X_add_C r
  rw [hr] at h'
  obtain ⟨β, γ, hb, hc⟩ := h'.proportional_of_linear_edge
  exact h'.exists_isEulerBrick_of_proportional rfl hb hc

theorem IsPolyBrick.exists_isEulerBrick_of_natDegree_eq_one' {a b c : ℚ[X]}
    (h : IsPolyBrick a b c) (hdeg : a.natDegree = 1 ∨ b.natDegree = 1 ∨ c.natDegree = 1) :
    ∃ A B C : ℕ, IsEulerBrick A B C := by
  rcases hdeg with h1 | h1 | h1
  · exact h.exists_isEulerBrick_of_natDegree_eq_one h1
  · exact h.swap_ab.exists_isEulerBrick_of_natDegree_eq_one h1
  · exact h.swap_ac.exists_isEulerBrick_of_natDegree_eq_one h1

/-! ### Quadratic monomial edge -/

/-- The three possible shapes of a leg `b` in a face `(α X², b, d)`. -/
theorem quad_leg {α : ℚ} (hα : α ≠ 0) {b d : ℚ[X]} (h : (C α * X ^ 2) ^ 2 + b ^ 2 = d ^ 2) :
    (∃ β : ℚ, b = C β * X ^ 2) ∨
      (∃ (b₁ : ℚ[X]) (u v : ℚ), u * v = α ^ 2 ∧ b = X * b₁ ∧ 2 * b₁ = C v * X ^ 2 - C u) ∨
      (∃ u v : ℚ, u * v = α ^ 2 ∧ 2 * b = C v * X ^ 4 - C u) := by
  by_cases hX : X ∣ b
  · obtain ⟨b₁, rfl⟩ := hX
    have hXd : X ∣ d := by
      apply prime_X.dvd_of_dvd_pow (n := 2)
      rw [← h]
      exact ⟨C α ^ 2 * X ^ 3 + b₁ ^ 2 * X, by ring⟩
    obtain ⟨d₁, rfl⟩ := hXd
    have h1 : (C α * X) ^ 2 + b₁ ^ 2 = d₁ ^ 2 := by
      have : X ^ 2 * ((C α * X) ^ 2 + b₁ ^ 2) = X ^ 2 * d₁ ^ 2 := by linear_combination h
      exact mul_left_cancel₀ (pow_ne_zero 2 X_ne_zero) this
    by_cases hX1 : X ∣ b₁
    · obtain ⟨β, hβ⟩ := linear_leg_of_X_dvd hα h1 hX1
      left
      exact ⟨β, by rw [hβ]; ring⟩
    · right; left
      obtain ⟨u, v, huv, hb⟩ := monomial_leg hα (isCoprime_C_mul_X_of_not_dvd hα hX1)
        (by rw [pow_one]; exact h1)
      exact ⟨b₁, u, v, huv, rfl, hb⟩
  · right; right
    have hC : IsCoprime (C α) b := ⟨C α⁻¹, 0, by rw [← C_mul, inv_mul_cancel₀ hα, C_1]; ring⟩
    have hcop : IsCoprime (C α * X ^ 2) b :=
      hC.mul_left ((irreducible_X.coprime_iff_not_dvd).mpr hX).pow_left
    exact monomial_leg hα hcop h

/-- Coefficients of `F²` in low degrees. -/
theorem coeff_sq_succ (F : ℚ[X]) (n : ℕ) :
    (F ^ 2).coeff n = ∑ k ∈ Finset.range (n + 1), F.coeff k * F.coeff (n - k) := by
  rw [sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- **The five-term case.** `2P = v X⁴ − u`, `Q = X Q₁` with `2Q₁ = v' X² − u'`,
`uv = u'v' = α² ≠ 0`: then `P² + Q²` is not a square. -/
theorem false_of_five_term {α u v u' v' : ℚ} (hα : α ≠ 0) (huv : u * v = α ^ 2)
    (huv' : u' * v' = α ^ 2) {P Q₁ f : ℚ[X]} (hP : 2 * P = C v * X ^ 4 - C u)
    (hQ : 2 * Q₁ = C v' * X ^ 2 - C u') (hf : P ^ 2 + (X * Q₁) ^ 2 = f ^ 2) : False := by
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα
  have hu : u ≠ 0 := by rintro rfl; rw [zero_mul] at huv; exact hα2 huv.symm
  have hu' : u' ≠ 0 := by rintro rfl; rw [zero_mul] at huv'; exact hα2 huv'.symm
  set F := 2 * f with hFdef
  have key : F ^ 2 = C (v ^ 2) * X ^ 8 + C (v' ^ 2) * X ^ 6 +
      C (-(2 * (u * v) + 2 * (u' * v'))) * X ^ 4 + C (u' ^ 2) * X ^ 2 + C (u ^ 2) := by
    simp only [map_add, map_neg, map_mul, map_pow, map_ofNat]
    rw [hFdef]
    linear_combination (-4 : ℚ[X]) * hf + (2 * P + (C v * X ^ 4 - C u)) * hP +
      X ^ 2 * (2 * Q₁ + (C v' * X ^ 2 - C u')) * hQ
  have hdeg : F.natDegree ≤ 4 := by
    have h8 : (F ^ 2).natDegree ≤ 8 := by rw [key]; compute_degree
    rw [natDegree_pow] at h8
    omega
  have hF5 : F.coeff 5 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hF6 : F.coeff 6 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have cf : ∀ n, (F ^ 2).coeff n = (C (v ^ 2) * X ^ 8 + C (v' ^ 2) * X ^ 6 +
      C (-(2 * (u * v) + 2 * (u' * v'))) * X ^ 4 + C (u' ^ 2) * X ^ 2 + C (u ^ 2)).coeff n := by
    intro n; rw [key]
  have c0 := cf 0
  have c1 := cf 1
  have c2 := cf 2
  have c3 := cf 3
  have c4 := cf 4
  have c6 := cf 6
  simp only [coeff_sq_succ, Finset.sum_range_succ, Finset.sum_range_zero, coeff_add,
    coeff_C_mul_X_pow, coeff_C] at c0 c1 c2 c3 c4 c6
  norm_num at c0 c1 c2 c3 c4 c6
  rw [hF5, hF6] at c6
  set f0 := F.coeff 0
  set f1 := F.coeff 1
  set f2 := F.coeff 2
  set f3 := F.coeff 3
  set f4 := F.coeff 4
  have hf0 : f0 ≠ 0 := by
    intro h0; rw [h0] at c0; apply hu; nlinarith [c0]
  have hf1 : f1 = 0 := by
    have : 2 * f0 * f1 = 0 := by linear_combination c1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linarith : f0 = 0) hf0
    · exact h
  have hf3 : f3 = 0 := by
    have : 2 * f0 * f3 = 0 := by rw [hf1] at c3; linear_combination c3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linarith : f0 = 0) hf0
    · exact h
  simp only [hf1, hf3] at c2 c4 c6
  -- c2 : 2 f0 f2 = u'², c4 : 2 f0 f4 + f2² = -(4 α²), c6 : 2 f2 f4 = v'²
  have hprod : 4 * (f0 * f4) * f2 ^ 2 = (α ^ 2) ^ 2 := by
    have : (u' * v') ^ 2 = (α ^ 2) ^ 2 := by rw [huv']
    nlinarith [c2, c6, this]
  have hneg : f2 ^ 2 + 2 * (f0 * f4) = -(4 * α ^ 2) := by
    rw [huv, huv'] at c4; linear_combination c4
  have hα4 : 0 < (α ^ 2) ^ 2 := by positivity
  have hα2' : 0 < α ^ 2 := by positivity
  have h04 : f0 * f4 < 0 := by nlinarith [sq_nonneg f2]
  have : 4 * (f0 * f4) * f2 ^ 2 ≤ 0 := by
    have := mul_nonpos_of_nonpos_of_nonneg (by linarith : 4 * (f0 * f4) ≤ 0) (sq_nonneg f2)
    linarith
  linarith

/-- **Quadratic monomial edge forces proportional edges (bricks).** If `(α X², b, c)` is a
polynomial Euler brick, then `b = β X²` and `c = γ X²`. No coprimality is assumed. -/
theorem IsPolyBrick.proportional_of_quadratic_monomial_edge {α : ℚ} {b c : ℚ[X]}
    (h : IsPolyBrick (C α * X ^ 2) b c) : ∃ β γ : ℚ, b = C β * X ^ 2 ∧ c = C γ * X ^ 2 := by
  have hα : α ≠ 0 := by rintro rfl; exact h.ne_a (by simp)
  have hαX : C α * X ^ 2 ≠ 0 := h.ne_a
  obtain ⟨d, hd⟩ := eq_sq_of_isSquare h.sq_ab
  obtain ⟨e, he⟩ := eq_sq_of_isSquare h.sq_ac
  obtain ⟨f, hf⟩ := eq_sq_of_isSquare h.sq_bc
  have hv0 : ∀ u v : ℚ, u * v = α ^ 2 → v ≠ 0 := by
    rintro u v huv rfl
    rw [mul_zero] at huv
    exact pow_ne_zero 2 hα huv.symm
  have hX1 : ∀ (p : ℚ[X]) (u v : ℚ), 2 * p = C v * X ^ 2 - C u →
      2 * p = C v * X ^ (2 * 1) - C u := fun p u v hp => by rw [mul_one]; exact hp
  have hX2 : ∀ (p : ℚ[X]) (u v : ℚ), 2 * p = C v * X ^ 4 - C u →
      2 * p = C v * X ^ (2 * 2) - C u := fun p u v hp => hp
  rcases quad_leg hα hd with ⟨β, hβ⟩ | ⟨b₁, u, v, huv, hb, hb1⟩ | ⟨u, v, huv, hb2⟩ <;>
  rcases quad_leg hα he with ⟨γ, hγ⟩ | ⟨c₁, u', v', huv', hc, hc1⟩ | ⟨u', v', huv', hc2⟩
  · exact ⟨β, γ, hβ, hγ⟩
  · exfalso
    have hβ0 : β ≠ 0 := by rintro rfl; exact h.ne_b (by rw [hβ]; simp)
    obtain ⟨f₁, hf₁⟩ := face_div_X (p := C β * X) (q := c₁) (f := f)
      (by rw [← hf, hβ, hc]; ring)
    have := mixed_face one_pos (hv0 u' v' huv') hβ0 (hX1 _ _ _ hc1)
      (by rw [pow_one]; exact hf₁)
    exact false_of_sq_eq_sq hαX (by rw [this, huv']) (by rw [← hβ]; exact hd)
  · exfalso
    have hβ0 : β ≠ 0 := by rintro rfl; exact h.ne_b (by rw [hβ]; simp)
    have := mixed_face two_pos (hv0 u' v' huv') hβ0 (hX2 _ _ _ hc2)
      (by rw [← hβ]; exact hf)
    exact false_of_sq_eq_sq hαX (by rw [this, huv']) (by rw [← hβ]; exact hd)
  · exfalso
    have hγ0 : γ ≠ 0 := by rintro rfl; exact h.ne_c (by rw [hγ]; simp)
    obtain ⟨f₁, hf₁⟩ := face_div_X (p := C γ * X) (q := b₁) (f := f)
      (by rw [← hf, hγ, hb]; ring)
    have := mixed_face one_pos (hv0 u v huv) hγ0 (hX1 _ _ _ hb1)
      (by rw [pow_one]; exact hf₁)
    exact false_of_sq_eq_sq hαX (by rw [this, huv]) (by rw [← hγ]; exact he)
  · exfalso
    have hb₁ : b₁ ≠ 0 := by rintro rfl; exact h.ne_b (by rw [hb, mul_zero])
    obtain ⟨f₁, hf₁⟩ := face_div_X (p := b₁) (q := c₁) (f := f) (by rw [← hf, hb, hc])
    exact false_of_two_legs two_pos hα huv huv' hb₁ hb1 hc1 hf₁
  · exfalso
    exact false_of_five_term hα huv' huv hc2 hb1 (by rw [← hb, ← hf]; ring)
  · exfalso
    have hγ0 : γ ≠ 0 := by rintro rfl; exact h.ne_c (by rw [hγ]; simp)
    have := mixed_face two_pos (hv0 u v huv) hγ0 (hX2 _ _ _ hb2)
      (by rw [← hγ, ← hf]; ring)
    exact false_of_sq_eq_sq hαX (by rw [this, huv]) (by rw [← hγ]; exact he)
  · exfalso
    exact false_of_five_term hα huv huv' hb2 hc1 (by rw [← hc]; exact hf)
  · exfalso
    exact false_of_two_legs (by norm_num) hα huv huv' h.ne_b hb2 hc2 hf

/-! ### Mason–Stothers, radical form -/

open UniqueFactorizationMonoid in
/-- **Mason–Stothers for polynomial Pythagorean triples, radical form.** If `x² + y² = z²` with
`x, y` coprime and `z` non-constant, then `deg z + 1 ≤ deg rad x + deg rad y`. -/
theorem natDegree_hyp_add_one_le_radical {x y z : ℚ[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : IsCoprime x y) (h : x ^ 2 + y ^ 2 = z ^ 2) (hz : 0 < z.natDegree) :
    z.natDegree + 1 ≤ (radical x).natDegree + (radical y).natDegree := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hsum : x ^ 2 + y ^ 2 + (-(z ^ 2)) = 0 := by rw [h]; ring
  rcases Polynomial.abc (pow_ne_zero 2 hx) (pow_ne_zero 2 hy) (neg_ne_zero.mpr (pow_ne_zero 2 hz0))
    (hxy.pow) hsum with ⟨-, -, h3⟩ | ⟨-, -, h3⟩
  · have hrad : (radical (x ^ 2 * y ^ 2 * -(z ^ 2))).natDegree ≤
        (radical x).natDegree + (radical y).natDegree + z.natDegree := by
      have : x ^ 2 * y ^ 2 * -(z ^ 2) = -((x * y * z) ^ 2) := by ring
      rw [this, UniqueFactorizationDomain.radical_neg, radical_pow _ two_ne_zero]
      have hdvd : radical (x * y * z) ∣ radical x * radical y * radical z :=
        radical_mul_dvd.trans (mul_dvd_mul_right radical_mul_dvd _)
      have hne : radical x * radical y * radical z ≠ 0 :=
        mul_ne_zero (mul_ne_zero radical_ne_zero radical_ne_zero) radical_ne_zero
      refine (natDegree_le_of_dvd hdvd hne).trans ?_
      rw [natDegree_mul (mul_ne_zero radical_ne_zero radical_ne_zero) radical_ne_zero,
        natDegree_mul radical_ne_zero radical_ne_zero]
      have := natDegree_radical_le (a := z)
      omega
    rw [natDegree_neg, natDegree_pow] at h3
    omega
  · rw [derivative_neg, neg_eq_zero, derivative_eq_zero, natDegree_pow] at h3
    omega

open UniqueFactorizationMonoid in
/-- **Radical bound for pairwise coprime polynomial bricks.** Summing the radical Mason–Stothers
inequality over the three faces. (No pairwise coprime polynomial brick over `ℚ[X]` is known;
Saunderson's brick is not pairwise coprime. In other characteristics they exist: the degenerate
cuboid `(2X, X² − 1, i(X² + 1))` of `PolyCharP.isCuboid_family` is pairwise coprime, and over
`𝔽₅[X]` there is a nondegenerate pairwise coprime cuboid,
`PolyPythagoras.isNondegCuboid_coprime_five`.) -/
theorem IsPolyBrick.radical_sum_bound {a b c : ℚ[X]} (h : IsPolyBrick a b c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c) {d e f : ℚ[X]}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    d.natDegree + e.natDegree + f.natDegree + 3 ≤
      2 * ((radical a).natDegree + (radical b).natDegree + (radical c).natDegree) := by
  obtain ⟨pa, pb, pc⟩ := h.natDegree_pos
  have dd := natDegree_hyp h.ne_a h.ne_b hd
  have de := natDegree_hyp h.ne_a h.ne_c he
  have df := natDegree_hyp h.ne_b h.ne_c hf
  have h1 := natDegree_hyp_add_one_le_radical h.ne_a h.ne_b hab hd (by omega)
  have h2 := natDegree_hyp_add_one_le_radical h.ne_a h.ne_c hac he (by omega)
  have h3 := natDegree_hyp_add_one_le_radical h.ne_b h.ne_c hbc hf (by omega)
  omega

end PerfectCuboid.Poly
