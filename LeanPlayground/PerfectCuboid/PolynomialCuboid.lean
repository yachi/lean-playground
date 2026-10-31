module

public import Mathlib
public import LeanPlayground.PerfectCuboid.ConfigCuboid

/-!
# Polynomial cuboids over `ℚ[X]` (first results; general case open)

A **polynomial cuboid** (`IsPolyCuboid a b c`) is a triple of nonzero polynomials
`a, b, c ∈ ℚ[X]`, not all constant, such that `a² + b²`, `a² + c²`, `b² + c²` and
`a² + b² + c²` are squares in `ℚ[X]`: a `ℚ`-rational curve on the cuboid surface. None is known.
An integer perfect cuboid `(p, q, r)` gives the polynomial cuboid `(pX, qX, rX)`
(`IsPerfectCuboid.isPolyCuboid`), so the question contains the perfect cuboid problem; the
interesting polynomial cuboids are the non-proportional ones.

## Main results

* `sq_add_sq_eq_zero_iff`, `natDegree_sq_add_sq`, `natDegree_hyp`: no cancellation of leading
  terms, so `deg √(x² + y²) = max (deg x) (deg y)`; `IsPolyCuboid.natDegree_space_diagonal`.
* `natDegree_eq_zero_of_leg`, `IsPolyCuboid.natDegree_pos`: no edge is constant.
* `IsPolyCuboid.rat_of_proportional`, `IsPolyCuboid.exists_isPerfectCuboid_of_proportional`:
  proportional edges give a rational, hence an integer, perfect cuboid.
* `pythagorean_param`: coprime polynomial Pythagorean triples, `z ∓ y = (unit)·(square)`.
* `natDegree_hyp_add_one_le` (Mason–Stothers, `Polynomial.abc`): for coprime legs,
  `deg z + 1 ≤ deg x + deg y`.
* `quad_disc`: if `A X^{2n} + B X^n + D` (`A ≠ 0`, `n ≥ 1`) is a square then `B² = 4AD`.
* **Polynomial Korec (coprime case)**: `not_squares_of_monomial` (face-cuboid form: the face
  `b² + c²` is not used), `IsPolyCuboid.edge_ne_C_mul_X_pow`,
  `IsPolyCuboid.edge_ne_C_mul_X_sub_C_pow`: an edge coprime to the other two edges is never
  `α (X − r)^k`, `k ≥ 1`.
* **Linear edges**: `IsPolyCuboid.proportional_of_linear_edge` (`(αX, b, c)` forces
  `b = βX`, `c = γX`) and `IsPolyCuboid.exists_isPerfectCuboid_of_natDegree_eq_one'`: a polynomial
  cuboid with an edge of degree one exists if and only if an integer perfect cuboid exists.
* `IsPolyCuboid.swap_ab`, `swap_bc`, `swap_ac`, `IsPolyCuboid.comp_X_add_C`: symmetries and
  translations.

Without coprimality the monomial statement is as hard as the perfect cuboid problem itself,
because `(αX^k, βX^k, γX^k)` is a polynomial cuboid whenever `(α, β, γ)` is a rational one.
Open (not proved here): a monomial edge `α X^k`, `k ≥ 2`, **not** coprime to the other edges
forces proportionality (done only for `k = 1`, `proportional_of_linear_edge`); edges with two
distinct roots; any non-proportional polynomial cuboid. Stoll–Testa (arXiv:1009.0388v3) classify
integral curves of degree ≤ 6 on the cuboid surface; whether this excludes every non-proportional
polynomial cuboid of reduced degree ≤ 7 depends on the list of `ℚ`-rational conics, which we did
not verify.
-/
@[expose] public section

open Polynomial

namespace PerfectCuboid.Poly

/-- A polynomial cuboid over `ℚ`: nonzero edges, not all constant, all four sums squares in
`ℚ[X]`. -/
structure IsPolyCuboid (a b c : ℚ[X]) : Prop where
  ne_a : a ≠ 0
  ne_b : b ≠ 0
  ne_c : c ≠ 0
  nonconst : ¬ (a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0)
  sq_ab : IsSquare (a ^ 2 + b ^ 2)
  sq_ac : IsSquare (a ^ 2 + c ^ 2)
  sq_bc : IsSquare (b ^ 2 + c ^ 2)
  sq_abc : IsSquare (a ^ 2 + b ^ 2 + c ^ 2)

/-- Over an ordered field, `x² + y² = 0` forces `x = y = 0` in the polynomial ring. -/
theorem sq_add_sq_eq_zero_iff {x y : ℚ[X]} : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hev : ∀ r : ℚ, x.eval r = 0 ∧ y.eval r = 0 := by
      intro r
      have h' := congrArg (eval r) h
      simp only [eval_add, eval_pow, eval_zero] at h'
      have h1 : x.eval r ^ 2 = 0 := by nlinarith [sq_nonneg (x.eval r), sq_nonneg (y.eval r)]
      have h2 : y.eval r ^ 2 = 0 := by nlinarith [sq_nonneg (x.eval r), sq_nonneg (y.eval r)]
      exact ⟨pow_eq_zero_iff (two_ne_zero) |>.mp h1, pow_eq_zero_iff (two_ne_zero) |>.mp h2⟩
    exact ⟨Polynomial.funext fun r => by simp [(hev r).1],
      Polynomial.funext fun r => by simp [(hev r).2]⟩
  · rintro ⟨rfl, rfl⟩
    ring

/-- No cancellation of leading terms: `deg (x² + y²) = 2 max(deg x, deg y)`. -/
theorem natDegree_sq_add_sq {x y : ℚ[X]} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x ^ 2 + y ^ 2).natDegree = 2 * max x.natDegree y.natDegree := by
  set M := max x.natDegree y.natDegree with hM
  have key : ∀ p : ℚ[X], p ≠ 0 → p.natDegree ≤ M →
      0 ≤ (p ^ 2).coeff (2 * M) ∧ (p.natDegree = M → 0 < (p ^ 2).coeff (2 * M)) := by
    intro p hp hle
    rcases hle.lt_or_eq with hlt | heq
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_pow]; omega)]
      exact ⟨le_rfl, fun h => absurd h (ne_of_lt hlt)⟩
    · have hl : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
      have hpos : 0 < p.leadingCoeff ^ 2 := by positivity
      rw [← heq, coeff_pow_mul_natDegree]
      exact ⟨hpos.le, fun _ => hpos⟩
  have kx := key x hx (le_max_left _ _)
  have ky := key y hy (le_max_right _ _)
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_pow]; omega
    · rw [natDegree_pow]; omega
  · rw [coeff_add]
    rcases le_total x.natDegree y.natDegree with hle | hle
    · have := ky.2 (by omega)
      linarith [kx.1]
    · have := kx.2 (by omega)
      linarith [ky.1]

/-- The hypotenuse of a polynomial right triangle has degree `max (deg x) (deg y)`. -/
theorem natDegree_hyp {x y z : ℚ[X]} (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ 2 + y ^ 2 = z ^ 2) :
    z.natDegree = max x.natDegree y.natDegree := by
  have := natDegree_sq_add_sq hx hy
  rw [h, natDegree_pow] at this
  omega

/-- `C (1/2) * 2 = 1` in `ℚ[X]`. -/
theorem C_half_mul_two : C (1 / 2 : ℚ) * 2 = 1 := by
  rw [← C_1, ← map_ofNat C 2, ← C_mul]
  norm_num

/-- If `2 * p` is constant, so is `p`. -/
theorem natDegree_eq_zero_of_two_mul {p : ℚ[X]} (h : (2 * p).natDegree = 0) : p.natDegree = 0 := by
  rwa [← map_ofNat C 2, natDegree_C_mul (by norm_num)] at h

/-- A polynomial right triangle with a constant leg is constant. -/
theorem natDegree_eq_zero_of_leg {x y z : ℚ[X]} (hx : x ≠ 0) (hx0 : x.natDegree = 0)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : y.natDegree = 0 ∧ z.natDegree = 0 := by
  have hu : IsUnit (x ^ 2) := by
    have hxC := eq_C_of_natDegree_eq_zero hx0
    have hc : x.coeff 0 ≠ 0 := by
      intro h0
      rw [h0, C_0] at hxC
      exact hx hxC
    rw [hxC, ← C_pow]
    exact isUnit_C.mpr (Ne.isUnit (pow_ne_zero _ hc))
  have hprod : (z - y) * (z + y) = x ^ 2 := by linear_combination -h
  rw [← hprod] at hu
  have h1 : (z - y).natDegree = 0 := natDegree_eq_zero_of_isUnit (isUnit_of_mul_isUnit_left hu)
  have h2 : (z + y).natDegree = 0 := natDegree_eq_zero_of_isUnit (isUnit_of_mul_isUnit_right hu)
  constructor
  · apply natDegree_eq_zero_of_two_mul
    have : 2 * y = (z + y) - (z - y) := by ring
    rw [this]
    exact Nat.eq_zero_of_le_zero ((natDegree_sub_le _ _).trans (by omega))
  · apply natDegree_eq_zero_of_two_mul
    have : 2 * z = (z + y) + (z - y) := by ring
    rw [this]
    exact Nat.eq_zero_of_le_zero ((natDegree_add_le _ _).trans (by omega))

theorem eq_sq_of_isSquare {p : ℚ[X]} (h : IsSquare p) : ∃ s, p = s ^ 2 := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, by rw [hs]; ring⟩

/-- No edge of a polynomial cuboid is constant. -/
theorem IsPolyCuboid.natDegree_pos {a b c : ℚ[X]} (h : IsPolyCuboid a b c) :
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

/-- The degree pattern: the space diagonal has degree `max (deg a) (deg b) (deg c)`. -/
theorem IsPolyCuboid.natDegree_space_diagonal {a b c : ℚ[X]} (h : IsPolyCuboid a b c)
    {g : ℚ[X]} (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    g.natDegree = max a.natDegree (max b.natDegree c.natDegree) := by
  obtain ⟨d, hd⟩ := eq_sq_of_isSquare h.sq_ab
  have hdne : d ≠ 0 := by
    rintro rfl
    exact h.ne_a (sq_add_sq_eq_zero_iff.mp (by rw [hd]; ring)).1
  have h1 := natDegree_hyp h.ne_a h.ne_b hd
  have h2 := natDegree_hyp (z := g) hdne h.ne_c (by rw [← hd]; exact hg)
  rw [h2, h1, max_assoc]

/-- If `r q² = s²` in `ℚ[X]` with `q ≠ 0`, then `r` is a square in `ℚ`. -/
theorem isSquare_of_C_mul_sq {r : ℚ} {q s : ℚ[X]} (hq : q ≠ 0) (h : C r * q ^ 2 = s ^ 2) :
    IsSquare r := by
  have h' := congrArg leadingCoeff h
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow, leadingCoeff_pow] at h'
  have hlq : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  refine ⟨s.leadingCoeff / q.leadingCoeff, ?_⟩
  field_simp
  linear_combination h'

/-- Proportional edges give a rational cuboid: the constants of proportionality satisfy the
four square conditions in `ℚ`. -/
theorem IsPolyCuboid.rat_of_proportional {a b c : ℚ[X]} (h : IsPolyCuboid a b c) {α β γ : ℚ}
    {q : ℚ[X]} (ha : a = C α * q) (hb : b = C β * q) (hc : c = C γ * q) :
    IsSquare (α ^ 2 + β ^ 2) ∧ IsSquare (α ^ 2 + γ ^ 2) ∧ IsSquare (β ^ 2 + γ ^ 2) ∧
      IsSquare (α ^ 2 + β ^ 2 + γ ^ 2) := by
  have hq : q ≠ 0 := by
    rintro rfl
    exact h.ne_a (by rw [ha, mul_zero])
  obtain ⟨d, hd⟩ := eq_sq_of_isSquare h.sq_ab
  obtain ⟨e, he⟩ := eq_sq_of_isSquare h.sq_ac
  obtain ⟨f, hf⟩ := eq_sq_of_isSquare h.sq_bc
  obtain ⟨g, hg⟩ := eq_sq_of_isSquare h.sq_abc
  subst ha hb hc
  refine ⟨isSquare_of_C_mul_sq (s := d) hq ?_, isSquare_of_C_mul_sq (s := e) hq ?_,
    isSquare_of_C_mul_sq (s := f) hq ?_, isSquare_of_C_mul_sq (s := g) hq ?_⟩
  · rw [← hd]; simp only [map_add, map_pow]; ring
  · rw [← he]; simp only [map_add, map_pow]; ring
  · rw [← hf]; simp only [map_add, map_pow]; ring
  · rw [← hg]; simp only [map_add, map_pow]; ring

/-- For a primitive polynomial Pythagorean triple, `z - y` and `z + y` are coprime. -/
theorem isCoprime_sub_add {x y z : ℚ[X]} (hxy : IsCoprime x y) (h : x ^ 2 + y ^ 2 = z ^ 2) :
    IsCoprime (z - y) (z + y) := by
  have hyz : IsCoprime y z := by
    have h1 : IsCoprime y (x ^ 2) := hxy.symm.pow_right
    have h2 : IsCoprime y (z ^ 2) := by
      have := h1.add_mul_left_right y
      rwa [show x ^ 2 + y * y = z ^ 2 by linear_combination h] at this
    exact (IsCoprime.pow_right_iff two_pos).mp h2
  obtain ⟨u, v, huv⟩ := hyz
  refine ⟨C (1 / 2) * (v - u), C (1 / 2) * (u + v), ?_⟩
  linear_combination (u * y + v * z) * C_half_mul_two + huv

/-- Polynomial Pythagorean parametrization for coprime legs. -/
theorem pythagorean_param {x y z : ℚ[X]} (_hx : x ≠ 0) (_hy : y ≠ 0) (hxy : IsCoprime x y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) :
    ∃ (m n : ℚ[X]) (u v : ℚ), u ≠ 0 ∧ v ≠ 0 ∧ z - y = C u * m ^ 2 ∧ z + y = C v * n ^ 2 ∧
      x ^ 2 = C (u * v) * (m * n) ^ 2 := by
  have hcop := isCoprime_sub_add hxy h
  have hprod : (z - y) * (z + y) = x ^ 2 := by linear_combination -h
  obtain ⟨m, μ, hμ⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  obtain ⟨n, ν, hν⟩ := exists_associated_pow_of_mul_eq_pow' hcop.symm
    (by rw [mul_comm]; exact hprod)
  obtain ⟨u, hu, hCu⟩ := Polynomial.isUnit_iff.mp μ.isUnit
  obtain ⟨v, hv, hCv⟩ := Polynomial.isUnit_iff.mp ν.isUnit
  refine ⟨m, n, u, v, hu.ne_zero, hv.ne_zero, ?_, ?_, ?_⟩
  · rw [← hμ, ← hCu, mul_comm]
  · rw [← hν, ← hCv, mul_comm]
  · rw [← hprod, ← hμ, ← hν, ← hCu, ← hCv, C_mul]
    ring

/-! ### Polynomial Korec: a monomial edge coprime to the other two -/

/-- **Discriminant lemma.** If `A Y² + B Y + D` with `Y = X ^ n`, `n ≥ 1`, `A ≠ 0`, is a square in
`ℚ[X]`, then its discriminant vanishes: `B² = 4AD`. -/
theorem quad_disc {F : ℚ[X]} {A B D : ℚ} {n : ℕ} (hn : 0 < n) (hA : A ≠ 0)
    (h : F ^ 2 = C A * X ^ (2 * n) + C B * X ^ n + C D) : B ^ 2 = 4 * A * D := by
  have hdeg : (C A * X ^ (2 * n) + C B * X ^ n + C D).natDegree = 2 * n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
      · exact (natDegree_C_mul_X_pow_le _ _)
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · simp
    · simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
      simp [show 2 * n ≠ n by omega, show 2 * n ≠ 0 by omega, hA]
  have hcoeff : (C A * X ^ (2 * n) + C B * X ^ n + C D).coeff (2 * n) = A := by
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
    simp [show 2 * n ≠ n by omega, show 2 * n ≠ 0 by omega]
  have hF : F.natDegree = n := by
    have := congrArg natDegree h
    rw [natDegree_pow, hdeg] at this
    omega
  have hP : F.leadingCoeff ^ 2 = A := by
    rw [← hcoeff, ← h, ← hF, coeff_pow_mul_natDegree]
  by_contra hne
  have hδ : B ^ 2 - 4 * A * D ≠ 0 := sub_ne_zero.mpr hne
  set s : ℚ[X] := C (2 * A) * X ^ n + C B with hs
  set t : ℚ[X] := C (2 * F.leadingCoeff) * F with ht
  have hPC : C F.leadingCoeff ^ 2 = C A := by rw [← C_pow, hP]
  have hst : (s - t) * (s + t) = C (B ^ 2 - 4 * A * D) := by
    rw [hs, ht]
    simp only [map_mul, map_sub, map_pow, map_ofNat]
    linear_combination (-4 * C A) * h - 4 * F ^ 2 * hPC
  have hne1 : s - t ≠ 0 := by
    intro h0; rw [h0, zero_mul, eq_comm, C_eq_zero] at hst; exact hδ hst
  have hne2 : s + t ≠ 0 := by
    intro h0; rw [h0, mul_zero, eq_comm, C_eq_zero] at hst; exact hδ hst
  have hsum := natDegree_mul hne1 hne2
  rw [hst, natDegree_C] at hsum
  have h2s : (2 * s).natDegree = 0 := by
    have : 2 * s = (s - t) + (s + t) := by ring
    rw [this]
    exact Nat.eq_zero_of_le_zero ((natDegree_add_le _ _).trans (by omega))
  have hs0 := natDegree_eq_zero_of_two_mul h2s
  have hsdeg : s.natDegree = n := by
    rw [hs]
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · refine (natDegree_add_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _) ?_)
      simp
    · simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
      simp [show n ≠ 0 by omega, hA]
  omega

/-- In a coprime factorization `p q = c X ^ m` one of the two factors is a unit. -/
theorem isUnit_or_isUnit_of_mul_eq_C_mul_X_pow {p q : ℚ[X]} {c : ℚ} {m : ℕ} (hc : c ≠ 0)
    (hpq : IsCoprime p q) (h : p * q = C c * X ^ m) : IsUnit p ∨ IsUnit q := by
  have hcu : IsUnit (C c) := isUnit_C.mpr (Ne.isUnit hc)
  have key : ∀ p q : ℚ[X], p * q = C c * X ^ m → ¬ X ∣ p → IsUnit p := by
    intro p q h hX
    have h1 : IsCoprime (X ^ m) p :=
      ((irreducible_X.coprime_iff_not_dvd).mpr hX).pow_left
    have h2 : p ∣ X ^ m * C c := ⟨q, by rw [h, mul_comm]⟩
    exact isUnit_of_dvd_unit (h1.symm.dvd_of_dvd_mul_left h2) hcu
  by_cases hp : X ∣ p
  · by_cases hq : X ∣ q
    · exact absurd (hpq.isUnit_of_dvd' hp hq) (not_isUnit_X)
    · exact Or.inr (key q p (by rw [mul_comm]; exact h) hq)
  · exact Or.inl (key p q h hp)

/-- A face `(α X^k, b, d)` with `b` coprime to the monomial leg: `2b = v X^{2k} − u` with
`u v = α²`. -/
theorem monomial_leg {α : ℚ} {k : ℕ} {b d : ℚ[X]} (hα : α ≠ 0)
    (hab : IsCoprime (C α * X ^ k) b) (h : (C α * X ^ k) ^ 2 + b ^ 2 = d ^ 2) :
    ∃ u v : ℚ, u * v = α ^ 2 ∧ 2 * b = C v * X ^ (2 * k) - C u := by
  have hcop := isCoprime_sub_add hab h
  have hprod : (d - b) * (d + b) = C (α ^ 2) * X ^ (2 * k) := by
    rw [C_pow]; linear_combination -h
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero _ hα
  rcases isUnit_or_isUnit_of_mul_eq_C_mul_X_pow hα2 hcop hprod with hu | hu
  · obtain ⟨u, hu0, hCu⟩ := Polynomial.isUnit_iff.mp hu
    have hu0 := hu0.ne_zero
    have hdb : d + b = C (u⁻¹ * α ^ 2) * X ^ (2 * k) := by
      have : d + b = C u⁻¹ * ((d - b) * (d + b)) := by
        rw [← hCu, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hu0, C_1, one_mul]
      rw [this, hprod, C_mul, mul_assoc]
    refine ⟨u, u⁻¹ * α ^ 2, by field_simp, ?_⟩
    rw [← hdb, hCu]
    ring
  · obtain ⟨w, hw0, hCw⟩ := Polynomial.isUnit_iff.mp hu
    have hw0 := hw0.ne_zero
    have hdb : d - b = C (w⁻¹ * α ^ 2) * X ^ (2 * k) := by
      have : d - b = C w⁻¹ * ((d - b) * (d + b)) := by
        rw [← hCw, mul_comm (d - b), ← mul_assoc, ← C_mul, inv_mul_cancel₀ hw0, C_1, one_mul]
      rw [this, hprod, C_mul, mul_assoc]
    refine ⟨-w, -(w⁻¹ * α ^ 2), by field_simp, ?_⟩
    simp only [map_neg]
    linear_combination -hCw - hdb

/-- **Polynomial Korec (coprime case), face-cuboid form.** If `α ≠ 0`, `k ≥ 1`, and `b, c` are
coprime to `α X^k`, then `(α X^k)² + b²`, `(α X^k)² + c²`, `(α X^k)² + b² + c²` cannot all be
squares in `ℚ[X]`. (The face `b² + c²` is not needed.) -/
theorem not_squares_of_monomial {α : ℚ} {k : ℕ} {b c : ℚ[X]} (hα : α ≠ 0) (hk : 0 < k)
    (hb : IsCoprime (C α * X ^ k) b) (hc : IsCoprime (C α * X ^ k) c)
    (hab : IsSquare ((C α * X ^ k) ^ 2 + b ^ 2)) (hac : IsSquare ((C α * X ^ k) ^ 2 + c ^ 2))
    (habc : IsSquare ((C α * X ^ k) ^ 2 + b ^ 2 + c ^ 2)) : False := by
  obtain ⟨d, hd⟩ := eq_sq_of_isSquare hab
  obtain ⟨e, he⟩ := eq_sq_of_isSquare hac
  obtain ⟨g, hg⟩ := eq_sq_of_isSquare habc
  obtain ⟨u, v, huv, hb2⟩ := monomial_leg hα hb hd
  obtain ⟨u', v', huv', hc2⟩ := monomial_leg hα hc he
  have hv : v ≠ 0 := by
    rintro rfl; simp at huv; exact hα (pow_eq_zero_iff two_ne_zero |>.mp huv.symm)
  have hu : u ≠ 0 := by
    rintro rfl; simp at huv; exact hα (pow_eq_zero_iff two_ne_zero |>.mp huv.symm)
  have hCuv : C u * C v = C α ^ 2 := by rw [← C_mul, huv, C_pow]
  have hCuv' : C u' * C v' = C α ^ 2 := by rw [← C_mul, huv', C_pow]
  have key : (2 * g) ^ 2 = C (v ^ 2 + v' ^ 2) * X ^ (2 * (2 * k)) + C 0 * X ^ (2 * k) +
      C (u ^ 2 + u' ^ 2) := by
    simp only [map_add, map_pow, map_zero, zero_mul, add_zero]
    linear_combination (-4) * hg + (2 * b + (C v * X ^ (2 * k) - C u)) * hb2 +
      (2 * c + (C v' * X ^ (2 * k) - C u')) * hc2 + (-2 * X ^ (2 * k)) * hCuv +
      (-2 * X ^ (2 * k)) * hCuv'
  have hA : v ^ 2 + v' ^ 2 ≠ 0 := by positivity
  have := quad_disc (by omega) hA key
  have hpos : 0 < 4 * (v ^ 2 + v' ^ 2) * (u ^ 2 + u' ^ 2) := by positivity
  linarith

/-! ### Symmetries and translations -/

theorem IsPolyCuboid.swap_ab {a b c : ℚ[X]} (h : IsPolyCuboid a b c) : IsPolyCuboid b a c where
  ne_a := h.ne_b
  ne_b := h.ne_a
  ne_c := h.ne_c
  nonconst := fun ⟨h1, h2, h3⟩ => h.nonconst ⟨h2, h1, h3⟩
  sq_ab := by convert h.sq_ab using 1; ring
  sq_ac := h.sq_bc
  sq_bc := h.sq_ac
  sq_abc := by convert h.sq_abc using 1; ring

theorem IsPolyCuboid.swap_bc {a b c : ℚ[X]} (h : IsPolyCuboid a b c) : IsPolyCuboid a c b where
  ne_a := h.ne_a
  ne_b := h.ne_c
  ne_c := h.ne_b
  nonconst := fun ⟨h1, h2, h3⟩ => h.nonconst ⟨h1, h3, h2⟩
  sq_ab := h.sq_ac
  sq_ac := h.sq_ab
  sq_bc := by convert h.sq_bc using 1; ring
  sq_abc := by convert h.sq_abc using 1; ring

theorem IsPolyCuboid.swap_ac {a b c : ℚ[X]} (h : IsPolyCuboid a b c) : IsPolyCuboid c b a where
  ne_a := h.ne_c
  ne_b := h.ne_b
  ne_c := h.ne_a
  nonconst := fun ⟨h1, h2, h3⟩ => h.nonconst ⟨h3, h2, h1⟩
  sq_ab := by convert h.sq_bc using 1; ring
  sq_ac := by convert h.sq_ac using 1; ring
  sq_bc := by convert h.sq_ab using 1; ring
  sq_abc := by convert h.sq_abc using 1; ring

theorem comp_X_add_C_comp_X_sub_C (p : ℚ[X]) (r : ℚ) :
    (p.comp (X + C r)).comp (X - C r) = p := by
  rw [comp_assoc]
  simp

/-- Translation `X ↦ X + r` maps polynomial cuboids to polynomial cuboids. -/
theorem IsPolyCuboid.comp_X_add_C {a b c : ℚ[X]} (h : IsPolyCuboid a b c) (r : ℚ) :
    IsPolyCuboid (a.comp (X + C r)) (b.comp (X + C r)) (c.comp (X + C r)) := by
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
  refine ⟨hne a h.ne_a, hne b h.ne_b, hne c h.ne_c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdeg, hdeg, hdeg]; exact h.nonconst
  · simpa [add_comp, pow_comp] using hsq _ h.sq_ab
  · simpa [add_comp, pow_comp] using hsq _ h.sq_ac
  · simpa [add_comp, pow_comp] using hsq _ h.sq_bc
  · simpa [add_comp, pow_comp] using hsq _ h.sq_abc

/-- **Polynomial Korec (coprime case).** An edge of a polynomial cuboid that is coprime to the
other two edges is not of the form `α X^k` with `k ≥ 1`. -/
theorem IsPolyCuboid.edge_ne_C_mul_X_pow {a b c : ℚ[X]} (h : IsPolyCuboid a b c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) {α : ℚ} {k : ℕ} (hα : α ≠ 0) (hk : 0 < k) :
    a ≠ C α * X ^ k := by
  rintro rfl
  exact not_squares_of_monomial hα hk hab hac h.sq_ab h.sq_ac h.sq_abc

/-- **Polynomial Korec (coprime case), translated form.** An edge of a polynomial cuboid that is
coprime to the other two edges is not of the form `α (X - r)^k` with `k ≥ 1`. -/
theorem IsPolyCuboid.edge_ne_C_mul_X_sub_C_pow {a b c : ℚ[X]} (h : IsPolyCuboid a b c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) {α r : ℚ} {k : ℕ} (hα : α ≠ 0) (hk : 0 < k) :
    a ≠ C α * (X - C r) ^ k := by
  intro ha
  have h' := h.comp_X_add_C r
  have hφa : a.comp (X + C r) = C α * X ^ k := by
    rw [ha]; simp
  rw [hφa] at h'
  refine h'.edge_ne_C_mul_X_pow ?_ ?_ hα hk rfl
  · rw [← hφa]; simpa [coe_compRingHom_apply] using hab.map (compRingHom (X + C r))
  · rw [← hφa]; simpa [coe_compRingHom_apply] using hac.map (compRingHom (X + C r))

/-! ### Proportional cuboids and linear edges -/

/-- A polynomial cuboid with proportional edges gives an integer perfect cuboid. -/
theorem IsPolyCuboid.exists_isPerfectCuboid_of_proportional {a b c : ℚ[X]}
    (h : IsPolyCuboid a b c) {α β γ : ℚ} {q : ℚ[X]} (ha : a = C α * q) (hb : b = C β * q)
    (hc : c = C γ * q) : ∃ A B C : ℕ, IsPerfectCuboid A B C := by
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩, ⟨g, hg⟩⟩ := h.rat_of_proportional ha hb hc
  have hα : α ≠ 0 := by rintro rfl; exact h.ne_a (by rw [ha]; simp)
  have hβ : β ≠ 0 := by rintro rfl; exact h.ne_b (by rw [hb]; simp)
  have hγ : γ ≠ 0 := by rintro rfl; exact h.ne_c (by rw [hc]; simp)
  have p1 : 0 < α ^ 2 + β ^ 2 := by positivity
  have p2 : 0 < α ^ 2 + γ ^ 2 := by positivity
  have p3 : 0 < β ^ 2 + γ ^ 2 := by positivity
  have p4 : 0 < α ^ 2 + β ^ 2 + γ ^ 2 := by positivity
  have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero] at hd; linarith
  have he0 : e ≠ 0 := by rintro rfl; rw [mul_zero] at he; linarith
  have hf0 : f ≠ 0 := by rintro rfl; rw [mul_zero] at hf; linarith
  have hg0 : g ≠ 0 := by rintro rfl; rw [mul_zero] at hg; linarith
  exact CongruentRank.IsRatCuboid.exists_isPerfectCuboid (a := |α|) (b := |β|) (c := |γ|)
    (d := |d|) (e := |e|) (f := |f|) (g := |g|)
    { pos_a := abs_pos.mpr hα
      pos_b := abs_pos.mpr hβ
      pos_c := abs_pos.mpr hγ
      pos_d := abs_pos.mpr hd0
      pos_e := abs_pos.mpr he0
      pos_f := abs_pos.mpr hf0
      pos_g := abs_pos.mpr hg0
      hd := by simp only [sq_abs]; rw [hd]; ring
      he := by simp only [sq_abs]; rw [he]; ring
      hf := by simp only [sq_abs]; rw [hf]; ring
      hg := by simp only [sq_abs]; rw [hg]; ring }

/-- Conversely, an integer perfect cuboid `(p, q, r)` gives the polynomial cuboid
`(p X, q X, r X)`. Hence polynomial cuboids exist iff perfect cuboids do. -/
theorem _root_.PerfectCuboid.IsPerfectCuboid.isPolyCuboid {p q r : ℕ}
    (h : IsPerfectCuboid p q r) :
    IsPolyCuboid (C (p : ℚ) * X) (C (q : ℚ) * X) (C (r : ℚ) * X) := by
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
    ?_, sq2 q r h.sq_bc, ?_⟩
  · rintro ⟨h1, -, -⟩
    rw [natDegree_C_mul_X _ hp] at h1
    exact one_ne_zero h1
  · have := sq2 r p h.sq_ca
    convert this using 1; ring
  · obtain ⟨s, hs⟩ := h.sq_abc
    have hs' : (p : ℚ) ^ 2 + (q : ℚ) ^ 2 + (r : ℚ) ^ 2 = (s : ℚ) * s := by exact_mod_cast hs
    refine ⟨C (s : ℚ) * X, ?_⟩
    have : (C (p : ℚ) * X) ^ 2 + (C (q : ℚ) * X) ^ 2 + (C (r : ℚ) * X) ^ 2 =
        C ((p : ℚ) ^ 2 + (q : ℚ) ^ 2 + (r : ℚ) ^ 2) * X ^ 2 := by
      simp only [map_add, map_pow]; ring
    rw [this, hs', map_mul]; ring

/-- In a face `(α X, b, d)` with `X ∣ b`, the leg `b` is `β X` for a constant `β`. -/
theorem linear_leg_of_X_dvd {α : ℚ} {b d : ℚ[X]} (hα : α ≠ 0)
    (h : (C α * X) ^ 2 + b ^ 2 = d ^ 2) (hX : X ∣ b) : ∃ β : ℚ, b = C β * X := by
  obtain ⟨b1, rfl⟩ := hX
  have hXd : X ∣ d := by
    apply prime_X.dvd_of_dvd_pow (n := 2)
    rw [← h]
    exact ⟨(C α) ^ 2 * X + b1 ^ 2 * X, by ring⟩
  obtain ⟨d1, rfl⟩ := hXd
  have h1 : (C α) ^ 2 + b1 ^ 2 = d1 ^ 2 := by
    have : X ^ 2 * ((C α) ^ 2 + b1 ^ 2) = X ^ 2 * d1 ^ 2 := by linear_combination h
    exact mul_left_cancel₀ (pow_ne_zero 2 X_ne_zero) this
  have hCα : C α ≠ 0 := C_ne_zero.mpr hα
  have h0 := (natDegree_eq_zero_of_leg hCα (natDegree_C α) h1).1
  have hb1 := eq_C_of_natDegree_eq_zero h0
  refine ⟨b1.coeff 0, ?_⟩
  rw [mul_comm X b1]
  exact congrArg (· * X) hb1

theorem isCoprime_C_mul_X_of_not_dvd {α : ℚ} {b : ℚ[X]} (hα : α ≠ 0) (hX : ¬ X ∣ b) :
    IsCoprime (C α * X ^ 1) b := by
  have hC : IsCoprime (C α) b := ⟨C α⁻¹, 0, by rw [← C_mul, inv_mul_cancel₀ hα, C_1]; ring⟩
  rw [pow_one]
  exact hC.mul_left ((irreducible_X.coprime_iff_not_dvd).mpr hX)

/-- The mixed case for a linear edge: `α X`, `β X` (`β ≠ 0`) and `c` coprime to `X` never give
squares `(αX)² + c²` and `(αX)² + (βX)² + c²`. -/
theorem not_squares_linear_mixed {α β : ℚ} {c : ℚ[X]} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hc : IsCoprime (C α * X ^ 1) c) (hac : IsSquare ((C α * X) ^ 2 + c ^ 2))
    (habc : IsSquare ((C α * X) ^ 2 + (C β * X) ^ 2 + c ^ 2)) : False := by
  obtain ⟨e, he⟩ := eq_sq_of_isSquare hac
  obtain ⟨g, hg⟩ := eq_sq_of_isSquare habc
  obtain ⟨u, v, huv, hc2⟩ := monomial_leg hα hc (by rw [pow_one]; exact he)
  have hv : v ≠ 0 := by
    rintro rfl; simp at huv; exact hα (pow_eq_zero_iff two_ne_zero |>.mp huv.symm)
  have hCuv : C u * C v = C α ^ 2 := by rw [← C_mul, huv, C_pow]
  have key : (2 * g) ^ 2 = C (v ^ 2) * X ^ (2 * 2) + C (2 * α ^ 2 + 4 * β ^ 2) * X ^ 2 +
      C (u ^ 2) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    linear_combination (-4) * hg + (2 * c + (C v * X ^ (2 * 1) - C u)) * hc2 +
      (-2 * X ^ 2) * hCuv
  have hd := quad_disc (by norm_num) (pow_ne_zero 2 hv) key
  have h1 : (u * v) ^ 2 = (α ^ 2) ^ 2 := by rw [huv]
  have h2 : β ^ 2 * (α ^ 2 + β ^ 2) = 0 := by linear_combination (hd + 4 * h1) / 16
  have h3 : 0 < β ^ 2 * (α ^ 2 + β ^ 2) := by positivity
  linarith

/-- **Linear edge forces proportional edges.** If `(α X, b, c)` is a polynomial cuboid, then
`b = β X` and `c = γ X` for constants `β, γ`. -/
theorem IsPolyCuboid.proportional_of_linear_edge {α : ℚ} {b c : ℚ[X]}
    (h : IsPolyCuboid (C α * X) b c) : ∃ β γ : ℚ, b = C β * X ∧ c = C γ * X := by
  have hα : α ≠ 0 := by rintro rfl; exact h.ne_a (by simp)
  obtain ⟨d, hd⟩ := eq_sq_of_isSquare h.sq_ab
  obtain ⟨e, he⟩ := eq_sq_of_isSquare h.sq_ac
  by_cases hb : X ∣ b <;> by_cases hc : X ∣ c
  · obtain ⟨β, hβ⟩ := linear_leg_of_X_dvd hα hd hb
    obtain ⟨γ, hγ⟩ := linear_leg_of_X_dvd hα he hc
    exact ⟨β, γ, hβ, hγ⟩
  · exfalso
    obtain ⟨β, rfl⟩ := linear_leg_of_X_dvd hα hd hb
    have hβ : β ≠ 0 := by rintro rfl; exact h.ne_b (by simp)
    exact not_squares_linear_mixed hα hβ (isCoprime_C_mul_X_of_not_dvd hα hc) h.sq_ac h.sq_abc
  · exfalso
    obtain ⟨γ, rfl⟩ := linear_leg_of_X_dvd hα he hc
    have hγ : γ ≠ 0 := by rintro rfl; exact h.ne_c (by simp)
    exact not_squares_linear_mixed hα hγ (isCoprime_C_mul_X_of_not_dvd hα hb) h.sq_ab
      (by convert h.sq_abc using 1; ring)
  · exfalso
    have hab := isCoprime_C_mul_X_of_not_dvd hα hb
    have hac := isCoprime_C_mul_X_of_not_dvd hα hc
    rw [pow_one] at hab hac
    exact h.edge_ne_C_mul_X_pow hab hac hα one_pos (by rw [pow_one])

/-- A polynomial of degree one becomes `α X` after a translation. -/
theorem exists_comp_eq_C_mul_X {a : ℚ[X]} (ha : a.natDegree = 1) :
    ∃ α r : ℚ, a.comp (X + C r) = C α * X := by
  have hne : a ≠ 0 := by rintro rfl; simp at ha
  have ha1 : a.coeff 1 ≠ 0 := by
    have := leadingCoeff_ne_zero.mpr hne
    rwa [leadingCoeff, ha] at this
  refine ⟨a.coeff 1, -(a.coeff 0) / a.coeff 1, ?_⟩
  have hexp := eq_X_add_C_of_natDegree_le_one ha.le
  have key : a.coeff 1 * (-(a.coeff 0) / a.coeff 1) + a.coeff 0 = 0 := by
    field_simp; ring
  calc a.comp (X + C (-(a.coeff 0) / a.coeff 1))
      = (C (a.coeff 1) * X + C (a.coeff 0)).comp (X + C (-(a.coeff 0) / a.coeff 1)) := by
        rw [← hexp]
    _ = C (a.coeff 1) * X + C (a.coeff 1 * (-(a.coeff 0) / a.coeff 1) + a.coeff 0) := by
        simp only [add_comp, mul_comp, C_comp, X_comp, map_add, map_mul]; ring
    _ = C (a.coeff 1) * X := by rw [key, C_0, add_zero]

/-- **A polynomial cuboid with an edge of degree one exists only if an integer perfect cuboid
exists.** (With `IsPerfectCuboid.isPolyCuboid` this is an equivalence.) -/
theorem IsPolyCuboid.exists_isPerfectCuboid_of_natDegree_eq_one {a b c : ℚ[X]}
    (h : IsPolyCuboid a b c) (ha : a.natDegree = 1) : ∃ A B C : ℕ, IsPerfectCuboid A B C := by
  obtain ⟨α, r, hr⟩ := exists_comp_eq_C_mul_X ha
  have h' := h.comp_X_add_C r
  rw [hr] at h'
  obtain ⟨β, γ, hb, hc⟩ := h'.proportional_of_linear_edge
  exact h'.exists_isPerfectCuboid_of_proportional rfl hb hc

/-- Some edge of a polynomial cuboid has degree one only if an integer perfect cuboid exists. -/
theorem IsPolyCuboid.exists_isPerfectCuboid_of_natDegree_eq_one' {a b c : ℚ[X]}
    (h : IsPolyCuboid a b c) (h1 : a.natDegree = 1 ∨ b.natDegree = 1 ∨ c.natDegree = 1) :
    ∃ A B C : ℕ, IsPerfectCuboid A B C := by
  rcases h1 with h1 | h1 | h1
  · exact h.exists_isPerfectCuboid_of_natDegree_eq_one h1
  · exact h.swap_ab.exists_isPerfectCuboid_of_natDegree_eq_one h1
  · exact h.swap_ac.exists_isPerfectCuboid_of_natDegree_eq_one h1

/-! ### Mason–Stothers -/

open UniqueFactorizationMonoid in
/-- **Mason–Stothers for polynomial Pythagorean triples.** If `x² + y² = z²` with `x, y` coprime
and `z` non-constant, then `deg z + 1 ≤ deg x + deg y`; in particular both legs are
non-constant. (First use of `Polynomial.abc` in the repository.) -/
theorem natDegree_hyp_add_one_le {x y z : ℚ[X]} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : IsCoprime x y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) (hz : 0 < z.natDegree) :
    z.natDegree + 1 ≤ x.natDegree + y.natDegree := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hsum : x ^ 2 + y ^ 2 + (-(z ^ 2)) = 0 := by rw [h]; ring
  rcases Polynomial.abc (pow_ne_zero 2 hx) (pow_ne_zero 2 hy) (neg_ne_zero.mpr (pow_ne_zero 2 hz0))
    (hxy.pow) hsum with ⟨-, -, h3⟩ | ⟨-, -, h3⟩
  · have hrad : (radical (x ^ 2 * y ^ 2 * -(z ^ 2))).natDegree ≤
        x.natDegree + y.natDegree + z.natDegree := by
      have : x ^ 2 * y ^ 2 * -(z ^ 2) = -((x * y * z) ^ 2) := by ring
      rw [this, UniqueFactorizationDomain.radical_neg, radical_pow _ two_ne_zero]
      refine natDegree_radical_le.trans ?_
      rw [natDegree_mul (mul_ne_zero hx hy) hz0, natDegree_mul hx hy]
    rw [natDegree_neg, natDegree_pow] at h3
    omega
  · rw [derivative_neg, neg_eq_zero, derivative_eq_zero, natDegree_pow] at h3
    omega

end PerfectCuboid.Poly
