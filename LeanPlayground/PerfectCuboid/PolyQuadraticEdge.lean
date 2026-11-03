module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolyCharP
public import LeanPlayground.PerfectCuboid.PolyNegOne
public import LeanPlayground.PerfectCuboid.PolyGenusOne
public import LeanPlayground.PerfectCuboid.PolynomialCuboid

/-! # An edge of degree two forces proportionality (round 18, brief 4)

* **Headline** (`IsCuboid.proportional_of_natDegree_eq_two`,
  `IsCuboid.proportional_of_natDegree_le_two`):
  if `¬ IsSquare (-1 : K)` and `2 ≠ 0`, a cuboid over `K[X]` with an edge of degree `≤ 2` is
  proportional (degrees 0, 1 are `PolyNegOne`). Corollaries: over `ℚ[X]` such a polynomial cuboid
  gives an integer perfect cuboid (`IsPolyCuboid.exists_isPerfectCuboid_of_natDegree_le_two`), so
  one with an edge of degree `≤ 2` exists iff a perfect cuboid does; every edge of every cuboid over
  `𝔽₃[X]`, `𝔽₇[X]`, `𝔽₁₁[X]`, `𝔽₁₉[X]` has degree `≥ 3` (`no_cuboid_natDegree_le_two_three`, …,
  via `IsCuboid.three_le_natDegree_all`).
* **Stronger, characteristic-free form** (`exists_parallel_of_natDegree_eq_two`): over *any* field
  with `2 ≠ 0`, in a cuboid with `deg a = 2` one of `b`, `c`, `f` (`f² = b² + c²`) is a constant
  multiple of `a`; hence (`IsNondegCuboid.proportional_of_natDegree_eq_two`) a **nondegenerate**
  cuboid with an edge of degree 2 is proportional over any field with `2 ≠ 0` (the case `f ∥ a` is
  `IsNondegCuboid.proportional_of_opp_diag_eq_edge`). `¬ IsSquare (-1)` is used only to get
  nondegeneracy (`IsCuboid.isNondegCuboid`). The degenerate `(X² − 1, 2X, i(X² + 1))` (`g = 0`,
  `f = i a`) shows the nondegeneracy hypothesis is needed; the char-`p` non-proportional cuboids
  (Frobenius, `𝔽₅` coprime, `𝔽₇`) all have edges of degree `≥ 5`, consistent with this.

## Method (uniform, no 28-pair case analysis)

For a face `a² + x² = y²` put `p = y − x`, `q = y + x`: `p q = a²`, `2x = q − p` and
`(2x)² + 2a² = p² + q²` (`face_identity`). Since `a` is a leg of the three faces `(a, b, d)`,
`(a, c, e)`, `(a, f, g)` and `b² + c² = f²`, the three "types" satisfy
`Σ_{b,c} ((2x)² + 2a²) − ((2f)² + 2a²) = 2a²`; a linear functional `ℓ` killing the three terms
kills `a²` (`functional_key`). The divisor `p` of `a²` is a unit times a monomial in the prime
factors of `a`; the middle divisor (`p ∼ a`) is exactly the case `x ∥ a`.
* `a = α X²` (`double_parallel`): `ℓ` = coefficient of `X⁴`.
* `a` irreducible (`irr_parallel`): `p ∈ {1, a, a²}`; `ℓ(P) = lc(a)⁴ P₄ − (a⁴)₄ P₈` kills `1`, `a⁴`.
* `a = κ X (X − 1)` (`split_parallel`): `p ∼ Xⁱ (X − 1)ʲ`,
  `(2x)² + 2a² ∈ span(B i j, B (2−i) (2−j))`
  with `B i j = X^{2i}(X − 1)^{2j}`. The nine `B i j` satisfy one relation, which involves `B 1 1`,
  so no single functional works; instead four integer functionals `ell00, ell01, ell02, ell10`
  (coordinates in the basis without `B 1 1`, verified coefficientwise in Lean) show that each of the
  four classes `{(i,j),(2−i,2−j)} ≠ {(1,1)}` must be hit by one of `b, c, f`: impossible for three
  elements (`split_class_hit`, `omega`).
* General `a` of degree 2 (`irreducible_or_split`) is reduced to these by `X ↦ λ X + r`
  (`isCuboid_comp_linear`, `proportional_comp_linear_iff`, `parallel_of_comp`); scaling lemmas
  `isCuboid_C_mul`, `proportional_C_mul_iff` are included for completeness.

Not done: the brief's explicit partner list `partner_shape` (S0–S6) is replaced by the uniform
divisor description in `split_partner`; degree 3 is not attempted. Over `ℂ` the statement is
covered by Stoll–Testa's classification of low-degree curves on the cuboid surface; the Lean proof
and the version over arbitrary fields with `2 ≠ 0` (nondegenerate) / with `−1 ∉ K²` are new here.
-/

@[expose] public section

open Polynomial

namespace PerfectCuboid.PolyQuadraticEdge

variable {K : Type*} [Field K]

open PolyCharP

/-! ## Linear substitutions and scaling -/

theorem comp_linear_comp_inv (p : K[X]) {lam : K} (hlam : lam ≠ 0) (r : K) :
    (p.comp (C lam * X + C r)).comp (C lam⁻¹ * (X - C r)) = p := by
  have h : (C lam * X + C r).comp (C lam⁻¹ * (X - C r)) = X := by
    simp only [add_comp, mul_comp, C_comp, X_comp]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hlam, C_1, one_mul]
    ring
  rw [comp_assoc, h, comp_X]

/-- Linear substitution `X ↦ λ X + r` (`λ ≠ 0`) preserves cuboids. -/
theorem isCuboid_comp_linear {a b c : K[X]} (h : IsCuboid a b c) {lam r : K} (hlam : lam ≠ 0) :
    IsCuboid (a.comp (C lam * X + C r)) (b.comp (C lam * X + C r))
      (c.comp (C lam * X + C r)) := by
  have hne : ∀ p : K[X], p ≠ 0 → p.comp (C lam * X + C r) ≠ 0 := by
    intro p hp h0
    apply hp
    rw [← comp_linear_comp_inv p hlam r, h0, zero_comp]
  have hsq : ∀ p : K[X], IsSquare p → IsSquare (p.comp (C lam * X + C r)) := by
    intro p hp
    simpa [coe_compRingHom_apply] using hp.map (compRingHom (C lam * X + C r))
  refine ⟨hne a h.ne_a, hne b h.ne_b, hne c h.ne_c, ?_, ?_, ?_, ?_⟩
  · simpa [add_comp, pow_comp] using hsq _ h.sq_ab
  · simpa [add_comp, pow_comp] using hsq _ h.sq_ac
  · simpa [add_comp, pow_comp] using hsq _ h.sq_bc
  · simpa [add_comp, pow_comp] using hsq _ h.sq_abc

theorem proportional_comp {a b c : K[X]} (h : Proportional a b c) (q : K[X]) :
    Proportional (a.comp q) (b.comp q) (c.comp q) := by
  obtain ⟨p, α, β, γ, ha, hb, hc⟩ := h
  exact ⟨p.comp q, α, β, γ, by rw [ha, mul_comp, C_comp], by rw [hb, mul_comp, C_comp],
    by rw [hc, mul_comp, C_comp]⟩

theorem proportional_comp_linear_iff {a b c : K[X]} {lam r : K} (hlam : lam ≠ 0) :
    Proportional (a.comp (C lam * X + C r)) (b.comp (C lam * X + C r))
      (c.comp (C lam * X + C r)) ↔ Proportional a b c := by
  constructor
  · intro h
    have := proportional_comp h (C lam⁻¹ * (X - C r))
    simpa only [comp_linear_comp_inv _ hlam] using this
  · intro h
    exact proportional_comp h _

/-- Scaling a cuboid by a nonzero constant. -/
theorem isCuboid_C_mul {a b c : K[X]} (h : IsCuboid a b c) {κ : K} (hκ : κ ≠ 0) :
    IsCuboid (C κ * a) (C κ * b) (C κ * c) := by
  have hC : (C κ : K[X]) ≠ 0 := C_ne_zero.2 hκ
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  exact ⟨mul_ne_zero hC h.ne_a, mul_ne_zero hC h.ne_b, mul_ne_zero hC h.ne_c,
    ⟨C κ * d, by linear_combination C κ ^ 2 * hd⟩, ⟨C κ * e, by linear_combination C κ ^ 2 * he⟩,
    ⟨C κ * f, by linear_combination C κ ^ 2 * hf⟩, ⟨C κ * g, by linear_combination C κ ^ 2 * hg⟩⟩

theorem proportional_C_mul {a b c : K[X]} (h : Proportional a b c) (κ : K) :
    Proportional (C κ * a) (C κ * b) (C κ * c) := by
  obtain ⟨p, α, β, γ, ha, hb, hc⟩ := h
  exact ⟨p, κ * α, κ * β, κ * γ, by rw [ha, C_mul, mul_assoc], by rw [hb, C_mul, mul_assoc],
    by rw [hc, C_mul, mul_assoc]⟩

theorem proportional_C_mul_iff {a b c : K[X]} {κ : K} (hκ : κ ≠ 0) :
    Proportional (C κ * a) (C κ * b) (C κ * c) ↔ Proportional a b c := by
  constructor
  · intro h
    have e : ∀ p : K[X], C κ⁻¹ * (C κ * p) = p := fun p => by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hκ, C_1, one_mul]
    simpa only [e] using proportional_C_mul h κ⁻¹
  · intro h
    exact proportional_C_mul h κ

/-! ## From "an edge is parallel to `a`" to proportionality -/

/-- If one of `b`, `c`, `f` (with `f² = b² + c²`) is a constant multiple of `a`, a
nondegenerate cuboid is proportional: two edges by `IsCuboid.proportional_of_two_edges`, the
opposite face diagonal by `IsNondegCuboid.proportional_of_opp_diag_eq_edge`. -/
theorem proportional_of_parallel (h2 : (2 : K) ≠ 0) {a b c f : K[X]} (h : IsNondegCuboid a b c)
    (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hpar : (∃ β : K, b = C β * a) ∨ (∃ γ : K, c = C γ * a) ∨ (∃ φ : K, f = C φ * a)) :
    Proportional a b c := by
  rcases hpar with hb | hc | ⟨φ, rfl⟩
  · exact h.toIsCuboid.proportional_of_two_edges h2 (Or.inl hb)
  · exact h.toIsCuboid.proportional_of_two_edges h2 (Or.inr (Or.inl hc))
  · exact h.proportional_of_opp_diag_eq_edge h2 hf

/-! ## The face identity and the functional argument -/

/-- For a face `a² + x² = y²`, with `p = y − x`, `q = y + x`: `p q = a²`, `2x = q − p` and
`(2x)² + 2a² = p² + q²`. -/
theorem face_identity {a x y : K[X]} (h : a ^ 2 + x ^ 2 = y ^ 2) :
    (y - x) * (y + x) = a ^ 2 ∧ 2 * x = (y + x) - (y - x) ∧
      (2 * x) ^ 2 + 2 * a ^ 2 = (y - x) ^ 2 + (y + x) ^ 2 :=
  ⟨by linear_combination -h, by ring, by linear_combination 2 * h⟩

/-- **Key identity.** If `b² + c² = f²` then `Σ ((2x)² + 2a²)` over `b, c` minus the same for `f`
is `2a²`; so a linear functional killing the three terms kills `a²`. -/
theorem functional_key (h2 : (2 : K) ≠ 0) (ℓ : K[X] →ₗ[K] K) {a b c f : K[X]}
    (hbcf : b ^ 2 + c ^ 2 = f ^ 2) (hb : ℓ ((2 * b) ^ 2 + 2 * a ^ 2) = 0)
    (hc : ℓ ((2 * c) ^ 2 + 2 * a ^ 2) = 0) (hf : ℓ ((2 * f) ^ 2 + 2 * a ^ 2) = 0) :
    ℓ (a ^ 2) = 0 := by
  have e : ((2 * b) ^ 2 + 2 * a ^ 2) + ((2 * c) ^ 2 + 2 * a ^ 2) - ((2 * f) ^ 2 + 2 * a ^ 2)
      = (2 : K) • a ^ 2 := by
    rw [smul_eq_C_mul, show (C 2 : K[X]) = 2 from map_ofNat C 2]
    linear_combination 4 * hbcf
  have := congrArg ℓ e
  rw [map_sub, map_add, hb, hc, hf, map_smul, smul_eq_mul] at this
  have h0 : (2 : K) * ℓ (a ^ 2) = 0 := by rw [← this]; ring
  exact (mul_eq_zero.1 h0).resolve_left h2

theorem ell_C_mul (ℓ : K[X] →ₗ[K] K) (u : K) (p : K[X]) : ℓ (C u * p) = u * ℓ p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

/-! ## Divisors -/

theorem exists_C_mul_of_associated {p q : K[X]} (h : Associated p q) :
    ∃ u : K, u ≠ 0 ∧ p = C u * q := by
  obtain ⟨w, hw⟩ := h.symm
  obtain ⟨r, hr, hrw⟩ := Polynomial.isUnit_iff.1 w.isUnit
  exact ⟨r, hr.ne_zero, by rw [← hw, ← hrw, mul_comm]⟩

theorem exists_C_mul_of_dvd_prime_pow {π p : K[X]} (hπ : Prime π) {n : ℕ} (h : p ∣ π ^ n) :
    ∃ i ≤ n, ∃ u : K, u ≠ 0 ∧ p = C u * π ^ i := by
  obtain ⟨i, hi, hass⟩ := (dvd_prime_pow hπ n).1 h
  obtain ⟨u, hu, rfl⟩ := exists_C_mul_of_associated hass
  exact ⟨i, hi, u, hu, rfl⟩

theorem cofactor {p q D D' : K[X]} {u : K} (hu : u ≠ 0) (hD : D ≠ 0) (hp : p = C u * D)
    (h : p * q = D * D') : q = C u⁻¹ * D' := by
  subst hp
  apply mul_left_cancel₀ (mul_ne_zero (C_ne_zero.2 hu) hD)
  rw [h, show C u * D * (C u⁻¹ * D') = (C u * C u⁻¹) * (D * D') by ring, ← C_mul,
    mul_inv_cancel₀ hu, C_1, one_mul]

theorem two_ne_zero_poly (h2 : (2 : K) ≠ 0) : (2 : K[X]) ≠ 0 := by
  rw [show (2 : K[X]) = C 2 from (map_ofNat C 2).symm]
  exact C_ne_zero.2 h2

/-- If `2x = C s * a` then `x = C (s/2) * a`. -/
theorem eq_C_mul_of_two_mul (h2 : (2 : K) ≠ 0) {x a : K[X]} {s : K} (h : 2 * x = C s * a) :
    x = C (s / 2) * a := by
  apply mul_left_cancel₀ (two_ne_zero_poly h2)
  rw [h, show (2 : K[X]) = C 2 from (map_ofNat C 2).symm, ← mul_assoc, ← C_mul,
    mul_div_cancel₀ _ h2]

/-! ## Split edge `a = κ X (X − 1)` -/

theorem coeff_X_pow_mul_X_sub_one_pow (i j k : ℕ) : (X ^ i * (X - 1 : K[X]) ^ j).coeff k =
    if i ≤ k then (-1 : K) ^ (j - (k - i)) * ((j.choose (k - i) : ℕ) : K) else 0 := by
  rw [coeff_X_pow_mul', show (X - 1 : K[X]) = X + C (-1) by simp [sub_eq_add_neg]]
  split_ifs
  · rw [coeff_X_add_C_pow]
  · rfl

theorem split_divisor {p : K[X]} (h : p ∣ X ^ 2 * (X - 1) ^ 2) :
    ∃ i j : ℕ, i ≤ 2 ∧ j ≤ 2 ∧ ∃ u : K, u ≠ 0 ∧ p = C u * (X ^ i * (X - 1) ^ j) := by
  obtain ⟨p1, p2, h1, h2, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
  have hZ : Prime (X - 1 : K[X]) := by simpa using prime_X_sub_C (1 : K)
  obtain ⟨i, hi, u, hu, rfl⟩ := exists_C_mul_of_dvd_prime_pow prime_X h1
  obtain ⟨j, hj, w, hw, rfl⟩ := exists_C_mul_of_dvd_prime_pow hZ h2
  exact ⟨i, j, hi, hj, u * w, mul_ne_zero hu hw, by rw [C_mul]; ring⟩

/-- **Partners of the split edge.** If `(κ X (X − 1))² + x² = y²`, then either `x ∥ X (X − 1)`, or
`y − x = u Xⁱ (X − 1)ʲ` with `(i, j) ≠ (1, 1)`, and then `(2x)² + 2a²` is a combination of
`X^{2i} (X − 1)^{2j}` and `X^{2(2−i)} (X − 1)^{2(2−j)}` (killed by every functional killing
both). -/
theorem split_partner (h2 : (2 : K) ≠ 0) {κ : K} (hκ : κ ≠ 0) {x y : K[X]}
    (h : (C κ * (X * (X - 1))) ^ 2 + x ^ 2 = y ^ 2) :
    (∃ β : K, x = C β * (C κ * (X * (X - 1)))) ∨
    ∃ i j : ℕ, i ≤ 2 ∧ j ≤ 2 ∧ ¬ (i = 1 ∧ j = 1) ∧ ∀ ℓ : K[X] →ₗ[K] K,
      ℓ (X ^ (2 * i) * (X - 1) ^ (2 * j)) = 0 →
      ℓ (X ^ (2 * (2 - i)) * (X - 1) ^ (2 * (2 - j))) = 0 →
      ℓ ((2 * x) ^ 2 + 2 * (C κ * (X * (X - 1))) ^ 2) = 0 := by
  obtain ⟨hpq, hx, hT⟩ := face_identity h
  have ha2 : (C κ * (X * (X - 1))) ^ 2 = C (κ ^ 2) * (X ^ 2 * (X - 1) ^ 2) := by
    rw [C_pow]; ring
  have hdvd : y - x ∣ X ^ 2 * (X - 1) ^ 2 := by
    have : y - x ∣ C (κ ^ 2) * (X ^ 2 * (X - 1) ^ 2) := ⟨y + x, by rw [← ha2, hpq]⟩
    exact (IsUnit.dvd_mul_left (isUnit_C.2 (pow_ne_zero 2 hκ).isUnit)).1 this
  obtain ⟨i, j, hi, hj, u, hu, hp⟩ := split_divisor hdvd
  have hZ : (X - 1 : K[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : K)
  have hD : (X ^ i * (X - 1) ^ j : K[X]) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hZ)
  have hq : y + x = C u⁻¹ * (C (κ ^ 2) * (X ^ (2 - i) * (X - 1) ^ (2 - j))) := by
    apply cofactor hu hD hp
    rw [hpq, ha2]
    have e1 : (X : K[X]) ^ i * X ^ (2 - i) = X ^ 2 := by rw [← pow_add, Nat.add_sub_cancel' hi]
    have e2 : (X - 1 : K[X]) ^ j * (X - 1) ^ (2 - j) = (X - 1) ^ 2 := by
      rw [← pow_add, Nat.add_sub_cancel' hj]
    rw [← e1, ← e2]; ring
  by_cases h11 : i = 1 ∧ j = 1
  · left
    obtain ⟨rfl, rfl⟩ := h11
    refine ⟨(u⁻¹ * κ ^ 2 - u) / κ / 2, eq_C_mul_of_two_mul h2 ?_⟩
    rw [hx, hq, hp]
    have hk : C ((u⁻¹ * κ ^ 2 - u) / κ) * C κ = C u⁻¹ * C (κ ^ 2) - C u := by
      rw [← C_mul, div_mul_cancel₀ _ hκ, C_sub, C_mul]
    simp only [C_pow, pow_one, show 2 - 1 = 1 from rfl] at hk ⊢
    linear_combination (-(X * (X - 1))) * hk
  · right
    refine ⟨i, j, hi, hj, h11, fun ℓ h1 h2' => ?_⟩
    rw [hT, hp, hq]
    have e : (C u * (X ^ i * (X - 1) ^ j)) ^ 2 +
        (C u⁻¹ * (C (κ ^ 2) * (X ^ (2 - i) * (X - 1) ^ (2 - j)))) ^ 2
        = C (u ^ 2) * (X ^ (2 * i) * (X - 1) ^ (2 * j)) +
          C ((u⁻¹ * κ ^ 2) ^ 2) * (X ^ (2 * (2 - i)) * (X - 1) ^ (2 * (2 - j))) := by
      simp only [C_pow, C_mul]; ring
    rw [e, map_add, ell_C_mul, ell_C_mul, h1, h2', mul_zero, mul_zero, add_zero]

/-! ### Four coordinate functionals

The nine polynomials `B i j = X^{2i} (X − 1)^{2j}` (`i, j ≤ 2`) satisfy exactly one linear
relation, `B 0 0 − 2 B 0 1 + B 0 2 − 2 B 1 0 − 2 B 1 1 + B 2 0 = 0` (from `X − (X − 1) = 1`), so
`B 1 1 = a²/κ²` is *not* a coordinate. The other eight are independent over `ℤ[1/2]`; `ell00`,
`ell01`, `ell02`, `ell10` are (multiples of) the coordinate functionals of `B 0 0`, `B 0 1`,
`B 0 2`, `B 1 0` in that basis, with integer coefficients: each vanishes on the six `B i j`
outside its "class" `{(i, j), (2 − i, 2 − j)}` and `∉ {(1,1)}`, and takes the value `±2` on
`B 1 1`. -/

noncomputable def ell00 : K[X] →ₗ[K] K :=
  4 • lcoeff K 0 + 2 • lcoeff K 1 - lcoeff K 3 + 2 • lcoeff K 5 + 4 • lcoeff K 6 + 4 • lcoeff K 7

noncomputable def ell01 : K[X] →ₗ[K] K :=
  lcoeff K 3 - lcoeff K 1 - 2 • lcoeff K 5 - 4 • lcoeff K 6 - 4 • lcoeff K 7

noncomputable def ell02 : K[X] →ₗ[K] K :=
  2 • lcoeff K 5 + 4 • lcoeff K 6 + 4 • lcoeff K 7 - lcoeff K 3

noncomputable def ell10 : K[X] →ₗ[K] K :=
  lcoeff K 1 + 2 • lcoeff K 2 + 2 • lcoeff K 3 - 3 • lcoeff K 5 - 6 • lcoeff K 6 - 6 • lcoeff K 7

theorem ell00_B (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 2) (h : ¬ ((i = 0 ∧ j = 0) ∨ (i = 2 ∧ j = 2)))
    (h11 : ¬ (i = 1 ∧ j = 1)) : (ell00 : K[X] →ₗ[K] K) (X ^ (2 * i) * (X - 1) ^ (2 * j)) = 0 := by
  interval_cases i <;> interval_cases j <;> simp at h h11 <;>
    simp only [ell00, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      lcoeff_apply, coeff_X_pow_mul_X_sub_one_pow] <;> norm_num [Nat.choose]

theorem ell01_B (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 2) (h : ¬ ((i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 1)))
    (h11 : ¬ (i = 1 ∧ j = 1)) : (ell01 : K[X] →ₗ[K] K) (X ^ (2 * i) * (X - 1) ^ (2 * j)) = 0 := by
  interval_cases i <;> interval_cases j <;> simp at h h11 <;>
    simp only [ell01, LinearMap.sub_apply, LinearMap.smul_apply,
      lcoeff_apply, coeff_X_pow_mul_X_sub_one_pow] <;> norm_num [Nat.choose]

theorem ell02_B (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 2) (h : ¬ ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)))
    (h11 : ¬ (i = 1 ∧ j = 1)) : (ell02 : K[X] →ₗ[K] K) (X ^ (2 * i) * (X - 1) ^ (2 * j)) = 0 := by
  interval_cases i <;> interval_cases j <;> simp at h h11 <;>
    simp only [ell02, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      lcoeff_apply, coeff_X_pow_mul_X_sub_one_pow] <;> norm_num [Nat.choose]

theorem ell10_B (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 2) (h : ¬ ((i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2)))
    (h11 : ¬ (i = 1 ∧ j = 1)) : (ell10 : K[X] →ₗ[K] K) (X ^ (2 * i) * (X - 1) ^ (2 * j)) = 0 := by
  interval_cases i <;> interval_cases j <;> simp at h h11 <;>
    simp only [ell10, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      lcoeff_apply, coeff_X_pow_mul_X_sub_one_pow] <;> norm_num [Nat.choose]

theorem ell00_B11 : (ell00 : K[X] →ₗ[K] K) (X ^ (2 * 1) * (X - 1) ^ (2 * 1)) = 2 := by
  simp only [ell00, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_X_pow_mul_X_sub_one_pow]; norm_num [Nat.choose]

theorem ell01_B11 : (ell01 : K[X] →ₗ[K] K) (X ^ (2 * 1) * (X - 1) ^ (2 * 1)) = -2 := by
  simp only [ell01, LinearMap.sub_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_X_pow_mul_X_sub_one_pow]; norm_num [Nat.choose]

theorem ell02_B11 : (ell02 : K[X] →ₗ[K] K) (X ^ (2 * 1) * (X - 1) ^ (2 * 1)) = 2 := by
  simp only [ell02, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_X_pow_mul_X_sub_one_pow]; norm_num [Nat.choose]

theorem ell10_B11 : (ell10 : K[X] →ₗ[K] K) (X ^ (2 * 1) * (X - 1) ^ (2 * 1)) = -2 := by
  simp only [ell10, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_X_pow_mul_X_sub_one_pow]; norm_num [Nat.choose]

/-- Data attached to a non-parallel partner of the split edge (the right disjunct of
`split_partner`). -/
def SplitData (κ : K) (x : K[X]) (i j : ℕ) : Prop :=
  i ≤ 2 ∧ j ≤ 2 ∧ ¬ (i = 1 ∧ j = 1) ∧ ∀ ℓ : K[X] →ₗ[K] K,
      ℓ (X ^ (2 * i) * (X - 1) ^ (2 * j)) = 0 →
      ℓ (X ^ (2 * (2 - i)) * (X - 1) ^ (2 * (2 - j))) = 0 →
      ℓ ((2 * x) ^ 2 + 2 * (C κ * (X * (X - 1))) ^ 2) = 0

/-- **Pigeonhole step.** If a functional `ℓ` vanishes on every `B i j` outside a class closed
under `(i, j) ↦ (2 − i, 2 − j)` and outside `(1, 1)`, but not on `B 1 1`, then one of `b, c, f`
has its type in the class. -/
theorem split_class_hit (h2 : (2 : K) ≠ 0) {κ : K} (hκ : κ ≠ 0) (ℓ : K[X] →ₗ[K] K)
    (cls : ℕ → ℕ → Prop)
    (hℓ : ∀ i j, i ≤ 2 → j ≤ 2 → ¬ cls i j → ¬ (i = 1 ∧ j = 1) →
      ℓ (X ^ (2 * i) * (X - 1) ^ (2 * j)) = 0)
    (hsym : ∀ i j, i ≤ 2 → j ≤ 2 → cls (2 - i) (2 - j) → cls i j)
    (h11 : ℓ (X ^ (2 * 1) * (X - 1) ^ (2 * 1)) ≠ 0)
    {b c f : K[X]} (hbcf : b ^ 2 + c ^ 2 = f ^ 2) {ib jb ic jc i_f jf : ℕ}
    (hb : SplitData κ b ib jb) (hc : SplitData κ c ic jc) (hf : SplitData κ f i_f jf) :
    cls ib jb ∨ cls ic jc ∨ cls i_f jf := by
  have kill : ∀ (x : K[X]) (i j : ℕ), SplitData κ x i j → ¬ cls i j →
      ℓ ((2 * x) ^ 2 + 2 * (C κ * (X * (X - 1))) ^ 2) = 0 := by
    rintro x i j ⟨hi, hj, hij, hx⟩ hn
    exact hx ℓ (hℓ i j hi hj hn hij)
      (hℓ (2 - i) (2 - j) (by omega) (by omega) (fun h' => hn (hsym i j hi hj h')) (by omega))
  by_contra hn
  simp only [not_or] at hn
  have key := functional_key h2 ℓ hbcf (kill b ib jb hb hn.1) (kill c ic jc hc hn.2.1)
    (kill f i_f jf hf hn.2.2)
  have ha2 : (C κ * (X * (X - 1))) ^ 2 = C (κ ^ 2) * (X ^ (2 * 1) * (X - 1) ^ (2 * 1)) := by
    rw [C_pow]; ring
  rw [ha2, ell_C_mul] at key
  exact (mul_ne_zero (pow_ne_zero 2 hκ) h11) key

/-- **Split edge, any field with `2 ≠ 0`.** In a cuboid with edge `κ X (X − 1)`, one of `b`, `c`,
`f` (`f² = b² + c²`) is a constant multiple of the edge. -/
theorem split_parallel (h2 : (2 : K) ≠ 0) {κ : K} (hκ : κ ≠ 0) {b c f : K[X]}
    (h : IsCuboid (C κ * (X * (X - 1))) b c) (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    (∃ β : K, b = C β * (C κ * (X * (X - 1)))) ∨ (∃ γ : K, c = C γ * (C κ * (X * (X - 1)))) ∨
      (∃ φ : K, f = C φ * (C κ * (X * (X - 1)))) := by
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨g, hg⟩ := h.sq_abc
  rw [← sq] at hd he hg
  have hg' : (C κ * (X * (X - 1))) ^ 2 + f ^ 2 = g ^ 2 := by rw [← hf, ← hg]; ring
  rcases split_partner h2 hκ hd with hb | ⟨ib, jb, hb⟩
  · exact Or.inl hb
  rcases split_partner h2 hκ he with hc | ⟨ic, jc, hc⟩
  · exact Or.inr (Or.inl hc)
  rcases split_partner h2 hκ hg' with hf' | ⟨i_f, jf, hfT⟩
  · exact Or.inr (Or.inr hf')
  exfalso
  have k1 := split_class_hit h2 hκ ell00 (fun i j => (i = 0 ∧ j = 0) ∨ (i = 2 ∧ j = 2))
    ell00_B (fun i j _ _ h => by omega) (by rw [ell00_B11]; exact h2) hf hb hc hfT
  have k2 := split_class_hit h2 hκ ell01 (fun i j => (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 1))
    ell01_B (fun i j _ _ h => by omega) (by rw [ell01_B11]; exact neg_ne_zero.2 h2) hf hb hc hfT
  have k3 := split_class_hit h2 hκ ell02 (fun i j => (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0))
    ell02_B (fun i j _ _ h => by omega) (by rw [ell02_B11]; exact h2) hf hb hc hfT
  have k4 := split_class_hit h2 hκ ell10 (fun i j => (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2))
    ell10_B (fun i j _ _ h => by omega) (by rw [ell10_B11]; exact neg_ne_zero.2 h2) hf hb hc hfT
  obtain ⟨hib, hjb, hb11, -⟩ := hb
  obtain ⟨hic, hjc, hc11, -⟩ := hc
  obtain ⟨hif, hjf, hf11, -⟩ := hfT
  omega

/-! ## Double root `a = α X²` -/

theorem double_partner (h2 : (2 : K) ≠ 0) {α : K} (hα : α ≠ 0) {x y : K[X]}
    (h : (C α * X ^ 2) ^ 2 + x ^ 2 = y ^ 2) :
    (∃ β : K, x = C β * (C α * X ^ 2)) ∨ ((2 * x) ^ 2 + 2 * (C α * X ^ 2) ^ 2).coeff 4 = 0 := by
  obtain ⟨hpq, hx, hT⟩ := face_identity h
  have ha2 : (C α * X ^ 2) ^ 2 = C (α ^ 2) * X ^ 4 := by rw [C_pow]; ring
  have hdvd : y - x ∣ X ^ 4 := by
    have : y - x ∣ C (α ^ 2) * X ^ 4 := ⟨y + x, by rw [← ha2, hpq]⟩
    exact (IsUnit.dvd_mul_left (isUnit_C.2 (pow_ne_zero 2 hα).isUnit)).1 this
  obtain ⟨i, hi, u, hu, hp⟩ := exists_C_mul_of_dvd_prime_pow prime_X hdvd
  have hq : y + x = C u⁻¹ * (C (α ^ 2) * X ^ (4 - i)) := by
    apply cofactor hu (pow_ne_zero _ X_ne_zero) hp
    have e1 : (X : K[X]) ^ i * X ^ (4 - i) = X ^ 4 := by rw [← pow_add, Nat.add_sub_cancel' hi]
    rw [hpq, ha2, ← e1]; ring
  by_cases h22 : i = 2
  · left
    subst h22
    refine ⟨(u⁻¹ * α ^ 2 - u) / α / 2, eq_C_mul_of_two_mul h2 ?_⟩
    rw [hx, hq, hp]
    have hk : C ((u⁻¹ * α ^ 2 - u) / α) * C α = C u⁻¹ * C (α ^ 2) - C u := by
      rw [← C_mul, div_mul_cancel₀ _ hα, C_sub, C_mul]
    simp only [C_pow, show 4 - 2 = 2 from rfl] at hk ⊢
    linear_combination (-(X ^ 2)) * hk
  · right
    rw [hT, hp, hq]
    have e : (C u * X ^ i) ^ 2 + (C u⁻¹ * (C (α ^ 2) * X ^ (4 - i))) ^ 2
        = C (u ^ 2) * X ^ (2 * i) + C ((u⁻¹ * α ^ 2) ^ 2) * X ^ (2 * (4 - i)) := by
      simp only [C_pow, C_mul]; ring
    rw [e, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X_pow]
    split_ifs <;> first | omega | ring

/-- **Double root, any field with `2 ≠ 0`.** In a cuboid with edge `α X²`, one of `b`, `c`, `f` is
a constant multiple of the edge (the functional is the coefficient of `X⁴`). -/
theorem double_parallel (h2 : (2 : K) ≠ 0) {α : K} (hα : α ≠ 0) {b c f : K[X]}
    (h : IsCuboid (C α * X ^ 2) b c) (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    (∃ β : K, b = C β * (C α * X ^ 2)) ∨ (∃ γ : K, c = C γ * (C α * X ^ 2)) ∨
      (∃ φ : K, f = C φ * (C α * X ^ 2)) := by
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨g, hg⟩ := h.sq_abc
  rw [← sq] at hd he hg
  have hg' : (C α * X ^ 2) ^ 2 + f ^ 2 = g ^ 2 := by rw [← hf, ← hg]; ring
  rcases double_partner h2 hα hd with hb | hb
  · exact Or.inl hb
  rcases double_partner h2 hα he with hc | hc
  · exact Or.inr (Or.inl hc)
  rcases double_partner h2 hα hg' with hf' | hfT
  · exact Or.inr (Or.inr hf')
  exfalso
  have key := functional_key h2 (lcoeff K 4) hf (by rw [lcoeff_apply]; exact hb)
    (by rw [lcoeff_apply]; exact hc) (by rw [lcoeff_apply]; exact hfT)
  have ha2 : (C α * X ^ 2) ^ 2 = C (α ^ 2) * X ^ 4 := by rw [C_pow]; ring
  rw [lcoeff_apply, ha2, coeff_C_mul, coeff_X_pow, ite_eq_left (rfl : 4 = 4), mul_one] at key
  exact pow_ne_zero 2 hα key

/-! ## Irreducible quadratic edge -/

/-- The functional `p ↦ lc(a)⁴ p₄ − (a⁴)₄ p₈`: it kills `1` and `a⁴` and not `a²`. -/
noncomputable def ellIrr (a : K[X]) : K[X] →ₗ[K] K :=
  a.leadingCoeff ^ 4 • lcoeff K 4 - (a ^ 4).coeff 4 • lcoeff K 8

theorem irr_partner (h2 : (2 : K) ≠ 0) {a : K[X]} (hirr : Irreducible a) (hdeg : a.natDegree = 2)
    {x y : K[X]} (h : a ^ 2 + x ^ 2 = y ^ 2) :
    (∃ β : K, x = C β * a) ∨ ellIrr a ((2 * x) ^ 2 + 2 * a ^ 2) = 0 := by
  obtain ⟨hpq, hx, hT⟩ := face_identity h
  have hdvd : y - x ∣ a ^ 2 := ⟨y + x, hpq.symm⟩
  obtain ⟨i, hi, u, hu, hp⟩ := exists_C_mul_of_dvd_prime_pow hirr.prime hdvd
  have ha0 : a ≠ 0 := hirr.ne_zero
  have hq : y + x = C u⁻¹ * a ^ (2 - i) := by
    apply cofactor hu (pow_ne_zero _ ha0) hp
    rw [hpq, ← pow_add, Nat.add_sub_cancel' hi]
  by_cases h1 : i = 1
  · left
    subst h1
    refine ⟨(u⁻¹ - u) / 2, eq_C_mul_of_two_mul h2 ?_⟩
    rw [hx, hq, hp, C_sub]
    simp only [show 2 - 1 = 1 from rfl, pow_one]
    ring
  · right
    rw [hT, hp, hq]
    have h4 : ellIrr a (a ^ 4) = 0 := by
      simp only [ellIrr, LinearMap.sub_apply, LinearMap.smul_apply, lcoeff_apply, smul_eq_mul]
      have : (a ^ 4).coeff 8 = a.leadingCoeff ^ 4 := by
        rw [← leadingCoeff_pow, leadingCoeff, natDegree_pow, hdeg]
      rw [this]; ring
    have h0 : ellIrr a 1 = 0 := by
      simp only [ellIrr, LinearMap.sub_apply, LinearMap.smul_apply, lcoeff_apply, coeff_one]
      simp
    interval_cases i
    · have e : (C u * a ^ 0) ^ 2 + (C u⁻¹ * a ^ (2 - 0)) ^ 2 =
          C (u ^ 2) * 1 + C (u⁻¹ ^ 2) * a ^ 4 := by
        simp only [C_pow]; ring
      rw [e, map_add, ell_C_mul, ell_C_mul, h0, h4]; ring
    · exact absurd rfl h1
    · have e : (C u * a ^ 2) ^ 2 + (C u⁻¹ * a ^ (2 - 2)) ^ 2 =
          C (u ^ 2) * a ^ 4 + C (u⁻¹ ^ 2) * 1 := by
        simp only [C_pow]; ring
      rw [e, map_add, ell_C_mul, ell_C_mul, h0, h4]; ring

/-- **Irreducible quadratic edge, any field with `2 ≠ 0`.** One of `b`, `c`, `f` is a constant
multiple of `a`. -/
theorem irr_parallel (h2 : (2 : K) ≠ 0) {a b c f : K[X]} (hirr : Irreducible a)
    (hdeg : a.natDegree = 2) (h : IsCuboid a b c) (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    (∃ β : K, b = C β * a) ∨ (∃ γ : K, c = C γ * a) ∨ (∃ φ : K, f = C φ * a) := by
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨g, hg⟩ := h.sq_abc
  rw [← sq] at hd he hg
  have hg' : a ^ 2 + f ^ 2 = g ^ 2 := by rw [← hf, ← hg]; ring
  rcases irr_partner h2 hirr hdeg hd with hb | hb
  · exact Or.inl hb
  rcases irr_partner h2 hirr hdeg he with hc | hc
  · exact Or.inr (Or.inl hc)
  rcases irr_partner h2 hirr hdeg hg' with hf' | hfT
  · exact Or.inr (Or.inr hf')
  exfalso
  have key := functional_key h2 (ellIrr a) hf hb hc hfT
  simp only [ellIrr, LinearMap.sub_apply, LinearMap.smul_apply, lcoeff_apply, smul_eq_mul] at key
  have h4 : (a ^ 2).coeff 4 = a.leadingCoeff ^ 2 := by
    rw [← leadingCoeff_pow, leadingCoeff, natDegree_pow, hdeg]
  have h8 : (a ^ 2).coeff 8 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [natDegree_pow, hdeg]; norm_num)
  rw [h4, h8, mul_zero, sub_zero] at key
  have hl : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hirr.ne_zero
  exact mul_ne_zero (pow_ne_zero 4 hl) (pow_ne_zero 2 hl) key

/-! ## Reduction of an arbitrary quadratic edge -/

/-- A quadratic polynomial is irreducible or splits as `m (X − r)(X − s)`. -/
theorem irreducible_or_split {a : K[X]} (ha : a.natDegree = 2) :
    Irreducible a ∨ ∃ m r s : K, m ≠ 0 ∧ a = C m * ((X - C r) * (X - C s)) := by
  by_cases hroot : ∃ r, a.IsRoot r
  · right
    obtain ⟨r, hr⟩ := hroot
    have e1 : (X - C r) * (a /ₘ (X - C r)) = a := mul_divByMonic_eq_iff_isRoot.2 hr
    have hd1 : (a /ₘ (X - C r)).natDegree = 1 := by
      rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, ha]
    obtain ⟨s, hs⟩ := exists_root_of_degree_eq_one
      ((degree_eq_iff_natDegree_eq_of_pos one_pos).2 hd1)
    have e2 : (X - C s) * ((a /ₘ (X - C r)) /ₘ (X - C s)) = a /ₘ (X - C r) :=
      mul_divByMonic_eq_iff_isRoot.2 hs
    have hd2 : ((a /ₘ (X - C r)) /ₘ (X - C s)).natDegree = 0 := by
      rw [natDegree_divByMonic _ (monic_X_sub_C s), natDegree_X_sub_C, hd1]
    have hm := eq_C_of_natDegree_eq_zero hd2
    refine ⟨((a /ₘ (X - C r)) /ₘ (X - C s)).coeff 0, r, s, ?_, ?_⟩
    · intro h0
      rw [h0, C_0] at hm
      rw [hm, mul_zero] at e2
      rw [← e2, mul_zero] at e1
      rw [← e1] at ha
      simp at ha
    · rw [← hm]
      calc a = (X - C r) * ((X - C s) * ((a /ₘ (X - C r)) /ₘ (X - C s))) := by rw [e2, e1]
        _ = _ := by ring
  · left
    push Not at hroot
    exact irreducible_of_degree_le_three_of_not_isRoot (by rw [ha]; decide) hroot

theorem eq_of_comp_eq {x a : K[X]} {lam r β : K} (hlam : lam ≠ 0)
    (h : x.comp (C lam * X + C r) = C β * a.comp (C lam * X + C r)) : x = C β * a := by
  rw [← comp_linear_comp_inv x hlam r, h, mul_comp, C_comp, comp_linear_comp_inv a hlam r]

/-- Transport of the "parallel" trichotomy along `X ↦ λ X + r`. -/
theorem parallel_of_comp {a b c f : K[X]} {lam r : K} (hlam : lam ≠ 0) {a' : K[X]}
    (ha' : a.comp (C lam * X + C r) = a')
    (hpar : (∃ β : K, b.comp (C lam * X + C r) = C β * a') ∨
      (∃ γ : K, c.comp (C lam * X + C r) = C γ * a') ∨
      (∃ φ : K, f.comp (C lam * X + C r) = C φ * a')) :
    (∃ β : K, b = C β * a) ∨ (∃ γ : K, c = C γ * a) ∨ (∃ φ : K, f = C φ * a) := by
  subst ha'
  rcases hpar with ⟨β, hb⟩ | ⟨γ, hc⟩ | ⟨φ, hf⟩
  · exact Or.inl ⟨β, eq_of_comp_eq hlam hb⟩
  · exact Or.inr (Or.inl ⟨γ, eq_of_comp_eq hlam hc⟩)
  · exact Or.inr (Or.inr ⟨φ, eq_of_comp_eq hlam hf⟩)

/-- **Main structural theorem (any field with `2 ≠ 0`, no hypothesis on `−1`).** In a cuboid
`(a, b, c)` with `deg a = 2`, one of `b`, `c` and the face diagonal `f` (`f² = b² + c²`) is a
constant multiple of `a`. (The degenerate `(X² − 1, 2X, i(X² + 1))` has `f = i a`.) -/
theorem exists_parallel_of_natDegree_eq_two (h2 : (2 : K) ≠ 0) {a b c f : K[X]}
    (h : IsCuboid a b c) (ha : a.natDegree = 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    (∃ β : K, b = C β * a) ∨ (∃ γ : K, c = C γ * a) ∨ (∃ φ : K, f = C φ * a) := by
  rcases irreducible_or_split ha with hirr | ⟨m, r, s, hm, hrs⟩
  · exact irr_parallel h2 hirr ha h hf
  have hfc : ∀ q : K[X], (b.comp q) ^ 2 + (c.comp q) ^ 2 = (f.comp q) ^ 2 := fun q => by
    rw [← pow_comp, ← pow_comp, ← add_comp, hf, pow_comp]
  by_cases hsr : s = r
  · subst hsr
    have ha' : a.comp (C 1 * X + C s) = C m * X ^ 2 := by
      rw [hrs]; simp only [mul_comp, sub_comp, C_comp, X_comp, C_1]; ring
    have h' := isCuboid_comp_linear h (r := s) one_ne_zero
    rw [ha'] at h'
    exact parallel_of_comp one_ne_zero ha' (double_parallel h2 hm h' (hfc _))
  · have hl : s - r ≠ 0 := sub_ne_zero.2 hsr
    have ha' : a.comp (C (s - r) * X + C r) = C (m * (s - r) ^ 2) * (X * (X - 1)) := by
      rw [hrs]; simp only [mul_comp, sub_comp, C_comp, X_comp, C_mul, C_pow, C_sub]; ring
    have h' := isCuboid_comp_linear h (r := r) hl
    rw [ha'] at h'
    exact parallel_of_comp hl ha'
      (split_parallel h2 (mul_ne_zero hm (pow_ne_zero 2 hl)) h' (hfc _))

/-! ## Headline theorems -/

/-- **A nondegenerate cuboid with an edge of degree 2 is proportional**, over any field with
`2 ≠ 0`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_natDegree_eq_two
    (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsNondegCuboid a b c) (ha : a.natDegree = 2) :
    Proportional a b c := by
  obtain ⟨f, hf⟩ := h.sq_bc
  rw [← sq] at hf
  exact proportional_of_parallel h2 h hf
    (exists_parallel_of_natDegree_eq_two h2 h.toIsCuboid ha hf)

/-- **Headline: `−1 ∉ K²`, `2 ≠ 0`: a cuboid with an edge of degree 2 is proportional.** -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_natDegree_eq_two
    (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsCuboid a b c)
    (ha : a.natDegree = 2) : Proportional a b c :=
  (h.isNondegCuboid hK).proportional_of_natDegree_eq_two h2 ha

/-- **`−1 ∉ K²`, `2 ≠ 0`: a cuboid with an edge of degree `≤ 2` is proportional.** -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_natDegree_le_two
    (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsCuboid a b c)
    (ha : a.natDegree ≤ 2) : Proportional a b c := by
  rcases (show a.natDegree = 0 ∨ a.natDegree = 1 ∨ a.natDegree = 2 by omega) with h0 | h1 | h2'
  · rw [eq_C_of_natDegree_eq_zero h0] at h ⊢
    exact h.proportional_of_const h2
  · exact h.proportional_of_natDegree_eq_one hK h2 h1
  · exact h.proportional_of_natDegree_eq_two hK h2 h2'

/-- Normalised split edge `X (X − 1)`. -/
theorem proportional_of_edge_X_mul_X_sub_one (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0)
    {b c : K[X]} (h : IsCuboid (X * (X - 1)) b c) : Proportional (X * (X - 1)) b c :=
  h.proportional_of_natDegree_eq_two hK h2 (by
    rw [natDegree_mul X_ne_zero (by simpa using X_sub_C_ne_zero (1 : K)), natDegree_X,
      show (X - 1 : K[X]) = X - C 1 by simp, natDegree_X_sub_C])

/-- Irreducible quadratic edge. -/
theorem proportional_of_edge_irreducible_quadratic (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0)
    {a b c : K[X]} (h : IsCuboid a b c) (ha : a.natDegree = 2) (_hirr : Irreducible a) :
    Proportional a b c :=
  h.proportional_of_natDegree_eq_two hK h2 ha

/-- If `−1 ∉ K²`, `2 ≠ 0` and `K` has no constant cuboid, every edge of a cuboid over `K[X]` has
degree `≥ 3`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.three_le_natDegree (hK : ¬ IsSquare (-1 : K))
    (h2 : (2 : K) ≠ 0) (h0 : ∀ α β γ : K, ¬ PolyNegOne.IsConstCuboid α β γ) {a b c : K[X]}
    (h : IsCuboid a b c) : 3 ≤ a.natDegree := by
  by_contra hlt
  obtain ⟨α, β, γ, hc⟩ :=
    (h.proportional_of_natDegree_le_two hK h2 (by omega)).isConstCuboid h
  exact h0 _ _ _ hc

theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.three_le_natDegree_all (hK : ¬ IsSquare (-1 : K))
    (h2 : (2 : K) ≠ 0) (h0 : ∀ α β γ : K, ¬ PolyNegOne.IsConstCuboid α β γ) {a b c : K[X]}
    (h : IsCuboid a b c) : 3 ≤ a.natDegree ∧ 3 ≤ b.natDegree ∧ 3 ≤ c.natDegree :=
  ⟨h.three_le_natDegree hK h2 h0, (PolyNegOne.isCuboid_swap_ab h).three_le_natDegree hK h2 h0,
    (PolyNegOne.isCuboid_swap_ac h).three_le_natDegree hK h2 h0⟩

/-! ## Corollaries over `ℚ` and `𝔽_p` -/

theorem not_isSquare_neg_one_rat : ¬ IsSquare (-1 : ℚ) := by
  rintro ⟨r, hr⟩
  nlinarith [mul_self_nonneg r]

theorem isCuboid_of_isPolyCuboid {a b c : ℚ[X]} (h : Poly.IsPolyCuboid a b c) : IsCuboid a b c :=
  ⟨h.ne_a, h.ne_b, h.ne_c, h.sq_ab, h.sq_ac, h.sq_bc, h.sq_abc⟩

/-- **`ℚ[X]`: a polynomial cuboid with an edge of degree `≤ 2` gives an integer perfect cuboid.**
(Conversely `(pX, qX, rX)` is one, so such polynomial cuboids exist iff perfect cuboids do.) -/
theorem _root_.PerfectCuboid.Poly.IsPolyCuboid.exists_isPerfectCuboid_of_natDegree_le_two
    {a b c : ℚ[X]} (h : Poly.IsPolyCuboid a b c) (ha : a.natDegree ≤ 2) :
    ∃ A B C : ℕ, IsPerfectCuboid A B C := by
  obtain ⟨q, α, β, γ, h1, h2, h3⟩ := (isCuboid_of_isPolyCuboid h).proportional_of_natDegree_le_two
    not_isSquare_neg_one_rat (by norm_num) ha
  exact h.exists_isPerfectCuboid_of_proportional h1 h2 h3

section Fp

local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance fact_prime_nineteen : Fact (Nat.Prime 19) := ⟨by norm_num⟩

/-- **Every edge of every cuboid over `𝔽₃[X]` has degree `≥ 3`.** -/
theorem no_cuboid_natDegree_le_two_three :
    ∀ a b c : (ZMod 3)[X], IsCuboid a b c →
      3 ≤ a.natDegree ∧ 3 ≤ b.natDegree ∧ 3 ≤ c.natDegree :=
  fun _ _ _ h => h.three_le_natDegree_all (PolyNegOne.zmod_not_isSquare_neg_one (by norm_num))
    (by decide) PolyNegOne.not_isConstCuboid_three

theorem no_cuboid_natDegree_le_two_seven :
    ∀ a b c : (ZMod 7)[X], IsCuboid a b c →
      3 ≤ a.natDegree ∧ 3 ≤ b.natDegree ∧ 3 ≤ c.natDegree :=
  fun _ _ _ h => h.three_le_natDegree_all (PolyNegOne.zmod_not_isSquare_neg_one (by norm_num))
    (by decide) PolyNegOne.not_isConstCuboid_seven

theorem no_cuboid_natDegree_le_two_eleven :
    ∀ a b c : (ZMod 11)[X], IsCuboid a b c →
      3 ≤ a.natDegree ∧ 3 ≤ b.natDegree ∧ 3 ≤ c.natDegree :=
  fun _ _ _ h => h.three_le_natDegree_all (PolyNegOne.zmod_not_isSquare_neg_one (by norm_num))
    (by decide) PolyNegOne.not_isConstCuboid_eleven

theorem no_cuboid_natDegree_le_two_nineteen :
    ∀ a b c : (ZMod 19)[X], IsCuboid a b c →
      3 ≤ a.natDegree ∧ 3 ≤ b.natDegree ∧ 3 ≤ c.natDegree :=
  fun _ _ _ h => h.three_le_natDegree_all (PolyNegOne.zmod_not_isSquare_neg_one (by norm_num))
    (by decide) PolyNegOne.not_isConstCuboid_nineteen

end Fp

end PerfectCuboid.PolyQuadraticEdge
