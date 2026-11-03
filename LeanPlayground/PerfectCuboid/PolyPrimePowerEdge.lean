module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolyCharP
public import LeanPlayground.PerfectCuboid.PolyNegOne
public import LeanPlayground.PerfectCuboid.PolyPythagoras
public import LeanPlayground.PerfectCuboid.PolyGenusOne
public import LeanPlayground.PerfectCuboid.PolyQuadraticEdge
public import LeanPlayground.PerfectCuboid.PolynomialCuboid

/-! # An edge or the space diagonal that is a power of one irreducible (round 19, brief 1)

Cuboids over `K[X]` (`PolyCharP.IsCuboid`): nonzero `a, b, c` with `a² + b²`, `a² + c²`,
`b² + c² = f²`, `a² + b² + c² = g²` squares.

* **Core, any field with `2 ≠ 0`, no nondegeneracy** (`exists_parallel_of_irreducible_pow_edge`):
  if the edge is `a = α πⁿ` with `π` irreducible, one of `b`, `c`, `f` is a constant multiple of
  `a`. Proof: for each face `a² + x² = y²`, `(y − x)(y + x) = a²` forces `y − x = u πⁱ`
  (`partner`); if `i = n` then `x ∥ a`, otherwise `(2x)² + 2a² = T(π)` with `T` free of
  `X^{2n}`. The identity `Σ_{b,c} ((2x)² + 2a²) − ((2f)² + 2a²) = 2a²` then gives a polynomial
  `P` with `P(π) = 0` and `P_{2n} = −2α² ≠ 0`, impossible for nonconstant `π`
  (`eq_zero_of_comp_irreducible`, via `comp_eq_zero_iff`). This is `PolyQuadraticEdge
  .double_parallel` for every `n` and every irreducible `π`.
* **Headlines**: `IsNondegCuboid.proportional_of_irreducible_pow_edge` (nondegenerate, any field,
  `2 ≠ 0`), `IsCuboid.proportional_of_irreducible_pow_edge` (`−1 ∉ K²`),
  `IsNondegCuboid.proportional_of_single_root_edge` (`a = α (X − r)ⁿ`, any field),
  `IsNondegCuboid.proportional_of_irreducible_pow_space_diag` (`g = α πⁿ`, `i ∈ K`, via the space
  swap `(g, ib, ic)`), `IsNondegCuboid.proportional_of_single_root_space_diag` (`g = α (X − r)ⁿ`,
  any field with `2 ≠ 0`, via `AlgebraicClosure K` and the descent `proportional_of_map`),
  and over an algebraically closed field `IsNondegCuboid.proportional_of_roots_card_le_one`
  (`a.roots.toFinset.card ≤ 1`) and `IsNondegCuboid.proportional_of_space_diag_roots_card_le_one`.
  Over `ℚ`: `IsPolyCuboid.exists_isPerfectCuboid_of_irreducible_pow_edge`.
* **Meaning over `ℂ`**: what is formalised is that every edge and the space diagonal of a
  nondegenerate non-proportional cuboid over `ℂ[X]` has at least two distinct (affine) roots, in
  the fixed coordinate `X`; `∞` is not counted. Invariantly: after a Möbius reparametrisation of
  `ℙ¹` sending one zero to `∞` (not formalised here), no nondegenerate rational curve on the
  cuboid surface meets a coordinate hyperplane `{edge = 0}` or `{g = 0}` in at most two points of
  `ℙ¹`. The degree is unbounded, so this is outside the Stoll–Testa classification of curves of
  degree `≤ 6`; we
  found no such statement in the literature. It supersedes `PolyLinearNondeg
  .false_of_irreducible_pow_edge` (coprime case) and generalises `PolyMonomialEdge` (`ℚ`) to every
  field with `2 ≠ 0`.
* **Sharpness.** The degenerate `(2X, X² − 1, i(X² + 1))` (`g = 0`) has `f = 2iX = i a` (third
  alternative of the core lemma; `b, c` are not parallel to `a`), so "one of `b, c, f`" cannot be
  improved to "`b` or `c`" and nondegeneracy is needed for proportionality; `(X, iX, c)` has
  `b ∥ a` with `a² + b² = 0`. The char-`p` nondegenerate non-proportional cuboids (Frobenius,
  `𝔽₅` coprime, `𝔽₇`, the `𝔽₅` face-diagonal cuboid) have no edge of the form `α πⁿ`; the
  statement is characteristic-free (only `2 ≠ 0`).

Not proved: anything about edges with two or more distinct irreducible factors, or face diagonals.
Every result concludes `Proportional`, never non-existence of cuboids.
-/

@[expose] public section

open Polynomial

namespace PerfectCuboid.PolyPrimePowerEdge

variable {K : Type*} [Field K]

open PolyCharP PolyQuadraticEdge

/-- A polynomial `P` with `P.comp π = 0`, `π` irreducible, is zero. -/
theorem eq_zero_of_comp_irreducible {π P : K[X]} (hπ : Irreducible π) (h : P.comp π = 0) :
    P = 0 := by
  rcases comp_eq_zero_iff.1 h with h0 | ⟨_, hc⟩
  · exact h0
  · exfalso
    apply hπ.not_isUnit
    have hc0 : π.coeff 0 ≠ 0 := by
      intro h0; rw [h0, C_0] at hc; exact hπ.ne_zero hc
    rw [hc]; exact isUnit_C.2 hc0.isUnit

/-- **Partners of a prime-power edge.** If `(α πⁿ)² + x² = y²` then either `x ∥ α πⁿ`, or
`(2x)² + 2(α πⁿ)² = T(π)` for a polynomial `T` whose coefficient of `X^{2n}` vanishes. -/
theorem partner (hπ : Irreducible π) {α : K} (hα : α ≠ 0) {n : ℕ} {x y : K[X]}
    (h2 : (2 : K) ≠ 0) (h : (C α * π ^ n) ^ 2 + x ^ 2 = y ^ 2) :
    (∃ β : K, x = C β * (C α * π ^ n)) ∨
      ∃ T : K[X], T.coeff (2 * n) = 0 ∧ (2 * x) ^ 2 + 2 * (C α * π ^ n) ^ 2 = T.comp π := by
  obtain ⟨hpq, hx, hT⟩ := face_identity h
  have ha2 : (C α * π ^ n) ^ 2 = C (α ^ 2) * π ^ (2 * n) := by rw [C_pow]; ring
  have hdvd : y - x ∣ π ^ (2 * n) := by
    have : y - x ∣ C (α ^ 2) * π ^ (2 * n) := ⟨y + x, by rw [← ha2, hpq]⟩
    exact (IsUnit.dvd_mul_left (isUnit_C.2 (pow_ne_zero 2 hα).isUnit)).1 this
  obtain ⟨i, hi, u, hu, hp⟩ := exists_C_mul_of_dvd_prime_pow hπ.prime hdvd
  have hq : y + x = C u⁻¹ * (C (α ^ 2) * π ^ (2 * n - i)) := by
    apply cofactor hu (pow_ne_zero _ hπ.ne_zero) hp
    have e1 : π ^ i * π ^ (2 * n - i) = π ^ (2 * n) := by rw [← pow_add, Nat.add_sub_cancel' hi]
    rw [hpq, ha2, ← e1]; ring
  by_cases hin : i = n
  · left
    subst hin
    refine ⟨(u⁻¹ * α ^ 2 - u) / α / 2, eq_C_mul_of_two_mul h2 ?_⟩
    rw [hx, hq, hp]
    have hk : C ((u⁻¹ * α ^ 2 - u) / α) * C α = C u⁻¹ * C (α ^ 2) - C u := by
      rw [← C_mul, div_mul_cancel₀ _ hα, C_sub, C_mul]
    rw [show 2 * i - i = i by omega]
    simp only [C_pow] at hk ⊢
    linear_combination (-(π ^ i)) * hk
  · right
    refine ⟨C (u ^ 2) * X ^ (2 * i) + C ((u⁻¹ * α ^ 2) ^ 2) * X ^ (2 * (2 * n - i)), ?_, ?_⟩
    · rw [coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X_pow]
      split_ifs <;> first | omega | ring
    · rw [hT, hp, hq]
      simp only [add_comp, mul_comp, C_comp, X_pow_comp]
      simp only [C_pow, C_mul]
      ring

/-- **Core lemma (any field with `2 ≠ 0`, no nondegeneracy).** In a cuboid whose edge is
`α πⁿ` (`π` irreducible), one of `b`, `c`, `f` (`f² = b² + c²`) is a constant multiple of
that edge. -/
theorem exists_parallel_of_irreducible_pow_edge (h2 : (2 : K) ≠ 0) {π : K[X]} (hπ : Irreducible π)
    {α : K} (hα : α ≠ 0) {n : ℕ} {b c f : K[X]} (h : IsCuboid (C α * π ^ n) b c)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    (∃ β : K, b = C β * (C α * π ^ n)) ∨ (∃ γ : K, c = C γ * (C α * π ^ n)) ∨
      (∃ φ : K, f = C φ * (C α * π ^ n)) := by
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨g, hg⟩ := h.sq_abc
  rw [← sq] at hd he hg
  have hg' : (C α * π ^ n) ^ 2 + f ^ 2 = g ^ 2 := by rw [← hf, ← hg]; ring
  rcases partner hπ hα h2 hd with hb | ⟨Tb, hTb, eb⟩
  · exact Or.inl hb
  rcases partner hπ hα h2 he with hc | ⟨Tc, hTc, ec⟩
  · exact Or.inr (Or.inl hc)
  rcases partner hπ hα h2 hg' with hf' | ⟨Tf, hTf, ef⟩
  · exact Or.inr (Or.inr hf')
  exfalso
  set P : K[X] := Tb + Tc - Tf - C (2 * α ^ 2) * X ^ (2 * n) with hP
  have hcomp : P.comp π = 0 := by
    simp only [hP, sub_comp, add_comp, mul_comp, C_comp, X_pow_comp, ← eb, ← ec, ← ef]
    simp only [C_mul, C_pow]
    rw [show (C 2 : K[X]) = 2 from map_ofNat C 2]
    linear_combination 4 * hf
  have hP0 := congrArg (coeff · (2 * n)) (eq_zero_of_comp_irreducible hπ hcomp)
  simp only [hP, coeff_sub, coeff_add, hTb, hTc, hTf, coeff_C_mul, coeff_X_pow,
    coeff_zero, ↓reduceIte] at hP0
  exact mul_ne_zero h2 (pow_ne_zero 2 hα) (by linear_combination -hP0)

/-! ## Headline theorems for an edge -/

/-- **Nondegenerate cuboid with an edge `α πⁿ` (`π` irreducible) is proportional**, any field
with `2 ≠ 0`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_irreducible_pow_edge
    (h2 : (2 : K) ≠ 0) {π : K[X]} (hπ : Irreducible π) {α : K} (hα : α ≠ 0) {n : ℕ} {b c : K[X]}
    (h : IsNondegCuboid (C α * π ^ n) b c) : Proportional (C α * π ^ n) b c := by
  obtain ⟨f, hf⟩ := h.sq_bc
  rw [← sq] at hf
  exact proportional_of_parallel h2 h hf
    (exists_parallel_of_irreducible_pow_edge h2 hπ hα h.toIsCuboid hf)

/-- The same for every cuboid when `−1` is not a square in `K`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_irreducible_pow_edge
    (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {π : K[X]} (hπ : Irreducible π) {α : K}
    (hα : α ≠ 0) {n : ℕ} {b c : K[X]} (h : IsCuboid (C α * π ^ n) b c) :
    Proportional (C α * π ^ n) b c :=
  (h.isNondegCuboid hK).proportional_of_irreducible_pow_edge h2 hπ hα

/-- **Single root, any field with `2 ≠ 0`**: a nondegenerate cuboid with an edge `α (X − r)ⁿ`
is proportional. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_single_root_edge
    (h2 : (2 : K) ≠ 0) {α r : K} (hα : α ≠ 0) {n : ℕ} {b c : K[X]}
    (h : IsNondegCuboid (C α * (X - C r) ^ n) b c) : Proportional (C α * (X - C r) ^ n) b c :=
  h.proportional_of_irreducible_pow_edge h2 (irreducible_X_sub_C r) hα

/-! ## Swaps of nondegenerate cuboids -/

theorem isNondegCuboid_swap_ab {a b c : K[X]} (h : IsNondegCuboid a b c) :
    IsNondegCuboid b a c :=
  ⟨PolyNegOne.isCuboid_swap_ab h.toIsCuboid, by convert h.ne_ab using 1; ring,
    by convert h.ne_bc using 1, by convert h.ne_ac using 1, by convert h.ne_abc using 1; ring⟩

theorem isNondegCuboid_swap_ac {a b c : K[X]} (h : IsNondegCuboid a b c) :
    IsNondegCuboid c b a :=
  ⟨PolyNegOne.isCuboid_swap_ac h.toIsCuboid, by convert h.ne_bc using 1; ring,
    by convert h.ne_ac using 1; ring, by convert h.ne_ab using 1; ring,
    by convert h.ne_abc using 1; ring⟩

theorem proportional_swap_ab {a b c : K[X]} (h : Proportional b a c) : Proportional a b c := by
  obtain ⟨q, x, y, z, h1, h2, h3⟩ := h
  exact ⟨q, y, x, z, h2, h1, h3⟩

theorem proportional_swap_ac {a b c : K[X]} (h : Proportional c b a) : Proportional a b c := by
  obtain ⟨q, x, y, z, h1, h2, h3⟩ := h
  exact ⟨q, z, y, x, h3, h2, h1⟩

/-- If `C i * x = C β * G` with `i ≠ 0`, `x ≠ 0`, then `G = C (i / β) * x`. -/
theorem eq_C_mul_of_C_mul_eq {i β : K} (hi : i ≠ 0) {x G : K[X]} (hx : x ≠ 0)
    (h : C i * x = C β * G) : G = C (i / β) * x := by
  have hβ : β ≠ 0 := by
    rintro rfl
    rw [C_0, zero_mul] at h
    exact mul_ne_zero (C_ne_zero.2 hi) hx h
  apply mul_left_cancel₀ (C_ne_zero.2 hβ)
  rw [← h, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ hβ]

/-! ## The space diagonal -/

/-- **Space diagonal `α πⁿ`, field containing `i`** (`i² = −1`, `2 ≠ 0`): a nondegenerate cuboid
whose space diagonal is a constant times a power of one irreducible is proportional. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_irreducible_pow_space_diag
    (h2 : (2 : K) ≠ 0) {i : K} (hi : i ^ 2 = -1) {π : K[X]} (hπ : Irreducible π) {α : K}
    (hα : α ≠ 0) {n : ℕ} {a b c : K[X]} (h : IsNondegCuboid a b c)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = (C α * π ^ n) ^ 2) : Proportional a b c := by
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact one_ne_zero (neg_eq_zero.1 (by rw [← hi]; ring))
  have hs := PolyPythagoras.isNondegCuboid_space_swap hi h hg
  obtain ⟨f, hf⟩ := h.sq_bc
  rw [← sq] at hf
  have hf' : (C i * b) ^ 2 + (C i * c) ^ 2 = (C i * f) ^ 2 := by
    linear_combination (C i) ^ 2 * hf
  rcases exists_parallel_of_irreducible_pow_edge h2 hπ hα hs.toIsCuboid hf' with
    ⟨β, hβ⟩ | ⟨γ, hγ⟩ | ⟨φ, hφ⟩
  · have hG := eq_C_mul_of_C_mul_eq hi0 h.ne_b hβ
    apply proportional_swap_ab
    exact (isNondegCuboid_swap_ab h).proportional_of_space_diag_eq_edge h2 (lam := i / β)
      (by rw [← hG, ← hg]; ring)
  · have hG := eq_C_mul_of_C_mul_eq hi0 h.ne_c hγ
    apply proportional_swap_ac
    exact (isNondegCuboid_swap_ac h).proportional_of_space_diag_eq_edge h2 (lam := i / γ)
      (by rw [← hG, ← hg]; ring)
  · have hf0 : f ≠ 0 := by
      rintro rfl; apply h.ne_bc; rw [hf]; ring
    have hG := eq_C_mul_of_C_mul_eq hi0 hf0 hφ
    set μ := i / φ
    -- `(μ f)² = a² + f²`, so `(μ² − 1) f² = a²`
    have e : C (μ ^ 2 - 1) * f ^ 2 = a ^ 2 := by
      rw [C_sub, C_pow, C_1]
      linear_combination -hg + hf - (by rw [hG] : (C α * π ^ n) ^ 2 = (C μ * f) ^ 2)
    have hμ : μ ^ 2 - 1 ≠ 0 := by
      intro h0; rw [h0, C_0, zero_mul] at e
      exact h.ne_a (pow_eq_zero_iff two_ne_zero |>.1 e.symm)
    obtain ⟨ν, hν⟩ := PolyGenusOne.exists_C_mul_of_sq_eq (b := f) h.ne_a (κ := (μ ^ 2 - 1)⁻¹)
      (by
        rw [← e, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hμ, C_1, one_mul])
    exact h.proportional_of_opp_diag_eq_edge h2 (lam := ν) (by rw [hf, hν])

/-! ## Base change to an extension and descent of proportionality -/

section Map

variable {L : Type*} [Field L]

theorem isNondegCuboid_map (φ : K →+* L) {a b c : K[X]} (h : IsNondegCuboid a b c) :
    IsNondegCuboid (a.map φ) (b.map φ) (c.map φ) := by
  have sq : ∀ p : K[X], IsSquare p → IsSquare (p.map φ) := by
    rintro p ⟨r, hr⟩
    exact ⟨r.map φ, by rw [hr, Polynomial.map_mul]⟩
  have ne : ∀ p : K[X], p ≠ 0 → p.map φ ≠ 0 := fun p hp =>
    (Polynomial.map_ne_zero_iff φ.injective).2 hp
  refine ⟨⟨ne _ h.ne_a, ne _ h.ne_b, ne _ h.ne_c, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [Polynomial.map_add, Polynomial.map_pow] using sq _ h.sq_ab
  · simpa only [Polynomial.map_add, Polynomial.map_pow] using sq _ h.sq_ac
  · simpa only [Polynomial.map_add, Polynomial.map_pow] using sq _ h.sq_bc
  · simpa only [Polynomial.map_add, Polynomial.map_pow] using sq _ h.sq_abc
  · simpa only [Polynomial.map_add, Polynomial.map_pow] using ne _ h.ne_ab
  · simpa only [Polynomial.map_add, Polynomial.map_pow] using ne _ h.ne_ac
  · simpa only [Polynomial.map_add, Polynomial.map_pow] using ne _ h.ne_bc
  · simpa only [Polynomial.map_add, Polynomial.map_pow] using ne _ h.ne_abc

/-- Descent of "constant multiple" along a field extension. -/
theorem exists_C_mul_of_map (φ : K →+* L) {x y : K[X]} (hy : y ≠ 0) {μ : L}
    (h : x.map φ = C μ * y.map φ) : ∃ μ' : K, x = C μ' * y := by
  refine ⟨x.leadingCoeff / y.leadingCoeff, Polynomial.map_injective φ φ.injective ?_⟩
  have hly : φ y.leadingCoeff ≠ 0 :=
    (map_ne_zero φ).2 (leadingCoeff_ne_zero.2 hy)
  have hlc := congrArg leadingCoeff h
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_map, leadingCoeff_map] at hlc
  rw [Polynomial.map_mul, map_C, h, map_div₀, hlc, mul_div_cancel_right₀ _ hly]

theorem proportional_of_map (φ : K →+* L) {a b c : K[X]} (ha : a ≠ 0)
    (h : Proportional (a.map φ) (b.map φ) (c.map φ)) : Proportional a b c := by
  obtain ⟨q, α, β, γ, h1, h2, h3⟩ := h
  have hα : α ≠ 0 := by
    rintro rfl
    rw [C_0, zero_mul] at h1
    exact (Polynomial.map_ne_zero_iff φ.injective).2 ha h1
  have key : ∀ {x : K[X]} {β : L}, x.map φ = C β * q → ∃ μ' : K, x = C μ' * a := by
    intro x β hx
    refine exists_C_mul_of_map φ ha (μ := β / α) ?_
    rw [hx, h1, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hα]
  obtain ⟨β', hb⟩ := key h2
  obtain ⟨γ', hc⟩ := key h3
  exact ⟨a, 1, β', γ', by rw [C_1, one_mul], hb, hc⟩

end Map

/-- **Space diagonal with a single root, any field with `2 ≠ 0`** (via `AlgebraicClosure K`): a
nondegenerate cuboid with `g = α (X − r)ⁿ` is proportional. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_single_root_space_diag
    (h2 : (2 : K) ≠ 0) {α r : K} (hα : α ≠ 0) {n : ℕ} {a b c : K[X]} (h : IsNondegCuboid a b c)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = (C α * (X - C r) ^ n) ^ 2) : Proportional a b c := by
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : L) two_pos
  have h2L : (2 : L) ≠ 0 := by
    intro h0; apply h2; apply φ.injective; rw [map_ofNat, h0, map_zero]
  have hgL : (a.map φ) ^ 2 + (b.map φ) ^ 2 + (c.map φ) ^ 2 =
      (C (φ α) * (X - C (φ r)) ^ n) ^ 2 := by
    have := congrArg (Polynomial.map φ) hg
    simpa only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, map_C,
      Polynomial.map_sub, map_X] using this
  exact proportional_of_map φ h.ne_a
    ((isNondegCuboid_map φ h).proportional_of_irreducible_pow_space_diag h2L hi
      (irreducible_X_sub_C (φ r)) ((map_ne_zero φ).2 hα) hgL)

/-! ## Algebraically closed fields: at most one distinct root -/

/-- Over an algebraically closed field, a nonzero polynomial with at most one distinct root is
`α (X − r)ᵐ`. -/
theorem exists_single_root_form [IsAlgClosed K] [DecidableEq K] {a : K[X]} (ha : a ≠ 0)
    (hcard : a.roots.toFinset.card ≤ 1) :
    ∃ α : K, α ≠ 0 ∧ ∃ (m : ℕ) (r : K), a = C α * (X - C r) ^ m := by
  have hroots := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := a))
  obtain ⟨r, hr⟩ : ∃ r : K, ∀ x ∈ a.roots, x = r := by
    by_cases h0 : a.roots = 0
    · exact ⟨0, by simp [h0]⟩
    · obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero h0
      exact ⟨r, fun x hx => Finset.card_le_one.1 hcard x (Multiset.mem_toFinset.2 hx) r
        (Multiset.mem_toFinset.2 hr)⟩
  have hrep := Multiset.eq_replicate_of_mem hr
  rw [hrep, Multiset.map_replicate, Multiset.prod_replicate] at hroots
  exact ⟨a.leadingCoeff, leadingCoeff_ne_zero.2 ha, _, r, hroots.symm⟩

/-- **Algebraically closed field (e.g. `ℂ`), `2 ≠ 0`: a nondegenerate cuboid with an edge having
at most one distinct root is proportional.** Equivalently, every edge of a nondegenerate
non-proportional cuboid has at least two distinct affine roots (`∞` is not counted; the
`ℙ¹`-invariant reading "the hyperplane `{a = 0}` meets the curve in at least three points of `ℙ¹`"
needs a Möbius reparametrisation, which is not formalised). -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_roots_card_le_one
    [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsNondegCuboid a b c)
    (ha : a.roots.toFinset.card ≤ 1) : Proportional a b c := by
  obtain ⟨α, hα, m, r, rfl⟩ := exists_single_root_form h.ne_a ha
  exact h.proportional_of_single_root_edge h2 hα

/-- **Algebraically closed field, `2 ≠ 0`: a nondegenerate cuboid whose space diagonal has at most
one distinct root is proportional.** -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_space_diag_roots_card_le_one
    [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0) {a b c g : K[X]} (h : IsNondegCuboid a b c)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (hg0 : g.roots.toFinset.card ≤ 1) :
    Proportional a b c := by
  have hg0' : g ≠ 0 := by
    rintro rfl; apply h.ne_abc; rw [hg]; ring
  obtain ⟨α, hα, m, r, rfl⟩ := exists_single_root_form hg0' hg0
  exact h.proportional_of_single_root_space_diag h2 hα hg

/-! ## `ℚ[X]` -/

/-- **`ℚ[X]`: a polynomial cuboid with an edge `α πⁿ` (`π` irreducible over `ℚ`) gives an integer
perfect cuboid.** -/
theorem _root_.PerfectCuboid.Poly.IsPolyCuboid.exists_isPerfectCuboid_of_irreducible_pow_edge
    {π : ℚ[X]} (hπ : Irreducible π) {α : ℚ} (hα : α ≠ 0) {n : ℕ} {b c : ℚ[X]}
    (h : Poly.IsPolyCuboid (C α * π ^ n) b c) : ∃ A B C : ℕ, IsPerfectCuboid A B C := by
  have hc := isCuboid_of_isPolyCuboid h
  obtain ⟨q, x, y, z, h1, h2, h3⟩ :=
    hc.proportional_of_irreducible_pow_edge not_isSquare_neg_one_rat (by norm_num) hπ hα
  exact h.exists_isPerfectCuboid_of_proportional h1 h2 h3

end PerfectCuboid.PolyPrimePowerEdge
