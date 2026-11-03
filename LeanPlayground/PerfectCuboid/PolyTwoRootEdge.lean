module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolyCharP
public import LeanPlayground.PerfectCuboid.PolyNegOne
public import LeanPlayground.PerfectCuboid.PolyGenusOne
public import LeanPlayground.PerfectCuboid.PolyPythagoras

/-! # Polynomial Korec II: coprime edges `α π^k` and `α (X − r)^j (X − s)^k`

Round 18, brief 2. `K` is a field with `¬ IsSquare (-1 : K)` and `2 ≠ 0` (ℚ, ordered fields,
`𝔽_p` with `p ≡ 3 (mod 4)`); cuboids are `PolyCharP.IsCuboid`.

* **Coprime splittings** (`isUnit_or_isUnit_of_mul_eq_C_mul_irreducible_pow`, `pair_split`,
  `coprime_splitting_irreducible`, `coprime_splitting_two_roots`): coprime `p q = α P^m Q^n`
  (`P, Q` irreducible) splits as `(1, P^m Q^n)`, `(P^m Q^n, 1)`, `(P^m, Q^n)` or `(Q^n, P^m)` up
  to constants.
* **Square lemmas** (any `K` with `2 ≠ 0`): `sq_eq_C_mul_sq_add_C` (`F² = A T² + D`, `T`
  nonconstant, `A ≠ 0` ⇒ `D = 0`) and the discriminant lemma `disc_of_sq` for an arbitrary
  nonconstant `W` (`F² = A W² + B W + D` ⇒ `B² = 4AD`).
* **(A) power of an irreducible.** `face_shape_irreducible_pow` (a leg coprime to `α π^k` is
  `(u π^{2k} − v)/2`, `uv = α²`), the (I,I) lemma `proportional_of_two_type_one` (two such legs
  are proportional), and the headline `IsCuboid.edge_coprime_ne_C_mul_irreducible_pow`: an edge
  coprime to both other edges is never `α π^k`, `k ≥ 1`. Brick level
  (`not_brick_irreducible_pow_coprime`, three face equations only) with the extra hypothesis
  `¬ IsSquare (2 : K)`: over `𝔽₇`, `π = X² + 1`, three-face solutions with `c = ± b` exist
  (`round18/code/b2/b2_irrpow.py`).
* **(B) two roots.** `IsCuboid.edge_coprime_ne_two_roots`: an edge coprime to both other edges
  is never `α (X − r)^j (X − s)^k` (`r ≠ s`, `j, k ≥ 1`). Proof (`core_two_irreducible`):
  `f = √(b² + c²)` is coprime to `a` (at a root `r`, `f(r)² = b(r)² + c(r)² ≠ 0`), and
  `g² = a² + f²`,
  so `b, c, f` are all legs coprime to `a`, each of type I (`2x = uW − v`, `W = Y^{2j} Z^{2k}`;
  `TypeOne`) or type II (`4x² = A P² + B Q² − 2α² P Q`, `P = Y^{2j}`, `Q = Z^{2k}`; `TypeTwo`).
  `f` and a leg both of type I: `4c² = (ρ² − u²) W² + (σ² − v²)`, impossible
  (`false_of_typeOne_typeOne`); mixed types: degrees (`deg f = max(deg b, deg c)`); all of type
  II: the `P Q`-coefficient of `4(b² + c² − f²) = 0` is `−2α² ≠ 0` (`quadratic_form_eq_zero`,
  `false_of_typeTwo`). The fourth equation enters through `g`. This is simpler than the brief's
  sketch (no (I,I) lemma and no Lagrange identity needed for (B)).
* **Stretch: two irreducibles** (`IsCuboid.edge_coprime_ne_two_irreducible`): the same for
  `a = α π₁^j π₂^k`, `π₁, π₂` coprime irreducibles, under the residue hypothesis
  `πᵢ ∣ x² + y² ⇒ πᵢ ∣ y` (`−1` is not a square in `K[X]/(πᵢ)`); for linear `πᵢ` it follows from
  `¬ IsSquare (-1 : K)` (`X_sub_C_dvd_sq_add_sq`).
* **`𝔽_p`, `p ≡ 3 (mod 4)`**: `zmod_edge_coprime_ne_C_mul_irreducible_pow`,
  `zmod_edge_coprime_ne_two_roots`.

Hypotheses are needed: the 𝔽₅ coprime cuboid and the Frobenius cuboids have `√−1 ∈ K`; the
𝔽₇ cuboid (`PolyNegOne.isCuboid_seven`) has no edge coprime to both others. Not proved: the
non-coprime cases, edges with three or more distinct irreducible factors, and (stretch) two
irreducible factors without the residue hypothesis.
-/

@[expose] public section

open Polynomial

namespace PerfectCuboid.PolyTwoRootEdge

open PolyCharP

variable {K : Type*} [Field K]

/-! ## Coprime splittings -/

/-- Coprime splitting of `α π^n`, `π` irreducible: one factor is a unit. -/
theorem isUnit_or_isUnit_of_mul_eq_C_mul_irreducible_pow {π p q : K[X]} (hπ : Irreducible π)
    {α : K} (hα : α ≠ 0) {n : ℕ} (hpq : IsCoprime p q) (h : p * q = C α * π ^ n) :
    IsUnit p ∨ IsUnit q := by
  have hcu : IsUnit (C α) := isUnit_C.mpr (Ne.isUnit hα)
  have key : ∀ p q : K[X], p * q = C α * π ^ n → ¬ π ∣ p → IsUnit p := by
    intro p q h hX
    have h1 : IsCoprime (π ^ n) p := ((hπ.coprime_iff_not_dvd).mpr hX).pow_left
    have h2 : p ∣ π ^ n * C α := ⟨q, by rw [h, mul_comm]⟩
    exact isUnit_of_dvd_unit (h1.symm.dvd_of_dvd_mul_left h2) hcu
  by_cases hp : π ∣ p
  · by_cases hq : π ∣ q
    · exact absurd (hpq.isUnit_of_dvd' hp hq) hπ.not_isUnit
    · exact Or.inr (key q p (by rw [mul_comm]; exact h) hq)
  · exact Or.inl (key p q h hp)

/-- Pair lemma: `p q = α X₁ X₂`, `p ⊥ X₂`, `q ⊥ X₁` ⇒ `p = u X₁`, `q = (α/u) X₂`. -/
theorem pair_split {p q X₁ X₂ : K[X]} {α : K} (hα : α ≠ 0) (hX : X₁ * X₂ ≠ 0)
    (hp : IsCoprime p X₂) (hq : IsCoprime q X₁) (h : p * q = C α * (X₁ * X₂)) :
    ∃ u : K, u ≠ 0 ∧ p = C u * X₁ ∧ q = C (α / u) * X₂ := by
  have hcu : IsUnit (C α) := isUnit_C.mpr (Ne.isUnit hα)
  have hp1 : p ∣ X₁ := by
    have : p ∣ X₂ * (C α * X₁) := ⟨q, by rw [h]; ring⟩
    exact (hcu.dvd_mul_left).mp (hp.dvd_of_dvd_mul_left this)
  have hq1 : q ∣ X₂ := by
    have : q ∣ X₁ * (C α * X₂) := ⟨p, by rw [← mul_assoc, mul_comm X₁, mul_assoc, ← h]; ring⟩
    exact (hcu.dvd_mul_left).mp (hq.dvd_of_dvd_mul_left this)
  obtain ⟨p', hp'⟩ := hp1
  obtain ⟨q', hq'⟩ := hq1
  have hpq0 : p * q ≠ 0 := by
    intro h0; apply hX; rw [hp', hq']; linear_combination (p' * q') * h0
  have h1 : C α * p' * q' = 1 := by
    have : p * q * (C α * p' * q' - 1) = 0 := by rw [hp', hq'] at h; linear_combination -h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hpq0
    · exact sub_eq_zero.mp h0
  have hu' : IsUnit p' := isUnit_of_mul_isUnit_left
    (show IsUnit (p' * (C α * q')) by
      rw [show p' * (C α * q') = 1 by linear_combination h1]; exact isUnit_one)
  obtain ⟨w, hw, hCw⟩ := Polynomial.isUnit_iff.mp hu'
  have hw0 := hw.ne_zero
  refine ⟨w⁻¹, inv_ne_zero hw0, ?_, ?_⟩
  · rw [hp', ← hCw]
    have : C w⁻¹ * C w = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hw0, C_1]
    linear_combination (-p) * this
  · rw [hq', div_inv_eq_mul]
    have : q' * C (α * w) = 1 := by rw [C_mul, hCw]; linear_combination h1
    linear_combination (-q) * this

/-- **Coprime splitting of `α P^m Q^n`** for coprime irreducibles `P, Q`. -/
theorem coprime_splitting_irreducible {P Q : K[X]} (hP : Irreducible P) (hQ : Irreducible Q)
    {α : K} (hα : α ≠ 0) {m n : ℕ} {p q : K[X]} (hpq : IsCoprime p q)
    (h : p * q = C α * P ^ m * Q ^ n) :
    (∃ u : K, u ≠ 0 ∧ p = C u ∧ q = C (α / u) * P ^ m * Q ^ n) ∨
    (∃ u : K, u ≠ 0 ∧ p = C u * P ^ m * Q ^ n ∧ q = C (α / u)) ∨
    (∃ u : K, u ≠ 0 ∧ p = C u * P ^ m ∧ q = C (α / u) * Q ^ n) ∨
    (∃ u : K, u ≠ 0 ∧ p = C u * Q ^ n ∧ q = C (α / u) * P ^ m) := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hPm : P ^ m ≠ 0 := pow_ne_zero _ hP0
  have hQn : Q ^ n ≠ 0 := pow_ne_zero _ hQ0
  have cop : ∀ {R x : K[X]} {e : ℕ}, Irreducible R → ¬ R ∣ x → IsCoprime x (R ^ e) :=
    fun hR hx => ((hR.coprime_iff_not_dvd).mpr hx).pow_left.symm
  have notboth : ∀ {R : K[X]}, Irreducible R → R ∣ p → ¬ R ∣ q :=
    fun hR h1 h2 => hR.not_isUnit (hpq.isUnit_of_dvd' h1 h2)
  by_cases hPp : P ∣ p <;> by_cases hQp : Q ∣ p
  · -- p ∼ P^m Q^n
    right; left
    have hq : IsCoprime q (P ^ m * Q ^ n) :=
      (cop hP (notboth hP hPp)).mul_right (cop hQ (notboth hQ hQp))
    obtain ⟨u, hu, h1, h2⟩ := pair_split (X₁ := P ^ m * Q ^ n) (X₂ := 1) hα
      (by simpa using mul_ne_zero hPm hQn) isCoprime_one_right hq (by rw [h]; ring)
    exact ⟨u, hu, by rw [h1]; ring, by rw [h2, mul_one]⟩
  · -- p ∼ P^m, q ∼ Q^n
    right; right; left
    obtain ⟨u, hu, h1, h2⟩ := pair_split (X₁ := P ^ m) (X₂ := Q ^ n) hα (mul_ne_zero hPm hQn)
      (cop hQ hQp) (cop hP (notboth hP hPp)) (by rw [h]; ring)
    exact ⟨u, hu, h1, h2⟩
  · -- p ∼ Q^n, q ∼ P^m
    right; right; right
    obtain ⟨u, hu, h1, h2⟩ := pair_split (X₁ := Q ^ n) (X₂ := P ^ m) hα (mul_ne_zero hQn hPm)
      (cop hP hPp) (cop hQ (notboth hQ hQp)) (by rw [h]; ring)
    exact ⟨u, hu, h1, h2⟩
  · -- p a unit
    left
    obtain ⟨u, hu, h1, h2⟩ := pair_split (X₁ := 1) (X₂ := P ^ m * Q ^ n) hα
      (by simpa using mul_ne_zero hPm hQn) ((cop hP hPp).mul_right (cop hQ hQp))
      isCoprime_one_right (by rw [h]; ring)
    exact ⟨u, hu, by rw [h1, mul_one], by rw [h2]; ring⟩

theorem isCoprime_of_isUnit_left' {x y : K[X]} (hu : IsUnit x) : IsCoprime x y :=
  ⟨↑hu.unit⁻¹, 0, by simp⟩

/-! ## Square lemmas over `K[X]` -/

theorem C_two_eq : (C (2 : K) : K[X]) = 2 := map_ofNat C 2

/-- `F² = A T² + D` with `T` nonconstant and `A ≠ 0` forces `D = 0` (any field with `2 ≠ 0`). -/
theorem sq_eq_C_mul_sq_add_C (h2 : (2 : K) ≠ 0) {F T : K[X]} (hT : 0 < T.natDegree) {A D : K}
    (hA : A ≠ 0) (h : F ^ 2 = C A * T ^ 2 + C D) : D = 0 := by
  by_contra hD
  have hT0 : T ≠ 0 := ne_zero_of_natDegree_gt hT
  have hdeg : (C D).degree < (C A * T ^ 2).degree := by
    refine lt_of_le_of_lt degree_C_le ?_
    rw [← natDegree_pos_iff_degree_pos, natDegree_C_mul hA, natDegree_pow]
    omega
  have hlc : F.leadingCoeff ^ 2 = A * T.leadingCoeff ^ 2 := by
    have := congrArg leadingCoeff h
    rwa [leadingCoeff_pow, leadingCoeff_add_of_degree_lt' hdeg, leadingCoeff_mul, leadingCoeff_C,
      leadingCoeff_pow] at this
  have hlT : T.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hT0
  set l := F.leadingCoeff / T.leadingCoeff with hl_def
  have hl : l ^ 2 = A := by rw [hl_def, div_pow, hlc]; field_simp
  have hl0 : l ≠ 0 := by rintro h0; rw [h0] at hl; exact hA (by rw [← hl]; ring)
  have hfac : (F - C l * T) * (F + C l * T) = C D := by
    have : C l ^ 2 = C A := by rw [← C_pow, hl]
    linear_combination h - T ^ 2 * this
  have hu : IsUnit (C D : K[X]) := isUnit_C.mpr (Ne.isUnit hD)
  rw [← hfac] at hu
  have e1 := natDegree_eq_zero_of_isUnit (isUnit_of_mul_isUnit_left hu)
  have e2 := natDegree_eq_zero_of_isUnit (isUnit_of_mul_isUnit_right hu)
  have : (C (2 * l) * T).natDegree = 0 := by
    have e : C (2 * l) * T = (F + C l * T) - (F - C l * T) := by rw [C_mul, C_two_eq]; ring
    rw [e]
    exact Nat.le_zero.mp ((natDegree_sub_le _ _).trans (by rw [e1, e2]; rfl))
  rw [natDegree_C_mul (mul_ne_zero h2 hl0)] at this
  omega

/-- **Discriminant lemma** for an arbitrary nonconstant `W`: if `A W² + B W + D` is a square
(`A ≠ 0`), then `B² = 4 A D`. -/
theorem disc_of_sq (h2 : (2 : K) ≠ 0) {F W : K[X]} (hW : 0 < W.natDegree) {A B D : K}
    (hA : A ≠ 0) (h : F ^ 2 = C A * W ^ 2 + C B * W + C D) : B ^ 2 = 4 * A * D := by
  have h4A : 4 * A ≠ 0 := mul_ne_zero (PolyNegOne.four_ne_zero' h2) hA
  have hT : 0 < (C (2 * A) * W + C B).natDegree := by
    rw [natDegree_add_C, natDegree_C_mul (mul_ne_zero h2 hA)]; exact hW
  have e : (4 * A)⁻¹ * (4 * A) = 1 := inv_mul_cancel₀ h4A
  have e' : C (4 * A)⁻¹ * C (4 * A) = (1 : K[X]) := by rw [← C_mul, e, C_1]
  have key := sq_eq_C_mul_sq_add_C h2 hT (inv_ne_zero h4A)
    (D := (4 * A)⁻¹ * (4 * A * D - B ^ 2)) (F := F) (by
      rw [h]
      simp only [map_mul, map_sub, map_pow, map_ofNat] at e' ⊢
      linear_combination (-(C A * W ^ 2 + C B * W + C D)) * e')
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 (inv_ne_zero h4A)
  · linear_combination -h0

/-! ## (A): an edge `α π^k` coprime to the other two -/

/-- (A) Type I face shape: a leg coprime to `α π^k` is `(u π^{2k} − v)/2` with `u v = α²`. The
diagonal is `± (u π^{2k} + v)/2` (the sign depends on the orientation of the splitting). -/
theorem face_shape_irreducible_pow (h2 : (2 : K) ≠ 0) {π : K[X]} (hπ : Irreducible π) {α : K}
    (hα : α ≠ 0) {k : ℕ} {b d : K[X]} (hab : IsCoprime (C α * π ^ k) b)
    (h : (C α * π ^ k) ^ 2 + b ^ 2 = d ^ 2) :
    ∃ u v : K, u ≠ 0 ∧ v ≠ 0 ∧ u * v = α ^ 2 ∧ C 2 * b = C u * π ^ (2 * k) - C v ∧
      (C 2 * d = C u * π ^ (2 * k) + C v ∨ C 2 * d = -(C u * π ^ (2 * k) + C v)) := by
  have hcop := PolyNegOne.isCoprime_sub_add h2 hab h
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero _ hα
  have hprod : (d - b) * (d + b) = C (α ^ 2) * (1 * π ^ (2 * k)) := by
    rw [C_pow]; linear_combination -h
  have hW : (1 : K[X]) * π ^ (2 * k) ≠ 0 := by simpa using pow_ne_zero _ hπ.ne_zero
  rw [C_two_eq]
  rcases isUnit_or_isUnit_of_mul_eq_C_mul_irreducible_pow hπ hα2 hcop
    (by rw [hprod, one_mul]) with hu | hu
  · obtain ⟨u, hu0, h1, h2'⟩ := pair_split hα2 hW (isCoprime_of_isUnit_left' hu)
      isCoprime_one_right hprod
    refine ⟨α ^ 2 / u, u, div_ne_zero hα2 hu0, hu0, div_mul_cancel₀ _ hu0, ?_, Or.inl ?_⟩
    · linear_combination h2' - h1
    · linear_combination h2' + h1
  · have hprod' : (d - b) * (d + b) = C (α ^ 2) * (π ^ (2 * k) * 1) := by
      rw [hprod]; ring
    obtain ⟨u, hu0, h1, h2'⟩ := pair_split hα2 (by simpa using hW) isCoprime_one_right
      (isCoprime_of_isUnit_left' hu) hprod'
    refine ⟨-u, -(α ^ 2 / u), neg_ne_zero.mpr hu0, neg_ne_zero.mpr (div_ne_zero hα2 hu0),
      by field_simp, ?_, Or.inr ?_⟩
    · simp only [map_neg]; linear_combination h2' - h1
    · simp only [map_neg]; linear_combination h2' + h1

/-- **(I,I) lemma.** Two legs `b = (u W − v)/2`, `c = (u' W − v')/2` (`W` nonconstant) with
`b² + c²` a square force `c = μ b`. Uses `¬ IsSquare (-1)` only for `u² + u'² ≠ 0`. -/
theorem proportional_of_two_type_one (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0)
    {W b c f : K[X]} (hW : 0 < W.natDegree) {u v u' v' : K}
    (hu : u ≠ 0) (_hv : v ≠ 0) (hu' : u' ≠ 0) (_hv' : v' ≠ 0)
    (hb : C 2 * b = C u * W - C v) (hc : C 2 * c = C u' * W - C v') (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    ∃ μ : K, c = C μ * b := by
  rw [C_two_eq] at hb hc
  have hF : (2 * f) ^ 2 = C (u ^ 2 + u' ^ 2) * W ^ 2 + C (-(2 * (u * v + u' * v'))) * W +
      C (v ^ 2 + v' ^ 2) := by
    simp only [map_add, map_mul, map_neg, map_pow, map_ofNat]
    linear_combination (-4) * hf + (2 * b + (C u * W - C v)) * hb +
      (2 * c + (C u' * W - C v')) * hc
  have hA : u ^ 2 + u' ^ 2 ≠ 0 := PolyNegOne.sq_add_sq_ne_zero hK hu'
  have hd := disc_of_sq h2 hW hA hF
  have h4 : (4 : K) * (u * v' - u' * v) ^ 2 = 0 := by linear_combination -hd
  have h0 : u * v' = u' * v := by
    have := (mul_eq_zero.mp h4).resolve_left (PolyNegOne.four_ne_zero' h2)
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  refine ⟨u' / u, ?_⟩
  have e1 : C (u' / u) * C u = (C u' : K[X]) := by rw [← C_mul, div_mul_cancel₀ _ hu]
  have e2 : C (u' / u) * C v = (C v' : K[X]) := by
    rw [← C_mul]; congr 1; field_simp; linear_combination -h0
  have : (2 : K[X]) * (c - C (u' / u) * b) = 0 := by
    linear_combination hc - C (u' / u) * hb - W * e1 + e2
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (by rw [← C_two_eq] at h0; exact C_eq_zero.mp h0) h2
  · exact sub_eq_zero.mp h0

/-- Proportional edges with `a ⊥ b` force `a` constant. -/
theorem natDegree_eq_zero_of_proportional_of_coprime {a b c : K[X]} (h : Proportional a b c)
    (hab : IsCoprime a b) : a.natDegree = 0 := by
  obtain ⟨q, α₀, β₀, γ₀, ha, hb, -⟩ := h
  have hq : IsUnit q := hab.isUnit_of_dvd' ⟨C α₀, by rw [ha, mul_comm]⟩
    ⟨C β₀, by rw [hb, mul_comm]⟩
  rw [ha]
  exact Nat.le_zero.mp ((natDegree_C_mul_le _ _).trans (natDegree_eq_zero_of_isUnit hq).le)

theorem natDegree_C_mul_irreducible_pow_pos {π : K[X]} (hπ : Irreducible π) {α : K} (hα : α ≠ 0)
    {k : ℕ} (hk : 0 < k) : 0 < (C α * π ^ k).natDegree := by
  rw [natDegree_C_mul hα, natDegree_pow]
  exact Nat.mul_pos hk hπ.natDegree_pos

/-- **(A), cuboid level.** Over `K` with `−1 ∉ K²`, `2 ≠ 0`: an edge coprime to the other two
edges is never `α π^k` (`π` irreducible, `k ≥ 1`). -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.edge_coprime_ne_C_mul_irreducible_pow
    (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsCuboid a b c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) {π : K[X]} (hπ : Irreducible π) {α : K} {k : ℕ}
    (hk : 0 < k) : a ≠ C α * π ^ k := by
  rintro rfl
  have hα : α ≠ 0 := by rintro rfl; exact h.ne_a (by simp)
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨u, v, hu, hv, -, hb2, -⟩ :=
    face_shape_irreducible_pow h2 hπ hα hab (by rw [hd]; ring)
  obtain ⟨u', v', hu', hv', -, hc2, -⟩ :=
    face_shape_irreducible_pow h2 hπ hα hac (by rw [he]; ring)
  have hW : 0 < (π ^ (2 * k)).natDegree := by
    rw [natDegree_pow]; exact Nat.mul_pos (by omega) hπ.natDegree_pos
  obtain ⟨μ, hμ⟩ := proportional_of_two_type_one hK h2 hW hu hv hu' hv' hb2 hc2
    (by rw [hf]; ring)
  have := natDegree_eq_zero_of_proportional_of_coprime
    (h.proportional_of_two_edges h2 (Or.inr (Or.inr ⟨μ, hμ⟩))) hab
  have := natDegree_C_mul_irreducible_pow_pos hπ hα hk
  omega

/-- **(A), brick level** (only the three face equations; needs `¬ IsSquare 2` because of the
three-face solutions `c = ± b` with `b² + c² = 2 b²`, e.g. over `𝔽₇`). -/
theorem not_brick_irreducible_pow_coprime (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0)
    (h2sq : ¬ IsSquare (2 : K)) {a b c : K[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (sab : IsSquare (a ^ 2 + b ^ 2)) (sac : IsSquare (a ^ 2 + c ^ 2))
    (sbc : IsSquare (b ^ 2 + c ^ 2)) (hab : IsCoprime a b) (hac : IsCoprime a c)
    {π : K[X]} (hπ : Irreducible π) {α : K} {k : ℕ} (hk : 0 < k) : a ≠ C α * π ^ k := by
  rintro rfl
  have hα : α ≠ 0 := by rintro rfl; exact ha (by simp)
  obtain ⟨d, hd⟩ := sab
  obtain ⟨e, he⟩ := sac
  obtain ⟨f, hf⟩ := sbc
  obtain ⟨u, v, hu, hv, -, hb2, -⟩ :=
    face_shape_irreducible_pow h2 hπ hα hab (by rw [hd]; ring)
  obtain ⟨u', v', hu', hv', -, hc2, -⟩ :=
    face_shape_irreducible_pow h2 hπ hα hac (by rw [he]; ring)
  have hW : 0 < (π ^ (2 * k)).natDegree := by
    rw [natDegree_pow]; exact Nat.mul_pos (by omega) hπ.natDegree_pos
  obtain ⟨μ, rfl⟩ := proportional_of_two_type_one hK h2 hW hu hv hu' hv' hb2 hc2
    (by rw [hf]; ring)
  have hpos := natDegree_C_mul_irreducible_pow_pos hπ hα hk
  by_cases hμ1 : μ ^ 2 = 1
  · apply h2sq
    have e : C μ ^ 2 = (1 : K[X]) := by rw [← C_pow, hμ1, C_1]
    obtain ⟨ν, hν, -⟩ := PolyPythagoras.eq_C_mul_of_sq_eq (r := 2) hb
      (show f ^ 2 = C 2 * b ^ 2 by rw [C_two_eq]; linear_combination -hf + b ^ 2 * e)
    exact ⟨ν, by rw [← hν]; ring⟩
  · have hμ0 : μ ^ 2 ≠ 0 := by
      rintro h0
      have : μ = 0 := pow_eq_zero_iff two_ne_zero |>.mp h0
      subst this
      apply hpos.ne'
      have hcu : IsUnit (C α * π ^ k) := isCoprime_zero_right.mp (by simpa using hac)
      exact natDegree_eq_zero_of_isUnit hcu
    obtain ⟨l, hl⟩ := PolyGenusOne.two_forms_proportional h2 one_ne_zero hμ0 (Ne.symm hμ1) hb
      ⟨d, by rw [C_1, one_mul]; exact hd⟩ ⟨e, by rw [← he, C_pow]; ring⟩
    have hbu : IsUnit b := hab.isUnit_of_dvd' ⟨C l, by rw [hl, mul_comm]⟩ dvd_rfl
    have hb0 := natDegree_eq_zero_of_isUnit hbu
    have := (PolyNegOne.natDegree_eq_zero_of_leg h2 hb hb0
      (show b ^ 2 + (C α * π ^ k) ^ 2 = d ^ 2 by rw [sq d, ← hd]; ring)).1
    omega

/-! ## (B): an edge `α Y^j Z^k` coprime to the other two -/

/-- Type I leg relative to `W` (with `u v = β`): `2 x = u W − v`. -/
def TypeOne (W : K[X]) (β : K) (x : K[X]) : Prop :=
  ∃ u v : K, u ≠ 0 ∧ v ≠ 0 ∧ u * v = β ∧ 2 * x = C u * W - C v

/-- Type II leg relative to `(P, Q)`: `4 x² = A P² + B Q² − 2 β P Q` and `deg x ≤ max(deg P, deg Q)`
(this is what `2 x = v Q − u P` or `2 x = v P − u Q`, `u v = β`, gives). -/
def TypeTwo (P Q : K[X]) (β : K) (x : K[X]) : Prop :=
  (∃ A B : K, 4 * x ^ 2 = C A * P ^ 2 + C B * Q ^ 2 - C (2 * β) * (P * Q)) ∧
    x.natDegree ≤ max P.natDegree Q.natDegree

theorem typeTwo_of_eq (h2 : (2 : K) ≠ 0) {P Q x : K[X]} {u v β : K} (huv : u * v = β)
    (hx : 2 * x = C v * Q - C u * P) : TypeTwo P Q β x := by
  refine ⟨⟨u ^ 2, v ^ 2, ?_⟩, ?_⟩
  · have e : C u * C v = (C β : K[X]) := by rw [← C_mul, huv]
    simp only [map_mul, map_pow, map_ofNat]
    linear_combination (2 * x + (C v * Q - C u * P)) * hx - 2 * P * Q * e
  · have : (2 * x).natDegree = x.natDegree := by rw [← C_two_eq, natDegree_C_mul h2]
    rw [← this, hx]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans (le_max_right _ _)
    · exact (natDegree_C_mul_le _ _).trans (le_max_left _ _)

theorem TypeTwo.symm {P Q x : K[X]} {β : K} (h : TypeTwo P Q β x) : TypeTwo Q P β x := by
  obtain ⟨⟨A, B, e⟩, hd⟩ := h
  exact ⟨⟨B, A, by rw [e]; ring⟩, by rw [max_comm]; exact hd⟩

theorem TypeOne.natDegree_eq (h2 : (2 : K) ≠ 0) {W x : K[X]} {β : K} (h : TypeOne W β x) :
    x.natDegree = W.natDegree := by
  obtain ⟨u, v, hu, -, -, hx⟩ := h
  have : (2 * x).natDegree = x.natDegree := by rw [← C_two_eq, natDegree_C_mul h2]
  rw [← this, hx, natDegree_sub_C, natDegree_C_mul hu]

/-- **Leg shapes for `a = α Y^j Z^k`** (`Y, Z` irreducible): a leg coprime to `a` is of type I
relative to `W = Y^{2j} Z^{2k}` or of type II relative to `(Y^{2j}, Z^{2k})`. -/
theorem leg_shape_two (h2 : (2 : K) ≠ 0) {Y Z : K[X]} (hY : Irreducible Y) (hZ : Irreducible Z)
    {α : K} (hα : α ≠ 0) {j k : ℕ} {x d : K[X]} (hax : IsCoprime (C α * Y ^ j * Z ^ k) x)
    (h : (C α * Y ^ j * Z ^ k) ^ 2 + x ^ 2 = d ^ 2) :
    TypeOne (Y ^ (2 * j) * Z ^ (2 * k)) (α ^ 2) x ∨
      TypeTwo (Y ^ (2 * j)) (Z ^ (2 * k)) (α ^ 2) x := by
  have hcop := PolyNegOne.isCoprime_sub_add h2 hax h
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero _ hα
  have hprod : (d - x) * (d + x) = C (α ^ 2) * Y ^ (2 * j) * Z ^ (2 * k) := by
    rw [C_pow]; linear_combination -h
  rcases coprime_splitting_irreducible hY hZ hα2 hcop hprod with
    ⟨u, hu, h1, h2'⟩ | ⟨u, hu, h1, h2'⟩ | ⟨u, hu, h1, h2'⟩ | ⟨u, hu, h1, h2'⟩
  · left
    exact ⟨α ^ 2 / u, u, div_ne_zero hα2 hu, hu, div_mul_cancel₀ _ hu,
      by linear_combination h2' - h1⟩
  · left
    refine ⟨-u, -(α ^ 2 / u), neg_ne_zero.mpr hu, neg_ne_zero.mpr (div_ne_zero hα2 hu),
      by field_simp, ?_⟩
    simp only [map_neg]; linear_combination h2' - h1
  · right
    exact typeTwo_of_eq h2 (u := u) (v := α ^ 2 / u) (by field_simp)
      (by linear_combination h2' - h1)
  · right
    exact (typeTwo_of_eq h2 (u := u) (v := α ^ 2 / u) (by field_simp)
      (by linear_combination h2' - h1)).symm

/-- A leg and the hypotenuse both of type I relative to the same nonconstant `W`, with the
other leg coprime to `W`: impossible. -/
theorem false_of_typeOne_typeOne (h2 : (2 : K) ≠ 0) {W b c f : K[X]} (hW : 0 < W.natDegree)
    {β : K} (hcW : IsCoprime W c) (hb : TypeOne W β b) (hf : TypeOne W β f)
    (h : b ^ 2 + c ^ 2 = f ^ 2) : False := by
  obtain ⟨u, v, hu, hv, huv, hb2⟩ := hb
  obtain ⟨ρ, σ, hρ, hσ, hρσ, hf2⟩ := hf
  have hW0 : W ≠ 0 := ne_zero_of_natDegree_gt hW
  have hWu : ¬ IsUnit W := fun hu => by
    have := natDegree_eq_zero_of_isUnit hu; omega
  have e1 : C ρ * C σ = (C u * C v : K[X]) := by rw [← C_mul, ← C_mul, hρσ, huv]
  have key : (2 * c) ^ 2 = C (ρ ^ 2 - u ^ 2) * W ^ 2 + C (σ ^ 2 - v ^ 2) := by
    simp only [map_sub, map_pow]
    linear_combination 4 * h + (2 * f + (C ρ * W - C σ)) * hf2 -
      (2 * b + (C u * W - C v)) * hb2 - 2 * W * e1
  by_cases hρu : ρ ^ 2 - u ^ 2 = 0
  · have hσv : σ ^ 2 - v ^ 2 = 0 := by
      have hρ2 : ρ ^ 2 = u ^ 2 := sub_eq_zero.mp hρu
      have : ρ ^ 2 * (σ ^ 2 - v ^ 2) = 0 := by
        linear_combination (ρ * σ + u * v) * (hρσ.trans huv.symm) - v ^ 2 * hρ2
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hρ)
    rw [hρu, hσv, C_0, zero_mul, zero_add] at key
    have hc : c = 0 := by
      have := pow_eq_zero_iff two_ne_zero |>.mp key
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (by rw [← C_two_eq] at h0; exact C_eq_zero.mp h0) h2
      · exact h0
    exact hWu (isCoprime_zero_right.mp (hc ▸ hcW))
  · have hD := sq_eq_C_mul_sq_add_C h2 hW hρu key
    rw [hD, C_0, add_zero] at key
    obtain ⟨μ, hμ⟩ := PolyGenusOne.exists_C_mul_of_sq_eq hW0 key
    have : IsCoprime W (2 * c) := by
      rw [← C_two_eq]
      exact (isCoprime_mul_unit_left_right (isUnit_C.mpr (Ne.isUnit h2)) W c).mpr hcW
    rw [hμ] at this
    exact hWu (this.isUnit_of_dvd' dvd_rfl (dvd_mul_left _ _))

/-- **Injectivity of binary quadratic forms** in coprime nonconstant `P, Q`. -/
theorem quadratic_form_eq_zero {P Q : K[X]} (hP : 0 < P.natDegree) (hQ : 0 < Q.natDegree)
    (hPQ : IsCoprime P Q) {A B D : K} (h : C A * P ^ 2 + C B * (P * Q) + C D * Q ^ 2 = 0) :
    A = 0 ∧ B = 0 ∧ D = 0 := by
  have nu : ∀ {R : K[X]}, 0 < R.natDegree → ∀ {t : K}, R ∣ C t → t = 0 := by
    intro R hR t hRt
    by_contra ht
    have := natDegree_eq_zero_of_isUnit (isUnit_of_dvd_unit hRt (isUnit_C.mpr (Ne.isUnit ht)))
    omega
  have hD : D = 0 := nu hP ((hPQ.pow_right (n := 2)).dvd_of_dvd_mul_right
    ⟨-(C A * P + C B * Q), by linear_combination h⟩)
  have hA : A = 0 := nu hQ ((hPQ.symm.pow_right (n := 2)).dvd_of_dvd_mul_right
    ⟨-(C B * P + C D * Q), by linear_combination h⟩)
  refine ⟨hA, ?_, hD⟩
  rw [hA, hD, C_0] at h
  have hPQ0 : P * Q ≠ 0 :=
    mul_ne_zero (ne_zero_of_natDegree_gt hP) (ne_zero_of_natDegree_gt hQ)
  have : C B * (P * Q) = 0 := by linear_combination h
  exact C_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hPQ0)

/-- Three legs of type II with `b² + c² = f²`: impossible (the `P Q` coefficient is `−2β ≠ 0`). -/
theorem false_of_typeTwo (h2 : (2 : K) ≠ 0) {P Q b c f : K[X]} (hP : 0 < P.natDegree)
    (hQ : 0 < Q.natDegree) (hPQ : IsCoprime P Q) {β : K} (hβ : β ≠ 0) (hb : TypeTwo P Q β b)
    (hc : TypeTwo P Q β c) (hf : TypeTwo P Q β f) (h : b ^ 2 + c ^ 2 = f ^ 2) : False := by
  obtain ⟨⟨A₁, B₁, e₁⟩, -⟩ := hb
  obtain ⟨⟨A₂, B₂, e₂⟩, -⟩ := hc
  obtain ⟨⟨A₃, B₃, e₃⟩, -⟩ := hf
  have := quadratic_form_eq_zero hP hQ hPQ (A := A₁ + A₂ - A₃) (B := -(2 * β))
    (D := B₁ + B₂ - B₃) (by
      simp only [map_add, map_sub, map_neg, map_mul, map_ofNat] at e₁ e₂ e₃ ⊢
      linear_combination -e₁ - e₂ + e₃ + 4 * h)
  exact hβ (by have := this.2.1; rw [neg_eq_zero] at this;
                exact (mul_eq_zero.mp this).resolve_left h2)

/-- **Core of (B)** for two coprime irreducibles: if the three legs `b, c, f` (with
`b² + c² = f²`) are all coprime to `a = α Y^j Z^k` and each completes `a` to a right triangle,
contradiction. -/
theorem core_two_irreducible (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {Y Z : K[X]}
    (hY : Irreducible Y) (hZ : Irreducible Z) (hYZ : IsCoprime Y Z) {α : K} (hα : α ≠ 0)
    {j k : ℕ} (hj : 0 < j) (hk : 0 < k) {b c f d e g : K[X]} (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : IsCoprime (C α * Y ^ j * Z ^ k) b) (hac : IsCoprime (C α * Y ^ j * Z ^ k) c)
    (haf : IsCoprime (C α * Y ^ j * Z ^ k) f)
    (hd : (C α * Y ^ j * Z ^ k) ^ 2 + b ^ 2 = d ^ 2)
    (he : (C α * Y ^ j * Z ^ k) ^ 2 + c ^ 2 = e ^ 2)
    (hg : (C α * Y ^ j * Z ^ k) ^ 2 + f ^ 2 = g ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) : False := by
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero _ hα
  have hP : (Y ^ (2 * j)).natDegree = 2 * j * Y.natDegree := natDegree_pow _ _
  have hQ : (Z ^ (2 * k)).natDegree = 2 * k * Z.natDegree := natDegree_pow _ _
  have hYd := hY.natDegree_pos
  have hZd := hZ.natDegree_pos
  have hP0 : 0 < (Y ^ (2 * j)).natDegree := by rw [hP]; positivity
  have hQ0 : 0 < (Z ^ (2 * k)).natDegree := by rw [hQ]; positivity
  have hW : (Y ^ (2 * j) * Z ^ (2 * k)).natDegree = 2 * j * Y.natDegree + 2 * k * Z.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ hY.ne_zero) (pow_ne_zero _ hZ.ne_zero), hP, hQ]
  have hW0 : 0 < (Y ^ (2 * j) * Z ^ (2 * k)).natDegree := by rw [hW]; positivity
  have hsq : (C α * Y ^ j * Z ^ k) ^ 2 = C (α ^ 2) * (Y ^ (2 * j) * Z ^ (2 * k)) := by
    rw [C_pow]; ring
  have copW : ∀ {x : K[X]}, IsCoprime (C α * Y ^ j * Z ^ k) x →
      IsCoprime (Y ^ (2 * j) * Z ^ (2 * k)) x := fun hx => by
    have := hx.pow_left (m := 2)
    rw [hsq] at this
    exact this.of_mul_left_right
  have hPQ : IsCoprime (Y ^ (2 * j)) (Z ^ (2 * k)) := hYZ.pow
  have Lb := leg_shape_two h2 hY hZ hα hab hd
  have Lc := leg_shape_two h2 hY hZ hα hac he
  have Lf := leg_shape_two h2 hY hZ hα haf hg
  have hdeg := PolyNegOne.natDegree_hyp hK hb0 hc0 hf
  rcases Lf with Ff | Ff
  · rcases Lb with Fb | Fb
    · exact false_of_typeOne_typeOne h2 hW0 (copW hac) Fb Ff hf
    rcases Lc with Fc | Fc
    · exact false_of_typeOne_typeOne h2 hW0 (copW hab) Fc Ff (by linear_combination hf)
    · have := Ff.natDegree_eq h2
      have := Fb.2
      have := Fc.2
      rw [hP, hQ] at *
      omega
  · rcases Lb with Fb | Fb
    · have := Fb.natDegree_eq h2
      have := Ff.2
      rw [hP, hQ] at *
      omega
    rcases Lc with Fc | Fc
    · have := Fc.natDegree_eq h2
      have := Ff.2
      rw [hP, hQ] at *
      omega
    · exact false_of_typeTwo h2 hP0 hQ0 hPQ hα2 Fb Fc Ff hf

/-- **(B) for two irreducibles** (stretch): `a = α π₁^j π₂^k` with `π₁, π₂` coprime irreducibles
such that `−1` is not a square modulo `πᵢ` (`πᵢ ∣ x² + y² ⇒ πᵢ ∣ y`). Then `a` is not coprime to
both other edges. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.edge_coprime_ne_two_irreducible
    (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsCuboid a b c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) {π₁ π₂ : K[X]} (hπ₁ : Irreducible π₁)
    (hπ₂ : Irreducible π₂) (hπ : IsCoprime π₁ π₂)
    (hres₁ : ∀ x y : K[X], π₁ ∣ x ^ 2 + y ^ 2 → π₁ ∣ y)
    (hres₂ : ∀ x y : K[X], π₂ ∣ x ^ 2 + y ^ 2 → π₂ ∣ y) {α : K} {j k : ℕ} (hj : 0 < j)
    (hk : 0 < k) : a ≠ C α * π₁ ^ j * π₂ ^ k := by
  rintro rfl
  have hα : α ≠ 0 := by rintro rfl; exact h.ne_a (by simp)
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  have cop : ∀ {π : K[X]}, Irreducible π → (∀ x y : K[X], π ∣ x ^ 2 + y ^ 2 → π ∣ y) →
      π ∣ C α * π₁ ^ j * π₂ ^ k → IsCoprime π f := by
    intro π hπ hres hπa
    refine (hπ.coprime_iff_not_dvd).mpr fun hπf => hπ.not_isUnit (hab.isUnit_of_dvd' hπa ?_)
    exact hres c b (by rw [add_comm, hf]; exact dvd_mul_of_dvd_left hπf f)
  have h1 : π₁ ∣ C α * π₁ ^ j * π₂ ^ k :=
    ((dvd_pow_self π₁ hj.ne').mul_left _).mul_right _
  have h2' : π₂ ∣ C α * π₁ ^ j * π₂ ^ k := (dvd_pow_self π₂ hk.ne').mul_left _
  have haf : IsCoprime (C α * π₁ ^ j * π₂ ^ k) f :=
    (((isCoprime_mul_unit_left_left (isUnit_C.mpr (Ne.isUnit hα)) _ _).mpr
      (cop hπ₁ hres₁ h1).pow_left).mul_left (cop hπ₂ hres₂ h2').pow_left)
  exact core_two_irreducible hK h2 hπ₁ hπ₂ hπ hα hj hk h.ne_b h.ne_c hab hac haf
    (by rw [hd]; ring) (by rw [he]; ring) (g := g) (by linear_combination hg - hf)
    (by rw [hf]; ring)

/-- If `−1 ∉ K²`, then `−1` is not a square modulo `X − r`. -/
theorem X_sub_C_dvd_sq_add_sq (hK : ¬ IsSquare (-1 : K)) (r : K) (x y : K[X])
    (h : X - C r ∣ x ^ 2 + y ^ 2) : X - C r ∣ y := by
  rw [dvd_iff_isRoot, IsRoot.def] at h ⊢
  by_contra hy
  apply PolyNegOne.sq_add_sq_ne_zero hK (u := x.eval r) hy
  simpa using h

theorem isCoprime_X_sub_C_X_sub_C {r s : K} (hrs : r ≠ s) : IsCoprime (X - C r) (X - C s) := by
  refine ((irreducible_X_sub_C r).coprime_iff_not_dvd).mpr ?_
  rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr hrs

/-- **(B) headline.** Over `K` with `−1 ∉ K²`, `2 ≠ 0`: an edge coprime to the other two edges
is never `α (X − r)^j (X − s)^k` with `r ≠ s`, `j, k ≥ 1`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.edge_coprime_ne_two_roots
    (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsCuboid a b c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) {α r s : K} (hrs : r ≠ s) {j k : ℕ}
    (hj : 0 < j) (hk : 0 < k) : a ≠ C α * (X - C r) ^ j * (X - C s) ^ k :=
  h.edge_coprime_ne_two_irreducible hK h2 hab hac (irreducible_X_sub_C r) (irreducible_X_sub_C s)
    (isCoprime_X_sub_C_X_sub_C hrs) (X_sub_C_dvd_sq_add_sq hK r) (X_sub_C_dvd_sq_add_sq hK s)
    hj hk

/-- Coprime splitting of `α (X − r)^m (X − s)^n`, `r ≠ s` (brief's statement). -/
theorem coprime_splitting_two_roots {r s : K} (_hrs : r ≠ s) {α : K} (hα : α ≠ 0) {m n : ℕ}
    {p q : K[X]} (hpq : IsCoprime p q) (h : p * q = C α * (X - C r) ^ m * (X - C s) ^ n) :
    (∃ u : K, u ≠ 0 ∧ p = C u ∧ q = C (α / u) * (X - C r) ^ m * (X - C s) ^ n) ∨
    (∃ u : K, u ≠ 0 ∧ p = C u * (X - C r) ^ m * (X - C s) ^ n ∧ q = C (α / u)) ∨
    (∃ u : K, u ≠ 0 ∧ p = C u * (X - C r) ^ m ∧ q = C (α / u) * (X - C s) ^ n) ∨
    (∃ u : K, u ≠ 0 ∧ p = C u * (X - C s) ^ n ∧ q = C (α / u) * (X - C r) ^ m) :=
  coprime_splitting_irreducible (irreducible_X_sub_C r) (irreducible_X_sub_C s) hα hpq h

/-! ## `𝔽_p`, `p ≡ 3 (mod 4)` -/

theorem zmod_edge_coprime_ne_C_mul_irreducible_pow {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {a b c : (ZMod p)[X]} (h : IsCuboid a b c) (hab : IsCoprime a b) (hac : IsCoprime a c)
    {π : (ZMod p)[X]} (hπ : Irreducible π) {α : ZMod p} {k : ℕ} (hk : 0 < k) :
    a ≠ C α * π ^ k :=
  h.edge_coprime_ne_C_mul_irreducible_pow (PolyNegOne.zmod_not_isSquare_neg_one hp)
    (PolyNegOne.zmod_two_ne_zero (by omega)) hab hac hπ hk

theorem zmod_edge_coprime_ne_two_roots {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {a b c : (ZMod p)[X]} (h : IsCuboid a b c) (hab : IsCoprime a b) (hac : IsCoprime a c)
    {α r s : ZMod p} (hrs : r ≠ s) {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    a ≠ C α * (X - C r) ^ j * (X - C s) ^ k :=
  h.edge_coprime_ne_two_roots (PolyNegOne.zmod_not_isSquare_neg_one hp)
    (PolyNegOne.zmod_two_ne_zero (by omega)) hab hac hrs hj hk

end PerfectCuboid.PolyTwoRootEdge
