module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolyCharP
public import LeanPlayground.PerfectCuboid.PolyNegOne

/-! # Nondegenerate cuboids with a linear edge are proportional (round 18, brief 3)

Round 17 (`PolyNegOne.IsCuboid.proportional_of_linear_edge`) proved "linear edge ⇒ proportional"
over fields with `¬ IsSquare (-1)`. Here that hypothesis is replaced by **nondegeneracy**
(`IsNondegCuboid`): over **every field with `2 ≠ 0`** (e.g. `ℂ`, `𝔽_p` with `p ≡ 1 (mod 4)`)

* `linear_leg_shape`: a right triangle `(α X)² + y² = z²` has `y = β X`, or
  `2y = v X² − u`, `2z = ±(v X² + u)` with `u v = α²`;
* `IsNondegCuboid.proportional_of_linear_edge`: `IsNondegCuboid (C α * X) b c ⇒ b = β X, c = γ X`;
* `IsNondegCuboid.proportional_of_natDegree_eq_one`: an edge of degree one forces `Proportional`
  (via the translation `isNondegCuboid_comp_X_add_C`);
* `zmod_nondeg_proportional_of_natDegree_le_one`: the same over `𝔽_p[X]`, `p` an odd prime;
* `IsNondegConstCuboid`, `isNondegCuboid_C_iff`, `not_isNondegConstCuboid_five`,
  `not_isNondegConstCuboid_thirteen` (kernel `decide`), and
  `no_nondeg_cuboid_natDegree_le_one_five/_thirteen`: over `𝔽₅[X]` and `𝔽₁₃[X]` every edge of
  a nondegenerate cuboid has degree `≥ 2`.

Case table of the main proof (`a = α X`; legs coprime to `X` have the shape `2b = vX² − u`):
* `b = βX, c = γX`: the conclusion.
* `b = βX` (`β ≠ 0`), `2c = v'X² − u'` (`mixed_case`): the discriminants of `4f²` and `4g²`
  (`PolyNegOne.quad_disc`) give `16β²(β² − α²) = 0` and `16β²(α² + β²) = 0`, so `32β⁴ = 0`.
  This case uses only `IsCuboid` (no nondegeneracy, no hypothesis on `−1`).
* `2b = vX² − u`, `2c = v'X² − u'` (`both_case`): if `v² + v'² ≠ 0` the discriminants of `4f²`
  and `4g²` give `16α⁴ = 4(v² + v'²)(u² + u'²) = 0`; if `v² + v'² = 0` then `u² + u'² = 0` and
  `4(a² + b² + c²) = 0`, contradicting `ne_abc`. This is the only use of nondegeneracy.

Stretch (`IsNondegCuboid.false_of_irreducible_pow_edge`, via `quad_disc_W`, the discriminant
lemma for `A W² + B W + D` with `W` nonconstant): over any field with `2 ≠ 0` there is no
nondegenerate cuboid `(α π^k, b, c)` (`π` irreducible, `k ≥ 1`) whose edge `α π^k` is coprime to
`b` and to `c`. (The `𝔽₅` pairwise-coprime cuboid `(X⁶ − 1, X + X⁵, 2(X⁶ + 1))` has no edge of
the form `α π^k`; the degenerate `(2X, X² − 1, i(X² + 1))` is excluded by `g ≠ 0`.) Superseded in
round 19 by `PolyPrimePowerEdge`: `IsNondegCuboid.proportional_of_irreducible_pow_edge` drops the
coprimality and concludes `Proportional` (which with `k ≥ 1` and coprimality is absurd).

Nondegeneracy is necessary: over any `K ∋ i`, `char K ≠ 2`, `(2X, X² − 1, i(X² + 1))` is a
(degenerate, `g = 0`) cuboid with a linear edge that is not proportional
(`PolyCharP.isCuboid_family`). The Frobenius cuboids over `𝔽₅, 𝔽₁₃` have no edge of degree
`≤ 1`, consistent with the theorem. Not proved here: monomial edges `α X^k`, `k ≥ 2`, without
`¬ IsSquare (-1)`.
-/

@[expose] public section

open Polynomial

namespace PerfectCuboid.PolyLinearNondeg

open PolyCharP

variable {K : Type*} [Field K]

/-! ## The shape of a leg opposite a linear leg -/

/-- Partners of a linear leg (any field, `2 ≠ 0`): `y = β X`, or `2y = v X² − u`,
`2z = ±(v X² + u)` with `u v = α²`. (The sign of `z` cannot be fixed, since `z` and `−z`
both satisfy the hypothesis.) -/
theorem linear_leg_shape (h2 : (2 : K) ≠ 0) {α : K} (hα : α ≠ 0) {y z : K[X]}
    (h : (C α * X) ^ 2 + y ^ 2 = z ^ 2) :
    (∃ β : K, y = C β * X) ∨ ∃ u v : K, u ≠ 0 ∧ v ≠ 0 ∧ u * v = α ^ 2 ∧
      C 2 * y = C v * X ^ 2 - C u ∧
      (C 2 * z = C v * X ^ 2 + C u ∨ C 2 * z = -(C v * X ^ 2 + C u)) := by
  by_cases hX : X ∣ y
  · exact Or.inl (PolyNegOne.linear_leg_of_X_dvd h2 hα h hX)
  right
  have hab := PolyNegOne.isCoprime_C_mul_X_of_not_dvd hα hX
  obtain ⟨u, v, huv, hy2⟩ := PolyNegOne.monomial_leg h2 hα hab (by rw [pow_one]; exact h)
  have hv : v ≠ 0 := by rintro rfl; rw [mul_zero] at huv; exact pow_ne_zero 2 hα huv.symm
  have hu : u ≠ 0 := by rintro rfl; rw [zero_mul] at huv; exact pow_ne_zero 2 hα huv.symm
  have hCuv : C u * C v = C α ^ 2 := by rw [← C_mul, huv, C_pow]
  refine ⟨u, v, hu, hv, huv, ?_, ?_⟩
  · rw [map_ofNat]; simpa using hy2
  · rw [map_ofNat]
    have hz : (2 * z - (C v * X ^ 2 + C u)) * (2 * z + (C v * X ^ 2 + C u)) = 0 := by
      linear_combination (-4) * h + (2 * y + (C v * X ^ (2 * 1) - C u)) * hy2 +
        (-4 * X ^ 2) * hCuv
    rcases mul_eq_zero.1 hz with h0 | h0
    · left; linear_combination h0
    · right; linear_combination h0

/-! ## The two non-trivial cases -/

theorem four_ne_zero_poly (h2 : (2 : K) ≠ 0) : (4 : K[X]) ≠ 0 := by
  rw [← map_ofNat C 4]
  exact C_ne_zero.2 (PolyNegOne.four_ne_zero' h2)

/-- Mixed case: `b = β X` (`β ≠ 0`) and `2c = v X² − u`. Only the faces `(b, c)` and the space
diagonal are used; no nondegeneracy and no hypothesis on `−1`. -/
theorem mixed_case (h2 : (2 : K) ≠ 0) {α β u v : K} {c f g : K[X]} (hβ : β ≠ 0) (hv : v ≠ 0)
    (huv : u * v = α ^ 2) (hc2 : C 2 * c = C v * X ^ 2 - C u)
    (hf : (C β * X) ^ 2 + c ^ 2 = f ^ 2) (hg : (C α * X) ^ 2 + (C β * X) ^ 2 + c ^ 2 = g ^ 2) :
    False := by
  rw [map_ofNat] at hc2
  have hCuv : C u * C v = C α ^ 2 := by rw [← C_mul, huv, C_pow]
  have keyg : (2 * g) ^ 2 = C (v ^ 2) * X ^ (2 * 2) + C (2 * α ^ 2 + 4 * β ^ 2) * X ^ 2 +
      C (u ^ 2) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    linear_combination (-4) * hg + (2 * c + (C v * X ^ 2 - C u)) * hc2 + (-2 * X ^ 2) * hCuv
  have keyf : (2 * f) ^ 2 = C (v ^ 2) * X ^ (2 * 2) + C (4 * β ^ 2 - 2 * α ^ 2) * X ^ 2 +
      C (u ^ 2) := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    linear_combination (-4) * hf + (2 * c + (C v * X ^ 2 - C u)) * hc2 + (-2 * X ^ 2) * hCuv
  have hdg := PolyNegOne.quad_disc h2 (by norm_num) (pow_ne_zero 2 hv) keyg
  have hdf := PolyNegOne.quad_disc h2 (by norm_num) (pow_ne_zero 2 hv) keyf
  have h1 : (u * v) ^ 2 = (α ^ 2) ^ 2 := by rw [huv]
  have h3 : (2 * 2 * 2 * 2 * 2) * β ^ 4 = 0 := by linear_combination hdg + hdf + 8 * h1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2) h2)
    (pow_ne_zero 4 hβ) h3

/-- Both legs coprime to `X`: `2b = v X² − u`, `2c = v' X² − u'`. Uses `a² + b² + c² ≠ 0`. -/
theorem both_case (h2 : (2 : K) ≠ 0) {α u v u' v' : K} {b c f g : K[X]} (hα : α ≠ 0)
    (hv : v ≠ 0) (hv' : v' ≠ 0) (huv : u * v = α ^ 2) (huv' : u' * v' = α ^ 2)
    (hb2 : C 2 * b = C v * X ^ 2 - C u) (hc2 : C 2 * c = C v' * X ^ 2 - C u')
    (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : (C α * X) ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    (hne : (C α * X) ^ 2 + b ^ 2 + c ^ 2 ≠ 0) : False := by
  rw [map_ofNat] at hb2 hc2
  have hCuv : C u * C v = C α ^ 2 := by rw [← C_mul, huv, C_pow]
  have hCuv' : C u' * C v' = C α ^ 2 := by rw [← C_mul, huv', C_pow]
  have key0 : 4 * ((C α * X) ^ 2 + b ^ 2 + c ^ 2) = C (v ^ 2 + v' ^ 2) * X ^ (2 * 2) +
      C 0 * X ^ 2 + C (u ^ 2 + u' ^ 2) := by
    simp only [map_add, map_pow, map_zero, zero_mul, add_zero]
    linear_combination (2 * b + (C v * X ^ 2 - C u)) * hb2 +
      (2 * c + (C v' * X ^ 2 - C u')) * hc2 + (-2 * X ^ 2) * hCuv + (-2 * X ^ 2) * hCuv'
  by_cases hA : v ^ 2 + v' ^ 2 = 0
  · have hD0 : v ^ 2 * v' ^ 2 * (u ^ 2 + u' ^ 2) = 0 := by
      linear_combination (u * v + α ^ 2) * v' ^ 2 * huv + (u' * v' + α ^ 2) * v ^ 2 * huv' +
        α ^ 4 * hA
    have hD : u ^ 2 + u' ^ 2 = 0 := by
      rcases mul_eq_zero.1 hD0 with h0 | h0
      · exact absurd h0 (mul_ne_zero (pow_ne_zero 2 hv) (pow_ne_zero 2 hv'))
      · exact h0
    rw [hA, hD, C_0, zero_mul, zero_mul, add_zero, add_zero] at key0
    exact hne ((mul_eq_zero.1 key0).resolve_left (four_ne_zero_poly h2))
  · have keyg : (2 * g) ^ 2 = C (v ^ 2 + v' ^ 2) * X ^ (2 * 2) + C 0 * X ^ 2 +
        C (u ^ 2 + u' ^ 2) := by
      rw [← key0]; linear_combination (-4) * hg
    have keyf : (2 * f) ^ 2 = C (v ^ 2 + v' ^ 2) * X ^ (2 * 2) + C (-4 * α ^ 2) * X ^ 2 +
        C (u ^ 2 + u' ^ 2) := by
      simp only [map_add, map_pow, map_mul, map_neg, map_ofNat]
      linear_combination (-4) * hf + (2 * b + (C v * X ^ 2 - C u)) * hb2 +
        (2 * c + (C v' * X ^ 2 - C u')) * hc2 + (-2 * X ^ 2) * hCuv + (-2 * X ^ 2) * hCuv'
    have hdg := PolyNegOne.quad_disc h2 (by norm_num) hA keyg
    have hdf := PolyNegOne.quad_disc h2 (by norm_num) hA keyf
    have h3 : (2 * 2 * 2 * 2) * α ^ 4 = 0 := by linear_combination hdf - hdg
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2)
      (pow_ne_zero 4 hα) h3

/-! ## Main theorem -/

/-- **A nondegenerate cuboid with a linear edge `α X` has all edges `β X, γ X`**, over any
field with `2 ≠ 0` (no hypothesis on `−1`). -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_linear_edge
    (h2 : (2 : K) ≠ 0) {α : K} {b c : K[X]} (h : IsNondegCuboid (C α * X) b c) :
    ∃ β γ : K, b = C β * X ∧ c = C γ * X := by
  have hα : α ≠ 0 := by rintro rfl; exact h.ne_a (by simp)
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  rw [← sq] at hd he hf hg
  rcases linear_leg_shape h2 hα hd with ⟨β, hβ⟩ | ⟨u, v, hu, hv, huv, hb2, -⟩ <;>
    rcases linear_leg_shape h2 hα he with ⟨γ, hγ⟩ | ⟨u', v', hu', hv', huv', hc2, -⟩
  · exact ⟨β, γ, hβ, hγ⟩
  · exfalso
    subst hβ
    have hβ0 : β ≠ 0 := by rintro rfl; exact h.ne_b (by simp)
    exact mixed_case h2 hβ0 hv' huv' hc2 hf hg
  · exfalso
    subst hγ
    have hγ0 : γ ≠ 0 := by rintro rfl; exact h.ne_c (by simp)
    exact mixed_case (α := α) (β := γ) (f := f) (g := g) h2 hγ0 hv huv hb2
      (by linear_combination hf)
      (by linear_combination hg)
  · exact (both_case h2 hα hv hv' huv huv' hb2 hc2 hf hg h.ne_abc).elim

/-! ## Translations and degree-one edges -/

/-- Translation `X ↦ X + r` maps nondegenerate cuboids to nondegenerate cuboids. -/
theorem isNondegCuboid_comp_X_add_C {a b c : K[X]} (h : IsNondegCuboid a b c) (r : K) :
    IsNondegCuboid (a.comp (X + C r)) (b.comp (X + C r)) (c.comp (X + C r)) := by
  have hne : ∀ p : K[X], p ≠ 0 → p.comp (X + C r) ≠ 0 := by
    intro p hp h0
    apply hp
    rw [← PolyNegOne.comp_X_add_C_comp_X_sub_C p r, h0, zero_comp]
  refine ⟨PolyNegOne.isCuboid_comp_X_add_C h.toIsCuboid r, ?_, ?_, ?_, ?_⟩
  · simpa [add_comp, pow_comp] using hne _ h.ne_ab
  · simpa [add_comp, pow_comp] using hne _ h.ne_ac
  · simpa [add_comp, pow_comp] using hne _ h.ne_bc
  · simpa [add_comp, pow_comp] using hne _ h.ne_abc

/-- **Degree-one edge ⇒ proportional** for nondegenerate cuboids over any field with `2 ≠ 0`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_natDegree_eq_one
    (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsNondegCuboid a b c) (ha : a.natDegree = 1) :
    Proportional a b c := by
  obtain ⟨α, r, hr⟩ := PolyNegOne.exists_comp_eq_C_mul_X ha
  have h' := isNondegCuboid_comp_X_add_C h r
  rw [hr] at h'
  obtain ⟨β, γ, hb, hc⟩ := h'.proportional_of_linear_edge h2
  refine ⟨X - C r, α, β, γ, ?_, ?_, ?_⟩
  · rw [← PolyNegOne.comp_X_add_C_comp_X_sub_C a r, hr]; simp
  · rw [← PolyNegOne.comp_X_add_C_comp_X_sub_C b r, hb]; simp
  · rw [← PolyNegOne.comp_X_add_C_comp_X_sub_C c r, hc]; simp

/-- Edge of degree `≤ 1` ⇒ proportional (degree `0` needs only `IsCuboid`). -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_natDegree_le_one
    (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsNondegCuboid a b c) (ha : a.natDegree ≤ 1) :
    Proportional a b c := by
  rcases (show a.natDegree = 0 ∨ a.natDegree = 1 by omega) with h1 | h1
  · have h' := h.toIsCuboid
    rw [eq_C_of_natDegree_eq_zero h1] at h' ⊢
    exact h'.proportional_of_const h2
  · exact h.proportional_of_natDegree_eq_one h2 h1

/-! ## Nondegenerate constant cuboids -/

/-- A *nondegenerate constant cuboid* over `K`. -/
def IsNondegConstCuboid (α β γ : K) : Prop :=
  PolyNegOne.IsConstCuboid α β γ ∧ α ^ 2 + β ^ 2 ≠ 0 ∧ α ^ 2 + γ ^ 2 ≠ 0 ∧ β ^ 2 + γ ^ 2 ≠ 0 ∧
    α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0

/-- A proportional nondegenerate cuboid `(α q, β q, γ q)` gives a nondegenerate constant
cuboid `(α, β, γ)`. -/
theorem isNondegConstCuboid_of_mul {α β γ : K} {q : K[X]}
    (h : IsNondegCuboid (C α * q) (C β * q) (C γ * q)) : IsNondegConstCuboid α β γ := by
  refine ⟨PolyNegOne.isConstCuboid_of_isCuboid_mul h.toIsCuboid, ?_, ?_, ?_, ?_⟩
  · intro h0; apply h.ne_ab
    rw [show (C α * q) ^ 2 + (C β * q) ^ 2 = C (α ^ 2 + β ^ 2) * q ^ 2 by
      simp only [map_add, map_pow]; ring, h0, C_0, zero_mul]
  · intro h0; apply h.ne_ac
    rw [show (C α * q) ^ 2 + (C γ * q) ^ 2 = C (α ^ 2 + γ ^ 2) * q ^ 2 by
      simp only [map_add, map_pow]; ring, h0, C_0, zero_mul]
  · intro h0; apply h.ne_bc
    rw [show (C β * q) ^ 2 + (C γ * q) ^ 2 = C (β ^ 2 + γ ^ 2) * q ^ 2 by
      simp only [map_add, map_pow]; ring, h0, C_0, zero_mul]
  · intro h0; apply h.ne_abc
    rw [show (C α * q) ^ 2 + (C β * q) ^ 2 + (C γ * q) ^ 2 = C (α ^ 2 + β ^ 2 + γ ^ 2) * q ^ 2 by
      simp only [map_add, map_pow]; ring, h0, C_0, zero_mul]

theorem isNondegCuboid_C_iff {α β γ : K} :
    IsNondegCuboid (C α) (C β) (C γ) ↔ IsNondegConstCuboid α β γ := by
  constructor
  · intro h
    exact isNondegConstCuboid_of_mul (q := 1) (by simpa only [mul_one] using h)
  · rintro ⟨hc, h1, h2, h3, h4⟩
    refine ⟨PolyNegOne.isCuboid_C_iff.2 hc, ?_, ?_, ?_, ?_⟩
    · rw [← C_pow, ← C_pow, ← C_add]; exact C_ne_zero.2 h1
    · rw [← C_pow, ← C_pow, ← C_add]; exact C_ne_zero.2 h2
    · rw [← C_pow, ← C_pow, ← C_add]; exact C_ne_zero.2 h3
    · rw [← C_pow, ← C_pow, ← C_pow, ← C_add, ← C_add]; exact C_ne_zero.2 h4

/-- If `K` (`2 ≠ 0`) has no nondegenerate constant cuboid, every edge of a nondegenerate cuboid
over `K[X]` has degree `≥ 2`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.one_lt_natDegree (h2 : (2 : K) ≠ 0)
    (h0 : ∀ α β γ : K, ¬ IsNondegConstCuboid α β γ) {a b c : K[X]} (h : IsNondegCuboid a b c) :
    1 < a.natDegree := by
  by_contra hlt
  obtain ⟨q, α, β, γ, rfl, rfl, rfl⟩ := h.proportional_of_natDegree_le_one h2 (by omega)
  exact h0 α β γ (isNondegConstCuboid_of_mul h)

/-! ## `𝔽_p` -/

/-- For an odd prime `p`, a nondegenerate cuboid over `𝔽_p[X]` with an edge of degree `≤ 1` is
proportional (covers `p ≡ 1 (mod 4)`, where `−1` is a square). -/
theorem zmod_nondeg_proportional_of_natDegree_le_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {a b c : (ZMod p)[X]} (h : IsNondegCuboid a b c) (ha : a.natDegree ≤ 1) :
    Proportional a b c :=
  h.proportional_of_natDegree_le_one (PolyNegOne.zmod_two_ne_zero hp) ha

theorem zmod_nondeg_proportional_of_natDegree_eq_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {a b c : (ZMod p)[X]} (h : IsNondegCuboid a b c) (ha : a.natDegree = 1) :
    Proportional a b c :=
  h.proportional_of_natDegree_eq_one (PolyNegOne.zmod_two_ne_zero hp) ha

section Instances
local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- **No nondegenerate constant cuboid over `𝔽₅`** (kernel `decide`). -/
theorem not_isNondegConstCuboid_five : ∀ α β γ : ZMod 5, ¬ IsNondegConstCuboid α β γ := by
  unfold IsNondegConstCuboid PolyNegOne.IsConstCuboid; decide +kernel

/-- **No nondegenerate constant cuboid over `𝔽₁₃`** (kernel `decide`). -/
theorem not_isNondegConstCuboid_thirteen : ∀ α β γ : ZMod 13, ¬ IsNondegConstCuboid α β γ := by
  unfold IsNondegConstCuboid PolyNegOne.IsConstCuboid; decide +kernel

theorem not_isNondegCuboid_C_five : ∀ α β γ : ZMod 5, ¬ IsNondegCuboid (C α) (C β) (C γ) :=
  fun α β γ h => not_isNondegConstCuboid_five α β γ (isNondegCuboid_C_iff.1 h)

theorem not_isNondegCuboid_C_thirteen :
    ∀ α β γ : ZMod 13, ¬ IsNondegCuboid (C α) (C β) (C γ) :=
  fun α β γ h => not_isNondegConstCuboid_thirteen α β γ (isNondegCuboid_C_iff.1 h)

/-- **Over `𝔽₅[X]` every edge of a nondegenerate cuboid has degree `≥ 2`.** -/
theorem no_nondeg_cuboid_natDegree_le_one_five :
    ∀ a b c : (ZMod 5)[X], IsNondegCuboid a b c → 1 < a.natDegree :=
  fun _ _ _ h => h.one_lt_natDegree (by decide) not_isNondegConstCuboid_five

/-- **Over `𝔽₁₃[X]` every edge of a nondegenerate cuboid has degree `≥ 2`.** -/
theorem no_nondeg_cuboid_natDegree_le_one_thirteen :
    ∀ a b c : (ZMod 13)[X], IsNondegCuboid a b c → 1 < a.natDegree :=
  fun _ _ _ h => h.one_lt_natDegree (by decide) not_isNondegConstCuboid_thirteen

end Instances

/-! ## Stretch: an edge `α π^k` (`π` irreducible) coprime to the other two edges -/

/-- **Discriminant lemma in a nonconstant `W`** (any field with `2 ≠ 0`): if
`A W² + B W + D` (`A ≠ 0`, `deg W ≥ 1`) is a square in `K[X]`, then `B² = 4AD`. -/
theorem quad_disc_W (h2 : (2 : K) ≠ 0) {F W : K[X]} {A B D : K} (hW : 0 < W.natDegree)
    (hA : A ≠ 0) (h : F ^ 2 = C A * W ^ 2 + C B * W + C D) : B ^ 2 = 4 * A * D := by
  have hW0 : W ≠ 0 := by rintro rfl; simp at hW
  have hw : W.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hW0
  have hL : (C B * W + C D).natDegree ≤ W.natDegree :=
    (natDegree_add_le _ _).trans (max_le (natDegree_C_mul_le _ _) (by simp))
  have hM : (C A * W ^ 2).natDegree = 2 * W.natDegree := by
    rw [natDegree_C_mul hA, natDegree_pow]
  have hlt : (C B * W + C D).natDegree < (C A * W ^ 2).natDegree := by rw [hM]; omega
  have hR : C A * W ^ 2 + C B * W + C D = C A * W ^ 2 + (C B * W + C D) := by ring
  rw [hR] at h
  have hdeg := natDegree_add_eq_left_of_natDegree_lt hlt
  have hlc : (C A * W ^ 2 + (C B * W + C D)).leadingCoeff = A * W.leadingCoeff ^ 2 := by
    have hMne : C A * W ^ 2 ≠ 0 := mul_ne_zero (C_ne_zero.2 hA) (pow_ne_zero 2 hW0)
    rw [leadingCoeff_add_of_degree_lt' (degree_lt_degree hlt), leadingCoeff_mul,
      leadingCoeff_C, leadingCoeff_pow]
  have hF : F.natDegree = W.natDegree := by
    have := congrArg natDegree h
    rw [natDegree_pow, hdeg, hM] at this
    omega
  have hP : F.leadingCoeff ^ 2 = A * W.leadingCoeff ^ 2 := by
    rw [← hlc, ← h, leadingCoeff_pow]
  set l : K := F.leadingCoeff / W.leadingCoeff with hl
  have hl2 : l ^ 2 = A := by
    rw [hl, div_pow, hP]; field_simp
  by_contra hne
  have hδ : B ^ 2 - 4 * A * D ≠ 0 := sub_ne_zero.mpr hne
  set s : K[X] := C (2 * A) * W + C B with hs
  set t : K[X] := C (2 * l) * F with ht
  have hPC : C l ^ 2 = C A := by rw [← C_pow, hl2]
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
  have hs0 := PolyNegOne.natDegree_eq_zero_of_two_mul h2 h2s
  have hsdeg : s.natDegree = W.natDegree := by
    have h2A := mul_ne_zero h2 hA
    rw [hs, natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_C_mul h2A]; simpa using hW),
      natDegree_C_mul h2A]
  omega

/-- In a coprime factorization `p q = c π ^ m` (`π` irreducible) one factor is a unit. -/
theorem isUnit_or_isUnit_of_mul_eq_C_mul_pow {p q π : K[X]} {c : K} {m : ℕ} (hπ : Irreducible π)
    (hc : c ≠ 0) (hpq : IsCoprime p q) (h : p * q = C c * π ^ m) : IsUnit p ∨ IsUnit q := by
  have hcu : IsUnit (C c) := isUnit_C.mpr (Ne.isUnit hc)
  have key : ∀ p q : K[X], p * q = C c * π ^ m → ¬ π ∣ p → IsUnit p := by
    intro p q h hX
    have h1 : IsCoprime (π ^ m) p := ((hπ.coprime_iff_not_dvd).mpr hX).pow_left
    have h2 : p ∣ π ^ m * C c := ⟨q, by rw [h, mul_comm]⟩
    exact isUnit_of_dvd_unit (h1.symm.dvd_of_dvd_mul_left h2) hcu
  by_cases hp : π ∣ p
  · by_cases hq : π ∣ q
    · exact absurd (hpq.isUnit_of_dvd' hp hq) hπ.not_isUnit
    · exact Or.inr (key q p (by rw [mul_comm]; exact h) hq)
  · exact Or.inl (key p q h hp)

/-- A face `(α π^k, b, d)` with `b` coprime to the edge: `2b = v π^{2k} − u`, `u v = α²`. -/
theorem irreducible_pow_leg (h2 : (2 : K) ≠ 0) {α : K} {k : ℕ} {π b d : K[X]} (hα : α ≠ 0)
    (hπ : Irreducible π) (hab : IsCoprime (C α * π ^ k) b)
    (h : (C α * π ^ k) ^ 2 + b ^ 2 = d ^ 2) :
    ∃ u v : K, u * v = α ^ 2 ∧ 2 * b = C v * π ^ (2 * k) - C u := by
  have hcop := PolyNegOne.isCoprime_sub_add h2 hab h
  have hprod : (d - b) * (d + b) = C (α ^ 2) * π ^ (2 * k) := by
    rw [C_pow, pow_mul]; linear_combination -h
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero _ hα
  rcases isUnit_or_isUnit_of_mul_eq_C_mul_pow hπ hα2 hcop hprod with hu | hu
  · obtain ⟨u, hu0, hCu⟩ := Polynomial.isUnit_iff.mp hu
    have hu0 := hu0.ne_zero
    have hdb : d + b = C (u⁻¹ * α ^ 2) * π ^ (2 * k) := by
      have : d + b = C u⁻¹ * ((d - b) * (d + b)) := by
        rw [← hCu, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hu0, C_1, one_mul]
      rw [this, hprod, C_mul, mul_assoc]
    refine ⟨u, u⁻¹ * α ^ 2, by field_simp, ?_⟩
    rw [← hdb, hCu]
    ring
  · obtain ⟨w, hw0, hCw⟩ := Polynomial.isUnit_iff.mp hu
    have hw0 := hw0.ne_zero
    have hdb : d - b = C (w⁻¹ * α ^ 2) * π ^ (2 * k) := by
      have : d - b = C w⁻¹ * ((d - b) * (d + b)) := by
        rw [← hCw, mul_comm (d - b), ← mul_assoc, ← C_mul, inv_mul_cancel₀ hw0, C_1, one_mul]
      rw [this, hprod, C_mul, mul_assoc]
    refine ⟨-w, -(w⁻¹ * α ^ 2), by field_simp, ?_⟩
    simp only [map_neg]
    linear_combination -hCw - hdb

/-- **Irreducible-power edge, nondegenerate, any field with `2 ≠ 0`**: there is no
nondegenerate cuboid `(α π^k, b, c)` (`π` irreducible, `k ≥ 1`) with the edge `α π^k` coprime
to `b` and to `c`. With `W = π^{2k}`: `4f² = (v² + v'²)W² − 4α²W + (u² + u'²)` and
`4g² = (v² + v'²)W² + (u² + u'²)`; `quad_disc_W` gives `16α⁴ = 0` unless `v² + v'² = 0`, and
then `u² + u'² = 0` and `a² + b² + c² = 0`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.false_of_irreducible_pow_edge
    (h2 : (2 : K) ≠ 0) {α : K} {k : ℕ} {π b c : K[X]} (hπ : Irreducible π) (hk : 0 < k)
    (h : IsNondegCuboid (C α * π ^ k) b c) (hb : IsCoprime (C α * π ^ k) b)
    (hc : IsCoprime (C α * π ^ k) c) : False := by
  have hα : α ≠ 0 := by rintro rfl; exact h.ne_a (by simp)
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  rw [← sq] at hd he hf hg
  obtain ⟨u, v, huv, hb2⟩ := irreducible_pow_leg h2 hα hπ hb hd
  obtain ⟨u', v', huv', hc2⟩ := irreducible_pow_leg h2 hα hπ hc he
  have hv : v ≠ 0 := by rintro rfl; rw [mul_zero] at huv; exact pow_ne_zero 2 hα huv.symm
  have hv' : v' ≠ 0 := by rintro rfl; rw [mul_zero] at huv'; exact pow_ne_zero 2 hα huv'.symm
  set W : K[X] := π ^ (2 * k) with hWdef
  have hW : 0 < W.natDegree := by
    rw [hWdef, natDegree_pow]
    have := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hπ)
    positivity
  have hWa : (C α * π ^ k) ^ 2 = C (α ^ 2) * W := by rw [hWdef, C_pow, pow_mul]; ring
  have hCuv : C u * C v = C α ^ 2 := by rw [← C_mul, huv, C_pow]
  have hCuv' : C u' * C v' = C α ^ 2 := by rw [← C_mul, huv', C_pow]
  have key0 : 4 * ((C α * π ^ k) ^ 2 + b ^ 2 + c ^ 2) = C (v ^ 2 + v' ^ 2) * W ^ 2 +
      C 0 * W + C (u ^ 2 + u' ^ 2) := by
    rw [hWa]
    simp only [map_add, map_pow, map_zero, zero_mul, add_zero]
    linear_combination (2 * b + (C v * W - C u)) * hb2 +
      (2 * c + (C v' * W - C u')) * hc2 + (-2 * W) * hCuv + (-2 * W) * hCuv'
  by_cases hA : v ^ 2 + v' ^ 2 = 0
  · have hD0 : v ^ 2 * v' ^ 2 * (u ^ 2 + u' ^ 2) = 0 := by
      linear_combination (u * v + α ^ 2) * v' ^ 2 * huv + (u' * v' + α ^ 2) * v ^ 2 * huv' +
        α ^ 4 * hA
    have hD : u ^ 2 + u' ^ 2 = 0 := by
      rcases mul_eq_zero.1 hD0 with h0 | h0
      · exact absurd h0 (mul_ne_zero (pow_ne_zero 2 hv) (pow_ne_zero 2 hv'))
      · exact h0
    rw [hA, hD, C_0, zero_mul, zero_mul, add_zero, add_zero] at key0
    exact h.ne_abc ((mul_eq_zero.1 key0).resolve_left (four_ne_zero_poly h2))
  · have keyg : (2 * g) ^ 2 = C (v ^ 2 + v' ^ 2) * W ^ 2 + C 0 * W + C (u ^ 2 + u' ^ 2) := by
      rw [← key0]; linear_combination (-4) * hg
    have keyf : (2 * f) ^ 2 = C (v ^ 2 + v' ^ 2) * W ^ 2 + C (-4 * α ^ 2) * W +
        C (u ^ 2 + u' ^ 2) := by
      simp only [map_add, map_pow, map_mul, map_neg, map_ofNat]
      linear_combination (-4) * hf + (2 * b + (C v * W - C u)) * hb2 +
        (2 * c + (C v' * W - C u')) * hc2 + (-2 * W) * hCuv + (-2 * W) * hCuv'
    have hdg := quad_disc_W h2 hW hA keyg
    have hdf := quad_disc_W h2 hW hA keyf
    have h3 : (2 * 2 * 2 * 2) * α ^ 4 = 0 := by linear_combination hdf - hdg
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2)
      (pow_ne_zero 4 hα) h3

end PerfectCuboid.PolyLinearNondeg
