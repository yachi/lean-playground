module

public import LeanPlayground.PerfectCuboid.DivPolyFormula
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The torsion of the congruent-number curve

For every rational `N ≠ 0`, the rational torsion of `E_N : Y² = X³ − N²X` is `{0, S, T, U}`
(Koblitz, *Introduction to Elliptic Curves and Modular Forms*, Ch. I §9). This is the hypothesis
`TorsionTwo` of Asiryan's Remark 1 (arXiv:2610.10643), which this file discharges, so that
Lemmas 2 and 3 (`rankOneReduction_of_torsion`) hold unconditionally.

The proof has two parts.

* **No point of order `4`** (`add_self_eq_zero_of_four`): if `2Q ∈ {S, T, U}` then the doubling
  formula gives `x² + N² = 0` or `(x ∓ N)² = 2N²`, which have no rational solution.
* **No point of odd prime order `ℓ`** (`eq_zero_of_prime_nsmul`). Suppose `ℓ • (x, y) = 0`. Then
  `ΨSq_ℓ(x) = 0` (the division-polynomial formula, `zsmul_eq_zero_iff`). Dirichlet's theorem gives
  a prime `p ≡ 3 (mod 4)`, `p ≡ 1 (mod ℓ)`, larger than the denominators of `x`, `y` and the
  numerator and denominator of `N`. Then `x, y, N` lie in `ℤ_[p]`, and reducing them modulo `p`
  gives a point `P̄ ≠ 0` of `E_N(𝔽_p)` with `ΨSq_ℓ(x̄) = 0`, so `ℓ • P̄ = 0` and `ℓ` divides
  `#E_N(𝔽_p) = p + 1` (`natCard_point`: the abscissas `x` and `−x` pair off, because `−1` is not a
  square modulo `p`). But `p + 1 ≡ 2 (mod ℓ)`.

Unlike the textbook proof, no integrality (Nagell–Lutz) and no injectivity of reduction on torsion
is needed: the prime `p` is chosen after the point, and `P̄` is an affine point, so it is nonzero.
-/

@[expose] public section

open Polynomial

/-! ### `n • P = 0` in terms of the division polynomials -/

namespace WeierstrassCurve

open Jacobian

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- **`n • (x, y) = 0` iff `ΨSqₙ(x) = 0`.** -/
theorem zsmul_eq_zero_iff {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (Affine.Point.some x y h : W.toAffine.Point) = 0 ↔ (W.ΨSq n).eval x = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ by_contra fun hn ↦ (W.exists_zsmul_some_eq h n hn).1 h0⟩
  set e := Point.toAffineAddEquiv W.toAffine.toJacobian
  have he : n • (Affine.Point.some x y h : W.toAffine.Point) =
      e (n • Point.fromAffine (Affine.Point.some x y h)) := by
    rw [map_zsmul]
    congr 1
    exact (e.apply_symm_apply _).symm
  have hpt := zsmul_point_eq_smulEval W h n
  rw [he] at h0
  generalize n • Point.fromAffine (Affine.Point.some x y h) = J at h0 hpt
  obtain @⟨pt, hJ⟩ := J
  simp only at hpt
  subst hpt
  have hsq : (W.ΨSq n).eval x = (W.ψ n).evalEval x y ^ 2 := by
    rw [evalEval_ψ_eq_evalEval_Ψ W h.1, evalEval_Ψ_sq_eq_eval_ΨSq W h.1]
  rw [hsq]
  by_contra hψ
  simp only [e, Point.toAffineAddEquiv_apply] at h0
  rw [Point.toAffineLift_eq, Point.toAffine_of_Z_ne_zero hJ
    (by simpa [smulEval] using (pow_ne_zero_iff two_ne_zero).mp hψ)] at h0
  exact Affine.Point.some_ne_zero _ h0

end WeierstrassCurve

/-! ### Counting points of `Y² = X³ + bX` over a finite field -/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F]

/-- The points of an affine Weierstrass curve: the point at infinity and the affine points. -/
def pointEquivOption (W : WeierstrassCurve.Affine F) :
    W.Point ≃ Option {q : F × F // W.Nonsingular q.1 q.2} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), h⟩
  invFun
    | none => .zero
    | some q => .some q.1.1 q.1.2 q.2
  left_inv P := by cases P <;> rfl
  right_inv q := by rcases q with _ | ⟨⟨x, y⟩, h⟩ <;> rfl

/-- The curve `Y² = X³ + bX`. -/
def oddCurve (b : F) : WeierstrassCurve.Affine F := ⟨0, 0, 0, b, 0⟩

theorem oddCurve_nonsingular_iff [NeZero (2 : F)] {b : F} (hb : b ≠ 0) {x y : F} :
    (oddCurve b).Nonsingular x y ↔ y ^ 2 = x ^ 3 + b * x := by
  have hΔ : (oddCurve b).Δ ≠ 0 := by
    have : (oddCurve b).Δ = -64 * b ^ 3 := by
      simp only [oddCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [this]
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have : (64 : F) = 2 ^ 6 := by norm_num
    rw [this]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ h2)) (pow_ne_zero _ hb)
  rw [← equation_iff_nonsingular_of_Δ_ne_zero hΔ, equation_iff]
  simp only [oddCurve]
  constructor <;> intro h <;> linear_combination h

variable [Fintype F] [DecidableEq F]

/-- `∑ₓ χ(x³ + bx) = 0` when `χ(−1) = −1`: the summand is odd in `x`. -/
theorem sum_quadraticChar_odd (b : F) (hχ : quadraticChar F (-1) = -1) :
    ∑ x : F, quadraticChar F (x ^ 3 + b * x) = 0 := by
  have h := Equiv.sum_comp (Equiv.neg F) (fun x ↦ quadraticChar F (x ^ 3 + b * x))
  have e : ∀ x : F, quadraticChar F ((-x) ^ 3 + b * -x) = -quadraticChar F (x ^ 3 + b * x) := by
    intro x
    rw [show (-x) ^ 3 + b * -x = -1 * (x ^ 3 + b * x) by ring, map_mul, hχ, neg_one_mul]
  simp only [Equiv.neg_apply, e, Finset.sum_neg_distrib] at h
  linarith

/-- **`#{Y² = X³ + bX}(F) = #F + 1`** when `b ≠ 0`, `char F ≠ 2` and `−1` is not a square. -/
theorem natCard_point {b : F} (hb : b ≠ 0) (hF : ringChar F ≠ 2)
    (hχ : quadraticChar F (-1) = -1) : Nat.card (oddCurve b).Point = Fintype.card F + 1 := by
  classical
  have : NeZero (2 : F) := ⟨Ring.two_ne_zero hF⟩
  rw [Nat.card_congr (pointEquivOption _), Nat.card_eq_fintype_card, Fintype.card_option]
  congr 1
  rw [Fintype.card_subtype]
  simp_rw [oddCurve_nonsingular_iff hb]
  have key : ∀ x : F, ((Finset.univ.filter fun y : F ↦ y ^ 2 = x ^ 3 + b * x).card : ℤ) =
      quadraticChar F (x ^ 3 + b * x) + 1 := by
    intro x
    rw [← quadraticChar_card_sqrts hF]
    congr 2
    ext y
    simp
  have hfib : (Finset.univ.filter fun q : F × F ↦ q.2 ^ 2 = q.1 ^ 3 + b * q.1).card =
      ∑ x : F, (Finset.univ.filter fun y : F ↦ y ^ 2 = x ^ 3 + b * x).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ) (by simp)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    refine Finset.card_bij (fun q _ ↦ q.2) (by simp +contextual) (by aesop) (fun y hy ↦ ?_)
    exact ⟨(x, y), by simpa using hy, rfl⟩
  have : ((Finset.univ.filter fun q : F × F ↦ q.2 ^ 2 = q.1 ^ 3 + b * q.1).card : ℤ) =
      Fintype.card F := by
    rw [hfib, Nat.cast_sum]
    simp_rw [key]
    rw [Finset.sum_add_distrib, sum_quadraticChar_odd b hχ]
    simp
  exact_mod_cast this

end WeierstrassCurve.Affine

namespace PerfectCuboid.CongruentRank

open WeierstrassCurve WeierstrassCurve.Affine

variable {N : ℚ}

/-! ### No point of order `4` -/

/-- **`E_N(ℚ)` has no point of order `4`**: if `4Q = 0` then `2Q = 0`. -/
theorem add_self_eq_zero_of_four (hN : N ≠ 0) {Q : (curve N).Point}
    (hQ : Q + Q + (Q + Q) = 0) : Q + Q = 0 := by
  by_contra h2
  rcases Q with _ | @⟨x, y, h⟩
  · exact h2 (zero_add 0)
  have hy2 := (nonsingular_iff hN).mp h
  have hy : y ≠ (curve N).negY x y := by
    simp only [curve, negY, zero_mul, sub_zero]
    intro hy
    apply h2
    rw [Point.add_self_of_Y_eq (by simp only [curve, negY, zero_mul, sub_zero]; exact hy)]
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hy
    simp [curve, negY, hy0]
  rcases two_torsion hN hQ with h0 | hR | hR | hR
  · exact h2 h0
  all_goals
    rw [Point.add_self_of_Y_ne hy] at hR
    simp only [S, T, U, Point.some.injEq] at hR
    have hl := (curve N).slope_of_Y_ne rfl hy
    generalize (curve N).slope x x y y = l at hl hR
    simp only [curve, negY, addX, zero_mul, sub_zero, mul_zero, add_zero] at hl hR
    have hl' : l * (2 * y) = 3 * x ^ 2 - N ^ 2 := by
      rw [hl]
      field_simp
      ring
  · -- `2Q = S`: `(x² + N²)² = 0`
    have : (x ^ 2 + N ^ 2) ^ 2 = 0 := by
      linear_combination -(l * (2 * y) + 3 * x ^ 2 - N ^ 2) * hl' + 4 * y ^ 2 * hR.1 +
        (8 * x) * hy2
    have : x ^ 2 + N ^ 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp this
    have : N ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg N]
    exact hN (pow_eq_zero_iff two_ne_zero |>.mp this)
  · -- `2Q = T`: `(x² − 2Nx − N²)² = 0`
    have : (x ^ 2 - 2 * N * x - N ^ 2) ^ 2 = 0 := by
      linear_combination -(l * (2 * y) + 3 * x ^ 2 - N ^ 2) * hl' + 4 * y ^ 2 * hR.1 +
        (8 * x + 4 * N) * hy2
    have h' := pow_eq_zero_iff two_ne_zero |>.mp this
    exact sq_ne_two ((x - N) / N) (by field_simp; linear_combination h')
  · -- `2Q = U`: `(x² + 2Nx − N²)² = 0`
    have : (x ^ 2 + 2 * N * x - N ^ 2) ^ 2 = 0 := by
      linear_combination -(l * (2 * y) + 3 * x ^ 2 - N ^ 2) * hl' + 4 * y ^ 2 * hR.1 +
        (8 * x - 4 * N) * hy2
    have h' := pow_eq_zero_iff two_ne_zero |>.mp this
    exact sq_ne_two ((x + N) / N) (by field_simp; linear_combination h')

/-! ### No point of odd prime order -/

section Reduction

variable {p : ℕ} [Fact p.Prime]

/-- A rational number whose denominator is prime to `p`, as a `p`-adic integer. -/
noncomputable def toPadicInt (q : ℚ) (hq : ¬p ∣ q.den) : ℤ_[p] := ⟨q, Padic.norm_rat_le_one hq⟩

@[simp] theorem coe_toPadicInt (q : ℚ) (hq : ¬p ∣ q.den) : (toPadicInt q hq : ℚ_[p]) = q := rfl

@[simp] theorem ringHom_toPadicInt (q : ℚ) (hq : ¬p ∣ q.den) :
    PadicInt.Coe.ringHom (toPadicInt q hq) = (q : ℚ_[p]) := rfl

/-- **Reduction modulo `p`.** If `ℓ • (x, y) = 0` on `E_N(ℚ)` and `p` is an odd prime dividing
none of the denominators of `x`, `y`, `N` and not the numerator of `N`, then `ℓ` kills a nonzero
point of `Y² = X³ − N̄²X` over `𝔽_p`. -/
theorem exists_reduction (hN : N ≠ 0) {x y : ℚ} (h : (curve N).Nonsingular x y) (ℓ : ℕ)
    (hℓ : ℓ • (Point.some x y h : (curve N).Point) = 0) (hp2 : p ≠ 2) (hx : ¬p ∣ x.den)
    (hy : ¬p ∣ y.den) (hNd : ¬p ∣ N.den) (hNn : ¬p ∣ N.num.natAbs) :
    ∃ b : ZMod p, b ≠ 0 ∧ ∃ P : (oddCurve b).Point, P ≠ 0 ∧ ℓ • P = 0 := by
  classical
  have hNi : ¬p ∣ N⁻¹.den := by
    rwa [Rat.den_inv_of_ne_zero hN]
  set X := toPadicInt x hx
  set Y := toPadicInt y hy
  set M := toPadicInt N hNd
  set M' := toPadicInt N⁻¹ hNi
  have hinj : Function.Injective (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) := Subtype.val_injective
  have hMM : M * M' = 1 := hinj (by
    rw [map_mul, map_one, ringHom_toPadicInt, ringHom_toPadicInt, ← Rat.cast_mul,
      mul_inv_cancel₀ hN, Rat.cast_one])
  let φ := PadicInt.toZMod (p := p)
  let b : ZMod p := -φ M ^ 2
  have hb : b ≠ 0 := by
    have : φ M * φ M' = 1 := by rw [← map_mul, hMM, map_one]
    simpa [b] using left_ne_zero_of_mul_eq_one this
  have h2 : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have : NeZero (2 : ZMod p) := ⟨Ring.two_ne_zero h2⟩
  have hy2 := (nonsingular_iff hN).mp h
  have hYX : Y ^ 2 = X ^ 3 + (-M ^ 2) * X := hinj (by
    simp only [map_pow, map_add, map_mul, map_neg, X, Y, M, ringHom_toPadicInt]
    exact_mod_cast (by linear_combination hy2 : y ^ 2 = x ^ 3 + -N ^ 2 * x))
  have hP : (oddCurve b).Nonsingular (φ X) (φ Y) :=
    (oddCurve_nonsingular_iff hb).mpr (by simpa [b] using congrArg φ hYX)
  refine ⟨b, hb, .some _ _ hP, Point.some_ne_zero _, ?_⟩
  -- `ΨSq_ℓ(x) = 0` over `ℚ`, hence over `ℤ_[p]`, hence over `𝔽_p`
  have hψ : ((curve N).ΨSq ℓ).eval x = 0 := by
    rw [← natCast_zsmul] at hℓ
    exact ((curve N).zsmul_eq_zero_iff h ℓ).mp hℓ
  let WO : WeierstrassCurve ℤ_[p] := ⟨0, 0, 0, -M ^ 2, 0⟩
  have hWO : WO.map PadicInt.Coe.ringHom = (curve N).map (Rat.castHom ℚ_[p]) := by
    ext <;> simp [WO, curve, M]
  have hψO : (WO.ΨSq ℓ).eval X = 0 := by
    apply hinj
    rw [map_zero, ← eval_map_apply, ← map_ΨSq, hWO, map_ΨSq]
    change eval ((Rat.castHom ℚ_[p]) x) _ = 0
    rw [eval_map_apply, hψ, map_zero]
  have hWb : WO.map φ = oddCurve b := by
    ext <;> simp [WO, oddCurve, b]
  rw [← natCast_zsmul, (oddCurve b).zsmul_eq_zero_iff, ← hWb, map_ΨSq, eval_map_apply, hψO,
    map_zero]

end Reduction

/-- The primes of Dirichlet's theorem used here: `p ≡ 3 (mod 4)` and `p ≡ 1 (mod ℓ)`. -/
theorem exists_prime_three_mod_four_one_mod (B : ℕ) {ℓ : ℕ} (hℓ : Odd ℓ) :
    ∃ p > B, p.Prime ∧ p % 4 = 3 ∧ p % ℓ = 1 % ℓ := by
  obtain ⟨j, hj⟩ := hℓ
  have hcop : (2 * ℓ + 1).Coprime (4 * ℓ) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · have : Nat.Coprime 2 (2 * ℓ + 1) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      simpa using this.symm.pow_right 2
    · rw [show 2 * ℓ + 1 = 1 + ℓ * 2 by ring, Nat.coprime_add_mul_left_left]
      exact Nat.coprime_one_left ℓ
  obtain ⟨p, hpB, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq B (by omega : 4 * ℓ ≠ 0) hcop
  refine ⟨p, hpB, hp, ?_, ?_⟩
  · have := (Nat.ModEq.of_mul_right ℓ hmod)
    unfold Nat.ModEq at this
    omega
  · have := (Nat.ModEq.of_mul_left 4 hmod)
    unfold Nat.ModEq at this
    rw [this]
    simp [Nat.add_mod]

/-- **`E_N(ℚ)` has no point of odd prime order.** -/
theorem eq_zero_of_prime_nsmul (hN : N ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    {P : (curve N).Point} (hP : ℓ • P = 0) : P = 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · rfl
  exfalso
  have hodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  obtain ⟨p, hpB, hp, hp4, hpℓ⟩ := exists_prime_three_mod_four_one_mod
    (x.den + y.den + N.den + N.num.natAbs) hodd
  have := Fact.mk hp
  have hnd : ∀ d, 0 < d → d ≤ x.den + y.den + N.den + N.num.natAbs → ¬p ∣ d :=
    fun d hd hdB ↦ Nat.not_dvd_of_pos_of_lt hd (by omega)
  have hNn : 0 < N.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hN)
  obtain ⟨b, hb, P, hP0, hℓP⟩ := exists_reduction hN h ℓ hP (by omega)
    (hnd _ x.den_pos (by omega)) (hnd _ y.den_pos (by omega)) (hnd _ N.den_pos (by omega))
    (hnd _ hNn (by omega))
  have h2 : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hχ : quadraticChar (ZMod p) (-1) = -1 := by
    rw [quadraticChar_neg_one h2, ZMod.card]
    exact ZMod.χ₄_nat_three_mod_four hp4
  have hcard := natCard_point hb h2 hχ
  rw [ZMod.card] at hcard
  have := Fact.mk hℓ
  have hord : addOrderOf P = ℓ := addOrderOf_eq_prime hℓP hP0
  have hdvd : ℓ ∣ p + 1 := hcard ▸ hord ▸ addOrderOf_dvd_natCard P
  have : ℓ ∣ 2 := ((Nat.ModEq.add_right 1 hpℓ).dvd_iff dvd_rfl).mp hdvd
  have := Nat.le_of_dvd two_pos this
  have := hℓ.two_le
  omega

/-! ### The torsion of `E_N` -/

/-- **The rational torsion of `E_N` is `{0, S, T, U}`** (Asiryan, Remark 1), for every rational
`N ≠ 0`. -/
theorem torsionTwo (hN : N ≠ 0) : TorsionTwo N := by
  intro P n hn hP
  have hfin : IsOfFinAddOrder P := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hP⟩
  have hm0 : 0 < addOrderOf P := hfin.addOrderOf_pos
  -- a proper multiple `k • P` with `0 < k < addOrderOf P` is nonzero
  have hne : ∀ k, 0 < k → k < addOrderOf P → k • P ≠ 0 := fun k hk hkm ↦
    nsmul_ne_zero_of_lt_addOrderOf hk.ne' hkm
  -- no odd prime divides the order
  have hodd : ∀ ℓ, ℓ.Prime → ℓ ∣ addOrderOf P → ℓ = 2 := by
    intro ℓ hℓ ⟨k, hk⟩
    by_contra hℓ2
    have hk0 : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ hm0)
    apply hne k hk0 (by rw [hk]; nlinarith [hℓ.two_le])
    apply eq_zero_of_prime_nsmul hN hℓ hℓ2
    rw [smul_smul, ← hk, addOrderOf_nsmul_eq_zero]
  -- `4` does not divide the order
  have h4 : ¬4 ∣ addOrderOf P := by
    rintro ⟨k, hk⟩
    have hk0 : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ hm0)
    apply hne (2 * k) (by omega) (by omega)
    have := add_self_eq_zero_of_four hN (Q := k • P) (by
      rw [← two_nsmul, ← two_nsmul, smul_smul, smul_smul, show 2 * 2 * k = 4 * k by
        ring, ← hk, addOrderOf_nsmul_eq_zero])
    rwa [← two_nsmul, smul_smul] at this
  obtain ⟨a, o, ho, hao⟩ := Nat.exists_eq_two_pow_mul_odd hm0.ne'
  have ho1 : o = 1 := by
    by_contra ho1
    have hmin := Nat.minFac_prime ho1
    have h2 := hodd _ hmin (hao ▸ Dvd.dvd.mul_left (Nat.minFac_dvd o) _)
    have : 2 ∣ o := h2 ▸ Nat.minFac_dvd o
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr this)
  subst ho1
  have ha : a ≤ 1 := by
    by_contra ha
    exact h4 (hao ▸ (Nat.pow_dvd_pow 2 (by omega : 2 ≤ a)).trans (by simp))
  rw [← two_nsmul, ← addOrderOf_dvd_iff_nsmul_eq_zero, hao, mul_one]
  interval_cases a <;> norm_num

/-- A rational point of `E_N` off the `2`-torsion has infinite order. In particular the three
points of a cuboid configuration (`−N < X < 0`) do. -/
theorem nonTors_of_hasX (hN : N ≠ 0) {P : (curve N).Point} {x : ℚ} (h : HasX P x)
    (hx : x * (x - N) * (x + N) ≠ 0) : NonTors P := by
  intro n hn h0
  rcases two_torsion hN (torsionTwo hN P n hn h0) with rfl | rfl | rfl | rfl
  · exact h.ne_zero rfl
  all_goals
    have := h.unique (hasX_some rfl)
    subst this
    exact hx (by ring)

theorem nonTors_of_mem (hN : 0 < N) {Q : (curve N).Point} {x : ℚ} (h : HasX Q x)
    (h1 : -N < x) (h2 : x < 0) : NonTors Q :=
  nonTors_of_hasX hN.ne' h
    (mul_ne_zero (mul_ne_zero h2.ne (by linarith)) (by linarith))

/-- **Asiryan, Lemmas 2 and 3**, unconditionally. -/
theorem rankOneReduction_of_pos (hN : 0 < N) : RankOneReduction N hN :=
  rankOneReduction_of_torsion hN (torsionTwo hN.ne')

/-- **Asiryan, Theorem 1 (rank-one case)**, conditional only on Ingram's primitive-divisor step. -/
theorem not_rankOne_of_primitiveDivisorStep {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃)
    (hprim : PrimitiveDivisorStep N hc.pos) {Q₁ Q₂ Q₃ : (curve N).Point} (h₁ : HasX Q₁ x₁)
    (h₂ : HasX Q₂ x₂) (h₃ : HasX Q₃ x₃) : ¬InRankOne Q₁ Q₂ Q₃ :=
  not_rankOne_of_torsion hc (torsionTwo hc.pos.ne') hprim h₁ h₂ h₃

end PerfectCuboid.CongruentRank
