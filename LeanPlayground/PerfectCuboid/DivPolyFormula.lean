module

public import LeanPlayground.PerfectCuboid.RankOneReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Eval

/-!
# The division-polynomial formula for `n • P`

The Tau Ceti project (vendored under `TauCeti/`, Apache-2.0; ported there from the AINTLIB work of
J. Xu and D. K. Angdinata) proves `zsmul_point_eq_smulEval`: on a Weierstrass curve over a field,
`n • (x, y)` has Jacobian coordinates `(φₙ(x, y) : ωₙ(x, y) : ψₙ(x, y))`. This file turns it into
the affine statement `DivPolyX` used by `RankOneReduction.lean`, which removes that hypothesis from
Asiryan's rank-one reduction (`rankOneReduction_of_torsion`).
-/

@[expose] public section

namespace WeierstrassCurve

open Polynomial Jacobian

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
theorem some_eq_of_X_eq {a b c : F} (hab : a = b) (H : W.toAffine.Nonsingular a c) :
    ∃ c' h', (Affine.Point.some a c H : W.toAffine.Point) = .some b c' h' := by
  subst hab
  exact ⟨c, H, rfl⟩

/-- **The abscissa of `n • P`.** If `n • (x, y) ≠ 0`, then `ΨSqₙ(x) ≠ 0` and `n • (x, y)` has
abscissa `Φₙ(x)/ΨSqₙ(x)`. -/
theorem exists_zsmul_some_eq {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ)
    (hn : n • (Affine.Point.some x y h : W.toAffine.Point) ≠ 0) :
    (W.ΨSq n).eval x ≠ 0 ∧ ∃ y' h', n • (Affine.Point.some x y h : W.toAffine.Point) =
      .some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' := by
  set e := Point.toAffineAddEquiv W.toAffine.toJacobian
  have he : n • (Affine.Point.some x y h : W.toAffine.Point) =
      e (n • Point.fromAffine (Affine.Point.some x y h)) := by
    rw [map_zsmul]
    congr 1
    exact (e.apply_symm_apply _).symm
  have hpt := zsmul_point_eq_smulEval W h n
  rw [he] at hn ⊢
  generalize n • Point.fromAffine (Affine.Point.some x y h) = J at hn hpt
  obtain @⟨pt, hJ⟩ := J
  simp only at hpt
  subst hpt
  have hψ : (W.ψ n).evalEval x y ≠ 0 := by
    intro h0
    apply hn
    simp only [e, Point.toAffineAddEquiv_apply]
    rw [Point.toAffineLift_eq]
    exact Point.toAffine_of_Z_eq_zero (by simpa [smulEval] using h0)
  have hsq : (W.ΨSq n).eval x = (W.ψ n).evalEval x y ^ 2 := by
    rw [evalEval_ψ_eq_evalEval_Ψ W h.1, evalEval_Ψ_sq_eq_eval_ΨSq W h.1]
  refine ⟨by rw [hsq]; exact pow_ne_zero 2 hψ, ?_⟩
  simp only [e, Point.toAffineAddEquiv_apply]
  rw [Point.toAffineLift_eq, Point.toAffine_of_Z_ne_zero hJ (by simpa [smulEval] using hψ)]
  refine some_eq_of_X_eq W ?_ _
  simp [smulEval, hsq, evalEval_φ_eq_eval_Φ W h.1]

end WeierstrassCurve

namespace PerfectCuboid.CongruentRank

variable {N : ℚ}

/-- The division-polynomial formula holds on `E_N`. -/
theorem divPolyX (N : ℚ) : DivPolyX N := by
  classical
  rintro P x ⟨y, h, rfl⟩ n hn
  have hn' : (n : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : (curve N).Point) ≠ 0 := by
    rwa [natCast_zsmul]
  obtain ⟨h0, y', h', e⟩ := (curve N).exists_zsmul_some_eq h n hn'
  rw [natCast_zsmul] at e
  exact ⟨h0, y', h', e⟩

/-- **Asiryan, Lemmas 2 and 3**, now conditional only on the torsion of `E_N` (Remark 1). -/
theorem rankOneReduction_of_torsion (hN : 0 < N) (htor : TorsionTwo N) :
    RankOneReduction N hN :=
  rankOneReduction hN (divPolyX N) htor

/-- **Asiryan, Theorem 1 (rank-one case)**, conditional on the torsion of `E_N` (Remark 1) and
Ingram's primitive-divisor step. -/
theorem not_rankOne_of_torsion {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃) (htor : TorsionTwo N)
    (hprim : PrimitiveDivisorStep N hc.pos) {Q₁ Q₂ Q₃ : (curve N).Point} (h₁ : HasX Q₁ x₁)
    (h₂ : HasX Q₂ x₂) (h₃ : HasX Q₃ x₃) : ¬InRankOne Q₁ Q₂ Q₃ :=
  not_rankOne_of hc (divPolyX N) htor hprim h₁ h₂ h₃

end PerfectCuboid.CongruentRank
