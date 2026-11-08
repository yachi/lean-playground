module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions

@[expose] public section

/-!
# Crouzeix's conjecture: the constant `2` is optimal

For an operator `A` on a complex inner product space, the *numerical range* is
`W(A) = {⟪x, A x⟫ : ‖x‖ = 1}`. Crouzeix's inequality `‖p(A)‖ ≤ 2 · max_{W(A)} |p|`
(proved in 2026 by Jin and, independently, by Lorist–Schwenninger; see
`LeanPlayground.Crouzeix.DilationLemma`) is sharp: for the `2 × 2` matrix
`J = [[0, 2], [0, 0]]` the numerical range is the closed unit disk while `‖J‖ = 2`, so `p = X`
gives equality.

Main results:
* `Crouzeix.numericalRange_J`: `W(J)` is the closed unit disk;
* `Crouzeix.norm_J`: `‖J‖ = 2`;
* `Crouzeix.two_le_of_crouzeix_bound`: any constant `C` with
  `‖p(J)‖ ≤ C · sup_{W(J)} |p|` for all polynomials satisfies `2 ≤ C`.
-/

open scoped InnerProductSpace
open Polynomial

namespace Crouzeix

/-- The numerical range `W(A) = {⟪x, A x⟫ : ‖x‖ = 1}` of an operator `A`. -/
def numericalRange {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) : Set ℂ :=
  {z | ∃ x : H, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z}

/-- The matrix `[[0, 2], [0, 0]]` acting on `ℂ²`: `J x = 2 x₁ e₀`. -/
noncomputable def J : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (2 : ℂ) • (innerSL ℂ (EuclideanSpace.single 1 (1 : ℂ))).smulRight
    (EuclideanSpace.single 0 (1 : ℂ))

lemma J_apply (x : EuclideanSpace ℂ (Fin 2)) : J x = EuclideanSpace.single 0 (2 * x 1) := by
  ext i
  fin_cases i <;> simp [J, EuclideanSpace.inner_single_left]

/-- `J` is the matrix `[[0, 2], [0, 0]]`. -/
lemma J_eq_toEuclideanCLM : J = Matrix.toEuclideanCLM (𝕜 := ℂ) !![0, 2; 0, 0] := by
  ext x i
  fin_cases i <;> simp [J_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

lemma norm_sq_fin_two (x : EuclideanSpace ℂ (Fin 2)) : ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

lemma inner_J (x : EuclideanSpace ℂ (Fin 2)) :
    ⟪x, J x⟫_ℂ = 2 * x 1 * starRingEnd ℂ (x 0) := by
  rw [J_apply, EuclideanSpace.inner_single_right]

/-- The numerical range of `[[0, 2], [0, 0]]` is the closed unit disk. -/
theorem numericalRange_J : numericalRange J = Metric.closedBall 0 1 := by
  ext z
  simp only [numericalRange, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h := norm_sq_fin_two x
    rw [hx] at h
    rw [inner_J, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_ofNat]
    nlinarith [sq_nonneg (‖x 0‖ - ‖x 1‖), norm_nonneg (x 0), norm_nonneg (x 1)]
  · intro hz
    set r := ‖z‖
    have hr0 : 0 ≤ r := norm_nonneg z
    set s := Real.sqrt (1 - r ^ 2)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by nlinarith)
    set t := (1 + s) / 2
    have ht : 0 < t := by positivity
    set c := Real.sqrt t
    have hc0 : 0 < c := Real.sqrt_pos.mpr ht
    have hc2 : c ^ 2 = t := Real.sq_sqrt ht.le
    let x : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![(c : ℂ), z / (2 * c)]
    have hx0 : x 0 = c := rfl
    have hx1 : x 1 = z / (2 * c) := rfl
    have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc0.ne'
    refine ⟨x, ?_, ?_⟩
    · have hn : ‖x‖ ^ 2 = 1 := by
        rw [norm_sq_fin_two, hx0, hx1, Complex.norm_real, Real.norm_of_nonneg hc0.le, norm_div,
          norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le, Complex.norm_ofNat, div_pow,
          mul_pow, hc2]
        have : 4 * t ^ 2 - 4 * t + r ^ 2 = 0 := by simp only [t]; nlinarith
        field_simp
        nlinarith
      have := norm_nonneg x
      nlinarith
    · rw [inner_J, hx0, hx1, Complex.conj_ofReal]
      field_simp

/-- The operator norm of `[[0, 2], [0, 0]]` is `2`. -/
theorem norm_J : ‖J‖ = 2 := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_two fun x => ?_
    have h := norm_sq_fin_two x
    rw [J_apply, PiLp.norm_single, norm_mul, Complex.norm_ofNat]
    have : ‖x 1‖ ≤ ‖x‖ := by
      nlinarith [norm_nonneg (x 0), norm_nonneg (x 1), norm_nonneg x, sq_nonneg (‖x 1‖ - ‖x‖)]
    linarith
  · have h := J.le_opNorm (EuclideanSpace.single 1 1)
    rw [J_apply] at h
    simpa using h

/-- **Sharpness of Crouzeix's constant.** If `‖p(J)‖ ≤ C · M` whenever `|p| ≤ M` on the
numerical range of `J = [[0, 2], [0, 0]]`, then `2 ≤ C`. -/
theorem two_le_of_crouzeix_bound (C : ℝ)
    (h : ∀ p : ℂ[X], ∀ M : ℝ, (∀ z ∈ numericalRange J, ‖p.eval z‖ ≤ M) → ‖aeval J p‖ ≤ C * M) :
    2 ≤ C := by
  have := h X 1 fun z hz => by
    rw [numericalRange_J] at hz
    simpa using hz
  simpa [norm_J] using this

end Crouzeix
