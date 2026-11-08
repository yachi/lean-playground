module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.RCLike.Lemmas

@[expose] public section

/-!
# Crouzeix's conjecture: the Lorist–Schwenninger perturbation lemma for `2`-dilations

Crouzeix's conjecture (2004) asserts that for every square complex matrix `A` and every
polynomial `p`,
`‖p(A)‖ ≤ 2 · max_{z ∈ W(A)} |p(z)|`, where `W(A)` is the numerical range of `A`.
It was proved in 2026, independently, by

* S. Jin, *The numerical range is a 2-spectral set*, Preprints.org 202607.1919 (first posted
  27 July 2026), and
* E. Lorist and F. L. Schwenninger, *A solution to Crouzeix's conjecture*, arXiv:2608.03841
  (4 August 2026).

This file formalizes the new ingredient of the Lorist–Schwenninger proof, their **Lemma 1**:

> Let `T ∈ L(H)`. Suppose there are a Hilbert space `K`, a contraction `Q ∈ L(K)` and an
> isometry `V : H → K` such that the operators `Eₙ := 2 V* Q*ⁿ V − T*ⁿ` (`n ≥ 1`) are uniformly
> bounded and commute with `T`. Then `‖T‖ ≤ 2`.

The paper reduces to the case that `T*T` has an eigenvector for the eigenvalue `‖T‖²`
(automatic in finite dimension, via an ultrapower in general). We prove the lemma under the
hypothesis that `T` attains its norm (`norm_le_two_of_dilation`), and unconditionally for
finite-dimensional `H` (`norm_le_two_of_dilation_of_finiteDimensional`), which is the case
needed for Crouzeix's conjecture on matrices.

We then formalize the abstract form of the theorem (Remark 3 (iv) of the paper, with the
Stinespring dilation taken as a hypothesis): if `θ` is a bounded unital-algebra homomorphism
from a commutative normed algebra into `L(H)`, `α` is bounded, and the "real part"
`½ (θ f + θ(α f)*)` has a contractive multiplicative dilation `V* π(f) V`, then
`‖θ f‖ ≤ 2 ‖f‖` (`norm_le_two_mul_of_dilation`).

For Crouzeix's conjecture one takes `𝒜 = A(Ω)` for a smooth convex `Ω ⊇ W(A)`, `θ f = f(A)`,
`α f` the Cauchy transform of `f̄`, `K = L²(∂Ω; H)`, `π f` multiplication by `f`, and
`V x = 2^{-1/2} P_Ω(·)^{1/2} x` with `P_Ω` the double-layer potential. That the double-layer
potential provides this dilation (positivity of `P_Ω` for convex `Ω ⊇ W(A)`, the identity
`2Φ(f) − f(A) = α(f)(A)*`) is classical (Delyon–Delyon 1999, Crouzeix 2007,
Crouzeix–Palencia 2017) and is **not** formalized here: Mathlib lacks Cauchy integrals over
general convex curves and the double-layer potential.
-/

open scoped InnerProduct InnerProductSpace
open ContinuousLinearMap

set_option linter.unusedSectionVars false

namespace Crouzeix

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The defect `Eₙ = 2 V* Q*ⁿ V − T*ⁿ` of `V* Q* V` from being a `2`-dilation of `T*`. -/
noncomputable def dilationDefect (T : H →L[ℂ] H) (Q : K →L[ℂ] K) (V : H →L[ℂ] K) (n : ℕ) :
    H →L[ℂ] H :=
  (2 : ℂ) • ((adjoint V) ∘L ((adjoint Q) ^ n) ∘L V) - (adjoint T) ^ n

lemma dilationDefect_apply (T : H →L[ℂ] H) (Q : K →L[ℂ] K) (V : H →L[ℂ] K) (n : ℕ) (x : H) :
    dilationDefect T Q V n x =
      (2 : ℂ) • (adjoint V) (((adjoint Q) ^ n) (V x)) - ((adjoint T) ^ n) x := rfl

lemma re_ofReal_mul' (r : ℝ) (z : ℂ) : RCLike.re ((r : ℂ) * z) = r * RCLike.re z := by
  simp [RCLike.re_to_complex]

lemma adjoint_pow (T : H →L[ℂ] H) (n : ℕ) : (adjoint T) ^ n = adjoint (T ^ n) := by
  rw [← star_eq_adjoint, ← star_eq_adjoint, star_pow]

lemma pow_apply_succ (T : H →L[ℂ] H) (n : ℕ) (x : H) : (T ^ (n + 1)) x = (T ^ n) (T x) := by
  rw [pow_succ]; rfl

lemma norm_adjoint_pow_apply_le {Q : K →L[ℂ] K} (hQ : ‖Q‖ ≤ 1) (n : ℕ) (v : K) :
    ‖((adjoint Q) ^ n) v‖ ≤ ‖v‖ := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_apply_succ]
    refine (ih _).trans ?_
    calc ‖(adjoint Q) v‖ ≤ ‖(adjoint Q)‖ * ‖v‖ := le_opNorm _ _
      _ = ‖Q‖ * ‖v‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ 1 * ‖v‖ := by gcongr
      _ = ‖v‖ := one_mul _

lemma norm_le_one_of_isometry {V : H →L[ℂ] K} (hV : ∀ x, ‖V x‖ = ‖x‖) : ‖V‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by rw [hV, one_mul]

lemma norm_adjoint_apply_le {V : H →L[ℂ] K} (hV : ∀ x, ‖V x‖ = ‖x‖) (v : K) :
    ‖(adjoint V) v‖ ≤ ‖v‖ :=
  calc ‖(adjoint V) v‖ ≤ ‖(adjoint V)‖ * ‖v‖ := le_opNorm _ _
    _ = ‖V‖ * ‖v‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ 1 * ‖v‖ := by gcongr; exact norm_le_one_of_isometry hV
    _ = ‖v‖ := one_mul _

/-- If `‖x‖ = 1` and `‖T x‖ = ‖T‖`, then `x` is an eigenvector of `T*T` for `‖T‖²`. -/
lemma adjoint_apply_apply_eq_of_norm_attained (T : H →L[ℂ] H) {x : H} (hx : ‖x‖ = 1)
    (hTx : ‖T x‖ = ‖T‖) : (adjoint T) (T x) = ((‖T‖ ^ 2 : ℝ) : ℂ) • x := by
  set κ := ‖T‖
  rw [← sub_eq_zero, ← norm_eq_zero]
  have hre : RCLike.re ⟪(adjoint T) (T x), x⟫_ℂ = κ ^ 2 := by
    rw [adjoint_inner_left, inner_self_eq_norm_sq, hTx]
  have hle : ‖(adjoint T) (T x)‖ ≤ κ * κ := by
    calc ‖(adjoint T) (T x)‖ ≤ ‖(adjoint T)‖ * ‖T x‖ := le_opNorm _ _
      _ = κ * κ := by rw [LinearIsometryEquiv.norm_map, hTx]
  have hsq : ‖(adjoint T) (T x) - ((κ ^ 2 : ℝ) : ℂ) • x‖ ^ 2 ≤ 0 := by
    rw [@norm_sub_sq ℂ, inner_smul_right, re_ofReal_mul', hre, norm_smul, hx,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    nlinarith [norm_nonneg ((adjoint T) (T x))]
  nlinarith [norm_nonneg ((adjoint T) (T x) - ((κ ^ 2 : ℝ) : ℂ) • x)]

/-- **Lemma 1 of Lorist–Schwenninger** (for norm-attaining `T`): if `Q` is a contraction, `V`
an isometry, and the defects `Eₙ = 2 V* Q*ⁿ V − T*ⁿ` (`n ≥ 1`) are uniformly bounded and commute
with `T`, then `‖T‖ ≤ 2`. -/
theorem norm_le_two_of_dilation (T : H →L[ℂ] H) (Q : K →L[ℂ] K) (V : H →L[ℂ] K)
    (hQ : ‖Q‖ ≤ 1) (hV : ∀ x, ‖V x‖ = ‖x‖) (B : ℝ)
    (hB : ∀ n, 1 ≤ n → ‖dilationDefect T Q V n‖ ≤ B)
    (hcomm : ∀ n, 1 ≤ n → Commute (dilationDefect T Q V n) T)
    (hattain : ∃ x, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖) : ‖T‖ ≤ 2 := by
  by_contra hlt
  push Not at hlt
  set κ := ‖T‖ with hκ
  obtain ⟨x, hx, hTx⟩ := hattain
  have hTT := adjoint_apply_apply_eq_of_norm_attained T hx hTx
  rw [← hκ] at hTT
  set E := dilationDefect T Q V
  have hκ1 : 1 < κ := by linarith
  have hκ0 : 0 < κ := by linarith
  -- the error vector `u = Q* V T x − κ V x`
  set u : K := (adjoint Q) (V (T x)) - (κ : ℂ) • V x with hu
  set c : ℝ := ‖u‖ ^ 2 / (κ * (κ - 1)) with hc
  have hc0 : 0 ≤ c := by positivity
  -- `mₙ = Re ⟨x, Eₙ Tⁿ x⟩`
  set m : ℕ → ℝ := fun n => RCLike.re ⟪x, E n ((T ^ n) x)⟫_ℂ with hm
  -- powers of `T*` applied to `T x`
  have hTpow : ∀ n,
      ((adjoint T) ^ n) ((adjoint T) (T x)) = ((κ ^ 2 : ℝ) : ℂ) • ((adjoint T) ^ n) x := by
    intro n; rw [hTT, map_smul]
  -- the key identity: `κ mₙ − mₙ₊₁ = κ(κ−1)‖T*ⁿx‖² − 2 Re⟨T*ⁿx, V*Q*ⁿu⟩`
  have hkey : ∀ n, 1 ≤ n → κ * m n - m (n + 1) =
      κ * (κ - 1) * ‖((adjoint T) ^ n) x‖ ^ 2 -
        2 * RCLike.re ⟪((adjoint T) ^ n) x, (adjoint V) (((adjoint Q) ^ n) u)⟫_ℂ := by
    intro n hn
    have h1 : E n ((T ^ n) x) = (T ^ n) (E n x) := by
      have := ((hcomm n hn).pow_right n).eq
      change (E n * T ^ n) x = (T ^ n * E n) x
      rw [this]
    have h2 : E (n + 1) ((T ^ (n + 1)) x) = (T ^ n) (E (n + 1) (T x)) := by
      have := ((hcomm (n + 1) (by omega)).pow_right n).eq
      have h' : E (n + 1) * T ^ (n + 1) = T ^ n * (E (n + 1) * T) := by
        rw [pow_succ, ← mul_assoc, this, mul_assoc]
      change (E (n + 1) * T ^ (n + 1)) x = (T ^ n * (E (n + 1) * T)) x
      rw [h']
    have hvec : (κ : ℂ) • E n x - E (n + 1) (T x) =
        ((κ * (κ - 1) : ℝ) : ℂ) • ((adjoint T) ^ n) x -
          (2 : ℂ) • (adjoint V) (((adjoint Q) ^ n) u) := by
      simp only [E, dilationDefect_apply, pow_apply_succ, hTpow, hu, map_sub, map_smul]
      push_cast
      module
    have hinner : ∀ z : H, RCLike.re ⟪x, (T ^ n) z⟫_ℂ = RCLike.re ⟪((adjoint T) ^ n) x, z⟫_ℂ := by
      intro z; rw [adjoint_pow, adjoint_inner_left]
    simp only [hm]
    rw [h1, h2, hinner, hinner]
    have h3 := congrArg (fun v => RCLike.re ⟪((adjoint T) ^ n) x, v⟫_ℂ) hvec
    simp only [inner_sub_right, inner_smul_right, map_sub, re_ofReal_mul',
      inner_self_eq_norm_sq_to_K] at h3
    rw [h3]
    simp [RCLike.re_to_complex, ← Complex.ofReal_pow]
  -- lower bound on each increment
  have hnormy : ∀ n, ‖(adjoint V) (((adjoint Q) ^ n) u)‖ ≤ ‖u‖ := fun n =>
    (norm_adjoint_apply_le hV _).trans (norm_adjoint_pow_apply_le hQ n u)
  have hstep : ∀ n, 1 ≤ n → m (n + 1) ≤ κ * m n + c := by
    intro n hn
    have hk := hkey n hn
    set t := ‖((adjoint T) ^ n) x‖
    set s := ‖(adjoint V) (((adjoint Q) ^ n) u)‖
    have hre :=
      re_inner_le_norm (𝕜 := ℂ) (((adjoint T) ^ n) x) ((adjoint V) (((adjoint Q) ^ n) u))
    have hs := hnormy n
    have ha : 0 < κ * (κ - 1) := by nlinarith
    have : -(‖u‖ ^ 2 / (κ * (κ - 1))) ≤ κ * (κ - 1) * t ^ 2 - 2 * (t * s) := by
      rw [neg_div', div_le_iff₀ ha]
      nlinarith [sq_nonneg (κ * (κ - 1) * t - s), norm_nonneg u, norm_nonneg (((adjoint T) ^ n) x),
        norm_nonneg ((adjoint V) (((adjoint Q) ^ n) u)),
        mul_le_mul_of_nonneg_left hs (norm_nonneg u)]
    linarith
  -- telescoping: `m_{N+1} + c/(κ−1) ≤ κ^N (m₁ + c/(κ−1))`
  have htel : ∀ N : ℕ, m (N + 1) + c / (κ - 1) ≤ κ ^ N * (m 1 + c / (κ - 1)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hs := hstep (N + 1) (by omega)
      have hid : c + c / (κ - 1) = κ * (c / (κ - 1)) := by
        field_simp
        ring
      calc m (N + 1 + 1) + c / (κ - 1) ≤ κ * m (N + 1) + c + c / (κ - 1) := by linarith
        _ = κ * (m (N + 1) + c / (κ - 1)) := by rw [add_assoc, hid]; ring
        _ ≤ κ * (κ ^ N * (m 1 + c / (κ - 1))) := by gcongr
        _ = κ ^ (N + 1) * (m 1 + c / (κ - 1)) := by ring
  -- the sequence `mₙ` is bounded below
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 le_rfl)
  have hbdd : ∀ n, 1 ≤ n → -(B * (2 + B)) ≤ m n := by
    intro n hn
    have hTn : ‖(T ^ n) x‖ ≤ 2 + B := by
      have hrep : (adjoint T) ^ n = (2 : ℂ) • ((adjoint V) ∘L ((adjoint Q) ^ n) ∘L V) - E n := by
        simp only [E, dilationDefect]; abel
      have hW : ‖(adjoint V) ∘L ((adjoint Q) ^ n) ∘L V‖ ≤ 1 :=
        opNorm_le_bound _ zero_le_one fun z => by
          rw [one_mul, comp_apply, comp_apply, ← hV z]
          exact (norm_adjoint_apply_le hV _).trans (norm_adjoint_pow_apply_le hQ n _)
      calc ‖(T ^ n) x‖ ≤ ‖T ^ n‖ * ‖x‖ := le_opNorm _ _
        _ = ‖(adjoint T) ^ n‖ := by rw [hx, mul_one, adjoint_pow, LinearIsometryEquiv.norm_map]
        _ ≤ ‖(2 : ℂ) • ((adjoint V) ∘L ((adjoint Q) ^ n) ∘L V)‖ + ‖E n‖ := by
          rw [hrep]; exact norm_sub_le _ _
        _ ≤ 2 * 1 + B := by
          rw [norm_smul]; gcongr
          · simp
          · exact hB n hn
        _ = 2 + B := by ring
    have : |m n| ≤ B * (2 + B) := by
      calc |m n| ≤ ‖⟪x, E n ((T ^ n) x)⟫_ℂ‖ := RCLike.abs_re_le_norm _
        _ ≤ ‖x‖ * ‖E n ((T ^ n) x)‖ := norm_inner_le_norm _ _
        _ ≤ 1 * (‖E n‖ * ‖(T ^ n) x‖) := by rw [hx]; gcongr; exact le_opNorm _ _
        _ ≤ 1 * (B * (2 + B)) := by gcongr; exact hB n hn
        _ = B * (2 + B) := one_mul _
    linarith [neg_abs_le (m n)]
  -- hence `m₁ + c/(κ−1) ≥ 0`
  have hD : 0 ≤ m 1 + c / (κ - 1) := by
    by_contra hneg
    push Not at hneg
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((B * (2 + B) + c / (κ - 1)) / -(m 1 + c / (κ - 1)))
      hκ1
    rw [div_lt_iff₀ (by linarith)] at hN
    have h1 := htel N
    have h2 := hbdd (N + 1) (by omega)
    have h3 : 0 ≤ c / (κ - 1) := div_nonneg hc0 (by linarith)
    have h4 : κ ^ N * -(m 1 + c / (κ - 1)) = -(κ ^ N * (m 1 + c / (κ - 1))) := by ring
    linarith
  -- the upper bound (4): `‖u‖² ≤ 2κ² − κ m₁ − κ³`
  have hm1 : m 1 = 2 * RCLike.re ⟪V x, (adjoint Q) (V (T x))⟫_ℂ - κ ^ 2 := by
    simp only [hm, E, pow_one, dilationDefect_apply, hTT, inner_sub_right, inner_smul_right,
      map_sub, adjoint_inner_right, inner_self_eq_norm_sq_to_K, hx]
    simp only [RCLike.re_to_complex, Complex.mul_re]
    norm_num
    norm_cast
  have hVx : ‖V x‖ = 1 := by rw [hV, hx]
  have hQVTx : ‖(adjoint Q) (V (T x))‖ ≤ κ := by
    calc ‖(adjoint Q) (V (T x))‖ ≤ ‖(adjoint Q)‖ * ‖V (T x)‖ := le_opNorm _ _
      _ = ‖Q‖ * κ := by rw [LinearIsometryEquiv.norm_map, hV, hTx]
      _ ≤ 1 * κ := by gcongr
      _ = κ := one_mul _
  have hu2 : ‖u‖ ^ 2 ≤ 2 * κ ^ 2 - κ * m 1 - κ ^ 3 := by
    have : RCLike.re ((κ : ℂ) * ⟪(adjoint Q) (V (T x)), V x⟫_ℂ) =
        κ * RCLike.re ⟪V x, (adjoint Q) (V (T x))⟫_ℂ := by
      rw [re_ofReal_mul', inner_re_symm]
    rw [hu, @norm_sub_sq ℂ, inner_smul_right, norm_smul, hVx, Complex.norm_real,
      Real.norm_of_nonneg hκ0.le, this, hm1]
    nlinarith [norm_nonneg ((adjoint Q) (V (T x)))]
  -- combine
  set s := ‖u‖ ^ 2
  have hs0 : 0 ≤ s := by positivity
  have hd : 1 < (κ - 1) ^ 2 := by nlinarith
  have hlow : -s ≤ κ * m 1 * (κ - 1) ^ 2 := by
    have h' : -(c / (κ - 1)) ≤ m 1 := by linarith
    have hκ1' : 0 < κ - 1 := by linarith
    rw [hc, div_div, neg_le, le_div_iff₀ (by positivity)] at h'
    have : κ * m 1 * (κ - 1) ^ 2 = -(-m 1 * (κ * (κ - 1) * (κ - 1))) := by ring
    linarith
  have h5 := mul_le_mul_of_nonneg_right hu2 (by positivity : (0 : ℝ) ≤ (κ - 1) ^ 2)
  have h6 : 0 < κ ^ 2 * (κ - 1) ^ 2 * (κ - 2) := mul_pos (by positivity) (by linarith)
  have h7 := mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ (κ - 1) ^ 2 - 1)
  nlinarith

/-- In finite dimension every operator attains its norm on the unit sphere. -/
lemma exists_norm_apply_eq_opNorm [FiniteDimensional ℂ H] [Nontrivial H] (T : H →L[ℂ] H) :
    ∃ x, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ := by
  have : ProperSpace H := FiniteDimensional.proper_rclike ℂ H
  obtain ⟨x, hxS, hmax⟩ := (isCompact_sphere (0 : H) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) (T.continuous.norm.continuousOn)
  have hx : ‖x‖ = 1 := by simpa using hxS
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · simpa [hx] using T.le_opNorm x
  · refine opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hz : ((‖y‖⁻¹ : ℝ) : ℂ) • y ∈ Metric.sphere (0 : H) 1 := by
        simp [norm_smul, hy'.ne']
      have := hmax hz
      simp only [Set.mem_ofPred_eq, map_smul, norm_smul, Complex.norm_real, norm_inv,
        Real.norm_of_nonneg hy'.le] at this
      rw [inv_mul_le_iff₀ hy'] at this
      linarith

/-- **Lemma 1 of Lorist–Schwenninger**, finite-dimensional `H` (no extra hypothesis). -/
theorem norm_le_two_of_dilation_of_finiteDimensional [FiniteDimensional ℂ H]
    (T : H →L[ℂ] H) (Q : K →L[ℂ] K) (V : H →L[ℂ] K)
    (hQ : ‖Q‖ ≤ 1) (hV : ∀ x, ‖V x‖ = ‖x‖) (B : ℝ)
    (hB : ∀ n, 1 ≤ n → ‖dilationDefect T Q V n‖ ≤ B)
    (hcomm : ∀ n, 1 ≤ n → Commute (dilationDefect T Q V n) T) : ‖T‖ ≤ 2 := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact opNorm_le_bound _ zero_le_two fun y => by simp [Subsingleton.elim y 0]
  · exact norm_le_two_of_dilation T Q V hQ hV B hB hcomm (exists_norm_apply_eq_opNorm T)

/-- **Abstract Crouzeix theorem** (Lorist–Schwenninger, Remark 3 (iv), with the dilation of
`Φ = ½(θ + θ(α ·)*)` given as a hypothesis). Let `θ : 𝒜 → L(H)` be a bounded algebra
homomorphism from a commutative normed algebra, `α : 𝒜 → 𝒜` bounded, and suppose
`2 V* π(f) V = θ f + θ(α f)*` for a contractive multiplicative `π : 𝒜 → L(K)` and an isometry
`V`. Then `‖θ f‖ ≤ 2 ‖f‖` for every `f`.

For Crouzeix's conjecture, `θ f = f(A)` and the dilation comes from the double-layer
potential on a convex domain containing `W(A)`; see the module docstring. -/
theorem norm_le_two_mul_of_dilation [FiniteDimensional ℂ H]
    {𝒜 : Type*} [NormedCommRing 𝒜] [NormedAlgebra ℂ 𝒜]
    (θ : 𝒜 →ₐ[ℂ] (H →L[ℂ] H)) (Cθ : ℝ) (hθ : ∀ f, ‖θ f‖ ≤ Cθ * ‖f‖)
    (α : 𝒜 → 𝒜) (Cα : ℝ) (hα : ∀ f, ‖α f‖ ≤ Cα * ‖f‖)
    (π : 𝒜 →* (K →L[ℂ] K)) (hπ : ∀ f, ‖π f‖ ≤ ‖f‖)
    (V : H →L[ℂ] K) (hV : ∀ x, ‖V x‖ = ‖x‖)
    (hΦ : ∀ f, (2 : ℂ) • ((adjoint V) ∘L π f ∘L V) = θ f + adjoint (θ (α f))) (f : 𝒜) :
    ‖θ f‖ ≤ 2 * ‖f‖ := by
  -- first the case `‖g‖ = 1`
  have hunit : ∀ g : 𝒜, ‖g‖ = 1 → ‖θ g‖ ≤ 2 := by
    intro g hg
    have hE : ∀ n, dilationDefect (θ g) (π g) V n = θ (α (g ^ n)) := by
      intro n
      have h1 : (adjoint V) ∘L (adjoint (π g) ^ n) ∘L V =
          adjoint ((adjoint V) ∘L π (g ^ n) ∘L V) := by
        rw [adjoint_pow, ← map_pow π, adjoint_comp, adjoint_comp, adjoint_adjoint]; rfl
      have h2 : adjoint (θ g) ^ n = adjoint (θ (g ^ n)) := by rw [adjoint_pow, ← map_pow θ]
      have h3 : ∀ X : H →L[ℂ] H, (2 : ℂ) • adjoint X = adjoint ((2 : ℂ) • X) := by
        intro X
        rw [LinearIsometryEquiv.map_smulₛₗ]
        congr 1
        exact (Complex.conj_ofReal 2).symm
      rw [dilationDefect, h1, h2, h3, hΦ, map_add, adjoint_adjoint]
      abel
    refine norm_le_two_of_dilation_of_finiteDimensional (θ g) (π g) V
      (by simpa [hg] using hπ g) hV (|Cθ| * |Cα|) (fun n hn => ?_) (fun n _ => ?_)
    · rw [hE]
      have hgn : ‖g ^ n‖ ≤ 1 := by
        calc ‖g ^ n‖ ≤ ‖g‖ ^ n := norm_pow_le' g (by omega)
          _ = 1 := by rw [hg, one_pow]
      calc ‖θ (α (g ^ n))‖ ≤ Cθ * ‖α (g ^ n)‖ := hθ _
        _ ≤ |Cθ| * ‖α (g ^ n)‖ := by gcongr; exact le_abs_self _
        _ ≤ |Cθ| * (Cα * ‖g ^ n‖) := by gcongr; exact hα _
        _ ≤ |Cθ| * (|Cα| * 1) := by
          gcongr
          · exact le_abs_self _
        _ = |Cθ| * |Cα| := by ring
    · rw [hE]; exact ((Commute.all _ _).map θ)
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hf' : 0 < ‖f‖ := norm_pos_iff.mpr hf
    have h := hunit (((‖f‖⁻¹ : ℝ) : ℂ) • f) (by simp [norm_smul, hf'.ne'])
    rw [map_smul, norm_smul, Complex.norm_real, norm_inv, Real.norm_of_nonneg hf'.le,
      inv_mul_le_iff₀ hf'] at h
    linarith

end Crouzeix
