module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

public section

/-!
# Cutoff regularization of `1 + 2 + 3 + ⋯`

Source: PBS Space Time, *Why Does -1/12 Keep Appearing Everywhere In Physics?*
(YouTube, 2026-10-08, <https://www.youtube.com/watch?v=w6229Ivy_Lo>).

The video says that damping the divergent sum `1 + 2 + 3 + ⋯` with a cutoff splits it into an
infinite piece that is "shared" (and so cancels in any physical difference) and a finite piece,
and that the finite piece is `-1/12`. It then applies this to the 1D Casimir effect.

Claims formalized here:

* [6:22-6:45, 13:38-13:56] Exponential cutoff: for `ε > 0`,
  `∑ n e^{-nε} = e^{-ε} / (1 - e^{-ε})²` (`MinusTwelfth.hasSum_cutoff`), which equals
  `1 / (4 sinh²(ε/2))` (`MinusTwelfth.cutoffSum_eq_sinh`); the divergent part is exactly
  `1/ε²` and the finite part tends to `-1/12` (`MinusTwelfth.tendsto_cutoff_sub`).
* [6:22-7:12] 1D Casimir energy with a frequency cutoff: the regulated energy is
  `ħ c d / (2 π ε²)` (proportional to the gap `d`, a uniform energy density) plus a finite part
  tending to `-π ħ c / (24 d)` (`MinusTwelfth.hasSum_casimirCut`,
  `MinusTwelfth.casimirCut_eq`, `MinusTwelfth.tendsto_casimirCut_sub`).
* The value `-1/12` obtained here is `riemannZeta (-1)` (proved in `MinusTwelfth.Zeta`, which
  this file deliberately does not import); see the note before `tendsto_cutoff_sub`.

Lean cannot prove physics: the physical modelling assumptions (which modes exist, the shape
of the cutoff, and the claim that the `ε⁻²` piece is cancelled by the outside vacuum) are stated
in the doc comments; only the mathematics is proved.
-/

open Filter Topology Real

namespace MinusTwelfth

/-- [6:22-6:45] Exponential cutoff, closed form: for `ε > 0`,
`∑ n e^{-nε} = e^{-ε} / (1 - e^{-ε})²`. The video's "add a cutoff so each term is damped". -/
theorem hasSum_cutoff {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun n : ℕ => (n : ℝ) * exp (-(n : ℝ) * ε)) (exp (-ε) / (1 - exp (-ε)) ^ 2) := by
  have hr : ‖exp (-ε)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_lt_one_iff]
    linarith
  convert hasSum_coe_mul_geometric_of_norm_lt_one hr using 2 with n
  rw [← Real.exp_nat_mul]
  ring_nf

/-- The cutoff sum in hyperbolic form, `e^{-ε}/(1-e^{-ε})² = 1/(4 sinh²(ε/2))`
(the hint form used to expand around `ε = 0`). -/
theorem cutoffSum_eq_sinh (ε : ℝ) (hε : ε ≠ 0) :
    exp (-ε) / (1 - exp (-ε)) ^ 2 = 1 / (4 * sinh (ε / 2) ^ 2) := by
  have h1 : exp (-ε) = exp (-(ε / 2)) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  have h2 : exp (ε / 2) * exp (-(ε / 2)) = 1 := by rw [← exp_add]; simp
  have hs : sinh (ε / 2) ≠ 0 := by
    rw [Ne, sinh_eq_zero]; exact fun h => hε (by linarith)
  have hne : 1 - exp (-ε) ≠ 0 := by
    intro h
    have : exp (-ε) = exp 0 := by rw [exp_zero]; linarith
    exact hε (by simpa using exp_injective this)
  rw [div_eq_div_iff (pow_ne_zero 2 hne) (mul_ne_zero four_ne_zero (pow_ne_zero 2 hs)),
    sinh_eq, h1]
  linear_combination (exp (ε / 2) * exp (-(ε / 2)) + 1 - 2 * exp (-(ε / 2)) ^ 2) * h2

/-- Third-order Taylor bound for `exp` on `(0, 1]`, from `Real.exp_bound`. -/
private lemma exp_taylor3 {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    |exp ε - (1 + ε + ε ^ 2 / 2 + ε ^ 3 / 6)| ≤ ε ^ 4 * (5 / 96) := by
  have := Real.exp_bound (x := ε) (by rw [abs_of_pos h0]; exact h1) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos h0] at this
  exact this

/-- `E ↦ (1 + E) / E²` is antitone on `(0, ∞)`. -/
private lemma one_add_div_sq_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (1 + b) / b ^ 2 ≤ (1 + a) / a ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hab) (add_pos ha hb).le,
    mul_nonneg (sub_nonneg.2 hab) (mul_pos ha hb).le]

/-- `(1 + ε q) / (ε q)² - 1/ε² = ((1 + ε q - q²) / ε²) / q²`. -/
private lemma key_identity {ε q : ℝ} (hε : ε ≠ 0) (hq : q ≠ 0) :
    (1 + ε * q) / (ε * q) ^ 2 - 1 / ε ^ 2 = ((1 + ε * q - q ^ 2) / ε ^ 2) / q ^ 2 := by
  field_simp

/-- `e^{-ε}/(1-e^{-ε})² = (1 + E)/E²` with `E = e^ε - 1`. -/
private lemma cutoff_eq_E {ε : ℝ} (hε : 0 < ε) :
    exp (-ε) / (1 - exp (-ε)) ^ 2 = (1 + (exp ε - 1)) / (exp ε - 1) ^ 2 := by
  have h1 : 1 < exp ε := one_lt_exp_iff.2 hε
  have h2 : exp ε - 1 ≠ 0 := by linarith
  have h3 : 1 - (exp ε)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; exact (inv_lt_one_of_one_lt₀ h1).ne'
  rw [exp_neg]
  field_simp
  ring

/-- [6:22-6:45, 13:38-13:56] "Cutoff regularization separates a shared infinite part from a
finite part, and the finite part of `1 + 2 + 3 + ⋯` is `-1/12`."

With the exponential cutoff `n ↦ n e^{-nε}`, subtracting exactly the divergent part `1/ε²`
leaves a quantity that tends to `-1/12` as `ε → 0⁺`.

The number `-1/12` here is `riemannZeta (-1)`; that identity is proved separately in
`MinusTwelfth.Zeta` (not imported here). The video's point is that the cutoff and zeta
regularizations agree on the finite part. -/
theorem tendsto_cutoff_sub :
    Tendsto (fun ε : ℝ => ∑' n : ℕ, (n : ℝ) * exp (-(n : ℝ) * ε) - 1 / ε ^ 2)
      (𝓝[>] 0) (𝓝 (-1 / 12)) := by
  -- polynomial brackets for `(e^ε - 1)/ε`
  let qp : ℝ → ℝ := fun ε => 1 + ε / 2 + ε ^ 2 / 6 + 5 / 96 * ε ^ 3
  let qm : ℝ → ℝ := fun ε => 1 + ε / 2 + ε ^ 2 / 6 - 5 / 96 * ε ^ 3
  -- `(1 + ε q - q²)/ε²` for `q = qp`, `q = qm`
  let Np : ℝ → ℝ := fun ε => -1 / 12 - ε ^ 2 / 36 + 5 / 96 * ε ^ 2
    - 2 * (5 / 96) * ε * (1 + ε / 2 + ε ^ 2 / 6) - (5 / 96) ^ 2 * ε ^ 4
  let Nm : ℝ → ℝ := fun ε => -1 / 12 - ε ^ 2 / 36 - 5 / 96 * ε ^ 2
    + 2 * (5 / 96) * ε * (1 + ε / 2 + ε ^ 2 / 6) - (5 / 96) ^ 2 * ε ^ 4
  have lim (N q : ℝ → ℝ) (hN : Continuous N) (hq : Continuous q) (hN0 : N 0 = -1 / 12)
      (hq0 : q 0 = 1) : Tendsto (fun ε => N ε / q ε ^ 2) (𝓝[>] 0) (𝓝 (-1 / 12)) := by
    have := (hN.tendsto 0).div ((hq.tendsto 0).pow 2) (by simp [hq0])
    rw [hN0, hq0, one_pow, div_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlo := lim Np qp (by fun_prop) (by fun_prop) (by norm_num [Np]) (by norm_num [qp])
  have hhi := lim Nm qm (by fun_prop) (by fun_prop) (by norm_num [Nm]) (by norm_num [qm])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  all_goals
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε ⟨h0, h1⟩
    have hT := abs_le.1 (exp_taylor3 h0 h1.le)
    have hqm : 0 < qm ε := by
      simp only [qm]; nlinarith [pow_pos h0 2, pow_pos h0 3, pow_le_one₀ h0.le h1.le (n := 3)]
    have hqp : 0 < qp ε := by simp only [qp]; positivity
    rw [(hasSum_cutoff h0).tsum_eq, cutoff_eq_E h0]
  · -- lower bracket: `E ≤ ε qp`
    have hE : exp ε - 1 ≤ ε * qp ε := by simp only [qp]; nlinarith
    have hpos : 0 < ε * qm ε := mul_pos h0 hqm
    have hEpos : 0 < exp ε - 1 := by simp only [qm] at hpos; nlinarith
    have := one_add_div_sq_anti hEpos hE
    have hid := key_identity h0.ne' hqp.ne'
    have : (1 + ε * qp ε - qp ε ^ 2) / ε ^ 2 = Np ε := by
      simp only [qp, Np]; field_simp; ring
    rw [this] at hid
    linarith
  · -- upper bracket: `ε qm ≤ E`
    have hE : ε * qm ε ≤ exp ε - 1 := by simp only [qm]; nlinarith
    have hpos : 0 < ε * qm ε := mul_pos h0 hqm
    have := one_add_div_sq_anti hpos hE
    have hid := key_identity h0.ne' hqm.ne'
    have : (1 + ε * qm ε - qm ε ^ 2) / ε ^ 2 = Nm ε := by
      simp only [qm, Nm]; field_simp; ring
    rw [this] at hid
    linarith

/-- The regulated 1D Casimir energy between plates a distance `d` apart, with the cutoff
`ε` placed on the frequency:
`E_cut(d, ε) = ½ (π ħ c / d) ∑ n e^{-n ε π / d}`.

Physical modelling assumptions (not proved, encoded in this definition): the allowed modes
between the plates have `ω_n = n π c / d` (standing waves vanishing at both plates), each
contributes its zero-point energy `ħ ω_n / 2 = ½ (π ħ c / d) n`, and the cutoff damps mode `n`
by `e^{-ε ω_n / c} = e^{-n ε π / d}`. -/
@[expose] noncomputable def casimirCut (ħ c d ε : ℝ) : ℝ :=
  (1 / 2) * (π * ħ * c / d) * ∑' n : ℕ, (n : ℝ) * exp (-(n : ℝ) * ε * π / d)

/-- [6:22-7:12] Closed form of the regulated Casimir mode sum: for `d > 0` and `ε > 0` the
damped sum `∑ n e^{-n ε π / d}` converges, to `e^{-δ}/(1 - e^{-δ})²` with `δ = ε π / d`. -/
theorem hasSum_casimirCut {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    HasSum (fun n : ℕ => (n : ℝ) * exp (-(n : ℝ) * ε * π / d))
      (exp (-(ε * π / d)) / (1 - exp (-(ε * π / d))) ^ 2) := by
  convert hasSum_cutoff (by positivity : 0 < ε * π / d) using 3 with n
  ring_nf

/-- [6:22-7:12] "The divergent part is proportional to `d`": the regulated Casimir energy
splits exactly as `ħ c d / (2 π ε²)` plus `(π ħ c / (2d))` times the finite part of the cutoff
sum of claim 1, evaluated at `δ = ε π / d`.

The divergent piece `ħ c d / (2 π ε²)` is linear in `d`, i.e. a uniform energy density
`ħ c / (2 π ε²)` per unit length. The video's physical argument (an assumption, not proved
here) is that the same density fills the vacuum outside the plates, so it does not depend on
where the plates sit and drops out of the force. -/
theorem casimirCut_eq (ħ c : ℝ) {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    casimirCut ħ c d ε = ħ * c * d / (2 * π * ε ^ 2) + π * ħ * c / (2 * d) *
      (∑' n : ℕ, (n : ℝ) * exp (-(n : ℝ) * (ε * π / d)) - 1 / (ε * π / d) ^ 2) := by
  have h : ∀ n : ℕ, -(n : ℝ) * ε * π / d = -(n : ℝ) * (ε * π / d) := fun n => by ring
  simp_rw [casimirCut, h]
  generalize ∑' n : ℕ, (n : ℝ) * exp (-(n : ℝ) * (ε * π / d)) = S
  field_simp
  ring

/-- [6:22-7:12] 1D Casimir energy: after subtracting the shared divergent piece
`ħ c d / (2 π ε²)`, the regulated energy tends to `-π ħ c / (24 d)` as the cutoff is removed
(`ε → 0⁺`). This is `(π ħ c / (2d)) · (-1/12)`: the `-1/12` of claim 1 times
`ħ ω₁ / 2`, the zero-point energy of the lowest mode.

No sign condition on `ħ` or `c` is needed (the statement is linear in `ħ c`); only `d > 0`. -/
theorem tendsto_casimirCut_sub (ħ c : ℝ) {d : ℝ} (hd : 0 < d) :
    Tendsto (fun ε => casimirCut ħ c d ε - ħ * c * d / (2 * π * ε ^ 2)) (𝓝[>] 0)
      (𝓝 (-π * ħ * c / (24 * d))) := by
  have hδ : Tendsto (fun ε : ℝ => ε * π / d) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => ε * π / d) (𝓝 0) (𝓝 (0 * π / d)) :=
        ((continuous_id.mul continuous_const).div_const d).tendsto 0
      rw [zero_mul, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact (by positivity : 0 < ε * π / d)
  have := (tendsto_cutoff_sub.comp hδ).const_mul (π * ħ * c / (2 * d))
  have hval : π * ħ * c / (2 * d) * (-1 / 12) = -π * ħ * c / (24 * d) := by
    field_simp
    ring
  rw [hval] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [Function.comp_apply, casimirCut_eq ħ c hd hε]
  ring

end MinusTwelfth
