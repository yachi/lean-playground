module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

public section

/-!
# The Riemann zeta function behind "1 + 2 + 3 + ⋯ = -1/12"

Source: PBS Space Time, *Why Does -1/12 Keep Appearing Everywhere In Physics?*
(YouTube, 2026-10-08, <https://www.youtube.com/watch?v=w6229Ivy_Lo>).

This file formalizes the purely mathematical statements the video makes about `ζ`.
No physics is proved here: where a statement is used in the video as a stand-in for a physical
computation (the 3D Casimir effect), the doc comment says so.

Claims, with timestamps and theorem names:

* [2:16-2:26] `ζ(s) = ∑ 1/n^s`, convergent for `re s > 1`: `zeta_eq_series`.
* [2:26-2:32] the series only defines `ζ` for `s > 1`: `not_summable_of_le_one`.
* [2:32-2:55] `ζ` extends analytically to `ℂ \ {1}`, and uniquely: `differentiableAt_zeta`,
  `zeta_unique_continuation`.
* [2:55-3:00] `ζ(-1) = -1/12`: `zeta_neg_one`.
* [8:03-8:10] the 3D Casimir sum gives `ζ(-3) = 1/120`: `zeta_neg_three`.
* [3:06-3:14] this does not mean `1 + 2 + 3 + ⋯ = -1/12`: `not_summable_naturals`,
  `not_summable_series_at_neg_one`, `tsum_naturals_eq_zero`; and `ζ` has a pole at `1`:
  `zeta_residue_one`, `not_continuousAt_zeta_one`.
-/

open Complex Filter Topology

namespace MinusTwelfth

/-- [2:16-2:26] "ζ(s) = ∑ 1/n^s, and this converges for s > 1." For complex `s` with
`1 < re s` the series `∑ 1/(n+1)^s` is summable and its sum is `riemannZeta s`. -/
theorem zeta_eq_series {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) ∧
      riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s := by
  refine ⟨?_, zeta_eq_tsum_one_div_nat_add_one_cpow hs⟩
  have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
  simpa using h

/-- [2:26-2:32] "The series only defines zeta for s > 1." For real `s ≤ 1` the real series
`∑ 1/(n+1)^s` diverges. -/
theorem not_summable_of_le_one {s : ℝ} (hs : s ≤ 1) :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ s) := by
  intro h
  have h' : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ s) := by
    refine h.congr fun n => ?_
    rw [abs_of_pos (by positivity)]
  exact absurd ((Real.summable_one_div_nat_add_rpow 1 s).mp h') (not_lt.mpr hs)

/-- [2:32-2:55] "Zeta can be analytically continued to the whole complex plane except s = 1."
`riemannZeta` is complex-differentiable at every `s ≠ 1`. -/
theorem differentiableAt_zeta {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

/-- [2:32-2:55] The analytic continuation is *unique*: any `f` that is complex-differentiable on
`ℂ \ {1}` and agrees with the series `∑ 1/(n+1)^s` on `re s > 1` equals `riemannZeta` on
`ℂ \ {1}` (identity theorem; `ℂ \ {1}` is open and connected). -/
theorem zeta_unique_continuation {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {1}ᶜ)
    (hser : ∀ s : ℂ, 1 < s.re → f s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) :
    Set.EqOn f riemannZeta {1}ᶜ := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hz : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp [rank_real_complex]) 1).isPreconnected
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by norm_num
  refine (hf.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hz.analyticOnNhd hU) hconn
    (z₀ := 2) (by norm_num) ?_
  filter_upwards [hopen.mem_nhds h2] with s hs
  rw [hser s hs, zeta_eq_tsum_one_div_nat_add_one_cpow hs]

/-- [2:55-3:00] "ζ(-1) = -1/12." -/
theorem zeta_neg_one : riemannZeta (-1) = -1 / 12 := by
  rw [show (-1 : ℂ) = -((1 : ℕ) : ℂ) by simp, riemannZeta_neg_nat_eq_bernoulli, bernoulli_two]
  norm_num

/-- [8:03-8:10] "In the 3D Casimir calculation, +1/120 appears in place of -1/12":
`ζ(-3) = 1/120`. Physical assumption stood in for: the regularized sum of cubed mode
frequencies between parallel plates is replaced by `ζ(-3)`; only that value is proved here. -/
theorem zeta_neg_three : riemannZeta (-3) = 1 / 120 := by
  have hb : bernoulli 4 = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]
  rw [show (-3 : ℂ) = -((3 : ℕ) : ℂ) by simp, riemannZeta_neg_nat_eq_bernoulli,
    show (3 : ℕ) + 1 = 4 from rfl, hb]
  norm_num

/-- [3:06-3:14] "None of this means 1 + 2 + 3 + ⋯ = -1/12." The series `1 + 2 + 3 + ⋯`
diverges. -/
theorem not_summable_naturals : ¬ Summable (fun n : ℕ => (n : ℝ) + 1) := by
  intro h
  have := not_summable_of_le_one (s := -1) (by norm_num)
  exact this (h.congr fun n => by simp [Real.rpow_neg_one])

/-- [3:06-3:14] The defining series of `ζ` at `s = -1` (which is `∑ (n+1)`) is not summable, so
`ζ(-1)` is *not* given by the series. -/
theorem not_summable_series_at_neg_one :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (-1 : ℂ)) := by
  intro h
  have h' : Summable (fun n : ℕ => (fun m : ℕ => 1 / (m : ℂ) ^ (-1 : ℂ)) (n + 1)) := by
    refine h.congr fun n => ?_
    simp
  have h'' := Complex.summable_one_div_nat_cpow.mp ((summable_nat_add_iff 1).mp h')
  norm_num at h''

/-- [3:06-3:14] In Lean, `∑'` of a non-summable series is the junk value `0`, so even
literally `∑' n, (n + 1) = 0 ≠ -1/12`: the `-1/12` comes from `ζ`, not from the sum. -/
theorem tsum_naturals_eq_zero : ∑' n : ℕ, ((n : ℝ) + 1) = 0 :=
  tsum_eq_zero_of_not_summable not_summable_naturals

/-- [3:06-3:14] `ζ` has a pole at `s = 1` with residue 1: `(s - 1) ζ(s) → 1` as `s → 1`. -/
theorem zeta_residue_one :
    Tendsto (fun s => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  riemannZeta_residue_one

/-- [3:06-3:14] Consequently `ζ` is not continuous at `s = 1` (so it is genuinely a pole). -/
theorem not_continuousAt_zeta_one : ¬ ContinuousAt riemannZeta 1 := by
  intro hc
  have h0 : Tendsto (fun s => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 0) := by
    have hc' : ContinuousAt (fun s : ℂ => (s - 1) * riemannZeta s) 1 :=
      ((continuousAt_id.sub continuousAt_const).mul hc)
    have := hc'.tendsto
    rw [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact one_ne_zero (tendsto_nhds_unique zeta_residue_one h0)

end MinusTwelfth
