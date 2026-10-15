module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

public section

/-!
# Where `-1/12` shows up in physics: Casimir energies and critical string dimensions

Claims from PBS Space Time, *Why Does -1/12 Keep Appearing Everywhere In Physics?*
(YouTube, 2026-10-08, https://www.youtube.com/watch?v=w6229Ivy_Lo).

Lean cannot prove physics. Every theorem below formalizes only the *mathematical* step the
video states: the algebra of a physics formula, or a special value of a zeta function that
replaces a divergent sum. The physical modelling assumption that a theorem stands in for is
named in its doc comment. In every case the assumption "`1 + 2 + 3 + ⋯` is replaced by
`-1/12`" is made precise as "the divergent sum is replaced by `riemannZeta (-1)`", which
Mathlib proves equals `-1/12` (`riemannZeta_neg_one`).

1. **[7:02-7:12]** 1D Casimir energy `E(d) = (π ħ c / d) · (1/2) · (-1/12) = -π ħ c / (24 d)`:
   `casimirEnergy1D_eq`, `casimirEnergy1D_eq_zeta` (the `-1/12` is `riemannZeta (-1)`),
   `casimirEnergy1D_neg` (`E d < 0`), `casimirEnergy1D_strictMonoOn` (energy is lower when
   the plates are closer), `hasDerivAt_casimirEnergy1D`, `casimirForce1D_eq`
   (`F(d) = -dE/dd = -π ħ c / (24 d²)`), `casimirForce1D_neg` (attractive).
2. **[11:24-11:54]** Bosonic string: `(D-2)/2 · (1 + 2 + 3 + ⋯) ↦ (D-2)/2 · (-1/12)
   = -(D-2)/24`, and `(D-2)/24 = 1 ↔ D = 26`: `bosonic_zeroPoint_eq`,
   `bosonic_zeroPoint_eq_zeta`, `bosonic_critical_iff`, `bosonic_critical_iff_nat`.
3. **[13:09-13:16]** Superstrings live in 10 dimensions (light-cone NS sector):
   `hurwitzZeta_neg_one_half` (`ζ(-1, 1/2) = 1/24`, from Mathlib's `hurwitzZeta_neg_nat`),
   `boson_zeroPoint_eq`, `ns_fermion_zeroPoint_eq`, `superstring_zeroPoint_eq_zeta`,
   `superstring_zeroPoint_eq`, `superstring_critical_iff`, `superstring_critical_iff_nat`.
4. **[8:03-8:10]** 3D Casimir energy per unit area `-π² ħ c / (720 d³)`:
   `riemannZeta_neg_three` (`ζ(-3) = 1/120`), `one_div_720_eq`, `casimirEnergy3D_eq_zeta`,
   `casimirEnergy3D_neg`. The prefactor `-π² ħ c / (6 d³)` multiplying the regularized
   `∑ n³` is taken from the literature (Casimir 1948), not derived here.
-/

open Real

namespace MinusTwelfth

/-! ## The zeta values that replace the divergent sums -/

/-- The video's "`1 + 2 + 3 + ⋯ = -1/12`" made precise: the analytic continuation of the
Riemann zeta function at `-1` (Mathlib's `riemannZeta`) equals `-1/12`. -/
theorem riemannZeta_neg_one : riemannZeta (-1) = -1 / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  rw [bernoulli_two] at h
  push_cast at h
  rw [h]
  norm_num

/-- [8:03-8:10] The 3D Casimir energy uses "`1³ + 2³ + 3³ + ⋯ = 1/120`", made precise as
`riemannZeta (-3) = 1/120`. -/
theorem riemannZeta_neg_three : riemannZeta (-3) = 1 / 120 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 3
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four] at h
  push_cast at h
  rw [h]
  norm_num

end MinusTwelfth

@[expose] public section

namespace MinusTwelfth

/-- The 1D Casimir energy as the video writes it at [7:02-7:12]:
`E(d) = (π ħ c / d) · (1/2) · (-1/12)`. Physical assumption: the zero-point energy of the
standing modes between plates a distance `d` apart is `(π ħ c / d) · (1/2) · ∑ n`, and the
divergent `∑ n` is replaced by its zeta-regularized value `-1/12`. -/
noncomputable def casimirEnergy1D (ħ c d : ℝ) : ℝ := π * ħ * c / d * (1 / 2) * (-1 / 12)

/-- The 1D Casimir force `F(d) = -dE/dd`. -/
noncomputable def casimirForce1D (ħ c d : ℝ) : ℝ := -deriv (casimirEnergy1D ħ c) d

/-- The 3D Casimir energy per unit plate area, `-π² ħ c / (720 d³)` [8:03-8:10]. -/
noncomputable def casimirEnergy3D (ħ c d : ℝ) : ℝ := -(π ^ 2 * ħ * c) / (720 * d ^ 3)

end MinusTwelfth

end

namespace MinusTwelfth

/-! ## Claim 1: the 1D Casimir effect -/

/-- [7:02-7:12] "`E = (π ħ c / d) · (1/2) · (-1/12) = -π ħ c / (24 d)`". -/
theorem casimirEnergy1D_eq (ħ c d : ℝ) : casimirEnergy1D ħ c d = -(π * ħ * c) / (24 * d) := by
  unfold casimirEnergy1D
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · field_simp
    ring

/-- [7:02-7:12] The `-1/12` in the 1D Casimir energy is exactly `riemannZeta (-1)`:
`E(d) = (π ħ c / d) · (1/2) · ζ(-1)`. Physical assumption: the divergent mode sum `∑ n` is
replaced by `ζ(-1)`. -/
theorem casimirEnergy1D_eq_zeta (ħ c d : ℝ) :
    (casimirEnergy1D ħ c d : ℂ) = (π * ħ * c / d : ℝ) * (1 / 2) * riemannZeta (-1) := by
  rw [riemannZeta_neg_one, casimirEnergy1D]
  push_cast
  ring

/-- [7:02-7:12] The Casimir energy is negative: `E d < 0` for `d > 0`. -/
theorem casimirEnergy1D_neg {ħ c d : ℝ} (hħ : 0 < ħ) (hc : 0 < c) (hd : 0 < d) :
    casimirEnergy1D ħ c d < 0 := by
  rw [casimirEnergy1D_eq, neg_div]
  exact neg_neg_of_pos (by positivity)

/-- [7:02-7:12] "The energy is lower when the plates are closer": `E` is strictly increasing
in the plate separation `d > 0`. -/
theorem casimirEnergy1D_strictMonoOn {ħ c : ℝ} (hħ : 0 < ħ) (hc : 0 < c) :
    StrictMonoOn (casimirEnergy1D ħ c) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  rw [casimirEnergy1D_eq, casimirEnergy1D_eq, neg_div, neg_div, neg_lt_neg_iff]
  have hk : 0 < π * ħ * c := by positivity
  exact div_lt_div_of_pos_left hk (by positivity) (by linarith)

/-- [7:02-7:12] The derivative of the Casimir energy: `dE/dd = π ħ c / (24 d²)` for `d ≠ 0`. -/
theorem hasDerivAt_casimirEnergy1D (ħ c : ℝ) {d : ℝ} (hd : d ≠ 0) :
    HasDerivAt (casimirEnergy1D ħ c) (π * ħ * c / (24 * d ^ 2)) d := by
  have hfun : casimirEnergy1D ħ c = fun x ↦ -(π * ħ * c / 24) * x⁻¹ := by
    funext x
    rw [casimirEnergy1D_eq]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · field_simp
  rw [hfun]
  convert (hasDerivAt_inv hd).const_mul (-(π * ħ * c / 24)) using 1
  field_simp

/-- [7:02-7:12] The Casimir force `F(d) = -dE/dd = -π ħ c / (24 d²)`. -/
theorem casimirForce1D_eq (ħ c : ℝ) {d : ℝ} (hd : d ≠ 0) :
    casimirForce1D ħ c d = -(π * ħ * c) / (24 * d ^ 2) := by
  rw [casimirForce1D, (hasDerivAt_casimirEnergy1D ħ c hd).deriv, neg_div]

/-- [7:02-7:12] The Casimir force is attractive: `F(d) < 0` for `d > 0`. -/
theorem casimirForce1D_neg {ħ c d : ℝ} (hħ : 0 < ħ) (hc : 0 < c) (hd : 0 < d) :
    casimirForce1D ħ c d < 0 := by
  rw [casimirForce1D_eq ħ c hd.ne', neg_div]
  exact neg_neg_of_pos (by positivity)

/-! ## Claim 2: the bosonic string lives in 26 dimensions -/

/-- [11:24-11:54] "`(D-2)/2 · (1 + 2 + 3 + ⋯)` with `1 + 2 + 3 + ⋯ = -1/12` gives
`-(D-2)/24`". -/
theorem bosonic_zeroPoint_eq (D : ℝ) : (D - 2) / 2 * (-1 / 12) = -(D - 2) / 24 := by ring

/-- [11:24-11:54] The same zero-point energy with the `-1/12` written as `riemannZeta (-1)`.
Physical assumption: each of the `D - 2` transverse oscillators contributes
`(1/2) ∑ n`, and the divergent `∑ n` is replaced by `ζ(-1)`. -/
theorem bosonic_zeroPoint_eq_zeta (D : ℂ) :
    (D - 2) / 2 * riemannZeta (-1) = -(D - 2) / 24 := by
  rw [riemannZeta_neg_one]
  ring

/-- [11:24-11:54] The zero-point shift `(D-2)/24` equals `1` exactly when `D = 26`.
Physical assumption: Lorentz invariance of the light-cone quantization forces this
shift to be `1` (normal-ordering constant `a = 1`). -/
theorem bosonic_critical_iff (D : ℝ) : (D - 2) / 24 = 1 ↔ D = 26 := by
  constructor <;> intro h <;> linarith

/-- [11:24-11:54] The critical dimension of the bosonic string, with `D` a natural number. -/
theorem bosonic_critical_iff_nat (D : ℕ) : ((D : ℝ) - 2) / 24 = 1 ↔ D = 26 := by
  rw [bosonic_critical_iff]
  exact_mod_cast Iff.rfl

/-! ## Claim 3: the superstring lives in 10 dimensions -/

/-- [13:09-13:16] The Hurwitz zeta value `ζ(-1, 1/2) = 1/24`, the regularized value of the
half-integer mode sum `1/2 + 3/2 + 5/2 + ⋯`. Mathlib: `ζ(-1, x) = -B₂(x)/2`, and
`B₂(1/2) = 1/4 - 1/2 + 1/6 = -1/12`. -/
theorem hurwitzZeta_neg_one_half :
    HurwitzZeta.hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) (-1) = 1 / 24 := by
  have h := HurwitzZeta.hurwitzZeta_neg_nat (k := 1) one_ne_zero
    (x := 1 / 2) ⟨by norm_num, by norm_num⟩
  push_cast at h
  rw [h]
  simp [Polynomial.bernoulli_def, Finset.sum_range_succ]
  norm_num

/-- [13:09-13:16] Each transverse boson contributes `(1/2) · ζ(-1) = -1/24`. -/
theorem boson_zeroPoint_eq : (1 / 2 : ℂ) * riemannZeta (-1) = -1 / 24 := by
  rw [riemannZeta_neg_one]
  ring

/-- [13:09-13:16] Each transverse Neveu-Schwarz fermion, with half-integer modes,
contributes `-(1/2) · ζ(-1, 1/2) = -1/48`. Physical assumption: fermionic zero-point
energies enter with the opposite sign, and the divergent `∑ (n - 1/2)` is replaced by the
Hurwitz zeta value `ζ(-1, 1/2)`. -/
theorem ns_fermion_zeroPoint_eq :
    -(1 / 2 : ℂ) * HurwitzZeta.hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) (-1) = -1 / 48 := by
  rw [hurwitzZeta_neg_one_half]
  ring

/-- [13:09-13:16] The total NS-sector zero-point energy of `D - 2` transverse bosons and
`D - 2` transverse fermions is `-(D-2)/16`, computed from the zeta values. -/
theorem superstring_zeroPoint_eq_zeta (D : ℂ) :
    (D - 2) * ((1 / 2) * riemannZeta (-1)
      - (1 / 2) * HurwitzZeta.hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) (-1))
      = -(D - 2) / 16 := by
  rw [riemannZeta_neg_one, hurwitzZeta_neg_one_half]
  ring

/-- [13:09-13:16] The algebra: `(D-2) · (-1/24 - 1/48) = -(D-2)/16`. -/
theorem superstring_zeroPoint_eq (D : ℝ) : (D - 2) * (-1 / 24 - 1 / 48) = -(D - 2) / 16 := by
  ring

/-- [13:09-13:16] "Superstrings give 10 dimensions": the NS zero-point energy
`(D-2) · (-1/24 - 1/48)` equals `-1/2` exactly when `D = 10`. Physical assumption:
Lorentz invariance forces the NS-sector normal-ordering constant to be `-1/2`. -/
theorem superstring_critical_iff (D : ℝ) : (D - 2) * (-1 / 24 - 1 / 48) = -1 / 2 ↔ D = 10 := by
  constructor <;> intro h <;> linarith

/-- [13:09-13:16] The superstring critical dimension, with `D` a natural number. -/
theorem superstring_critical_iff_nat (D : ℕ) :
    ((D : ℝ) - 2) * (-1 / 24 - 1 / 48) = -1 / 2 ↔ D = 10 := by
  rw [superstring_critical_iff]
  exact_mod_cast Iff.rfl

/-! ## Claim 4: the 3D Casimir effect -/

/-- [8:03-8:10] The arithmetic behind the `720`: `1/720 = (1/6) · (1/120)`. -/
theorem one_div_720_eq : (1 / 720 : ℝ) = 1 / 6 * (1 / 120) := by norm_num

/-- [8:03-8:10] "Energy per unit area `-π² ħ c / (720 d³)`", written as
`-(π² ħ c / (6 d³)) · ζ(-3)`. Physical assumption, taken from the literature (Casimir 1948)
and not derived here: the regularized energy per unit area is `-(π² ħ c / (6 d³)) · ∑ n³`
with the divergent `∑ n³` replaced by `ζ(-3) = 1/120`. -/
theorem casimirEnergy3D_eq_zeta (ħ c d : ℝ) :
    (casimirEnergy3D ħ c d : ℂ) = -(π ^ 2 * ħ * c / (6 * d ^ 3) : ℝ) * riemannZeta (-3) := by
  rw [riemannZeta_neg_three, casimirEnergy3D]
  push_cast
  rcases eq_or_ne (d : ℂ) 0 with hd | hd
  · simp [hd]
  · field_simp
    ring

/-- [8:03-8:10] The 3D Casimir energy per unit area is negative for `d > 0`. -/
theorem casimirEnergy3D_neg {ħ c d : ℝ} (hħ : 0 < ħ) (hc : 0 < c) (hd : 0 < d) :
    casimirEnergy3D ħ c d < 0 := by
  rw [casimirEnergy3D, neg_div]
  exact neg_neg_of_pos (by positivity)

end MinusTwelfth
