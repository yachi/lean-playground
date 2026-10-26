module

public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

public section

/-!
# What a complex derivative means: a local rotation and scaling

Claims from Zundamon's Theorem, *What Does a Complex Derivative Actually Mean?*
(YouTube, 2026-10-26, https://youtu.be/2-95hN4fgmE).

The video's answer: the derivative `f'(a)` is the constant of proportionality in
`Δw ≈ f'(a) Δz` near `z = a`, so "what complex differentiation means comes down to what
multiplication by a complex number means". Writing `α = r e^{iθ}` in polar form, multiplying
by `α` scales the plane by `r` and rotates it by `θ`. So near `a`, a complex differentiable
`f` looks like "rotate by `arg f'(a)`, then scale by `|f'(a)|`".

1. **[8:40-9:50]** The derivative as a multiplier, `Δw ≈ f'(a) Δz`, made precise with
   limits: `hasDerivAt_iff_sub_mul_isLittleO` (the same statement holds for real `f`;
   it is the one Mathlib lemma `hasDerivAt_iff_isLittleO_nhds_zero` for any field).
2. **[10:20-10:45]** Euler's formula and polar form `α = |α| e^{i arg α}`:
   `polar_form`, `exp_mul_I_eq`.
3. **[10:45-13:15]** Multiplication in polar form multiplies the lengths and adds the angles:
   `polar_mul`, `norm_mul_eq`, `arg_mul_eq`. Multiplying by `α` is "scale by `|α|` after the
   rotation by `arg α`": `mul_eq_smul_rotation`. Multiplying the whole grid by `α ≠ 0`
   keeps angles (it is a conformal map) and scales all distances by `|α|`:
   `isConformalMap_mul`, `dist_mul_mul`.
4. **[9:55-10:00, 16:31]** The punchline: near `a`, `f(a + h) - f(a)` is the rotation by
   `arg f'(a)` scaled by `|f'(a)|`, applied to `h`, up to `o(h)`:
   `sub_rotation_isLittleO_of_hasDerivAt`. When `f'(a) ≠ 0`, `f` is conformal at `a`:
   `conformalAt_of_hasDerivAt`.
5. **[13:56-16:30]** A worked example at a point `z₀` built from `ln 2`. The transcript does
   not show the formulas on screen, so we read it as `f(z) = e^z` (differentiated "just as in
   the real case") at `z₀ = ln r + iθ`, and prove it for every `r > 0` and `θ`:
   `f'(z₀) = r e^{iθ}`, so `f` scales by `r` and rotates by `θ`
   near `z₀`: `exp_deriv_at_log_add`, `exp_local_scale_rotate`, and the case
   `z₀ = ln 2 + iπ/2` with `f'(z₀) = 2i` (scale by 2, quarter turn): `exp_deriv_ln_two`.
-/

open Complex Asymptotics Filter Topology

namespace ComplexDerivative

/-! ### 1. The derivative is a local multiplier -/

/-- **[8:40-9:50]** `Δw ≈ f'(a) Δz`, made precise: `f` has complex derivative `f'` at `a`
exactly when `f (a + h) - f a - f' * h` is `o(h)` as `h → 0`. -/
theorem hasDerivAt_iff_sub_mul_isLittleO {f : ℂ → ℂ} {f' a : ℂ} :
    HasDerivAt f f' a ↔ (fun h ↦ f (a + h) - f a - f' * h) =o[𝓝 0] fun h ↦ h := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [smul_eq_mul, mul_comm]

/-- The real version, which the video starts from: `Δy ≈ f'(a) Δx`. -/
theorem hasDerivAt_iff_sub_mul_isLittleO_real {f : ℝ → ℝ} {f' a : ℝ} :
    HasDerivAt f f' a ↔ (fun h ↦ f (a + h) - f a - f' * h) =o[𝓝 0] fun h ↦ h := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [smul_eq_mul, mul_comm]

/-! ### 2-3. Multiplication by a complex number: scale and rotate -/

/-- **[10:20]** Euler's formula: `e^{iθ} = cos θ + i sin θ`. -/
theorem exp_mul_I_eq (θ : ℝ) : exp (θ * I) = Real.cos θ + Real.sin θ * I := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]

/-- **[10:45]** Polar form: every complex number is `r e^{iθ}` with `r = |α|`, `θ = arg α`. -/
theorem polar_form (α : ℂ) : α = ‖α‖ * exp (arg α * I) :=
  (norm_mul_exp_arg_mul_I α).symm

/-- **[11:30]** Multiplication in polar form: `(r e^{iθ})(s e^{iφ}) = (rs) e^{i(θ+φ)}`. -/
theorem polar_mul (r s θ φ : ℝ) :
    (r * exp (θ * I)) * (s * exp (φ * I)) =
      ((r * s : ℝ) : ℂ) * exp ((θ + φ : ℝ) * I) := by
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

/-- **[12:00]** Multiplying by `α` multiplies every length by `|α|`. -/
theorem norm_mul_eq (α z : ℂ) : ‖α * z‖ = ‖α‖ * ‖z‖ := norm_mul α z

/-- **[12:00]** Multiplying by `α` adds `arg α` to every angle (as angles mod `2π`). -/
theorem arg_mul_eq {α z : ℂ} (hα : α ≠ 0) (hz : z ≠ 0) :
    (arg (α * z) : Real.Angle) = arg α + arg z :=
  arg_mul_coe_angle hα hz

/-- **[12:30]** Multiplying by `α` is the rotation of the plane by `arg α`, followed by the
scaling by `|α|`. -/
theorem mul_eq_smul_rotation (α z : ℂ) :
    α * z = ‖α‖ • rotation (Circle.exp (arg α)) z := by
  rw [rotation_apply, Circle.coe_exp, Complex.real_smul, ← mul_assoc, norm_mul_exp_arg_mul_I]

/-- **[13:05-13:20]** Multiplying the whole grid by `α ≠ 0` keeps angles: it is a conformal
map. -/
theorem isConformalMap_mul {α : ℂ} (hα : α ≠ 0) :
    IsConformalMap (α • ContinuousLinearMap.id ℝ ℂ) := by
  refine ⟨‖α‖, norm_ne_zero_iff.mpr hα,
    (rotation (Circle.exp (arg α))).toLinearIsometry, ?_⟩
  ext z
  simp [mul_eq_smul_rotation α z]

/-- **[13:05-13:20]** Multiplying by `α` scales every distance on the grid by `|α|`. -/
theorem dist_mul_mul (α z w : ℂ) : dist (α * z) (α * w) = ‖α‖ * dist z w := by
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]

/-! ### 4. Complex differentiation as local rotation and scaling -/

/-- **[9:55-10:00, 16:31]** Near `a`, a function with complex derivative `f'` at `a` acts on
small changes `h` as the rotation by `arg f'` followed by the scaling by `|f'|`, up to `o(h)`. -/
theorem sub_rotation_isLittleO_of_hasDerivAt {f : ℂ → ℂ} {f' a : ℂ} (hf : HasDerivAt f f' a) :
    (fun h ↦ f (a + h) - f a - ‖f'‖ • rotation (Circle.exp (arg f')) h) =o[𝓝 0]
      fun h ↦ h := by
  simpa only [← mul_eq_smul_rotation] using hasDerivAt_iff_sub_mul_isLittleO.mp hf

/-- When `f'(a) ≠ 0`, the local rotation and scaling keeps angles: `f` is conformal at `a`. -/
theorem conformalAt_of_hasDerivAt {f : ℂ → ℂ} {f' a : ℂ} (hf : HasDerivAt f f' a)
    (hf' : f' ≠ 0) : ConformalAt f a :=
  hf.differentiableAt.conformalAt (hf.deriv ▸ hf')

/-! ### 5. The worked example `f(z) = e^z` -/

/-- **[13:56-15:00]** At `z₀ = ln r + iθ`, the derivative of `e^z` is `r e^{iθ}`. -/
theorem exp_deriv_at_log_add {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasDerivAt exp (r * exp (θ * I)) (Real.log r + θ * I) := by
  have h := hasDerivAt_exp ((Real.log r : ℂ) + θ * I)
  rwa [Complex.exp_add, ← ofReal_exp, Real.exp_log hr] at h

/-- **[15:00-16:30]** Hence, for `θ ∈ (-π, π]`, near `z₀ = ln r + iθ` the exponential scales
small changes by `r` and rotates them by `θ`, up to `o(h)`. -/
theorem exp_local_scale_rotate {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    (fun h ↦ exp (Real.log r + θ * I + h) - exp (Real.log r + θ * I)
        - r • rotation (Circle.exp θ) h) =o[𝓝 0] fun h ↦ h := by
  have h := sub_rotation_isLittleO_of_hasDerivAt (exp_deriv_at_log_add hr θ)
  have hnorm : ‖(r : ℂ) * exp (θ * I)‖ = r := by
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hr.le]
  have harg : arg ((r : ℂ) * exp (θ * I)) = θ := by
    rw [arg_real_mul _ hr, arg_exp_mul_I, toIocMod_eq_self _ |>.mpr]
    simpa [neg_add_cancel_left, two_mul] using hθ
  rwa [hnorm, harg] at h

/-- One instance: `z₀ = ln 2 + iπ/2`: `(e^z)'(z₀) = 2i`, a scaling by `2` and a
quarter turn. -/
theorem exp_deriv_ln_two :
    HasDerivAt exp (2 * I) (Real.log 2 + (Real.pi / 2 : ℝ) * I) ∧
      ‖(2 : ℂ) * I‖ = 2 ∧ arg (2 * I) = Real.pi / 2 := by
  refine ⟨?_, by simp, ?_⟩
  · have h := exp_deriv_at_log_add (r := 2) two_pos (Real.pi / 2)
    rw [exp_mul_I_eq, Real.cos_pi_div_two, Real.sin_pi_div_two] at h
    simpa using h
  · have : (2 : ℂ) * I = ((2 : ℝ) : ℂ) * I := by norm_num
    rw [this, arg_real_mul _ two_pos, arg_I]

end ComplexDerivative
