module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

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

Timestamps are from the video's frames and subtitles.

0. **[5:30-6:30]** The complex derivative is the limit of `Δf/Δz`, of the same form as the
   real one: `hasDerivAt_iff_tendsto_slope'`. The familiar rules give the same results:
   `(z²)' = 2z`, `(sin z)' = cos z`, `(e^z)' = e^z`: `deriv_rules`.
1. **[9:15-10:00]** The derivative as a multiplier, `Δw ≈ f'(a) Δz`, "strictly speaking"
   from the limit definition: `hasDerivAt_iff_sub_mul_isLittleO` (and
   `hasDerivAt_iff_sub_mul_isLittleO_real` for `Δy ≈ f'(a) Δx`).
2. **[10:15-10:45]** Euler's formula `e^{iθ} = cos θ + i sin θ` and the polar form
   `α = |α| e^{i arg α}`: `exp_mul_I_eq`, `polar_form`.
3. **[11:00-13:15]** `z₁ z₂ = r₁ r₂ e^{i(θ₁+θ₂)}`: "Length → Multiply, Angle → Add":
   `polar_mul`, `norm_mul_eq`, `arg_mul_eq`. The example `α = √3 + i = 2 e^{iπ/6}` (length 2,
   angle 30°): `sqrt_three_add_I`. Multiplying by `α` is the rotation by `arg α` followed by
   the scaling by `|α|`: `mul_eq_smul_rotation`. Multiplying the whole grid by `α ≠ 0` keeps
   angles (a conformal map) and scales all distances by `|α|`: `isConformalMap_mul`,
   `dist_mul_mul`.
4. **[15:45-16:15]** Near `a`, `f(a + h) - f(a)` is the rotation by `arg f'(a)` scaled by
   `|f'(a)|`, applied to `h`, and "as we zoom in the distortion becomes smaller": the error
   is `o(h)`: `sub_rotation_isLittleO_of_hasDerivAt`. When `f'(a) ≠ 0`, `f` is conformal at
   `a`: `conformalAt_of_hasDerivAt`.
5. **[13:30-16:00]** The worked example `f(z) = e^{iz}`, `f'(z) = i e^{iz}`
   (`hasDerivAt_exp_I_mul`), at `z₀ = -π/4 - i ln 2`: `f(z₀) = 2 e^{-iπ/4}` and
   `f'(z₀) = 2 e^{iπ/4}` (`exp_I_mul_z₀`, `deriv_z₀`), so "multiplying by `f'(z₀)` means
   scaling by a factor of 2 and rotating by `π/4`": `norm_deriv_z₀`, `arg_deriv_z₀`,
   `exp_I_mul_local_scale_rotate`.
-/

open Complex Asymptotics Filter Topology

namespace ComplexDerivative

/-! ### 0. The limit definition and the familiar rules -/

/-- **[5:30]** `df/dz = lim_{Δz → 0} (f(z + Δz) - f(z)) / Δz`, the same form as the real
definition, where `Δz → 0` from every direction in the plane. -/
theorem hasDerivAt_iff_tendsto_slope' {f : ℂ → ℂ} {f' z : ℂ} :
    HasDerivAt f f' z ↔
      Tendsto (fun Δz ↦ (f (z + Δz) - f z) / Δz) (𝓝[≠] 0) (𝓝 f') := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [smul_eq_mul, div_eq_inv_mul]

/-- **[6:15-6:30]** "We get exactly the same corresponding results":
`(z²)' = 2z`, `(sin z)' = cos z`, `(e^z)' = e^z`. -/
theorem deriv_rules (z : ℂ) :
    HasDerivAt (fun z ↦ z ^ 2) (2 * z) z ∧ HasDerivAt sin (cos z) z ∧
      HasDerivAt exp (exp z) z := by
  refine ⟨?_, Complex.hasDerivAt_sin z, hasDerivAt_exp z⟩
  simpa using hasDerivAt_pow 2 z

/-! ### 1. The derivative is a local multiplier -/

/-- **[9:15-10:00]** `Δw ≈ f'(a) Δz`, made precise: `f` has complex derivative `f'` at `a`
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

/-- **[10:15]** Euler's formula: `e^{iθ} = cos θ + i sin θ`. -/
theorem exp_mul_I_eq (θ : ℝ) : exp (θ * I) = Real.cos θ + Real.sin θ * I := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]

/-- **[10:30]** Polar form: every complex number is `r e^{iθ}` with `r = |α|`, `θ = arg α`. -/
theorem polar_form (α : ℂ) : α = ‖α‖ * exp (arg α * I) :=
  (norm_mul_exp_arg_mul_I α).symm

/-- **[11:00-11:30]** Multiplication in polar form: `(r e^{iθ})(s e^{iφ}) = (rs) e^{i(θ+φ)}`. -/
theorem polar_mul (r s θ φ : ℝ) :
    (r * exp (θ * I)) * (s * exp (φ * I)) =
      ((r * s : ℝ) : ℂ) * exp ((θ + φ : ℝ) * I) := by
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

/-- **[11:30]** "Length → Multiply": multiplying by `α` multiplies every length by `|α|`. -/
theorem norm_mul_eq (α z : ℂ) : ‖α * z‖ = ‖α‖ * ‖z‖ := norm_mul α z

/-- **[11:30]** "Angle → Add": multiplying by `α` adds `arg α` to every angle (as angles
mod `2π`). -/
theorem arg_mul_eq {α z : ℂ} (hα : α ≠ 0) (hz : z ≠ 0) :
    (arg (α * z) : Real.Angle) = arg α + arg z :=
  arg_mul_coe_angle hα hz

/-- **[13:00-13:15]** Multiplying by `α` is the rotation of the plane by `arg α`, followed by the
scaling by `|α|`. -/
theorem mul_eq_smul_rotation (α z : ℂ) :
    α * z = ‖α‖ • rotation (Circle.exp (arg α)) z := by
  rw [rotation_apply, Circle.coe_exp, Complex.real_smul, ← mul_assoc, norm_mul_exp_arg_mul_I]

/-- **[12:45-13:15]** Multiplying the whole grid by `α ≠ 0` keeps angles: it is a conformal
map. -/
theorem isConformalMap_mul {α : ℂ} (hα : α ≠ 0) :
    IsConformalMap (α • ContinuousLinearMap.id ℝ ℂ) := by
  refine ⟨‖α‖, norm_ne_zero_iff.mpr hα,
    (rotation (Circle.exp (arg α))).toLinearIsometry, ?_⟩
  ext z
  simp [mul_eq_smul_rotation α z]

/-- **[12:45-13:15]** Multiplying by `α` scales every distance on the grid by `|α|`. -/
theorem dist_mul_mul (α z w : ℂ) : dist (α * z) (α * w) = ‖α‖ * dist z w := by
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]

/-- A complex number `r e^{iθ}` with `r > 0` and `θ ∈ (-π, π]` has length `r` and angle `θ`. -/
theorem norm_arg_polar {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    ‖(r : ℂ) * exp (θ * I)‖ = r ∧ arg ((r : ℂ) * exp (θ * I)) = θ := by
  refine ⟨?_, ?_⟩
  · rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hr.le]
  · rw [arg_real_mul _ hr, arg_exp_mul_I, toIocMod_eq_self _ |>.mpr]
    simpa [neg_add_cancel_left, two_mul] using hθ

/-- **[11:45-12:15]** The example `α = √3 + i = 2 e^{iπ/6}`: length 2, angle 30°. -/
theorem sqrt_three_add_I :
    (Real.sqrt 3 + I : ℂ) = 2 * exp ((Real.pi / 6 : ℝ) * I) ∧
      ‖(Real.sqrt 3 + I : ℂ)‖ = 2 ∧ arg (Real.sqrt 3 + I) = Real.pi / 6 := by
  have h : (Real.sqrt 3 + I : ℂ) = ((2 : ℝ) : ℂ) * exp ((Real.pi / 6 : ℝ) * I) := by
    rw [exp_mul_I_eq, Real.cos_pi_div_six, Real.sin_pi_div_six]
    push_cast
    ring
  have hθ : Real.pi / 6 ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  obtain ⟨hn, ha⟩ := norm_arg_polar two_pos hθ
  rw [h]
  exact ⟨by push_cast; rfl, hn, ha⟩

/-! ### 4. Complex differentiation as local rotation and scaling -/

/-- **[15:45-16:15]** Near `a`, a function with complex derivative `f'` at `a` acts on
small changes `h` as the rotation by `arg f'` followed by the scaling by `|f'|`, up to `o(h)`. -/
theorem sub_rotation_isLittleO_of_hasDerivAt {f : ℂ → ℂ} {f' a : ℂ} (hf : HasDerivAt f f' a) :
    (fun h ↦ f (a + h) - f a - ‖f'‖ • rotation (Circle.exp (arg f')) h) =o[𝓝 0]
      fun h ↦ h := by
  simpa only [← mul_eq_smul_rotation] using hasDerivAt_iff_sub_mul_isLittleO.mp hf

/-- When `f'(a) ≠ 0`, the local rotation and scaling keeps angles: `f` is conformal at `a`. -/
theorem conformalAt_of_hasDerivAt {f : ℂ → ℂ} {f' a : ℂ} (hf : HasDerivAt f f' a)
    (hf' : f' ≠ 0) : ConformalAt f a :=
  hf.differentiableAt.conformalAt (hf.deriv ▸ hf')

/-! ### 5. The worked example `f(z) = e^{iz}` -/

/-- **[13:30-13:45]** `f(z) = e^{iz}` has `f'(z) = i e^{iz}`: "since `z` is multiplied by `i`,
an extra factor of `i` appears". -/
theorem hasDerivAt_exp_I_mul (z : ℂ) :
    HasDerivAt (fun z ↦ exp (I * z)) (I * exp (I * z)) z := by
  simpa [mul_comm] using ((hasDerivAt_id z).const_mul I).cexp

/-- **[15:00]** The point `z₀ = -π/4 - i ln 2`. -/
noncomputable def z₀ : ℂ := -(Real.pi / 4 : ℝ) - Real.log 2 * I

/-- **[15:15]** `f(z₀) = e^{i z₀} = 2 e^{-iπ/4}`. -/
theorem exp_I_mul_z₀ : exp (I * z₀) = 2 * exp ((-(Real.pi / 4) : ℝ) * I) := by
  have : I * z₀ = Real.log 2 + (-(Real.pi / 4) : ℝ) * I := by
    simp only [z₀]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [this, Complex.exp_add, ← ofReal_exp, Real.exp_log two_pos]
  push_cast
  ring

/-- **[15:15]** `f'(z₀) = i e^{i z₀} = 2 e^{iπ/4}`. -/
theorem deriv_z₀ : I * exp (I * z₀) = 2 * exp ((Real.pi / 4 : ℝ) * I) := by
  have hI : I = exp ((Real.pi / 2 : ℝ) * I) := by
    rw [exp_mul_I_eq, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  rw [exp_I_mul_z₀, mul_left_comm]
  congr 1
  nth_rewrite 1 [hI]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem hasDerivAt_z₀ :
    HasDerivAt (fun z ↦ exp (I * z)) (2 * exp ((Real.pi / 4 : ℝ) * I)) z₀ :=
  deriv_z₀ ▸ hasDerivAt_exp_I_mul z₀

private theorem pi_div_four_mem : Real.pi / 4 ∈ Set.Ioc (-Real.pi) Real.pi :=
  ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- **[16:00]** `|f'(z₀)| = 2`: "scaling by a factor of 2". -/
theorem norm_deriv_z₀ : ‖(2 : ℂ) * exp ((Real.pi / 4 : ℝ) * I)‖ = 2 := by
  simpa using (norm_arg_polar two_pos pi_div_four_mem).1

/-- **[16:00]** `arg f'(z₀) = π/4`: "rotating by `π/4` radians, or 45 degrees". -/
theorem arg_deriv_z₀ : arg ((2 : ℂ) * exp ((Real.pi / 4 : ℝ) * I)) = Real.pi / 4 := by
  simpa using (norm_arg_polar two_pos pi_div_four_mem).2

/-- **[16:00-16:15]** Near `z₀`, `e^{iz}` scales small changes by 2 and rotates them by
`π/4`, and the distortion vanishes as we zoom in: the error is `o(h)`. -/
theorem exp_I_mul_local_scale_rotate :
    (fun h ↦ exp (I * (z₀ + h)) - exp (I * z₀)
        - (2 : ℝ) • rotation (Circle.exp (Real.pi / 4)) h) =o[𝓝 0] fun h ↦ h := by
  have h := sub_rotation_isLittleO_of_hasDerivAt hasDerivAt_z₀
  rwa [norm_deriv_z₀, arg_deriv_z₀] at h

end ComplexDerivative
