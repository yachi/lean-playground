import Mathlib

/-!
# Derivatives of `sin` and the imaginary unit

Claims from Zundamon's Theorem, *Mysterious Connection Between Derivatives and Imaginary Numbers*
(YouTube, 2026-11-17, https://youtu.be/SH7WwuVhlIs).

The video compares the cycle `sin → cos → -sin → -cos → sin` of repeated differentiation with the
cycle `1 → i → -1 → -i → 1` of repeated multiplication by `i`, and explains the match:

* multiplying by `i` rotates the complex plane by 90°: `i (x + y i) = -y + x i`;
* differentiating `sin` or `cos` shifts the phase by `π / 2`;
* the velocity of `r θ = (cos θ, sin θ)` is `r θ` rotated by 90°, so it has length one and is
  perpendicular to `r θ`;
* `d/dθ e^{iθ} = i e^{iθ}`, and the real and imaginary parts of `iⁿ e^{iθ}` are the `n`-th
  derivatives of `cos` and `sin`.

At the end the video writes `D` for `d/dθ` and observes `D² = -1` on `sin, cos`, `D² = 1` on
`sinh, cosh` (split-complex `j`, with `j ≠ ±1`) and `D² = 0` on `θ, 1` (dual `ε ≠ 0`).
We make this precise: for a pair `u, v` with `u' = v`, `v' = c u`, differentiation is a linear
endomorphism `D` of `span {u, v}` with `D² = c`, and `D` is not a scalar as soon as `u, v` are
linearly independent. Hence `X ↦ D` gives an injective `ℝ`-algebra map
`ℝ[X]/(X² - c) → End (span {u, v})`; for `sin, cos` this is `ℂ ↪ End`, `i ↦ D`.
-/

open Real

namespace DerivImaginary

/-! ### Multiplying by `i` is a quarter turn -/

/-- `i (x + y i) = -y + x i`: multiplication by `i` sends `(x, y)` to `(-y, x)`. -/
theorem I_mul_eq (x y : ℝ) : Complex.I * (x + y * Complex.I) = -y + x * Complex.I := by
  ring_nf; rw [Complex.I_sq]; ring

/-- The cycle `1 → i → -1 → -i → 1`. -/
theorem I_pow_four : Complex.I ^ 4 = 1 := Complex.I_pow_four

/-! ### Repeated derivatives of `sin` and `cos` -/

/-- `cos x = sin (x + π / 2)`: differentiating `sin` is a phase shift by 90°. -/
theorem deriv_sin_eq_phase_shift : deriv sin = fun x => sin (x + π / 2) := by
  funext x; rw [Real.deriv_sin, Real.sin_add_pi_div_two]

theorem deriv_cos_eq_phase_shift : deriv cos = fun x => cos (x + π / 2) := by
  funext x; rw [Real.deriv_cos', Real.cos_add_pi_div_two]

/-- The `n`-th derivative of `sin` is `sin` shifted by `n · π / 2`. -/
theorem iteratedDeriv_sin (n : ℕ) : iteratedDeriv n sin = fun x => sin (x + n * (π / 2)) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have : deriv (fun x => sin (x + n * (π / 2))) x = cos (x + n * (π / 2)) := by
      simp
    rw [this, ← Real.sin_add_pi_div_two]; push_cast; ring_nf

/-- The `n`-th derivative of `cos` is `cos` shifted by `n · π / 2`. -/
theorem iteratedDeriv_cos (n : ℕ) : iteratedDeriv n cos = fun x => cos (x + n * (π / 2)) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have : deriv (fun x => cos (x + n * (π / 2))) x = -sin (x + n * (π / 2)) := by
      simp
    rw [this, ← Real.cos_add_pi_div_two]; push_cast; ring_nf

/-- Differentiating `sin` twice multiplies it by `-1`. -/
theorem iteratedDeriv_two_sin : iteratedDeriv 2 sin = -sin := by
  rw [iteratedDeriv_sin]; funext x
  simp only [Pi.neg_apply]; push_cast
  rw [show x + 2 * (π / 2) = x + π by ring, Real.sin_add_pi]

theorem iteratedDeriv_two_cos : iteratedDeriv 2 cos = -cos := by
  rw [iteratedDeriv_cos]; funext x
  simp only [Pi.neg_apply]; push_cast
  rw [show x + 2 * (π / 2) = x + π by ring, Real.cos_add_pi]

/-- Four derivatives bring `sin` back to itself. -/
theorem iteratedDeriv_four_sin : iteratedDeriv 4 sin = sin := by
  rw [iteratedDeriv_sin]; funext x; push_cast
  rw [show x + 4 * (π / 2) = x + 2 * π by ring, Real.sin_add_two_pi]

theorem iteratedDeriv_four_cos : iteratedDeriv 4 cos = cos := by
  rw [iteratedDeriv_cos]; funext x; push_cast
  rw [show x + 4 * (π / 2) = x + 2 * π by ring, Real.cos_add_two_pi]

/-! ### The unit circle: velocity is position turned by 90° -/

/-- The point `(cos θ, sin θ)` of the unit circle, as a complex number. -/
noncomputable def r (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * Complex.I

/-- `r' θ = i · r θ`: the velocity is the position vector rotated by 90°. -/
theorem hasDerivAt_r (θ : ℝ) : HasDerivAt r (Complex.I * r θ) θ := by
  have hc := (Real.hasDerivAt_cos θ).ofReal_comp
  have hs := (Real.hasDerivAt_sin θ).ofReal_comp
  have := hc.add (hs.mul_const Complex.I)
  convert this using 1
  · funext y; simp [r]
  · rw [r]; push_cast; ring_nf; rw [Complex.I_sq]; ring

theorem r_eq_exp (θ : ℝ) : r θ = Complex.exp (θ * Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, r]

/-- The point moves with speed one. -/
theorem norm_deriv_r (θ : ℝ) : ‖deriv r θ‖ = 1 := by
  rw [(hasDerivAt_r θ).deriv, norm_mul, Complex.norm_I, one_mul, r_eq_exp,
    Complex.norm_exp_ofReal_mul_I]

/-- Position and velocity are perpendicular: `Re (conj r · r') = 0`. -/
theorem r_perp_deriv (θ : ℝ) : (starRingEnd ℂ (r θ) * deriv r θ).re = 0 := by
  rw [(hasDerivAt_r θ).deriv, r]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-! ### Euler's formula: differentiation brings out a factor `i` -/

/-- `d/dθ e^{iθ} = i e^{iθ}`. -/
theorem hasDerivAt_exp_mul_I (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I))
      (Complex.I * Complex.exp (θ * Complex.I)) θ := by
  have h := ((hasDerivAt_id (θ : ℂ)).mul_const Complex.I).cexp.comp_ofReal
  simpa [mul_comm] using h

theorem deriv_exp_mul_I :
    deriv (fun t : ℝ => Complex.exp (t * Complex.I)) =
      fun θ : ℝ => Complex.I * Complex.exp (θ * Complex.I) :=
  funext fun θ => (hasDerivAt_exp_mul_I θ).deriv

/-- `dⁿ/dθⁿ e^{iθ} = iⁿ e^{iθ}`. -/
theorem iteratedDeriv_exp_mul_I (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Complex.exp (t * Complex.I)) =
      fun θ : ℝ => Complex.I ^ n * Complex.exp (θ * Complex.I) := by
  induction n with
  | zero => funext θ; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    rw [deriv_const_mul _ (hasDerivAt_exp_mul_I θ).differentiableAt, deriv_exp_mul_I, pow_succ]
    ring

/-- `iⁿ e^{iθ} = e^{i (θ + n π / 2)}`: each factor `i` is a quarter turn. -/
theorem I_pow_mul_exp (n : ℕ) (θ : ℝ) :
    Complex.I ^ n * Complex.exp (θ * Complex.I) =
      Complex.exp (((θ + n * (π / 2) : ℝ) : ℂ) * Complex.I) := by
  rw [show Complex.I ^ n = Complex.exp (n * (π / 2 * Complex.I)) by
    rw [Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I], ← Complex.exp_add]
  congr 1; push_cast; ring

/-- Taking imaginary parts of `iⁿ e^{iθ}` gives the `n`-th derivative of `sin`. -/
theorem im_iteratedDeriv_exp_mul_I (n : ℕ) (θ : ℝ) :
    (Complex.I ^ n * Complex.exp (θ * Complex.I)).im = iteratedDeriv n sin θ := by
  rw [iteratedDeriv_sin, I_pow_mul_exp, Complex.exp_ofReal_mul_I_im]

/-- Taking real parts of `iⁿ e^{iθ}` gives the `n`-th derivative of `cos`. -/
theorem re_iteratedDeriv_exp_mul_I (n : ℕ) (θ : ℝ) :
    (Complex.I ^ n * Complex.exp (θ * Complex.I)).re = iteratedDeriv n cos θ := by
  rw [iteratedDeriv_cos, I_pow_mul_exp, Complex.exp_ofReal_mul_I_re]

/-! ### `D² = c` on a two-dimensional space of functions

A pair `u, v` with `u' = v` and `v' = c u`: `(sin, cos, -1)`, `(sinh, cosh, 1)`, `(θ, 1, 0)`. -/

/-- Two functions `u, v` with `u' = v` and `v' = c • u`, linearly independent. -/
structure DerivPair where
  u : ℝ → ℝ
  v : ℝ → ℝ
  c : ℝ
  hu : ∀ x, HasDerivAt u (v x) x
  hv : ∀ x, HasDerivAt v (c * u x) x
  indep : ∀ s t : ℝ, s • u + t • v = 0 → s = 0 ∧ t = 0

namespace DerivPair

variable (P : DerivPair)

/-- The space `span {u, v}` of the video's "representative functions". -/
def V : Submodule ℝ (ℝ → ℝ) := Submodule.span ℝ {P.u, P.v}

theorem exists_of_mem {f : ℝ → ℝ} (hf : f ∈ P.V) : ∃ a b : ℝ, f = a • P.u + b • P.v := by
  obtain ⟨a, b, h⟩ := Submodule.mem_span_pair.1 hf
  exact ⟨a, b, h.symm⟩

theorem hasDerivAt_comb (a b x : ℝ) :
    HasDerivAt (a • P.u + b • P.v) ((b * P.c) * P.u x + a * P.v x) x := by
  have := ((P.hu x).const_smul a).add ((P.hv x).const_smul b)
  convert this using 1
  simp only [smul_eq_mul]; ring

theorem deriv_comb (a b : ℝ) : deriv (a • P.u + b • P.v) = (b * P.c) • P.u + a • P.v := by
  funext x; simpa using (P.hasDerivAt_comb a b x).deriv

theorem u_mem : P.u ∈ P.V := Submodule.subset_span (by simp)

theorem v_mem : P.v ∈ P.V := Submodule.subset_span (by simp)

theorem comb_mem (a b : ℝ) : a • P.u + b • P.v ∈ P.V :=
  P.V.add_mem (P.V.smul_mem a P.u_mem) (P.V.smul_mem b P.v_mem)

theorem differentiable_of_mem {f : ℝ → ℝ} (hf : f ∈ P.V) : Differentiable ℝ f := by
  obtain ⟨a, b, rfl⟩ := P.exists_of_mem hf
  exact fun x => (P.hasDerivAt_comb a b x).differentiableAt

theorem deriv_mem {f : ℝ → ℝ} (hf : f ∈ P.V) : deriv f ∈ P.V := by
  obtain ⟨a, b, rfl⟩ := P.exists_of_mem hf
  rw [deriv_comb]; exact P.comb_mem _ _

/-- Differentiation `D = d/dθ` as a linear endomorphism of `span {u, v}`. -/
noncomputable def D : Module.End ℝ P.V where
  toFun f := ⟨deriv f, P.deriv_mem f.2⟩
  map_add' f g := by
    ext x
    exact deriv_add (P.differentiable_of_mem f.2 x) (P.differentiable_of_mem g.2 x)
  map_smul' a f := by
    ext x
    exact deriv_const_smul a (P.differentiable_of_mem f.2 x)

@[simp] theorem D_apply (f : P.V) : (P.D f : ℝ → ℝ) = deriv f := rfl

/-- `D² = c`. -/
theorem D_mul_D : P.D * P.D = algebraMap ℝ (Module.End ℝ P.V) P.c := by
  ext ⟨f, hf⟩ x
  obtain ⟨a, b, rfl⟩ := P.exists_of_mem hf
  simp only [Module.End.mul_apply, D_apply, deriv_comb, Module.algebraMap_end_apply,
    Submodule.coe_smul, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- `D` is not a real scalar (e.g. `j ≠ ±1`, `ε ≠ 0`). -/
theorem D_not_mem_range : P.D ∉ (algebraMap ℝ (Module.End ℝ P.V)).range := by
  rintro ⟨a, ha⟩
  have h := congrArg (fun T : Module.End ℝ P.V => (T ⟨P.u, P.u_mem⟩ : ℝ → ℝ)) ha
  simp only [Module.algebraMap_end_apply, Submodule.coe_smul, D_apply] at h
  have hd : deriv P.u = P.v := funext fun x => (P.hu x).deriv
  rw [hd] at h
  have := (P.indep a (-1) (by rw [h]; simp)).2
  norm_num at this

theorem isIntegral_D : IsIntegral ℝ P.D := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C P.c,
    Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  simp [Polynomial.eval₂_sub, sq, P.D_mul_D]

instance : Nontrivial P.V :=
  ⟨⟨⟨P.u, P.u_mem⟩, 0, fun h => by
    have := (P.indep 1 0 (by simpa using congrArg Subtype.val h)).1
    norm_num at this⟩⟩

/-- The minimal polynomial of `D` is `X² - c`. -/
theorem minpoly_D : minpoly ℝ P.D = Polynomial.X ^ 2 - Polynomial.C P.c := by
  have hm : (Polynomial.X ^ 2 - Polynomial.C P.c).Monic :=
    Polynomial.monic_X_pow_sub_C _ two_ne_zero
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C P.c).natDegree = 2 :=
    Polynomial.natDegree_X_pow_sub_C
  have hdvd : minpoly ℝ P.D ∣ Polynomial.X ^ 2 - Polynomial.C P.c :=
    minpoly.dvd _ _ (by simp [Polynomial.aeval_def, Polynomial.eval₂_sub, sq, P.D_mul_D])
  have h2 : 2 ≤ (minpoly ℝ P.D).natDegree :=
    (minpoly.two_le_natDegree_iff P.isIntegral_D).2 P.D_not_mem_range
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic P.isIntegral_D) hm hdvd
    (by omega)).symm

/-- A real polynomial kills `D` exactly when it is a multiple of `X² - c`, i.e.
`ℝ[D] ≅ ℝ[X] / (X² - c)`: complex numbers for `c = -1`, split-complex numbers for `c = 1`,
dual numbers for `c = 0`. -/
theorem aeval_D_eq_zero_iff (q : Polynomial ℝ) :
    Polynomial.aeval P.D q = 0 ↔ Polynomial.X ^ 2 - Polynomial.C P.c ∣ q := by
  rw [← P.minpoly_D, minpoly.dvd_iff]

end DerivPair

/-- `(sin, cos)`: `sin' = cos`, `cos' = -sin`. -/
noncomputable def trig : DerivPair where
  u := sin
  v := cos
  c := -1
  hu x := Real.hasDerivAt_sin x
  hv x := by simpa using Real.hasDerivAt_cos x
  indep s t h := by
    have h0 := congrFun h 0
    have h1 := congrFun h (π / 2)
    simp only [Pi.add_apply, Pi.smul_apply, sin_zero, smul_eq_mul, mul_zero, cos_zero, mul_one,
      zero_add, Pi.zero_apply, sin_pi_div_two, cos_pi_div_two, add_zero] at h0 h1
    exact ⟨h1, h0⟩

/-- `(sinh, cosh)`: `sinh' = cosh`, `cosh' = sinh`. -/
noncomputable def hyp : DerivPair where
  u := sinh
  v := cosh
  c := 1
  hu x := Real.hasDerivAt_sinh x
  hv x := by simpa using Real.hasDerivAt_cosh x
  indep s t h := by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Pi.add_apply, Pi.smul_apply, sinh_zero, smul_eq_mul, mul_zero, cosh_zero, mul_one,
      zero_add, Pi.zero_apply] at h0 h1
    subst h0
    exact ⟨(mul_eq_zero.1 (by simpa using h1)).resolve_right (Real.sinh_pos_iff.2 one_pos).ne',
      rfl⟩

/-- `(θ, 1)`: `θ' = 1`, `1' = 0`. -/
noncomputable def lin : DerivPair where
  u := id
  v := fun _ => 1
  c := 0
  hu x := by simpa using hasDerivAt_id x
  hv x := by simpa using hasDerivAt_const x (1 : ℝ)
  indep s t h := by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Pi.add_apply, Pi.smul_apply, id_eq, smul_eq_mul, mul_zero, mul_one, zero_add,
      Pi.zero_apply] at h0 h1
    subst h0
    simpa using h1

/-- On `span {sin, cos}`, `D² = -1`: the analogue of `i² = -1`. -/
theorem trig_D_sq : trig.D * trig.D = -1 := by
  rw [trig.D_mul_D, show trig.c = -1 from rfl, map_neg, map_one]

/-- On `span {sinh, cosh}`, `D² = 1` but `D ≠ ±1`: the split-complex unit `j`. -/
theorem hyp_D_sq : hyp.D * hyp.D = 1 ∧ hyp.D ≠ 1 ∧ hyp.D ≠ -1 := by
  refine ⟨by rw [hyp.D_mul_D]; exact map_one _, fun h => hyp.D_not_mem_range ⟨1, by simp [h]⟩,
    fun h => hyp.D_not_mem_range ⟨-1, by simp [h]⟩⟩

/-- On `span {θ, 1}`, `D² = 0` but `D ≠ 0`: the dual unit `ε`. -/
theorem lin_D_sq : lin.D * lin.D = 0 ∧ lin.D ≠ 0 := by
  refine ⟨by rw [lin.D_mul_D]; exact map_zero _, fun h => lin.D_not_mem_range ⟨0, by simp [h]⟩⟩

/-- `i ↦ D` is an `ℝ`-algebra embedding of `ℂ` into the endomorphisms of `span {sin, cos}`. -/
noncomputable def complexToEnd : ℂ →ₐ[ℝ] Module.End ℝ trig.V :=
  Complex.lift ⟨trig.D, trig_D_sq⟩

@[simp] theorem complexToEnd_I : complexToEnd Complex.I = trig.D := by simp [complexToEnd]

theorem complexToEnd_injective : Function.Injective complexToEnd :=
  complexToEnd.toRingHom.injective

end DerivImaginary
