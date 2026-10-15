module

public import LeanPlayground.Productegral.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

public section

/-!
# Multiplicative calculus: the multiplying slope and the multiplicative FTC

Claims from Sohil Rathi, *The Missing Calculus Operation* (YouTube, https://youtu.be/QN680Is4euw).

1. **[6:32-6:51]** An exponential is multiplied by the same amount every step. For `f x = 2 ^ x`:
   `f (x + 1) / f x = 2` (`two_rpow_step`), its multiplying slope is always two
   (`mulDeriv_two_rpow`), while its ordinary slope keeps growing (`strictMono_deriv_two_rpow`).
   A line, by contrast, has constant ordinary slope (`deriv_line`).
2. **[6:51-7:04]** The multiplicative fundamental theorem: the productegral of the multiplying
   slope is `f b / f a` (`productegral_mulDeriv`), the analogue of the additive
   `∫_a^b f' = f b - f a` (`additive_ftc`, which is
   `intervalIntegral.integral_eq_sub_of_hasDerivAt`).
3. Sanity checks: the productegral of a constant `c > 0` is `c ^ (b - a)`
   (`productegral_const`), and the productegral is multiplicative over adjacent intervals
   (`productegral_mul_adjacent`).

All three claims hold as stated (under the natural positivity / differentiability hypotheses).

-/

open Real intervalIntegral MeasureTheory

namespace Productegral

/-- **[6:32-6:51]** "An exponential is multiplied by the same amount every step":
for `f x = 2 ^ x`, `f (x + 1) / f x = 2` for every real `x`. -/
theorem two_rpow_step (x : ℝ) : (2 : ℝ) ^ (x + 1) / (2 : ℝ) ^ x = 2 := by
  have h : (0 : ℝ) < 2 ^ x := Real.rpow_pos_of_pos (by norm_num) x
  rw [Real.rpow_add_one (by norm_num) x]
  field_simp

/-- The ordinary derivative of `2 ^ x` is `2 ^ x * log 2`. -/
theorem deriv_two_rpow : deriv (fun x : ℝ => (2 : ℝ) ^ x) = fun x => (2 : ℝ) ^ x * log 2 := by
  funext x
  exact (Real.hasStrictDerivAt_const_rpow (by norm_num : (0 : ℝ) < 2) x).hasDerivAt.deriv

/-- **[6:32-6:51]** "The multiplying slope is always two": `mulDeriv (2 ^ ·) x = 2` for all `x`. -/
theorem mulDeriv_two_rpow (x : ℝ) : mulDeriv (fun x : ℝ => (2 : ℝ) ^ x) x = 2 := by
  have h : (2 : ℝ) ^ x ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) x).ne'
  unfold mulDeriv
  rw [deriv_two_rpow]
  simp only
  rw [mul_div_cancel_left₀ _ h, Real.exp_log (by norm_num)]

/-- **[6:32-6:51]** In contrast, the ordinary (additive) slope of `2 ^ x` is not constant:
it is strictly increasing. -/
theorem strictMono_deriv_two_rpow : StrictMono (deriv fun x : ℝ => (2 : ℝ) ^ x) := by
  rw [deriv_two_rpow]
  intro x y hxy
  have hlog : 0 < log 2 := Real.log_pos (by norm_num)
  exact mul_lt_mul_of_pos_right (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hxy) hlog

/-- **[6:32-6:51]** "A line has a constant slope": `deriv (fun x => m * x + c) x = m`. -/
theorem deriv_line (m c x : ℝ) : deriv (fun x => m * x + c) x = m := by
  have : HasDerivAt (fun x => m * x + c) m x := by
    simpa using ((hasDerivAt_id x).const_mul m).add_const c
  exact this.deriv

/-- **[6:51-7:04]** The additive fundamental theorem for comparison:
`∫_a^b f' = f b - f a` (this is `intervalIntegral.integral_eq_sub_of_hasDerivAt`). -/
theorem additive_ftc {f f' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a :=
  integral_eq_sub_of_hasDerivAt hderiv hint

/-- **[6:51-7:04]** The multiplicative fundamental theorem: "the productegral of the multiplying
slope gives the final value divided by the initial value",
`∏_a^b (f*)(x)^dx = f b / f a`, for `f` positive and differentiable on `[a, b]` with continuous
derivative there. -/
theorem productegral_mulDeriv {f : ℝ → ℝ} {a b : ℝ}
    (hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ f x)
    (hpos : ∀ x ∈ Set.uIcc a b, 0 < f x)
    (hcont : ContinuousOn (deriv f) (Set.uIcc a b)) :
    productegral (mulDeriv f) a b = f b / f a := by
  unfold productegral mulDeriv
  simp_rw [Real.log_exp]
  have hfc : ContinuousOn f (Set.uIcc a b) := fun x hx =>
    (hdiff x hx).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y => log (f y)) (deriv f x / f x) x := fun x hx =>
    (hdiff x hx).hasDerivAt.log (hpos x hx).ne'
  have hint : IntervalIntegrable (fun x => deriv f x / f x) volume a b :=
    (hcont.div hfc fun x hx => (hpos x hx).ne').intervalIntegrable
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, Real.exp_sub,
    Real.exp_log (hpos b Set.right_mem_uIcc), Real.exp_log (hpos a Set.left_mem_uIcc)]

/-- Sanity check: the productegral of a constant `c > 0` on `[a, b]` is `c ^ (b - a)`
(a constant multiplying slope `c` applied for `b - a` units of time). -/
theorem productegral_const {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    productegral (fun _ => c) a b = c ^ (b - a) := by
  unfold productegral
  rw [intervalIntegral.integral_const, smul_eq_mul, Real.rpow_def_of_pos hc, mul_comm]

/-- Sanity check: the productegral is multiplicative over adjacent intervals,
`∏_a^b · ∏_b^c = ∏_a^c` (given that `log ∘ f` is interval integrable on both pieces). -/
theorem productegral_mul_adjacent {f : ℝ → ℝ} {a b c : ℝ}
    (hab : IntervalIntegrable (fun x => log (f x)) volume a b)
    (hbc : IntervalIntegrable (fun x => log (f x)) volume b c) :
    productegral f a b * productegral f b c = productegral f a c := by
  unfold productegral
  rw [← Real.exp_add, integral_add_adjacent_intervals hab hbc]

end Productegral
