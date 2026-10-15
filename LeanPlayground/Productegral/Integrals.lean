module

public import LeanPlayground.Productegral.Defs
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

public section

/-!
# Integrals and productegrals from *The Missing Calculus Operation*

Claims from Sohil Rathi, *The Missing Calculus Operation* (YouTube, https://youtu.be/QN680Is4euw),
formalized against the shared definitions in `LeanPlayground.Productegral.Defs`.

1. [0:54-1:00] `∫_0^5 x dx = 12.5`, and the right-endpoint Riemann sums of `y = x` on `[0,5]`
   tend to `12.5` (`integral_id_zero_five`, `riemannSum_id_zero_five`,
   `tendsto_riemannSum_id_zero_five`).
2. [4:40-4:48] The log scale turns a stretch into a step: `log (h ^ w) = w * log h`
   (`log_stretch_eq_step`).
3. [5:31-5:38] `∫_0^5 log x dx = 5 log 5 - 5 ≈ 3.05` (`integral_log_zero_five`,
   `integral_log_zero_five_bounds`, `integral_log_zero_five_bounds_tight`). The exact value is
   `3.04718956...`, which rounds to `3.05` at two decimals.
4. [5:38-5:43, 6:01] The productegral of `y = x` on `[0,5]` is `(5 / e)^5 ≈ 21.06`
   (`productegral_id_zero_five`, `productegral_id_zero_five_bounds`,
   `productegral_id_zero_five_bounds_tight`). The exact value is `21.0561...`, so "21.06" is the
   correct two-decimal rounding (it is *not* 21.05).
5. [3:41-4:10, 5:13-5:23] Sweeping `y = x` from `0`: the line length `L t = (t / e)^t` falls on
   `(0,1]`, rises on `[1,∞)`, is below `1` before `e`, equal to `1` at `e`, above `1` after `e`,
   and starts at `1` as `t → 0⁺` (`productegral_id_zero_eq_rpow`, `lineLength_strictAntiOn`,
   `lineLength_strictMonoOn`, `lineLength_lt_one`, `lineLength_exp_one`,
   `integral_log_zero_exp_one`, `one_lt_lineLength`, `tendsto_lineLength_zero`).
6. [6:04-6:08] "It works for any function": the log of a Riemann product is an ordinary Riemann
   sum of `log ∘ f` (`log_riemannProduct`, `log_riemannProduct_of_pos_on_Ioc`,
   `riemannProduct_eq_exp_riemannSum`).

-/

open Real Filter Topology Set

namespace Productegral

/-! ## Claim 1: area under `y = x` on `[0, 5]` -/

/-- [0:54-1:00] "The area under y = x from 0 to 5 is 12.5." -/
theorem integral_id_zero_five : ∫ x in (0 : ℝ)..5, x = 12.5 := by
  rw [integral_id]; norm_num

/-- Helper for [0:54-1:00]: Gauss's sum `1 + 2 + ... + N = N (N + 1) / 2` over the reals. -/
theorem sum_range_succ_cast (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k : ℝ) + 1) = N * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- [0:54-1:00] Closed form of the video's bar sums for `y = x` on `[0,5]` with `N` right-endpoint
bars: the bars over-shoot the area `12.5` by exactly `12.5 / N`. -/
theorem riemannSum_id_zero_five {N : ℕ} (hN : N ≠ 0) :
    riemannSum id 0 5 N = 12.5 + 12.5 / N := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  unfold riemannSum
  have : ∀ k ∈ Finset.range N,
      id ((0 : ℝ) + (k + 1) * (5 - 0) / N) * ((5 - 0) / N) = 25 / (N : ℝ) ^ 2 * ((k : ℝ) + 1) := by
    intro k _
    simp only [id]
    field_simp
    ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_range_succ_cast]
  field_simp
  ring

/-- [0:54-1:00] "As the bars get thinner the sum approaches 12.5": the right-endpoint Riemann sums
of `y = x` on `[0,5]` tend to `12.5`. -/
theorem tendsto_riemannSum_id_zero_five :
    Tendsto (fun N : ℕ => riemannSum id 0 5 N) atTop (𝓝 12.5) := by
  have h : Tendsto (fun N : ℕ => (12.5 : ℝ) + 12.5 / N) atTop (𝓝 (12.5 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat 12.5)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  rw [riemannSum_id_zero_five hN]

/-! ## Claim 2: the log scale turns a stretch into a step -/

/-- [4:40-4:48] "On the log scale, a stretch becomes a step": `log (h ^ w) = w * log h`
for a positive height `h` and any width `w`. -/
theorem log_stretch_eq_step {h : ℝ} (hh : 0 < h) (w : ℝ) : log (h ^ w) = w * log h :=
  Real.log_rpow hh w

/-! ## Productegral of `y = x` from `0` -/

/-- [5:13-5:23] The productegral of `y = x` from `0` to any `t` is `exp (t log t - t)`
(no positivity hypothesis needed: Mathlib's `log` is `0` at `0` and even). -/
theorem productegral_id_zero (t : ℝ) : productegral id 0 t = exp (t * log t - t) := by
  unfold productegral
  simp only [id]
  rw [integral_log_from_zero]

/-! ## Claim 3: `∫_0^5 log x dx` -/

/-- [5:31-5:38] "The area under log x from 0 to 5 is 5 log 5 - 5." -/
theorem integral_log_zero_five : ∫ x in (0 : ℝ)..5, log x = 5 * log 5 - 5 := by
  rw [integral_log_from_zero]

/-- [5:31-5:38] "... which is about 3.05": `3.04 < ∫_0^5 log x dx < 3.05`. -/
theorem integral_log_zero_five_bounds :
    3.04 < ∫ x in (0 : ℝ)..5, log x ∧ ∫ x in (0 : ℝ)..5, log x < 3.05 := by
  rw [integral_log_zero_five]
  constructor <;> linarith [log_five_gt_d9, log_five_lt_d9]

/-- [5:31-5:38] Sharper: `3.047 < ∫_0^5 log x dx < 3.048`, so the value `3.0471...` rounds to
`3.05` at two decimals, matching the video's "about 3.05". -/
theorem integral_log_zero_five_bounds_tight :
    3.047 < ∫ x in (0 : ℝ)..5, log x ∧ ∫ x in (0 : ℝ)..5, log x < 3.048 := by
  rw [integral_log_zero_five]
  constructor <;> linarith [log_five_gt_d9, log_five_lt_d9]

/-! ## Claim 4: the productegral of `y = x` on `[0, 5]` -/

/-- [5:38-5:43, 6:01] "The productegral of x from 0 to 5 is (5 / e)^5." -/
theorem productegral_id_zero_five : productegral id 0 5 = (5 / exp 1) ^ 5 := by
  have h1 : exp (5 * log 5) = 5 ^ 5 := by
    rw [show (5 : ℝ) * log 5 = ((5 : ℕ) : ℝ) * log 5 by norm_num, exp_nat_mul,
      exp_log (by norm_num)]
  have h2 : exp 5 = exp 1 ^ 5 := by
    rw [← exp_nat_mul]; norm_num
  rw [productegral_id_zero, exp_sub, h1, h2, div_pow]

/-- [5:38-5:43, 6:01] "... which lands on 21.06": `21.05 < (5/e)^5 < 21.06`. -/
theorem productegral_id_zero_five_bounds :
    21.05 < productegral id 0 5 ∧ productegral id 0 5 < 21.06 := by
  have hlo : exp 1 ^ 5 < (2.7182818286 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos 1).le (by norm_num)
  have hhi : (2.7182818283 : ℝ) ^ 5 < exp 1 ^ 5 :=
    pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num)
  have hpos : 0 < exp 1 ^ 5 := by positivity
  rw [productegral_id_zero_five, div_pow]
  generalize exp 1 ^ 5 = E at *
  rw [lt_div_iff₀ hpos, div_lt_iff₀ hpos]
  norm_num at hlo hhi ⊢
  constructor <;> linarith

/-- [5:38-5:43, 6:01] Sharper: `21.056 < (5/e)^5 < 21.057`. The value `21.0561...` rounds to
`21.06` at two decimals, so the video's "21.06" is the correct rounding (not `21.05`). -/
theorem productegral_id_zero_five_bounds_tight :
    21.056 < productegral id 0 5 ∧ productegral id 0 5 < 21.057 := by
  have hlo : exp 1 ^ 5 < (2.7182818286 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos 1).le (by norm_num)
  have hhi : (2.7182818283 : ℝ) ^ 5 < exp 1 ^ 5 :=
    pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num)
  have hpos : 0 < exp 1 ^ 5 := by positivity
  rw [productegral_id_zero_five, div_pow]
  generalize exp 1 ^ 5 = E at *
  rw [lt_div_iff₀ hpos, div_lt_iff₀ hpos]
  norm_num at hlo hhi ⊢
  constructor <;> linarith

/-! ## Claim 5: sweeping the right end of `y = x` -/

/-- [5:13-5:23] The swept line length `L t = productegral id 0 t` equals `(t / e)^t` for `t > 0`. -/
theorem productegral_id_zero_eq_rpow {t : ℝ} (ht : 0 < t) :
    productegral id 0 t = (t / exp 1) ^ t := by
  rw [productegral_id_zero, rpow_def_of_pos (div_pos ht (exp_pos 1)),
    log_div ht.ne' (exp_pos 1).ne', log_exp]
  ring_nf

/-- Helper for [3:41-4:10]: the exponent `t log t - t` has derivative `log t` at `t ≠ 0`. -/
theorem hasDerivAt_mul_log_sub {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x => x * log x - x) (log t) t := by
  have := (hasDerivAt_mul_log ht).fun_sub (hasDerivAt_id' t)
  simpa using this

/-- [3:41-4:10] "At first the line shrinks": `L t = productegral id 0 t` is strictly decreasing on
`(0, 1]`. -/
theorem lineLength_strictAntiOn : StrictAntiOn (fun t => productegral id 0 t) (Ioc 0 1) := by
  simp only [productegral_id_zero]
  refine exp_strictMono.comp_strictAntiOn ?_
  refine strictAntiOn_of_deriv_neg (convex_Ioc 0 1)
    (continuous_mul_log.sub continuous_id).continuousOn fun x hx => ?_
  rw [interior_Ioc] at hx
  rw [(hasDerivAt_mul_log_sub hx.1.ne').deriv]
  exact log_neg hx.1 hx.2

/-- [3:41-4:10] "Past 1 the line grows": `L t = productegral id 0 t` is strictly increasing on
`[1, ∞)`. -/
theorem lineLength_strictMonoOn : StrictMonoOn (fun t => productegral id 0 t) (Ici 1) := by
  simp only [productegral_id_zero]
  refine exp_strictMono.comp_strictMonoOn ?_
  refine strictMonoOn_of_deriv_pos (convex_Ici 1)
    (continuous_mul_log.sub continuous_id).continuousOn fun x hx => ?_
  rw [interior_Ici] at hx
  have hx1 : (1 : ℝ) < x := hx
  rw [(hasDerivAt_mul_log_sub (by linarith)).deriv]
  exact log_pos hx1

/-- [5:13-5:23] "Before e, the line length is less than 1": `L t < 1` for `0 < t < e`. -/
theorem lineLength_lt_one {t : ℝ} (ht : 0 < t) (hte : t < exp 1) : productegral id 0 t < 1 := by
  rw [productegral_id_zero, exp_lt_one_iff]
  have : log t < 1 := (log_lt_iff_lt_exp ht).mpr hte
  nlinarith

/-- [5:13-5:23] "At e the line is back to length exactly 1": `L e = 1`. -/
theorem lineLength_exp_one : productegral id 0 (exp 1) = 1 := by
  rw [productegral_id_zero, log_exp]; simp

/-- [5:13-5:23] Equivalent form of `L e = 1`: `∫_0^e log x dx = 0` (the area below the axis on
`(0,1)` exactly cancels the area above it on `(1,e)`). -/
theorem integral_log_zero_exp_one : ∫ x in (0 : ℝ)..exp 1, log x = 0 := by
  rw [integral_log_from_zero, log_exp]; ring

/-- [5:13-5:23] "After e, the line is longer than 1": `L t > 1` for `t > e`. -/
theorem one_lt_lineLength {t : ℝ} (hte : exp 1 < t) : 1 < productegral id 0 t := by
  have ht : 0 < t := (exp_pos 1).trans hte
  rw [productegral_id_zero, one_lt_exp_iff]
  have : 1 < log t := (lt_log_iff_exp_lt ht).mpr hte
  nlinarith

/-- [3:41-4:10] "The sweep starts with a line of length 1": `L t → 1` as `t → 0⁺`. -/
theorem tendsto_lineLength_zero :
    Tendsto (fun t => productegral id 0 t) (𝓝[>] 0) (𝓝 1) := by
  simp only [productegral_id_zero]
  have hc : Continuous fun t : ℝ => exp (t * log t - t) :=
    continuous_exp.comp (continuous_mul_log.sub continuous_id)
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa using this

/-! ## Claim 6: every productegral is a Riemann sum behind a logarithm -/

/-- [6:04-6:08] "It works for any function": the log of the bar product is the ordinary Riemann
sum of `log ∘ f`, as long as every sampled height is positive. -/
theorem log_riemannProduct (f : ℝ → ℝ) (a b : ℝ) (N : ℕ)
    (hf : ∀ k ∈ Finset.range N, 0 < f (a + (k + 1) * (b - a) / N)) :
    log (riemannProduct f a b N) = riemannSum (log ∘ f) a b N := by
  unfold riemannProduct riemannSum
  rw [log_prod fun k hk => (rpow_pos_of_pos (hf k hk) _).ne']
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [log_rpow (hf k hk), Function.comp_apply, mul_comm]

/-- Helper for [6:04-6:08]: for `a < b` and `k < N`, the right endpoint
`a + (k + 1)(b - a)/N` of the `k`-th bar lies in `(a, b]`. -/
theorem sample_mem_Ioc {a b : ℝ} (hab : a < b) {N k : ℕ} (hk : k < N) :
    a + (k + 1) * (b - a) / N ∈ Ioc a b := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le k).trans_lt hk
  have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  have hba : 0 < b - a := sub_pos.mpr hab
  constructor
  · have : 0 < (k + 1) * (b - a) / N := by positivity
    linarith
  · have : (k + 1) * (b - a) / N ≤ b - a := by
      rw [div_le_iff₀ hN]; nlinarith
    linarith

/-- [6:04-6:08] "It works for any function", stated for `f` positive on `(a, b]`:
`log (riemannProduct f a b N) = riemannSum (log ∘ f) a b N`. The hypothesis `a < b` is assumed so
that the sample points lie in `(a, b]`, where the positivity hypothesis applies; for `a ≥ b` they
fall outside `(a, b]` (see `log_riemannProduct` for the pointwise version). -/
theorem log_riemannProduct_of_pos_on_Ioc (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (N : ℕ)
    (hf : ∀ x ∈ Ioc a b, 0 < f x) :
    log (riemannProduct f a b N) = riemannSum (log ∘ f) a b N :=
  log_riemannProduct f a b N fun _ hk =>
    hf _ (sample_mem_Ioc hab (Finset.mem_range.mp hk))

/-- [6:04-6:08] Equivalently, the bar product is `exp` of an ordinary Riemann sum:
`riemannProduct f a b N = exp (riemannSum (log ∘ f) a b N)` for `f` positive on `(a, b]`. -/
theorem riemannProduct_eq_exp_riemannSum (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (N : ℕ)
    (hf : ∀ x ∈ Ioc a b, 0 < f x) :
    riemannProduct f a b N = exp (riemannSum (log ∘ f) a b N) := by
  rw [← log_riemannProduct_of_pos_on_Ioc f hab N hf, exp_log]
  unfold riemannProduct
  exact Finset.prod_pos fun k hk =>
    rpow_pos_of_pos (hf _ (sample_mem_Ioc hab (Finset.mem_range.mp hk))) _

end Productegral
