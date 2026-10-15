module

public import LeanPlayground.Productegral.Defs

public section

/-!
# Limits of the shrinking bar products, and where `n! ≈ (n/e)^n` comes from

Claims from Sohil Rathi, *The Missing Calculus Operation* (YouTube, https://youtu.be/QN680Is4euw).
Bars sit under `y = x` on `[0, 5]` with right endpoints; `N = 5 * n` bars of width `1 / n`.

1. **[5:43-6:01]** The shrinking products converge to the productegral `(5/e)^5`:
   `tendsto_riemannProduct_id_five_mul` (along `N = 5n`, as in the video) and
   `tendsto_riemannProduct_id` (along all `N`). Closed forms used:
   `riemannProduct_id_eq` (`P(N) = (5 · (N!)^(1/N) / N)^5`) and
   `riemannProduct_id_five_mul_eq` (`P(5n) = ((5n)!)^(1/n) / n^5`).
2. **[6:08-6:17]** "The smooth version of 5! is (5/e)^5": `productegral_id_zero_five`
   (`∏_0^5 x^dx = (5/e)^5`) and `factorial_five_eq_riemannProduct` (`5! = P(5)`).
3. **[6:17-6:29]** "This is where the famous approximation n! ≈ (n/e)^n comes from".
   True only in the `n`-th-root sense, i.e. up to a subexponential factor:
   `tendsto_factorial_root_div` (`(n!)^(1/n) / (n/e) → 1`) and
   `pow_div_exp_le_factorial` (`(n/e)^n ≤ n!` for all `n`). The naive ratio reading fails:
   `tendsto_factorial_div_pow_atTop` (`n! / (n/e)^n → ∞`; by Stirling it grows like `√(2πn)`).

-/

open Real Filter Topology
open scoped Nat

namespace Productegral

/-- Closed form behind [5:43-6:01]: `N` right-endpoint bars under `y = x` on `[0, 5]` have
heights `5k/N` and width `5/N`, so their product is `(5 · (N!)^(1/N) / N)^5`. -/
theorem riemannProduct_id_eq (N : ℕ) (hN : N ≠ 0) :
    riemannProduct id 0 5 N = (5 * ((N ! : ℝ) ^ (1 / (N : ℝ))) / N) ^ 5 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by positivity
  have hfac : ∏ k ∈ Finset.range N, ((k : ℝ) + 1) = N ! := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial N
  have h1 : riemannProduct id 0 5 N
      = ∏ k ∈ Finset.range N, (((k : ℝ) + 1) * (5 / N)) ^ ((5 : ℝ) / N) := by
    simp only [riemannProduct, id, zero_add, sub_zero, mul_div_assoc]
  rw [h1, Real.finsetProd_rpow _ _ (fun i _ => by positivity), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_range, hfac,
    Real.mul_rpow (by positivity) (by positivity)]
  have h2 : (((5 : ℝ) / N) ^ N) ^ ((5 : ℝ) / N) = (5 / N) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [show (N : ℝ) * (5 / N) = ((5 : ℕ) : ℝ) by field_simp; norm_num, Real.rpow_natCast]
  have h3 : ((N ! : ℝ)) ^ ((5 : ℝ) / N) = ((N ! : ℝ) ^ (1 / (N : ℝ))) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  rw [h2, h3]; ring

/-- [5:43-6:01] The video's `5n` bars of width `1/n` (heights `1/n, 2/n, …, 5`) multiply to
`((5n)!)^(1/n) / n^5`. -/
theorem riemannProduct_id_five_mul_eq (n : ℕ) (hn : n ≠ 0) :
    riemannProduct id 0 5 (5 * n) = (((5 * n) ! : ℕ) : ℝ) ^ (1 / (n : ℝ)) / (n : ℝ) ^ 5 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hr : ((((5 * n) ! : ℕ) : ℝ) ^ (1 / ((5 * n : ℕ) : ℝ))) ^ 5
      = (((5 * n) ! : ℕ) : ℝ) ^ (1 / (n : ℝ)) := by
    rw [← Real.rpow_natCast _ 5, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; field_simp
  rw [riemannProduct_id_eq _ (by omega), div_pow, mul_pow, hr]
  push_cast
  field_simp

/-- Auxiliary: `(log (stirlingSeq n) + ½ log (2n)) / n → 0`, which is
`log ((n!)^(1/n) / (n/e))` for `n ≥ 1`. -/
theorem log_div_tendsto :
    Tendsto (fun n : ℕ => (log (Stirling.stirlingSeq n) + 1 / 2 * log (2 * n)) / n)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => log (Stirling.stirlingSeq n) / n) atTop (𝓝 0) :=
    ((Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity))).div_atTop
      tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => log (2 * n) / n) atTop (𝓝 0) := by
    have := (tendsto_pow_log_div_mul_add_atTop (1 / 2) 0 1 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2))
    refine this.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp, pow_one]
    congr 1; ring
  have := h1.add (h2.const_mul (1 / 2))
  simp only [add_zero, mul_zero] at this
  refine this.congr' (Eventually.of_forall fun n => ?_)
  ring

/-- [6:17-6:29] "This is where the famous approximation n! ≈ (n/e)^n comes from."
The precise true statement: `(n!)^(1/n) / (n/e) → 1`. The video's "≈" holds in this `n`-th-root
sense (equivalently `n! = (n/e)^n · e^{o(n)}`), not as a ratio of `n!` to `(n/e)^n`; see
`tendsto_factorial_div_pow_atTop`. -/
theorem tendsto_factorial_root_div :
    Tendsto (fun n : ℕ => (n ! : ℝ) ^ (1 / (n : ℝ)) / (n / exp 1)) atTop (𝓝 1) := by
  have h := (Real.continuous_exp.tendsto 0).comp log_div_tendsto
  rw [Real.exp_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hpos : 0 < (n ! : ℝ) ^ (1 / (n : ℝ)) / (n / exp 1) := by positivity
  simp only [Function.comp]
  rw [← Real.exp_log hpos]
  congr 1
  rw [Real.log_div (by positivity) (by positivity), Real.log_rpow (by positivity),
    Stirling.log_stirlingSeq_formula]
  field_simp
  ring

/-- [5:43-6:01] "The shrinking products converge to the productegral", along every bar count
`N`: `riemannProduct id 0 5 N → (5/e)^5`. -/
theorem tendsto_riemannProduct_id :
    Tendsto (fun N => riemannProduct id 0 5 N) atTop (𝓝 ((5 / exp 1) ^ 5)) := by
  have h : Tendsto (fun N : ℕ => (5 * ((N ! : ℝ) ^ (1 / (N : ℝ))) / N) ^ 5) atTop
      (𝓝 ((5 / exp 1) ^ 5)) := by
    have := (tendsto_factorial_root_div.const_mul (5 / exp 1)).pow 5
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    congr 1
    field_simp
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (riemannProduct_id_eq n hn).symm

/-- [5:43-6:01] "The shrinking products converge to the productegral": with the video's `5n`
bars of width `1/n`, `riemannProduct id 0 5 (5n) → (5/e)^5`. -/
theorem tendsto_riemannProduct_id_five_mul :
    Tendsto (fun n => riemannProduct id 0 5 (5 * n)) atTop (𝓝 ((5 / exp 1) ^ 5)) :=
  tendsto_riemannProduct_id.comp
    (tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (by norm_num)) tendsto_id)

/-- [6:08-6:17] "The smooth version of 5! is (5/e)^5": `∏_0^5 x^dx = exp (∫_0^5 log x) = (5/e)^5`
(using `∫_0^5 log x dx = 5 log 5 - 5`). -/
theorem productegral_id_zero_five : productegral id 0 5 = (5 / exp 1) ^ 5 := by
  simp only [productegral, id, integral_log]
  rw [show (5 : ℝ) * log 5 - 0 * log 0 - 5 + 0 = (5 : ℕ) * log 5 - (5 : ℕ) * 1 by push_cast; ring,
    Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num), div_pow]

/-- [6:08-6:17] The non-smooth side: `5!` is the product of the five width-1 bars,
`5! = riemannProduct id 0 5 5`. -/
theorem factorial_five_eq_riemannProduct : ((5 ! : ℕ) : ℝ) = riemannProduct id 0 5 5 := by
  simp only [riemannProduct, Finset.prod_range_succ, Finset.prod_range_zero, id]
  norm_num [Nat.factorial]

/-- [6:17-6:29] "n! ≈ (n/e)^n": the one-sided bound `(n/e)^n ≤ n!` holds for all `n`
(from Mathlib's Stirling lower bound `√(2πn) (n/e)^n ≤ n!`). -/
theorem pow_div_exp_le_factorial (n : ℕ) : (n / exp 1) ^ n ≤ n ! := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : (1 : ℝ) ≤ √(2 * π * n) := by
    rw [Real.one_le_sqrt]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  calc (n / exp 1) ^ n = 1 * (n / exp 1) ^ n := (one_mul _).symm
    _ ≤ √(2 * π * n) * (n / exp 1) ^ n := by gcongr
    _ ≤ n ! := Stirling.le_factorial_stirling n

/-- [6:17-6:29] "n! ≈ (n/e)^n": the literal ratio reading is FALSE. `n! / (n/e)^n → ∞`, since
it is at least `√(2πn)` (Stirling: the ratio is asymptotic to `√(2πn)`). So "about" is true only
up to a `√(2πn)` factor, i.e. in the `n`-th-root sense of `tendsto_factorial_root_div`. -/
theorem tendsto_factorial_div_pow_atTop :
    Tendsto (fun n : ℕ => (n ! : ℝ) / (n / exp 1) ^ n) atTop atTop := by
  have h : Tendsto (fun n : ℕ => √(2 * π * n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity))
  refine tendsto_atTop_mono' _ ?_ h
  filter_upwards [eventually_ne_atTop 0] with n hn
  have : (0 : ℝ) < (n / exp 1) ^ n := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  rw [le_div_iff₀ this]
  exact Stirling.le_factorial_stirling n

end Productegral
