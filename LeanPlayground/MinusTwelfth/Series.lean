module

public import Mathlib.Analysis.SpecificLimits.Normed

public section

/-!
# Ordinary sums, divergence, and why `1 + 2 + 3 + ⋯ ≠ -1/12`

Formalization of the elementary series claims in PBS Space Time,
*"Why Does -1/12 Keep Appearing Everywhere In Physics?"* (YouTube, 2026-10-08,
<https://www.youtube.com/watch?v=w6229Ivy_Lo>).

This file is pure mathematics: no physical modelling assumption is used anywhere. It only
pins down what an ordinary infinite sum is, and why the viral "proof" of
`1 + 2 + 3 + ⋯ = -1/12` cannot be an ordinary (or any linear, shift-stable) summation.

## Claims

1. [1:07-1:13] `1/2 + 1/4 + 1/8 + ⋯ = 1` — `MinusTwelfth.hasSum_half_pow_succ`.
2. [1:20-1:32] `1 + 2 + 3 + ⋯` diverges — `MinusTwelfth.not_summable_natCast`,
   `MinusTwelfth.tendsto_sum_range_natCast_atTop`; Lean's junk value
   `∑' n, (n : ℝ) = 0 ≠ -1/12` — `MinusTwelfth.tsum_natCast_eq_zero`,
   `MinusTwelfth.tsum_natCast_ne_neg_one_div_twelve`.
3. [1:37-1:53, 3:06-3:14] the viral manipulations are invalid: no linear, shift-stable
   summation method can assign a value to `1, 2, 3, …` —
   `MinusTwelfth.no_stable_additive_sum_nat_succ`,
   `MinusTwelfth.no_stable_linear_sum_nat_succ`; the final algebra step of the viral
   argument — `MinusTwelfth.viral_algebra`.
4. Context: the Cesàro mean of `1 - 1 + 1 - ⋯` tends to `1/2` —
   `MinusTwelfth.tendsto_cesaro_grandi`; the Abel sum of `1 - 2 + 3 - 4 + ⋯` is `1/4` —
   `MinusTwelfth.tsum_alternating_succ_mul_pow`, `MinusTwelfth.tendsto_abel_alternating_succ`
   (and the Abel sum of Grandi's series is `1/2` — `MinusTwelfth.tendsto_abel_grandi`).
-/

open Filter Topology Finset

namespace MinusTwelfth

/-- Video [1:07-1:13]: "1/2 + 1/4 + 1/8 + ... = 1". An honest convergent geometric series:
`∑_{n ≥ 0} (1/2)^(n+1) = 1`. -/
theorem hasSum_half_pow_succ : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1 := by
  have h := hasSum_geometric_two.mul_left (1 / 2 : ℝ)
  norm_num at h
  convert h using 1
  funext n
  rw [pow_succ]
  ring

/-- Video [1:20-1:32]: "1 + 2 + 3 + ... just grows without bound" — the series of natural
numbers is not summable in `ℝ`. -/
theorem not_summable_natCast : ¬ Summable (fun n : ℕ => (n : ℝ)) := by
  intro h
  have h0 := h.tendsto_atTop_zero
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_natCast_atTop_atTop 0 h0

/-- Video [1:20-1:32]: the partial sums `0 + 1 + ⋯ + (n-1)` of `1 + 2 + 3 + ⋯` tend to
`+∞`. -/
theorem tendsto_sum_range_natCast_atTop :
    Tendsto (fun n : ℕ => ∑ k ∈ range n, (k : ℝ)) atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n => Nat.cast_nonneg n).1 not_summable_natCast

/-- Video [1:20-1:32], Lean convention: `∑'` returns the *junk value* `0` for a series that is
not summable. So `∑' n, (n : ℝ)` is `0`; this is a convention, not a sum. -/
theorem tsum_natCast_eq_zero : ∑' n : ℕ, (n : ℝ) = 0 :=
  tsum_eq_zero_of_not_summable not_summable_natCast

/-- Video [1:20-1:32]: no ordinary sum gives `-1/12`: even Lean's junk value for
`∑' n, (n : ℝ)` is `0`, not `-1/12`. -/
theorem tsum_natCast_ne_neg_one_div_twelve : ∑' n : ℕ, (n : ℝ) ≠ -1 / 12 := by
  rw [tsum_natCast_eq_zero]
  norm_num

/-- Video [1:37-1:53, 3:06-3:14]: the viral "proof" of `1 + 2 + 3 + ⋯ = -1/12` shifts and
subtracts series term by term; the video says these manipulations are not valid.

Precise impossibility. A "summation method" is modelled as an additive map `L` on an
additive group `V` of sequences (the sequences it can sum) that is *stable*:
`L a = a 0 + L (n ↦ a (n + 1))` (dropping the first term subtracts it). If `V` contains
`1, 2, 3, …` (`n ↦ n + 1`) and is closed under the shift, then no such `L` exists.

Proof idea: shifting `n ↦ n + 1` gives `n ↦ n + 2 = (n ↦ n + 1) + 1`, so the constant
sequence `1` lies in `V`; stability on it reads `L 1 = 1 + L 1`, i.e. `0 = 1`. -/
theorem no_stable_additive_sum_nat_succ (V : AddSubgroup (ℕ → ℝ))
    (ha : (fun n : ℕ => (n : ℝ) + 1) ∈ V)
    (hshift : ∀ f ∈ V, (fun n => f (n + 1)) ∈ V)
    (L : V →+ ℝ)
    (hL : ∀ f (hf : f ∈ V), L ⟨f, hf⟩ = f 0 + L ⟨fun n => f (n + 1), hshift f hf⟩) :
    False := by
  have h1 : (fun _ : ℕ => (1 : ℝ)) ∈ V := by
    have := V.sub_mem (hshift _ ha) ha
    convert this using 1
    funext n
    simp only [Pi.sub_apply]
    push_cast
    ring
  have key : L ⟨_, h1⟩ = 1 + L ⟨_, h1⟩ := hL _ h1
  linarith

/-- Video [1:37-1:53, 3:06-3:14]: the same impossibility for an `ℝ`-linear summation method
on a subspace `V` of sequences: no linear, shift-stable `L` can assign a value to
`1 + 2 + 3 + ⋯`. In particular no such method gives `-1/12`; the `-1/12` of the video comes
from zeta regularization, which is *not* stable under shifting. -/
theorem no_stable_linear_sum_nat_succ (V : Submodule ℝ (ℕ → ℝ))
    (ha : (fun n : ℕ => (n : ℝ) + 1) ∈ V)
    (hshift : ∀ f ∈ V, (fun n => f (n + 1)) ∈ V)
    (L : V →ₗ[ℝ] ℝ)
    (hL : ∀ f (hf : f ∈ V), L ⟨f, hf⟩ = f 0 + L ⟨fun n => f (n + 1), hshift f hf⟩) :
    False :=
  no_stable_additive_sum_nat_succ V.toAddSubgroup ha hshift L.toAddMonoidHom hL

/-- Video [1:37-1:53]: the last algebra step of the viral argument: writing
`S = 1 + 2 + 3 + ⋯`, it claims `S - 4 S = 1 - 2 + 3 - 4 + ⋯ = 1/4`, hence `S = -1/12`.
The algebra is fine; what is invalid (see `no_stable_linear_sum_nat_succ`) is treating the
divergent `S` as a number that obeys these rules. -/
theorem viral_algebra (S : ℝ) (h : S - 4 * S = 1 / 4) : S = -1 / 12 := by
  linarith

/-- Partial sums of Grandi's series: `∑_{k ≤ m} (-1)^k = (1 + (-1)^m) / 2`, i.e. `1, 0, 1, 0, …`.
-/
theorem sum_range_succ_neg_one_pow (m : ℕ) :
    ∑ k ∈ range (m + 1), (-1 : ℝ) ^ k = (1 + (-1) ^ m) / 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ, ih, pow_succ]
    ring

/-- Context for the viral argument (Grandi's series `1 - 1 + 1 - 1 + ⋯`): the Cesàro means
(averages of the first `n` partial sums `1, 0, 1, 0, …`) tend to `1/2`. -/
theorem tendsto_cesaro_grandi :
    Tendsto (fun n : ℕ => (∑ m ∈ range n, ∑ k ∈ range (m + 1), (-1 : ℝ) ^ k) / n)
      atTop (𝓝 (1 / 2)) := by
  have hT : ∀ n : ℕ, ∑ m ∈ range n, ∑ k ∈ range (m + 1), (-1 : ℝ) ^ k
      = n / 2 + (1 - (-1) ^ n) / 4 := by
    intro n
    simp only [sum_range_succ_neg_one_pow]
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [sum_range_succ, ih, pow_succ]
      push_cast
      ring
  have hg : Tendsto (fun n : ℕ => ((1 - (-1 : ℝ) ^ n) / 4) / n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ))
    rw [norm_div, Real.norm_natCast]
    gcongr
    rw [Real.norm_eq_abs, abs_div]
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> norm_num
  have hlim := hg.const_add (1 / 2 : ℝ)
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [hT]
  field_simp

/-- Abel closed form: for `|x| < 1`, `∑ (-1)^n (n+1) x^n = 1 / (1 + x)^2`. -/
theorem tsum_alternating_succ_mul_pow {x : ℝ} (hx : |x| < 1) :
    ∑' n : ℕ, (-1 : ℝ) ^ n * (n + 1) * x ^ n = 1 / (1 + x) ^ 2 := by
  have hr : ‖-x‖ < 1 := by rwa [norm_neg, Real.norm_eq_abs]
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hr).add
    (hasSum_geometric_of_norm_lt_one hr)
  have hx1 : 1 + x ≠ 0 := by
    have := (abs_lt.1 hx).1
    linarith
  have e : (fun n : ℕ => (-1 : ℝ) ^ n * (n + 1) * x ^ n)
      = fun n : ℕ => (n : ℝ) * (-x) ^ n + (-x) ^ n := by
    funext n
    rw [neg_pow]
    ring
  rw [e, h.tsum_eq, sub_neg_eq_add]
  field_simp
  ring

/-- Context for the viral argument: the Abel sum of `1 - 2 + 3 - 4 + ⋯` is `1/4`, i.e.
`∑ (-1)^n (n+1) x^n → 1/4` as `x → 1⁻`. -/
theorem tendsto_abel_alternating_succ :
    Tendsto (fun x : ℝ => ∑' n : ℕ, (-1 : ℝ) ^ n * (n + 1) * x ^ n) (𝓝[<] 1) (𝓝 (1 / 4)) := by
  have hc : Tendsto (fun x : ℝ => 1 / (1 + x) ^ 2) (𝓝[<] 1) (𝓝 (1 / 4)) := by
    have : ContinuousAt (fun x : ℝ => 1 / (1 + x) ^ 2) 1 := by
      fun_prop (disch := norm_num)
    have h := this.tendsto
    norm_num at h
    exact tendsto_nhdsWithin_of_tendsto_nhds (by norm_num; exact h)
  refine hc.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
  rw [tsum_alternating_succ_mul_pow]
  rw [abs_lt]
  constructor <;> linarith [hx.1, hx.2]

/-- Context for the viral argument: the Abel sum of Grandi's series `1 - 1 + 1 - ⋯` is
`1/2`, matching its Cesàro value. -/
theorem tendsto_abel_grandi :
    Tendsto (fun x : ℝ => ∑' n : ℕ, (-1 : ℝ) ^ n * x ^ n) (𝓝[<] 1) (𝓝 (1 / 2)) := by
  have hc : Tendsto (fun x : ℝ => 1 / (1 + x)) (𝓝[<] 1) (𝓝 (1 / 2)) := by
    have : ContinuousAt (fun x : ℝ => 1 / (1 + x)) 1 := by
      fun_prop (disch := norm_num)
    have h := this.tendsto
    norm_num at h
    exact tendsto_nhdsWithin_of_tendsto_nhds (by norm_num; exact h)
  refine hc.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
  have hr : ‖-x‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have e : (fun n : ℕ => (-1 : ℝ) ^ n * x ^ n) = fun n : ℕ => (-x) ^ n := by
    funext n
    exact (neg_pow x n).symm
  rw [e, tsum_geometric_of_norm_lt_one hr, sub_neg_eq_add, one_div]

end MinusTwelfth
