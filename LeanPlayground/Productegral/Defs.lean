module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The productegral

Definitions for the claims in Sohil Rathi, *The Missing Calculus Operation* (YouTube, 2026-10-12,
https://youtu.be/QN680Is4euw).

The video multiplies `f x ^ dx` over thin bars instead of adding `f x * dx`.
-/

@[expose] public section

open Real

namespace Productegral

/-- The product of `N` right-endpoint bars on `[a, b]`: each bar contributes
`height ^ width`. The video's bar pictures use `a = 0`, `b = 5`, `N = 5 * n`. -/
noncomputable def riemannProduct (f : ℝ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  ∏ k ∈ Finset.range N, f (a + (k + 1) * (b - a) / N) ^ ((b - a) / N)

/-- The matching right-endpoint Riemann sum: each bar contributes `height * width`. -/
noncomputable def riemannSum (f : ℝ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, f (a + (k + 1) * (b - a) / N) * ((b - a) / N)

/-- The productegral `∏_a^b f(x)^dx`, defined through the log scale as `exp (∫_a^b log f)`. -/
noncomputable def productegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  exp (∫ x in a..b, log (f x))

/-- The multiplying slope (multiplicative derivative) `f* = exp (f' / f)`. -/
noncomputable def mulDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  exp (deriv f x / f x)

end Productegral
