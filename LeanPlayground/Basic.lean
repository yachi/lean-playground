module

public import Mathlib

public section

/-! Smoke test: confirms that Mathlib loads from the cache. -/

example : (2 : ℝ) + 2 = 4 := by norm_num

theorem sum_sq_nonneg (a b : ℝ) : 0 ≤ a ^ 2 + b ^ 2 := by positivity

theorem infinitely_many_primes (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n
