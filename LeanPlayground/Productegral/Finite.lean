module

public import LeanPlayground.Productegral.Defs

public section

/-!
# Finite bar computations from *The Missing Calculus Operation*

Sohil Rathi, *The Missing Calculus Operation* (YouTube, https://youtu.be/QN680Is4euw).
All bars sit under `y = x` on `[0, 5]` with right endpoints, so `N = 5 * n` bars of width `1 / n`
have heights `1/n, 2/n, …, 5`.

* [0:42-0:48] Width-1 bars (heights 1..5) sum to 15: `riemannSum_id_five`.
* [1:07-1:12] Multiplying those heights gives 120 = 5!: `riemannProduct_id_five`.
* [1:18-1:21] Half-width heights multiplied plainly give "3,543"; the exact value is
  `10! / 2^10 = 3543.75` (the video truncates): `plainProduct_halfWidth`,
  `plainProduct_halfWidth_ne_3543`.
* [1:56-2:03] Half-width with `height ^ width`: "about 59.5". Exactly `√(10!/2^10)`, and
  `59.5 < · < 59.6`: `riemannProduct_id_ten`, `riemannProduct_id_ten_bounds`.
* [2:03-2:09] Third-width (cube roots): "exactly 45". FALSE as stated: `15!/3^15 ≈ 91134.07`
  is not `45^3 = 91125`. Proved instead: `P(15) = (15!/3^15)^(1/3)`, `45 < P(15) < 45.01`, and
  `P(15) ≠ 45`: `riemannProduct_id_fifteen`, `riemannProduct_id_fifteen_bounds`,
  `riemannProduct_id_fifteen_ne_45`.
* [2:09-2:15] "It keeps getting smaller" over widths 1, 1/2, 1/3, 1/4, 1/10:
  `riemannProduct_id_chain`. The general closed form `P(5n)^n = (5n)!/n^(5n)` is
  `riemannProduct_id_pow`. Strict decrease for *all* `n` is in `Productegral/Decrease.lean`.
* [3:24-3:34] `4 ^ 0.01` is "about 1.014": `four_rpow_hundredth_bounds`.
* [3:34-3:41] "Our new zero is one": `two_mul_half`, `rpow_mul_rpow_neg`.
-/

open Real Finset

namespace Productegral

/-- [0:42-0:48] "Width-1 bars under `y = x` on `[0,5]` … add up to 15." -/
theorem riemannSum_id_five : riemannSum id 0 5 5 = 15 := by
  unfold riemannSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, id]
  norm_num

/-- [1:07-1:12] "Multiply those heights … 120", i.e. `5!`, using the `height ^ width` rule
(width 1, so each factor is just the height). -/
theorem riemannProduct_id_five : riemannProduct id 0 5 5 = 120 := by
  unfold riemannProduct
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, id]
  norm_num

/-- [1:18-1:21] Half-width bars: multiplying the ten heights `0.5, 1, …, 5` plainly gives
"3,543". The exact value is `10! / 2^10 = 3543.75`; the video truncates the decimals. -/
theorem plainProduct_halfWidth :
    ∏ k ∈ range 10, ((k + 1 : ℝ) * 5 / 10) = (Nat.factorial 10 : ℝ) / 2 ^ 10 ∧
    ∏ k ∈ range 10, ((k + 1 : ℝ) * 5 / 10) = 3543.75 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- [1:18-1:21] The literal on-screen value "3,543" is not exact (it is `3543.75` truncated). -/
theorem plainProduct_halfWidth_ne_3543 : ∏ k ∈ range 10, ((k + 1 : ℝ) * 5 / 10) ≠ 3543 := by
  rw [plainProduct_halfWidth.2]; norm_num

/-- `riemannProduct id 0 5 N` is nonnegative. -/
theorem riemannProduct_id_nonneg (N : ℕ) : 0 ≤ riemannProduct id 0 5 N := by
  unfold riemannProduct
  refine Finset.prod_nonneg fun k _ => Real.rpow_nonneg ?_ _
  simp only [id]; positivity

/-- Closed form behind the [2:09-2:15] pictures: with `5n` bars of width `1/n`,
`(riemannProduct id 0 5 (5n)) ^ n = (5n)! / n ^ (5n)`. -/
theorem riemannProduct_id_pow (n : ℕ) (hn : 0 < n) :
    riemannProduct id 0 5 (5 * n) ^ n = ((5 * n).factorial : ℝ) / (n : ℝ) ^ (5 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hP : riemannProduct id 0 5 (5 * n) =
      ∏ k ∈ range (5 * n), ((k + 1 : ℝ) / n) ^ ((1 : ℝ) / n) := by
    unfold riemannProduct
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [id]
    congr 1 <;> push_cast <;> field_simp <;> ring
  rw [hP, Real.finsetProd_rpow _ _ (fun k _ => by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (Finset.prod_nonneg fun k _ => by positivity)]
  rw [one_div_mul_cancel hn'.ne', Real.rpow_one, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_range, Nat.factorial_eq_prod_range_add_one]
  push_cast; rfl

/-- [1:56-2:03] Half-width bars with `height ^ width` (square roots): exactly `√(10!/2^10)`. -/
theorem riemannProduct_id_ten :
    riemannProduct id 0 5 10 = √((Nat.factorial 10 : ℝ) / 2 ^ 10) := by
  have h := riemannProduct_id_pow 2 (by norm_num)
  norm_num at h
  rw [← Real.sqrt_sq (riemannProduct_id_nonneg 10), h]
  norm_num [Nat.factorial]

/-- [1:56-2:03] "about 59.5": `59.5 < riemannProduct id 0 5 10 < 59.6` (it is `≈ 59.53`). -/
theorem riemannProduct_id_ten_bounds :
    59.5 < riemannProduct id 0 5 10 ∧ riemannProduct id 0 5 10 < 59.6 := by
  rw [riemannProduct_id_ten]
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num [Nat.factorial]
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num [Nat.factorial]

/-- [2:03-2:09] Third-width bars (cube roots): the video says "exactly 45". This is only
approximately true: `P(15)^3 = 15!/3^15 = 1307674368000/14348907 ≈ 91134.07`, while
`45^3 = 91125`. The exact value is the cube root of `15!/3^15`. -/
theorem riemannProduct_id_fifteen :
    riemannProduct id 0 5 15 = ((Nat.factorial 15 : ℝ) / 3 ^ 15) ^ ((1 : ℝ) / 3) := by
  have h := riemannProduct_id_pow 3 (by norm_num)
  norm_num at h
  rw [show (Nat.factorial 15 : ℝ) / 3 ^ 15 = 1793792000 / 19683 by norm_num [Nat.factorial],
    ← h, one_div, ← Nat.cast_ofNat (R := ℝ) (n := 3),
    Real.pow_rpow_inv_natCast (riemannProduct_id_nonneg 15) (by norm_num)]

/-- [2:03-2:09] Corrected numeric form of "exactly 45": `45 < P(15) < 45.01` (`≈ 45.0015`). -/
theorem riemannProduct_id_fifteen_bounds :
    45 < riemannProduct id 0 5 15 ∧ riemannProduct id 0 5 15 < 45.01 := by
  have h := riemannProduct_id_pow 3 (by norm_num)
  norm_num [Nat.factorial] at h
  have h0 := riemannProduct_id_nonneg 15
  constructor
  · rw [← pow_lt_pow_iff_left₀ (by norm_num) h0 (by norm_num : (3 : ℕ) ≠ 0), h]; norm_num
  · rw [← pow_lt_pow_iff_left₀ h0 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0), h]; norm_num

/-- [2:03-2:09] The literal claim "exactly 45" fails: `riemannProduct id 0 5 15 ≠ 45`. -/
theorem riemannProduct_id_fifteen_ne_45 : riemannProduct id 0 5 15 ≠ 45 :=
  riemannProduct_id_fifteen_bounds.1.ne'

/-- Comparison principle: `P(5m) < P(5n)` follows from `Q_m ^ n < Q_n ^ m`, where
`Q_n = (5n)!/n^(5n) = P(5n)^n`. -/
theorem riemannProduct_id_lt_of {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : (((5 * m).factorial : ℝ) / (m : ℝ) ^ (5 * m)) ^ n <
      (((5 * n).factorial : ℝ) / (n : ℝ) ^ (5 * n)) ^ m) :
    riemannProduct id 0 5 (5 * m) < riemannProduct id 0 5 (5 * n) := by
  rw [← pow_lt_pow_iff_left₀ (riemannProduct_id_nonneg _) (riemannProduct_id_nonneg _)
    (Nat.mul_ne_zero hm.ne' hn.ne' : m * n ≠ 0)]
  rw [pow_mul, mul_comm m n, pow_mul (riemannProduct id 0 5 (5 * n)),
    riemannProduct_id_pow m hm, riemannProduct_id_pow n hn]
  exact h

/-- [2:09-2:15] "It keeps getting smaller": for widths 1, 1/2, 1/3, 1/4, 1/10 the bar products
strictly decrease (≈ 120 > 59.53 > 45.00 > 38.57 > 28.07). -/
theorem riemannProduct_id_chain :
    riemannProduct id 0 5 5 > riemannProduct id 0 5 10 ∧
    riemannProduct id 0 5 10 > riemannProduct id 0 5 15 ∧
    riemannProduct id 0 5 15 > riemannProduct id 0 5 20 ∧
    riemannProduct id 0 5 20 > riemannProduct id 0 5 50 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact riemannProduct_id_lt_of (m := 2) (n := 1) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial])
  · exact riemannProduct_id_lt_of (m := 3) (n := 2) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial])
  · exact riemannProduct_id_lt_of (m := 4) (n := 3) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial])
  · exact riemannProduct_id_lt_of (m := 10) (n := 4) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial])

/-- [3:24-3:34] A bar of height 4 and width 0.01 stretches by `4 ^ 0.01`, "about 1.014":
`1.0138 < 4 ^ 0.01 < 1.0140` (it is `≈ 1.01396`). -/
theorem four_rpow_hundredth_bounds :
    (1.0138 : ℝ) < (4 : ℝ) ^ (0.01 : ℝ) ∧ (4 : ℝ) ^ (0.01 : ℝ) < 1.0140 := by
  have hy : ((4 : ℝ) ^ (0.01 : ℝ)) ^ (100 : ℕ) = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h0 : (0 : ℝ) ≤ (4 : ℝ) ^ (0.01 : ℝ) := Real.rpow_nonneg (by norm_num) _
  constructor
  · rw [← pow_lt_pow_iff_left₀ (by norm_num) h0 (by norm_num : (100 : ℕ) ≠ 0), hy]; norm_num
  · rw [← pow_lt_pow_iff_left₀ h0 (by norm_num) (by norm_num : (100 : ℕ) ≠ 0), hy]; norm_num

/-- [3:34-3:41] "Our new zero is one": stretching by 2 then by 1/2 returns to the start. -/
theorem two_mul_half : (2 : ℝ) * (1 / 2) = 1 := by norm_num

/-- [3:34-3:41] "Our new zero is one": a bar `h ^ w` undone by `h ^ (-w)` gives the
multiplicative identity `1`, for any height `h > 0`. -/
theorem rpow_mul_rpow_neg {h : ℝ} (hh : 0 < h) (w : ℝ) : h ^ w * h ^ (-w) = 1 := by
  rw [Real.rpow_neg hh.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hh w).ne']

end Productegral
