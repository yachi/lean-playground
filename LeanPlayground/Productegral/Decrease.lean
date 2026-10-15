module

public import LeanPlayground.Productegral.Limits

public section

/-!
# The bar products strictly decrease

Claim from Sohil Rathi, *The Missing Calculus Operation* (YouTube, https://youtu.be/QN680Is4euw),
**[2:09-2:15]**: as the bars under `y = x` on `[0, 5]` get thinner (width `1, 1/2, 1/3, 1/4,
1/10, …`) the product "keeps getting smaller".

* `factorial_root_div_strictAntiOn`: `a N = (N!)^(1/N) / N` is strictly decreasing on `N ≥ 1`.
* `strictAntiOn_riemannProduct_id`: the bar product `P(N) = (5 · a N)^5` strictly decreases over
  every bar count `N ≥ 1` (not only multiples of `5`).
* `riemannProduct_id_five_mul_strictAnti`: the video's form, `5n` bars of width `1/n`.

Proof of the key step `a (N+1) < a N`: raising both sides to the power `N (N+1)` and using
`(N+1)! = (N+1) · N!`, it is equivalent to `N^N < N! · (1 + 1/N)^(N^2)`. Stirling gives
`N! ≥ √(2πN) (N/e)^N`, and `log (1 + x) > 2x / (x + 2)` gives `N^2 log (1 + 1/N) > N - 1/2`;
these combine since `e < 2πN`.
-/

open Real Filter
open scoped Nat

namespace Productegral

/-- `N^2 · log (1 + 1/N) > N - 1/2` for `N ≥ 1`, from `log (1 + x) > 2x / (x + 2)`. -/
theorem sub_half_lt_sq_mul_log_one_add_inv (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) - 1 / 2 < (N : ℝ) ^ 2 * log (1 + 1 / N) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := lt_log_one_add_of_pos (x := 1 / (N : ℝ)) (by positivity)
  have he : 2 * (1 / (N : ℝ)) / (1 / N + 2) = 2 / (1 + 2 * N) := by
    field_simp
  rw [he, div_lt_iff₀ (by positivity)] at h
  nlinarith [mul_lt_mul_of_pos_left h (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)]

/-- The key inequality `N^N < N! · (1 + 1/N)^(N^2)` for `N ≥ 1`, in the cleared form
`N^N · N^(N^2) < N! · (N + 1)^(N^2)`. -/
theorem pow_mul_pow_lt_factorial_mul (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ N * (N : ℝ) ^ (N ^ 2) < N ! * ((N : ℝ) + 1) ^ (N ^ 2) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by positivity
  set Q := (1 + 1 / (N : ℝ)) ^ (N ^ 2) with hQ
  -- `(1 + 1/N)^(N^2) > exp (N - 1/2)`
  have h1 : exp (N : ℝ) < Q * exp (1 / 2) := by
    have : exp ((N : ℝ) - 1 / 2) < Q := by
      rw [hQ, ← Real.exp_log (by positivity : (0 : ℝ) < (1 + 1 / (N : ℝ)) ^ (N ^ 2)),
        Real.log_pow]
      push_cast
      exact Real.exp_lt_exp.mpr (sub_half_lt_sq_mul_log_one_add_inv N hN)
    rw [Real.exp_sub, div_lt_iff₀ (by positivity)] at this
    exact this
  -- Stirling: `N! · e^N ≥ √(2πN) · N^N ≥ e^(1/2) · N^N`
  have h2 : exp (1 / 2) * (N : ℝ) ^ N ≤ N ! * exp (N : ℝ) := by
    have hS := Stirling.le_factorial_stirling N
    rw [div_pow, ← Real.exp_nat_mul, mul_one, mul_div_assoc', div_le_iff₀ (by positivity)] at hS
    have h3 : exp (1 / 2) ≤ √(2 * π * N) := by
      rw [Real.le_sqrt (by positivity) (by positivity), ← Real.exp_nat_mul]
      have := Real.exp_one_lt_d9
      have := Real.pi_gt_three
      norm_num
      nlinarith
    calc exp (1 / 2) * (N : ℝ) ^ N ≤ √(2 * π * N) * (N : ℝ) ^ N := by gcongr
      _ ≤ _ := hS
  have hQ' : Q = ((N : ℝ) + 1) ^ (N ^ 2) / (N : ℝ) ^ (N ^ 2) := by
    rw [hQ, ← div_pow]
    congr 1
    field_simp
  -- `N^N < N! · Q`
  have h4 : (N : ℝ) ^ N < N ! * Q := by
    have hE : 0 < exp (1 / 2) * exp (N : ℝ) := by positivity
    refine lt_of_mul_lt_mul_right ?_ hE.le
    calc (N : ℝ) ^ N * (exp (1 / 2) * exp (N : ℝ))
        < (N : ℝ) ^ N * (exp (1 / 2) * (Q * exp (1 / 2))) := by gcongr
      _ = (exp (1 / 2) * (N : ℝ) ^ N) * (Q * exp (1 / 2)) := by ring
      _ ≤ (N ! * exp (N : ℝ)) * (Q * exp (1 / 2)) := by gcongr
      _ = N ! * Q * (exp (1 / 2) * exp (N : ℝ)) := by ring
  rw [hQ', mul_div_assoc', lt_div_iff₀ (by positivity)] at h4
  exact h4

/-- `((N!)^(1/N))^N = N!` for `N ≠ 0`. -/
theorem factorial_root_pow (N : ℕ) (hN : N ≠ 0) :
    ((N ! : ℝ) ^ (1 / (N : ℝ))) ^ N = N ! := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div_mul_cancel hN',
    Real.rpow_one]

/-- One step of the decrease: `a (N+1) < a N` where `a N = (N!)^(1/N) / N`, for `N ≥ 1`. -/
theorem factorial_root_div_succ_lt (N : ℕ) (hN : 1 ≤ N) :
    (((N + 1) ! : ℕ) : ℝ) ^ (1 / ((N + 1 : ℕ) : ℝ)) / ((N + 1 : ℕ) : ℝ)
      < (N ! : ℝ) ^ (1 / (N : ℝ)) / N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : N * (N + 1) ≠ 0 := by positivity
  have hA : ((((N + 1) ! : ℕ) : ℝ) ^ (1 / ((N + 1 : ℕ) : ℝ))) ^ (N * (N + 1))
      = (((N + 1) ! : ℕ) : ℝ) ^ N := by
    rw [mul_comm, pow_mul, factorial_root_pow _ (by omega)]
  have hB : ((N ! : ℝ) ^ (1 / (N : ℝ))) ^ (N * (N + 1)) = (N ! : ℝ) ^ (N + 1) := by
    rw [pow_mul, factorial_root_pow _ (by omega)]
  rw [← pow_lt_pow_iff_left₀ (by positivity) (by positivity) hk, div_pow, div_pow, hA, hB,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have key := pow_mul_pow_lt_factorial_mul N hN
  push_cast [Nat.factorial_succ]
  calc (((N : ℝ) + 1) * N !) ^ N * (N : ℝ) ^ (N * (N + 1))
      = (((N : ℝ) + 1) ^ N * (N ! : ℝ) ^ N) * ((N : ℝ) ^ N * (N : ℝ) ^ (N ^ 2)) := by
        rw [mul_pow]; ring
    _ < (((N : ℝ) + 1) ^ N * (N ! : ℝ) ^ N) * (N ! * ((N : ℝ) + 1) ^ (N ^ 2)) := by gcongr
    _ = (N ! : ℝ) ^ (N + 1) * ((N : ℝ) + 1) ^ (N * (N + 1)) := by ring

/-- The key lemma: `a N = (N!)^(1/N) / N` is strictly decreasing on `N ≥ 1`. -/
theorem factorial_root_div_strictAntiOn :
    StrictAntiOn (fun N : ℕ => (N ! : ℝ) ^ (1 / (N : ℝ)) / N) (Set.Ici 1) := by
  refine strictAntiOn_Ici_of_lt_pred fun m hm => ?_
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Order.pred_eq_sub_one, Nat.add_sub_cancel]
  exact factorial_root_div_succ_lt k (by omega)

/-- [2:09-2:15] "As the bars get thinner the product keeps getting smaller": the product of `N`
right-endpoint bars under `y = x` on `[0, 5]` strictly decreases over all bar counts `N ≥ 1`. -/
theorem strictAntiOn_riemannProduct_id :
    StrictAntiOn (fun N : ℕ => riemannProduct id 0 5 N) (Set.Ici 1) := by
  intro m hm n hn hmn
  have h := factorial_root_div_strictAntiOn hm hn hmn
  simp only [Set.mem_Ici] at hm hn h
  simp only
  rw [riemannProduct_id_eq m (by omega), riemannProduct_id_eq n (by omega), mul_div_assoc,
    mul_div_assoc]
  gcongr

/-- [2:09-2:15] The video's form: with `5n` bars of width `1/n` (`n = 1, 2, 3, 4, 10, …`),
thinner bars (`n < m`) give a strictly smaller product. -/
theorem riemannProduct_id_five_mul_strictAnti :
    ∀ n m : ℕ, 1 ≤ n → n < m →
      riemannProduct id 0 5 (5 * m) < riemannProduct id 0 5 (5 * n) := fun n m hn hnm =>
  strictAntiOn_riemannProduct_id (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr (by omega))
    (by omega)

end Productegral
