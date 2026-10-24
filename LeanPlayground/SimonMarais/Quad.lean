module

public import LeanPlayground.SimonMarais.Lucas
public import LeanPlayground.SimonMarais.OddSum
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Arithmetic in `ℚ(√n)` inside `ℝ`

We write elements of `ℚ(√n)` as real numbers `u + v√n` with `u v : ℚ`. For `t = u + v√n`,
`coeffA n u v k` and `coeffB n u v k` are the rational coefficients of `t^k = A_k + B_k √n`.
-/

@[expose] public section

namespace SimonMarais

open Real Finset

/-- The coefficients `(A_k, B_k)` of `(u + v√n)^k = A_k + B_k √n`. -/
def coeffs (n : ℕ) (u v : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | k + 1 => (u * (coeffs n u v k).1 + n * v * (coeffs n u v k).2,
      v * (coeffs n u v k).1 + u * (coeffs n u v k).2)

/-- The rational part of `(u + v√n)^k`. -/
def coeffA (n : ℕ) (u v : ℚ) (k : ℕ) : ℚ := (coeffs n u v k).1

/-- The `√n` part of `(u + v√n)^k`. -/
def coeffB (n : ℕ) (u v : ℚ) (k : ℕ) : ℚ := (coeffs n u v k).2

variable {n : ℕ}

theorem coeffA_succ (u v : ℚ) (k : ℕ) :
    coeffA n u v (k + 1) = u * coeffA n u v k + n * v * coeffB n u v k := rfl
theorem coeffB_succ (u v : ℚ) (k : ℕ) :
    coeffB n u v (k + 1) = v * coeffA n u v k + u * coeffB n u v k := rfl
@[simp] theorem coeffA_zero (u v : ℚ) : coeffA n u v 0 = 1 := rfl
@[simp] theorem coeffB_zero (u v : ℚ) : coeffB n u v 0 = 0 := rfl

theorem sq_sqrt_nat (n : ℕ) : (√(n : ℝ)) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)

theorem pow_eq_coeff (u v : ℚ) (k : ℕ) :
    ((u : ℝ) + v * √(n : ℝ)) ^ k = coeffA n u v k + coeffB n u v k * √(n : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, coeffA_succ, coeffB_succ]
    push_cast
    linear_combination (coeffB n u v k * v) * sq_sqrt_nat n

theorem conj_pow_eq_coeff (u v : ℚ) (k : ℕ) :
    ((u : ℝ) - v * √(n : ℝ)) ^ k = coeffA n u v k - coeffB n u v k * √(n : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, coeffA_succ, coeffB_succ]
    push_cast
    linear_combination (coeffB n u v k * v) * sq_sqrt_nat n

/-- `B_k = v · U_k(2u, u² - nv²)`. -/
theorem coeffB_eq_lucas (u v : ℚ) (k : ℕ) :
    coeffB n u v k = v * lucas (2 * u) (u ^ 2 - n * v ^ 2) k := by
  have key : ∀ k, coeffB n u v (k + 2) =
      2 * u * coeffB n u v (k + 1) - (u ^ 2 - n * v ^ 2) * coeffB n u v k := by
    intro k
    have h1 := coeffB_succ (n := n) u v (k + 1)
    have h2 := coeffB_succ (n := n) u v k
    have h3 := coeffA_succ (n := n) u v k
    rw [h1, h3]
    linear_combination (-u) * h2
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simp [coeffB_succ]
    | k + 2 =>
      rw [key, ih k (by omega), ih (k + 1) (by omega), lucas_add_two]
      ring

/-- Irrationality of `√n` for non-square `n`. -/
theorem irrational_sqrt (hn : ¬ IsSquare n) : Irrational √(n : ℝ) :=
  irrational_sqrt_natCast_iff.mpr hn

theorem two_le_of_not_isSquare (hn : ¬ IsSquare n) : 2 ≤ n := by
  by_contra h
  interval_cases n
  · exact hn ⟨0, rfl⟩
  · exact hn ⟨1, rfl⟩

theorem one_lt_sqrt (hn : ¬ IsSquare n) : 1 < √(n : ℝ) := by
  rw [show (1 : ℝ) = √1 by simp]
  apply Real.sqrt_lt_sqrt zero_le_one
  exact_mod_cast (two_le_of_not_isSquare hn)

/-- Coefficients in `ℚ + ℚ√n` are unique. -/
theorem coeff_unique (hn : ¬ IsSquare n) {x y x' y' : ℚ}
    (h : (x : ℝ) + y * √(n : ℝ) = x' + y' * √(n : ℝ)) : x = x' ∧ y = y' := by
  have hs := irrational_sqrt hn
  by_cases hy : y = y'
  · subst hy; refine ⟨?_, rfl⟩; exact_mod_cast (add_right_cancel h)
  · exfalso
    apply hs
    refine ⟨(x - x') / (y' - y), ?_⟩
    have : ((y' : ℝ) - y) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hy))
    push_cast
    field_simp
    linarith

/-- If `x + y√n` is rational then `y = 0`. -/
theorem coeff_eq_zero_of_rat (hn : ¬ IsSquare n) {x y q : ℚ}
    (h : (x : ℝ) + y * √(n : ℝ) = q) : y = 0 :=
  (coeff_unique hn (x' := q) (y' := 0) (by simpa using h)).2

/-- `u² = n v²` forces `v = 0` when `n` is not a square. -/
theorem eq_zero_of_sq_eq (hn : ¬ IsSquare n) {u v : ℚ} (h : u ^ 2 = n * v ^ 2) : v = 0 := by
  by_contra hv
  apply irrational_sqrt hn
  refine ⟨|u / v|, ?_⟩
  have : ((u / v) ^ 2 : ℚ) = n := by field_simp; linarith
  rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs]
  congr 1
  exact_mod_cast this

/-! ### `ℚ(√n)` as a subset of `ℝ` -/

/-- `x ∈ ℚ(√n)`. -/
def InQS (n : ℕ) (x : ℝ) : Prop := ∃ u v : ℚ, x = u + v * √(n : ℝ)

theorem InQS.rat (q : ℚ) : InQS n q := ⟨q, 0, by simp⟩

theorem InQS.sqrt : InQS n √(n : ℝ) := ⟨0, 1, by simp⟩

theorem InQS.sub {x y : ℝ} : InQS n x → InQS n y → InQS n (x - y) := by
  rintro ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
  exact ⟨u - u', v - v', by push_cast; ring⟩

theorem InQS.mul {x y : ℝ} : InQS n x → InQS n y → InQS n (x * y) := by
  rintro ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
  refine ⟨u * u' + n * v * v', u * v' + v * u', ?_⟩
  push_cast
  linear_combination (v * v') * sq_sqrt_nat n

theorem InQS.pow {x : ℝ} (hx : InQS n x) (k : ℕ) : InQS n (x ^ k) := by
  induction k with
  | zero => simpa using InQS.rat (n := n) 1
  | succ k ih => rw [pow_succ]; exact ih.mul hx

theorem InQS.inv (hn : ¬ IsSquare n) {x : ℝ} (hx : InQS n x) : InQS n x⁻¹ := by
  obtain ⟨u, v, rfl⟩ := hx
  by_cases hN : u ^ 2 - n * v ^ 2 = 0
  · have hv := eq_zero_of_sq_eq hn (u := u) (v := v) (by linarith)
    have hu : u = 0 := by subst hv; simpa using hN
    subst hu hv
    simpa using InQS.rat (n := n) 0
  refine ⟨u / (u ^ 2 - n * v ^ 2), -v / (u ^ 2 - n * v ^ 2), ?_⟩
  have hN' : ((u : ℝ) ^ 2 - n * v ^ 2) ≠ 0 := by exact_mod_cast hN
  have hprod : ((u : ℝ) + v * √(n : ℝ)) * (u - v * √(n : ℝ)) = u ^ 2 - n * v ^ 2 := by
    linear_combination (-(v : ℝ) ^ 2) * sq_sqrt_nat n
  have hne : ((u : ℝ) + v * √(n : ℝ)) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hprod; exact hN' hprod.symm
  refine inv_eq_of_mul_eq_one_right ?_
  push_cast
  rw [show ((u : ℝ) + v * √(n : ℝ)) *
        (u / (u ^ 2 - n * v ^ 2) + -v / (u ^ 2 - n * v ^ 2) * √(n : ℝ))
      = ((u + v * √(n : ℝ)) * (u - v * √(n : ℝ))) / (u ^ 2 - n * v ^ 2) by ring, hprod,
    div_self hN']

theorem InQS.div (hn : ¬ IsSquare n) {x y : ℝ} (hx : InQS n x) (hy : InQS n y) :
    InQS n (x / y) := by
  rw [div_eq_mul_inv]; exact hx.mul (hy.inv hn)

/-- Lemma 7 of the paper (first part): if `α, β` are coprime with `α < β`, and `t^α + √n` and
`t^β + √n` are rational, then `t ∈ ℚ(√n)`. -/
theorem inQS_of_pow (hn : ¬ IsSquare n) {t : ℝ} {α β : ℕ} (hα : 1 ≤ α) (hαβ : α < β)
    (hcop : α.Coprime β) {xa xb : ℚ} (ha : t ^ α = xa - √(n : ℝ)) (hb : t ^ β = xb - √(n : ℝ)) :
    InQS n t := by
  have hs := irrational_sqrt hn
  have hβ : 1 < β := by omega
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hβ
  obtain ⟨l, hl⟩ : ∃ l, l = α * m / β := ⟨_, rfl⟩
  have he : α * m = β * l + 1 := by
    have := Nat.div_add_mod (α * m) β
    rw [hm, ← hl] at this; omega
  have hxb : (xb : ℝ) - √(n : ℝ) ≠ 0 := by
    intro h0; exact hs ⟨xb, by linarith⟩
  have hpow : t ^ (β * l) ≠ 0 := by
    rw [pow_mul, hb]; exact pow_ne_zero _ hxb
  have ht : t = (xa - √(n : ℝ)) ^ m / (xb - √(n : ℝ)) ^ l := by
    rw [← ha, ← hb, ← pow_mul, ← pow_mul, he, pow_succ]
    field_simp
  rw [ht]
  exact ((InQS.rat xa).sub InQS.sqrt |>.pow m).div hn (((InQS.rat xb).sub InQS.sqrt).pow l)

/-! ### The binomial form of `B_b` -/

/-- `(u + v√n)^b`, split by the parity of the binomial index. -/
theorem pow_eq_binom (u v : ℚ) (b : ℕ) :
    ((u : ℝ) + v * √(n : ℝ)) ^ b =
      ((∑ i ∈ range (b + 1), if Odd i then 0 else
          (b.choose i : ℚ) * u ^ (b - i) * v ^ i * (n : ℚ) ^ (i / 2) : ℚ) : ℝ) +
      ((∑ i ∈ range (b + 1), if Odd i then
          (b.choose i : ℚ) * u ^ (b - i) * v ^ i * (n : ℚ) ^ (i / 2) else 0 : ℚ) : ℝ) *
        √(n : ℝ) := by
  rw [add_comm (u : ℝ), add_pow]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : √(n : ℝ) ^ i = (n : ℝ) ^ (i / 2) * √(n : ℝ) ^ (i % 2) := by
    conv_lhs => rw [← Nat.div_add_mod i 2, pow_add, pow_mul, sq_sqrt_nat]
  rcases Nat.even_or_odd i with he | ho
  · have : i % 2 = 0 := Nat.even_iff.mp he
    simp only [show ¬ Odd i from Nat.not_odd_iff_even.mpr he, ↓reduceIte, mul_pow, hs, this]
    push_cast
    ring
  · have : i % 2 = 1 := Nat.odd_iff.mp ho
    simp only [ho, ↓reduceIte, mul_pow, hs, this]
    push_cast
    ring

theorem coeffB_eq_binom (hn : ¬ IsSquare n) (u v : ℚ) (b : ℕ) :
    coeffB n u v b = ∑ i ∈ range (b + 1), if Odd i then
      (b.choose i : ℚ) * u ^ (b - i) * v ^ i * (n : ℚ) ^ (i / 2) else 0 := by
  have h := (pow_eq_coeff (n := n) u v b).symm.trans (pow_eq_binom u v b)
  exact (coeff_unique hn h).2

/-- `B_b = v u^(b-1) · oddSum b (v²n/u²)` for `u ≠ 0` and `b ≥ 1`. -/
theorem coeffB_eq_oddSum (hn : ¬ IsSquare n) {u : ℚ} (hu : u ≠ 0) (v : ℚ) {b : ℕ} (hb : 1 ≤ b) :
    coeffB n u v b = v * u ^ (b - 1) * oddSum b (v ^ 2 * n / u ^ 2) := by
  rw [coeffB_eq_binom hn, oddSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  split_ifs with ho
  · obtain ⟨j, rfl⟩ := ho
    have hj : (2 * j + 1) / 2 = j := by omega
    rw [hj]
    have e : b - 1 = (b - (2 * j + 1)) + 2 * j := by omega
    rw [e, pow_add u, show v ^ (2 * j + 1) = v * (v ^ 2) ^ j by ring, div_pow, mul_pow,
      pow_mul u 2 j]
    field_simp
  · simp

end SimonMarais
