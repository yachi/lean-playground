module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The odd part of a binomial expansion

`oddSum b ρ = ∑_{i odd, i ≤ b} C(b, i) ρ^((i-1)/2)`. If `t = u + v√n`, then the `√n`-coefficient
of `t^b` is `v u^(b-1) · oddSum b (v²n/u²)` (see `SimonMarais.coeffB_eq_oddSum`).

The key fact (`SimonMarais.padicValRat_oddSum`) is the valuation computation used twice in the
proof of Theorem 13 of the paper: if `ν_p(ρ) ≥ 2`, then `ν_p(oddSum b ρ) = ν_p(b)`, because the
`i = 1` term is `b` and every other term has larger valuation.
-/

@[expose] public section

namespace SimonMarais

open Finset

/-- `∑_{i odd, i ≤ b} C(b, i) ρ^((i-1)/2)`. -/
def oddSum (b : ℕ) (ρ : ℚ) : ℚ :=
  ∑ i ∈ range (b + 1), if Odd i then (b.choose i : ℚ) * ρ ^ (i / 2) else 0

theorem oddSum_ge {b : ℕ} (hb : 1 ≤ b) {ρ : ℚ} (hρ : 0 ≤ ρ) : (b : ℚ) ≤ oddSum b ρ := by
  unfold oddSum
  have h := Finset.single_le_sum (f := fun i => if Odd i then (b.choose i : ℚ) * ρ ^ (i / 2) else 0)
    (s := range (b + 1)) (fun i _ => by split_ifs <;> positivity) (a := 1) (by simp; omega)
  simpa using h

/-- A finite sum of terms that are each zero or of valuation `> e` is zero or of valuation `> e`. -/
theorem sum_eq_zero_or_lt {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (F : ι → ℚ) (e : ℤ)
    (hF : ∀ i ∈ s, F i = 0 ∨ e < padicValRat p (F i)) :
    ∑ i ∈ s, F i = 0 ∨ e < padicValRat p (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha]
    have ih := ih (fun i hi => hF i (mem_insert_of_mem hi))
    rcases hF a (mem_insert_self a s) with h0 | h0
    · rw [h0, zero_add]; exact ih
    rcases ih with ih | ih
    · rw [ih, add_zero]; exact Or.inr h0
    by_cases hsum : F a + ∑ i ∈ s, F i = 0
    · exact Or.inl hsum
    exact Or.inr (lt_of_lt_of_le (lt_min h0 ih) (padicValRat.min_le_padicValRat_add hsum))

/-- `ν_p(i) ≤ i - 2` for `i ≥ 3`. -/
theorem padicValNat_le_sub_two {p : ℕ} [hp : Fact p.Prime] {i : ℕ} (hi : 3 ≤ i) :
    padicValNat p i ≤ i - 2 := by
  by_contra! h
  have h1 : p ^ padicValNat p i ≤ i := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have h2 : 2 ^ (i - 1) ≤ p ^ padicValNat p i :=
    (Nat.pow_le_pow_left hp.out.two_le _).trans (Nat.pow_le_pow_right hp.out.pos (by omega))
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 3 := ⟨i - 3, by omega⟩
  have h3 := Nat.lt_two_pow_self (n := k)
  have : 2 ^ (k + 3 - 1) = 4 * 2 ^ k := by
    rw [show k + 3 - 1 = k + 2 by omega, pow_add]; ring
  omega

/-- `ν_p(b) ≤ ν_p(C(b, i)) + ν_p(i)`, from `i · C(b, i) = b · C(b-1, i-1)`. -/
theorem padicValNat_choose_add {p : ℕ} [Fact p.Prime] {b i : ℕ} (hi : 1 ≤ i) (hib : i ≤ b) :
    padicValNat p b ≤ padicValNat p (b.choose i) + padicValNat p i := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have e := Nat.add_one_mul_choose_eq n k
  have h1 : (n + 1).choose (k + 1) ≠ 0 := (Nat.choose_pos hib).ne'
  have h2 : n.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have := congrArg (padicValNat p) e
  rw [padicValNat.mul (by omega) h2, padicValNat.mul h1 (by omega)] at this
  omega

/-- If `ρ = 0` or `ν_p(ρ) ≥ 2`, then `ν_p(oddSum b ρ) = ν_p(b)`. -/
theorem padicValRat_oddSum {p : ℕ} [Fact p.Prime] {b : ℕ} (hb : 1 ≤ b) {ρ : ℚ}
    (hρ : ρ = 0 ∨ 2 ≤ padicValRat p ρ) : padicValRat p (oddSum b ρ) = padicValRat p b := by
  classical
  set F : ℕ → ℚ := fun i => if Odd i then (b.choose i : ℚ) * ρ ^ (i / 2) else 0
  have hsplit : oddSum b ρ = (b : ℚ) + ∑ i ∈ (range (b + 1)).erase 1, F i := by
    unfold oddSum
    rw [← add_sum_erase _ _ (show 1 ∈ range (b + 1) by simp; omega)]
    simp [F]
  have hb0 : (b : ℚ) ≠ 0 := by positivity
  have hrest := sum_eq_zero_or_lt (p := p) ((range (b + 1)).erase 1) F (padicValRat p b) ?_
  · rw [hsplit]
    rcases hrest with h | h
    · rw [h, add_zero]
    have hR : ∑ i ∈ (range (b + 1)).erase 1, F i ≠ 0 := by
      intro h0; rw [h0, padicValRat.zero] at h
      have : (0 : ℤ) ≤ padicValRat p b := by rw [← padicValRat_of_nat]; positivity
      omega
    have hne : (b : ℚ) + ∑ i ∈ (range (b + 1)).erase 1, F i ≠ 0 := by
      intro h0
      have : ∑ i ∈ (range (b + 1)).erase 1, F i = -b := by linarith
      rw [this, padicValRat.neg] at h
      omega
    exact padicValRat.add_eq_of_lt hne hb0 hR h
  · intro i hi
    simp only [mem_erase, mem_range] at hi
    simp only [F]
    split_ifs with hodd
    swap; · exact Or.inl rfl
    have hi3 : 3 ≤ i := by obtain ⟨j, rfl⟩ := hodd; omega
    rcases hρ with rfl | hρ
    · left; simp [zero_pow (show i / 2 ≠ 0 by omega)]
    right
    have hρ0 : ρ ≠ 0 := by rintro rfl; simp at hρ
    have hc : ((b.choose i : ℕ) : ℚ) ≠ 0 := by
      have := Nat.choose_pos (show i ≤ b by omega); positivity
    rw [padicValRat.mul hc (pow_ne_zero _ hρ0), padicValRat.pow, ← padicValRat_of_nat,
      ← padicValRat_of_nat]
    have h1 := padicValNat_choose_add (p := p) (b := b) (i := i) (by omega) (by omega)
    have h2 := padicValNat_le_sub_two (p := p) hi3
    have h3 : 2 * (i / 2 : ℕ) = i - 1 := by obtain ⟨j, rfl⟩ := hodd; omega
    have h4 : (2 : ℤ) * ((i / 2 : ℕ) : ℤ) ≤ ((i / 2 : ℕ) : ℤ) * padicValRat p ρ := by
      have : (0 : ℤ) ≤ ((i / 2 : ℕ) : ℤ) := by positivity
      nlinarith
    have h5 : ((2 * (i / 2) : ℕ) : ℤ) = ((i - 1 : ℕ) : ℤ) := by rw [h3]
    push_cast at h5
    have h6 : ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 := by omega
    have h7 : ((padicValNat p i : ℕ) : ℤ) ≤ (i : ℤ) - 2 := by omega
    omega

end SimonMarais
