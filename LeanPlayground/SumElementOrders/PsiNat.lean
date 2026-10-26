import Mathlib

/-!
# The sum of element orders of a cyclic group

For `n : ℕ` let `ψ(n) = ψ(Cₙ) = ∑_{d ∣ n} d φ(d)`, the sum of the orders of the elements of the
cyclic group of order `n`. This file collects its arithmetic: multiplicativity, the prime power
formula `(p + 1) ψ(pᵉ) = p^{2e+1} + 1`, Lemma 1 of Pálfy–Simonyi (arXiv:2610.27846), and the
estimate `(1)` of that paper, `∏_{p ∣ n} (p + 1) · ψ(n) > n² ∏_{p ∣ n} p`.
-/

namespace SumElementOrders

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-- `ψ(n)`, the sum of the element orders of the cyclic group of order `n`. -/
def psiNat (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d * d.totient

/-- `d ↦ d φ(d)` as an arithmetic function. -/
private def idTotient : ArithmeticFunction ℕ := ⟨fun d => d * d.totient, by simp⟩

private theorem isMultiplicative_idTotient : idTotient.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨by simp [idTotient], fun {m n} _ _ h => ?_⟩
  simp only [idTotient, coe_mk, Nat.totient_mul h]
  ring

private theorem psiNat_eq (n : ℕ) : psiNat n = (idTotient * (ζ : ArithmeticFunction ℕ)) n := by
  rw [← natCoe_nat ζ, coe_mul_zeta_apply]; rfl

theorem psiNat_mul {m n : ℕ} (h : m.Coprime n) : psiNat (m * n) = psiNat m * psiNat n := by
  simp only [psiNat_eq]
  exact (isMultiplicative_idTotient.mul isMultiplicative_zeta).map_mul_of_coprime h

@[simp] theorem psiNat_one : psiNat 1 = 1 := by simp [psiNat]

/-- `(p + 1) ψ(pᵉ) = p^{2e+1} + 1`. -/
theorem succ_mul_psiNat_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p + 1) * psiNat (p ^ e) = p ^ (2 * e + 1) + 1 := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h : psiNat (p ^ (e + 1)) = psiNat (p ^ e) + p ^ (e + 1) * (p ^ e * (p - 1)) := by
      simp only [psiNat, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ (n := e + 1)]
      rw [Nat.totient_prime_pow_succ hp]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    rw [h, mul_add, ih]
    simp only [Nat.add_sub_cancel]
    ring

theorem psiNat_prime {p : ℕ} (hp : p.Prime) : psiNat p = p ^ 2 - p + 1 := by
  have h := succ_mul_psiNat_prime_pow hp 1
  rw [pow_one] at h
  have h1 := hp.one_lt
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have : (q + 2 + 1) * psiNat (q + 2) = (q + 2 + 1) * ((q + 2) ^ 2 - (q + 2) + 1) := by
    rw [h]
    have : (q + 2) ^ 2 - (q + 2) = (q + 2) * (q + 1) := by
      rw [sq, ← Nat.mul_sub_one]; rfl
    rw [this]; ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

theorem psiNat_pos {n : ℕ} (hn : n ≠ 0) : 0 < psiNat n :=
  Finset.sum_pos (fun d hd => Nat.mul_pos (Nat.pos_of_mem_divisors hd)
    (Nat.totient_pos.2 (Nat.pos_of_mem_divisors hd))) ⟨1, by simp [hn]⟩

theorem psiNat_prime_pow_pos {p : ℕ} (hp : p.Prime) (e : ℕ) : 0 < psiNat (p ^ e) :=
  psiNat_pos (pow_ne_zero _ hp.ne_zero)

/-- **Lemma 1** (first identity), in the form `p² ψ(p^{k-1}) = ψ(pᵏ) + (p - 1)`. -/
theorem sq_mul_psiNat_pow_pred {p : ℕ} (hp : p.Prime) (k : ℕ) :
    p ^ 2 * psiNat (p ^ k) = psiNat (p ^ (k + 1)) + (p - 1) := by
  have h1 := succ_mul_psiNat_prime_pow hp k
  have h2 := succ_mul_psiNat_prime_pow hp (k + 1)
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  simp only [Nat.add_sub_cancel]
  refine Nat.eq_of_mul_eq_mul_left (Nat.succ_pos (q + 1)) ?_
  calc (q + 1 + 1) * ((q + 1) ^ 2 * psiNat ((q + 1) ^ k))
      = (q + 1) ^ 2 * ((q + 1 + 1) * psiNat ((q + 1) ^ k)) := by ring
    _ = _ := by rw [h1, Nat.succ_eq_add_one, Nat.mul_add (q + 1 + 1), h2]; ring

/-- **Lemma 1** of Pálfy–Simonyi: for a prime power `pᵏ > 1`,
`ψ(p^{k-1}) / ψ(pᵏ) = 1/p² + (p-1)/p² · 1/ψ(pᵏ)`. -/
theorem lemma1_one {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    (psiNat (p ^ (k - 1)) : ℚ) / psiNat (p ^ k) =
      1 / p ^ 2 + (p - 1) / p ^ 2 * (1 / psiNat (p ^ k)) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := sq_mul_psiNat_pow_pred hp k
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hpos : (0 : ℚ) < psiNat (p ^ (k + 1)) := by exact_mod_cast psiNat_prime_pow_pos hp _
  have hp0 : (p : ℚ) ≠ 0 := by positivity
  have hq : ((p ^ 2 * psiNat (p ^ k) : ℕ) : ℚ) = ((psiNat (p ^ (k + 1)) + (p - 1) : ℕ) : ℚ) := by
    rw [h]
  push_cast [Nat.cast_sub hp.one_lt.le] at hq
  simp only [Nat.add_sub_cancel]
  field_simp
  linear_combination hq

/-- **Lemma 1** (second identity), in the form `p⁴ ψ(p^{k-2}) = ψ(pᵏ) + (p² + 1)(p - 1)`. -/
theorem pow_four_mul_psiNat {p : ℕ} (hp : p.Prime) (k : ℕ) :
    p ^ 4 * psiNat (p ^ k) = psiNat (p ^ (k + 2)) + (p ^ 2 + 1) * (p - 1) := by
  have h1 := sq_mul_psiNat_pow_pred hp k
  have h2 := sq_mul_psiNat_pow_pred hp (k + 1)
  calc p ^ 4 * psiNat (p ^ k) = p ^ 2 * (p ^ 2 * psiNat (p ^ k)) := by ring
    _ = p ^ 2 * psiNat (p ^ (k + 1)) + p ^ 2 * (p - 1) := by rw [h1, mul_add]
    _ = _ := by rw [h2]; ring

/-- **Lemma 1** of Pálfy–Simonyi (second identity): for `k ≥ 2`,
`ψ(p^{k-2}) / ψ(pᵏ) = 1/p⁴ + (p²+1)(p-1)/p⁴ · 1/ψ(pᵏ)`. -/
theorem lemma1_two {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 2 ≤ k) :
    (psiNat (p ^ (k - 2)) : ℚ) / psiNat (p ^ k) =
      1 / p ^ 4 + (p ^ 2 + 1) * (p - 1) / p ^ 4 * (1 / psiNat (p ^ k)) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h := pow_four_mul_psiNat hp k
  have hpos : (0 : ℚ) < psiNat (p ^ (k + 2)) := by exact_mod_cast psiNat_prime_pow_pos hp _
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq : ((p ^ 4 * psiNat (p ^ k) : ℕ) : ℚ) =
      ((psiNat (p ^ (k + 2)) + (p ^ 2 + 1) * (p - 1) : ℕ) : ℚ) := by rw [h]
  push_cast [Nat.cast_sub hp.one_lt.le] at hq
  simp only [Nat.add_sub_cancel]
  field_simp
  linear_combination hq

/-- `ψ(n) = ∏_{p ∣ n} ψ(p^{v_p(n)})`. -/
theorem psiNat_eq_prod {n : ℕ} (hn : n ≠ 0) :
    psiNat n = ∏ p ∈ n.primeFactors, psiNat (p ^ n.factorization p) := by
  rw [Nat.multiplicative_factorization psiNat (fun _ _ => psiNat_mul) psiNat_one hn,
    Finsupp.prod, Nat.support_factorization]

/-- The estimate `(1)` of Pálfy–Simonyi, `ψ(n) > n² ∏_{p ∣ n} p/(p+1)`, cleared of denominators. -/
theorem sq_mul_prod_lt {n : ℕ} (hn : 2 ≤ n) :
    n ^ 2 * ∏ p ∈ n.primeFactors, p < (∏ p ∈ n.primeFactors, (p + 1)) * psiNat n := by
  have hn0 : n ≠ 0 := by omega
  have hnp : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
    rw [Finsupp.prod, Nat.support_factorization]
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
  calc n ^ 2 * ∏ p ∈ n.primeFactors, p
      = ∏ p ∈ n.primeFactors, p ^ (2 * n.factorization p + 1) := by
        calc n ^ 2 * ∏ p ∈ n.primeFactors, p
            = (∏ p ∈ n.primeFactors, p ^ n.factorization p) ^ 2 * ∏ p ∈ n.primeFactors, p := by
              rw [← hnp]
          _ = _ := by
              rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
              exact Finset.prod_congr rfl fun p _ => by ring
    _ < ∏ p ∈ n.primeFactors, (p ^ (2 * n.factorization p + 1) + 1) :=
        Finset.prod_lt_prod_of_nonempty₀
          (fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
          (fun p _ => Nat.lt_succ_self _) hne
    _ = (∏ p ∈ n.primeFactors, (p + 1)) * psiNat n := by
        rw [psiNat_eq_prod hn0, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun p hp =>
          (succ_mul_psiNat_prime_pow (Nat.prime_of_mem_primeFactors hp) _).symm

/-- For a nonempty finite set `S` of numbers `≥ a`, `a ∏_{s ∈ S} (s + 1) ≤ (max S + 1) ∏_{s ∈ S} s`
(the product `∏ (s + 1)/s` is at most the telescoping product `∏_{t=a}^{max S} (t + 1)/t`). -/
theorem mul_prod_succ_le (a : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (h : ∀ s ∈ S, a ≤ s) :
    a * ∏ s ∈ S, (s + 1) ≤ (S.max' hS + 1) * ∏ s ∈ S, s := by
  revert hS h
  induction S using Finset.induction_on_max with
  | empty => intro hS; exact absurd hS (by simp)
  | insert x S hlt ih =>
    intro hS h
    have hx : x ∉ S := fun hx => lt_irrefl x (hlt x hx)
    rw [Finset.prod_insert hx, Finset.prod_insert hx]
    rcases S.eq_empty_or_nonempty with rfl | hS'
    · simpa [mul_comm] using Nat.mul_le_mul_right (x + 1) (h x (by simp))
    · have hmax : (insert x S).max' hS = x := by
        rw [Finset.max'_insert x S hS']
        exact max_eq_left (hlt _ (S.max'_mem hS')).le
      have ih' := ih hS' (fun s hs => h s (Finset.mem_insert_of_mem hs))
      have hm : S.max' hS' + 1 ≤ x := hlt _ (S.max'_mem hS')
      rw [hmax]
      calc a * ((x + 1) * ∏ s ∈ S, (s + 1)) = (x + 1) * (a * ∏ s ∈ S, (s + 1)) := by ring
        _ ≤ (x + 1) * ((S.max' hS' + 1) * ∏ s ∈ S, s) := Nat.mul_le_mul_left _ ih'
        _ ≤ (x + 1) * (x * ∏ s ∈ S, s) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm)
        _ = (x + 1) * (x * ∏ s ∈ S, s) := rfl

/-- If `q` is the largest prime divisor of `n ≥ 2`, then `n² < q ψ(n)`. -/
theorem sq_lt_maxPrime_mul_psiNat {n : ℕ} (hn : 2 ≤ n) :
    n ^ 2 < (n.primeFactors.max' (Nat.nonempty_primeFactors.2 (by omega))) * psiNat n := by
  set S := n.primeFactors
  have hS : S.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
  set q := S.max' hS
  have h1 := sq_mul_prod_lt hn
  have h2 := mul_prod_succ_le 2 S hS fun s hs => (Nat.prime_of_mem_primeFactors hs).two_le
  have hq : 1 ≤ q := (Nat.prime_of_mem_primeFactors (S.max'_mem hS)).one_lt.le
  have hP : 0 < ∏ s ∈ S, s := Finset.prod_pos fun s hs => (Nat.prime_of_mem_primeFactors hs).pos
  have : 2 * (n ^ 2 * ∏ s ∈ S, s) < 2 * (q * psiNat n * ∏ s ∈ S, s) :=
    calc 2 * (n ^ 2 * ∏ s ∈ S, s) < 2 * ((∏ p ∈ S, (p + 1)) * psiNat n) :=
          Nat.mul_lt_mul_of_pos_left h1 (by norm_num)
      _ = (2 * ∏ p ∈ S, (p + 1)) * psiNat n := by ring
      _ ≤ ((q + 1) * ∏ s ∈ S, s) * psiNat n := Nat.mul_le_mul_right _ h2
      _ ≤ (2 * q * ∏ s ∈ S, s) * psiNat n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      _ = 2 * (q * psiNat n * ∏ s ∈ S, s) := by ring
  exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_mul_lt_mul_left this)

end SumElementOrders
