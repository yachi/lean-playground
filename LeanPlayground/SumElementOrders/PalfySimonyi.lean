module

public import LeanPlayground.SumElementOrders.Basic
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# Lemmas 2 and 3 of Pálfy–Simonyi

Péter P. Pálfy and Alex D. Simonyi, *Finite groups with large sum of element orders compared to
cyclic groups* (arXiv:2610.27846). Write `ψ'(G) = ψ(G) / ψ(|G|)`.

* **Lemma 2.** For `k ≥ 2`,
  `ψ(C_{p^{k-1}} × C_p) / ψ(pᵏ) = 1/p + (p² - p + 1)(p - 1)/p · 1/ψ(pᵏ)`.
* **Lemma 3.** Let `p` be the largest prime divisor of `|G|` and `c` the smallest index of a cyclic
  subgroup. If `ψ'(G) ≥ 1/3` then `c < p`, or `(c, π(G))` is one of ten exceptional pairs.

Lemma 1 and the estimate `(1)` are in `PsiNat.lean`.
-/

namespace SumElementOrders

open Finset

/-! ### Lemma 2 -/

section Lemma2

variable {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B] [IsCyclic A] [IsCyclic B]

/-- `ψ(C_{pᵏ} × C_p) = p (ψ(pᵏ) - 1) + ψ(p)` for `k ≥ 1`: an element `(x, y)` has order `o(x)`
if `x ≠ 1` and `o(y)` if `x = 1`. -/
theorem psi_prod {p k : ℕ} (hp : p.Prime) (hA : Nat.card A = p ^ k)
    (hB : Nat.card B = p) : psi (A × B) = p * (psiNat (p ^ k) - 1) + psiNat p := by
  classical
  have hpsiA := (psi_eq_psiNat (G := A)).trans (by rw [hA])
  have hpsiB := (psi_eq_psiNat (G := B)).trans (by rw [hB])
  have hx : ∀ x : A, x ≠ 1 → ∀ y : B, orderOf (x, y) = orderOf x := by
    intro x hx1 y
    rw [Prod.orderOf_mk]
    apply Nat.lcm_eq_left
    have hy : orderOf y ∣ p := hB ▸ orderOf_dvd_natCard y
    obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow hp).1 (hA ▸ orderOf_dvd_natCard x)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.1 (by simpa using hjx))
    exact hy.trans (hjx ▸ dvd_pow_self p hj0)
  have hsplit := Fintype.sum_eq_add_sum_compl (1 : A) (fun x : A => orderOf x)
  simp only [orderOf_one] at hsplit
  rw [psi, Fintype.sum_prod_type, Fintype.sum_eq_add_sum_compl (1 : A)]
  have h1 : ∑ y : B, orderOf ((1 : A), y) = psiNat p := by
    rw [← hpsiB, psi]
    exact Finset.sum_congr rfl fun y _ => by rw [Prod.orderOf_mk, orderOf_one, Nat.lcm_one_left]
  have h2 : ∑ x ∈ {(1 : A)}ᶜ, ∑ y : B, orderOf (x, y) = p * (psiNat (p ^ k) - 1) := by
    rw [Finset.sum_congr rfl fun x hx' => Finset.sum_congr rfl fun y _ =>
      hx x (by simpa using hx') y]
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hB, smul_eq_mul]
    rw [← Finset.mul_sum, ← hpsiA, psi, hsplit, Nat.add_sub_cancel_left]
  rw [h1, h2, add_comm]

/-- **Lemma 2** of Pálfy–Simonyi: for `k ≥ 2`,
`ψ(C_{p^{k-1}} × C_p) / ψ(pᵏ) = 1/p + (p² - p + 1)(p - 1)/p · 1/ψ(pᵏ)`. -/
theorem lemma2 {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hA : Nat.card A = p ^ (k - 1))
    (hB : Nat.card B = p) :
    (psi (A × B) : ℚ) / psiNat (p ^ k) =
      1 / p + (p ^ 2 - p + 1) * (p - 1) / p * (1 / psiNat (p ^ k)) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hA
  rw [psi_prod hp hA hB, psiNat_prime hp]
  have h := sq_mul_psiNat_pow_pred hp k
  have hX : 1 ≤ psiNat (p ^ k) := psiNat_prime_pow_pos hp k
  have hpp : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  have hpos : (0 : ℚ) < psiNat (p ^ (k + 1)) := by exact_mod_cast psiNat_prime_pow_pos hp _
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq : ((p ^ 2 * psiNat (p ^ k) : ℕ) : ℚ) = ((psiNat (p ^ (k + 1)) + (p - 1) : ℕ) : ℚ) := by
    rw [h]
  push_cast [Nat.cast_sub hp.one_lt.le] at hq
  push_cast [Nat.cast_sub hX, Nat.cast_sub hpp]
  field_simp
  linear_combination hq

end Lemma2

/-! ### Lemma 3 -/

/-- The ten exceptional pairs `(c, π(G))` of Lemma 3. -/
def lemma3Exceptions : List (ℕ × Finset ℕ) :=
  [(2, {2}), (3, {3}), (3, {2, 3}), (4, {2}), (4, {2, 3}), (5, {2, 5}), (5, {2, 3, 5}),
    (6, {2, 3, 5}), (7, {2, 3, 5, 7}), (8, {2, 3, 5, 7})]

/-- The "direct calculation" of Lemma 3: over sets of primes `T ⊆ {2, 3, 5, 7}`. -/
theorem lemma3_small : ∀ T ∈ ({2, 3, 5, 7} : Finset ℕ).powerset, T.Nonempty →
    ∀ c ∈ Finset.range 9, 0 < c → (∀ p ∈ ({2, 3, 5, 7} : Finset ℕ), p ∣ c → p ∈ T) →
      c * ∏ p ∈ T, p < 3 * ∏ p ∈ T, (p + 1) →
        (∃ p ∈ T, c < p) ∨ (c, T) ∈ lemma3Exceptions := by
  decide +kernel

/-- `35 ∏_{p ∈ T} (p + 1) ≤ 96 ∏_{p ∈ T} p` for `T ⊆ {2, 3, 5, 7}`. -/
theorem prod_small_le : ∀ T ∈ ({2, 3, 5, 7} : Finset ℕ).powerset,
    35 * ∏ p ∈ T, (p + 1) ≤ 96 * ∏ p ∈ T, p := by
  decide +kernel

/-- The arithmetic part of Lemma 3: if `S` is a nonempty set of primes containing the prime
factors of `c > 0`, and `c ∏_{p ∈ S} p < 3 ∏_{p ∈ S} (p + 1)`, then `c < max S` or `(c, S)` is
exceptional. -/
theorem lemma3_arith {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) {c : ℕ}
    (hc0 : 0 < c) (hc : c.primeFactors ⊆ S) (h : c * ∏ p ∈ S, p < 3 * ∏ p ∈ S, (p + 1)) :
    c < S.max' hne ∨ (c, S) ∈ lemma3Exceptions := by
  set small := S.filter (· < 11)
  set large := S.filter (fun p => ¬ p < 11)
  have hsmall : small ∈ ({2, 3, 5, 7} : Finset ℕ).powerset := by
    rw [Finset.mem_powerset]
    intro p hp
    obtain ⟨hpS, hp11⟩ := Finset.mem_filter.1 hp
    have hpr := hS p hpS
    interval_cases p <;> first | decide | (exfalso; norm_num at hpr)
  have hprod1 : ∏ p ∈ S, p = (∏ p ∈ small, p) * ∏ p ∈ large, p :=
    (Finset.prod_filter_mul_prod_filter_not S (· < 11) fun p => p).symm
  have hprod2 : ∏ p ∈ S, (p + 1) = (∏ p ∈ small, (p + 1)) * ∏ p ∈ large, (p + 1) :=
    (Finset.prod_filter_mul_prod_filter_not S (· < 11) fun p => p + 1).symm
  rcases large.eq_empty_or_nonempty with hl | hl
  · -- `S ⊆ {2, 3, 5, 7}`
    have hSs : small = S := by
      rw [Finset.filter_eq_self]
      intro p hp
      by_contra h11
      exact Finset.notMem_empty p (hl ▸ Finset.mem_filter.2 ⟨hp, h11⟩)
    have hc9 : c < 9 := by
      have h1 := prod_small_le small hsmall
      rw [hSs] at h1
      have hP : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS p hp).pos
      have : 35 * (c * ∏ p ∈ S, p) < 35 * (3 * ∏ p ∈ S, (p + 1)) :=
        Nat.mul_lt_mul_of_pos_left h (by norm_num)
      nlinarith
    have hcT : ∀ p ∈ ({2, 3, 5, 7} : Finset ℕ), p ∣ c → p ∈ S := by
      intro p hp hpc
      apply hc
      rw [Nat.mem_primeFactors]
      refine ⟨?_, hpc, hc0.ne'⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> norm_num
    rcases lemma3_small S (hSs ▸ hsmall) hne c (Finset.mem_range.2 hc9) hc0 hcT h with
      ⟨p, hp, hcp⟩ | hex
    · exact Or.inl (hcp.trans_le (S.le_max' p hp))
    · exact Or.inr hex
  · -- the largest prime `q` is at least `11`
    left
    have hmax : S.max' hne = large.max' hl := by
      apply le_antisymm
      · by_contra hlt
        rw [not_le] at hlt
        have hmS := S.max'_mem hne
        have h11 : ¬ S.max' hne < 11 := by
          have := large.max'_mem hl
          have h11' := (Finset.mem_filter.1 this).2
          omega
        exact absurd (large.le_max' _ (Finset.mem_filter.2 ⟨hmS, h11⟩)) (not_le.2 hlt)
      · exact S.le_max' _ (Finset.mem_filter.1 (large.max'_mem hl)).1
    have h11 : ∀ p ∈ large, 11 ≤ p := fun p hp => by
      have := (Finset.mem_filter.1 hp).2
      omega
    have hL := mul_prod_succ_le 11 large hl h11
    have hSm := prod_small_le small hsmall
    rw [hmax]
    set q := large.max' hl
    have hq11 : 11 ≤ q := h11 q (large.max'_mem hl)
    have hPs : 0 < ∏ p ∈ small, p :=
      Finset.prod_pos fun p hp => (hS p (Finset.mem_filter.1 hp).1).pos
    have hPl : 0 < ∏ p ∈ large, p :=
      Finset.prod_pos fun p hp => (hS p (Finset.mem_filter.1 hp).1).pos
    rw [hprod1, hprod2] at h
    -- `385 c ∏ p < 3 · 35 · 11 ∏ (p + 1) ≤ 3 · 96 (q + 1) ∏ p`, so `385 c < 288 (q + 1) ≤ 385 q`
    have key : 385 * c * ((∏ p ∈ small, p) * ∏ p ∈ large, p) <
        288 * (q + 1) * ((∏ p ∈ small, p) * ∏ p ∈ large, p) := by
      calc 385 * c * ((∏ p ∈ small, p) * ∏ p ∈ large, p)
          = 385 * (c * ((∏ p ∈ small, p) * ∏ p ∈ large, p)) := by ring
        _ < 385 * (3 * ((∏ p ∈ small, (p + 1)) * ∏ p ∈ large, (p + 1))) :=
          Nat.mul_lt_mul_of_pos_left h (by norm_num)
        _ = 3 * ((35 * ∏ p ∈ small, (p + 1)) * (11 * ∏ p ∈ large, (p + 1))) := by ring
        _ ≤ 3 * ((96 * ∏ p ∈ small, p) * ((q + 1) * ∏ p ∈ large, p)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hSm hL)
        _ = 288 * (q + 1) * ((∏ p ∈ small, p) * ∏ p ∈ large, p) := by ring
    have := Nat.lt_of_mul_lt_mul_right key
    omega

/-- **Lemma 3** of Pálfy–Simonyi. Let `q` be the largest prime divisor of `n = |G| ≥ 2`, and let
`C` be a cyclic subgroup of smallest index `c`. If `ψ'(G) ≥ 1/3`, i.e. `ψ(n) ≤ 3 ψ(G)`, then
`c < q`, or `(c, π(G))` is one of the ten pairs in `lemma3Exceptions`. -/
theorem lemma3 {G : Type*} [Group G] [Fintype G] (hn : 2 ≤ Nat.card G) (C : Subgroup G)
    (_hC : IsCyclic C) (hmin : ∀ D : Subgroup G, IsCyclic D → C.index ≤ D.index)
    (h : psiNat (Nat.card G) ≤ 3 * psi G) :
    C.index < (Nat.card G).primeFactors.max' (Nat.nonempty_primeFactors.2 (by omega)) ∨
      (C.index, (Nat.card G).primeFactors) ∈ lemma3Exceptions := by
  set n := Nat.card G
  set c := C.index
  set S := n.primeFactors
  have hc0 : 0 < c := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  -- every element has order at most `n / c`, so `c ψ(G) ≤ n²`
  have hord : ∀ g : G, c * orderOf g ≤ n := fun g => by
    have := Subgroup.card_mul_index (Subgroup.zpowers g)
    rw [Nat.card_zpowers] at this
    calc c * orderOf g ≤ (Subgroup.zpowers g).index * orderOf g :=
          Nat.mul_le_mul_right _ (hmin _ inferInstance)
      _ = n := by rw [mul_comm]; exact this
  have hcpsi : c * psi G ≤ n ^ 2 := by
    calc c * psi G = ∑ g : G, c * orderOf g := by rw [psi, Finset.mul_sum]
      _ ≤ ∑ _g : G, n := Finset.sum_le_sum fun g _ => hord g
      _ = n ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul, sq]
  -- combine with the estimate `(1)`: `c ∏ p < 3 ∏ (p + 1)`
  have h1 := sq_mul_prod_lt hn
  have key : n ^ 2 * (c * ∏ p ∈ S, p) < n ^ 2 * (3 * ∏ p ∈ S, (p + 1)) := by
    calc n ^ 2 * (c * ∏ p ∈ S, p) = c * (n ^ 2 * ∏ p ∈ S, p) := by ring
      _ < c * ((∏ p ∈ S, (p + 1)) * psiNat n) := Nat.mul_lt_mul_of_pos_left h1 hc0
      _ ≤ c * ((∏ p ∈ S, (p + 1)) * (3 * psi G)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
      _ = 3 * (∏ p ∈ S, (p + 1)) * (c * psi G) := by ring
      _ ≤ 3 * (∏ p ∈ S, (p + 1)) * n ^ 2 := Nat.mul_le_mul_left _ hcpsi
      _ = n ^ 2 * (3 * ∏ p ∈ S, (p + 1)) := by ring
  have hcn : c ∣ n := Subgroup.index_dvd_card C
  exact lemma3_arith (fun p hp => Nat.prime_of_mem_primeFactors hp) _ hc0
    (Nat.primeFactors_mono hcn (by omega)) (Nat.lt_of_mul_lt_mul_left key)

end SumElementOrders
