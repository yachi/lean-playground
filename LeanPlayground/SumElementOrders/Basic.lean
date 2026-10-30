module

public import LeanPlayground.SumElementOrders.PsiNat
public import Mathlib.GroupTheory.Sylow

@[expose] public section

/-!
# The sum of element orders of a finite group

For a finite group `G` let `ψ(G) = ∑_{g ∈ G} o(g)`. We prove the theorem of Amiri, Jafarian Amiri
and Isaacs (*Sums of element orders in finite groups*, Comm. Algebra 37 (2009)): among groups of
order `n` the cyclic group has the largest value, `ψ(G) ≤ ψ(Cₙ)`, with equality only for `G` cyclic.

The proof is by strong induction on `n`. Let `q` be the largest prime divisor of `n`.
* If every element has `q · o(g) ≤ n`, then `q ψ(G) ≤ n² < q ψ(n)`.
* Otherwise some `⟨g⟩` has index `c < q`. Its Sylow `q`-subgroup `Q` is a Sylow subgroup of `G`
  normalised by `g`, so the number of Sylow `q`-subgroups divides `c < q`, hence is `1`, and `Q` is
  a cyclic normal Sylow subgroup. Then `ψ(G) ≤ ψ(Q) ψ(G/Q)` (the coset lemma below), and induction
  on `G/Q` finishes the proof.
-/

namespace SumElementOrders

open Finset

section Defs

variable (G : Type*) [Group G] [Fintype G]

/-- `ψ(G)`, the sum of the orders of the elements of `G`. -/
noncomputable def psi : ℕ := ∑ g : G, orderOf g

end Defs

variable {G : Type*} [Group G]

theorem psi_pos [Fintype G] : 0 < psi G :=
  Finset.sum_pos (fun g _ => orderOf_pos g) ⟨1, mem_univ _⟩

/-- `ψ(Cₙ) = ψ(n) = ∑_{d ∣ n} d φ(d)`. -/
theorem psi_eq_psiNat [Fintype G] [IsCyclic G] : psi G = psiNat (Nat.card G) := by
  classical
  rw [psi, psiNat, Nat.card_eq_fintype_card,
    ← Finset.sum_fiberwise_of_maps_to (g := orderOf) (t := (Fintype.card G).divisors)
      fun g _ => Nat.mem_divisors.2 ⟨orderOf_dvd_card, Fintype.card_ne_zero⟩]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_congr rfl fun g hg => (Finset.mem_filter.1 hg).2, Finset.sum_const, smul_eq_mul,
    IsCyclic.card_orderOf_eq_totient (Nat.dvd_of_mem_divisors hd), mul_comm]

/-- In a finite cyclic group, an element whose order divides that of `z` is a power of `z`. -/
theorem mem_zpowers_of_orderOf_dvd {C : Type*} [Group C] [IsCyclic C] [Finite C] {z w : C}
    (h : orderOf w ∣ orderOf z) : w ∈ Subgroup.zpowers z := by
  have : Subgroup.zpowers w ≤ Subgroup.zpowers z := by
    rwa [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers]
  exact this (Subgroup.mem_zpowers w)

/-- If `Q` is a cyclic normal subgroup, `bᵐ = 1` and `z ∈ Q`, then `o(bz) ∣ m · o(z)`: indeed
`(bz)ᵐ = ∏_{i=1}^{m} bⁱ z b⁻ⁱ` lies in `⟨z⟩`, since every conjugate of `z` does. -/
theorem orderOf_mul_dvd {Q : Subgroup G} [Q.Normal] [IsCyclic Q] [Finite Q] {b : G} {m : ℕ}
    (hb : b ^ m = 1) {z : G} (hz : z ∈ Q) : orderOf (b * z) ∣ m * orderOf z := by
  have hconj : ∀ i : ℕ, b ^ i * z * (b ^ i)⁻¹ ∈ Subgroup.zpowers z := by
    intro i
    have hmem : b ^ i * z * (b ^ i)⁻¹ ∈ Q := ‹Q.Normal›.conj_mem z hz _
    have hord : orderOf (b ^ i * z * (b ^ i)⁻¹) = orderOf z :=
      orderOf_injective (MulAut.conj (b ^ i)).toMonoidHom (MulAut.conj (b ^ i)).injective z
    have h := mem_zpowers_of_orderOf_dvd (z := (⟨z, hz⟩ : Q)) (w := ⟨_, hmem⟩)
      (by rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]; exact hord.dvd)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hpow : ∀ j : ℕ, (b * z) ^ j * (b ^ j)⁻¹ ∈ Subgroup.zpowers z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have : (b * z) ^ (j + 1) * (b ^ (j + 1))⁻¹ =
          ((b * z) ^ j * (b ^ j)⁻¹) * (b ^ (j + 1) * z * (b ^ (j + 1))⁻¹) := by
        simp only [pow_succ, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      rw [this]
      exact mul_mem ih (hconj _)
  have h1 := hpow m
  rw [hb, inv_one, mul_one] at h1
  apply orderOf_dvd_of_pow_eq_one
  rw [pow_mul, orderOf_dvd_iff_pow_eq_one.1 (orderOf_dvd_of_mem_zpowers h1)]

/-- If `|Q|` is coprime to `|G : Q|`, every coset `x` of `Q` has a representative `b` with
`b^{o(x)} = 1`. -/
theorem exists_rep {Q : Subgroup G} [Q.Normal] [Finite Q] [Finite (G ⧸ Q)]
    (hcop : (Nat.card Q).Coprime Q.index) (x : G ⧸ Q) :
    ∃ b : G, (b : G ⧸ Q) = x ∧ b ^ orderOf x = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  set m := orderOf (y : G ⧸ Q)
  have hm : m ∣ Q.index := orderOf_dvd_natCard _
  obtain ⟨t, ht1, ht2⟩ := Nat.chineseRemainder (hcop.symm.coprime_dvd_left hm) 1 0
  refine ⟨y ^ t, ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, ← pow_mod_orderOf, ht1, pow_mod_orderOf, pow_one]
  · have hQ : y ^ m ∈ Q := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]
    obtain ⟨s, hs⟩ := (Nat.modEq_zero_iff_dvd.1 ht2)
    have : (⟨y ^ m, hQ⟩ : Q) ^ Nat.card Q = 1 := pow_card_eq_one'
    rw [← pow_mul, mul_comm, pow_mul, hs, pow_mul]
    have := congrArg Subtype.val this
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
    rw [this, one_pow]

/-- **Coset lemma.** If `Q` is a cyclic normal subgroup with `|Q|` coprime to `|G : Q|`, then
`ψ(G) ≤ ψ(Q) ψ(G/Q)`, and the inequality is strict when `G/Q` is cyclic but `G` is not. -/
theorem psi_le_mul [Fintype G] {Q : Subgroup G} [Q.Normal] [IsCyclic Q] [Fintype Q]
    [Fintype (G ⧸ Q)] (hcop : (Nat.card Q).Coprime Q.index) :
    psi G ≤ psi Q * psi (G ⧸ Q) ∧
      (IsCyclic (G ⧸ Q) → ¬ IsCyclic G → psi G < psi Q * psi (G ⧸ Q)) := by
  choose r hr1 hr2 using exists_rep hcop
  have hmem : ∀ g : G, (r g)⁻¹ * g ∈ Q := fun g => QuotientGroup.eq.1 (hr1 _)
  let e : (G ⧸ Q) × Q ≃ G :=
    { toFun := fun p => r p.1 * p.2
      invFun := fun g => (g, ⟨(r g)⁻¹ * g, hmem g⟩)
      left_inv := fun ⟨x, z⟩ => by
        have hx : ((r x * z : G) : G ⧸ Q) = x := by
          rw [QuotientGroup.mk_mul, hr1, (QuotientGroup.eq_one_iff (z : G)).2 z.2, mul_one]
        ext
        · exact hx
        · simp [hx]
      right_inv := fun g => by simp }
  have hdvd : ∀ p : (G ⧸ Q) × Q, orderOf (e p) ∣ orderOf p.1 * orderOf p.2 := fun p => by
    rw [← Subgroup.orderOf_coe p.2]
    exact orderOf_mul_dvd (hr2 p.1) p.2.2
  have hsum : psi G = ∑ p : (G ⧸ Q) × Q, orderOf (e p) :=
    (Fintype.sum_equiv e _ _ fun _ => rfl).symm
  have hprod : psi Q * psi (G ⧸ Q) = ∑ p : (G ⧸ Q) × Q, orderOf p.1 * orderOf p.2 := by
    rw [psi, psi, Fintype.sum_prod_type, mul_comm, Finset.sum_mul_sum]
  refine ⟨?_, fun hGQ hG => ?_⟩
  · rw [hsum, hprod]
    exact Finset.sum_le_sum fun p _ => Nat.le_of_dvd (Nat.mul_pos (orderOf_pos _) (orderOf_pos _))
      (hdvd p)
  · obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G ⧸ Q)
    obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
    rw [hsum, hprod]
    refine Finset.sum_lt_sum (fun p _ => Nat.le_of_dvd
      (Nat.mul_pos (orderOf_pos _) (orderOf_pos _)) (hdvd p)) ⟨(x, z), mem_univ _, ?_⟩
    refine lt_of_le_of_ne (Nat.le_of_dvd (Nat.mul_pos (orderOf_pos _) (orderOf_pos _))
      (hdvd _)) fun h => hG (isCyclic_of_orderOf_eq_card (e (x, z)) ?_)
    rw [h, hx, hz, ← Subgroup.card_mul_index Q, mul_comm]
    rfl

/-- If some `⟨g⟩` has index smaller than a prime `q` and `Q ≤ ⟨g⟩` is a Sylow `q`-subgroup, then
`Q` is normal: the number of Sylow `q`-subgroups is `≡ 1 mod q` and equals `|G : N_G(Q)|`, which
divides `|G : ⟨g⟩| < q`, because `⟨g⟩` is abelian and so normalises `Q`. -/
theorem normal_of_index_lt [Finite G] {q : ℕ} [hq : Fact q.Prime] {g : G}
    (hc : (Subgroup.zpowers g).index < q) (Q : Subgroup G) (hQg : Q ≤ Subgroup.zpowers g)
    (hQ : Nat.card Q = q ^ (Nat.card G).factorization q) : Q.Normal := by
  let P : Sylow q G := Sylow.ofCard Q hQ
  have hcomm : ∀ x ∈ Subgroup.zpowers g, ∀ y ∈ Subgroup.zpowers g, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Commute.zpow_zpow_self g i j
  have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (Q : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rwa [hcomm k hk h (hQg hh), mul_inv_cancel_right]
    · intro hh
      have h' := hcomm k hk _ (hQg hh)
      have : h = k * h * k⁻¹ := by
        calc h = k⁻¹ * (k * h * k⁻¹) * k := by group
          _ = k * h * k⁻¹ := by rw [mul_assoc, ← h', ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]; exact hh
  have hN : Nat.card (Sylow q G) = 1 := by
    have h1 := card_sylow_modEq_one q G
    have h2 : Nat.card (Sylow q G) ∣ (Subgroup.zpowers g).index := by
      rw [Sylow.card_eq_index_normalizer P]
      exact Subgroup.index_dvd_of_le hle
    have h3 : 0 < (Subgroup.zpowers g).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h4 := Nat.le_of_dvd h3 h2
    unfold Nat.ModEq at h1
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hq.out.one_lt] at h1
  have := Sylow.card_eq_index_normalizer P
  rw [hN, eq_comm, Subgroup.index_eq_one] at this
  exact Subgroup.normalizer_eq_top_iff.1 this

/-- **Amiri–Jafarian Amiri–Isaacs.** For a group `G` of order `n`, `ψ(G) ≤ ψ(n) = ψ(Cₙ)`, and
`ψ(G) < ψ(n)` unless `G` is cyclic. -/
theorem psi_le_psiNat_and_lt (n : ℕ) :
    ∀ (G : Type*) [Group G] [Fintype G], Nat.card G = n →
      psi G ≤ psiNat n ∧ (¬ IsCyclic G → psi G < psiNat n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn
  by_cases hcyc : IsCyclic G
  · exact ⟨(psi_eq_psiNat.trans (by rw [hn])).le, fun h => absurd hcyc h⟩
  suffices psi G < psiNat n from ⟨this.le, fun _ => this⟩
  have hn0 : n ≠ 0 := by rw [← hn]; exact Nat.card_pos.ne'
  have hn2 : 2 ≤ n := by
    by_contra h
    have h1 : Nat.card G = 1 := by omega
    exact hcyc (@isCyclic_of_subsingleton G _ (Nat.card_eq_one_iff_unique.mp h1).1)
  have hS : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
  set q := n.primeFactors.max' hS
  have hqS : q ∈ n.primeFactors := n.primeFactors.max'_mem hS
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqS
  have hqn : q ∣ n := Nat.dvd_of_mem_primeFactors hqS
  have : Fact q.Prime := ⟨hqp⟩
  have hlt : n ^ 2 < q * psiNat n := sq_lt_maxPrime_mul_psiNat hn2
  by_cases hA : ∀ g : G, q * orderOf g ≤ n
  · -- every element has `q · o(g) ≤ n`, so `q ψ(G) ≤ n² < q ψ(n)`
    have : q * psi G ≤ n ^ 2 := by
      calc q * psi G = ∑ g : G, q * orderOf g := by rw [psi, Finset.mul_sum]
        _ ≤ ∑ _g : G, n := Finset.sum_le_sum fun g _ => hA g
        _ = n ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hn, smul_eq_mul, sq]
    exact Nat.lt_of_mul_lt_mul_left (this.trans_lt hlt)
  -- some `⟨g⟩` has index `< q`
  obtain ⟨g, hg⟩ := not_forall.1 hA
  rw [not_le] at hg
  have hidx : orderOf g * (Subgroup.zpowers g).index = n := by
    rw [← Nat.card_zpowers, Subgroup.card_mul_index, hn]
  have hc : (Subgroup.zpowers g).index < q := by
    by_contra h
    rw [not_lt] at h
    have : orderOf g * q ≤ n := hidx ▸ Nat.mul_le_mul_left _ h
    rw [mul_comm] at this
    omega
  set a := n.factorization q
  have hcq : ¬ q ∣ (Subgroup.zpowers g).index := fun h =>
    absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h) (by omega)
  have hqa : q ^ a ∣ orderOf g :=
    (((Nat.Prime.coprime_iff_not_dvd hqp).2 hcq).pow_left a).dvd_of_dvd_mul_right
      (hidx ▸ Nat.ordProj_dvd n q)
  -- `Q`, the Sylow `q`-subgroup of `⟨g⟩`, is a cyclic normal Sylow subgroup of `G`
  set Q := Subgroup.zpowers (g ^ (orderOf g / q ^ a))
  have hQcard : Nat.card Q = q ^ a := by
    rw [Nat.card_zpowers, orderOf_pow_orderOf_div (orderOf_pos g).ne' hqa]
  have hQg : Q ≤ Subgroup.zpowers g :=
    Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _)
  have : Q.Normal := normal_of_index_lt hc Q hQg (by rw [hQcard, hn])
  have hidxQ : Q.index = n / q ^ a := by
    have := Subgroup.card_mul_index Q
    rw [hQcard, hn] at this
    rw [← this, Nat.mul_div_cancel_left _ (pow_pos hqp.pos _)]
  have hcop' : (q ^ a).Coprime (n / q ^ a) := (Nat.coprime_ordCompl hqp hn0).pow_left a
  have hcop : (Nat.card Q).Coprime Q.index := by rw [hQcard, hidxQ]; exact hcop'
  have hm : Q.index < n := by
    rw [hidxQ]
    exact Nat.div_lt_self (by omega)
      (Nat.one_lt_pow (Nat.pos_iff_ne_zero.1 (hqp.factorization_pos_of_dvd hn0 hqn)) hqp.one_lt)
  let : Fintype (G ⧸ Q) := Fintype.ofFinite _
  let : Fintype Q := Fintype.ofFinite _
  obtain ⟨ih1, ih2⟩ := ih _ hm (G ⧸ Q) rfl
  have hsplit : psiNat n = psi Q * psiNat Q.index := by
    rw [psi_eq_psiNat, hQcard, hidxQ, ← psiNat_mul hcop', Nat.ordProj_mul_ordCompl_eq_self]
  obtain ⟨hle, hlt'⟩ := psi_le_mul hcop
  rw [hsplit]
  by_cases hGQ : IsCyclic (G ⧸ Q)
  · exact (hlt' hGQ hcyc).trans_le (Nat.mul_le_mul_left _ ih1)
  · exact hle.trans_lt (Nat.mul_lt_mul_of_pos_left (ih2 hGQ) psi_pos)

/-- **Amiri–Jafarian Amiri–Isaacs.** `ψ(G) ≤ ψ(C_{|G|})`. -/
theorem psi_le [Fintype G] : psi G ≤ psiNat (Nat.card G) :=
  (psi_le_psiNat_and_lt _ G rfl).1

/-- **Amiri–Jafarian Amiri–Isaacs.** `ψ(G) < ψ(C_{|G|})` if `G` is not cyclic. -/
theorem psi_lt [Fintype G] (h : ¬ IsCyclic G) : psi G < psiNat (Nat.card G) :=
  (psi_le_psiNat_and_lt _ G rfl).2 h

/-- `ψ(G) = ψ(C_{|G|})` if and only if `G` is cyclic. -/
theorem psi_eq_iff [Fintype G] : psi G = psiNat (Nat.card G) ↔ IsCyclic G :=
  ⟨fun h => by_contra fun hc => (psi_lt hc).ne h, fun _ => psi_eq_psiNat⟩

end SumElementOrders
