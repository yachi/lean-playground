module

public import LeanPlayground.SumElementOrders.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# A negative answer to Amiri's Question 3.10 (2)

For a finite group `G` let `ψ(G) = ∑_{g ∈ G} o(g)`. Following M. Amiri, *On the sum of element
orders in finite abelian groups* (arXiv:2511.08320), call `G` an *LCM-group* if
`o(xⁿy) ∣ lcm(o(xⁿ), o(y))` for all `x, y ∈ G` and `n ∈ ℤ`. Every abelian group is an LCM-group.

Amiri proved that two finite LCM-groups of the same order have the same `ψ` if and only if they
have the same order type, and asked (Question 3.10):

> Let `G` be a finite LCM-group and `H` a finite group with `|H| = |G|` and `exp(H) ∣ exp(G)`.
> (1) If `ψ(G) = ψ(H)`, must `G` and `H` have the same order type?
> (2) If `H` is not an LCM-group, is it true that `ψ(H) < ψ(G)`?

We answer (2) in the negative. Take
* `G = C₄ × C₂ × C₂ × C₂` (abelian): 1 identity, 15 involutions, 16 elements of order 4, so
  `ψ(G) = 1 + 30 + 64 = 95`;
* `H = C₄ × D₈` (here `D₈ = DihedralGroup 4` has order 8): 1 identity, 11 involutions,
  20 elements of order 4, so `ψ(H) = 1 + 22 + 80 = 103`.

Both have order 32 and exponent 4, and `H` is not an LCM-group because two reflections of `D₈`
(order 2) multiply to a rotation of order 4. So `ψ(H) > ψ(G)`.

A GAP search over all groups of order at most 255 shows 32 is the least order with
`ψ(H) > ψ(G)`; at order 16 the Pauli group `C₄ ∘ D₈` (non-LCM) already has `ψ = 47 = ψ(C₄ × C₂²)`,
so even the weak inequality `ψ(H) ≤ ψ(G)` is the best one could hope for, and it too fails at
order 32. The same search found no counterexample to part (1).
-/

namespace SumElementOrders

open Finset

/-- `G` is an *LCM-group* (Amiri): `o(xⁿy)` divides `lcm(o(xⁿ), o(y))` for all `x, y, n`. -/
def IsLCMGroup (G : Type*) [Group G] : Prop :=
  ∀ (x y : G) (n : ℤ), orderOf (x ^ n * y) ∣ Nat.lcm (orderOf (x ^ n)) (orderOf y)

/-- Every commutative group is an LCM-group. -/
theorem isLCMGroup_of_comm (G : Type*) [CommGroup G] : IsLCMGroup G :=
  fun x y n => (Commute.all (x ^ n) y).orderOf_mul_dvd_lcm

/-- In a group of exponent dividing 4 the order of an element is read off from `g = 1`, `g² = 1`. -/
theorem orderOf_eq_of_pow_four {G : Type*} [Group G] [DecidableEq G] {g : G} (h : g ^ 4 = 1) :
    orderOf g = if g = 1 then 1 else if g ^ 2 = 1 then 2 else 4 := by
  split_ifs with h1 h2
  · simp [h1]
  · exact orderOf_eq_prime h2 h1
  · have hd : orderOf g ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    interval_cases k
    · exact absurd (orderOf_eq_one_iff.1 (by simpa using hk')) h1
    · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [hk']; simp)) h2
    · simpa using hk'

/-- `ψ` of a group of exponent dividing 4, as a decidable sum. -/
theorem psi_eq_of_pow_four (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (h : ∀ g : G, g ^ 4 = 1) :
    psi G = ∑ g : G, if g = 1 then 1 else if g ^ 2 = 1 then 2 else 4 :=
  Finset.sum_congr rfl fun g _ => orderOf_eq_of_pow_four (h g)

/-- The abelian group `C₄ × C₂ × C₂ × C₂`. -/
abbrev GroupG : Type := Multiplicative (ZMod 4 × ZMod 2 × ZMod 2 × ZMod 2)

/-- The group `C₄ × D₈`. -/
abbrev GroupH : Type := Multiplicative (ZMod 4) × DihedralGroup 4

theorem card_groupG : Nat.card GroupG = 32 := by
  rw [Nat.card_eq_fintype_card]; rfl

theorem card_groupH : Nat.card GroupH = 32 := by
  rw [Nat.card_eq_fintype_card]; rfl

theorem pow_four_groupG : ∀ g : GroupG, g ^ 4 = 1 := by decide

theorem pow_four_groupH : ∀ g : GroupH, g ^ 4 = 1 := by decide

theorem psi_groupG : psi GroupG = 95 := by
  rw [psi_eq_of_pow_four _ pow_four_groupG]; decide

theorem psi_groupH : psi GroupH = 103 := by
  rw [psi_eq_of_pow_four _ pow_four_groupH]; decide

theorem exponent_groupH_dvd : Monoid.exponent GroupH ∣ 4 :=
  Monoid.exponent_dvd_of_forall_pow_eq_one pow_four_groupH

theorem exponent_groupG : Monoid.exponent GroupG = 4 := by
  apply Nat.dvd_antisymm (Monoid.exponent_dvd_of_forall_pow_eq_one pow_four_groupG)
  let x : GroupG := Multiplicative.ofAdd (1, 0, 0, 0)
  have h : orderOf x = 4 := by
    rw [orderOf_eq_of_pow_four (pow_four_groupG _)]; decide
  calc 4 = orderOf x := h.symm
    _ ∣ Monoid.exponent GroupG := Monoid.order_dvd_exponent x

theorem isLCMGroup_groupG : IsLCMGroup GroupG := isLCMGroup_of_comm _

/-- `C₄ × D₈` is not an LCM-group: two reflections of order 2 multiply to an element of order 4. -/
theorem not_isLCMGroup_groupH : ¬ IsLCMGroup GroupH := by
  intro h
  have := h (1, DihedralGroup.sr 0) (1, DihedralGroup.sr 1) 1
  rw [orderOf_eq_of_pow_four (pow_four_groupH _), orderOf_eq_of_pow_four (pow_four_groupH _),
    orderOf_eq_of_pow_four (pow_four_groupH _)] at this
  revert this
  decide

/-- **Amiri's Question 3.10 (2) has a negative answer.** There are finite groups `G`, `H` of the
same order with `G` an LCM-group, `exp(H) ∣ exp(G)`, `H` not an LCM-group, and `ψ(G) < ψ(H)`. -/
theorem amiri_question_3_10_two_false :
    ∃ (G H : Type) (_ : Group G) (_ : Group H) (_ : Fintype G) (_ : Fintype H),
      IsLCMGroup G ∧ Nat.card H = Nat.card G ∧ Monoid.exponent H ∣ Monoid.exponent G ∧
        ¬ IsLCMGroup H ∧ psi G < psi H :=
  ⟨GroupG, GroupH, inferInstance, inferInstance, inferInstance, inferInstance, isLCMGroup_groupG,
    card_groupH.trans card_groupG.symm, by rw [exponent_groupG]; exact exponent_groupH_dvd,
    not_isLCMGroup_groupH,
    by rw [psi_groupG, psi_groupH]; norm_num⟩

end SumElementOrders
