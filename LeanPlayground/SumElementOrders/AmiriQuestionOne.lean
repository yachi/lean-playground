module

public import LeanPlayground.SumElementOrders.AmiriQuestion
public import Mathlib.Algebra.Group.MinimalAxioms

@[expose] public section

/-!
# A negative answer to Amiri's Question 3.10 (1)

Amiri (arXiv:2511.08320, Question 3.10 (1)) asked: if `G` is a finite LCM-group and `H` a finite
group with `|H| = |G|`, `exp(H) ∣ exp(G)` and `ψ(G) = ψ(H)`, must `G` and `H` have the same order
type (the same number of elements of each order)? We answer this in the negative.

For a `2`-group of order `2ⁿ` and exponent `2ᵉ` write `cᵢ = #{x : x^(2ⁱ) = 1}`. Then
`ψ = 2ᵉ·2ⁿ − ∑_{i<e} 2ⁱ cᵢ`, so equal `ψ` only constrains one linear combination of the `cᵢ`,
while the order type is the whole vector `(c₀, c₁, …)`.

* `G = C₈ × C₂⁷` (abelian): `(c₁, c₂, c₃) = (256, 512, 1024)`, so it has 255 involutions and
  `ψ(G) = 8·1024 − (1 + 512 + 2048) = 5631`.
* `H = Hol(C₈) × (C₄ ≀ C₂)`, where `Hol(C₈) = C₈ ⋊ (ℤ/8)ˣ` has `(c₁, c₂, c₃) = (16, 24, 32)` and
  `C₄ ≀ C₂ = (C₄ × C₄) ⋊ C₂` has `(c₁, c₂, c₃) = (8, 24, 32)`, so `H` has
  `(c₁, c₂, c₃) = (128, 576, 1024)`, 127 involutions and `ψ(H) = 8·1024 − (1 + 256 + 2304) = 5631`.

Both have order 1024 and exponent 8, but `G` has 255 involutions and `H` only 127.

A GAP search over all groups of order at most 255 (`scripts/amiri-q310/search.g`) finds no
counterexample; the least order is 256 (`scripts/amiri-q310/pgroups.g`), e.g.
`G = C₄ × C₈ × Q₈ = SmallGroup(256, 13503)` (an LCM-group, `ψ = 1519`, 7 involutions) against
`H = SmallGroup(256, 2761)` (71 involutions). The order-1024 example above is used here because
both groups are easy to build in Lean and all counts are checked by `decide +kernel`.
-/

namespace SumElementOrders

open Finset

/-- In a group of exponent dividing 8 the order of an element is read off from `g`, `g²`, `g⁴`. -/
theorem orderOf_eq_of_pow_eight {G : Type*} [Group G] [DecidableEq G] {g : G} (h : g ^ 8 = 1) :
    orderOf g =
      if g = 1 then 1 else if g ^ 2 = 1 then 2 else if g ^ 4 = 1 then 4 else 8 := by
  split_ifs with h1 h2 h4
  · simp [h1]
  · exact orderOf_eq_prime h2 h1
  · have hd : orderOf g ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h4)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    interval_cases k
    · exact absurd (orderOf_eq_one_iff.1 (by simpa using hk')) h1
    · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [hk']; simp)) h2
    · simpa using hk'
  · have hd : orderOf g ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one (by simpa using h)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    interval_cases k
    · exact absurd (orderOf_eq_one_iff.1 (by simpa using hk')) h1
    · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [hk']; simp)) h2
    · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [hk']; simp)) h4
    · simpa using hk'

/-- The holomorph `C₈ ⋊ Aut(C₈)` of the cyclic group of order 8, as pairs `(a, u)` with
`(a, u) (b, v) = (a + u b, u v)`. -/
def Hol8 : Type := ZMod 8 × (ZMod 8)ˣ

namespace Hol8

instance : Fintype Hol8 := inferInstanceAs (Fintype (ZMod 8 × (ZMod 8)ˣ))
instance : DecidableEq Hol8 := inferInstanceAs (DecidableEq (ZMod 8 × (ZMod 8)ˣ))
instance : Mul Hol8 := ⟨fun x y => (x.1 + (x.2 : ZMod 8) * y.1, x.2 * y.2)⟩
instance : One Hol8 := ⟨(0, 1)⟩
instance : Inv Hol8 := ⟨fun x => (-(((x.2⁻¹ : (ZMod 8)ˣ) : ZMod 8) * x.1), x.2⁻¹)⟩

instance : Group Hol8 := Group.ofLeftAxioms
  (fun x y z => Prod.ext (show x.1 + (x.2 : ZMod 8) * y.1 + ((x.2 * y.2 : (ZMod 8)ˣ) : ZMod 8) * z.1
      = x.1 + (x.2 : ZMod 8) * (y.1 + (y.2 : ZMod 8) * z.1) by push_cast; ring)
    (mul_assoc x.2 y.2 z.2))
  (fun x => Prod.ext (show (0 : ZMod 8) + ((1 : (ZMod 8)ˣ) : ZMod 8) * x.1 = x.1 by simp)
    (one_mul x.2))
  (fun x => Prod.ext
    (show -(((x.2⁻¹ : (ZMod 8)ˣ) : ZMod 8) * x.1) + ((x.2⁻¹ : (ZMod 8)ˣ) : ZMod 8) * x.1 = 0
      by ring) (inv_mul_cancel x.2))

end Hol8

/-- The wreath product `C₄ ≀ C₂ = (C₄ × C₄) ⋊ C₂`, the generator of `C₂` swapping the factors. -/
def Wr42 : Type := ZMod 4 × ZMod 4 × ZMod 2

namespace Wr42

/-- Swap the two `C₄` coordinates when `s = 1`. -/
def act (s : ZMod 2) (p : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 := if s = 0 then p else (p.2, p.1)

instance : Fintype Wr42 := inferInstanceAs (Fintype (ZMod 4 × ZMod 4 × ZMod 2))
instance : DecidableEq Wr42 := inferInstanceAs (DecidableEq (ZMod 4 × ZMod 4 × ZMod 2))
instance : Mul Wr42 :=
  ⟨fun x y => let p := (x.1, x.2.1) + act x.2.2 (y.1, y.2.1); (p.1, p.2, x.2.2 + y.2.2)⟩
instance : One Wr42 := ⟨(0, 0, 0)⟩
instance : Inv Wr42 := ⟨fun x => let p := act x.2.2 (-x.1, -x.2.1); (p.1, p.2, x.2.2)⟩

instance : Group Wr42 := Group.ofLeftAxioms (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

end Wr42

/-- `G = C₈ × C₂⁷`, abelian of order 1024. -/
abbrev GroupG1 : Type :=
  Multiplicative (ZMod 8 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)

-- The default instance-size bound is too small for an eight-fold product.
set_option synthInstance.maxSize 2000 in
instance : DecidableEq GroupG1 := instDecidableEqMultiplicative

/-- `H = Hol(C₈) × (C₄ ≀ C₂)`, of order 1024. -/
abbrev GroupH1 : Type := Hol8 × Wr42

theorem pow_eight_groupG1 : ∀ g : GroupG1, g ^ 8 = 1 := by decide +kernel

theorem pow_eight_groupH1 : ∀ g : GroupH1, g ^ 8 = 1 := by decide +kernel

theorem card_groupG1 : Nat.card GroupG1 = 1024 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem card_groupH1 : Nat.card GroupH1 = 1024 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem psi_groupG1 : psi GroupG1 = 5631 := by
  rw [psi, Finset.sum_congr rfl fun g _ => orderOf_eq_of_pow_eight (pow_eight_groupG1 g)]
  decide +kernel

theorem psi_groupH1 : psi GroupH1 = 5631 := by
  rw [psi, Finset.sum_congr rfl fun g _ => orderOf_eq_of_pow_eight (pow_eight_groupH1 g)]
  decide +kernel

/-- `G` and `H` have the same order type: the same number of elements of each order. -/
def SameOrderType (G H : Type*) [Group G] [Group H] : Prop :=
  ∀ n : ℕ, Nat.card {g : G // orderOf g = n} = Nat.card {h : H // orderOf h = n}

theorem card_involutions_groupG1 : Nat.card {g : GroupG1 // orderOf g = 2} = 255 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.filter_congr fun g _ => by rw [orderOf_eq_of_pow_eight (pow_eight_groupG1 g)]]
  decide +kernel

theorem card_involutions_groupH1 : Nat.card {h : GroupH1 // orderOf h = 2} = 127 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.filter_congr fun g _ => by rw [orderOf_eq_of_pow_eight (pow_eight_groupH1 g)]]
  decide +kernel

theorem exponent_groupH1_dvd : Monoid.exponent GroupH1 ∣ 8 :=
  Monoid.exponent_dvd_of_forall_pow_eq_one pow_eight_groupH1

theorem exponent_groupG1 : Monoid.exponent GroupG1 = 8 := by
  apply Nat.dvd_antisymm (Monoid.exponent_dvd_of_forall_pow_eq_one pow_eight_groupG1)
  let x : GroupG1 := Multiplicative.ofAdd (1, 0, 0, 0, 0, 0, 0, 0)
  have h : orderOf x = 8 := by
    rw [orderOf_eq_of_pow_eight (pow_eight_groupG1 _)]; decide +kernel
  calc 8 = orderOf x := h.symm
    _ ∣ Monoid.exponent GroupG1 := Monoid.order_dvd_exponent x

/-- **Amiri's Question 3.10 (1) has a negative answer.** There are finite groups `G`, `H` of the
same order with `G` an LCM-group (here even abelian), `exp(H) ∣ exp(G)` and `ψ(G) = ψ(H)`, which
do not have the same order type. -/
theorem amiri_question_3_10_one_false :
    ∃ (G H : Type) (_ : Group G) (_ : Group H) (_ : Fintype G) (_ : Fintype H),
      IsLCMGroup G ∧ Nat.card H = Nat.card G ∧ Monoid.exponent H ∣ Monoid.exponent G ∧
        psi G = psi H ∧ ¬ SameOrderType G H :=
  ⟨GroupG1, GroupH1, inferInstance, inferInstance, inferInstance, inferInstance,
    isLCMGroup_of_comm _, card_groupH1.trans card_groupG1.symm,
    by rw [exponent_groupG1]; exact exponent_groupH1_dvd, psi_groupG1.trans psi_groupH1.symm,
    fun h => by have := h 2; rw [card_involutions_groupG1, card_involutions_groupH1] at this
                exact absurd this (by norm_num)⟩

end SumElementOrders
