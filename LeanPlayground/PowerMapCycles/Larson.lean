module

public import LeanPlayground.PowerMapCycles.Frobenius
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

/-!
# Cyclic groups minimize the number of cycles of `x ↦ xᵃ`

For a finite group `G` and `a : ℕ` let `G(a, G)` be the functional graph of `x ↦ xᵃ` and
`N(a, G)` its number of connected components (equivalently, of cycles). M. Larson, *Power maps
in finite groups*, Integers 19 (2019) A58 (arXiv:1707.06696), Conjecture 1.2:

> If `G` has order `n`, then `N(a, G) ≥ N(a, Cₙ)`.

Larson proved this for nilpotent `G` and checked it by computer for `|G| ≤ 1000`, `|G| ≠ 768`,
`2 ≤ a ≤ 20`. We prove it for all finite groups and all `a` (`larson_conjecture`).

## Proof

Let `n = |G|` and `K = φ(n)`. The periodic points of `x ↦ xᵃ` form
`S = {x : x^(aᴷ) = x}` (`mem_periodic_of_pow_pow_eq`: a point with `x^(aᵐ) = x` for some
`m ≥ 1` has order prime to `a`, so `a^φ(o(x)) ≡ 1` and `φ(o(x)) ∣ φ(n)`). The group `ZMod K`
acts on `S` by `j +ᵥ s = s^(a^j)`, and the components of the graph are the orbits of this action
(`componentsEquivOrbits`). By Burnside's lemma
`K · N(a, G) = ∑_{j ∈ ZMod K} #{x ∈ G : x^(a^{m_j}) = x}` with `m_j ≥ 1`, and
`#{x : x^(aᵐ) = x} = #{x : x^g = 1}` for `g = gcd(aᵐ − 1, n)`. Frobenius' theorem gives
`#{x ∈ G : x^g = 1} ≥ g`, with equality for the cyclic group. Comparing the two Burnside sums
term by term proves the conjecture.
-/

open Finset

namespace PowerMapCycles

variable {G : Type*} [Group G]

/-- `N(a, G)`: the number of connected components of the graph on `G` with an edge
`x — xᵃ` for every `x` (Larson's `G(a, G)`). -/
noncomputable def powerMapComponents (G : Type*) [Group G] (a : ℕ) : ℕ :=
  Nat.card (Quot fun x y : G => x ^ a = y)

/-! ### Periodic points -/

/-- Points with `x^(aᵐ) = x` for some `m ≥ 1` satisfy `x^(a^φ(|G|)) = x`. -/
theorem mem_periodic_of_pow_pow_eq [Finite G] {a m : ℕ} (hm : 1 ≤ m) {x : G}
    (hx : x ^ (a ^ m) = x) : x ^ (a ^ (Nat.card G).totient) = x := by
  have hK : 1 ≤ (Nat.card G).totient := Nat.totient_pos.mpr Nat.card_pos
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [zero_pow (by omega), pow_zero] at hx
    rw [← hx, one_pow]
  -- `orderOf x ∣ aᵐ - 1`, so `a` is a unit modulo `orderOf x`
  have h1 : 1 ≤ a ^ m := Nat.one_le_pow _ _ ha
  have hd : orderOf x ∣ a ^ m - 1 := by
    apply orderOf_dvd_of_pow_eq_one
    have : x ^ (a ^ m - 1) * x = x := by rw [← pow_succ, Nat.sub_add_cancel h1, hx]
    simpa using this
  have hcop : Nat.Coprime a (orderOf x) := by
    have h2 : Nat.Coprime (a ^ m) (a ^ m - 1) := by
      have := (Nat.coprime_add_self_left (m := 1) (n := a ^ m - 1)).mpr (Nat.coprime_one_left _)
      rwa [Nat.add_comm, Nat.sub_add_cancel h1] at this
    exact ((h2.coprime_dvd_left (dvd_pow_self a (by omega))).coprime_dvd_right hd)
  have htot := Nat.ModEq.pow_totient hcop
  have hdvd : (orderOf x).totient ∣ (Nat.card G).totient :=
    Nat.totient_dvd_of_dvd (orderOf_dvd_natCard x)
  obtain ⟨c, hc⟩ := hdvd
  have : a ^ (Nat.card G).totient ≡ 1 [MOD orderOf x] := by
    rw [hc, pow_mul]
    simpa using htot.pow c
  conv_rhs => rw [← pow_one x]
  exact pow_eq_pow_iff_modEq.mpr this

/-- The set `S` of periodic points, for a period `K`. -/
def Periodic (G : Type*) [Group G] (a K : ℕ) : Type _ := {x : G // x ^ (a ^ K) = x}

/-- On a periodic point, `x^(aᵐ)` only depends on `m mod K`. -/
theorem pow_pow_mod {a K : ℕ} {x : G} (hx : x ^ (a ^ K) = x) (m : ℕ) :
    x ^ (a ^ m) = x ^ (a ^ (m % K)) := by
  have hq : ∀ q : ℕ, x ^ ((a ^ K) ^ q) = x := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [pow_succ, pow_mul, ih, hx]
  conv_lhs => rw [← Nat.div_add_mod m K, pow_add, pow_mul, pow_mul, hq]

instance {a K : ℕ} [NeZero K] : AddAction (ZMod K) (Periodic G a K) where
  vadd j s := ⟨s.1 ^ (a ^ j.val), by rw [← pow_mul, mul_comm, pow_mul, s.2]⟩
  zero_vadd s := by
    apply Subtype.ext
    change s.1 ^ (a ^ (0 : ZMod K).val) = s.1
    rw [ZMod.val_zero, pow_zero, pow_one]
  add_vadd j j' s := by
    apply Subtype.ext
    change s.1 ^ (a ^ (j + j').val) = (s.1 ^ (a ^ j'.val)) ^ (a ^ j.val)
    rw [ZMod.val_add, ← pow_mul, ← pow_add, Nat.add_comm j'.val, ← pow_pow_mod s.2]

theorem vadd_val {a K : ℕ} [NeZero K] (j : ZMod K) (s : Periodic G a K) :
    (j +ᵥ s).1 = s.1 ^ (a ^ j.val) := rfl

/-! ### Components are orbits -/

section Components

variable [Finite G] (a : ℕ)

/-- The common period `K = φ(|G|)` of all periodic points. -/
noncomputable abbrev period (G : Type*) [Group G] : ℕ := (Nat.card G).totient

instance : NeZero (period G) := ⟨(Nat.totient_pos.mpr Nat.card_pos).ne'⟩

/-- Every element reaches a periodic point after `|G|` steps. -/
theorem pow_pow_card_mem (x : G) :
    (x ^ (a ^ Nat.card G)) ^ (a ^ period G) = x ^ (a ^ Nat.card G) := by
  classical
  let _ := Fintype.ofFinite G
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Nat.card G + 1) => x ^ (a ^ (i : ℕ))) (by simp [Nat.card_eq_fintype_card])
  -- wlog `i < j`
  have key : ∀ i j : ℕ, i < j → j ≤ Nat.card G → x ^ (a ^ i) = x ^ (a ^ j) →
      (x ^ (a ^ Nat.card G)) ^ (a ^ period G) = x ^ (a ^ Nat.card G) := by
    intro i j hij hj heq
    have hy : (x ^ (a ^ i)) ^ (a ^ (j - i)) = x ^ (a ^ i) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hij.le, heq]
    have hyS := mem_periodic_of_pow_pow_eq (by omega) hy
    have hxy : x ^ (a ^ Nat.card G) = (x ^ (a ^ i)) ^ (a ^ (Nat.card G - i)) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [hxy, ← pow_mul, mul_comm, pow_mul, hyS]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact key i j h (by omega) heq
  · exact key j i h (by omega) heq.symm

omit [Finite G] in
theorem quot_mk_pow_pow (n : ℕ) (x : G) :
    Quot.mk (fun x y : G => x ^ a = y) (x ^ (a ^ n)) = Quot.mk _ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ih, pow_succ, pow_mul]
    exact (Quot.sound (r := fun x y : G => x ^ a = y) rfl).symm

/-- The periodic point `x^(a^|G|)` below `x`. -/
noncomputable def toPeriodic (x : G) : Periodic G a (period G) :=
  ⟨x ^ (a ^ Nat.card G), pow_pow_card_mem a x⟩

/-- The components of the graph of `x ↦ xᵃ` are the `ZMod (period G)`-orbits of periodic points. -/
noncomputable def componentsEquivOrbits :
    Quot (fun x y : G => x ^ a = y) ≃
      Quotient (AddAction.orbitRel (ZMod (period G)) (Periodic G a (period G))) where
  toFun := Quot.lift (fun x => ⟦toPeriodic a x⟧) (by
    rintro x _ rfl
    refine Quotient.sound ((AddAction.orbitRel _ _).iseqv.symm ⟨(1 : ZMod (period G)), ?_⟩)
    apply Subtype.ext
    rw [vadd_val]
    change (x ^ (a ^ Nat.card G)) ^ (a ^ (1 : ZMod (period G)).val) = (x ^ a) ^ (a ^ Nat.card G)
    rw [ZMod.val_one_eq_one_mod, ← pow_pow_mod (pow_pow_card_mem a x), pow_one, ← pow_mul,
      ← pow_mul, mul_comm])
  invFun := Quotient.lift (fun s => Quot.mk _ s.1) (by
    rintro s t ⟨j, rfl⟩
    change Quot.mk _ (j +ᵥ t).1 = Quot.mk _ t.1
    rw [vadd_val, quot_mk_pow_pow])
  left_inv := by
    rintro ⟨x⟩
    change Quot.mk _ (x ^ (a ^ Nat.card G)) = Quot.mk _ x
    exact quot_mk_pow_pow a _ x
  right_inv := by
    rintro ⟨s⟩
    change ⟦toPeriodic a s.1⟧ = ⟦s⟧
    apply Quotient.sound
    refine ⟨((Nat.card G : ℕ) : ZMod (period G)), ?_⟩
    apply Subtype.ext
    rw [vadd_val, ZMod.val_natCast, ← pow_pow_mod s.2]
    rfl

/-- The fixed points of `j ∈ ZMod (period G)` are the solutions of `x^(aᵐ) = x`, `m = j` or `K`. -/
noncomputable def fixedByEquiv (j : ZMod (period G)) :
    AddAction.fixedBy (Periodic G a (period G)) j ≃
      {x : G // x ^ (a ^ (if j.val = 0 then period G else j.val)) = x} where
  toFun s := ⟨s.1.1, by
    have hs : s.1.1 ^ (a ^ j.val) = s.1.1 := congrArg Subtype.val s.2
    split_ifs with h
    · exact s.1.2
    · exact hs⟩
  invFun x := ⟨⟨x.1, by
      have hm : 1 ≤ (if j.val = 0 then period G else j.val) := by
        split_ifs with h
        · exact Nat.totient_pos.mpr Nat.card_pos
        · omega
      exact mem_periodic_of_pow_pow_eq hm x.2⟩, by
    apply Subtype.ext
    change x.1 ^ (a ^ j.val) = x.1
    have hx := x.2
    split_ifs at hx with h
    · have h' : a ^ j.val = 1 := by rw [h, pow_zero]
      rw [h', pow_one]
    · exact hx⟩
  left_inv s := rfl
  right_inv x := rfl

/-- Burnside's lemma for the action of `ZMod (period G)` on the periodic points. -/
theorem card_mul_totient :
    powerMapComponents G a * period G =
      ∑ j : ZMod (period G),
        Nat.card {x : G // x ^ (a ^ (if j.val = 0 then period G else j.val)) = x} := by
  classical
  let _ := Fintype.ofFinite G
  have : Finite (Periodic G a (period G)) := Subtype.finite
  let _ : Fintype (Periodic G a (period G)) := Fintype.ofFinite _
  let _ : ∀ j : ZMod (period G),
      Fintype (AddAction.fixedBy (Periodic G a (period G)) j) :=
    fun _ => Fintype.ofFinite _
  let _ : Fintype (Quotient (AddAction.orbitRel (ZMod (period G))
      (Periodic G a (period G)))) := Fintype.ofFinite _
  have hB := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup (ZMod (period G))
    (Periodic G a (period G))
  rw [ZMod.card] at hB
  rw [powerMapComponents, Nat.card_congr (componentsEquivOrbits a), Nat.card_eq_fintype_card]
  convert hB.symm using 2 with j
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (fixedByEquiv a j)]

/-- `card_mul_totient` with the group order as a parameter. -/
theorem card_mul_totient' {N : ℕ} [NeZero N.totient] (hN : Nat.card G = N) :
    powerMapComponents G a * N.totient =
      ∑ j : ZMod N.totient,
        Nat.card {x : G // x ^ (a ^ (if j.val = 0 then N.totient else j.val)) = x} := by
  subst hN
  exact card_mul_totient a

end Components

/-! ### Comparison with the cyclic group -/

theorem card_zero_pow_fixed {L : Type*} [Group L] {m : ℕ} (hm : 1 ≤ m) :
    Nat.card {x : L // x ^ (0 ^ m) = x} = 1 := by
  rw [zero_pow (by omega)]
  simp only [pow_zero]
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun x y => Subtype.ext (x.2.symm.trans y.2)⟩, ⟨⟨1, rfl⟩⟩⟩

/-- `x^(aᵐ) = x ↔ x^(gcd(aᵐ - 1, |L|)) = 1`. -/
theorem card_fixed_eq_gcd {L : Type*} [Group L] [Finite L] {a m : ℕ} (ha : 0 < a) :
    Nat.card {x : L // x ^ (a ^ m) = x} =
      Nat.card {x : L // x ^ ((a ^ m - 1).gcd (Nat.card L)) = 1} := by
  have h1 : 1 ≤ a ^ m := Nat.one_le_pow _ _ ha
  rw [← card_pow_eq_one_gcd]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  conv_lhs => rw [← Nat.sub_add_cancel h1, pow_succ]
  exact mul_eq_right

/-- The number of solutions of `x^(aᵐ) = x`, `m ≥ 1`, in a group of order `n` is at least its
value in the cyclic group of order `n`. -/
theorem card_pow_pow_eq_le {H : Type*} [Group H] [Finite G] [Finite H] [IsCyclic H]
    (hcard : Nat.card H = Nat.card G) (a : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Nat.card {x : H // x ^ (a ^ m) = x} ≤ Nat.card {x : G // x ^ (a ^ m) = x} := by
  classical
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite H
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- `x ↦ 1`: the only fixed point is `1`
    rw [card_zero_pow_fixed hm, card_zero_pow_fixed hm]
  rw [card_fixed_eq_gcd ha, card_fixed_eq_gcd ha, hcard]
  set g := (a ^ m - 1).gcd (Nat.card G)
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ Nat.card_pos
  calc Nat.card {x : H // x ^ g = 1}
      ≤ g := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact IsCyclic.card_pow_eq_one_le hg0
    _ ≤ Nat.card {x : G // x ^ g = 1} :=
        Nat.le_of_dvd (Nat.card_pos_iff.mpr ⟨⟨⟨1, one_pow g⟩⟩, inferInstance⟩)
          (dvd_card_pow_eq_one (Nat.gcd_dvd_right _ _))

/-- **Larson's conjecture** (Integers 19 (2019) A58, Conjecture 1.2). For every finite group `G`
and every `a`, the graph of `x ↦ xᵃ` on `G` has at least as many connected components as on the
cyclic group of the same order. -/
theorem larson_conjecture {H : Type*} [Group H] [Finite G] [Finite H] [IsCyclic H]
    (hcard : Nat.card H = Nat.card G) (a : ℕ) :
    powerMapComponents H a ≤ powerMapComponents G a := by
  have hK : 0 < period G := Nat.totient_pos.mpr Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hK
  rw [card_mul_totient' (G := H) a hcard, card_mul_totient' (G := G) a rfl]
  refine sum_le_sum fun j _ => card_pow_pow_eq_le hcard a ?_
  split_ifs with h
  · exact hK
  · omega

/-- Larson's conjecture with `Cₙ = Multiplicative (ZMod n)`. -/
theorem powerMapComponents_zmod_le [Finite G] (a : ℕ) :
    powerMapComponents (Multiplicative (ZMod (Nat.card G))) a ≤ powerMapComponents G a := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  exact larson_conjecture (by simp [Nat.card_eq_fintype_card]) a

end PowerMapCycles
