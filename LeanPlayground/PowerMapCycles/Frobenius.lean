module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Frobenius' theorem on the equation `xⁿ = 1`

**Theorem** (Frobenius, 1895). If `G` is a finite group and `n ∣ |G|`, then `n` divides the number
of solutions of `xⁿ = 1` in `G`.

The proof follows the classical route (compare I. M. Isaacs and G. R. Robinson, *On a theorem of
Frobenius: solutions of xⁿ = 1 in finite groups*, Amer. Math. Monthly 99 (1992)):

* `card_pow_mul_eq_sum`: for coprime `r, s`, every solution of `x^(rs) = 1` splits uniquely as
  `x = u * v` with `v^s = 1`, `u^r = 1` and `u` commuting with `v`. So
  `#{x^(rs) = 1} = ∑_{v^s = 1} #{u ∈ C(v) : u^r = 1}`.
* `sum_modEq_sum_center`: a class function `f` with `m ∣ |G : C(x)| · f x` for every noncentral
  `x` has `∑ f ≡ ∑_{Z(G)} f (mod m)`, by summing over conjugacy classes.
* `prime_pow_dvd_card_pow_eq_one`: the prime power case, by strong induction on `|G|`. For the
  full `p`-part `pᴱ` of `|G| = pᴱ m`, split `|G| = #{x^(pᴱ m) = 1}` as above with `r = pᴱ`,
  `s = m`. Noncentral `v` contribute multiples of `pᴱ` by induction in `C(v)`, and the central
  ones contribute `#{v ∈ Z(G) : v^m = 1} · #{x^(pᴱ) = 1}`, whose first factor is prime to `p`.
  Smaller powers follow because the elements of order exactly `p^(a+1)` come in blocks of
  `φ(p^(a+1))`, the generators of one cyclic subgroup (`totient_dvd_card_orderOf_eq`).
* `dvd_card_pow_eq_one`: the general case, one prime at a time, by the same splitting.
-/

open Finset

namespace PowerMapCycles

variable {G : Type*} [Group G]

/-! ### Splitting along coprime exponents -/

section Split

variable [Fintype G] [DecidableEq G]

/-- For coprime `r, s`, the solutions of `x^(r*s) = 1` correspond to pairs `(v, u)` with `v^s = 1`,
`u^r = 1` and `u` commuting with `v` (via `x = u * v`). -/
theorem card_pow_mul_eq_sum {r s : ℕ} (hrs : Nat.Coprime r s) :
    #{x : G | x ^ (r * s) = 1} =
      ∑ v ∈ ({v : G | v ^ s = 1} : Finset G), #{u : G | u * v = v * u ∧ u ^ r = 1} := by
  set A := Nat.gcdA r s
  set B := Nat.gcdB r s
  have hAB : (r : ℤ) * A + s * B = 1 := by
    have := Nat.gcd_eq_gcd_ab r s
    rw [hrs.gcd_eq_one] at this
    push_cast at this
    linarith
  -- powers of an element killed by `r * s`
  have hzr : ∀ x : G, x ^ (r * s) = 1 → ∀ k : ℤ, x ^ ((r : ℤ) * s * k) = 1 := by
    intro x hx k
    rw [zpow_mul, show ((r : ℤ) * s) = ((r * s : ℕ) : ℤ) by push_cast; ring, zpow_natCast, hx,
      one_zpow]
  rw [← card_sigma]
  refine card_bij' (fun x _ => ⟨x ^ ((r : ℤ) * A), x ^ ((s : ℤ) * B)⟩) (fun p _ => p.2 * p.1)
    ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    simp only [mem_sigma, mem_filter, mem_univ, true_and]
    refine ⟨?_, ((Commute.refl x).zpow_zpow _ _ :), ?_⟩
    · rw [← zpow_natCast, ← zpow_mul, show (r : ℤ) * A * s = r * s * A by ring]
      exact hzr x hx A
    · rw [← zpow_natCast, ← zpow_mul, show (s : ℤ) * B * r = r * s * B by ring]
      exact hzr x hx B
  · rintro ⟨v, u⟩ hp
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at hp
    obtain ⟨hv, huv, hu⟩ := hp
    replace huv : Commute u v := huv
    simp only [mem_filter, mem_univ, true_and]
    rw [huv.mul_pow, pow_mul, hu, one_pow, one_mul, pow_mul' v r s, hv, one_pow]
  · intro x _
    rw [← zpow_add, show (s : ℤ) * B + r * A = 1 by linarith, zpow_one]
  · rintro ⟨v, u⟩ hp
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at hp
    obtain ⟨hv, huv, hu⟩ := hp
    replace huv : Commute u v := huv
    have hv' : ∀ k : ℤ, v ^ ((s : ℤ) * k) = 1 := fun k => by
      rw [zpow_mul, zpow_natCast, hv, one_zpow]
    have hu' : ∀ k : ℤ, u ^ ((r : ℤ) * k) = 1 := fun k => by
      rw [zpow_mul, zpow_natCast, hu, one_zpow]
    simp only [Sigma.mk.injEq, heq_eq_eq]
    constructor
    · rw [huv.mul_zpow, hu', one_mul, show (r : ℤ) * A = 1 - s * B by linarith, zpow_sub,
        zpow_one, hv', inv_one, mul_one]
    · rw [huv.mul_zpow, hv', mul_one, show (s : ℤ) * B = 1 - r * A by linarith, zpow_sub,
        zpow_one, hu', inv_one, mul_one]

end Split

/-! ### Summing a class function over conjugacy classes -/

section ClassSum

variable [Fintype G] [DecidableEq G]

/-- If `f` is constant on conjugacy classes and `m ∣ |G : C(x)| · f x` for every noncentral `x`,
then `∑ₓ f x ≡ ∑_{x ∈ Z(G)} f x (mod m)`. -/
theorem sum_modEq_sum_center (f : G → ℕ) (hf : ∀ g x : G, f (g * x * g⁻¹) = f x) (m : ℕ)
    (h : ∀ x : G, x ∉ Subgroup.center G → m ∣ (Subgroup.centralizer {x}).index * f x) :
    ∑ x, f x ≡ ∑ x ∈ ({x : G | x ∈ Subgroup.center G} : Finset G), f x [MOD m] := by
  rw [← sum_filter_add_sum_filter_not univ (fun x => x ∈ Subgroup.center G)]
  conv_rhs => rw [← add_zero (∑ x ∈ _, f x)]
  refine Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr ?_)
  set s : Finset G := {x : G | x ∉ Subgroup.center G}
  rw [← sum_fiberwise_of_maps_to (g := fun x => ConjClasses.mk x) (t := s.image ConjClasses.mk)
    (fun x hx => mem_image_of_mem _ hx)]
  refine dvd_sum fun c hc => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hc
  have hx₀' : x₀ ∉ Subgroup.center G := by simpa [s] using hx₀
  -- the fibre is the conjugacy class of `x₀`
  have hfib : ({x ∈ s | ConjClasses.mk x = ConjClasses.mk x₀} : Finset G) =
      (conjugatesOf x₀).toFinset := by
    ext x
    rw [Set.mem_toFinset]
    change _ ↔ IsConj x₀ x
    simp only [mem_filter, ConjClasses.mk_eq_mk_iff_isConj, s, mem_univ, true_and]
    constructor
    · rintro ⟨-, hx⟩; exact hx.symm
    · intro hx
      refine ⟨fun hxc => hx₀' ?_, hx.symm⟩
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      have hcx : c * x = x * c := Subgroup.mem_center_iff.mp hxc c
      have : x₀ = x := by
        calc x₀ = c⁻¹ * (c * x₀ * c⁻¹) * c := by group
          _ = c⁻¹ * x * c := by rw [hc]
          _ = x := by rw [mul_assoc, ← hcx, inv_mul_cancel_left]
      rwa [this]
  rw [hfib]
  have hconst : ∀ x ∈ (conjugatesOf x₀).toFinset, f x = f x₀ := by
    intro x hx
    rw [Set.mem_toFinset] at hx
    obtain ⟨c, hc⟩ := isConj_iff.mp hx
    rw [← hc, hf]
  rw [sum_congr rfl hconst, sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card',
    ← Subgroup.index_centralizer_eq_ncard]
  exact h x₀ hx₀'

end ClassSum

/-! ### Elements of a given order -/

section OrderCount

variable [Fintype G]

/-- The elements of order `d` come in blocks of `φ(d)`: the generators of one cyclic subgroup. -/
theorem totient_dvd_card_orderOf_eq (d : ℕ) : d.totient ∣ #{x : G | orderOf x = d} := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun x => Subgroup.zpowers x)
    (t := (({x : G | orderOf x = d} : Finset G).image fun x => Subgroup.zpowers x))
    (fun x hx => mem_image_of_mem _ hx)]
  refine dvd_sum fun H hH => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hH
  simp only [mem_filter, mem_univ, true_and] at hx₀
  have hcard : Nat.card (Subgroup.zpowers x₀) = d := by rw [Nat.card_zpowers, hx₀]
  have key : #{x ∈ ({x : G | orderOf x = d} : Finset G) | Subgroup.zpowers x = Subgroup.zpowers x₀}
      = #{y : Subgroup.zpowers x₀ | orderOf y = d} := by
    symm
    refine card_bij (fun y _ => (y : G)) ?_ (fun _ _ _ _ h => Subtype.ext h) ?_
    · intro y hy
      simp only [mem_filter, mem_univ, true_and, Subgroup.orderOf_coe] at hy ⊢
      refine ⟨hy, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
      · rw [Subgroup.zpowers_le]; exact y.2
      · rw [hcard, Nat.card_zpowers, Subgroup.orderOf_coe, hy]
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      refine ⟨⟨x, hx.2 ▸ Subgroup.mem_zpowers x⟩, ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and, Subgroup.orderOf_mk, hx.1]
  rw [key, IsCyclic.card_orderOf_eq_totient]
  rw [← Nat.card_eq_fintype_card, hcard]

end OrderCount

/-! ### The prime-power case -/

section Centralizer

/-- Counting inside a centralizer. -/
theorem card_centralizer_pow_eq_one [Fintype G] [DecidableEq G] (v : G) (r : ℕ) :
    #{u : G | u * v = v * u ∧ u ^ r = 1} =
      Nat.card {u : Subgroup.centralizer {v} // u ^ r = 1} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  symm
  refine card_bij (fun y _ => (y : G)) ?_ (fun _ _ _ _ h => Subtype.ext h) ?_
  · intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mp y.2, by
      rw [← Subgroup.coe_pow, hy, Subgroup.coe_one]⟩
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    refine ⟨⟨x, Subgroup.mem_centralizer_singleton_iff.mpr hx.1⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    exact Subtype.ext (by simpa using hx.2)

/-- Inside a finite group `H`, `u^k = 1` iff `u^(gcd k |H|) = 1`. -/
theorem card_pow_eq_one_gcd {H : Type*} [Group H] [Finite H] (k : ℕ) :
    Nat.card {u : H // u ^ k = 1} = Nat.card {u : H // u ^ (k.gcd (Nat.card H)) = 1} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
  rw [pow_gcd_eq_one]
  exact ⟨fun h => ⟨h, pow_card_eq_one'⟩, fun h => h.1⟩

/-- If `gcd(k, |H|)` divides `#{u ∈ H : u^k = 1}` and `k ∣ |G|`, then `k` divides
`|G : H| · #{u ∈ H : u^k = 1}`. -/
theorem dvd_index_mul [Finite G] (H : Subgroup G) {k : ℕ} (hk : k ∣ Nat.card G)
    (hH : k.gcd (Nat.card H) ∣ Nat.card {u : H // u ^ k = 1}) :
    k ∣ H.index * Nat.card {u : H // u ^ k = 1} := by
  refine dvd_trans ?_ (mul_dvd_mul_left H.index hH)
  rw [← Nat.gcd_mul_left, H.index_mul_card]
  exact Nat.dvd_gcd (dvd_mul_left _ _) hk

end Centralizer

section Split

variable [Fintype G] [DecidableEq G]

/-- The splitting `x = u * v`, summed over conjugacy classes. -/
theorem card_pow_mul_modEq {r s M : ℕ} (hrs : Nat.Coprime r s)
    (h : ∀ v : G, v ∉ Subgroup.center G → v ^ s = 1 →
      M ∣ (Subgroup.centralizer {v}).index * #{u : G | u * v = v * u ∧ u ^ r = 1}) :
    #{x : G | x ^ (r * s) = 1} ≡
      #{v : G | v ∈ Subgroup.center G ∧ v ^ s = 1} * #{x : G | x ^ r = 1} [MOD M] := by
  classical
  set f : G → ℕ := fun v => if v ^ s = 1 then #{u : G | u * v = v * u ∧ u ^ r = 1} else 0
  have hsum : #{x : G | x ^ (r * s) = 1} = ∑ v, f v := by
    rw [card_pow_mul_eq_sum hrs, sum_filter]
  have hf : ∀ g v : G, f (g * v * g⁻¹) = f v := by
    intro g v
    simp only [f, conj_pow, conj_eq_one_iff]
    split_ifs with hv
    · refine card_bij' (fun u _ => g⁻¹ * u * g) (fun u _ => g * u * g⁻¹) ?_ ?_ ?_ ?_
      · intro u hu
        simp only [mem_filter, mem_univ, true_and] at hu ⊢
        refine ⟨?_, ?_⟩
        · calc g⁻¹ * u * g * v = g⁻¹ * (u * (g * v * g⁻¹)) * g := by group
            _ = g⁻¹ * ((g * v * g⁻¹) * u) * g := by rw [hu.1]
            _ = v * (g⁻¹ * u * g) := by group
        · have := conj_pow (a := g⁻¹) (b := u) (i := r)
          rw [inv_inv] at this
          rw [this, hu.2]; group
      · intro u hu
        simp only [mem_filter, mem_univ, true_and] at hu ⊢
        refine ⟨?_, ?_⟩
        · calc g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
            _ = g * (v * u) * g⁻¹ := by rw [hu.1]
            _ = g * v * g⁻¹ * (g * u * g⁻¹) := by group
        · rw [conj_pow, hu.2]; group
      · intro u _; group
      · intro u _; group
    · rfl
  rw [hsum]
  refine (sum_modEq_sum_center f hf M fun v hv => ?_).trans ?_
  · simp only [f]
    split_ifs with hvs
    · exact h v hv hvs
    · simp
  · have : ∀ v ∈ ({v : G | v ∈ Subgroup.center G} : Finset G),
        f v = if v ^ s = 1 then #{x : G | x ^ r = 1} else 0 := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv
      simp only [f]
      congr 2
      ext u
      simp [Subgroup.mem_center_iff.mp hv u]
    rw [sum_congr rfl this, sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul,
      filter_filter]

end Split

/-- The central `s`-torsion has order prime to every prime `p ∤ s`. -/
theorem not_dvd_card_center_pow_eq_one [Fintype G] [DecidableEq G] {p s : ℕ} (hp : p.Prime)
    (hps : ¬ p ∣ s) : ¬ p ∣ #{v : G | v ∈ Subgroup.center G ∧ v ^ s = 1} := by
  intro hdvd
  let K : Subgroup G :=
    { carrier := {v | v ∈ Subgroup.center G ∧ v ^ s = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        have hab : Commute a b := (Subgroup.mem_center_iff.mp ha b).symm
        rw [hab.mul_pow, ha', hb', one_mul]
      one_mem' := ⟨Subgroup.one_mem _, one_pow _⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨Subgroup.inv_mem _ ha, by rw [inv_pow, ha', inv_one]⟩ }
  have hK : Nat.card K = #{v : G | v ∈ Subgroup.center G ∧ v ^ s = 1} := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) p (hK ▸ hdvd)
  apply hps
  rw [← hx, ← Subgroup.orderOf_coe]
  exact orderOf_dvd_of_pow_eq_one x.2.2

/-- **Frobenius' theorem, prime-power case.** If `pᵉ ∣ |G|` then `pᵉ ∣ #{x : x^(pᵉ) = 1}`. -/
theorem prime_pow_dvd_card_pow_eq_one {p : ℕ} (hp : p.Prime) :
    ∀ (n : ℕ) (G : Type*) [Group G] [Finite G], Nat.card G = n → ∀ e : ℕ, p ^ e ∣ Nat.card G →
      p ^ e ∣ Nat.card {x : G // x ^ (p ^ e) = 1} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro G _ _ hGn e he
  classical
  let _ := Fintype.ofFinite G
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  set E := (Nat.card G).factorization p
  set m := ordCompl[p] (Nat.card G)
  have hGE : p ^ E * m = Nat.card G := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : Nat.Coprime (p ^ E) m := (Nat.coprime_ordCompl hp hG0).pow_left E
  have hpm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_ordCompl hp hG0)
  have hcount : ∀ k : ℕ, Nat.card {x : G // x ^ k = 1} = #{x : G | x ^ k = 1} := fun k => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Step 1: the full `p`-part.
  have step1 : p ^ E ∣ #{x : G | x ^ (p ^ E) = 1} := by
    have hmod := card_pow_mul_modEq (G := G) (M := p ^ E) hcop (by
      intro v hv _
      rw [card_centralizer_pow_eq_one]
      set C := Subgroup.centralizer {v}
      refine dvd_index_mul C (Dvd.intro m hGE) ?_
      have hlt : Nat.card C < Nat.card G := by
        rw [← Subgroup.card_top (G := G)]
        refine Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr fun htop => hv ?_)
        rw [Subgroup.mem_center_iff]
        intro g
        have : g ∈ C := htop ▸ Subgroup.mem_top g
        exact Subgroup.mem_centralizer_singleton_iff.mp this
      obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p ^ E) (Nat.card C))
      rw [card_pow_eq_one_gcd, hf]
      refine IH _ (hGn ▸ hlt) C rfl f ?_
      rw [← hf]; exact Nat.gcd_dvd_right _ _)
    have hall : #{x : G | x ^ (p ^ E * m) = 1} = Nat.card G := by
      rw [hGE, filter_true_of_mem fun x _ => pow_card_eq_one', card_univ, Nat.card_eq_fintype_card]
    rw [hall] at hmod
    have h1 : p ^ E ∣ #{v : G | v ∈ Subgroup.center G ∧ v ^ m = 1} * #{x : G | x ^ (p ^ E) = 1} :=
      Nat.modEq_zero_iff_dvd.mp
        ((Nat.modEq_zero_iff_dvd.mpr (Dvd.intro m hGE)).symm.trans hmod).symm
    refine (Nat.Coprime.dvd_of_dvd_mul_left ?_ h1)
    exact Nat.Coprime.pow_left E ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (not_dvd_card_center_pow_eq_one hp hpm))
  -- Step 2: descend from `pᴱ`.
  have hsplit : ∀ a : ℕ, #{x : G | x ^ (p ^ (a + 1)) = 1} =
      #{x : G | x ^ (p ^ a) = 1} + #{x : G | orderOf x = p ^ (a + 1)} := by
    intro a
    rw [← card_union_of_disjoint]
    · congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · intro hx
        obtain ⟨j, hj, hxj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hx)
        rcases Nat.lt_or_ge j (a + 1) with hja | hja
        · left
          rw [← orderOf_dvd_iff_pow_eq_one, hxj]
          exact Nat.pow_dvd_pow p (by omega)
        · right; rw [hxj, show j = a + 1 by omega]
      · rintro (hx | hx)
        · rw [pow_succ, pow_mul, hx, one_pow]
        · rw [← hx]; exact pow_orderOf_eq_one x
    · rw [disjoint_filter]
      intro x _ hx hxo
      have := orderOf_dvd_of_pow_eq_one hx
      rw [hxo, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at this
      omega
  have step2 : ∀ i ≤ E, p ^ (E - i) ∣ #{x : G | x ^ (p ^ (E - i)) = 1} := by
    intro i
    induction i with
    | zero => intro; simpa using step1
    | succ i ih =>
      intro hi
      have h := ih (by omega)
      obtain ⟨a, ha⟩ : ∃ a, E - i = a + 1 := ⟨E - i - 1, by omega⟩
      rw [show E - (i + 1) = a by omega]
      rw [ha, hsplit a] at h
      have hφ : p ^ a ∣ #{x : G | orderOf x = p ^ (a + 1)} := by
        refine dvd_trans ?_ (totient_dvd_card_orderOf_eq _)
        rw [Nat.totient_prime_pow_succ hp]
        exact dvd_mul_right _ _
      exact (Nat.dvd_add_left hφ).mp (dvd_trans (Nat.pow_dvd_pow p (Nat.le_succ a)) h)
  have heE : e ≤ E := (hp.pow_dvd_iff_le_factorization hG0).mp he
  have := step2 (E - e) (Nat.sub_le _ _)
  rw [show E - (E - e) = e by omega] at this
  rwa [hcount]

/-- **Frobenius' theorem** (1895). If `n` divides the order of a finite group `G`, then `n` divides
the number of solutions of `xⁿ = 1` in `G`. -/
theorem dvd_card_pow_eq_one [Finite G] {n : ℕ} (hn : n ∣ Nat.card G) :
    n ∣ Nat.card {x : G // x ^ n = 1} := by
  classical
  let _ := Fintype.ofFinite G
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hn0 : n ≠ 0 := by rintro rfl; exact hG0 (zero_dvd_iff.mp hn)
  have hX0 : Nat.card {x : G // x ^ n = 1} ≠ 0 :=
    (Nat.card_pos_iff.mpr ⟨⟨⟨1, one_pow n⟩⟩, inferInstance⟩).ne'
  refine (Nat.factorization_prime_le_iff_dvd hn0 hX0).mp fun p hp => ?_
  rw [← hp.pow_dvd_iff_le_factorization hX0]
  set b := n.factorization p
  set q := ordCompl[p] n
  have hnb : p ^ b * q = n := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : Nat.Coprime (p ^ b) q := (Nat.coprime_ordCompl hp hn0).pow_left b
  have hbG : p ^ b ∣ Nat.card G := dvd_trans (Dvd.intro q hnb) hn
  have hmod := card_pow_mul_modEq (G := G) (M := p ^ b) hcop (by
    intro v _ _
    rw [card_centralizer_pow_eq_one]
    set C := Subgroup.centralizer {v}
    refine dvd_index_mul C hbG ?_
    obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p ^ b) (Nat.card C))
    rw [card_pow_eq_one_gcd, hf]
    refine prime_pow_dvd_card_pow_eq_one hp _ C rfl f ?_
    rw [← hf]; exact Nat.gcd_dvd_right _ _)
  rw [hnb] at hmod
  have hcard : Nat.card {x : G // x ^ n = 1} = #{x : G | x ^ n = 1} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  refine (Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr ?_)))
  refine dvd_mul_of_dvd_right ?_ _
  have := prime_pow_dvd_card_pow_eq_one hp _ G rfl b hbG
  rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this

end PowerMapCycles
