module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Tactic

@[expose] public section

/-!
# Minimum covers of LCM `p`-groups need not be LCM, for every odd prime `p`

A finite group `G` is an *LCM-group* (M.-S. Lazorec, *On some problems regarding LCM-groups*,
arXiv:2602.06228, 2026) if `o(xⁿ y)` divides `lcm(o(xⁿ), o(y))` for all `x, y ∈ G` and `n ∈ ℕ`.
For a set `𝓕` of finite groups, `G` is an *`𝓕`-cover* if every member of `𝓕` embeds in `G`,
and a *minimum* `𝓕`-cover if no `𝓕`-cover has smaller order. Lazorec shows that for
`𝓕ₖ = {Q₈, C_{2^{k-1}}}` all minimum covers are non-LCM, and asks (Question 4.5):

> Let `p` be an odd prime. Can one find infinitely many sets `𝓕` of LCM-`p`-groups such that all
> their minimum `𝓕`-covers are non-LCM-`p`-groups?

(He gives one example for `p = 3`: `𝓕 = {3^{1+2}₊, C₉²}`.) We answer **yes, for every odd prime
`p`**. Let `Hₚ = 𝔽ₚ² ⋊ Cₚ` be the Heisenberg group of order `p³` (exponent `p`) and
`Aₖ = (ℤ/pᵏ)^p`, and put `𝓕ₖ = {Hₚ, Aₖ}` for `k ≥ 2`.

* Both members are LCM-groups (`isLCMGroup_heis`, `isLCMGroup_A`).
* The regular wreath product `Gₖ = C_{pᵏ} ≀ Cₚ = Aₖ ⋊ Cₚ` (cyclic shift) is an `𝓕ₖ`-cover of
  order `p^{pk+1}` (`covers_W`, `card_W`).
* Every `𝓕ₖ`-cover has order at least `p^{pk+1}` (`card_ge_of_covers`, a Sylow argument).
* No `𝓕ₖ`-cover of order `p^{pk+1}` is an LCM-group (`not_isLCMGroup_of_covers`).

So the minimum `𝓕ₖ`-covers are exactly the `𝓕ₖ`-covers of order `p^{pk+1}`, and none is an
LCM-group (`answer_question_4_5`).

The heart is `commute_of_exp_p`: in a group where the elements of order dividing `p` are closed
under multiplication (true in LCM-groups), let `A` be an abelian normal subgroup of index `p` in
which every element of order `p` is a `p`-th power. Then every subgroup `E` of exponent `p` is
abelian. Indeed, for `h ∈ E \ A` and `b ∈ A`, the commutator `h⁻¹ b⁻¹ h b` is a product of two
elements of order `p`, so has order `p`; hence `h` moves `b` by an element of order `p`, and so
fixes `bᵖ`, i.e. it centralises the elements of order `p` of `A`, which contain `E ∩ A`; finally
`E = ⟨h⟩(E ∩ A)`. In a cover of order `p^{pk+1}` the copy of `Aₖ` has index `p`, while the copy
of `Hₚ` is a non-abelian subgroup of exponent `p`.
-/

namespace LCMCover

open Function Multiplicative

/-! ### LCM-groups -/

/-- Lazorec's LCM property: `o(xⁿ y) ∣ lcm(o(xⁿ), o(y))` for all `x, y, n`. -/
def IsLCMGroup (G : Type*) [Group G] : Prop :=
  ∀ (x y : G) (n : ℕ), orderOf (x ^ n * y) ∣ Nat.lcm (orderOf (x ^ n)) (orderOf y)

/-- In an LCM-group the elements `x` with `xᵖ = 1` are closed under multiplication. -/
theorem IsLCMGroup.pow_mul_eq_one {G : Type*} [Group G] (hG : IsLCMGroup G) {p : ℕ} {x y : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) : (x * y) ^ p = 1 := by
  have h := hG x y 1
  rw [pow_one] at h
  exact orderOf_dvd_iff_pow_eq_one.1 (h.trans (Nat.lcm_dvd (orderOf_dvd_of_pow_eq_one hx)
    (orderOf_dvd_of_pow_eq_one hy)))

/-- Abelian groups are LCM-groups. -/
theorem isLCMGroup_of_commGroup (G : Type*) [CommGroup G] : IsLCMGroup G :=
  fun x y n => (Commute.all (x ^ n) y).orderOf_mul_dvd_lcm

/-- Groups of exponent `p` (prime) are LCM-groups. -/
theorem isLCMGroup_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (h : ∀ x : G, x ^ p = 1) : IsLCMGroup G := by
  intro x y n
  have hdvd : ∀ z : G, orderOf z = 1 ∨ orderOf z = p := fun z =>
    (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (h z))
  rcases hdvd (x ^ n) with h1 | h1
  · rw [orderOf_eq_one_iff] at h1
    rw [h1, one_mul, orderOf_one, Nat.lcm_one_left]
  · rw [h1]
    exact (orderOf_dvd_of_pow_eq_one (h _)).trans (Nat.dvd_lcm_left _ _)

/-! ### The key lemma -/

/-- **Key lemma.** Suppose the elements `x` with `xᵖ = 1` are closed under multiplication, and
let `A` be an abelian normal subgroup of prime index `p` in which every element of order dividing
`p` is a `p`-th power. Then every subgroup of exponent dividing `p` is abelian. -/
theorem commute_of_exp_p {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]
    (hΩ : ∀ x y : G, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1)
    (A : Subgroup G) [hAn : A.Normal] (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hroot : ∀ a ∈ A, a ^ p = 1 → ∃ b ∈ A, b ^ p = a) (hidx : A.index = p)
    (E : Subgroup G) (hE : ∀ e ∈ E, e ^ p = 1) :
    ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := by
  by_cases hEA : E ≤ A
  · intro e he f hf
    exact hAc e (hEA he) f (hEA hf)
  obtain ⟨h, hhE, hhA⟩ := Set.not_subset.1 hEA
  have hhp : h ^ p = 1 := hE h hhE
  -- Step 1: `h` centralises the elements of order dividing `p` of `A`.
  have step1 : ∀ a ∈ A, a ^ p = 1 → Commute h a := by
    intro a ha hap
    obtain ⟨b, hb, rfl⟩ := hroot a ha hap
    set c := h⁻¹ * b⁻¹ * h * b with hc
    have hcA : c ∈ A := by
      have h1 : h⁻¹ * b⁻¹ * h⁻¹⁻¹ ∈ A := hAn.conj_mem b⁻¹ (inv_mem hb) h⁻¹
      rw [inv_inv] at h1
      exact mul_mem h1 hb
    have hcp : c ^ p = 1 := by
      have e1 : c = h⁻¹ * (b⁻¹ * h * b⁻¹⁻¹) := by rw [hc, inv_inv]; group
      rw [e1]
      apply hΩ
      · rw [inv_pow, hhp, inv_one]
      · rw [conj_pow, hhp]; group
    have e2 : h⁻¹ * b * h⁻¹⁻¹ = b * c⁻¹ := by rw [hc, inv_inv]; group
    have hbc : Commute b c⁻¹ := hAc b hb c⁻¹ (inv_mem hcA)
    have e3 : h⁻¹ * b ^ p * h⁻¹⁻¹ = b ^ p := by
      rw [← conj_pow, e2, hbc.mul_pow, inv_pow, hcp, inv_one, mul_one]
    rw [inv_inv] at e3
    show h * b ^ p = b ^ p * h
    calc h * b ^ p = h * (h⁻¹ * b ^ p * h) := by rw [e3]
      _ = b ^ p * h := by group
  -- Step 2: every element is `hⁱ a` with `a ∈ A`.
  have step2 : ∀ g : G, ∃ i : ℤ, (h ^ i)⁻¹ * g ∈ A := by
    intro g
    have hcard : Nat.card (G ⧸ A) = p := hidx
    have hne : (h : G ⧸ A) ≠ 1 := by
      rwa [Ne, QuotientGroup.eq_one_iff]
    have htop := zpowers_eq_top_of_prime_card hcard hne
    have hg : (g : G ⧸ A) ∈ Subgroup.zpowers (h : G ⧸ A) := by rw [htop]; trivial
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨i, ?_⟩
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hi]
  -- Step 3: conclude.
  have decomp : ∀ e ∈ E, ∃ i : ℤ, ∃ a, a ∈ A ∧ Commute h a ∧ e = h ^ i * a := by
    intro e he
    obtain ⟨i, hi⟩ := step2 e
    refine ⟨i, (h ^ i)⁻¹ * e, hi, step1 _ hi (hE _ ?_), by group⟩
    exact mul_mem (inv_mem (zpow_mem hhE i)) he
  intro e he f hf
  obtain ⟨i, a, ha, hca, rfl⟩ := decomp e he
  obtain ⟨j, b, hb, hcb, rfl⟩ := decomp f hf
  have hab : Commute a b := hAc a ha b hb
  have hc : Commute (h ^ i * a) (h ^ j * b) := by
    refine Commute.mul_right (Commute.mul_left ?_ ?_) (Commute.mul_left ?_ hab)
    · exact Commute.zpow_zpow_self h i j
    · exact (hca.symm.zpow_right j)
    · exact hcb.zpow_left i
  exact hc

/-! ### The groups -/

variable (p : ℕ) [hp : Fact p.Prime]

/-- The action of `Cₚ` on `𝔽ₚ²` by the unipotent matrices `(x, y) ↦ (x - i y, y)`. -/
def heisAct : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod p × ZMod p)) where
  toFun i :=
    { toFun := fun v => ofAdd ((toAdd v).1 - toAdd i * (toAdd v).2, (toAdd v).2)
      invFun := fun v => ofAdd ((toAdd v).1 + toAdd i * (toAdd v).2, (toAdd v).2)
      left_inv := fun v => by simp
      right_inv := fun v => by simp
      map_mul' := fun v w => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
        rw [← ofAdd_add]
        congr 1
        ext <;> simp
        ring }
  map_one' := by
    ext v : 1
    simp
  map_mul' i j := by
    ext v : 1
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply, toAdd_ofAdd, toAdd_mul]
    congr 1
    ext <;> simp
    ring

/-- The Heisenberg group `Hₚ = 𝔽ₚ² ⋊ Cₚ` of order `p³` (for odd `p`, the extraspecial group of
exponent `p`). -/
abbrev Heis : Type := Multiplicative (ZMod p × ZMod p) ⋊[heisAct p] Multiplicative (ZMod p)

variable (k : ℕ)

/-- The homocyclic abelian group `Aₖ = (ℤ/pᵏ)^p`, written multiplicatively. -/
abbrev A : Type := Multiplicative (ZMod p → ZMod (p ^ k))

/-- The cyclic shift action of `Cₚ` on `Aₖ`: `(i • f)(j) = f(j - i)`. -/
def shift : Multiplicative (ZMod p) →* MulAut (A p k) where
  toFun i :=
    { toFun := fun f => ofAdd (fun j => toAdd f (j - toAdd i))
      invFun := fun f => ofAdd (fun j => toAdd f (j + toAdd i))
      left_inv := fun f => by simp
      right_inv := fun f => by simp
      map_mul' := fun f g => rfl }
  map_one' := by
    ext f : 1
    simp
  map_mul' i j := by
    ext f : 1
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply, toAdd_ofAdd, toAdd_mul]
    congr 1
    ext l
    rw [sub_sub]

/-- The regular wreath product `Wₖ = C_{pᵏ} ≀ Cₚ = Aₖ ⋊ Cₚ`, of order `p^{pk+1}`. -/
abbrev W : Type := A p k ⋊[shift p k] Multiplicative (ZMod p)

/-- The members of `𝓕ₖ = {Hₚ, Aₖ}`. `G` is an `𝓕ₖ`-cover if both embed in `G`. -/
def Covers (G : Type*) [Group G] : Prop :=
  (∃ f : Heis p →* G, Injective f) ∧ (∃ f : A p k →* G, Injective f)

/-! ### The members of `𝓕ₖ` are LCM-groups -/

/-- Multiplication in `Hₚ`, in coordinates. -/
theorem heis_mul (x y : Heis p) : x * y =
    ⟨ofAdd ((toAdd x.left).1 + (toAdd y.left).1 - toAdd x.right * (toAdd y.left).2,
      (toAdd x.left).2 + (toAdd y.left).2), x.right * y.right⟩ := by
  apply SemidirectProduct.ext
  · rw [SemidirectProduct.mul_left]
    apply toAdd.injective
    ext <;> simp [heisAct]
    ring
  · rfl

/-- `n`-th powers in `Hₚ`, in coordinates. -/
theorem heis_pow (x : Heis p) (n : ℕ) :
    x ^ n = ⟨ofAdd ((n : ZMod p) * (toAdd x.left).1 -
      ((n.choose 2 : ℕ) : ZMod p) * toAdd x.right * (toAdd x.left).2,
      (n : ZMod p) * (toAdd x.left).2), x.right ^ n⟩ := by
  induction n with
  | zero =>
    apply SemidirectProduct.ext <;> simp
    rfl
  | succ n ih =>
    rw [pow_succ, ih, heis_mul]
    apply SemidirectProduct.ext
    · apply toAdd.injective
      simp only [toAdd_ofAdd, toAdd_pow, nsmul_eq_mul, Nat.cast_succ, Nat.choose_succ_succ',
        Nat.choose_one_right, Nat.cast_add]
      ext <;> simp <;> ring
    · simp [pow_succ]

/-- For odd `p`, the group `Hₚ` has exponent `p`. -/
theorem heis_pow_p (hp2 : p ≠ 2) (x : Heis p) : x ^ p = 1 := by
  rw [heis_pow]
  have hch : ((p.choose 2 : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.Prime.dvd_choose_self hp.out (by norm_num)
      (lt_of_le_of_ne hp.out.two_le (Ne.symm hp2))
  ext
  · simp [hch]
  · simp
  · simp only [SemidirectProduct.one_right]
    rw [← ofAdd_toAdd x.right, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      ofAdd_zero]

theorem isLCMGroup_heis (hp2 : p ≠ 2) : IsLCMGroup (Heis p) :=
  isLCMGroup_of_pow_eq_one hp.out (heis_pow_p p hp2)

omit hp in
theorem isLCMGroup_A : IsLCMGroup (A p k) := isLCMGroup_of_commGroup _

/-- `Hₚ` is not abelian. -/
theorem heis_not_comm : (⟨1, ofAdd 1⟩ : Heis p) * ⟨ofAdd (0, 1), 1⟩ ≠
    ⟨ofAdd (0, 1), 1⟩ * ⟨1, ofAdd 1⟩ := by
  intro h
  rw [heis_mul, heis_mul] at h
  have h1 := congrArg (fun z : Heis p => (toAdd z.left).1) h
  simp at h1

/-! ### The wreath product `Wₖ` is an `𝓕ₖ`-cover of order `p^{pk+1}` -/

instance : NeZero p := ⟨hp.out.ne_zero⟩

instance : Finite (W p k) := Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem card_A : Nat.card (A p k) = p ^ (p * k) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
    ZMod.card, ← pow_mul, mul_comm]

theorem card_W : Nat.card (W p k) = p ^ (p * k + 1) := by
  rw [SemidirectProduct.card, card_A, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    ZMod.card, pow_succ]

/-- `x ↦ p^{k-1} x`, the embedding `ℤ/p → ℤ/pᵏ`. -/
def scale : ZMod p →+ ZMod (p ^ k) :=
  ZMod.lift p ⟨zmultiplesHom _ ((p : ZMod (p ^ k)) ^ (k - 1)), by
    simp only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul]
    exact_mod_cast (ZMod.natCast_eq_zero_iff (p * p ^ (k - 1)) (p ^ k)).2
      (by rcases k with _ | k <;> simp [pow_succ'])⟩

theorem scale_natCast (n : ℕ) : scale p k (n : ZMod p) = n * (p : ZMod (p ^ k)) ^ (k - 1) := by
  have : ((n : ℤ) : ZMod p) = (n : ZMod p) := by simp
  rw [← this, scale, ZMod.lift_coe]
  simp

theorem scale_injective (hk : 1 ≤ k) : Injective (scale p k) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← ZMod.natCast_zmod_val x, scale_natCast] at hx
  rw [← ZMod.natCast_zmod_val x, ZMod.natCast_eq_zero_iff]
  have h1 : ((x.val * p ^ (k - 1) : ℕ) : ZMod (p ^ k)) = 0 := by exact_mod_cast hx
  rw [ZMod.natCast_eq_zero_iff] at h1
  have h2 : p ^ (k - 1) * p ∣ p ^ (k - 1) * x.val := by
    rw [← pow_succ, Nat.sub_add_cancel hk, mul_comm]; exact h1
  exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos _) h2

/-- `(x, y) ↦ (j ↦ p^{k-1}(x + y j))`, which intertwines the two `Cₚ`-actions. -/
def emb : Multiplicative (ZMod p × ZMod p) →* A p k :=
  AddMonoidHom.toMultiplicative
    { toFun := fun v j => scale p k (v.1 + v.2 * j)
      map_zero' := by ext; simp
      map_add' := fun v w => by
        ext j
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ← map_add]
        congr 1
        ring }

theorem emb_injective (hk : 1 ≤ k) : Injective (emb p k) := by
  intro v w h
  have h0 := congrFun (congrArg toAdd h) 0
  have h1 := congrFun (congrArg toAdd h) 1
  simp only [emb, AddMonoidHom.toMultiplicative_apply_apply, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, mul_zero, add_zero, mul_one, toAdd_ofAdd] at h0 h1
  have e0 := scale_injective p k hk h0
  have e1 := scale_injective p k hk h1
  rw [e0, add_right_inj] at e1
  rw [← ofAdd_toAdd v, ← ofAdd_toAdd w]
  congr 1
  exact Prod.ext e0 e1

/-- The embedding `Hₚ → Wₖ`. -/
def heisEmb : Heis p →* W p k :=
  SemidirectProduct.map (emb p k) (MonoidHom.id _) (fun i => by
    refine MonoidHom.ext fun v => ?_
    apply toAdd.injective
    funext j
    change scale p k (((toAdd v).1 - toAdd i * (toAdd v).2) + (toAdd v).2 * j) =
      scale p k ((toAdd v).1 + (toAdd v).2 * (j - toAdd i))
    congr 1
    ring)

theorem covers_W (hk : 1 ≤ k) : Covers p k (W p k) := by
  refine ⟨⟨heisEmb p k, ?_⟩, ⟨SemidirectProduct.inl, SemidirectProduct.inl_injective⟩⟩
  intro x y h
  have h1 := congrArg SemidirectProduct.left h
  have h2 := congrArg SemidirectProduct.right h
  simp only [heisEmb, SemidirectProduct.map_left, SemidirectProduct.map_right,
    MonoidHom.id_apply] at h1 h2
  exact SemidirectProduct.ext (emb_injective p k hk h1) h2

/-! ### Lower bound for covers -/

/-- **Every `𝓕ₖ`-cover has order at least `p^{pk+1}`**: if `|G| < p^{pk+1}`, the copy of `Aₖ`
is a Sylow `p`-subgroup, so every Sylow `p`-subgroup is abelian, but one of them contains the
non-abelian group `Hₚ`. -/
theorem card_ge_of_covers (G : Type*) [Group G] [Finite G] (hG : Covers p k G) :
    p ^ (p * k + 1) ≤ Nat.card G := by
  obtain ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ := hG
  by_contra hlt
  push Not at hlt
  set B : Subgroup G := g.range
  have hB : Nat.card B = p ^ (p * k) := by
    rw [← card_A p k]
    exact Nat.card_congr (MonoidHom.ofInjective hg).toEquiv.symm
  have hdvd : p ^ (p * k) ∣ Nat.card G := hB ▸ Subgroup.card_subgroup_dvd_card B
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
  have hmp : m < p := by
    by_contra h
    push Not at h
    have : p ^ (p * k + 1) ≤ Nat.card G := by
      rw [hm, pow_succ]; exact Nat.mul_le_mul_left _ h
    omega
  have hndvd : ¬ p ∣ m := fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h) (by omega)
  have hfac : (Nat.card G).factorization p = p * k := by
    rw [hm, Nat.factorization_mul (pow_pos hp.out.pos _).ne' hm0, Finsupp.add_apply,
      hp.out.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]
  -- `B` is a Sylow subgroup
  have hBp : IsPGroup p B := IsPGroup.of_card hB
  obtain ⟨Q, hQ⟩ := hBp.exists_le_sylow
  have hQB : (Q : Subgroup G) = B := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hQ
    rw [Q.card_eq_multiplicity, hfac, hB]
  -- the image of `Hₚ` lies in a Sylow subgroup
  set E : Subgroup G := f.range
  have hEp : IsPGroup p E := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, SemidirectProduct.card,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      Fintype.card_multiplicative, Fintype.card_prod, ZMod.card]
    ring
  obtain ⟨P, hP⟩ := hEp.exists_le_sylow
  -- all Sylow subgroups are isomorphic, and `B` is abelian
  have hPcomm : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x := by
    intro x hx y hy
    let e : (P : Subgroup G) ≃* (Q : Subgroup G) := Sylow.equiv P Q
    have hQc : ∀ u v : (Q : Subgroup G), u * v = v * u := by
      intro u v
      have hu : (u : G) ∈ B := hQB ▸ u.2
      have hv : (v : G) ∈ B := hQB ▸ v.2
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      apply Subtype.ext
      simp only [Subgroup.coe_mul, ← ha, ← hb, ← map_mul, mul_comm a b]
    have := hQc (e ⟨x, hx⟩) (e ⟨y, hy⟩)
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (e.injective this)
  apply heis_not_comm p
  apply hf
  rw [map_mul, map_mul]
  exact hPcomm _ (hP ⟨_, rfl⟩) _ (hP ⟨_, rfl⟩)

/-! ### Covers of order `p^{pk+1}` are not LCM-groups -/

/-- In `Aₖ` with `k ≥ 2`, every element of order dividing `p` is a `p`-th power. -/
theorem A_root (hk : 2 ≤ k) (a : A p k) (ha : a ^ p = 1) : ∃ b : A p k, b ^ p = a := by
  have hz : ∀ z : ZMod (p ^ k), (p : ZMod (p ^ k)) * z = 0 → ∃ w, (p : ZMod (p ^ k)) * w = z := by
    intro z hz
    rw [← ZMod.natCast_zmod_val z] at hz ⊢
    have h1 : ((p * z.val : ℕ) : ZMod (p ^ k)) = 0 := by exact_mod_cast hz
    rw [ZMod.natCast_eq_zero_iff] at h1
    have h2 : p * p ^ (k - 1) ∣ p * z.val := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega)]; exact h1
    obtain ⟨t, ht⟩ := Nat.dvd_of_mul_dvd_mul_left hp.out.pos h2
    refine ⟨((p ^ (k - 2) * t : ℕ) : ZMod (p ^ k)), ?_⟩
    rw [ht]
    push_cast
    rw [← mul_assoc, ← pow_succ', show k - 2 + 1 = k - 1 by omega]
  choose w hw using hz
  refine ⟨ofAdd (fun j => w (toAdd a j) ?_), ?_⟩
  · have := congrFun (congrArg toAdd ha) j
    simpa [toAdd_pow, nsmul_eq_mul] using this
  · apply toAdd.injective
    ext j
    simp only [toAdd_pow, toAdd_ofAdd, Pi.smul_apply, nsmul_eq_mul]
    exact hw _ _

/-- **No `𝓕ₖ`-cover of order `p^{pk+1}` is an LCM-group** (`p` odd, `k ≥ 2`). -/
theorem not_isLCMGroup_of_covers (hp2 : p ≠ 2) (hk : 2 ≤ k) (G : Type*) [Group G] [Finite G]
    (hG : Covers p k G) (hcard : Nat.card G = p ^ (p * k + 1)) : ¬ IsLCMGroup G := by
  intro hL
  obtain ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ := hG
  set B : Subgroup G := g.range
  have hB : Nat.card B = p ^ (p * k) := by
    rw [← card_A p k]
    exact Nat.card_congr (MonoidHom.ofInjective hg).toEquiv.symm
  have hidx : B.index = p := by
    have := B.index_mul_card
    rw [hB, hcard, pow_succ, mul_comm] at this
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) this
  have hminFac : (Nat.card G).minFac = p := by
    rw [hcard, Nat.Prime.pow_minFac hp.out (by omega)]
  have : B.Normal := Subgroup.normal_of_index_eq_minFac_card (hidx.trans hminFac.symm)
  have key := commute_of_exp_p (p := p) (fun x y hx hy => hL.pow_mul_eq_one hx hy) B
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; rw [← map_mul, ← map_mul, mul_comm])
    (by
      rintro _ ⟨a, rfl⟩ ha
      rw [← map_pow] at ha
      obtain ⟨b, hb⟩ := A_root p k hk a (hg (ha.trans (map_one g).symm))
      exact ⟨g b, ⟨b, rfl⟩, by rw [← map_pow, hb]⟩)
    hidx f.range (by rintro _ ⟨x, rfl⟩; rw [← map_pow, heis_pow_p p hp2, map_one])
  apply heis_not_comm p
  apply hf
  rw [map_mul, map_mul]
  exact key _ ⟨_, rfl⟩ _ ⟨_, rfl⟩

/-- In particular the wreath product `Wₖ` is not an LCM-group. -/
theorem not_isLCMGroup_W (hp2 : p ≠ 2) (hk : 2 ≤ k) : ¬ IsLCMGroup (W p k) :=
  not_isLCMGroup_of_covers p k hp2 hk _ (covers_W p k (by omega)) (card_W p k)

/-! ### The answer to Lazorec, Question 4.5 -/

/-- `G` is a minimum `𝓕ₖ`-cover (among finite groups in the same universe). -/
def IsMinimumCover (G : Type) [Group G] [Finite G] : Prop :=
  Covers p k G ∧ ∀ (H : Type) [Group H] [Finite H], Covers p k H → Nat.card G ≤ Nat.card H

/-- **Answer to Lazorec's Question 4.5.** Let `p` be an odd prime. For every `k ≥ 2` the set
`𝓕ₖ = {Hₚ, (ℤ/pᵏ)^p}` consists of LCM-`p`-groups, has a minimum cover (of order `p^{pk+1}`),
and no minimum `𝓕ₖ`-cover is an LCM-group. The sets `𝓕ₖ` are pairwise different since
`|Aₖ| = p^{pk}` (`card_A`), so there are infinitely many of them. -/
theorem answer_question_4_5 (hp2 : p ≠ 2) (hk : 2 ≤ k) :
    IsLCMGroup (Heis p) ∧ IsLCMGroup (A p k) ∧ IsMinimumCover p k (W p k) ∧
      ∀ (G : Type) [Group G] [Finite G], IsMinimumCover p k G → ¬ IsLCMGroup G := by
  refine ⟨isLCMGroup_heis p hp2, isLCMGroup_A p k,
    ⟨covers_W p k (by omega), fun H _ _ hH => card_W p k ▸ card_ge_of_covers p k H hH⟩, ?_⟩
  intro G _ _ ⟨hG, hmin⟩
  refine not_isLCMGroup_of_covers p k hp2 hk G hG (le_antisymm ?_ (card_ge_of_covers p k G hG))
  exact card_W p k ▸ hmin (W p k) (covers_W p k (by omega))

end LCMCover
