module

public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Generalized Diophantine tuples over `ℤ`: `M_k(n) ≤ 4` under Lander–Parkin–Selfridge

A set `A` of positive integers has *property `D_k(n)`* if `ab + n` is the `k`-th power of a
nonnegative integer for all distinct `a, b ∈ A`.

K. M. Tsang and C. H. Yip, *An absolute bound for generalized Diophantine tuples over polynomial
rings* (arXiv:2607.01165, Theorem 2.2), prove that the Lander–Parkin–Selfridge conjecture implies
`|A| ≤ 5` for all `k ≥ 7` and `n ≠ 0`. Their proof takes six elements `a₁, a₂, a₃, b₁, b₂, b₃`,
expands `det (aᵢ bⱼ + n) = 0` and gets an equal sum of at most six `k`-th powers.

**New here.** Five elements suffice. For `a₁, a₂, b₁, b₂, b₃ ∈ A` the three vectors
`(1, 1, 1)`, `(a₁ bⱼ + n)ⱼ`, `(a₂ bⱼ + n)ⱼ` lie in the span of `(1, 1, 1)` and `(bⱼ)ⱼ`, so the
`3 × 3` determinant with an all-ones first row vanishes. Its six terms are again `k`-th powers
(`1 = 1ᵏ`), every term on one side differs from every term on the other side, and some term is
positive. So the same Lander–Parkin–Selfridge argument gives `|A| ≤ 4`
(`card_le_four_of_landerParkinSelfridge`).

Write `Xᵢⱼ = aᵢ bⱼ + n = xᵢⱼᵏ`. The identity is
`X₁₁X₂₂ + X₁₂X₂₃ + X₁₃X₂₁ = X₁₁X₂₃ + X₁₂X₂₁ + X₁₃X₂₂`, and each of the nine differences
"left term minus right term" factors as a product of nonzero numbers, for example
`X₁₁X₂₂ − X₁₂X₂₁ = n (a₁ − a₂)(b₁ − b₂)` and `X₁₁X₂₂ − X₁₁X₂₃ = X₁₁ a₂ (b₂ − b₃)`.
-/

namespace DiophantineTuples

open Multiset

/-- The Lander–Parkin–Selfridge conjecture for exponent `k`: a nontrivial equal sum of like powers
`∑ xᵢᵏ = ∑ yⱼᵏ` in positive integers with no base on both sides has at least `k` terms. -/
def LanderParkinSelfridge (k : ℕ) : Prop :=
  ∀ S T : Multiset ℕ, S ≠ 0 → T ≠ 0 → (∀ x ∈ S, 0 < x) → (∀ x ∈ T, 0 < x) →
    (∀ x ∈ S, x ∉ T) → (S.map (· ^ k)).sum = (T.map (· ^ k)).sum → k ≤ card S + card T

/-- `A` has property `D_k(n)`: `ab + n` is the `k`-th power of a natural number for distinct
`a, b ∈ A`. -/
def HasPropertyD (k : ℕ) (n : ℤ) (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ x : ℕ, (x : ℤ) ^ k = a * b + n

lemma sum_map_pow_filter_pos {k : ℕ} (hk : 0 < k) (M : Multiset ℕ) :
    ((M.filter (0 < ·)).map (· ^ k)).sum = (M.map (· ^ k)).sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    by_cases ha : 0 < a
    · simp [Multiset.filter_cons_of_pos _ ha, ih]
    · have : a = 0 := by omega
      subst this
      simp [Multiset.filter_cons_of_neg _ ha, ih, zero_pow hk.ne']

/-- If `x ^ k = y ^ k` with `x * ... = y * ...` coming from integers whose `k`-th powers are the
products `P` and `Q`, then `P = Q`. -/
lemma pow_eq_of_eq {k : ℕ} {x y : ℕ} {P Q : ℤ} (hx : ((x : ℤ)) ^ k = P) (hy : ((y : ℤ)) ^ k = Q)
    (h : x = y) : P = Q := by
  subst h; rw [← hx, ← hy]

/-- **Five-element core.** Five integers `a₁, a₂, b₁, b₂, b₃` with `a₁, a₂ ≠ 0`, `a₁ ≠ a₂`,
pairwise distinct `bⱼ`, and every `aᵢ bⱼ + n` a `k`-th power, force `k ≤ 6` under
Lander–Parkin–Selfridge. -/
theorem le_six_of_five {k : ℕ} (hLPS : LanderParkinSelfridge k) (hk : 0 < k) {n : ℤ}
    (hn : n ≠ 0) {a₁ a₂ b₁ b₂ b₃ : ℤ} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha : a₁ ≠ a₂)
    (hb₁₂ : b₁ ≠ b₂) (hb₁₃ : b₁ ≠ b₃) (hb₂₃ : b₂ ≠ b₃)
    {x₁₁ x₁₂ x₁₃ x₂₁ x₂₂ x₂₃ : ℕ}
    (h₁₁ : (x₁₁ : ℤ) ^ k = a₁ * b₁ + n) (h₁₂ : (x₁₂ : ℤ) ^ k = a₁ * b₂ + n)
    (h₁₃ : (x₁₃ : ℤ) ^ k = a₁ * b₃ + n) (h₂₁ : (x₂₁ : ℤ) ^ k = a₂ * b₁ + n)
    (h₂₂ : (x₂₂ : ℤ) ^ k = a₂ * b₂ + n) (h₂₃ : (x₂₃ : ℤ) ^ k = a₂ * b₃ + n) : k ≤ 6 := by
  have hk0 : k ≠ 0 := hk.ne'
  -- a `k`-th power vanishes iff its base does
  have hz : ∀ {x : ℕ} {P : ℤ}, (x : ℤ) ^ k = P → (x = 0 ↔ P = 0) := by
    intro x P hx
    rw [← hx]
    constructor
    · rintro rfl; simp [hk0]
    · intro h; exact_mod_cast pow_eq_zero_iff hk0 |>.mp h
  have sub_ne : ∀ {x y : ℤ}, x ≠ y → x - y ≠ 0 := fun h => sub_ne_zero.mpr h
  -- the six terms
  set e₁ := x₁₁ * x₂₂; set e₂ := x₁₂ * x₂₃; set e₃ := x₁₃ * x₂₁
  set o₁ := x₁₁ * x₂₃; set o₂ := x₁₂ * x₂₁; set o₃ := x₁₃ * x₂₂
  have hsum : e₁ ^ k + e₂ ^ k + e₃ ^ k = o₁ ^ k + o₂ ^ k + o₃ ^ k := by
    have : ((e₁ ^ k + e₂ ^ k + e₃ ^ k : ℕ) : ℤ) = ((o₁ ^ k + o₂ ^ k + o₃ ^ k : ℕ) : ℤ) := by
      push_cast [e₁, e₂, e₃, o₁, o₂, o₃]
      simp only [mul_pow, h₁₁, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃]
      ring
    exact_mod_cast this
  -- an equality between a left and a right term is impossible
  have hne : ∀ {e o : ℕ}, 0 < e → e = o → (e = e₁ ∨ e = e₂ ∨ e = e₃) →
      (o = o₁ ∨ o = o₂ ∨ o = o₃) → False := by
    intro e o he heo hE hO
    subst heo
    have pos : ∀ {x y : ℕ}, 0 < x * y → x ≠ 0 ∧ y ≠ 0 := fun h =>
      ⟨fun hx => by simp [hx] at h, fun hy => by simp [hy] at h⟩
    have key : ∀ {x y z w : ℕ} {P Q R S : ℤ}, (x : ℤ) ^ k = P → (y : ℤ) ^ k = Q →
        (z : ℤ) ^ k = R → (w : ℤ) ^ k = S → x * y = z * w → P * Q = R * S := by
      intro x y z w P Q R S hx hy hz' hw h
      rw [← hx, ← hy, ← hz', ← hw, ← mul_pow, ← mul_pow]
      exact_mod_cast congrArg (· ^ k) h
    rcases hE with rfl | rfl | rfl <;> rcases hO with h | h | h
    -- e₁ = o₁ : X₁₁ (X₂₂ - X₂₃) = X₁₁ a₂ (b₂ - b₃)
    · have := key h₁₁ h₂₂ h₁₁ h₂₃ h
      obtain ⟨h1, -⟩ := pos he
      have h1' : a₁ * b₁ + n ≠ 0 := fun h0 => h1 ((hz h₁₁).mpr h0)
      apply mul_ne_zero (mul_ne_zero h1' ha₂) (sub_ne hb₂₃)
      linear_combination this
    -- e₁ = o₂ : n (a₁ - a₂)(b₁ - b₂)
    · have := key h₁₁ h₂₂ h₁₂ h₂₁ h
      apply mul_ne_zero (mul_ne_zero hn (sub_ne ha)) (sub_ne hb₁₂)
      linear_combination this
    -- e₁ = o₃ : X₂₂ a₁ (b₁ - b₃)
    · have := key h₁₁ h₂₂ h₁₃ h₂₂ h
      obtain ⟨-, h2⟩ := pos he
      have h2' : a₂ * b₂ + n ≠ 0 := fun h0 => h2 ((hz h₂₂).mpr h0)
      apply mul_ne_zero (mul_ne_zero h2' ha₁) (sub_ne hb₁₃)
      linear_combination this
    -- e₂ = o₁ : X₂₃ a₁ (b₂ - b₁)
    · have := key h₁₂ h₂₃ h₁₁ h₂₃ h
      obtain ⟨-, h2⟩ := pos he
      have h2' : a₂ * b₃ + n ≠ 0 := fun h0 => h2 ((hz h₂₃).mpr h0)
      apply mul_ne_zero (mul_ne_zero h2' ha₁) (sub_ne hb₁₂.symm)
      linear_combination this
    -- e₂ = o₂ : X₁₂ a₂ (b₃ - b₁)
    · have := key h₁₂ h₂₃ h₁₂ h₂₁ h
      obtain ⟨h1, -⟩ := pos he
      have h1' : a₁ * b₂ + n ≠ 0 := fun h0 => h1 ((hz h₁₂).mpr h0)
      apply mul_ne_zero (mul_ne_zero h1' ha₂) (sub_ne hb₁₃.symm)
      linear_combination this
    -- e₂ = o₃ : n (a₁ - a₂)(b₂ - b₃)
    · have := key h₁₂ h₂₃ h₁₃ h₂₂ h
      apply mul_ne_zero (mul_ne_zero hn (sub_ne ha)) (sub_ne hb₂₃)
      linear_combination this
    -- e₃ = o₁ : n (a₁ - a₂)(b₃ - b₁)
    · have := key h₁₃ h₂₁ h₁₁ h₂₃ h
      apply mul_ne_zero (mul_ne_zero hn (sub_ne ha)) (sub_ne hb₁₃.symm)
      linear_combination this
    -- e₃ = o₂ : X₂₁ a₁ (b₃ - b₂)
    · have := key h₁₃ h₂₁ h₁₂ h₂₁ h
      obtain ⟨-, h2⟩ := pos he
      have h2' : a₂ * b₁ + n ≠ 0 := fun h0 => h2 ((hz h₂₁).mpr h0)
      apply mul_ne_zero (mul_ne_zero h2' ha₁) (sub_ne hb₂₃.symm)
      linear_combination this
    -- e₃ = o₃ : X₁₃ a₂ (b₁ - b₂)
    · have := key h₁₃ h₂₁ h₁₃ h₂₂ h
      obtain ⟨h1, -⟩ := pos he
      have h1' : a₁ * b₃ + n ≠ 0 := fun h0 => h1 ((hz h₁₃).mpr h0)
      apply mul_ne_zero (mul_ne_zero h1' ha₂) (sub_ne hb₁₂)
      linear_combination this
  -- at most one zero in each row
  have row₁ : ∀ {x y : ℕ} {b b' : ℤ}, b ≠ b' → (x : ℤ) ^ k = a₁ * b + n →
      (y : ℤ) ^ k = a₁ * b' + n → x = 0 → y = 0 → False := by
    intro x y b b' hbb hx hy h0 h0'
    have e1 := (hz hx).mp h0; have e2 := (hz hy).mp h0'
    exact mul_ne_zero ha₁ (sub_ne hbb) (by linear_combination e1 - e2)
  have row₂ : ∀ {x y : ℕ} {b b' : ℤ}, b ≠ b' → (x : ℤ) ^ k = a₂ * b + n →
      (y : ℤ) ^ k = a₂ * b' + n → x = 0 → y = 0 → False := by
    intro x y b b' hbb hx hy h0 h0'
    have e1 := (hz hx).mp h0; have e2 := (hz hy).mp h0'
    exact mul_ne_zero ha₂ (sub_ne hbb) (by linear_combination e1 - e2)
  -- some term is positive
  have hpos : 0 < e₁ ^ k + e₂ ^ k + e₃ ^ k := by
    by_contra hcon
    have h0 : e₁ ^ k + e₂ ^ k + e₃ ^ k = 0 := by omega
    have h0' : o₁ ^ k + o₂ ^ k + o₃ ^ k = 0 := hsum ▸ h0
    simp only [Nat.add_eq_zero_iff, pow_eq_zero_iff hk0, e₁, e₂, e₃, o₁, o₂, o₃,
      mul_eq_zero] at h0 h0'
    obtain ⟨⟨E1, E2⟩, E3⟩ := h0
    obtain ⟨⟨O1, O2⟩, O3⟩ := h0'
    by_cases z₁₁ : x₁₁ = 0
    · by_cases z₁₂ : x₁₂ = 0
      · exact row₁ hb₁₂ h₁₁ h₁₂ z₁₁ z₁₂
      · have : x₂₃ = 0 := E2.resolve_left z₁₂
        have : x₂₁ = 0 := O2.resolve_left z₁₂
        exact row₂ hb₁₃ h₂₁ h₂₃ ‹_› ‹_›
    · exact row₂ hb₂₃ h₂₂ h₂₃ (E1.resolve_left z₁₁) (O1.resolve_left z₁₁)
  -- apply Lander–Parkin–Selfridge to the positive terms
  set S : Multiset ℕ := ({e₁, e₂, e₃} : Multiset ℕ).filter (0 < ·)
  set T : Multiset ℕ := ({o₁, o₂, o₃} : Multiset ℕ).filter (0 < ·)
  have hS : (S.map (· ^ k)).sum = e₁ ^ k + e₂ ^ k + e₃ ^ k := by
    rw [sum_map_pow_filter_pos hk]; simp [add_assoc]
  have hT : (T.map (· ^ k)).sum = o₁ ^ k + o₂ ^ k + o₃ ^ k := by
    rw [sum_map_pow_filter_pos hk]; simp [add_assoc]
  have hS0 : S ≠ 0 := by
    intro h; rw [h] at hS; simp at hS; omega
  have hT0 : T ≠ 0 := by
    intro h; rw [h] at hT; simp at hT; omega
  have hdisj : ∀ x ∈ S, x ∉ T := by
    intro x hxS hxT
    simp only [S, T, Multiset.mem_filter, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hxS hxT
    exact hne hxS.2 rfl hxS.1 hxT.1
  have hle := hLPS S T hS0 hT0 (fun x hx => (Multiset.mem_filter.mp hx).2)
    (fun x hx => (Multiset.mem_filter.mp hx).2) hdisj (by rw [hS, hT, hsum])
  have hcS : card S ≤ 3 := (Multiset.card_le_card (Multiset.filter_le _ _)).trans (by simp)
  have hcT : card T ≤ 3 := (Multiset.card_le_card (Multiset.filter_le _ _)).trans (by simp)
  omega

/-- **Theorem.** Assume the Lander–Parkin–Selfridge conjecture for exponent `k ≥ 7`. Then every
set of positive integers with property `D_k(n)`, `n ≠ 0`, has at most four elements.
(Tsang–Yip, Theorem 2.2, prove `≤ 5`.) -/
theorem card_le_four_of_landerParkinSelfridge {k : ℕ} (hLPS : LanderParkinSelfridge k)
    (hk : 7 ≤ k) {n : ℤ} (hn : n ≠ 0) {A : Finset ℤ} (hApos : ∀ a ∈ A, 0 < a)
    (hA : HasPropertyD k n A) : A.card ≤ 4 := by
  by_contra hcard
  rw [not_le] at hcard
  obtain ⟨t, htA, htc⟩ := Finset.exists_subset_card_eq (show 5 ≤ A.card by omega)
  obtain ⟨a₁, t₁, ha₁, rfl, ht₁⟩ := Finset.card_eq_succ.mp htc
  obtain ⟨a₂, t₂, ha₂, rfl, ht₂⟩ := Finset.card_eq_succ.mp ht₁
  obtain ⟨b₁, t₃, hb₁, rfl, ht₃⟩ := Finset.card_eq_succ.mp ht₂
  obtain ⟨b₂, b₃, hb₂₃, rfl⟩ := Finset.card_eq_two.mp ht₃
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha₁ ha₂ hb₁
  have mem : ∀ x, x = a₁ ∨ x = a₂ ∨ x = b₁ ∨ x = b₂ ∨ x = b₃ → x ∈ A := by
    intro x hx
    apply htA
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have get : ∀ {a b : ℤ}, a ∈ A → b ∈ A → a ≠ b → ∃ x : ℕ, (x : ℤ) ^ k = a * b + n :=
    fun ha hb hab => hA _ ha _ hb hab
  have A1 := mem a₁ (by tauto); have A2 := mem a₂ (by tauto)
  have B1 := mem b₁ (by tauto); have B2 := mem b₂ (by tauto); have B3 := mem b₃ (by tauto)
  obtain ⟨x₁₁, h₁₁⟩ := get A1 B1 ha₁.2.1
  obtain ⟨x₁₂, h₁₂⟩ := get A1 B2 ha₁.2.2.1
  obtain ⟨x₁₃, h₁₃⟩ := get A1 B3 ha₁.2.2.2
  obtain ⟨x₂₁, h₂₁⟩ := get A2 B1 ha₂.1
  obtain ⟨x₂₂, h₂₂⟩ := get A2 B2 ha₂.2.1
  obtain ⟨x₂₃, h₂₃⟩ := get A2 B3 ha₂.2.2
  have := le_six_of_five hLPS (by omega) hn (hApos _ A1).ne' (hApos _ A2).ne' ha₁.1
    hb₁.1 hb₁.2 hb₂₃ h₁₁ h₁₂ h₁₃ h₂₁ h₂₂ h₂₃
  omega

end DiophantineTuples
