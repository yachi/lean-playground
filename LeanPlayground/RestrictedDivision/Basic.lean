module

public import Mathlib.Tactic.Ring

public section

/-!
# Restricted and full division are equivalent over PA⁻

Formalization of Naoya Kato, "Equivalence of Restricted and Full Division",
<https://arxiv.org/abs/2610.24976> (October 2026).

Over PA⁻, the division principle restricted to co-prime pairs (`pa17⁻`) is
equivalent to full Euclidean division (`pa17`). This answers Visser's
Open Question 8.29 (From Numbers to Container Strings, arXiv:2411.15873).

We work semantically: `PAMinus M` says that `M` is a model of the axioms
pa1–pa13 and pa15 exactly as listed in the paper, and we prove the
equivalence in every such model. By Gödel's completeness theorem this is the
same as the paper's `PA⁻ ⊢ (pa17⁻ ↔ pa17)`. Corollary 5 (every extension of PA⁻ proves the
equivalence) is then immediate, since a model of an extension is a model of PA⁻.

## Main results

* Lemma 1 — `PAMinus.le_antisymm'`, `PAMinus.le_of_add_le_add_right`, `PAMinus.mul_zero'`,
  `PAMinus.zero_le'`, `PAMinus.lt_iff_add_one_le`, `PAMinus.pos_iff_ne_zero`.
* Theorem 2 — `PAMinus.euc_iff_euc_affine`. The paper's hypothesis `x ≠ 0` is not needed.
* Corollary 3 — `PAMinus.cop_sq`, `PAMinus.euc_iff_euc_sq`.
* Corollary 4 (main result) — `PAMinus.pa17Minus_iff_pa17`.
-/

/-- A model of PA⁻, with the axioms numbered as in Visser / the paper.
`<` is the paper's abbreviation `x < y :↔ x ≤ y ∧ x ≠ y`. -/
class PAMinus (M : Type*) extends Zero M, One M, Add M, Mul M, LE M, LT M where
  pa1 : ∀ x : M, x + 0 = x
  pa2 : ∀ x y : M, x + y = y + x
  pa3 : ∀ x y z : M, (x + y) + z = x + (y + z)
  pa4 : ∀ x : M, x * 1 = x
  pa5 : ∀ x y : M, x * y = y * x
  pa6 : ∀ x y z : M, (x * y) * z = x * (y * z)
  pa7 : ∀ x y z : M, x * (y + z) = x * y + x * z
  pa8 : ∀ x y : M, x ≤ y ∨ y ≤ x
  pa9 : ∀ x y z : M, x ≤ y → y ≤ z → x ≤ z
  pa10 : ∀ x : M, ¬ x + 1 ≤ x
  pa11 : ∀ x y : M, y ≤ x → y = x ∨ y + 1 ≤ x
  pa12 : ∀ x y z : M, y ≤ x → y + z ≤ x + z
  pa13 : ∀ x y z : M, y ≤ x → y * z ≤ x * z
  pa15 : ∀ x y : M, y ≤ x → ∃ z, x = y + z
  lt_iff_le_ne : ∀ x y : M, x < y ↔ x ≤ y ∧ x ≠ y

namespace PAMinus

variable {M : Type*} [PAMinus M]

/-! ### Lemma 1: basic consequences of PA⁻ -/

section Basic

variable {a b c : M}

theorem le_refl' (a : M) : a ≤ a := (pa8 a a).elim id id

theorem le_trans' : a ≤ b → b ≤ c → a ≤ c := pa9 a b c

theorem le_antisymm' (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  rcases pa11 b a h₁ with h | h
  · exact h
  · exact absurd (le_trans' h h₂) (pa10 a)

theorem add_one_add (b c : M) : (b + 1) + c = (b + c) + 1 := by
  rw [pa3, pa2 1 c, ← pa3]

/-- Lemma 1(1): cancellation of addition in inequalities. -/
theorem le_of_add_le_add_right (h : a + c ≤ b + c) : a ≤ b := by
  rcases pa8 a b with hab | hba
  · exact hab
  rcases pa11 a b hba with rfl | h'
  · exact le_refl' _
  have : (b + c) + 1 ≤ b + c := by
    rw [← add_one_add]; exact le_trans' (pa12 _ _ c h') h
  exact absurd this (pa10 _)

theorem add_right_cancel' (h : a + c = b + c) : a = b :=
  le_antisymm' (le_of_add_le_add_right (by rw [h]; exact le_refl' _))
    (le_of_add_le_add_right (by rw [h]; exact le_refl' _))

theorem zero_add' (a : M) : 0 + a = a := by rw [pa2, pa1]

/-- Lemma 1(2): `a * 0 = 0`. -/
theorem mul_zero' (a : M) : a * 0 = 0 := by
  apply add_right_cancel' (c := a * 0)
  rw [← pa7, pa1, zero_add']

theorem zero_mul' (a : M) : 0 * a = 0 := by rw [pa5, mul_zero']

theorem one_mul' (a : M) : 1 * a = a := by rw [pa5, pa4]

theorem zero_le_one' : (0 : M) ≤ 1 :=
  (pa8 0 1).resolve_right fun h => pa10 (0 : M) (by rwa [zero_add'])

theorem zero_ne_one' : (0 : M) ≠ 1 :=
  fun h => pa10 (0 : M) (by rw [zero_add', ← h]; exact le_refl' _)

/-- Lemma 1(2): `0 ≤ a`. If `a < 0` then `a + z = 0` for some `z ≥ 1`; multiplying
out `(a + z) * a` and `(a + z) * z` forces `z * z = 0`, contradicting `z ≥ 1`. -/
theorem zero_le' (a : M) : 0 ≤ a := by
  rcases pa8 0 a with h | ha
  · exact h
  obtain ⟨z, hz⟩ := pa15 0 a ha
  rcases pa11 0 a ha with rfl | ha1
  · exact le_refl' _
  -- `1 ≤ z`
  have hz1 : 1 ≤ z := by
    have := pa12 0 (a + 1) z ha1
    rwa [add_one_add, ← hz, zero_add', zero_add'] at this
  have hz0 : 0 ≤ z := le_trans' zero_le_one' hz1
  -- `a * z = 0`
  have haz : a * z = 0 := by
    apply le_antisymm'
    · simpa [zero_mul'] using pa13 0 a z ha
    · simpa [zero_mul', pa5 z a] using pa13 z 0 a hz0
  -- `z * z = 0`
  have hzz : z * z = 0 := by
    have : a * z + z * z = 0 := by rw [← zero_mul' z, hz, pa5 (a + z), pa7, pa5 z a]
    rwa [haz, zero_add'] at this
  have : z ≤ 0 := by simpa [one_mul', hzz] using pa13 z 1 z hz1
  exact absurd (le_antisymm' (le_trans' hz1 this) zero_le_one') zero_ne_one'.symm

/-- Lemma 1(3): `a < b ↔ a + 1 ≤ b`. -/
theorem lt_iff_add_one_le : a < b ↔ a + 1 ≤ b := by
  rw [lt_iff_le_ne]
  constructor
  · rintro ⟨h, hne⟩
    exact (pa11 b a h).resolve_left hne
  · intro h
    have ha : a ≤ a + 1 := by simpa [zero_add', pa2 1 a] using pa12 1 0 a zero_le_one'
    refine ⟨le_trans' ha h, ?_⟩
    rintro rfl
    exact pa10 a h

theorem le_of_lt' (h : a < b) : a ≤ b := ((lt_iff_le_ne a b).1 h).1

theorem not_le_of_lt (h : a < b) : ¬ b ≤ a :=
  fun h' => ((lt_iff_le_ne a b).1 h).2 (le_antisymm' (le_of_lt' h) h')

theorem lt_of_not_le (h : ¬ b ≤ a) : a < b :=
  (lt_iff_le_ne a b).2 ⟨(pa8 a b).resolve_right h, fun e => h (e ▸ le_refl' _)⟩

/-- Lemma 1(2): `a ≠ 0 ↔ 0 < a`. -/
theorem pos_iff_ne_zero : 0 < a ↔ a ≠ 0 := by
  rw [lt_iff_le_ne]
  exact ⟨fun h e => h.2 e.symm, fun h => ⟨zero_le' a, fun e => h e.symm⟩⟩

theorem le_add_right' (a b : M) : a ≤ a + b := by
  have := pa12 b 0 a (zero_le' b)
  rwa [zero_add', pa2 b a] at this

theorem lt_add_of_lt_of_le {d e : M} (h₁ : a < b) (h₂ : d ≤ e) : a + d < b + e := by
  rw [lt_iff_add_one_le] at h₁ ⊢
  rw [← add_one_add]
  exact le_trans' (pa12 _ _ d h₁) (by rw [pa2 b d, pa2 b e]; exact pa12 e d b h₂)

end Basic

/-- Every model of PA⁻ is a commutative semiring; this lets us use `ring`. -/
instance (priority := 100) toCommSemiring : CommSemiring M where
  add_assoc := pa3
  zero_add := zero_add'
  add_zero := pa1
  add_comm := pa2
  mul_assoc := pa6
  one_mul := one_mul'
  mul_one := pa4
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  left_distrib := pa7
  right_distrib a b c := by rw [pa5, pa7, pa5 c a, pa5 c b]
  mul_comm := pa5
  nsmul := nsmulRec

/-! ### The division principles -/

/-- `euc a b`: `b` can be divided by `a` with remainder. -/
def euc (a b : M) : Prop := ∃ q r, b = a * q + r ∧ r < a

/-- `cop a b`: `(a, b)` is a co-prime pair. -/
def cop (a b : M) : Prop := ∃ c d, a * d = b * c + 1

variable (M) in
/-- Restricted Euclidean division: division for co-prime pairs. -/
def pa17Minus : Prop := ∀ a b : M, cop a b → euc a b

variable (M) in
/-- Full Euclidean division. -/
def pa17 : Prop := ∀ a b : M, a ≠ 0 → euc a b

/-! ### Theorem 2: a quotient-preserving division transformation -/

/-- Theorem 2. The paper also assumes `x ≠ 0`, but the proof does not need it
(for `x = 0` both sides are false, since nothing is `< 0`). -/
theorem euc_iff_euc_affine {x y s t : M} (hst : s < t) :
    euc x y ↔ euc (t * x) (t * y + s) := by
  constructor
  · rintro ⟨q, r, rfl, hr⟩
    refine ⟨q, t * r + s, by ring, ?_⟩
    -- `t * r + s < t * r + t = t * (r + 1) ≤ t * x`
    have h₁ : t * r + s < t * r + t := by
      rw [pa2 (t * r) s, pa2 (t * r) t]; exact lt_add_of_lt_of_le hst (le_refl' _)
    have h₂ : t * (r + 1) ≤ t * x := by
      rw [pa5 t, pa5 t]; exact pa13 _ _ t (lt_iff_add_one_le.1 hr)
    rw [lt_iff_add_one_le] at h₁ ⊢
    exact le_trans' h₁ (by rw [pa7, pa4] at h₂; exact h₂)
  · rintro ⟨q, u, hu, hut⟩
    -- first, `x * q ≤ y`
    have hxq : x * q ≤ y := by
      by_contra hcon
      have h₁ := pa13 _ _ t (lt_iff_add_one_le.1 (lt_of_not_le hcon))
      -- `t * y + t ≤ t * x * q ≤ t * y + s`
      have h₂ : t * y + t ≤ t * y + s := by
        have e₁ : (y + 1) * t = t * y + t := by ring
        have e₂ : x * q * t = t * x * q := by ring
        rw [e₁, e₂] at h₁
        exact le_trans' h₁ (hu ▸ le_add_right' _ _)
      exact not_le_of_lt hst (le_of_add_le_add_right (by rwa [pa2 s, pa2 t]))
    obtain ⟨r, rfl⟩ := pa15 _ _ hxq
    refine ⟨q, r, rfl, lt_of_not_le fun hxr => ?_⟩
    -- comparing the two divisions gives `t * r + s = u`
    have hru : t * r + s = u := by
      apply add_right_cancel' (c := t * x * q)
      rw [pa2 u, ← hu]; ring
    apply not_le_of_lt hut
    rw [← hru]
    have h₁ := pa13 r x t hxr
    rw [pa5 x t, pa5 r t] at h₁
    exact le_trans' h₁ (le_add_right' _ _)

/-! ### Corollary 3: transfer to a co-prime pair -/

/-- If `1 < x` and `0 < y` then `(x², xy + 1)` is a co-prime pair:
writing `xy = z + 1`, we have `x²y² = (xy + 1)z + 1`. -/
theorem cop_sq {x y : M} (hx : 1 < x) (hy : 0 < y) : cop (x * x) (x * y + 1) := by
  have h1x : 1 ≤ x := le_of_lt' hx
  have h1y : 1 ≤ y := by have := lt_iff_add_one_le.1 hy; rwa [zero_add'] at this
  have hxy : 1 ≤ x * y := by
    have h₁ := pa13 y 1 x h1y
    rw [one_mul', pa5 y x] at h₁
    exact le_trans' h1x h₁
  obtain ⟨z, hz⟩ := pa15 _ _ hxy
  refine ⟨z, y * y, ?_⟩
  have : x * x * (y * y) = (x * y) * (x * y) := by ring
  rw [this, hz]
  ring

/-- Taking `t = x` and `s = 1` in Theorem 2. -/
theorem euc_iff_euc_sq {x y : M} (hx : 1 < x) : euc x y ↔ euc (x * x) (x * y + 1) :=
  euc_iff_euc_affine hx

/-! ### Corollary 4: the main theorem -/

/-- **Main theorem** (answers Visser's Open Question 8.29): over PA⁻, division for
co-prime pairs is equivalent to full Euclidean division. -/
theorem pa17Minus_iff_pa17 : pa17Minus M ↔ pa17 M := by
  constructor
  · intro h x y hx
    have hx0 : 0 < x := pos_iff_ne_zero.2 hx
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, 0, by rw [mul_zero', pa1], hx0⟩
    rcases eq_or_ne x 1 with rfl | hx1
    · exact ⟨y, 0, by rw [pa1, one_mul'], hx0⟩
    have h1x : 1 < x := by
      refine (lt_iff_le_ne 1 x).2 ⟨?_, hx1.symm⟩
      have := lt_iff_add_one_le.1 hx0
      rwa [zero_add'] at this
    exact (euc_iff_euc_sq h1x).2 (h _ _ (cop_sq h1x (pos_iff_ne_zero.2 hy)))
  · rintro h a b ⟨c, d, hcd⟩
    refine h a b fun ha => pa10 (b * c) ?_
    rw [← hcd, ha, zero_mul']
    exact zero_le' _

/-! ### Sanity check: the axioms are satisfiable, e.g. by `ℕ` -/

example : PAMinus ℕ where
  pa1 := Nat.add_zero
  pa2 := Nat.add_comm
  pa3 := Nat.add_assoc
  pa4 := Nat.mul_one
  pa5 := Nat.mul_comm
  pa6 := Nat.mul_assoc
  pa7 := Nat.mul_add
  pa8 := Nat.le_total
  pa9 _ _ _ := Nat.le_trans
  pa10 _ := by omega
  pa11 _ _ h := by omega
  pa12 _ _ _ h := by omega
  pa13 _ _ z h := Nat.mul_le_mul_right z h
  pa15 x y h := ⟨x - y, by omega⟩
  lt_iff_le_ne _ _ := by omega

end PAMinus
