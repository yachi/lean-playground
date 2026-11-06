module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Polynomial `D_k(n)`-tuples have at most four elements

Let `F` be a field, `k ≥ 1` and `n ∈ F[X]`, `n ≠ 0`. A finite set `A ⊆ F[X]` has *property
`D_k(n)`* if `ab + n` is a `k`-th power in `F[X]` for all distinct `a, b ∈ A`.

K. M. Tsang and C. H. Yip, *An absolute bound for generalized Diophantine tuples over polynomial
rings* (arXiv:2607.01165, Theorem 1.1), prove for `F` algebraically closed of characteristic `0`
and `k ≥ 18` that `|A| ≤ 6`, unless `n = s²` is a `k`-th power and `A ⊆ s F` (an infinite family).
Their proof expands `det (aᵢ bⱼ + n)_{3×3} = 0` for six elements of `A`.

**New here: `|A| ≤ 4` (`card_le_four`).** Five elements are enough. For `a₁, a₂, b₁, b₂, b₃ ∈ A`
the `3 × 3` matrix with rows `(1, 1, 1)`, `(a₁ bⱼ + n)ⱼ`, `(a₂ bⱼ + n)ⱼ` has rank at most `2`
(all rows lie in the span of `(1, 1, 1)` and `(bⱼ)ⱼ`), and all its entries are `k`-th powers.
Writing `Xᵢⱼ = aᵢ bⱼ + n`, its determinant gives the six-term relation
`X₁₁X₂₂ + X₁₂X₂₃ + X₁₃X₂₁ = X₁₁X₂₃ + X₁₂X₂₁ + X₁₃X₂₂`
between products of `k`-th powers. The product of the three left terms equals the product of the
three right terms, and no left term equals a right term.

The only analytic input is the statement `SixTermRigid F k`: in such a six-term relation of
`k`-th powers all six terms are proportional. For `F` algebraically closed of characteristic `0`
and `k ≥ 18` this is exactly what Tsang–Yip prove in their Claims 4.8 and 4.9 (via Corollary 4.2
and Proposition 4.4, which rest on the Vaserstein–Wheland generalization of Mason–Stothers);
their argument uses only the three properties above. Any improvement of their Proposition 4.4
(Remark 4.6 asks for `k ≥ 15`) lowers the threshold here as well.

Six-term rigidity forces, for each `aᵢ`, the three values `aᵢ b₁ + n, aᵢ b₂ + n, aᵢ b₃ + n` to be
proportional (`flat_of_config`). The new combinatorial part is that this cannot happen for all
the ways of splitting five elements, unless all five lie on one line `F s` through `0` and
`n ∈ F s²` (`exists_line_of_card_eq_five`); over an algebraically closed field that is
Tsang–Yip's exceptional family (`card_le_four`).
-/

namespace DiophantineTuples

open Polynomial

variable {F : Type*} [Field F]

/-- `A ⊆ F[X]` has property `D_k(n)`. -/
def PolyHasPropertyD (k : ℕ) (n : F[X]) (A : Finset F[X]) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ f : F[X], a * b + n = f ^ k

variable (F) in
/-- **Six-term rigidity** for exponent `k`: if six nonzero polynomials satisfy
`q₁ᵏ + q₂ᵏ + q₃ᵏ = r₁ᵏ + r₂ᵏ + r₃ᵏ` and `q₁q₂q₃ = r₁r₂r₃`, and no `qᵢᵏ` equals an `rⱼᵏ`, then
all `qᵢᵏ` and `rⱼᵏ` are proportional. Tsang–Yip (Claims 4.8–4.9 of arXiv:2607.01165) prove this
for `F` algebraically closed of characteristic `0` and `k ≥ 18`. -/
def SixTermRigid (k : ℕ) : Prop :=
  ∀ q r : Fin 3 → F[X], (∀ i, q i ≠ 0) → (∀ j, r j ≠ 0) → (∀ i j, q i ^ k ≠ r j ^ k) →
    ∑ i, q i ^ k = ∑ j, r j ^ k → ∏ i, q i = ∏ j, r j → ∀ i j, Associated (q i ^ k) (r j ^ k)

/-- `f` is an `F`-multiple of `g`. -/
def IsMul (f g : F[X]) : Prop := ∃ c : F, f = C c * g

namespace IsMul

lemma refl (g : F[X]) : IsMul g g := ⟨1, by simp⟩

lemma trans {f g h : F[X]} (h₁ : IsMul f g) (h₂ : IsMul g h) : IsMul f h := by
  obtain ⟨c, rfl⟩ := h₁; obtain ⟨d, rfl⟩ := h₂
  exact ⟨c * d, by rw [C_mul, mul_assoc]⟩

lemma sub {f g h : F[X]} (h₁ : IsMul f h) (h₂ : IsMul g h) : IsMul (f - g) h := by
  obtain ⟨c, rfl⟩ := h₁; obtain ⟨d, rfl⟩ := h₂
  exact ⟨c - d, by rw [C_sub, sub_mul]⟩

lemma neg {f h : F[X]} (h₁ : IsMul f h) : IsMul (-f) h := by
  obtain ⟨c, rfl⟩ := h₁
  exact ⟨-c, by rw [C_neg, neg_mul]⟩

lemma mul {f g f' g' : F[X]} (h₁ : IsMul f g) (h₂ : IsMul f' g') : IsMul (f * f') (g * g') := by
  obtain ⟨c, rfl⟩ := h₁; obtain ⟨d, rfl⟩ := h₂
  exact ⟨c * d, by rw [C_mul]; ring⟩

lemma mul_left (x : F[X]) {f g : F[X]} (h : IsMul f g) : IsMul (x * f) (x * g) :=
  (refl x).mul h

lemma cancel_left {x f g : F[X]} (hx : x ≠ 0) (h : IsMul (x * f) (x * g)) : IsMul f g := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, mul_left_cancel₀ hx (by rw [hc]; ring)⟩

lemma cancel_right {x f g : F[X]} (hx : x ≠ 0) (h : IsMul (f * x) (g * x)) : IsMul f g :=
  cancel_left hx (by rwa [mul_comm x f, mul_comm x g])

lemma symm {f g : F[X]} (hf : f ≠ 0) (h : IsMul f g) : IsMul g f := by
  obtain ⟨c, rfl⟩ := h
  have hc : c ≠ 0 := by rintro rfl; simp at hf
  exact ⟨c⁻¹, by rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]⟩

lemma of_associated {f g : F[X]} (h : Associated f g) : IsMul g f := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp u.isUnit
  exact ⟨r, by rw [← hu, hr, mul_comm]⟩

lemma zero_left (g : F[X]) : IsMul 0 g := ⟨0, by simp⟩

end IsMul

/-- `a b + n = 0` has at most one solution `b` for given `a`, because `n ≠ 0`. -/
lemma partner_unique {n a b b' : F[X]} (hn : n ≠ 0) (h : a * b + n = 0) (h' : a * b' + n = 0) :
    b = b' := by
  have ha : a ≠ 0 := by rintro rfl; simp [hn] at h
  exact mul_left_cancel₀ ha (by linear_combination h - h')

lemma ne_zero_of_partner {n a b : F[X]} (hn : n ≠ 0) (h : a * b + n = 0) : a ≠ 0 := by
  rintro rfl; simp [hn] at h

/-- **Configuration lemma.** Take `a₁, a₂ ≠ 0` and `b₁, b₂, b₃` (five distinct polynomials) such
that every `aᵢ bⱼ + n` is a nonzero `k`-th power. Under six-term rigidity, for each `i` the three
values `aᵢ b₁ + n`, `aᵢ b₂ + n`, `aᵢ b₃ + n` are pairwise proportional. -/
theorem flat_of_config {k : ℕ} (hR : SixTermRigid F k) (hk : 0 < k) {n : F[X]} (hn : n ≠ 0)
    {a₁ a₂ b₁ b₂ b₃ : F[X]} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha : a₁ ≠ a₂)
    (hb₁₂ : b₁ ≠ b₂) (hb₁₃ : b₁ ≠ b₃) (hb₂₃ : b₂ ≠ b₃)
    (n₁₁ : a₁ * b₁ + n ≠ 0) (n₁₂ : a₁ * b₂ + n ≠ 0) (n₁₃ : a₁ * b₃ + n ≠ 0)
    (n₂₁ : a₂ * b₁ + n ≠ 0) (n₂₂ : a₂ * b₂ + n ≠ 0) (n₂₃ : a₂ * b₃ + n ≠ 0)
    {f₁₁ f₁₂ f₁₃ f₂₁ f₂₂ f₂₃ : F[X]}
    (h₁₁ : a₁ * b₁ + n = f₁₁ ^ k) (h₁₂ : a₁ * b₂ + n = f₁₂ ^ k) (h₁₃ : a₁ * b₃ + n = f₁₃ ^ k)
    (h₂₁ : a₂ * b₁ + n = f₂₁ ^ k) (h₂₂ : a₂ * b₂ + n = f₂₂ ^ k) (h₂₃ : a₂ * b₃ + n = f₂₃ ^ k) :
    Associated (a₁ * b₁ + n) (a₁ * b₂ + n) ∧ Associated (a₁ * b₁ + n) (a₁ * b₃ + n) ∧
      Associated (a₂ * b₁ + n) (a₂ * b₂ + n) ∧ Associated (a₂ * b₁ + n) (a₂ * b₃ + n) := by
  have hf : ∀ {f X : F[X]}, X ≠ 0 → X = f ^ k → f ≠ 0 := by
    rintro f X hX rfl rfl; exact hX (zero_pow hk.ne')
  have sub_ne : ∀ {x y : F[X]}, x ≠ y → x - y ≠ 0 := fun h => sub_ne_zero.mpr h
  set q : Fin 3 → F[X] := ![f₁₁ * f₂₂, f₁₂ * f₂₃, f₁₃ * f₂₁] with hq
  set r : Fin 3 → F[X] := ![f₁₁ * f₂₃, f₁₂ * f₂₁, f₁₃ * f₂₂] with hr
  have hq0 : ∀ i, q i ≠ 0 := by
    intro i; fin_cases i <;>
      simp [q, hf n₁₁ h₁₁, hf n₁₂ h₁₂, hf n₁₃ h₁₃, hf n₂₁ h₂₁, hf n₂₂ h₂₂, hf n₂₃ h₂₃]
  have hr0 : ∀ j, r j ≠ 0 := by
    intro j; fin_cases j <;>
      simp [r, hf n₁₁ h₁₁, hf n₁₂ h₁₂, hf n₁₃ h₁₃, hf n₂₁ h₂₁, hf n₂₂ h₂₂, hf n₂₃ h₂₃]
  have eq0 : q 0 ^ k = (a₁ * b₁ + n) * (a₂ * b₂ + n) := by simp [q, mul_pow, h₁₁, h₂₂]
  have eq1 : q 1 ^ k = (a₁ * b₂ + n) * (a₂ * b₃ + n) := by simp [q, mul_pow, h₁₂, h₂₃]
  have eq2 : q 2 ^ k = (a₁ * b₃ + n) * (a₂ * b₁ + n) := by simp [q, mul_pow, h₁₃, h₂₁]
  have er0 : r 0 ^ k = (a₁ * b₁ + n) * (a₂ * b₃ + n) := by simp [r, mul_pow, h₁₁, h₂₃]
  have er1 : r 1 ^ k = (a₁ * b₂ + n) * (a₂ * b₁ + n) := by simp [r, mul_pow, h₁₂, h₂₁]
  have er2 : r 2 ^ k = (a₁ * b₃ + n) * (a₂ * b₂ + n) := by simp [r, mul_pow, h₁₃, h₂₂]
  have hne : ∀ i j, q i ^ k ≠ r j ^ k := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h
    · rw [eq0, er0] at h
      exact mul_ne_zero (mul_ne_zero n₁₁ ha₂) (sub_ne hb₂₃) (by linear_combination h)
    · rw [eq0, er1] at h
      exact mul_ne_zero (mul_ne_zero hn (sub_ne ha)) (sub_ne hb₁₂) (by linear_combination h)
    · rw [eq0, er2] at h
      exact mul_ne_zero (mul_ne_zero n₂₂ ha₁) (sub_ne hb₁₃) (by linear_combination h)
    · rw [eq1, er0] at h
      exact mul_ne_zero (mul_ne_zero n₂₃ ha₁) (sub_ne hb₁₂.symm) (by linear_combination h)
    · rw [eq1, er1] at h
      exact mul_ne_zero (mul_ne_zero n₁₂ ha₂) (sub_ne hb₁₃.symm) (by linear_combination h)
    · rw [eq1, er2] at h
      exact mul_ne_zero (mul_ne_zero hn (sub_ne ha)) (sub_ne hb₂₃) (by linear_combination h)
    · rw [eq2, er0] at h
      exact mul_ne_zero (mul_ne_zero hn (sub_ne ha)) (sub_ne hb₁₃.symm) (by linear_combination h)
    · rw [eq2, er1] at h
      exact mul_ne_zero (mul_ne_zero n₂₁ ha₁) (sub_ne hb₂₃.symm) (by linear_combination h)
    · rw [eq2, er2] at h
      exact mul_ne_zero (mul_ne_zero n₁₃ ha₂) (sub_ne hb₁₂) (by linear_combination h)
  have hsum : ∑ i, q i ^ k = ∑ j, r j ^ k := by
    simp only [Fin.sum_univ_three, eq0, eq1, eq2, er0, er1, er2]; ring
  have hprod : ∏ i, q i = ∏ j, r j := by
    simp only [Fin.prod_univ_three, q, r, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have H := hR q r hq0 hr0 hne hsum hprod
  have A00 := H 0 0; have A02 := H 0 2; have A11 := H 1 1; have A10 := H 1 0
  have A22 := H 2 2
  rw [eq0, er0] at A00; rw [eq0, er2] at A02; rw [eq1, er1] at A11; rw [eq1, er0] at A10
  rw [eq2, er2] at A22
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- X₁₂ X₂₃ ~ X₁₁ X₂₃
    exact (A10.of_mul_right (Associated.refl _) n₂₃).symm
  · -- X₁₁ X₂₂ ~ X₁₃ X₂₂
    exact A02.of_mul_right (Associated.refl _) n₂₂
  · -- X₁₃ X₂₁ ~ X₁₃ X₂₂
    exact A22.of_mul_left (Associated.refl _) n₁₃
  · -- X₁₂ X₂₃ ~ X₁₂ X₂₁
    exact (A11.of_mul_left (Associated.refl _) n₁₂).symm

/-- **Algebraic core.** Suppose `a₁, a₂, u, v ≠ 0`, `a₁ ≠ a₂`, `u ≠ v`, and
* `a₁ u + n`, `a₁ v + n`, `a₁ w + n` are proportional (`a₁` is flat on `{u, v, w}`),
* `a₂ u + n`, `a₂ v + n` are proportional,
* `u a₁ + n`, `u a₂ + n` are proportional,
* `a₁ a₂ + n = 0`, or `u v + n = 0`, or `a₁ a₂ + n` and `a₁ v + n` are proportional.

Then `a₁, a₂, u, v, w ∈ F a₂` and `n ∈ F a₂²`. -/
theorem line_of_flat {n a₁ a₂ u v w : F[X]} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hu : u ≠ 0)
    (hv : v ≠ 0) (ha : a₁ ≠ a₂) (huv : u ≠ v)
    (h₁ : Associated (a₁ * u + n) (a₁ * v + n)) (h₂ : Associated (a₁ * u + n) (a₁ * w + n))
    (h₃ : Associated (a₂ * u + n) (a₂ * v + n)) (h₄ : Associated (u * a₁ + n) (u * a₂ + n))
    (h₅ : a₁ * a₂ + n = 0 ∨ u * v + n = 0 ∨ Associated (a₁ * a₂ + n) (a₁ * v + n)) :
    IsMul n (a₂ ^ 2) ∧ IsMul a₁ a₂ ∧ IsMul a₂ a₂ ∧ IsMul u a₂ ∧ IsMul v a₂ ∧ IsMul w a₂ := by
  set G := a₁ * u + n
  have hsub : ∀ {x y : F[X]}, x ≠ y → x - y ≠ 0 := fun h => sub_ne_zero.mpr h
  -- everything relevant is a multiple of `G`
  have m₁ : IsMul (a₁ * v + n) G := IsMul.of_associated h₁
  have m₂ : IsMul (a₁ * w + n) G := IsMul.of_associated h₂
  have m₄ : IsMul (a₂ * u + n) G := by
    have := IsMul.of_associated h₄
    rwa [mul_comm u a₂, mul_comm u a₁] at this
  have m₃ : IsMul (a₂ * v + n) G := (IsMul.of_associated h₃).trans m₄
  -- `a₁ (u - v)`, `a₂ (u - v)`, `u (a₁ - a₂)`, `v (a₁ - a₂)` are multiples of `G`
  have d₁ : IsMul (a₁ * (u - v)) G := by
    have := (IsMul.refl G).sub m₁; rwa [show G - (a₁ * v + n) = a₁ * (u - v) by ring] at this
  have d₂ : IsMul (a₂ * (u - v)) G := by
    have := m₄.sub m₃; rwa [show a₂ * u + n - (a₂ * v + n) = a₂ * (u - v) by ring] at this
  have d₃ : IsMul (u * (a₁ - a₂)) G := by
    have := (IsMul.refl G).sub m₄; rwa [show G - (a₂ * u + n) = u * (a₁ - a₂) by ring] at this
  have d₄ : IsMul (v * (a₁ - a₂)) G := by
    have := m₁.sub m₃; rwa [show a₁ * v + n - (a₂ * v + n) = v * (a₁ - a₂) by ring] at this
  -- `a₁ ∈ F a₂` and `u ∈ F v`
  have G₂ : IsMul G (a₂ * (u - v)) := d₂.symm (mul_ne_zero ha₂ (hsub huv))
  have e₁ : IsMul a₁ a₂ := by
    have := d₁.trans G₂
    rw [mul_comm a₁, mul_comm a₂] at this
    exact this.cancel_left (hsub huv)
  have G₄ : IsMul G (v * (a₁ - a₂)) := d₄.symm (mul_ne_zero hv (hsub ha))
  have e₂ : IsMul u v := by
    have := d₃.trans G₄
    rw [mul_comm u, mul_comm v] at this
    exact this.cancel_left (hsub ha)
  -- `G ∈ F (a₂ v)` and `n ∈ F (a₂ v)`
  have GV : IsMul G (a₂ * v) := G₂.trans ((e₂.sub (IsMul.refl v)).mul_left a₂)
  have nV : IsMul n (a₂ * v) := by
    have := GV.sub (e₁.mul e₂); rwa [show G - a₁ * u = n by ring] at this
  -- `w ∈ F v`
  have e₃ : IsMul w v := by
    have h₁w : IsMul (a₁ * w) (a₂ * v) := by
      have := (m₂.trans GV).sub nV; rwa [show a₁ * w + n - n = a₁ * w by ring] at this
    have h₂w : IsMul (a₂ * w) (a₂ * v) := (((e₁.symm ha₁).mul (IsMul.refl w))).trans h₁w
    exact h₂w.cancel_left ha₂
  -- `v ∈ F a₂`
  have hn' : IsMul (-n) (a₂ * v) := nV.neg
  have from_a₁a₂ : IsMul (a₁ * a₂) (a₂ * v) → IsMul v a₂ := by
    intro h
    have : IsMul (a₂ * a₂) (a₂ * v) := ((e₁.symm ha₁).mul (IsMul.refl a₂)).trans h
    exact (this.cancel_left ha₂).symm ha₂
  have e₄ : IsMul v a₂ := by
    rcases h₅ with h | h | h
    · exact from_a₁a₂ (by rwa [show a₁ * a₂ = -n by linear_combination h])
    · have huv' : IsMul (u * v) (a₂ * v) := by rwa [show u * v = -n by linear_combination h]
      have : IsMul (v * v) (a₂ * v) := ((e₂.symm hu).mul (IsMul.refl v)).trans huv'
      exact this.cancel_right hv
    · apply from_a₁a₂
      have := ((IsMul.of_associated h.symm).trans (m₁.trans GV)).sub nV
      rwa [show a₁ * a₂ + n - n = a₁ * a₂ by ring] at this
  refine ⟨?_, e₁, IsMul.refl _, e₂.trans e₄, e₄, e₃.trans e₄⟩
  rw [sq]
  exact nV.trans ((IsMul.refl a₂).mul e₄)

/-- Among three distinct polynomials one can order them as `u, v, w` with `u, v ≠ 0` and
`u w + n ≠ 0 ≠ v w + n`. -/
lemma choose_three {n : F[X]} (hn : n ≠ 0) {r₁ r₂ r₃ : F[X]} (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃)
    (h₂₃ : r₂ ≠ r₃) : ∃ u v w : F[X], (∀ z, z = u ∨ z = v ∨ z = w ↔ z = r₁ ∨ z = r₂ ∨ z = r₃) ∧
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ u ≠ 0 ∧ v ≠ 0 ∧ u * w + n ≠ 0 ∧ v * w + n ≠ 0 := by
  -- an edge `{p, q}` (with `p q + n = 0`) becomes `{u, v}`
  have edge : ∀ {p q t : F[X]}, p ≠ q → p ≠ t → q ≠ t → p * q + n = 0 →
      p * t + n ≠ 0 ∧ q * t + n ≠ 0 ∧ p ≠ 0 ∧ q ≠ 0 := by
    intro p q t hpq hpt hqt h
    refine ⟨fun h' => hqt (partner_unique hn h h'), fun h' => hpt (partner_unique hn
      (by rw [mul_comm]; exact h) h'), ne_zero_of_partner hn h,
      ne_zero_of_partner hn (by rw [mul_comm]; exact h)⟩
  by_cases e₁₂ : r₁ * r₂ + n = 0
  · obtain ⟨a, b, c, d⟩ := edge h₁₂ h₁₃ h₂₃ e₁₂
    exact ⟨r₁, r₂, r₃, fun z => Iff.rfl, h₁₂, h₁₃, h₂₃, c, d, a, b⟩
  by_cases e₁₃ : r₁ * r₃ + n = 0
  · obtain ⟨a, b, c, d⟩ := edge h₁₃ h₁₂ h₂₃.symm e₁₃
    exact ⟨r₁, r₃, r₂, fun z => by tauto, h₁₃, h₁₂, h₂₃.symm, c, d, a, b⟩
  by_cases e₂₃ : r₂ * r₃ + n = 0
  · obtain ⟨a, b, c, d⟩ := edge h₂₃ h₁₂.symm h₁₃.symm e₂₃
    exact ⟨r₂, r₃, r₁, fun z => by tauto, h₂₃, h₁₂.symm, h₁₃.symm, c, d, a, b⟩
  have e₂₁ : r₂ * r₁ + n ≠ 0 := by rwa [mul_comm]
  have e₃₁ : r₃ * r₁ + n ≠ 0 := by rwa [mul_comm]
  have e₃₂ : r₃ * r₂ + n ≠ 0 := by rwa [mul_comm]
  by_cases z₁ : r₁ = 0
  · subst z₁
    exact ⟨r₂, r₃, 0, fun z => by tauto, h₂₃, h₁₂.symm, h₁₃.symm, h₁₂.symm, h₁₃.symm, e₂₁, e₃₁⟩
  by_cases z₂ : r₂ = 0
  · subst z₂
    exact ⟨r₁, r₃, 0, fun z => by tauto, h₁₃, h₁₂, h₂₃.symm, z₁, h₂₃.symm, e₁₂, e₃₂⟩
  exact ⟨r₁, r₂, r₃, fun z => Iff.rfl, h₁₂, h₁₃, h₂₃, z₁, z₂, e₁₃, e₂₃⟩

/-- **Selection.** Five distinct polynomials can be named `a₁, a₂, u, v, w` so that
`a₁, a₂, u, v ≠ 0`, `aᵢ b + n ≠ 0` for `b ∈ {u, v, w}`, and `u w + n ≠ 0 ≠ v w + n`. Then both
`({a₁, a₂}, {u, v, w})` and `({u, v}, {a₁, a₂, w})` are admissible splittings. -/
lemma exists_split {n : F[X]} (hn : n ≠ 0) {A : Finset F[X]} (h5 : A.card = 5) :
    ∃ a₁ a₂ u v w : F[X], a₁ ∈ A ∧ a₂ ∈ A ∧ u ∈ A ∧ v ∈ A ∧ w ∈ A ∧
      (∀ z ∈ A, z = a₁ ∨ z = a₂ ∨ z = u ∨ z = v ∨ z = w) ∧
      a₁ ≠ a₂ ∧ a₁ ≠ u ∧ a₁ ≠ v ∧ a₁ ≠ w ∧ a₂ ≠ u ∧ a₂ ≠ v ∧ a₂ ≠ w ∧
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      a₁ * u + n ≠ 0 ∧ a₁ * v + n ≠ 0 ∧ a₁ * w + n ≠ 0 ∧
      a₂ * u + n ≠ 0 ∧ a₂ * v + n ≠ 0 ∧ a₂ * w + n ≠ 0 ∧
      u * w + n ≠ 0 ∧ v * w + n ≠ 0 := by
  classical
  -- first choose the pair `{a₁, a₂}`
  obtain ⟨x, y, hx, hy, hxy, hx0, hy0, hcross⟩ : ∃ x y : F[X], x ∈ A ∧ y ∈ A ∧ x ≠ y ∧
      x ≠ 0 ∧ y ≠ 0 ∧ ∀ r ∈ A, r ≠ x → r ≠ y → x * r + n ≠ 0 ∧ y * r + n ≠ 0 := by
    by_cases hE : ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ x * y + n = 0
    · obtain ⟨x, hx, y, hy, hxy, h⟩ := hE
      have h' : y * x + n = 0 := by rw [mul_comm]; exact h
      exact ⟨x, y, hx, hy, hxy, ne_zero_of_partner hn h, ne_zero_of_partner hn h',
        fun r _ hrx hry => ⟨fun h'' => hry (partner_unique hn h h'').symm,
          fun h'' => hrx (partner_unique hn h' h'').symm⟩⟩
    · push Not at hE
      have h4 : 1 < (A.erase 0).card := by
        have := Finset.pred_card_le_card_erase (s := A) (a := 0); omega
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h4
      obtain ⟨hx0, hx⟩ := Finset.mem_erase.mp hx
      obtain ⟨hy0, hy⟩ := Finset.mem_erase.mp hy
      exact ⟨x, y, hx, hy, hxy, hx0, hy0, fun r hr hrx hry =>
        ⟨hE x hx r hr hrx.symm, hE y hy r hr hry.symm⟩⟩
  -- the other three
  set R := (A.erase x).erase y with hR
  have hRc : R.card = 3 := by
    rw [hR, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩),
      Finset.card_erase_of_mem hx, h5]
  obtain ⟨r₁, r₂, r₃, h₁₂, h₁₃, h₂₃, hReq⟩ := Finset.card_eq_three.mp hRc
  have memR : ∀ z, z ∈ R ↔ z ≠ y ∧ z ≠ x ∧ z ∈ A := by
    intro z; simp [R, Finset.mem_erase]
  have memR' : ∀ z, z ∈ R ↔ z = r₁ ∨ z = r₂ ∨ z = r₃ := by
    intro z; rw [hReq]; simp
  obtain ⟨u, v, w, huvw, huv, huw, hvw, hu0, hv0, huw0, hvw0⟩ := choose_three hn h₁₂ h₁₃ h₂₃
  have inR : ∀ z, z = u ∨ z = v ∨ z = w → z ≠ y ∧ z ≠ x ∧ z ∈ A := by
    intro z hz; exact (memR z).mp ((memR' z).mpr ((huvw z).mp hz))
  obtain ⟨uy, ux, uA⟩ := inR u (Or.inl rfl)
  obtain ⟨vy, vx, vA⟩ := inR v (Or.inr (Or.inl rfl))
  obtain ⟨wy, wx, wA⟩ := inR w (Or.inr (Or.inr rfl))
  obtain ⟨xu, yu⟩ := hcross u uA ux uy
  obtain ⟨xv, yv⟩ := hcross v vA vx vy
  obtain ⟨xw, yw⟩ := hcross w wA wx wy
  refine ⟨x, y, u, v, w, hx, hy, uA, vA, wA, ?_, hxy, Ne.symm ux, Ne.symm vx, Ne.symm wx,
    Ne.symm uy, Ne.symm vy, Ne.symm wy, huv, huw, hvw, hx0, hy0, hu0, hv0, xu, xv, xw, yu, yv,
    yw, huw0, hvw0⟩
  intro z hz
  by_cases zx : z = x
  · exact Or.inl zx
  by_cases zy : z = y
  · exact Or.inr (Or.inl zy)
  have := (huvw z).mpr ((memR' z).mp ((memR z).mpr ⟨zy, zx, hz⟩))
  tauto

/-- **Five elements force a line.** Under six-term rigidity, every `D_k(n)`-tuple `A ⊆ F[X]` with
five elements lies on a line `F s` through `0` (with `s ∈ A`, `s ≠ 0`), and `n ∈ F s²`. -/
theorem exists_line_of_card_eq_five {k : ℕ} (hR : SixTermRigid F k) (hk : 0 < k) {n : F[X]}
    (hn : n ≠ 0) {A : Finset F[X]} (hA : PolyHasPropertyD k n A) (h5 : A.card = 5) :
    ∃ s ∈ A, s ≠ 0 ∧ IsMul n (s ^ 2) ∧ ∀ x ∈ A, IsMul x s := by
  obtain ⟨a₁, a₂, u, v, w, a₁A, a₂A, uA, vA, wA, hAsub, a₁₂, a₁u, a₁v, a₁w, a₂u, a₂v, a₂w, uv, uw,
    vw, a₁0, a₂0, u0, v0, X₁u, X₁v, X₁w, X₂u, X₂v, X₂w, Xuw, Xvw⟩ := exists_split hn h5
  have pw : ∀ {a b : F[X]}, a ∈ A → b ∈ A → a ≠ b → ∃ f, a * b + n = f ^ k :=
    fun ha hb hab => hA _ ha _ hb hab
  have cm : ∀ a b : F[X], b * a + n = a * b + n := fun a b => by ring
  obtain ⟨f₁u, e₁u⟩ := pw a₁A uA a₁u; obtain ⟨f₁v, e₁v⟩ := pw a₁A vA a₁v
  obtain ⟨f₁w, e₁w⟩ := pw a₁A wA a₁w; obtain ⟨f₂u, e₂u⟩ := pw a₂A uA a₂u
  obtain ⟨f₂v, e₂v⟩ := pw a₂A vA a₂v; obtain ⟨f₂w, e₂w⟩ := pw a₂A wA a₂w
  obtain ⟨fuw, euw⟩ := pw uA wA uw; obtain ⟨fvw, evw⟩ := pw vA wA vw
  -- splitting `({a₁, a₂}, {u, v, w})`
  obtain ⟨F₁, F₂, F₃, -⟩ := flat_of_config hR hk hn a₁0 a₂0 a₁₂ uv uw vw X₁u X₁v X₁w X₂u X₂v X₂w
    e₁u e₁v e₁w e₂u e₂v e₂w
  -- splitting `({u, v}, {a₁, a₂, w})`
  obtain ⟨F₄, -⟩ := flat_of_config hR hk hn u0 v0 uv a₁₂ a₁w a₂w (by rwa [cm]) (by rwa [cm])
    Xuw (by rwa [cm]) (by rwa [cm]) Xvw (by rwa [cm]) (by rwa [cm]) euw (by rwa [cm])
    (by rwa [cm]) evw
  -- the third splitting `({a₁, u}, {a₂, v, w})`, when admissible
  have F₅ : a₁ * a₂ + n = 0 ∨ u * v + n = 0 ∨ Associated (a₁ * a₂ + n) (a₁ * v + n) := by
    by_cases X₁₂ : a₁ * a₂ + n = 0
    · exact Or.inl X₁₂
    by_cases Xuv : u * v + n = 0
    · exact Or.inr (Or.inl Xuv)
    obtain ⟨f₁₂, e₁₂⟩ := pw a₁A a₂A a₁₂
    obtain ⟨fuv, euv⟩ := pw uA vA uv
    exact Or.inr (Or.inr (flat_of_config hR hk hn a₁0 u0 a₁u a₂v a₂w vw X₁₂ X₁v X₁w
      (by rwa [cm]) Xuv Xuw e₁₂ e₁v e₁w (by rwa [cm]) euv euw).1)
  obtain ⟨hn2, m₁, m₂, mu, mv, mw⟩ := line_of_flat a₁0 a₂0 u0 v0 a₁₂ uv F₁ F₂ F₃ F₄ F₅
  refine ⟨a₂, a₂A, a₂0, hn2, fun z hz => ?_⟩
  rcases hAsub z hz with rfl | rfl | rfl | rfl | rfl <;> assumption

lemma PolyHasPropertyD.mono {k : ℕ} {n : F[X]} {A B : Finset F[X]} (hA : PolyHasPropertyD k n A)
    (hBA : B ⊆ A) : PolyHasPropertyD k n B :=
  fun a ha b hb hab => hA a (hBA ha) b (hBA hb) hab

/-- **At least five elements force a line.** Under six-term rigidity, a `D_k(n)`-tuple
`A ⊆ F[X]` with `|A| ≥ 5` lies on a line `F s` through `0`, `s ≠ 0`, and `n ∈ F s²`. -/
theorem exists_line_of_five_le_card {k : ℕ} (hR : SixTermRigid F k) (hk : 0 < k) {n : F[X]}
    (hn : n ≠ 0) {A : Finset F[X]} (hA : PolyHasPropertyD k n A) (h5 : 5 ≤ A.card) :
    ∃ s, s ≠ 0 ∧ IsMul n (s ^ 2) ∧ ∀ x ∈ A, IsMul x s := by
  classical
  obtain ⟨t, htA, htc⟩ := Finset.exists_subset_card_eq h5
  obtain ⟨s, hst, hs0, hns, hts⟩ := exists_line_of_card_eq_five hR hk hn (hA.mono htA) htc
  refine ⟨s, hs0, hns, fun y hy => ?_⟩
  by_cases hyt : y ∈ t
  · exact hts y hyt
  -- replace some `z ∈ t`, `z ≠ s`, by `y`
  obtain ⟨z, hz, hzs⟩ : ∃ z ∈ t, z ≠ s := by
    by_contra! h
    have : t ⊆ {s} := fun z hz => Finset.mem_singleton.mpr (h z hz)
    have := Finset.card_le_card this
    simp at this; omega
  set t' := insert y (t.erase z)
  have ht'A : t' ⊆ A := Finset.insert_subset hy ((Finset.erase_subset _ _).trans htA)
  have ht'c : t'.card = 5 := by
    rw [Finset.card_insert_of_notMem (fun h => hyt (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hz, htc]
  obtain ⟨s', -, -, -, hts'⟩ := exists_line_of_card_eq_five hR hk hn (hA.mono ht'A) ht'c
  have hss' : IsMul s s' := hts' s (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hzs.symm, hst⟩))
  exact (hts' y (Finset.mem_insert_self _ _)).trans (hss'.symm hs0)

/-- **Main theorem: `|A| ≤ 4`.** Let `F` be algebraically closed, `n ∈ F[X]` nonzero, and assume
six-term rigidity for `k` (true for characteristic `0` and `k ≥ 18` by Tsang–Yip, Claims 4.8–4.9).
If `A ⊆ F[X]` has property `D_k(n)` and is not in the exceptional family
(`n = s²` is a `k`-th power and `A ⊆ F s`), then `|A| ≤ 4`. Tsang–Yip prove `|A| ≤ 6`. -/
theorem card_le_four [IsAlgClosed F] {k : ℕ} (hR : SixTermRigid F k) (hk : 0 < k) {n : F[X]}
    (hn : n ≠ 0) {A : Finset F[X]} (hA : PolyHasPropertyD k n A)
    (hexc : ¬ ∃ s : F[X], n = s ^ 2 ∧ (∃ f : F[X], n = f ^ k) ∧ ∀ a ∈ A, IsMul a s) :
    A.card ≤ 4 := by
  classical
  by_contra! h5
  obtain ⟨s, hs0, ⟨κ, hκ⟩, hAs⟩ := exists_line_of_five_le_card hR hk hn hA h5
  have hκ0 : κ ≠ 0 := by rintro rfl; simp [hκ] at hn
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq κ two_pos
  have hμ0 : μ ≠ 0 := by rintro rfl; simp at hμ; exact hκ0 hμ.symm
  set s₀ := C μ * s
  have hn₀ : n = s₀ ^ 2 := by rw [hκ, ← hμ, C_pow]; ring
  have hAs₀ : ∀ a ∈ A, IsMul a s₀ := fun a ha =>
    (hAs a ha).trans ⟨μ⁻¹, by rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hμ0, C_1, one_mul]⟩
  apply hexc
  refine ⟨s₀, hn₀, ?_, hAs₀⟩
  -- a pair `x ≠ y` with `x y + n ≠ 0`
  obtain ⟨x, hx, y, hy, hxy, hX⟩ : ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ x * y + n ≠ 0 := by
    have h1 : 0 < A.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp h1
    have h3 : 1 < (A.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
    obtain ⟨y₁, hy₁, y₂, hy₂, hy₁₂⟩ := Finset.one_lt_card.mp h3
    obtain ⟨hy₁x, hy₁⟩ := Finset.mem_erase.mp hy₁
    obtain ⟨hy₂x, hy₂⟩ := Finset.mem_erase.mp hy₂
    by_cases h : x * y₁ + n = 0
    · exact ⟨x, hx, y₂, hy₂, hy₂x.symm, fun h' => hy₁₂ (partner_unique hn h h')⟩
    · exact ⟨x, hx, y₁, hy₁, hy₁x.symm, h⟩
  obtain ⟨f, hf⟩ := hA x hx y hy hxy
  obtain ⟨c, rfl⟩ := hAs₀ x hx
  obtain ⟨c', rfl⟩ := hAs₀ y hy
  have hxy' : C c * s₀ * (C c' * s₀) + n = C (c * c' + 1) * n := by
    rw [hn₀, C_add, C_mul, C_1]; ring
  have hcc : c * c' + 1 ≠ 0 := by
    intro h; rw [hxy', h, C_0, zero_mul] at hX; exact hX rfl
  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq (c * c' + 1)⁻¹ hk
  refine ⟨C ν * f, ?_⟩
  rw [mul_pow, ← C_pow, hν, ← hf, hxy', ← mul_assoc, ← C_mul, inv_mul_cancel₀ hcc, C_1, one_mul]

end DiophantineTuples
