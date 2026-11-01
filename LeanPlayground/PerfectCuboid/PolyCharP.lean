module

public import Mathlib

/-!
# Polynomial cuboids over an arbitrary field (characteristic `p`)

Rounds 13–14 (`PolynomialCuboid.lean`, `PolyMonomialEdge.lean`) studied polynomial cuboids over
`ℚ[X]`, where positivity forbids cancellation (`x² + y² = 0 ⇒ x = y = 0`, `natDegree_hyp`) and a
monomial edge forces proportional edges. Here the field `K` is arbitrary.

* `IsCuboid a b c`: nonzero `a, b, c ∈ K[X]` with the four sums `a² + b²`, `a² + c²`, `b² + c²`,
  `a² + b² + c²` squares in `K[X]` (zero allowed); `IsNondegCuboid`: moreover the four sums are
  nonzero; `Proportional a b c`: `a, b, c ∈ K · q` for one polynomial `q`.
* **Characteristic 2 is empty of content** (`isCuboid_of_charTwo`): every triple of nonzero
  polynomials is a cuboid, since `x² + y² = (x + y)²`; it is nondegenerate iff `a ≠ b`, `a ≠ c`,
  `b ≠ c`, `a + b + c ≠ 0` (`isNondegCuboid_iff_of_charTwo`).
* **Zero space diagonal** (`isCuboid_of_sum_eq_zero`): if `i² = −1` in `K` and
  `a² + b² + c² = 0` with `a b c ≠ 0`, then `(a, b, c)` is a cuboid: `a² + b² = (i c)²`,
  `a² + c² = (i b)²`, `b² + c² = (i a)²`. Hence every Pythagorean triple `a² + b² = d²` gives the
  cuboid `(a, b, i d)` (`isCuboid_of_pythagorean`), e.g. the non-proportional
  `(2X, X² − 1, i (X² + 1))` (`isCuboid_family`, `not_proportional_family`), and over `𝔽_p` for
  every prime `p ≡ 1 (mod 4)` there is a non-proportional cuboid
  (`exists_not_proportional_of_mod_four`).
* **The `𝔽₅` example** (`isCuboid_five`, `not_proportional_five`): `(X, 1 + X², 2 + 3X²)` over
  `𝔽₅` with `a² + b² = (X² + 4)²`, `a² + c² = (2X² + 2)²`, `b² + c² = (2X)²`, `a² + b² + c² = 0`.
  Its edge `X` is a monomial, so the round-14 theorem `IsPolyCuboid.proportional_of_monomial_edge`
  (monomial edge ⇒ proportional) is false over `𝔽₅` once a zero sum is allowed: the ordered-field
  hypothesis of `not_isSquare_four_term` is necessary at cuboid level, not only for the lemma.
* **Degenerate cuboids need `√−1`** (`isSquare_neg_one_of_sq_add_sq_eq_zero`,
  `IsCuboid.isNondegCuboid`): if `−1` is not a square in `K`, every cuboid over `K[X]` is
  nondegenerate (a zero sum `x² + y² = 0`, or `a² + b² = −c²`, forces `−1 = (lc/lc)²`). So for
  `p ≡ 3 (mod 4)` there is nothing degenerate (`IsCuboid.isNondegCuboid_of_mod_four_eq_three`),
  and for `p ≡ 1 (mod 4)` there is (above).
* **Degree of the hypotenuse** (`natDegree_hyp_fails_five`, `natDegree_hyp_of_ne`): the round-13
  lemma `natDegree_hyp` fails over `𝔽₅` (`X² + (2X)² = 0`), and holds over any field when the
  squares of the leading coefficients do not cancel.

* **Nondegenerate non-proportional cuboids exist in odd characteristic `p` with `√−1`**
  (`isNondegCuboid_frobenius`, `not_proportional_frobenius`): the *Frobenius cuboid*
  `(X − X^p, i (X + X^p), X^(p+1) + 1)` has `a² + b² = (2i X^((p+1)/2))²`,
  `a² + c² = ((X² + 1)^((p+1)/2))²`, `b² + c² = ((X² − 1)^((p+1)/2))²`,
  `a² + b² + c² = (X^(p+1) − 1)²`, all nonzero; the middle identities are the Frobenius
  `(X² ± 1)^p = X^(2p) ± 1`. Hence for every prime `p ≡ 1 (mod 4)` the cuboid surface has
  non-constant `𝔽_p(X)`-points with all seven coordinates nonzero
  (`exists_nondeg_not_proportional_of_mod_four`; over `𝔽₅`: `isNondegCuboid_five`), and for every
  odd `p` it has such `𝔽_{p²}(X)`-points. Over `ℚ[X]` no non-proportional polynomial cuboid is
  known and every theorem so far forces proportionality; the Frobenius cuboid shows that any such
  theorem must use characteristic `0` (or at least `p ∤` something), not only the algebra of
  squares. For `p ≡ 3 (mod 4)` over `𝔽_p` itself, none was found by exhaustive search (`p = 3`,
  degree ≤ 7; `p = 7`, degree ≤ 5; `p = 11`, degree ≤ 3; round 15, brief 4, `code/b4/`).
-/
@[expose] public section

open Polynomial

namespace PerfectCuboid.PolyCharP

variable {K : Type*} [Field K]

/-- A cuboid over `K[X]`: nonzero edges, the four sums are squares (possibly zero). -/
structure IsCuboid (a b c : K[X]) : Prop where
  ne_a : a ≠ 0
  ne_b : b ≠ 0
  ne_c : c ≠ 0
  sq_ab : IsSquare (a ^ 2 + b ^ 2)
  sq_ac : IsSquare (a ^ 2 + c ^ 2)
  sq_bc : IsSquare (b ^ 2 + c ^ 2)
  sq_abc : IsSquare (a ^ 2 + b ^ 2 + c ^ 2)

/-- Nondegenerate: the four sums are nonzero. -/
structure IsNondegCuboid (a b c : K[X]) : Prop extends IsCuboid a b c where
  ne_ab : a ^ 2 + b ^ 2 ≠ 0
  ne_ac : a ^ 2 + c ^ 2 ≠ 0
  ne_bc : b ^ 2 + c ^ 2 ≠ 0
  ne_abc : a ^ 2 + b ^ 2 + c ^ 2 ≠ 0

/-- Proportional edges: `a, b, c` are constant multiples of one polynomial. -/
def Proportional (a b c : K[X]) : Prop :=
  ∃ q : K[X], ∃ α β γ : K, a = C α * q ∧ b = C β * q ∧ c = C γ * q

/-- Nonzero proportional edges have equal degrees. -/
theorem Proportional.natDegree_eq {a b c : K[X]} (h : Proportional a b c) (ha : a ≠ 0)
    (hb : b ≠ 0) : a.natDegree = b.natDegree := by
  obtain ⟨q, α, β, γ, rfl, rfl, -⟩ := h
  have hα : α ≠ 0 := by rintro rfl; simp at ha
  have hβ : β ≠ 0 := by rintro rfl; simp at hb
  rw [natDegree_C_mul hα, natDegree_C_mul hβ]

/-- Edges of different degrees are not proportional. -/
theorem not_proportional_of_natDegree_ne {a b c : K[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.natDegree ≠ b.natDegree) : ¬ Proportional a b c :=
  fun hp => h (hp.natDegree_eq ha hb)

/-! ## Characteristic 2 -/

section CharTwo

variable [CharP K 2]

/-- **T1.** In characteristic 2 every triple of nonzero polynomials is a cuboid. -/
theorem isCuboid_of_charTwo {a b c : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    IsCuboid a b c where
  ne_a := ha
  ne_b := hb
  ne_c := hc
  sq_ab := ⟨a + b, by rw [← sq, CharTwo.add_sq]⟩
  sq_ac := ⟨a + c, by rw [← sq, CharTwo.add_sq]⟩
  sq_bc := ⟨b + c, by rw [← sq, CharTwo.add_sq]⟩
  sq_abc := ⟨a + b + c, by rw [← sq, CharTwo.add_sq, CharTwo.add_sq]⟩

theorem add_eq_zero_iff_of_charTwo {x y : K[X]} : x + y = 0 ↔ x = y := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

/-- In characteristic 2 a cuboid is nondegenerate iff the edges are pairwise distinct and
`a + b + c ≠ 0`. -/
theorem isNondegCuboid_iff_of_charTwo {a b c : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    IsNondegCuboid a b c ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b + c ≠ 0 := by
  have e : ∀ x y : K[X], x ^ 2 + y ^ 2 = (x + y) ^ 2 := fun x y => (CharTwo.add_sq x y).symm
  have e3 : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 := by rw [e, e]
  have hz : ∀ x : K[X], x ^ 2 ≠ 0 ↔ x ≠ 0 := fun x => pow_ne_zero_iff two_ne_zero
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := h.ne_ab; rw [e, hz] at this; exact fun h' => this (add_eq_zero_iff_of_charTwo.2 h')
    · have := h.ne_ac; rw [e, hz] at this; exact fun h' => this (add_eq_zero_iff_of_charTwo.2 h')
    · have := h.ne_bc; rw [e, hz] at this; exact fun h' => this (add_eq_zero_iff_of_charTwo.2 h')
    · have := h.ne_abc; rw [e3, hz] at this; exact this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨isCuboid_of_charTwo ha hb hc, ?_, ?_, ?_, ?_⟩
    · rw [e, hz]; exact fun h' => h1 (add_eq_zero_iff_of_charTwo.1 h')
    · rw [e, hz]; exact fun h' => h2 (add_eq_zero_iff_of_charTwo.1 h')
    · rw [e, hz]; exact fun h' => h3 (add_eq_zero_iff_of_charTwo.1 h')
    · rw [e3, hz]; exact h4

end CharTwo

/-! ## A square root of `−1`: cuboids with zero space diagonal -/

theorem C_sq_eq_neg_one {i : K} (hi : i ^ 2 = -1) : (C i : K[X]) ^ 2 = -1 := by
  rw [← C_pow, hi, C_neg, C_1]

/-- **T3.** If `i² = −1` and `a² + b² + c² = 0` with `a b c ≠ 0`, then `(a, b, c)` is a cuboid. -/
theorem isCuboid_of_sum_eq_zero {i : K} (hi : i ^ 2 = -1) {a b c : K[X]} (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (h : a ^ 2 + b ^ 2 + c ^ 2 = 0) : IsCuboid a b c where
  ne_a := ha
  ne_b := hb
  ne_c := hc
  sq_ab := ⟨C i * c, by linear_combination h - c ^ 2 * C_sq_eq_neg_one hi⟩
  sq_ac := ⟨C i * b, by linear_combination h - b ^ 2 * C_sq_eq_neg_one hi⟩
  sq_bc := ⟨C i * a, by linear_combination h - a ^ 2 * C_sq_eq_neg_one hi⟩
  sq_abc := ⟨0, by rw [h, mul_zero]⟩

/-- Every Pythagorean triple `a² + b² = d²` gives the degenerate cuboid `(a, b, i d)`. -/
theorem isCuboid_of_pythagorean {i : K} (hi : i ^ 2 = -1) {a b d : K[X]} (ha : a ≠ 0)
    (hb : b ≠ 0) (hd : d ≠ 0) (h : a ^ 2 + b ^ 2 = d ^ 2) : IsCuboid a b (C i * d) := by
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi
  refine isCuboid_of_sum_eq_zero hi ha hb (mul_ne_zero (C_ne_zero.2 hi0) hd) ?_
  linear_combination h + d ^ 2 * C_sq_eq_neg_one hi

theorem natDegree_X_sq_sub_one : (X ^ 2 - 1 : K[X]).natDegree = 2 := by
  rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp

theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : K[X]).natDegree = 2 := by
  rw [natDegree_add_eq_left_of_natDegree_lt] <;> simp

/-- The family `(2X, X² − 1, i (X² + 1))` over any field with `i² = −1` and `2 ≠ 0`. -/
theorem isCuboid_family {i : K} (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) :
    IsCuboid (C 2 * X) (X ^ 2 - 1) (C i * (X ^ 2 + 1)) := by
  refine isCuboid_of_pythagorean hi ?_ ?_ ?_ ?_
  · exact mul_ne_zero (C_ne_zero.2 h2) X_ne_zero
  · intro h; have := congrArg natDegree h; rw [natDegree_X_sq_sub_one] at this; simp at this
  · intro h; have := congrArg natDegree h; rw [natDegree_X_sq_add_one] at this; simp at this
  · rw [C_ofNat]; ring

theorem not_proportional_family {i : K} (h2 : (2 : K) ≠ 0) :
    ¬ Proportional (C 2 * X) (X ^ 2 - 1) (C i * (X ^ 2 + 1)) := by
  apply not_proportional_of_natDegree_ne (mul_ne_zero (C_ne_zero.2 h2) X_ne_zero)
  · intro h; have := congrArg natDegree h; rw [natDegree_X_sq_sub_one] at this; simp at this
  · rw [natDegree_C_mul h2, natDegree_X_sq_sub_one, natDegree_X]; omega

/-- For every prime `p ≡ 1 (mod 4)` there is a non-proportional (degenerate) cuboid over
`𝔽_p[X]`. -/
theorem exists_not_proportional_of_mod_four {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b c : (ZMod p)[X], IsCuboid a b c ∧ ¬ Proportional a b c := by
  obtain ⟨i, hi⟩ := ZMod.exists_sq_eq_neg_one_iff.2 (by omega : p % 4 ≠ 3)
  have hi' : i ^ 2 = -1 := by rw [sq, ← hi]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd two_pos this
    have := (Fact.out : p.Prime).two_le
    have : p = 2 := by omega
    omega
  exact ⟨_, _, _, isCuboid_family hi' h2, not_proportional_family h2⟩

/-! ## Degenerate cuboids need `√−1` -/

/-- If `x² + y² = 0` with `y ≠ 0` in `K[X]`, then `−1` is a square in `K`. -/
theorem isSquare_neg_one_of_sq_add_sq_eq_zero {x y : K[X]} (hy : y ≠ 0)
    (h : x ^ 2 + y ^ 2 = 0) : IsSquare (-1 : K) := by
  have hl : y.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hy
  have h' : x ^ 2 = -y ^ 2 := eq_neg_of_add_eq_zero_left h
  have := congrArg leadingCoeff h'
  rw [leadingCoeff_neg, leadingCoeff_pow, leadingCoeff_pow] at this
  refine ⟨x.leadingCoeff / y.leadingCoeff, ?_⟩
  field_simp
  linear_combination -this

/-- If `−1` is not a square in `K`, every cuboid over `K[X]` is nondegenerate. -/
theorem IsCuboid.isNondegCuboid {a b c : K[X]} (h : IsCuboid a b c)
    (hK : ¬ IsSquare (-1 : K)) : IsNondegCuboid a b c := by
  have two : ∀ x y : K[X], y ≠ 0 → x ^ 2 + y ^ 2 ≠ 0 :=
    fun x y hy h0 => hK (isSquare_neg_one_of_sq_add_sq_eq_zero hy h0)
  refine ⟨h, two _ _ h.ne_b, two _ _ h.ne_c, two _ _ h.ne_c, ?_⟩
  intro h0
  obtain ⟨d, hd⟩ := h.sq_ab
  apply two d c h.ne_c
  rw [← sq] at hd
  rw [← hd, h0]

/-- Over `𝔽_p`, `p ≡ 3 (mod 4)`, every cuboid is nondegenerate. -/
theorem IsCuboid.isNondegCuboid_of_mod_four_eq_three {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {a b c : (ZMod p)[X]} (h : IsCuboid a b c) : IsNondegCuboid a b c :=
  h.isNondegCuboid fun hs => ZMod.exists_sq_eq_neg_one_iff.1 hs hp

/-! ## Nondegenerate non-proportional cuboids from Frobenius -/

/-- Nonzero proportional edges `a, c` have equal degrees. -/
theorem Proportional.natDegree_eq_ac {a b c : K[X]} (h : Proportional a b c) (ha : a ≠ 0)
    (hc : c ≠ 0) : a.natDegree = c.natDegree := by
  obtain ⟨q, α, β, γ, rfl, -, rfl⟩ := h
  have hα : α ≠ 0 := by rintro rfl; simp at ha
  have hγ : γ ≠ 0 := by rintro rfl; simp at hc
  rw [natDegree_C_mul hα, natDegree_C_mul hγ]

/-- **The Frobenius cuboid.** Let `K` have odd prime characteristic `p` and contain `i` with
`i² = −1`. Then `(X − X^p, i (X + X^p), X^(p+1) + 1)` is a nondegenerate cuboid over `K[X]`:
`a² + b² = (2i X^((p+1)/2))²`, `a² + c² = ((X² + 1)^((p+1)/2))²`,
`b² + c² = ((X² − 1)^((p+1)/2))²`, `a² + b² + c² = (X^(p+1) − 1)²`. The middle two identities are
`(X² ± 1)^(p+1) = (X² ± 1)(X^(2p) ± 1)`, i.e. the Frobenius `(u + v)^p = u^p + v^p`. -/
theorem isNondegCuboid_frobenius {p : ℕ} [hp : Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) {i : K}
    (hi : i ^ 2 = -1) :
    IsNondegCuboid (X - X ^ p) (C i * (X + X ^ p)) (X ^ (p + 1) + 1 : K[X]) := by
  obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two hp2
  have hp1 : 2 ≤ p := hp.out.two_le
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    have := Nat.le_of_dvd two_pos this
    omega
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi
  have hI : (C i : K[X]) ^ 2 = -1 := C_sq_eq_neg_one hi
  have hA : (X ^ 2 + 1 : K[X]) ^ p = (X ^ p) ^ 2 + 1 := by
    rw [add_pow_char, one_pow, ← pow_mul, ← pow_mul, mul_comm]
  have hB : (X ^ 2 - 1 : K[X]) ^ p = (X ^ p) ^ 2 - 1 := by
    rw [sub_pow_char, one_pow, ← pow_mul, ← pow_mul, mul_comm]
  have hX : (X : K[X]) ^ (m + 1) * X ^ (m + 1) = X ^ p * X := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  have hsq : ∀ u : K[X], u ^ (m + 1) * u ^ (m + 1) = u ^ p * u := fun u => by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  -- the four identities
  have e1 : (X - X ^ p) ^ 2 + (C i * (X + X ^ p)) ^ 2 =
      (2 * C i * X ^ (m + 1)) * (2 * C i * X ^ (m + 1)) := by
    generalize hZ : (X : K[X]) ^ (m + 1) = Z at hX
    generalize hY : (X : K[X]) ^ p = Y at hX
    linear_combination ((X + Y) ^ 2 - 4 * Z ^ 2) * hI + 4 * hX
  have e2 : (X - X ^ p : K[X]) ^ 2 + (X ^ (p + 1) + 1) ^ 2 =
      (X ^ 2 + 1) ^ (m + 1) * (X ^ 2 + 1) ^ (m + 1) := by
    rw [hsq, hA]
    ring
  have e3 : (C i * (X + X ^ p)) ^ 2 + (X ^ (p + 1) + 1) ^ 2 =
      (X ^ 2 - 1) ^ (m + 1) * (X ^ 2 - 1) ^ (m + 1) := by
    rw [hsq, hB]
    linear_combination (X + X ^ p) ^ 2 * hI
  have e4 : (X - X ^ p) ^ 2 + (C i * (X + X ^ p)) ^ 2 + (X ^ (p + 1) + 1) ^ 2 =
      (X ^ (p + 1) - 1) * (X ^ (p + 1) - 1) := by
    linear_combination (X + X ^ p) ^ 2 * hI
  -- nonvanishing
  have hX1 : (X - X ^ p : K[X]).natDegree = p := by
    rw [natDegree_sub_eq_right_of_natDegree_lt] <;> simp; omega
  have hX2 : (X + X ^ p : K[X]).natDegree = p := by
    rw [natDegree_add_eq_right_of_natDegree_lt] <;> simp; omega
  have hX3 : (X ^ (p + 1) + 1 : K[X]).natDegree = p + 1 := by
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> simp
  have hne : ∀ q : K[X], 0 < q.natDegree → q ≠ 0 := fun q hq h => by
    rw [h, natDegree_zero] at hq; exact lt_irrefl 0 hq
  have ha : (X - X ^ p : K[X]) ≠ 0 := hne _ (by omega)
  have hb : C i * (X + X ^ p : K[X]) ≠ 0 :=
    mul_ne_zero (C_ne_zero.2 hi0) (hne _ (by omega))
  have hc : (X ^ (p + 1) + 1 : K[X]) ≠ 0 := hne _ (by omega)
  have s1 : (2 * C i * X ^ (m + 1) : K[X]) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (C_ne_zero.2 hi0)) (pow_ne_zero _ X_ne_zero)
    rw [← C_ofNat]; exact C_ne_zero.2 h2K
  have s2 : ((X ^ 2 + 1) ^ (m + 1) : K[X]) ≠ 0 :=
    pow_ne_zero _ (hne _ (by rw [natDegree_X_sq_add_one]; omega))
  have s3 : ((X ^ 2 - 1) ^ (m + 1) : K[X]) ≠ 0 :=
    pow_ne_zero _ (hne _ (by rw [natDegree_X_sq_sub_one]; omega))
  have s4 : (X ^ (p + 1) - 1 : K[X]) ≠ 0 := by
    rw [← C_1]; exact X_pow_sub_C_ne_zero (by omega) 1
  exact ⟨⟨ha, hb, hc, ⟨_, e1⟩, ⟨_, e2⟩, ⟨_, e3⟩, ⟨_, e4⟩⟩,
    by rw [e1]; exact mul_ne_zero s1 s1, by rw [e2]; exact mul_ne_zero s2 s2,
    by rw [e3]; exact mul_ne_zero s3 s3, by rw [e4]; exact mul_ne_zero s4 s4⟩

/-- The Frobenius cuboid is not proportional (`deg a = p`, `deg c = p + 1`). -/
theorem not_proportional_frobenius {p : ℕ} [hp : Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {i : K} (hi : i ^ 2 = -1) :
    ¬ Proportional (X - X ^ p) (C i * (X + X ^ p)) (X ^ (p + 1) + 1 : K[X]) := by
  have h := isNondegCuboid_frobenius (K := K) hp2 hi
  have hp1 : 2 ≤ p := hp.out.two_le
  intro hP
  have := hP.natDegree_eq_ac h.ne_a h.ne_c
  rw [natDegree_sub_eq_right_of_natDegree_lt (by simp; omega),
    natDegree_add_eq_left_of_natDegree_lt (by simp)] at this
  simp at this

/-- **Nondegenerate non-proportional cuboids over `𝔽_p[X]`** for every prime `p ≡ 1 (mod 4)`:
non-constant `𝔽_p(X)`-points of the cuboid surface with all seven coordinates nonzero. -/
theorem exists_nondeg_not_proportional_of_mod_four {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b c : (ZMod p)[X], IsNondegCuboid a b c ∧ ¬ Proportional a b c := by
  obtain ⟨i, hi⟩ := ZMod.exists_sq_eq_neg_one_iff.2 (by omega : p % 4 ≠ 3)
  have hi' : i ^ 2 = -1 := by rw [sq, ← hi]
  exact ⟨_, _, _, isNondegCuboid_frobenius (by omega) hi',
    not_proportional_frobenius (by omega) hi'⟩

/-! ## The `𝔽₅` example -/

local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem five_eq_zero : (5 : (ZMod 5)[X]) = 0 := by
  have : ((5 : ℕ) : (ZMod 5)[X]) = 0 := CharP.cast_eq_zero _ 5
  exact_mod_cast this

/-- **T2.** `(X, 1 + X², 2 + 3X²)` is a cuboid over `𝔽₅` with
`a² + b² = (X² + 4)²`, `a² + c² = (2X² + 2)²`, `b² + c² = (2X)²`, `a² + b² + c² = 0`. -/
theorem isCuboid_five : IsCuboid (X : (ZMod 5)[X]) (1 + X ^ 2) (2 + 3 * X ^ 2) where
  ne_a := X_ne_zero
  ne_b := by
    intro h; have := congrArg natDegree h
    rw [add_comm, natDegree_X_sq_add_one] at this; simp at this
  ne_c := by
    intro h; have := congrArg (coeff · 0) h
    simp only [coeff_add, coeff_ofNat_zero, coeff_ofNat_mul, coeff_X_pow, OfNat.zero_ne_ofNat,
      ↓reduceIte, mul_zero, add_zero, coeff_zero] at this
    exact absurd this (by decide)
  sq_ab := ⟨X ^ 2 + 4, by linear_combination (-(X ^ 2 + 3)) * five_eq_zero⟩
  sq_ac := ⟨2 * X ^ 2 + 2, by linear_combination (X ^ 4 + X ^ 2) * five_eq_zero⟩
  sq_bc := ⟨2 * X, by linear_combination (2 * X ^ 4 + 2 * X ^ 2 + 1) * five_eq_zero⟩
  sq_abc := ⟨0, by linear_combination (2 * X ^ 4 + 3 * X ^ 2 + 1) * five_eq_zero⟩

theorem not_proportional_five :
    ¬ Proportional (X : (ZMod 5)[X]) (1 + X ^ 2) (2 + 3 * X ^ 2) := by
  apply not_proportional_of_natDegree_ne X_ne_zero isCuboid_five.ne_b
  rw [natDegree_X, add_comm, natDegree_X_sq_add_one]; omega

/-- **Explicit nondegenerate non-proportional cuboid over `𝔽₅`:**
`(X − X⁵, 2(X + X⁵), X⁶ + 1)`, with `a² + b² = (4X³)²`, `a² + c² = ((X² + 1)³)²`,
`b² + c² = ((X² − 1)³)²`, `a² + b² + c² = (X⁶ − 1)²` (all nonzero). -/
theorem isNondegCuboid_five :
    IsNondegCuboid (X - X ^ 5) (C 2 * (X + X ^ 5)) (X ^ (5 + 1) + 1 : (ZMod 5)[X]) :=
  isNondegCuboid_frobenius (by norm_num) (by decide)

theorem not_proportional_five' :
    ¬ Proportional (X - X ^ 5) (C 2 * (X + X ^ 5)) (X ^ (5 + 1) + 1 : (ZMod 5)[X]) :=
  not_proportional_frobenius (by norm_num) (by decide)

/-- The `𝔽₅` example is degenerate (its space diagonal vanishes). -/
theorem not_isNondegCuboid_five :
    ¬ IsNondegCuboid (X : (ZMod 5)[X]) (1 + X ^ 2) (2 + 3 * X ^ 2) := fun h =>
  h.ne_abc (by linear_combination (2 * X ^ 4 + 3 * X ^ 2 + 1) * five_eq_zero)

/-! ## Degree of the hypotenuse -/

/-- **T5.** The round-13 lemma `natDegree_hyp` fails over `𝔽₅`: `X² + (2X)² = 0²`. -/
theorem natDegree_hyp_fails_five :
    ∃ x y z : (ZMod 5)[X], x ≠ 0 ∧ y ≠ 0 ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧
      z.natDegree ≠ max x.natDegree y.natDegree := by
  refine ⟨X, 2 * X, 0, X_ne_zero, ?_, ?_, ?_⟩
  · rw [← C_ofNat]; exact mul_ne_zero (C_ne_zero.2 (by decide)) X_ne_zero
  · linear_combination X ^ 2 * five_eq_zero
  · rw [natDegree_X, ← C_ofNat, natDegree_C_mul (by decide), natDegree_X]; simp

/-- Char-free `natDegree_hyp`: `deg z = max (deg x) (deg y)` unless the leading terms of `x²`
and `y²` cancel. -/
theorem natDegree_hyp_of_ne {x y z : K[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (hlc : x.natDegree = y.natDegree → x.leadingCoeff ^ 2 + y.leadingCoeff ^ 2 ≠ 0)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : z.natDegree = max x.natDegree y.natDegree := by
  have hx' := leadingCoeff_ne_zero.2 hx
  have hy' := leadingCoeff_ne_zero.2 hy
  have key : (x ^ 2 + y ^ 2).natDegree = 2 * max x.natDegree y.natDegree := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · rw [natDegree_pow]; omega
      · rw [natDegree_pow]; omega
    · rw [coeff_add]
      rcases lt_trichotomy x.natDegree y.natDegree with hlt | heq | hgt
      · rw [max_eq_right hlt.le, coeff_eq_zero_of_natDegree_lt (by rw [natDegree_pow]; omega),
          zero_add, coeff_pow_mul_natDegree]
        exact pow_ne_zero 2 hy'
      · rw [← heq, max_self, coeff_pow_mul_natDegree, heq, coeff_pow_mul_natDegree]
        exact hlc heq
      · rw [max_eq_left hgt.le, coeff_eq_zero_of_natDegree_lt (n := 2 * x.natDegree)
          (p := y ^ 2) (by rw [natDegree_pow]; omega), add_zero,
          coeff_pow_mul_natDegree]
        exact pow_ne_zero 2 hx'
  rw [h, natDegree_pow] at key
  omega

end PerfectCuboid.PolyCharP
