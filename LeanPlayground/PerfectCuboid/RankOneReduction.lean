module

public import LeanPlayground.PerfectCuboid.DivPolyScale

/-!
# Reduction of a rank-one configuration (Asiryan, Lemmas 2 and 3)

This file proves `RankOneReduction` from `CongruentRank.lean`, Asiryan's reduction of a positive
cuboid configuration in a subgroup of rank one to the pattern `(aG, bG + T, cG + S + T)`
(arXiv:2610.10643, §5), from two inputs that Mathlib does not have yet:

* `DivPolyX N`: the abscissa of `n • P` is `Φₙ(x)/ΨSqₙ(x)` in terms of Mathlib's division
  polynomials (the classical formula `n • P = (φₙ : ωₙ : ψₙ)`, Silverman, Exercise 3.7);
* `TorsionTwo N` (Asiryan, Remark 1): every rational torsion point of `E_N` has order at most `2`.

Everything else is proved: the sign of `X(kG)` (`hasX_nsmul`), the classification of the
`2`-torsion (`two_torsion`), table (20) (`hasX_pt`), the polynomial `Z` of Lemma 2 and the rational
root theorem (`DivPolyScale.lean`), the base-point changes `G ↦ G + T` and `G ↦ 2G + S` of
Lemma 3, and the descent on the indices that ends in the pattern (22).
-/

@[expose] public section

namespace PerfectCuboid.CongruentRank

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

variable {N : ℚ}

/-! ### Points and abscissas -/

theorem HasX.unique {P : (curve N).Point} {x x' : ℚ} (h : HasX P x) (h' : HasX P x') :
    x = x' := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨y', hy', h'⟩ := h'
  exact (Point.some.inj h').1

theorem exists_hasX {P : (curve N).Point} (hP : P ≠ 0) : ∃ x, HasX P x := by
  cases P with
  | zero => exact absurd rfl hP
  | @some x y h => exact ⟨x, y, h, rfl⟩

/-- The real points of `E_N` have `X ≥ N` or `−N ≤ X ≤ 0`. -/
theorem HasX.region (hN : 0 < N) {P : (curve N).Point} {x : ℚ} (h : HasX P x) :
    N ≤ x ∨ (-N ≤ x ∧ x ≤ 0) := by
  obtain ⟨y, hy, -⟩ := h
  have hy2 := (nonsingular_iff hN.ne').mp hy
  by_contra! hc
  have : x * (x - N) * (x + N) < 0 := by
    by_cases hx : x ≤ 0
    · have h1 : x < -N := by
        by_contra! h1
        exact (hc.2 h1).not_ge hx
      have : 0 < -x * (N - x) := by nlinarith
      nlinarith
    · rw [not_le] at hx
      have : 0 < x * (N - x) := mul_pos hx (by linarith [hc.1])
      nlinarith
  nlinarith [sq_nonneg y]

/-- A point with `X ∈ {0, N, −N}` has order at most `2`. -/
theorem HasX.add_self_eq_zero (hN : N ≠ 0) {P : (curve N).Point} {x : ℚ} (h : HasX P x)
    (hx : x * (x - N) * (x + N) = 0) : P + P = 0 := by
  obtain ⟨y, hy, rfl⟩ := h
  have hy2 := (nonsingular_iff hN).mp hy
  have hy0 : y = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination hy2 + hx)
  subst hy0
  rw [Point.add_self_of_Y_eq]
  simp [curve, negY]

theorem HasX.add_self_ne_zero (hN : 0 < N) {P : (curve N).Point} {x : ℚ} (h : HasX P x)
    (h1 : -N < x) (h2 : x < 0) : P + P ≠ 0 := by
  obtain ⟨y, hy, rfl⟩ := h
  intro h0
  have hy0 : y = 0 := by
    by_contra hy0
    rw [Point.add_self_of_Y_ne (by
      simp only [curve, negY, zero_mul, sub_zero]; intro h; apply hy0; linarith)] at h0
    exact Point.some_ne_zero _ h0
  have hy2 := (nonsingular_iff hN.ne').mp hy
  subst hy0
  have : x * (x - N) * (x + N) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero h2.ne (by linarith)) (by linarith)
  exact this (by linear_combination -hy2)

/-- The `2`-torsion of `E_N` is `{0, S, T, U}`. -/
theorem two_torsion (hN : N ≠ 0) {R : (curve N).Point} (hR : R + R = 0) :
    R = 0 ∨ R = S hN ∨ R = T hN ∨ R = U hN := by
  cases R with
  | zero => exact .inl rfl
  | @some x y h =>
    right
    have hy0 : y = 0 := by
      by_contra hy0
      rw [Point.add_self_of_Y_ne (by
      simp only [curve, negY, zero_mul, sub_zero]; intro h; apply hy0; linarith)] at hR
      exact Point.some_ne_zero _ hR
    subst hy0
    have hy2 := (nonsingular_iff hN).mp h
    have : x * (x - N) * (x + N) = 0 := by linear_combination -hy2
    rcases mul_eq_zero.mp this with h' | h'
    · rcases mul_eq_zero.mp h' with h' | h'
      · subst h'; exact .inl rfl
      · obtain rfl : x = N := by linear_combination h'
        exact .inr (.inl rfl)
    · obtain rfl : x = -N := by linear_combination h'
      exact .inr (.inr rfl)

/-- For `P + Q = R` with abscissas `x₁, x₂, x₃`, the product `x₁x₂x₃` is the square of the
constant term of the line through the three points. -/
theorem mul_mul_nonneg {P Q : (curve N).Point} {x₁ x₂ x₃ : ℚ} (h₁ : HasX P x₁) (h₂ : HasX Q x₂)
    (h₃ : HasX (P + Q) x₃) : 0 ≤ x₁ * x₂ * x₃ := by
  obtain ⟨y₁, hy₁, rfl⟩ := h₁
  obtain ⟨y₂, hy₂, rfl⟩ := h₂
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curve N).negY x₂ y₂
  · exact absurd (Point.add_of_Y_eq hxy.1 hxy.2) h₃.ne_zero
  rw [Point.add_some hxy] at h₃
  have hx' := (h₃.unique (hasX_some rfl)).symm
  have h := (curve N).addPolynomial_slope hy₁.1 hy₂.1 hxy
  rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective, hx'] at h
  generalize (curve N).slope x₁ x₂ y₁ y₂ = ℓ at h
  simp only [Cubic.mk.injEq, curve] at h
  obtain ⟨-, -, -, hd⟩ := h
  have hd' : x₁ * x₂ * x₃ = (y₁ - ℓ * x₁) ^ 2 := by linear_combination hd
  rw [hd']
  exact sq_nonneg _

/-! ### Non-torsion points and the sign of `X(kG)` -/

/-- `G` has infinite order. -/
def NonTors (G : (curve N).Point) : Prop := ∀ n : ℕ, 0 < n → n • G ≠ 0

theorem NonTors.hasX_ne (hN : N ≠ 0) {G : (curve N).Point} (hG : NonTors G) {k : ℕ}
    (hk : 0 < k) {x : ℚ} (h : HasX (k • G) x) : x * (x - N) * (x + N) ≠ 0 := by
  intro hx
  apply hG (2 * k) (by omega)
  rw [mul_comm, mul_nsmul, two_nsmul]
  exact h.add_self_eq_zero hN hx

/-- **Signs of the multiples.** If `−N < X(G) < 0` and `G` has infinite order, then the odd
multiples of `G` have `−N < X < 0` and the even ones have `X > N`: the map `P ↦ sign X(P)` is a
homomorphism because `X(P)X(Q)X(P + Q)` is a square (`mul_mul_nonneg`). -/
theorem hasX_nsmul (hN : 0 < N) {G : (curve N).Point} (hG : NonTors G) {xG : ℚ}
    (hxG : HasX G xG) (h1 : -N < xG) (h2 : xG < 0) (k : ℕ) (hk : 0 < k) :
    ∃ x, HasX (k • G) x ∧ (Odd k → -N < x ∧ x < 0) ∧ (Even k → N < x) := by
  induction k with
  | zero => omega
  | succ k ih =>
    obtain ⟨x', hx'⟩ := exists_hasX (hG (k + 1) hk)
    refine ⟨x', hx', ?_⟩
    have hne := hG.hasX_ne hN.ne' hk hx'
    have hreg := hx'.region hN
    have hx'0 : x' ≠ 0 := fun h ↦ hne (by rw [h]; ring)
    have hx'N : x' ≠ N := fun h ↦ hne (by rw [h]; ring)
    have hx'N' : x' ≠ -N := fun h ↦ hne (by rw [h]; ring)
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [zero_add, one_smul] at hx'
      rw [hx'.unique hxG]
      exact ⟨fun _ ↦ ⟨h1, h2⟩, fun h ↦ absurd h (by decide)⟩
    obtain ⟨x, hx, hodd, heven⟩ := ih hk0
    have hsign := mul_mul_nonneg hx hxG (by rwa [← succ_nsmul])
    rcases Nat.even_or_odd k with he | ho
    · -- `X(kG) > N > 0` and `X(G) < 0`, so `X((k + 1)G) < 0`
      have hxpos := heven he
      refine ⟨fun _ ↦ ?_, fun h ↦ absurd h (Nat.not_even_iff_odd.mpr he.add_one)⟩
      have : x' < 0 := by
        by_contra! h0
        have hpos : 0 < x' := lt_of_le_of_ne h0 (Ne.symm hx'0)
        have : x * xG * x' < 0 := mul_neg_of_neg_of_pos
          (mul_neg_of_pos_of_neg (by linarith) h2) hpos
        linarith
      rcases hreg with h | h
      · linarith
      · exact ⟨lt_of_le_of_ne h.1 (Ne.symm hx'N'), this⟩
    · obtain ⟨h3, h4⟩ := hodd ho
      refine ⟨fun h ↦ absurd h (Nat.not_odd_iff_even.mpr ho.add_one), fun _ ↦ ?_⟩
      have : 0 < x' := by
        by_contra! h0
        have hneg : x' < 0 := lt_of_le_of_ne h0 hx'0
        have : x * xG * x' < 0 := mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg h4 h2) hneg
        linarith
      rcases hreg with h | h
      · exact lt_of_le_of_ne h (Ne.symm hx'N)
      · linarith

/-! ### The division-polynomial formula and table (20) -/

/-- **Hypothesis: the division-polynomial formula** on `E_N`. If `P` has abscissa `x` and
`n • P ≠ 0`, then `ΨSqₙ(x) ≠ 0` and `n • P` has abscissa `Φₙ(x)/ΨSqₙ(x)`. This is the affine
form of `n • (x, y) = (φₙ : ωₙ : ψₙ)` (Silverman, *The Arithmetic of Elliptic Curves*,
Exercise 3.7), which Mathlib does not have yet. -/
def DivPolyX (N : ℚ) : Prop :=
  ∀ ⦃P : (curve N).Point⦄ ⦃x : ℚ⦄, HasX P x → ∀ n : ℕ, n • P ≠ 0 →
    ((curve N).ΨSq n).eval x ≠ 0 ∧
      HasX (n • P) (((curve N).Φ n).eval x / ((curve N).ΨSq n).eval x)

theorem eval_neg_mul (p : ℚ[X]) (z : ℚ) : p.eval (-N * z) = (sub (-N) p).eval z := by
  simp [eval_comp]

theorem eval_E1Q_Φ (k : ℕ) (z : ℚ) : (E1Q.Φ k).eval z = aeval z (cΦ k) := by
  rw [← E1_map, map_Φ, eval_map, aeval_def, algebraMap_int_eq, cΦ]

theorem eval_E1Q_ΨSq (k : ℕ) (z : ℚ) : (E1Q.ΨSq k).eval z = aeval z (cΨSq k) := by
  rw [← E1_map, map_ΨSq, eval_map, aeval_def, algebraMap_int_eq, cΨSq]

/-- Equation (18): `t(kG) = P_k(z)/Q_k(z)`, i.e. `X(kG) = −N · P_k(z)/Q_k(z)`. -/
theorem hasX_nsmul_eq (hdp : DivPolyX N) (hN : 0 < N) {G : (curve N).Point} (hG : NonTors G)
    {z : ℚ} (hz : HasX G (-N * z)) {k : ℕ} (hk : 0 < k) :
    aeval z (cΨSq k) ≠ 0 ∧ HasX (k • G) (-N * (aeval z (cΦ k) / aeval z (cΨSq k))) := by
  obtain ⟨h0, h⟩ := hdp hz k (hG k hk)
  simp only [eval_neg_mul, sub_ΨSq, sub_Φ, eval_mul, eval_pow, eval_C, eval_E1Q_ΨSq,
    eval_E1Q_Φ] at h0 h
  have hq := right_ne_zero_of_mul h0
  refine ⟨hq, ?_⟩
  convert h using 1
  have hN' : (-N) ^ (k ^ 2) = (-N) ^ (k ^ 2 - 1) * -N := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hk)]
  rw [hN']
  field_simp [left_ne_zero_of_mul h0]

theorem pos_of_hasX {x t : ℚ} (hN : 0 < N) (hx : x = -N * t) (h1 : -N < x) (h2 : x < 0) :
    0 < t ∧ t < 1 := by
  subst hx
  constructor <;> nlinarith

/-- Translation by `T` in the coordinate `t = −X/N` is `t ↦ (1 − t)/(1 + t)`. -/
theorem hasX_add_T_frac (hN : 0 < N) {P : (curve N).Point} {n d : ℚ} (hd : d ≠ 0)
    (h : HasX P (-N * (n / d))) (h1 : -N < -N * (n / d)) (h2 : -N * (n / d) < 0) :
    d + n ≠ 0 ∧ HasX (P + T hN.ne') (-N * ((d - n) / (d + n))) ∧
      -N < -N * ((d - n) / (d + n)) ∧ -N * ((d - n) / (d + n)) < 0 := by
  obtain ⟨ht0, ht1⟩ := pos_of_hasX hN rfl h1 h2
  have hdn : d + n ≠ 0 := by
    intro h0
    rw [show n = -d by linear_combination h0, neg_div, div_self hd] at ht0
    norm_num at ht0
  have hx : -N * (n / d) ≠ N := by intro h; linarith
  have key : (d - n) / (d + n) = (1 - n / d) / (1 + n / d) := by field_simp
  refine ⟨hdn, ?_, ?_, ?_⟩
  · convert h.add_T hN.ne' hx using 1
    rw [eq_div_iff (by linarith : -N * (n / d) - N < 0).ne]
    field_simp
    ring
  · rw [key]
    have : 0 < 1 + n / d := by linarith
    rw [neg_mul, neg_lt_neg_iff, mul_lt_iff_lt_one_right hN, div_lt_one this]
    linarith
  · rw [key]
    have : 0 < 1 + n / d := by linarith
    have : 0 < (1 - n / d) / (1 + n / d) := div_pos (by linarith) this
    nlinarith

/-- Translation by `S` in the coordinate `t = −X/N` is `t ↦ −1/t`. -/
theorem hasX_add_S_frac (hN : 0 < N) {P : (curve N).Point} {n d : ℚ} (hn : n ≠ 0) (hd : d ≠ 0)
    (h : HasX P (-N * (n / d))) (h1 : N < -N * (n / d)) :
    HasX (P + S hN.ne') (-N * (-d / n)) ∧ -N < -N * (-d / n) ∧ -N * (-d / n) < 0 := by
  have hx : -N * (n / d) ≠ 0 := by intro h; linarith
  have key : -N * (-d / n) = -N ^ 2 / (-N * (n / d)) := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [key, add_comm]
    exact h.S_add hN.ne' hx
  · rw [key, lt_div_iff₀ (by linarith)]
    nlinarith
  · rw [key]
    exact div_neg_of_neg_of_pos (by nlinarith) (by linarith)

/-- The entry `A_k(G)` (label `false`) or `B_k(G)` (label `true`). -/
def pt (hN : N ≠ 0) (L : Bool) (k : ℕ) (G : (curve N).Point) : (curve N).Point :=
  cond L (B hN k G) (A hN k G)

/-- **Table (20).** With `z = t(G) ∈ (0, 1)`, the entry `A_k(G)` or `B_k(G)` has abscissa
`t = num(z)/den(z)` in `(0, 1)`. -/
theorem hasX_pt (hdp : DivPolyX N) (hN : 0 < N) {G : (curve N).Point} (hG : NonTors G) {z : ℚ}
    (hz : HasX G (-N * z)) (hz0 : 0 < z) (hz1 : z < 1) (L : Bool) {k : ℕ} (hk : 0 < k) :
    ∃ x, HasX (pt hN.ne' L k G) x ∧ aeval z (den L k) ≠ 0 ∧
      x = -N * (aeval z (num L k) / aeval z (den L k)) ∧ -N < x ∧ x < 0 := by
  obtain ⟨hq, hkG⟩ := hasX_nsmul_eq hdp hN hG hz hk
  set p := aeval z (cΦ k)
  set q := aeval z (cΨSq k)
  obtain ⟨x, hx, hodd, heven⟩ := hasX_nsmul hN hG hz (by nlinarith) (by nlinarith) k hk
  rw [hx.unique hkG] at hodd heven
  rcases Nat.even_or_odd k with he | ho
  · have hXpos := heven he
    have hp : p ≠ 0 := by intro h; rw [h, zero_div, mul_zero] at hXpos; linarith
    obtain ⟨hS, hS1, hS2⟩ := hasX_add_S_frac hN hp hq hkG hXpos
    have hA : A hN.ne' k G = k • G + S hN.ne' := by simp [A, he]
    cases L
    · refine ⟨_, by simpa [pt, hA] using hS, by simpa [den, he] using hp, ?_, hS1, hS2⟩
      simp [num, den, he, p, q]
    · obtain ⟨hdn, hT, hT1, hT2⟩ := hasX_add_T_frac hN hp hS hS1 hS2
      refine ⟨_, by simpa [pt, B, hA] using hT, ?_, ?_, hT1, hT2⟩
      · simpa [den, he, p, q, sub_eq_add_neg] using hdn
      · simp only [num, den, he, ↓reduceIte, map_add, map_sub]
        ring
  · obtain ⟨h1, h2⟩ := hodd ho
    have hA : A hN.ne' k G = k • G := by simp [A, Nat.not_even_iff_odd.mpr ho]
    cases L
    · refine ⟨_, by simpa [pt, hA] using hkG, by simpa [den, Nat.not_even_iff_odd.mpr ho] using hq,
        ?_, h1, h2⟩
      simp [num, den, Nat.not_even_iff_odd.mpr ho, p, q]
    · obtain ⟨hdn, hT, hT1, hT2⟩ := hasX_add_T_frac hN hq hkG h1 h2
      refine ⟨_, by simpa [pt, B, hA] using hT, ?_, ?_, hT1, hT2⟩
      · simpa [den, Nat.not_even_iff_odd.mpr ho, p, q, add_comm] using hdn
      · simp [num, den, Nat.not_even_iff_odd.mpr ho, p, q, add_comm]

/-- **Asiryan, Lemma 2.** A positive configuration made of entries `A_{kᵢ}(G)`, `B_{kᵢ}(G)` is
never excluded: otherwise `z = t(G)` would be a root in `(0, 1)` of the polynomial `Z` of
equation (21), whose top coefficient is `±1`. -/
theorem not_excluded (hdp : DivPolyX N) (hN : 0 < N) {G : (curve N).Point} (hG : NonTors G)
    {z : ℚ} (hz : HasX G (-N * z)) (hz0 : 0 < z) (hz1 : z < 1) {L₁ L₂ L₃ : Bool} {k₁ k₂ k₃ : ℕ}
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃) {x₁ x₂ x₃ : ℚ}
    (h₁ : HasX (pt hN.ne' L₁ k₁ G) x₁) (h₂ : HasX (pt hN.ne' L₂ k₂ G) x₂)
    (h₃ : HasX (pt hN.ne' L₃ k₃ G) x₃) (hc : IsConfig N x₁ x₂ x₃) :
    ¬Excluded L₁ (decide (Even k₁)) L₂ (decide (Even k₂)) L₃ (decide (Even k₃)) := by
  intro hex
  apply aeval_bigZ_ne_zero hk₁ hk₂ hk₃ hex hz0 hz1
  obtain ⟨y₁, g₁, hd₁, e₁, -⟩ := hasX_pt hdp hN hG hz hz0 hz1 L₁ hk₁
  obtain ⟨y₂, g₂, hd₂, e₂, -⟩ := hasX_pt hdp hN hG hz hz0 hz1 L₂ hk₂
  obtain ⟨y₃, g₃, hd₃, e₃, -⟩ := hasX_pt hdp hN hG hz hz0 hz1 L₃ hk₃
  have hcomp := hc.compat
  rw [h₁.unique g₁, h₂.unique g₂, h₃.unique g₃, e₁, e₂, e₃] at hcomp
  simp only [bigZ, map_add, map_sub, map_mul]
  field_simp at hcomp
  have hN2 : N ^ 2 ≠ 0 := by positivity
  apply mul_left_cancel₀ hN2
  linear_combination N ^ 2 * hcomp

/-! ### Lemma 3: changing the base point -/

/-- The label of an entry after `G ↦ G + T`: odd entries trade sequences, even ones stay. The
second argument says whether the index is even. -/
def swapB (L e : Bool) : Bool := if e then L else !L

theorem swapB_swapB (L e : Bool) : swapB (swapB L e) e = L := by
  cases L <;> cases e <;> rfl

/-- `G ↦ G + T` (Proposition 2): `pt L k (G + T) = pt (swapB L (k even)) k G`. -/
theorem pt_add_T (hN : N ≠ 0) (L : Bool) (k : ℕ) (G : (curve N).Point) :
    pt hN L k (G + T hN) = pt hN (swapB L (decide (Even k))) k G := by
  by_cases he : Even k
  · cases L <;> simp [pt, swapB, he, A_add_T_of_even, B_add_T_of_even]
  · have ho := Nat.not_even_iff_odd.mp he
    cases L <;> simp [pt, swapB, he, A_add_T_of_odd hN ho, B_add_T_of_odd hN ho]

theorem nsmul_S_of_even (hN : N ≠ 0) {k : ℕ} (hk : Even k) : k • S hN = 0 := by
  obtain ⟨m, rfl⟩ := hk
  rw [add_nsmul, ← nsmul_add, S_add_S, nsmul_zero]

theorem nsmul_S_of_odd (hN : N ≠ 0) {k : ℕ} (hk : Odd k) : k • S hN = S hN := by
  obtain ⟨m, rfl⟩ := hk
  rw [add_nsmul, nsmul_S_of_even hN (even_two_mul m), zero_add, one_nsmul]

/-- `G ↦ 2G + S` (equation (23)): `A_k(2G + S) = A_{2k}(G)` and `B_k(2G + S) = B_{2k}(G)`. -/
theorem pt_two_nsmul_add_S (hN : N ≠ 0) (L : Bool) (k : ℕ) (G : (curve N).Point) :
    pt hN L k (2 • G + S hN) = pt hN L (2 * k) G := by
  have hA : A hN k (2 • G + S hN) = A hN (2 * k) G := by
    unfold A
    rw [nsmul_add, ← mul_nsmul', ite_eq_left (even_two_mul k)]
    by_cases he : Even k
    · rw [nsmul_S_of_even hN he, ite_eq_left he, add_zero, mul_comm]
    · rw [nsmul_S_of_odd hN (Nat.not_even_iff_odd.mp he), ite_eq_right he, add_zero, mul_comm]
  cases L
  · exact hA
  · simp only [pt, Bool.cond_true, B, hA]

theorem NonTors.add {G R : (curve N).Point} (hG : NonTors G) (hR : R + R = 0) :
    NonTors (G + R) := by
  intro n hn h
  apply hG (2 * n) (by omega)
  have e : n • (G + R) + n • (G + R) = (2 * n) • G := by
    rw [← nsmul_add, add_add_add_comm, hR, add_zero, nsmul_add, two_mul, add_nsmul]
  rw [← e, h, add_zero]

theorem NonTors.two_nsmul {G : (curve N).Point} (hG : NonTors G) : NonTors (2 • G) := by
  intro n hn h
  apply hG (n * 2) (by omega)
  rwa [smul_smul] at h

theorem NonTors.ne_zero {G : (curve N).Point} (hG : NonTors G) : G ≠ 0 := by
  simpa using hG 1 one_pos

/-- After `G ↦ G + T` the base point still has `−N < X < 0`. -/
theorem hasX_add_T_of_mem (hN : 0 < N) {G : (curve N).Point} {x : ℚ} (h : HasX G x)
    (h1 : -N < x) (h2 : x < 0) : ∃ x', HasX (G + T hN.ne') x' ∧ -N < x' ∧ x' < 0 := by
  have e : x = -N * ((-x / N) / 1) := by field_simp
  rw [e] at h h1 h2
  obtain ⟨-, h', h1', h2'⟩ := hasX_add_T_frac hN one_ne_zero h h1 h2
  exact ⟨_, h', h1', h2'⟩

/-- After `G ↦ 2G + S` the base point still has `−N < X < 0`. -/
theorem hasX_two_nsmul_add_S (hN : 0 < N) {G : (curve N).Point} (hG : NonTors G) {x : ℚ}
    (h : HasX G x) (h1 : -N < x) (h2 : x < 0) :
    ∃ x', HasX (2 • G + S hN.ne') x' ∧ -N < x' ∧ x' < 0 := by
  obtain ⟨y, hy, -, hev⟩ := hasX_nsmul hN hG h h1 h2 2 two_pos
  have hy' := hev even_two
  have e : y = -N * ((-y / N) / 1) := by field_simp
  rw [e] at hy hy'
  obtain ⟨h', h1', h2'⟩ := hasX_add_S_frac hN (by
    intro h0; rw [h0, zero_div, mul_zero] at hy'; linarith) one_ne_zero hy hy'
  exact ⟨_, h', h1', h2'⟩

/-- The conclusion of `RankOneReduction`: the pattern (22). -/
def Pattern (N : ℚ) (hN : 0 < N) : Prop :=
  ∃ (G : (curve N).Point) (a b c : ℕ) (y₁ y₂ y₃ : ℚ), IsConfig N y₁ y₂ y₃ ∧
    HasX (a • G) y₁ ∧ HasX (b • G + T hN.ne') y₂ ∧ HasX (c • G + U hN.ne') y₃ ∧
    Odd a ∧ Odd b ∧ Even c ∧ 0 < c

theorem IsConfig.swap₁₂ {x₁ x₂ x₃ : ℚ} (h : IsConfig N x₁ x₂ x₃) : IsConfig N x₂ x₁ x₃ :=
  ⟨h.pos, h.lt₂, h.lt₁, h.lt₃, h.neg₂, h.neg₁, h.neg₃, by linear_combination h.compat⟩

theorem IsConfig.swap₂₃ {x₁ x₂ x₃ : ℚ} (h : IsConfig N x₁ x₂ x₃) : IsConfig N x₁ x₃ x₂ :=
  ⟨h.pos, h.lt₁, h.lt₃, h.lt₂, h.neg₁, h.neg₃, h.neg₂, by linear_combination h.compat⟩

/-- An odd `A` entry, an odd `B` entry and an even `B` entry form the pattern (22). -/
theorem pattern_of (hN : 0 < N) {G : (curve N).Point} {a b c : ℕ} {y₁ y₂ y₃ : ℚ}
    (h₁ : HasX (pt hN.ne' false a G) y₁) (h₂ : HasX (pt hN.ne' true b G) y₂)
    (h₃ : HasX (pt hN.ne' true c G) y₃) (ha : Odd a) (hb : Odd b) (hc : Even c) (hc0 : 0 < c)
    (hcfg : IsConfig N y₁ y₂ y₃) : Pattern N hN := by
  refine ⟨G, a, b, c, y₁, y₂, y₃, hcfg, ?_, ?_, ?_, ha, hb, hc, hc0⟩
  · simpa [pt, A, Nat.not_even_iff_odd.mpr ha] using h₁
  · simpa [pt, B, A, Nat.not_even_iff_odd.mpr hb] using h₂
  · simpa [pt, B, A, hc, add_assoc, S_add_T] using h₃

/-- Every triple of entries is excluded by Lemma 2, or becomes excluded after `G ↦ G + T`, or is
(a permutation of) the pattern (22), or has only even indices. -/
theorem classify (L₁ e₁ L₂ e₂ L₃ e₃ : Bool) :
    Excluded L₁ e₁ L₂ e₂ L₃ e₃ ∨
    Excluded (swapB L₁ e₁) e₁ (swapB L₂ e₂) e₂ (swapB L₃ e₃) e₃ ∨
    ((L₁, e₁, L₂, e₂, L₃, e₃) = (false, false, true, false, true, true) ∨
      (L₁, e₁, L₂, e₂, L₃, e₃) = (false, false, true, true, true, false) ∨
      (L₁, e₁, L₂, e₂, L₃, e₃) = (true, false, false, false, true, true) ∨
      (L₁, e₁, L₂, e₂, L₃, e₃) = (true, false, true, true, false, false) ∨
      (L₁, e₁, L₂, e₂, L₃, e₃) = (true, true, false, false, true, false) ∨
      (L₁, e₁, L₂, e₂, L₃, e₃) = (true, true, true, false, false, false)) ∨
    (e₁ = true ∧ e₂ = true ∧ e₃ = true) := by
  cases L₁ <;> cases e₁ <;> cases L₂ <;> cases e₂ <;> cases L₃ <;> cases e₃ <;>
    simp [Excluded, swapB, topZ, topNum, topDen]

/-- **Asiryan, Lemma 3**, the descent: a positive configuration of entries `A_{kᵢ}(G)`, `B_{kᵢ}(G)`
with `−N < X(G) < 0` can be brought to the pattern (22). Induction on `k₁ + k₂ + k₃`, halving all
indices by `G ↦ 2G + S` when they are all even. -/
theorem pattern_of_pt (hdp : DivPolyX N) (hN : 0 < N) (s : ℕ) :
    ∀ (G : (curve N).Point) (xG : ℚ) (L₁ L₂ L₃ : Bool) (k₁ k₂ k₃ : ℕ) (x₁ x₂ x₃ : ℚ),
      k₁ + k₂ + k₃ ≤ s → NonTors G → HasX G xG → -N < xG → xG < 0 →
      0 < k₁ → 0 < k₂ → 0 < k₃ → HasX (pt hN.ne' L₁ k₁ G) x₁ → HasX (pt hN.ne' L₂ k₂ G) x₂ →
      HasX (pt hN.ne' L₃ k₃ G) x₃ → IsConfig N x₁ x₂ x₃ → Pattern N hN := by
  induction s with
  | zero => intros; omega
  | succ s ih =>
  intro G xG L₁ L₂ L₃ k₁ k₂ k₃ x₁ x₂ x₃ hs hG hxG hG1 hG2 hk₁ hk₂ hk₃ h₁ h₂ h₃ hc
  have hz : HasX G (-N * (-xG / N)) := by convert hxG using 1; field_simp
  have hz0 : 0 < -xG / N := div_pos (by linarith) hN
  have hz1 : -xG / N < 1 := (div_lt_one hN).mpr (by linarith)
  rcases classify L₁ (decide (Even k₁)) L₂ (decide (Even k₂)) L₃ (decide (Even k₃)) with
    hex | hex | hfin | ⟨he₁, he₂, he₃⟩
  · exact absurd hex (not_excluded hdp hN hG hz hz0 hz1 hk₁ hk₂ hk₃ h₁ h₂ h₃ hc)
  · -- after `G ↦ G + T` the triple is excluded
    obtain ⟨x', hx', h1', h2'⟩ := hasX_add_T_of_mem hN hxG hG1 hG2
    have hz' : HasX (G + T hN.ne') (-N * (-x' / N)) := by convert hx' using 1; field_simp
    have e : ∀ L k, pt hN.ne' L k G = pt hN.ne' (swapB L (decide (Even k))) k (G + T hN.ne') :=
      fun L k ↦ by rw [pt_add_T, swapB_swapB]
    rw [e] at h₁ h₂ h₃
    exact absurd hex (not_excluded hdp hN (hG.add (T_add_T hN.ne')) hz'
      (div_pos (by linarith) hN) ((div_lt_one hN).mpr (by linarith)) hk₁ hk₂ hk₃ h₁ h₂ h₃ hc)
  · have ev : ∀ k : ℕ, decide (Even k) = true → Even k := fun k h ↦ of_decide_eq_true h
    have od : ∀ k : ℕ, decide (Even k) = false → Odd k :=
      fun k h ↦ Nat.not_even_iff_odd.mp (of_decide_eq_false h)
    simp only [Prod.mk.injEq] at hfin
    rcases hfin with ⟨rfl, o₁, rfl, o₂, rfl, o₃⟩ | ⟨rfl, o₁, rfl, o₂, rfl, o₃⟩ |
      ⟨rfl, o₁, rfl, o₂, rfl, o₃⟩ | ⟨rfl, o₁, rfl, o₂, rfl, o₃⟩ | ⟨rfl, o₁, rfl, o₂, rfl, o₃⟩ |
      ⟨rfl, o₁, rfl, o₂, rfl, o₃⟩
    · exact pattern_of hN h₁ h₂ h₃ (od _ o₁) (od _ o₂) (ev _ o₃) hk₃ hc
    · exact pattern_of hN h₁ h₃ h₂ (od _ o₁) (od _ o₃) (ev _ o₂) hk₂ hc.swap₂₃
    · exact pattern_of hN h₂ h₁ h₃ (od _ o₂) (od _ o₁) (ev _ o₃) hk₃ hc.swap₁₂
    · exact pattern_of hN h₃ h₁ h₂ (od _ o₃) (od _ o₁) (ev _ o₂) hk₂ hc.swap₂₃.swap₁₂
    · exact pattern_of hN h₂ h₃ h₁ (od _ o₂) (od _ o₃) (ev _ o₁) hk₁ hc.swap₁₂.swap₂₃
    · exact pattern_of hN h₃ h₂ h₁ (od _ o₃) (od _ o₂) (ev _ o₁) hk₁ hc.swap₂₃.swap₁₂.swap₂₃
  · -- all indices even: halve them with `G ↦ 2G + S`
    obtain ⟨m₁, rfl⟩ := of_decide_eq_true he₁
    obtain ⟨m₂, rfl⟩ := of_decide_eq_true he₂
    obtain ⟨m₃, rfl⟩ := of_decide_eq_true he₃
    obtain ⟨x', hx', h1', h2'⟩ := hasX_two_nsmul_add_S hN hG hxG hG1 hG2
    simp only [← two_mul, ← pt_two_nsmul_add_S] at h₁ h₂ h₃
    exact ih _ x' L₁ L₂ L₃ m₁ m₂ m₃ x₁ x₂ x₃ (by omega)
      (hG.two_nsmul.add (S_add_S hN.ne')) hx' h1' h2' (by omega) (by omega) (by omega)
      h₁ h₂ h₃ hc

/-! ### From a rank-one subgroup to entries `A_k(G)`, `B_k(G)` -/

/-- **Hypothesis (Asiryan, Remark 1):** every rational torsion point of `E_N` has order at
most `2`. Proved for every `N ≠ 0` in `Torsion.lean` (`torsionTwo`), by reduction modulo primes
`p ≡ 3 (mod 4)`. -/
def TorsionTwo (N : ℚ) : Prop :=
  ∀ (P : (curve N).Point) (n : ℕ), 0 < n → n • P = 0 → P + P = 0

theorem two_torsion_add {R R' : (curve N).Point} (hR : R + R = 0) (hR' : R' + R' = 0) (m : ℕ) :
    (m • R + R') + (m • R + R') = 0 := by
  rw [add_add_add_comm, ← nsmul_add, hR, nsmul_zero, zero_add, hR']

/-- Each `Qᵢ = kᵢG + Rᵢ` can be written with a positive index, after negating `Qᵢ`. -/
theorem exists_pos_index (hN : 0 < N) {G Q R : (curve N).Point} {k : ℤ} {x : ℚ}
    (hQ : HasX Q x) (h1 : -N < x) (h2 : x < 0) (hR : R + R = 0) (e : Q = k • G + R) :
    ∃ m : ℕ, 0 < m ∧ ∃ R' : (curve N).Point, R' + R' = 0 ∧ HasX (m • G + R') x := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero, zero_smul, zero_add] at e
      exact absurd (e ▸ hR) (hQ.add_self_ne_zero hN h1 h2)
    · exact ⟨m, hm, R, hR, by rwa [e, natCast_zsmul] at hQ⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero, neg_zero, zero_smul, zero_add] at e
      exact absurd (e ▸ hR) (hQ.add_self_ne_zero hN h1 h2)
    · refine ⟨m, hm, -R, by rw [← neg_add, hR, neg_zero], ?_⟩
      have := hQ.neg
      rwa [e, neg_add, neg_smul, neg_neg, natCast_zsmul] at this

/-- The base point can be moved by a `2`-torsion point to get `−N < X(G) < 0`. -/
theorem exists_good_base (hN : 0 < N) {G : (curve N).Point} (hG : NonTors G) :
    ∃ G' R₀ x, NonTors G' ∧ HasX G' x ∧ -N < x ∧ x < 0 ∧ R₀ + R₀ = 0 ∧ G = G' + R₀ := by
  obtain ⟨x, hx⟩ := exists_hasX hG.ne_zero
  have hne := hG.hasX_ne hN.ne' one_pos (by rwa [one_smul])
  have h0 : x ≠ 0 := fun h ↦ hne (by rw [h]; ring)
  have hN₁ : x ≠ N := fun h ↦ hne (by rw [h]; ring)
  have hN₂ : x ≠ -N := fun h ↦ hne (by rw [h]; ring)
  rcases hx.region hN with h | ⟨h1, h2⟩
  · replace h := lt_of_le_of_ne h (Ne.symm hN₁)
    have e : x = -N * ((-x / N) / 1) := by field_simp
    rw [e] at hx h
    obtain ⟨h', h1', h2'⟩ := hasX_add_S_frac hN (by
      intro h0; rw [h0, zero_div, mul_zero] at h; linarith) one_ne_zero hx h
    exact ⟨G + S hN.ne', S hN.ne', _, hG.add (S_add_S _), h', h1', h2', S_add_S _,
      by rw [add_assoc, S_add_S, add_zero]⟩
  · exact ⟨G, 0, x, hG, hx, lt_of_le_of_ne h1 (Ne.symm hN₂), lt_of_le_of_ne h2 h0, by simp,
      by simp⟩

/-- With `−N < X(G) < 0`, a translate `mG + R` by `2`-torsion with `−N < X < 0` is `A_m(G)` or
`B_m(G)`: the other two translates have positive abscissa. -/
theorem exists_pt (hN : 0 < N) {G R : (curve N).Point} (hG : NonTors G) {xG : ℚ}
    (hxG : HasX G xG) (hG1 : -N < xG) (hG2 : xG < 0) {m : ℕ} (hm : 0 < m) (hR : R + R = 0)
    {x : ℚ} (h : HasX (m • G + R) x) (h2 : x < 0) : ∃ L, m • G + R = pt hN.ne' L m G := by
  obtain ⟨x₀, hx₀, hodd, heven⟩ := hasX_nsmul hN hG hxG hG1 hG2 m hm
  have hA : A hN.ne' m G = m • G + if Even m then S hN.ne' else 0 := rfl
  rcases two_torsion hN.ne' hR with rfl | rfl | rfl | rfl
  · rcases Nat.even_or_odd m with he | ho
    · rw [add_zero] at h
      linarith [heven he, h.unique hx₀]
    · exact ⟨false, by simp [pt, hA, Nat.not_even_iff_odd.mpr ho]⟩
  · rcases Nat.even_or_odd m with he | ho
    · exact ⟨false, by simp [pt, hA, he]⟩
    · obtain ⟨h1', h2'⟩ := hodd ho
      have := (hx₀.S_add hN.ne' h2'.ne).unique (by rwa [add_comm] at h)
      have : 0 < -N ^ 2 / x₀ := div_pos_of_neg_of_neg (by nlinarith) h2'
      linarith
  · rcases Nat.even_or_odd m with he | ho
    · have hx := heven he
      have := (hx₀.add_T hN.ne' (by linarith)).unique h
      have : 0 < N * (x₀ + N) / (x₀ - N) := div_pos (by nlinarith) (by linarith)
      linarith
    · exact ⟨true, by simp [pt, B, hA, Nat.not_even_iff_odd.mpr ho]⟩
  · rcases Nat.even_or_odd m with he | ho
    · exact ⟨true, by simp [pt, B, hA, he, add_assoc, S_add_T]⟩
    · obtain ⟨h1', h2'⟩ := hodd ho
      have := (hx₀.add_U hN.ne' (by linarith)).unique h
      have : 0 < -N * (x₀ - N) / (x₀ + N) := div_pos (by nlinarith) (by linarith)
      linarith

/-- **Asiryan, Lemmas 2 and 3**: `RankOneReduction` holds, given the division-polynomial
formula and the torsion of `E_N`. -/
theorem rankOneReduction (hN : 0 < N) (hdp : DivPolyX N) (htor : TorsionTwo N) :
    RankOneReduction N hN := by
  intro x₁ x₂ x₃ Q₁ Q₂ Q₃ hc h₁ h₂ h₃ ⟨G, k₁, k₂, k₃, R₁, R₂, R₃, hR₁, hR₂, hR₃, e₁, e₂, e₃⟩
  have hG : NonTors G := by
    intro n hn hnG
    apply h₁.add_self_ne_zero hN hc.lt₁ hc.neg₁
    apply htor Q₁ (2 * n) (by omega)
    rw [e₁, nsmul_add, smul_comm, mul_nsmul', hnG, nsmul_zero, zsmul_zero, zero_add, mul_comm,
      mul_nsmul', two_nsmul, hR₁, nsmul_zero]
  obtain ⟨m₁, hm₁, R₁', hR₁', g₁⟩ := exists_pos_index hN h₁ hc.lt₁ hc.neg₁ hR₁ e₁
  obtain ⟨m₂, hm₂, R₂', hR₂', g₂⟩ := exists_pos_index hN h₂ hc.lt₂ hc.neg₂ hR₂ e₂
  obtain ⟨m₃, hm₃, R₃', hR₃', g₃⟩ := exists_pos_index hN h₃ hc.lt₃ hc.neg₃ hR₃ e₃
  obtain ⟨G', R₀, xG, hG', hxG, hG1, hG2, hR₀, rfl⟩ := exists_good_base hN hG
  have shift : ∀ (m : ℕ) (R : (curve N).Point), m • (G' + R₀) + R = m • G' + (m • R₀ + R) :=
    fun m R ↦ by rw [nsmul_add, add_assoc]
  rw [shift] at g₁ g₂ g₃
  obtain ⟨L₁, f₁⟩ := exists_pt hN hG' hxG hG1 hG2 hm₁ (two_torsion_add hR₀ hR₁' m₁) g₁ hc.neg₁
  obtain ⟨L₂, f₂⟩ := exists_pt hN hG' hxG hG1 hG2 hm₂ (two_torsion_add hR₀ hR₂' m₂) g₂ hc.neg₂
  obtain ⟨L₃, f₃⟩ := exists_pt hN hG' hxG hG1 hG2 hm₃ (two_torsion_add hR₀ hR₃' m₃) g₃ hc.neg₃
  rw [f₁] at g₁
  rw [f₂] at g₂
  rw [f₃] at g₃
  exact pattern_of_pt hdp hN _ G' xG L₁ L₂ L₃ m₁ m₂ m₃ x₁ x₂ x₃ le_rfl hG' hxG hG1 hG2 hm₁ hm₂
    hm₃ g₁ g₂ g₃ hc

/-- **Asiryan, Theorem 1 (rank-one case)**, now conditional only on the division-polynomial
formula, the torsion of `E_N` and Ingram's primitive-divisor step. -/
theorem not_rankOne_of {x₁ x₂ x₃ : ℚ} (hc : IsConfig N x₁ x₂ x₃) (hdp : DivPolyX N)
    (htor : TorsionTwo N) (hprim : PrimitiveDivisorStep N hc.pos)
    {Q₁ Q₂ Q₃ : (curve N).Point} (h₁ : HasX Q₁ x₁) (h₂ : HasX Q₂ x₂) (h₃ : HasX Q₃ x₃) :
    ¬InRankOne Q₁ Q₂ Q₃ :=
  not_rankOne hc (rankOneReduction hc.pos hdp htor) hprim h₁ h₂ h₃

end PerfectCuboid.CongruentRank
