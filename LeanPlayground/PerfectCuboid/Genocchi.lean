module

public import LeanPlayground.PerfectCuboid.CongruentNumber
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Genocchi's theorems on congruent numbers

**Theorem (Genocchi, 1855).** A prime `p ≡ 3 (mod 8)` is not a congruent number, and neither is
`2p` for a prime `p ≡ 5 (mod 8)`.

Both are proved by Fermat's descent (`FermatTriangle.lean`), with one change. A primitive right
triangle `(r² − s², 2rs, r² + s²)` of area `c w²` gives `r s (r − s)(r + s) = c w²` with the four
factors pairwise coprime. For `c = 1` all four are squares. For `c = p` or `2p` the prime `p` sits
in exactly one factor (`four_factor`), so there are four cases. Three of them die modulo `p`,
because `−1`, `2` or `−2` is not a square mod `p`, or modulo `8`. The fourth gives a smaller
triangle of the same area class, exactly as in Fermat's descent.

## Main results

* `not_isCongruent_prime_three_mod_eight`: a prime `p ≡ 3 (mod 8)` is not congruent.
* `not_isCongruent_two_mul_prime_five_mod_eight`: `2p` is not congruent for a prime
  `p ≡ 5 (mod 8)`.
* `ne_prime_mul_sq_three_mod_eight`, `ne_two_mul_prime_mul_sq_five_mod_eight`: the integer
  forms, `r s (r − s)(r + s) ≠ p w²` (respectively `2p w²`) for coprime `r > s > 0` of opposite
  parity.

Mathlib has quadratic reciprocity and its supplements (`ZMod.exists_sq_eq_two_iff`,
`ZMod.exists_sq_eq_neg_two_iff`, `ZMod.exists_sq_eq_neg_one_iff`), but no congruent numbers.

## Why it matters for perfect cuboids

`CongruentCharacters.lean` turns every body cuboid into a congruent number
`(x + u)(x + v)(g + u)(g + v)`, one for each edge of a perfect cuboid. Genocchi's theorems then
say that none of these three numbers is `p m²` with `p ≡ 3 (mod 8)` or `2p m²` with
`p ≡ 5 (mod 8)`.
-/

@[expose] public section

namespace FermatTriangle

/-! ### Splitting `p w²` among coprime factors -/

/-- If `a b = p w²` with `a, b` coprime and positive and `p > 0` prime, then one of `a, b` is
`p` times a square and the other is a square. -/
theorem sq_split {p a b w : ℤ} (hp : Prime p) (hp0 : 0 < p) (hab : IsCoprime a b) (ha : 0 < a)
    (hb : 0 < b) (h : a * b = p * w ^ 2) :
    (∃ A B : ℤ, 0 < A ∧ 0 < B ∧ a = p * A ^ 2 ∧ b = B ^ 2) ∨
      (∃ A B : ℤ, 0 < A ∧ 0 < B ∧ a = A ^ 2 ∧ b = p * B ^ 2) := by
  rcases hp.dvd_or_dvd (⟨w ^ 2, h⟩ : p ∣ a * b) with ⟨a', rfl⟩ | ⟨b', rfl⟩
  · have ha' : 0 < a' := pos_of_mul_pos_right ha hp0.le
    have h' : a' * b = w ^ 2 := mul_left_cancel₀ hp0.ne' (by linear_combination h)
    obtain ⟨A, B, hA, hB, rfl, rfl⟩ :=
      exists_sq_sq_eq_of_isCoprime (hab.of_mul_left_right) h' ha' hb
    exact Or.inl ⟨A, B, hA, hB, rfl, rfl⟩
  · have hb' : 0 < b' := pos_of_mul_pos_right hb hp0.le
    have h' : a * b' = w ^ 2 := mul_left_cancel₀ hp0.ne' (by linear_combination h)
    obtain ⟨A, B, hA, hB, rfl, rfl⟩ :=
      exists_sq_sq_eq_of_isCoprime (hab.of_mul_right_right) h' ha hb'
    exact Or.inr ⟨A, B, hA, hB, rfl, rfl⟩

/-- Four pairwise coprime positive factors with product `p w²`: `p` divides exactly one of them,
that one is `p` times a square, and the other three are squares. -/
theorem four_factor {p F₁ F₂ F₃ F₄ w : ℤ} (hp : Prime p) (hp0 : 0 < p)
    (h12 : IsCoprime F₁ F₂) (h13 : IsCoprime F₁ F₃) (h14 : IsCoprime F₁ F₄)
    (h23 : IsCoprime F₂ F₃) (h24 : IsCoprime F₂ F₄) (h34 : IsCoprime F₃ F₄)
    (h1 : 0 < F₁) (h2 : 0 < F₂) (h3 : 0 < F₃) (h4 : 0 < F₄)
    (h : F₁ * F₂ * F₃ * F₄ = p * w ^ 2) :
    ∃ A B C D : ℤ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D ∧
      ((F₁ = p * A ^ 2 ∧ F₂ = B ^ 2 ∧ F₃ = C ^ 2 ∧ F₄ = D ^ 2) ∨
        (F₁ = A ^ 2 ∧ F₂ = p * B ^ 2 ∧ F₃ = C ^ 2 ∧ F₄ = D ^ 2) ∨
        (F₁ = A ^ 2 ∧ F₂ = B ^ 2 ∧ F₃ = p * C ^ 2 ∧ F₄ = D ^ 2) ∨
        (F₁ = A ^ 2 ∧ F₂ = B ^ 2 ∧ F₃ = C ^ 2 ∧ F₄ = p * D ^ 2)) := by
  have hc1 : IsCoprime F₁ (F₂ * (F₃ * F₄)) := h12.mul_right (h13.mul_right h14)
  have hc2 : IsCoprime F₂ (F₃ * F₄) := h23.mul_right h24
  rcases sq_split hp hp0 hc1 h1 (by positivity)
      (by rw [← h]; ring : F₁ * (F₂ * (F₃ * F₄)) = p * w ^ 2) with
    ⟨A, R, hA, -, rfl, hR⟩ | ⟨A, R, hA, -, rfl, hR⟩
  · -- `p ∣ F₁`: the rest is a square
    obtain ⟨B, S, hB, -, rfl, hS⟩ :=
      exists_sq_sq_eq_of_isCoprime hc2 hR h2 (by positivity)
    obtain ⟨C, D, hC, hD, rfl, rfl⟩ := exists_sq_sq_eq_of_isCoprime h34 hS h3 h4
    exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  · rcases sq_split hp hp0 hc2 h2 (by positivity) hR with
      ⟨B, S, hB, -, rfl, hS⟩ | ⟨B, S, hB, -, rfl, hS⟩
    · obtain ⟨C, D, hC, hD, rfl, rfl⟩ := exists_sq_sq_eq_of_isCoprime h34 hS h3 h4
      exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)⟩
    · rcases sq_split hp hp0 h34 h3 h4 hS with
        ⟨C, D, hC, hD, rfl, rfl⟩ | ⟨C, D, hC, hD, rfl, rfl⟩
      · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))⟩
      · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))⟩

/-! ### Non-squares modulo `p` -/

/-- If `c` is not a square mod `p` and `p ∣ x² − c y²`, then `p` divides `x` and `y`. -/
theorem dvd_of_dvd_sq_sub_mul_sq {p : ℕ} [Fact p.Prime] {c x y : ℤ}
    (hc : ¬ IsSquare (c : ZMod p)) (h : (p : ℤ) ∣ x ^ 2 - c * y ^ 2) :
    (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hy : (p : ℤ) ∣ y := by
    by_contra hy
    have hy0 : (y : ZMod p) ≠ 0 := by
      rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h0 : ((x ^ 2 - c * y ^ 2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    push_cast at h0
    apply hc
    refine ⟨(x : ZMod p) / y, ?_⟩
    field_simp
    linear_combination -h0
  refine ⟨hpr.dvd_of_dvd_pow (n := 2) ?_, hy⟩
  obtain ⟨k, hk⟩ := hy
  obtain ⟨l, hl⟩ := h
  exact ⟨l + c * p * k ^ 2, by rw [hk] at hl; linear_combination hl⟩

/-! ### Triangles and the parameters `r, s` -/

/-- A primitive right triangle `(u, v, A)` is `(r² − s², 2rs, r² + s²)` up to order: so
`u v = 2 r s (r − s)(r + s)` and `A = r² + s²`, with `r > s > 0` coprime of opposite parity. -/
theorem exists_rs {u v A : ℤ} (hu : 0 < u) (hv : 0 < v) (hA : 0 < A) (h : u ^ 2 + v ^ 2 = A ^ 2)
    (hc : IsCoprime u v) :
    ∃ r s : ℤ, 0 < s ∧ s < r ∧ IsCoprime r s ∧ Odd (r - s) ∧
      u * v = 2 * (r * s * (r - s) * (r + s)) ∧ A = r ^ 2 + s ^ 2 := by
  -- the case of an odd first leg
  have key : ∀ {u v : ℤ}, 0 < u → 0 < v → u ^ 2 + v ^ 2 = A ^ 2 → IsCoprime u v → u % 2 = 1 →
      ∃ r s : ℤ, 0 < s ∧ s < r ∧ IsCoprime r s ∧ Odd (r - s) ∧
        u * v = 2 * (r * s * (r - s) * (r + s)) ∧ A = r ^ 2 + s ^ 2 := by
    intro u v hu hv h hc hodd
    have hpt : PythagoreanTriple u v A := by unfold PythagoreanTriple; linear_combination h
    obtain ⟨m, n, rfl, rfl, rfl, hmn, hpar, hm0⟩ :=
      hpt.coprime_classification' (Int.isCoprime_iff_gcd_eq_one.mp hc) hodd hA
    have hm : 0 < m := by
      rcases hm0.lt_or_eq with hm | rfl
      · exact hm
      · simp at hv
    have hn : 0 < n := by
      by_contra hn
      rw [not_lt] at hn
      nlinarith
    have hnm : n < m := by
      by_contra hnm
      rw [not_lt] at hnm
      nlinarith
    refine ⟨m, n, hn, hnm, Int.isCoprime_iff_gcd_eq_one.mpr hmn, ?_, by ring, rfl⟩
    rw [Int.odd_iff]
    rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  rcases Int.emod_two_eq_zero_or_one u with hu2 | hu2
  · rcases Int.emod_two_eq_zero_or_one v with hv2 | hv2
    · exfalso
      have : IsUnit (2 : ℤ) :=
        hc.isUnit_of_dvd' (Int.dvd_of_emod_eq_zero hu2) (Int.dvd_of_emod_eq_zero hv2)
      rw [Int.isUnit_iff] at this
      omega
    · obtain ⟨r, s, h1, h2, h3, h4, h5, h6⟩ :=
        key hv hu (by linear_combination h) hc.symm hv2
      exact ⟨r, s, h1, h2, h3, h4, by rw [mul_comm]; exact h5, h6⟩
  · exact key hu hv h hc hu2

/-- Fermat's halving step. If `r = A²`, `r − s = C²` and `r + s = D²` are coprime squares, then
`u = (D + C)/2` and `v = (D − C)/2` form a primitive triangle with hypotenuse `A` and
`2 u v = s`. -/
theorem exists_half {r s A C D : ℤ} (hC : 0 < C) (hD : 0 < D) (hs : 0 < s) (hr : r = A ^ 2)
    (h3 : r - s = C ^ 2) (h4 : r + s = D ^ 2) (hcop : IsCoprime (r - s) (r + s)) :
    ∃ u v : ℤ, 0 < u ∧ 0 < v ∧ u ^ 2 + v ^ 2 = A ^ 2 ∧ 2 * (u * v) = s ∧ IsCoprime u v := by
  have hcd : Even (C + D) := by
    have h2 : Even (C ^ 2 + D ^ 2) := ⟨r, by linear_combination -h3 - h4⟩
    rw [Int.even_add, Int.even_pow' two_ne_zero, Int.even_pow' two_ne_zero] at h2
    exact Int.even_add.mpr h2
  obtain ⟨u, hu⟩ := hcd
  obtain ⟨v, rfl⟩ : ∃ v, D = u + v := ⟨D - u, by ring⟩
  obtain rfl : C = u - v := by omega
  have hv : 0 < v := by nlinarith
  have hu0 : 0 < u := by omega
  refine ⟨u, v, hu0, hv, ?_, ?_, ?_⟩
  · have : 2 * (u ^ 2 + v ^ 2) = 2 * A ^ 2 := by linear_combination -h3 - h4 + 2 * hr
    exact mul_left_cancel₀ two_ne_zero this
  · have : 2 * (2 * (u * v)) = 2 * s := by linear_combination h3 - h4
    exact mul_left_cancel₀ two_ne_zero this
  · apply isCoprime_of_isCoprime_add_sub
    have := hcop.symm
    rw [h3, h4] at this
    exact (this.of_isCoprime_of_dvd_left (dvd_pow_self _ two_ne_zero)).of_isCoprime_of_dvd_right
      (dvd_pow_self _ two_ne_zero)

/-- The four factors `r, s, r − s, r + s` are pairwise coprime and positive. -/
theorem four_factor_rs {p r s w : ℤ} (hp : Prime p) (hp0 : 0 < p) (hs : 0 < s) (hsr : s < r)
    (hc : IsCoprime r s) (hodd : Odd (r - s)) (h : r * s * (r - s) * (r + s) = p * w ^ 2) :
    ∃ A B C D : ℤ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D ∧
      ((r = p * A ^ 2 ∧ s = B ^ 2 ∧ r - s = C ^ 2 ∧ r + s = D ^ 2) ∨
        (r = A ^ 2 ∧ s = p * B ^ 2 ∧ r - s = C ^ 2 ∧ r + s = D ^ 2) ∨
        (r = A ^ 2 ∧ s = B ^ 2 ∧ r - s = p * C ^ 2 ∧ r + s = D ^ 2) ∨
        (r = A ^ 2 ∧ s = B ^ 2 ∧ r - s = C ^ 2 ∧ r + s = p * D ^ 2)) :=
  four_factor hp hp0 hc (isCoprime_left_sub hc) (isCoprime_left_add hc) (isCoprime_right_sub hc)
    (isCoprime_right_add hc) (isCoprime_sub_add_of_odd hc hodd) (by omega) hs (by omega)
    (by omega) h

/-! ### The descent for `p ≡ 3 (mod 8)` -/

/-- **Genocchi's descent step for `p ≡ 3 (mod 8)`.** If `r s (r − s)(r + s) = p w²`, then the
same holds for a smaller `r`. Of the four places for `p`, three die modulo `p` and the fourth is
Fermat's halving step. -/
theorem descent_three_mod_eight {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3) {r s w : ℤ} (hs : 0 < s)
    (hsr : s < r) (hc : IsCoprime r s) (hodd : Odd (r - s))
    (h : r * s * (r - s) * (r + s) = p * w ^ 2) :
    ∃ r' s' w' : ℤ, 0 < s' ∧ s' < r' ∧ IsCoprime r' s' ∧ Odd (r' - s') ∧
      r' * s' * (r' - s') * (r' + s') = p * w' ^ 2 ∧ r' < r := by
  have := Fact.mk hp
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hP0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hcop : ¬ ((p : ℤ) ∣ r ∧ (p : ℤ) ∣ s) := fun ⟨h1, h2⟩ ↦
    hP.not_isUnit (hc.isUnit_of_dvd' h1 h2)
  have hn1 : ¬ IsSquare (((-1 : ℤ)) : ZMod p) := by
    rw [Int.cast_neg, Int.cast_one, ZMod.exists_sq_eq_neg_one_iff]
    omega
  have hn2 : ¬ IsSquare (((2 : ℤ)) : ZMod p) := by
    rw [Int.cast_ofNat, ZMod.exists_sq_eq_two_iff (by omega)]
    omega
  obtain ⟨A, B, C, D, hA, hB, hC, hD, H⟩ := four_factor_rs hP hP0 hs hsr hc hodd h
  rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · -- `r = p A²`: `C² + D² = 2 p A²`, and `−1` is not a square mod `p`
    exfalso
    obtain ⟨-, k, hk⟩ := dvd_of_dvd_sq_sub_mul_sq hn1
      (⟨2 * A ^ 2, by linear_combination -h3 - h4 + 2 * h1⟩ : (p : ℤ) ∣ C ^ 2 - -1 * D ^ 2)
    exact hcop ⟨⟨A ^ 2, h1⟩, ⟨p * k ^ 2 - A ^ 2, by linear_combination h4 - h1 + (D + p * k) * hk⟩⟩
  · -- `s = p B²`: Fermat's halving step
    obtain ⟨u, v, hu, hv, huv, h2uv, hcuv⟩ :=
      exists_half hC hD hs h1 h3 h4 (isCoprime_sub_add_of_odd hc hodd)
    obtain ⟨r', s', hs', hsr', hc', hodd', hprod, hA'⟩ := exists_rs hu hv hA huv hcuv
    -- `p B² = 2 u v` is even, so `B` is even
    have hBe : Even B := by
      have : Even ((p : ℤ) * B ^ 2) := ⟨u * v, by linear_combination -h2 - h2uv⟩
      rw [Int.even_mul, Int.even_pow' two_ne_zero] at this
      refine this.resolve_left fun hpe ↦ ?_
      have : (p : ℤ) % 2 = 0 := Int.even_iff.mp hpe
      omega
    obtain ⟨B', rfl⟩ := hBe
    refine ⟨r', s', B', hs', hsr', hc', hodd', ?_, ?_⟩
    · have : 4 * (r' * s' * (r' - s') * (r' + s')) = 4 * (p * B' ^ 2) := by
        linear_combination -2 * hprod + h2uv + h2
      exact mul_left_cancel₀ four_ne_zero this
    · have h1 : A ≤ A ^ 2 := by nlinarith
      nlinarith
  · -- `r − s = p C²`: `D² + p C² = 2 A²`, and `2` is not a square mod `p`
    exfalso
    obtain ⟨hD', hA'⟩ := dvd_of_dvd_sq_sub_mul_sq hn2
      (⟨-C ^ 2, by linear_combination -h4 - h3 + 2 * h1⟩ : (p : ℤ) ∣ D ^ 2 - 2 * A ^ 2)
    have hr : (p : ℤ) ∣ r := h1 ▸ dvd_pow hA' two_ne_zero
    have hrs : (p : ℤ) ∣ r + s := h4 ▸ dvd_pow hD' two_ne_zero
    exact hcop ⟨hr, by simpa using dvd_sub hrs hr⟩
  · -- `r + s = p D²`: `A² + B² = p D²`, and `−1` is not a square mod `p`
    exfalso
    obtain ⟨hA', hB'⟩ := dvd_of_dvd_sq_sub_mul_sq hn1
      (⟨D ^ 2, by linear_combination -h1 - h2 + h4⟩ : (p : ℤ) ∣ A ^ 2 - -1 * B ^ 2)
    exact hcop ⟨h1 ▸ dvd_pow hA' two_ne_zero, h2 ▸ dvd_pow hB' two_ne_zero⟩

/-! ### The descent for `2p`, `p ≡ 5 (mod 8)` -/

/-- The square of an odd integer is `1` modulo `8`. -/
theorem sq_emod_eight_of_odd {X : ℤ} (h : Odd X) : X ^ 2 % 8 = 1 := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨j, hj⟩ := Int.even_mul_succ_self k
  have : (2 * k + 1) ^ 2 = 8 * j + 1 := by linear_combination 4 * hj
  omega

/-- A square is `0` or `1` modulo `4`. -/
theorem sq_emod_four (X : ℤ) : X ^ 2 % 4 = 0 ∨ X ^ 2 % 4 = 1 := by
  rcases Int.even_or_odd X with ⟨k, rfl⟩ | h
  · left
    have : (k + k) ^ 2 = 4 * k ^ 2 := by ring
    omega
  · have := sq_emod_eight_of_odd h
    omega

/-- An odd number of the form `X²` or `p X²`, `p ≡ 5 (mod 8)`, is `1` modulo `4`. -/
theorem emod_four_of_odd {p Y X : ℤ} (hp : p % 8 = 5) (hY : Odd Y) (h : Y = X ^ 2 ∨ Y = p * X ^ 2) :
    Y % 4 = 1 := by
  have hX : Odd X := by
    rcases h with rfl | rfl
    · exact (Int.odd_pow' two_ne_zero).mp hY
    · exact (Int.odd_pow' two_ne_zero).mp (Int.odd_mul.mp hY).2
  have hX2 := sq_emod_eight_of_odd hX
  rcases h with rfl | rfl
  · omega
  · have : p * X ^ 2 % 8 = 5 := by rw [Int.mul_emod, hp, hX2]; rfl
    omega

/-- **Genocchi's descent step for `2p`, `p ≡ 5 (mod 8)`.** If `r s (r − s)(r + s) = 2p w²`,
then the same holds for a smaller `r`. The even one of `r, s` must be `s` (modulo `4`); then of
the four places for `p`, one dies modulo `8`, two die modulo `p` (`2` and `−2` are not squares)
and the last is Fermat's halving step. -/
theorem descent_two_mul_five_mod_eight {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 5) {r s w : ℤ}
    (hs : 0 < s) (hsr : s < r) (hc : IsCoprime r s) (hodd : Odd (r - s))
    (h : r * s * (r - s) * (r + s) = 2 * p * w ^ 2) :
    ∃ r' s' w' : ℤ, 0 < s' ∧ s' < r' ∧ IsCoprime r' s' ∧ Odd (r' - s') ∧
      r' * s' * (r' - s') * (r' + s') = 2 * p * w' ^ 2 ∧ r' < r := by
  have := Fact.mk hp
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hP0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hP8 : (p : ℤ) % 8 = 5 := by exact_mod_cast h8
  have hcop : ¬ ((p : ℤ) ∣ r ∧ (p : ℤ) ∣ s) := fun ⟨h1, h2⟩ ↦
    hP.not_isUnit (hc.isUnit_of_dvd' h1 h2)
  have hn2 : ¬ IsSquare (((2 : ℤ)) : ZMod p) := by
    rw [Int.cast_ofNat, ZMod.exists_sq_eq_two_iff (by omega)]
    omega
  have hn2' : ¬ IsSquare (((-2 : ℤ)) : ZMod p) := by
    rw [Int.cast_neg, Int.cast_ofNat, ZMod.exists_sq_eq_neg_two_iff (by omega)]
    omega
  have hsub := isCoprime_sub_add_of_odd hc hodd
  have hodd' : Odd (r + s) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + s, by linear_combination hk⟩
  rcases Int.even_or_odd s with ⟨s₁, hs₁⟩ | hso
  · -- `s = 2 s₁`
    have hs₁0 : 0 < s₁ := by omega
    have hdvd : s₁ ∣ s := ⟨2, by rw [hs₁]; ring⟩
    have h' : r * s₁ * (r - s) * (r + s) = p * w ^ 2 := by
      have : 2 * (r * s₁ * (r - s) * (r + s)) = 2 * (p * w ^ 2) := by
        rw [hs₁] at h ⊢; linear_combination h
      exact mul_left_cancel₀ two_ne_zero this
    obtain ⟨A, B, C, D, hA, hB, hC, hD, H⟩ := four_factor hP hP0
      (hc.of_isCoprime_of_dvd_right hdvd) (isCoprime_left_sub hc) (isCoprime_left_add hc)
      ((isCoprime_right_sub hc).of_isCoprime_of_dvd_left hdvd)
      ((isCoprime_right_add hc).of_isCoprime_of_dvd_left hdvd)
      hsub (by omega) hs₁0 (by omega) (by omega) h'
    rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · -- `r = p A²`: modulo `8`, `r ≡ 1` but `p A² ≡ 5`
      exfalso
      have hC8 := sq_emod_eight_of_odd ((Int.odd_pow' two_ne_zero).mp (h3 ▸ hodd))
      have hD8 := sq_emod_eight_of_odd ((Int.odd_pow' two_ne_zero).mp (h4 ▸ hodd'))
      have hro : Odd r := by
        rw [Int.odd_iff]
        obtain ⟨k, hk⟩ := hodd
        omega
      have hA8 : (p : ℤ) * A ^ 2 % 8 = 5 := by
        have hAo : Odd A := (Int.odd_pow' two_ne_zero).mp (Int.odd_mul.mp (h1 ▸ hro)).2
        rw [Int.mul_emod, hP8, sq_emod_eight_of_odd hAo]; rfl
      have hB4 := sq_emod_four B
      generalize C ^ 2 = c at *
      generalize D ^ 2 = d at *
      generalize B ^ 2 = b at *
      generalize (p : ℤ) * A ^ 2 = a at *
      omega
    · -- `s = 2 p B²`: Fermat's halving step
      obtain ⟨u, v, hu, hv, huv, h2uv, hcuv⟩ := exists_half hC hD hs h1 h3 h4 hsub
      obtain ⟨r', s', hs', hsr', hc', hodd'', hprod, hA'⟩ := exists_rs hu hv hA huv hcuv
      have huv' : u * v = p * B ^ 2 := by
        have : 2 * (u * v) = 2 * (p * B ^ 2) := by linear_combination h2uv + hs₁ + 2 * h2
        exact mul_left_cancel₀ two_ne_zero this
      -- `p B² = u v` is even, so `B` is even
      have hBe : Even B := by
        have : Even ((p : ℤ) * B ^ 2) :=
          ⟨r' * s' * (r' - s') * (r' + s'), by linear_combination -huv' + hprod⟩
        rw [Int.even_mul, Int.even_pow' two_ne_zero] at this
        refine this.resolve_left fun hpe ↦ ?_
        have : (p : ℤ) % 2 = 0 := Int.even_iff.mp hpe
        omega
      obtain ⟨B', rfl⟩ := hBe
      refine ⟨r', s', B', hs', hsr', hc', hodd'', ?_, ?_⟩
      · have : 2 * (r' * s' * (r' - s') * (r' + s')) = 2 * (2 * p * B' ^ 2) := by
          linear_combination -hprod + huv'
        exact mul_left_cancel₀ two_ne_zero this
      · have h1 : A ≤ A ^ 2 := by nlinarith
        nlinarith
    · -- `r − s = p C²`: `A² − 2 B² = p C²`, and `2` is not a square mod `p`
      exfalso
      obtain ⟨hA', hB'⟩ := dvd_of_dvd_sq_sub_mul_sq hn2
        (⟨C ^ 2, by linear_combination -h1 + h3 + hs₁ + 2 * h2⟩ : (p : ℤ) ∣ A ^ 2 - 2 * B ^ 2)
      exact hcop ⟨h1 ▸ dvd_pow hA' two_ne_zero, by
        rw [hs₁, h2]; exact dvd_add (dvd_pow hB' two_ne_zero) (dvd_pow hB' two_ne_zero)⟩
    · -- `r + s = p D²`: `A² + 2 B² = p D²`, and `−2` is not a square mod `p`
      exfalso
      obtain ⟨hA', hB'⟩ := dvd_of_dvd_sq_sub_mul_sq hn2'
        (⟨D ^ 2, by linear_combination -h1 + h4 - hs₁ - 2 * h2⟩ : (p : ℤ) ∣ A ^ 2 - -2 * B ^ 2)
      exact hcop ⟨h1 ▸ dvd_pow hA' two_ne_zero, by
        rw [hs₁, h2]; exact dvd_add (dvd_pow hB' two_ne_zero) (dvd_pow hB' two_ne_zero)⟩
  · -- `s` odd, so `r = 2 r₁`; but `r ± s ≡ 1 (mod 4)` forces `r` odd
    exfalso
    obtain ⟨r₁, hr₁⟩ : Even r := by
      rw [Int.even_iff]
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨j, hj⟩ := hso
      omega
    have hdvd : r₁ ∣ r := ⟨2, by rw [hr₁]; ring⟩
    have h' : r₁ * s * (r - s) * (r + s) = p * w ^ 2 := by
      have : 2 * (r₁ * s * (r - s) * (r + s)) = 2 * (p * w ^ 2) := by
        rw [hr₁] at h ⊢; linear_combination h
      exact mul_left_cancel₀ two_ne_zero this
    obtain ⟨A, B, C, D, -, -, -, -, H⟩ := four_factor hP hP0
      (hc.of_isCoprime_of_dvd_left hdvd)
      ((isCoprime_left_sub hc).of_isCoprime_of_dvd_left hdvd)
      ((isCoprime_left_add hc).of_isCoprime_of_dvd_left hdvd)
      (isCoprime_right_sub hc) (isCoprime_right_add hc) hsub (by omega) hs (by omega) (by omega) h'
    have key : (r - s = C ^ 2 ∨ r - s = p * C ^ 2) → (r + s = D ^ 2 ∨ r + s = p * D ^ 2) →
        False := fun h3 h4 ↦ by
      have := emod_four_of_odd hP8 hodd h3
      have := emod_four_of_odd hP8 hodd' h4
      omega
    rcases H with ⟨-, -, h3, h4⟩ | ⟨-, -, h3, h4⟩ | ⟨-, -, h3, h4⟩ | ⟨-, -, h3, h4⟩
    exacts [key (.inl h3) (.inl h4), key (.inl h3) (.inl h4), key (.inr h3) (.inl h4),
      key (.inl h3) (.inr h4)]

/-! ### Infinite descent -/

/-- If every solution of `r s (r − s)(r + s) = m w²` gives one with a smaller `r`, there is none. -/
theorem ne_mul_sq_of_descent {m : ℤ}
    (step : ∀ {r s w : ℤ}, 0 < s → s < r → IsCoprime r s → Odd (r - s) →
      r * s * (r - s) * (r + s) = m * w ^ 2 →
      ∃ r' s' w' : ℤ, 0 < s' ∧ s' < r' ∧ IsCoprime r' s' ∧ Odd (r' - s') ∧
        r' * s' * (r' - s') * (r' + s') = m * w' ^ 2 ∧ r' < r)
    {r s w : ℤ} (hs : 0 < s) (hsr : s < r) (hc : IsCoprime r s) (hodd : Odd (r - s)) :
    r * s * (r - s) * (r + s) ≠ m * w ^ 2 := by
  suffices ∀ k : ℕ, ∀ {r s w : ℤ}, r ≤ k → 0 < s → s < r → IsCoprime r s → Odd (r - s) →
      r * s * (r - s) * (r + s) ≠ m * w ^ 2 from
    this r.toNat (Int.self_le_toNat r) hs hsr hc hodd
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro r s w hrk hs hsr hc hodd h
    obtain ⟨r', s', w', hs', hsr', hc', hodd', h', hlt⟩ := step hs hsr hc hodd h
    exact ih r'.toNat (by omega) (Int.self_le_toNat r') hs' hsr' hc' hodd' h'

/-! ### From rational triangles to `r, s` -/

/-- If `R g² = m D²` with `m` squarefree and `g ≠ 0`, then `R = m w²`. -/
theorem eq_mul_sq_of_squarefree {m R g D : ℤ} (hm : Squarefree m) (hg : g ≠ 0)
    (h : R * g ^ 2 = m * D ^ 2) : ∃ w : ℤ, R = m * w ^ 2 := by
  obtain ⟨k, g₁, D₁, hk, hcop, rfl, rfl⟩ := Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left D hg)
  have hk2 : ((k : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hk.ne')
  have h' : R * g₁ ^ 2 = m * D₁ ^ 2 :=
    mul_right_cancel₀ hk2 (by linear_combination h)
  have hdvd : g₁ ^ 2 ∣ m * D₁ ^ 2 := ⟨R, by linear_combination -h'⟩
  have hg₁ : g₁ * g₁ ∣ m := by
    rw [← sq]
    exact ((Int.isCoprime_iff_gcd_eq_one.mpr hcop).pow).dvd_of_dvd_mul_right hdvd
  rcases Int.isUnit_iff.mp (hm g₁ hg₁) with rfl | rfl <;>
    exact ⟨D₁, by linear_combination h'⟩

/-- A rational right triangle of squarefree area `m` gives coprime `r > s > 0` of opposite parity
with `r s (r − s)(r + s) = m w²`. -/
theorem exists_rs_of_isCongruent {m : ℕ} (hm : Squarefree m)
    (h : PerfectCuboid.CongruentRank.IsCongruent (m : ℚ)) :
    ∃ r s w : ℤ, 0 < s ∧ s < r ∧ IsCoprime r s ∧ Odd (r - s) ∧
      r * s * (r - s) * (r + s) = m * w ^ 2 := by
  obtain ⟨x, y, z, hx, hy, h1, h2⟩ := h
  -- clear denominators
  set D : ℤ := x.den * y.den * z.den with hD
  have hDq : (D : ℚ) = x.den * y.den * z.den := by simp [hD]
  have hD0 : (0 : ℚ) < D := by rw [hDq]; positivity
  have hX : (x.num : ℚ) * y.den * z.den = x * D := by
    rw [hDq, ← Rat.mul_den_eq_num]; ring
  have hY : (y.num : ℚ) * x.den * z.den = y * D := by
    rw [hDq, ← Rat.mul_den_eq_num]; ring
  have hZ : (z.num : ℚ) * x.den * y.den = z * D := by
    rw [hDq, ← Rat.mul_den_eq_num]; ring
  set X : ℤ := x.num * y.den * z.den
  set Y : ℤ := y.num * x.den * z.den
  set Z : ℤ := z.num * x.den * y.den
  have hX0 : 0 < X := by
    have : (0 : ℚ) < X := by push_cast [X]; rw [hX]; positivity
    exact_mod_cast this
  have hY0 : 0 < Y := by
    have : (0 : ℚ) < Y := by push_cast [Y]; rw [hY]; positivity
    exact_mod_cast this
  have hXYZ : X ^ 2 + Y ^ 2 = Z ^ 2 := by
    have : (X : ℚ) ^ 2 + (Y : ℚ) ^ 2 = (Z : ℚ) ^ 2 := by
      push_cast [X, Y, Z]; rw [hX, hY, hZ]; linear_combination (D : ℚ) ^ 2 * h1
    exact_mod_cast this
  have hXY : X * Y = 2 * m * D ^ 2 := by
    have : (X : ℚ) * Y = 2 * m * (D : ℚ) ^ 2 := by
      push_cast [X, Y]; rw [hX, hY]; linear_combination (D : ℚ) ^ 2 * h2
    exact_mod_cast this
  clear_value X Y Z D
  -- divide by `g = gcd (X, Y)`
  obtain ⟨g, x', y', hg0, hcop, rfl, rfl⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left Y hX0.ne')
  have hg : (0 : ℤ) < g := by exact_mod_cast hg0
  have hg2 : (g : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hg.ne'
  have hx' : 0 < x' := pos_of_mul_pos_left hX0 hg.le
  have hy' : 0 < y' := pos_of_mul_pos_left hY0 hg.le
  obtain ⟨z', rfl⟩ : (g : ℤ) ∣ Z := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero]
    exact ⟨x' ^ 2 + y' ^ 2, by linear_combination -hXYZ⟩
  have h1' : x' ^ 2 + y' ^ 2 = |z'| ^ 2 := by
    rw [sq_abs]
    exact mul_right_cancel₀ hg2 (by linear_combination hXYZ)
  have hz' : 0 < |z'| := by
    rcases (abs_nonneg z').lt_or_eq with h | h
    · exact h
    · rw [← h] at h1'; nlinarith
  obtain ⟨r, s, hs, hsr, hc, hodd, hprod, -⟩ :=
    exists_rs hx' hy' hz' h1' (Int.isCoprime_iff_gcd_eq_one.mpr hcop)
  obtain ⟨w, hw⟩ := eq_mul_sq_of_squarefree (Int.squarefree_natCast.mpr hm) hg.ne'
    (R := r * s * (r - s) * (r + s)) (D := D)
    (mul_left_cancel₀ two_ne_zero (by linear_combination -(g : ℤ) ^ 2 * hprod + hXY))
  exact ⟨r, s, w, hs, hsr, hc, hodd, hw⟩

/-! ### Genocchi's theorems -/

/-- `r s (r − s)(r + s) ≠ p w²` for a prime `p ≡ 3 (mod 8)` and coprime `r > s > 0` of opposite
parity. -/
theorem ne_prime_mul_sq_three_mod_eight {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3) {r s w : ℤ}
    (hs : 0 < s) (hsr : s < r) (hc : IsCoprime r s) (hodd : Odd (r - s)) :
    r * s * (r - s) * (r + s) ≠ p * w ^ 2 :=
  ne_mul_sq_of_descent (descent_three_mod_eight hp h8) hs hsr hc hodd

/-- `r s (r − s)(r + s) ≠ 2p w²` for a prime `p ≡ 5 (mod 8)` and coprime `r > s > 0` of opposite
parity. -/
theorem ne_two_mul_prime_mul_sq_five_mod_eight {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 5)
    {r s w : ℤ} (hs : 0 < s) (hsr : s < r) (hc : IsCoprime r s) (hodd : Odd (r - s)) :
    r * s * (r - s) * (r + s) ≠ 2 * p * w ^ 2 :=
  ne_mul_sq_of_descent (descent_two_mul_five_mod_eight hp h8) hs hsr hc hodd

/-- **Genocchi (1855).** A prime `p ≡ 3 (mod 8)` is not a congruent number. -/
theorem not_isCongruent_prime_three_mod_eight {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3) :
    ¬ PerfectCuboid.CongruentRank.IsCongruent (p : ℚ) := fun h ↦ by
  obtain ⟨r, s, w, hs, hsr, hc, hodd, h⟩ := exists_rs_of_isCongruent hp.prime.squarefree h
  exact ne_prime_mul_sq_three_mod_eight hp h8 hs hsr hc hodd h

/-- **Genocchi (1855).** `2p` is not a congruent number for a prime `p ≡ 5 (mod 8)`. -/
theorem not_isCongruent_two_mul_prime_five_mod_eight {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 5) :
    ¬ PerfectCuboid.CongruentRank.IsCongruent (2 * p : ℚ) := fun h ↦ by
  have hsq : Squarefree (2 * p) := Nat.squarefree_mul_iff.mpr
    ⟨(Nat.coprime_primes Nat.prime_two hp).mpr (by omega), Nat.squarefree_two,
      hp.prime.squarefree⟩
  obtain ⟨r, s, w, hs, hsr, hc, hodd, h⟩ := exists_rs_of_isCongruent hsq (by exact_mod_cast h)
  exact ne_two_mul_prime_mul_sq_five_mod_eight hp h8 hs hsr hc hodd (by exact_mod_cast h)

end FermatTriangle
