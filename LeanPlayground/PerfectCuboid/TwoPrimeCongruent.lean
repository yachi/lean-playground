module

public import LeanPlayground.PerfectCuboid.CongruentCharacters

/-!
# Two-prime non-congruent numbers (Lagrange's classes)

**Theorem (classical; Lagrange 1974/75).** Let `p ≠ q` be primes.
* (C1) `p q` is not congruent if `p ≡ q ≡ 3 (mod 8)`.
* (C2) `p q` is not congruent if `p ≡ 1`, `q ≡ 3 (mod 8)` and `(p/q) = −1`.
* (C3) `2 p q` is not congruent if `p ≡ q ≡ 5 (mod 8)`.
* (C4) `2 p q` is not congruent if `p ≡ 1`, `q ≡ 5 (mod 8)` and `(p/q) = −1`.
* (C5) `p q` is not congruent if `p ≡ 5`, `q ≡ 7 (mod 8)` and `(p/q) = −1`.
* (C6) `2 p q` is not congruent if `p ≡ q ≡ 3 (mod 8)`.
* (C7) `2 p q` is not congruent if `p ≡ 3`, `q ≡ 7 (mod 8)` and `(p/q) = −1`.

These seven are exactly the two-prime classes (`n = p q` or `2 p q`, conditions on residues mod 8
and on `(p/q)`) in which every member has 2-Selmer rank 0 (checked for `n ≤ 6000`); in every
other such class the descent cannot close, because some member has a non-trivial everywhere
locally soluble case.

The proof is Genocchi's descent (`Genocchi.lean`) with two primes. A primitive right triangle of
area `n w²` gives `r s (r − s)(r + s) = n w²` with pairwise coprime factors. For `n = p q` each
prime sits in one of the four factors (`four_factor_two_primes`, 16 cases; for `2pq` first halve
the even one of `r, s`, 32 cases). The case `s = n B²` is Fermat's halving step and gives a
smaller solution. All other cases die:
* modulo `8` (`res8`: an odd `d X²` is `≡ d (mod 8)`, an even one is `≡ 0 (mod 4)`), when `p` and
  `q` sit in different factors (C1, C3), or in all but four cases (C2, C4);
* modulo `p`, because `−1`, `2` or `−2` is not a square, when `p q` sits in `r`, `r − s` or
  `r + s` (C1, C3: exactly Genocchi's argument);
* modulo `q`, because `p` is not a square mod `q`, in the three cases where `q` sits in `s`
  and `p` in `r`, `r − s` or `r + s` (C2, C4), and in three similar cases for C5 and C7;
* modulo `p`, because `2` is not a square, for C6 (three cases).

## Cuboid corollaries

The three congruent numbers `(a+d)(a+e)(g+d)(g+e)`, `(b+d)(b+f)(g+d)(g+f)`,
`(c+e)(c+f)(g+e)(g+f)` of a perfect cuboid (`CongruentCharacters.lean`) and the squarefree part
`N` of `abcg/2` avoid all these square classes.
-/

-- The 16-way case disjunctions below are generated and do not fit in 100 columns.
set_option linter.style.longLine false

@[expose] public section

namespace FermatTriangle

/-! ### Splitting `p q w²` among four coprime factors -/

/-- **Two primes among four coprime factors.** If four pairwise coprime positive integers have
product `p q w²` (`p`, `q` positive primes), then `p` sits in one factor, `q` in one factor, and each
factor is the product of the primes it holds times a square. The 16 cases are listed with `p`'s
place outer and `q`'s place inner. -/
theorem four_factor_two_primes {p q F₁ F₂ F₃ F₄ w : ℤ} (hp : Prime p) (hp0 : 0 < p)
    (hq : Prime q) (hq0 : 0 < q)
    (h12 : IsCoprime F₁ F₂) (h13 : IsCoprime F₁ F₃) (h14 : IsCoprime F₁ F₄)
    (h23 : IsCoprime F₂ F₃) (h24 : IsCoprime F₂ F₄) (h34 : IsCoprime F₃ F₄)
    (h1 : 0 < F₁) (h2 : 0 < F₂) (h3 : 0 < F₃) (h4 : 0 < F₄)
    (h : F₁ * F₂ * F₃ * F₄ = p * q * w ^ 2) :
    ∃ A B C D : ℤ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D ∧ (
        (F₁ = p * q * A ^ 2 ∧ F₂ = 1 * B ^ 2 ∧ F₃ = 1 * C ^ 2 ∧ F₄ = 1 * D ^ 2) ∨
        (F₁ = p * A ^ 2 ∧ F₂ = q * B ^ 2 ∧ F₃ = 1 * C ^ 2 ∧ F₄ = 1 * D ^ 2) ∨
        (F₁ = p * A ^ 2 ∧ F₂ = 1 * B ^ 2 ∧ F₃ = q * C ^ 2 ∧ F₄ = 1 * D ^ 2) ∨
        (F₁ = p * A ^ 2 ∧ F₂ = 1 * B ^ 2 ∧ F₃ = 1 * C ^ 2 ∧ F₄ = q * D ^ 2) ∨
        (F₁ = q * A ^ 2 ∧ F₂ = p * B ^ 2 ∧ F₃ = 1 * C ^ 2 ∧ F₄ = 1 * D ^ 2) ∨
        (F₁ = 1 * A ^ 2 ∧ F₂ = p * q * B ^ 2 ∧ F₃ = 1 * C ^ 2 ∧ F₄ = 1 * D ^ 2) ∨
        (F₁ = 1 * A ^ 2 ∧ F₂ = p * B ^ 2 ∧ F₃ = q * C ^ 2 ∧ F₄ = 1 * D ^ 2) ∨
        (F₁ = 1 * A ^ 2 ∧ F₂ = p * B ^ 2 ∧ F₃ = 1 * C ^ 2 ∧ F₄ = q * D ^ 2) ∨
        (F₁ = q * A ^ 2 ∧ F₂ = 1 * B ^ 2 ∧ F₃ = p * C ^ 2 ∧ F₄ = 1 * D ^ 2) ∨
        (F₁ = 1 * A ^ 2 ∧ F₂ = q * B ^ 2 ∧ F₃ = p * C ^ 2 ∧ F₄ = 1 * D ^ 2) ∨
        (F₁ = 1 * A ^ 2 ∧ F₂ = 1 * B ^ 2 ∧ F₃ = p * q * C ^ 2 ∧ F₄ = 1 * D ^ 2) ∨
        (F₁ = 1 * A ^ 2 ∧ F₂ = 1 * B ^ 2 ∧ F₃ = p * C ^ 2 ∧ F₄ = q * D ^ 2) ∨
        (F₁ = q * A ^ 2 ∧ F₂ = 1 * B ^ 2 ∧ F₃ = 1 * C ^ 2 ∧ F₄ = p * D ^ 2) ∨
        (F₁ = 1 * A ^ 2 ∧ F₂ = q * B ^ 2 ∧ F₃ = 1 * C ^ 2 ∧ F₄ = p * D ^ 2) ∨
        (F₁ = 1 * A ^ 2 ∧ F₂ = 1 * B ^ 2 ∧ F₃ = q * C ^ 2 ∧ F₄ = p * D ^ 2) ∨
        (F₁ = 1 * A ^ 2 ∧ F₂ = 1 * B ^ 2 ∧ F₃ = 1 * C ^ 2 ∧ F₄ = p * q * D ^ 2)) := by
  have hpd : p ∣ F₁ * F₂ * F₃ * F₄ := ⟨q * w ^ 2, by rw [h]; ring⟩
  rcases hp.dvd_or_dvd hpd with h123 | hdvd
  · rcases hp.dvd_or_dvd h123 with h12' | hdvd
    · rcases hp.dvd_or_dvd h12' with hdvd | hdvd
      · -- `p ∣ F₁`
        obtain ⟨G, rfl⟩ := hdvd
        have hG : 0 < G := pos_of_mul_pos_right h1 hp0.le
        have h' : G * F₂ * F₃ * F₄ = q * w ^ 2 :=
          mul_left_cancel₀ hp0.ne' (by linear_combination h)
        obtain ⟨A, B, C, D, hA, hB, hC, hD, H⟩ :=
          four_factor hq hq0 h12.of_mul_left_right h13.of_mul_left_right h14.of_mul_left_right h23 h24 h34 hG h2 h3 h4  h'
        rcases H with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inl ⟨by ring, by ring, by ring, by ring⟩⟩
        · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩)⟩
        · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩))⟩
        · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩)))⟩
      · -- `p ∣ F₂`
        obtain ⟨G, rfl⟩ := hdvd
        have hG : 0 < G := pos_of_mul_pos_right h2 hp0.le
        have h' : F₁ * G * F₃ * F₄ = q * w ^ 2 :=
          mul_left_cancel₀ hp0.ne' (by linear_combination h)
        obtain ⟨A, B, C, D, hA, hB, hC, hD, H⟩ :=
          four_factor hq hq0 h12.of_mul_right_right h13 h14 h23.of_mul_left_right h24.of_mul_left_right h34 h1 hG h3 h4  h'
        rcases H with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩))))⟩
        · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩)))))⟩
        · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩))))))⟩
        · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩)))))))⟩
    · -- `p ∣ F₃`
      obtain ⟨G, rfl⟩ := hdvd
      have hG : 0 < G := pos_of_mul_pos_right h3 hp0.le
      have h' : F₁ * F₂ * G * F₄ = q * w ^ 2 :=
        mul_left_cancel₀ hp0.ne' (by linear_combination h)
      obtain ⟨A, B, C, D, hA, hB, hC, hD, H⟩ :=
        four_factor hq hq0 h12 h13.of_mul_right_right h14 h23.of_mul_right_right h24 h34.of_mul_left_right h1 h2 hG h4  h'
      rcases H with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩))))))))⟩
      · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩)))))))))⟩
      · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩))))))))))⟩
      · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩)))))))))))⟩
  · -- `p ∣ F₄`
    obtain ⟨G, rfl⟩ := hdvd
    have hG : 0 < G := pos_of_mul_pos_right h4 hp0.le
    have h' : F₁ * F₂ * F₃ * G = q * w ^ 2 :=
      mul_left_cancel₀ hp0.ne' (by linear_combination h)
    obtain ⟨A, B, C, D, hA, hB, hC, hD, H⟩ :=
      four_factor hq hq0 h12 h13 h14.of_mul_right_right h23 h24.of_mul_right_right h34.of_mul_right_right h1 h2 h3 hG  h'
    rcases H with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩))))))))))))⟩
    · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩)))))))))))))⟩
    · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring, by ring, by ring, by ring⟩))))))))))))))⟩
    · exact ⟨A, B, C, D, hA, hB, hC, hD, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by ring, by ring, by ring, by ring⟩)))))))))))))))⟩

/-! ### Residues modulo `8` -/

/-- An odd `d X²` is `≡ d (mod 8)`; an even one is `≡ 0 (mod 4)`. -/
theorem res8 {F d X : ℤ} (hd : d % 2 = 1) (h : F = d * X ^ 2) :
    (F % 2 = 1 ∧ F % 8 = d % 8) ∨ (F % 2 = 0 ∧ F % 4 = 0) := by
  rcases Int.even_or_odd X with ⟨k, rfl⟩ | hX
  · right
    have : F = 4 * (d * k ^ 2) := by rw [h]; ring
    omega
  · left
    have hX8 := sq_emod_eight_of_odd hX
    obtain ⟨t, ht⟩ : ∃ t, X ^ 2 = 8 * t + 1 := ⟨X ^ 2 / 8, by omega⟩
    have : F = 8 * (d * t) + d := by rw [h, ht]; ring
    omega

-- `kill8` closes a case of the 16-way split by residues modulo `8`.
set_option hygiene false in
macro "kill8" : tactic => `(tactic| (
  exfalso
  have k1 := res8 (by omega) h1
  have k2 := res8 (by omega) h2
  have k3 := res8 (by omega) h3
  have k4 := res8 (by omega) h4
  omega))

/-! ### Fermat's halving step, for any odd `m` -/

/-- **The descending case, `m` odd.** If `r = A²`, `s = m B²`, `r − s = C²`, `r + s = D²`, there is
a solution of `r' s' (r' − s')(r' + s') = m w'²` with `r' < r`. -/
theorem descend_odd {m r s A B C D : ℤ} (hm : m % 2 = 1) (hA : 0 < A) (hC : 0 < C) (hD : 0 < D)
    (hs : 0 < s) (hc : IsCoprime r s) (hodd : Odd (r - s))
    (h1 : r = A ^ 2) (h2 : s = m * B ^ 2) (h3 : r - s = C ^ 2) (h4 : r + s = D ^ 2) :
    ∃ r' s' w' : ℤ, 0 < s' ∧ s' < r' ∧ IsCoprime r' s' ∧ Odd (r' - s') ∧
      r' * s' * (r' - s') * (r' + s') = m * w' ^ 2 ∧ r' < r := by
  obtain ⟨u, v, hu, hv, huv, h2uv, hcuv⟩ :=
    exists_half hC hD hs h1 h3 h4 (isCoprime_sub_add_of_odd hc hodd)
  obtain ⟨r', s', hs', hsr', hc', hodd', hprod, hA'⟩ := exists_rs hu hv hA huv hcuv
  have hBe : Even B := by
    have : Even (m * B ^ 2) := ⟨u * v, by linear_combination -h2 - h2uv⟩
    rw [Int.even_mul, Int.even_pow' two_ne_zero] at this
    refine this.resolve_left fun hme ↦ ?_
    have : m % 2 = 0 := Int.even_iff.mp hme
    omega
  obtain ⟨B', rfl⟩ := hBe
  refine ⟨r', s', B', hs', hsr', hc', hodd', ?_, ?_⟩
  · have : 4 * (r' * s' * (r' - s') * (r' + s')) = 4 * (m * B' ^ 2) := by
      linear_combination -2 * hprod + h2uv + h2
    exact mul_left_cancel₀ four_ne_zero this
  · have h1 : A ≤ A ^ 2 := by nlinarith
    nlinarith

/-- **The descending case for `2m`, `m` odd.** If `r = A²`, `s = 2 s₁`, `s₁ = m B²`, `r − s = C²`,
`r + s = D²`, there is a solution of `r' s' (r' − s')(r' + s') = 2 m w'²` with `r' < r`. -/
theorem descend_even {m r s s₁ A B C D : ℤ} (hm : m % 2 = 1) (hA : 0 < A) (hC : 0 < C)
    (hD : 0 < D) (hs : 0 < s) (hc : IsCoprime r s) (hodd : Odd (r - s))
    (h1 : r = A ^ 2) (hs₁ : s = 2 * s₁) (h2 : s₁ = m * B ^ 2) (h3 : r - s = C ^ 2)
    (h4 : r + s = D ^ 2) :
    ∃ r' s' w' : ℤ, 0 < s' ∧ s' < r' ∧ IsCoprime r' s' ∧ Odd (r' - s') ∧
      r' * s' * (r' - s') * (r' + s') = 2 * m * w' ^ 2 ∧ r' < r := by
  obtain ⟨u, v, hu, hv, huv, h2uv, hcuv⟩ :=
    exists_half hC hD hs h1 h3 h4 (isCoprime_sub_add_of_odd hc hodd)
  obtain ⟨r', s', hs', hsr', hc', hodd', hprod, hA'⟩ := exists_rs hu hv hA huv hcuv
  have huv' : u * v = m * B ^ 2 := by
    have : 2 * (u * v) = 2 * (m * B ^ 2) := by linear_combination h2uv + hs₁ + 2 * h2
    exact mul_left_cancel₀ two_ne_zero this
  have hBe : Even B := by
    have : Even (m * B ^ 2) :=
      ⟨r' * s' * (r' - s') * (r' + s'), by linear_combination -huv' + hprod⟩
    rw [Int.even_mul, Int.even_pow' two_ne_zero] at this
    refine this.resolve_left fun hme ↦ ?_
    have : m % 2 = 0 := Int.even_iff.mp hme
    omega
  obtain ⟨B', rfl⟩ := hBe
  refine ⟨r', s', B', hs', hsr', hc', hodd', ?_, ?_⟩
  · have : 2 * (r' * s' * (r' - s') * (r' + s')) = 2 * (2 * m * B' ^ 2) := by
      linear_combination -hprod + huv'
    exact mul_left_cancel₀ two_ne_zero this
  · have h1 : A ≤ A ^ 2 := by nlinarith
    nlinarith

/-! ### Common set-up -/

/-- A prime `ℓ` dividing two of `r, s, r − s, r + s` contradicts `gcd (r, s) = 1` — the cases we
need. -/
theorem not_dvd_both {ℓ r s : ℤ} (hℓ : Prime ℓ) (hc : IsCoprime r s) :
    ¬ (ℓ ∣ r ∧ ℓ ∣ s) := fun ⟨h1, h2⟩ ↦ hℓ.not_isUnit (hc.isUnit_of_dvd' h1 h2)

/-! ### (C1) `p q`, `p ≡ q ≡ 3 (mod 8)` -/

/-- **Descent step for `p q`, `p ≡ q ≡ 3 (mod 8)`.** -/
theorem descent_pq_three_three {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp8 : p % 8 = 3)
    (hq8 : q % 8 = 3) {r s w : ℤ} (hs : 0 < s) (hsr : s < r) (hc : IsCoprime r s)
    (hodd : Odd (r - s)) (h : r * s * (r - s) * (r + s) = p * q * w ^ 2) :
    ∃ r' s' w' : ℤ, 0 < s' ∧ s' < r' ∧ IsCoprime r' s' ∧ Odd (r' - s') ∧
      r' * s' * (r' - s') * (r' + s') = p * q * w' ^ 2 ∧ r' < r := by
  have := Fact.mk hp
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hQ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hP0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hQ0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hP8 : (p : ℤ) % 8 = 3 := by exact_mod_cast hp8
  have hQ8 : (q : ℤ) % 8 = 3 := by exact_mod_cast hq8
  have hPQ8 : ((p : ℤ) * q) % 8 = 1 := by rw [Int.mul_emod, hP8, hQ8]; rfl
  have hodd2 : (r - s) % 2 = 1 := Int.odd_iff.mp hodd
  have hcop := not_dvd_both hP hc
  have hn1 : ¬ IsSquare (((-1 : ℤ)) : ZMod p) := by
    rw [Int.cast_neg, Int.cast_one, ZMod.exists_sq_eq_neg_one_iff]
    omega
  have hn2 : ¬ IsSquare (((2 : ℤ)) : ZMod p) := by
    rw [Int.cast_ofNat, ZMod.exists_sq_eq_two_iff (by omega)]
    omega
  obtain ⟨A, B, C, D, hA, hB, hC, hD, H⟩ := four_factor_two_primes hP hP0 hQ hQ0 hc
    (isCoprime_left_sub hc) (isCoprime_left_add hc) (isCoprime_right_sub hc)
    (isCoprime_right_add hc) (isCoprime_sub_add_of_odd hc hodd) (by omega) hs (by omega)
    (by omega) h
  rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · -- `r = p q A²`: `C² + D² = 2 p q A²`, and `−1` is not a square mod `p`
    exfalso
    obtain ⟨hC', -⟩ := dvd_of_dvd_sq_sub_mul_sq hn1
      (⟨2 * q * A ^ 2, by linear_combination 2 * h1 - h3 - h4⟩ : (p : ℤ) ∣ C ^ 2 - -1 * D ^ 2)
    have hr : (p : ℤ) ∣ r := ⟨q * A ^ 2, by rw [h1]; ring⟩
    have hrs : (p : ℤ) ∣ r - s := by rw [h3]; exact dvd_mul_of_dvd_right (dvd_pow hC' two_ne_zero) _
    exact hcop ⟨hr, by simpa using dvd_sub hr hrs⟩
  all_goals try kill8
  · -- `s = p q B²`: Fermat's halving step
    exact descend_odd (by omega) hA hC hD hs hc hodd (by rw [h1]; ring) (by rw [h2]) (by rw [h3]; ring)
      (by rw [h4]; ring)
  · -- `r − s = p q C²`: `D² − 2 A² = −p q C²`, and `2` is not a square mod `p`
    exfalso
    obtain ⟨hD', hA'⟩ := dvd_of_dvd_sq_sub_mul_sq hn2
      (⟨-(q * C ^ 2), by linear_combination 2 * h1 - h3 - h4⟩ : (p : ℤ) ∣ D ^ 2 - 2 * A ^ 2)
    have hr : (p : ℤ) ∣ r := by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _
    have hrs : (p : ℤ) ∣ r + s := by rw [h4]; exact dvd_mul_of_dvd_right (dvd_pow hD' two_ne_zero) _
    exact hcop ⟨hr, by simpa using dvd_sub hrs hr⟩
  · -- `r + s = p q D²`: `A² + B² = p q D²`, and `−1` is not a square mod `p`
    exfalso
    obtain ⟨hA', hB'⟩ := dvd_of_dvd_sq_sub_mul_sq hn1
      (⟨q * D ^ 2, by linear_combination -h1 - h2 + h4⟩ : (p : ℤ) ∣ A ^ 2 - -1 * B ^ 2)
    exact hcop ⟨by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _,
      by rw [h2]; exact dvd_mul_of_dvd_right (dvd_pow hB' two_ne_zero) _⟩

/-! ### (C2) `p q`, `p ≡ 1`, `q ≡ 3 (mod 8)`, `(p/q) = −1` -/

/-- **Descent step for `p q`, `p ≡ 1`, `q ≡ 3 (mod 8)`, `p` not a square mod `q`.** -/
theorem descent_pq_one_three {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp8 : p % 8 = 1)
    (hq8 : q % 8 = 3) (hpq : ¬ IsSquare (((p : ℤ)) : ZMod q)) {r s w : ℤ} (hs : 0 < s)
    (hsr : s < r) (hc : IsCoprime r s) (hodd : Odd (r - s))
    (h : r * s * (r - s) * (r + s) = p * q * w ^ 2) :
    ∃ r' s' w' : ℤ, 0 < s' ∧ s' < r' ∧ IsCoprime r' s' ∧ Odd (r' - s') ∧
      r' * s' * (r' - s') * (r' + s') = p * q * w' ^ 2 ∧ r' < r := by
  have := Fact.mk hq
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hQ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hP0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hQ0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hP8 : (p : ℤ) % 8 = 1 := by exact_mod_cast hp8
  have hQ8 : (q : ℤ) % 8 = 3 := by exact_mod_cast hq8
  have hPQ8 : ((p : ℤ) * q) % 8 = 3 := by rw [Int.mul_emod, hP8, hQ8]; rfl
  have hodd2 : (r - s) % 2 = 1 := Int.odd_iff.mp hodd
  have hcop := not_dvd_both hQ hc
  obtain ⟨A, B, C, D, hA, hB, hC, hD, H⟩ := four_factor_two_primes hP hP0 hQ hQ0 hc
    (isCoprime_left_sub hc) (isCoprime_left_add hc) (isCoprime_right_sub hc)
    (isCoprime_right_add hc) (isCoprime_sub_add_of_odd hc hodd) (by omega) hs (by omega)
    (by omega) h
  rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  all_goals try kill8
  · -- `r = p A²`, `s = q B²`: `C² − p A² = −q B²`
    exfalso
    obtain ⟨-, hA'⟩ := dvd_of_dvd_sq_sub_mul_sq hpq
      (⟨-B ^ 2, by linear_combination -h3 + h1 - h2⟩ : (q : ℤ) ∣ C ^ 2 - p * A ^ 2)
    exact hcop ⟨by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _,
      ⟨B ^ 2, h2⟩⟩
  · -- `s = p q B²`: Fermat's halving step
    exact descend_odd (by omega) hA hC hD hs hc hodd (by rw [h1]; ring) (by rw [h2]) (by rw [h3]; ring)
      (by rw [h4]; ring)
  · -- `s = q B²`, `r − s = p C²`: `A² − p C² = q B²`
    exfalso
    obtain ⟨hA', -⟩ := dvd_of_dvd_sq_sub_mul_sq hpq
      (⟨B ^ 2, by linear_combination -h1 + h2 + h3⟩ : (q : ℤ) ∣ A ^ 2 - p * C ^ 2)
    exact hcop ⟨by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _,
      ⟨B ^ 2, h2⟩⟩
  · -- `s = q B²`, `r + s = p D²`: `A² − p D² = −q B²`
    exfalso
    obtain ⟨hA', -⟩ := dvd_of_dvd_sq_sub_mul_sq hpq
      (⟨-B ^ 2, by linear_combination -h1 - h2 + h4⟩ : (q : ℤ) ∣ A ^ 2 - p * D ^ 2)
    exact hcop ⟨by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _,
      ⟨B ^ 2, h2⟩⟩

/-! ### The even cases: halving the even one of `r, s` -/

/-- For `r s (r − s)(r + s) = 2 p q w²`: either `s = 2 s₁` and `r s₁ (r − s)(r + s) = p q w²`, or
`r = 2 r₁` and `r₁ s (r − s)(r + s) = p q w²`; in both cases the four factors are pairwise
coprime and positive, so `four_factor_two_primes` applies. -/
theorem even_split {p q r s w : ℤ} (hp : Prime p) (hp0 : 0 < p) (hq : Prime q) (hq0 : 0 < q)
    (hs : 0 < s) (hsr : s < r) (hc : IsCoprime r s) (hodd : Odd (r - s))
    (h : r * s * (r - s) * (r + s) = 2 * (p * q) * w ^ 2) :
    (∃ s₁, s = 2 * s₁ ∧ ∃ A B C D : ℤ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D ∧ (
        (r = p * q * A ^ 2 ∧ s₁ = 1 * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r = p * A ^ 2 ∧ s₁ = q * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r = p * A ^ 2 ∧ s₁ = 1 * B ^ 2 ∧ r - s = q * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r = p * A ^ 2 ∧ s₁ = 1 * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = q * D ^ 2) ∨
        (r = q * A ^ 2 ∧ s₁ = p * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r = 1 * A ^ 2 ∧ s₁ = p * q * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r = 1 * A ^ 2 ∧ s₁ = p * B ^ 2 ∧ r - s = q * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r = 1 * A ^ 2 ∧ s₁ = p * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = q * D ^ 2) ∨
        (r = q * A ^ 2 ∧ s₁ = 1 * B ^ 2 ∧ r - s = p * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r = 1 * A ^ 2 ∧ s₁ = q * B ^ 2 ∧ r - s = p * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r = 1 * A ^ 2 ∧ s₁ = 1 * B ^ 2 ∧ r - s = p * q * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r = 1 * A ^ 2 ∧ s₁ = 1 * B ^ 2 ∧ r - s = p * C ^ 2 ∧ r + s = q * D ^ 2) ∨
        (r = q * A ^ 2 ∧ s₁ = 1 * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = p * D ^ 2) ∨
        (r = 1 * A ^ 2 ∧ s₁ = q * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = p * D ^ 2) ∨
        (r = 1 * A ^ 2 ∧ s₁ = 1 * B ^ 2 ∧ r - s = q * C ^ 2 ∧ r + s = p * D ^ 2) ∨
        (r = 1 * A ^ 2 ∧ s₁ = 1 * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = p * q * D ^ 2))) ∨
    (∃ r₁, r = 2 * r₁ ∧ ∃ A B C D : ℤ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D ∧ (
        (r₁ = p * q * A ^ 2 ∧ s = 1 * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r₁ = p * A ^ 2 ∧ s = q * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r₁ = p * A ^ 2 ∧ s = 1 * B ^ 2 ∧ r - s = q * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r₁ = p * A ^ 2 ∧ s = 1 * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = q * D ^ 2) ∨
        (r₁ = q * A ^ 2 ∧ s = p * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r₁ = 1 * A ^ 2 ∧ s = p * q * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r₁ = 1 * A ^ 2 ∧ s = p * B ^ 2 ∧ r - s = q * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r₁ = 1 * A ^ 2 ∧ s = p * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = q * D ^ 2) ∨
        (r₁ = q * A ^ 2 ∧ s = 1 * B ^ 2 ∧ r - s = p * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r₁ = 1 * A ^ 2 ∧ s = q * B ^ 2 ∧ r - s = p * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r₁ = 1 * A ^ 2 ∧ s = 1 * B ^ 2 ∧ r - s = p * q * C ^ 2 ∧ r + s = 1 * D ^ 2) ∨
        (r₁ = 1 * A ^ 2 ∧ s = 1 * B ^ 2 ∧ r - s = p * C ^ 2 ∧ r + s = q * D ^ 2) ∨
        (r₁ = q * A ^ 2 ∧ s = 1 * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = p * D ^ 2) ∨
        (r₁ = 1 * A ^ 2 ∧ s = q * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = p * D ^ 2) ∨
        (r₁ = 1 * A ^ 2 ∧ s = 1 * B ^ 2 ∧ r - s = q * C ^ 2 ∧ r + s = p * D ^ 2) ∨
        (r₁ = 1 * A ^ 2 ∧ s = 1 * B ^ 2 ∧ r - s = 1 * C ^ 2 ∧ r + s = p * q * D ^ 2))) := by
  have hsub := isCoprime_sub_add_of_odd hc hodd
  rcases Int.even_or_odd s with ⟨s₁, hs₁⟩ | hso
  · left
    have hs₁0 : 0 < s₁ := by omega
    have hdvd : s₁ ∣ s := ⟨2, by rw [hs₁]; ring⟩
    have h' : r * s₁ * (r - s) * (r + s) = p * q * w ^ 2 := by
      have : 2 * (r * s₁ * (r - s) * (r + s)) = 2 * (p * q * w ^ 2) := by
        rw [hs₁] at h ⊢; linear_combination h
      exact mul_left_cancel₀ two_ne_zero this
    exact ⟨s₁, by omega, four_factor_two_primes hp hp0 hq hq0
      (hc.of_isCoprime_of_dvd_right hdvd) (isCoprime_left_sub hc) (isCoprime_left_add hc)
      ((isCoprime_right_sub hc).of_isCoprime_of_dvd_left hdvd)
      ((isCoprime_right_add hc).of_isCoprime_of_dvd_left hdvd)
      hsub (by omega) hs₁0 (by omega) (by omega) h'⟩
  · right
    obtain ⟨r₁, hr₁⟩ : Even r := by
      rw [Int.even_iff]
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨j, hj⟩ := hso
      omega
    have hdvd : r₁ ∣ r := ⟨2, by rw [hr₁]; ring⟩
    have h' : r₁ * s * (r - s) * (r + s) = p * q * w ^ 2 := by
      have : 2 * (r₁ * s * (r - s) * (r + s)) = 2 * (p * q * w ^ 2) := by
        rw [hr₁] at h ⊢; linear_combination h
      exact mul_left_cancel₀ two_ne_zero this
    exact ⟨r₁, by omega, four_factor_two_primes hp hp0 hq hq0
      (hc.of_isCoprime_of_dvd_left hdvd)
      ((isCoprime_left_sub hc).of_isCoprime_of_dvd_left hdvd)
      ((isCoprime_left_add hc).of_isCoprime_of_dvd_left hdvd)
      (isCoprime_right_sub hc) (isCoprime_right_add hc) hsub (by omega) hs (by omega) (by omega)
      h'⟩

/-! ### (C3) `2 p q`, `p ≡ q ≡ 5 (mod 8)` -/

/-- **Descent step for `2 p q`, `p ≡ q ≡ 5 (mod 8)`.** -/
theorem descent_two_pq_five_five {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp8 : p % 8 = 5)
    (hq8 : q % 8 = 5) {r s w : ℤ} (hs : 0 < s) (hsr : s < r) (hc : IsCoprime r s)
    (hodd : Odd (r - s)) (h : r * s * (r - s) * (r + s) = 2 * (p * q) * w ^ 2) :
    ∃ r' s' w' : ℤ, 0 < s' ∧ s' < r' ∧ IsCoprime r' s' ∧ Odd (r' - s') ∧
      r' * s' * (r' - s') * (r' + s') = 2 * (p * q) * w' ^ 2 ∧ r' < r := by
  have := Fact.mk hp
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hQ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hP0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hQ0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hP8 : (p : ℤ) % 8 = 5 := by exact_mod_cast hp8
  have hQ8 : (q : ℤ) % 8 = 5 := by exact_mod_cast hq8
  have hPQ8 : ((p : ℤ) * q) % 8 = 1 := by rw [Int.mul_emod, hP8, hQ8]; rfl
  have hodd2 : (r - s) % 2 = 1 := Int.odd_iff.mp hodd
  have hcop := not_dvd_both hP hc
  have hn2 : ¬ IsSquare (((2 : ℤ)) : ZMod p) := by
    rw [Int.cast_ofNat, ZMod.exists_sq_eq_two_iff (by omega)]
    omega
  have hn2' : ¬ IsSquare (((-2 : ℤ)) : ZMod p) := by
    rw [Int.cast_neg, Int.cast_ofNat, ZMod.exists_sq_eq_neg_two_iff (by omega)]
    omega
  rcases even_split hP hP0 hQ hQ0 hs hsr hc hodd h with
    ⟨s₁, hs₁, A, B, C, D, hA, hB, hC, hD, H⟩ | ⟨r₁, hr₁, A, B, C, D, hA, hB, hC, hD, H⟩
  · rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · -- `r = p q A²`, `s = 2 B²`: `C² + 2 B² = p q A²`, and `−2` is not a square mod `p`
      exfalso
      obtain ⟨-, hB'⟩ := dvd_of_dvd_sq_sub_mul_sq hn2'
        (⟨q * A ^ 2, by linear_combination h1 - 2 * h2 - h3 - hs₁⟩ :
          (p : ℤ) ∣ C ^ 2 - -2 * B ^ 2)
      exact hcop ⟨⟨q * A ^ 2, by rw [h1]; ring⟩, by
        rw [hs₁, h2]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
          (dvd_pow hB' two_ne_zero) _) _⟩
    all_goals try kill8
    · -- `s = 2 p q B²`: Fermat's halving step
      exact descend_even (by omega) hA hC hD hs hc hodd (by rw [h1]; ring) hs₁ (by rw [h2])
        (by rw [h3]; ring) (by rw [h4]; ring)
    · -- `r − s = p q C²`: `A² − 2 B² = p q C²`, and `2` is not a square mod `p`
      exfalso
      obtain ⟨hA', hB'⟩ := dvd_of_dvd_sq_sub_mul_sq hn2
        (⟨q * C ^ 2, by linear_combination -h1 + 2 * h2 + h3 + hs₁⟩ :
          (p : ℤ) ∣ A ^ 2 - 2 * B ^ 2)
      exact hcop ⟨by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _, by
        rw [hs₁, h2]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
          (dvd_pow hB' two_ne_zero) _) _⟩
    · -- `r + s = p q D²`: `A² + 2 B² = p q D²`, and `−2` is not a square mod `p`
      exfalso
      obtain ⟨hA', hB'⟩ := dvd_of_dvd_sq_sub_mul_sq hn2'
        (⟨q * D ^ 2, by linear_combination -h1 - 2 * h2 + h4 - hs₁⟩ :
          (p : ℤ) ∣ A ^ 2 - -2 * B ^ 2)
      exact hcop ⟨by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _, by
        rw [hs₁, h2]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
          (dvd_pow hB' two_ne_zero) _) _⟩
  · rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    all_goals kill8

/-! ### (C4) `2 p q`, `p ≡ 1`, `q ≡ 5 (mod 8)`, `(p/q) = −1` -/

/-- **Descent step for `2 p q`, `p ≡ 1`, `q ≡ 5 (mod 8)`, `p` not a square mod `q`.** -/
theorem descent_two_pq_one_five {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp8 : p % 8 = 1)
    (hq8 : q % 8 = 5) (hpq : ¬ IsSquare (((p : ℤ)) : ZMod q)) {r s w : ℤ} (hs : 0 < s)
    (hsr : s < r) (hc : IsCoprime r s) (hodd : Odd (r - s))
    (h : r * s * (r - s) * (r + s) = 2 * (p * q) * w ^ 2) :
    ∃ r' s' w' : ℤ, 0 < s' ∧ s' < r' ∧ IsCoprime r' s' ∧ Odd (r' - s') ∧
      r' * s' * (r' - s') * (r' + s') = 2 * (p * q) * w' ^ 2 ∧ r' < r := by
  have := Fact.mk hq
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hQ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hP0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hQ0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hP8 : (p : ℤ) % 8 = 1 := by exact_mod_cast hp8
  have hQ8 : (q : ℤ) % 8 = 5 := by exact_mod_cast hq8
  have hPQ8 : ((p : ℤ) * q) % 8 = 5 := by rw [Int.mul_emod, hP8, hQ8]; rfl
  have hodd2 : (r - s) % 2 = 1 := Int.odd_iff.mp hodd
  have hcop := not_dvd_both hQ hc
  rcases even_split hP hP0 hQ hQ0 hs hsr hc hodd h with
    ⟨s₁, hs₁, A, B, C, D, hA, hB, hC, hD, H⟩ | ⟨r₁, hr₁, A, B, C, D, hA, hB, hC, hD, H⟩
  · rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    all_goals try kill8
    · -- `r = p A²`, `s = 2 q B²`: `C² − p A² = −2 q B²`
      exfalso
      obtain ⟨-, hA'⟩ := dvd_of_dvd_sq_sub_mul_sq hpq
        (⟨-(2 * B ^ 2), by linear_combination h1 - 2 * h2 - h3 - hs₁⟩ :
          (q : ℤ) ∣ C ^ 2 - p * A ^ 2)
      exact hcop ⟨by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _,
        ⟨2 * B ^ 2, by rw [hs₁, h2]; ring⟩⟩
    · -- `s = 2 p q B²`: Fermat's halving step
      exact descend_even (by omega) hA hC hD hs hc hodd (by rw [h1]; ring) hs₁ (by rw [h2])
        (by rw [h3]; ring) (by rw [h4]; ring)
    · -- `s = 2 q B²`, `r − s = p C²`: `A² − p C² = 2 q B²`
      exfalso
      obtain ⟨hA', -⟩ := dvd_of_dvd_sq_sub_mul_sq hpq
        (⟨2 * B ^ 2, by linear_combination -h1 + 2 * h2 + h3 + hs₁⟩ :
          (q : ℤ) ∣ A ^ 2 - p * C ^ 2)
      exact hcop ⟨by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _,
        ⟨2 * B ^ 2, by rw [hs₁, h2]; ring⟩⟩
    · -- `s = 2 q B²`, `r + s = p D²`: `A² − p D² = −2 q B²`
      exfalso
      obtain ⟨hA', -⟩ := dvd_of_dvd_sq_sub_mul_sq hpq
        (⟨-(2 * B ^ 2), by linear_combination -h1 - 2 * h2 + h4 - hs₁⟩ :
          (q : ℤ) ∣ A ^ 2 - p * D ^ 2)
      exact hcop ⟨by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _,
        ⟨2 * B ^ 2, by rw [hs₁, h2]; ring⟩⟩
  · rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    all_goals kill8


/-! ### (C5) `p q`, `p ≡ 5`, `q ≡ 7 (mod 8)`, `(p/q) = −1` -/

/-- **Descent step for `p q`, `p ≡ 5`, `q ≡ 7 (mod 8)`, `p` not a square mod `q`.** -/
theorem descent_pq_five_seven {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp8 : p % 8 = 5)
    (hq8 : q % 8 = 7) (hpq : ¬ IsSquare (((p : ℤ)) : ZMod q)) {r s w : ℤ} (hs : 0 < s)
    (hsr : s < r) (hc : IsCoprime r s) (hodd : Odd (r - s))
    (h : r * s * (r - s) * (r + s) = p * q * w ^ 2) :
    ∃ r' s' w' : ℤ, 0 < s' ∧ s' < r' ∧ IsCoprime r' s' ∧ Odd (r' - s') ∧
      r' * s' * (r' - s') * (r' + s') = p * q * w' ^ 2 ∧ r' < r := by
  have := Fact.mk hq
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hQ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hP0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hQ0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hP8 : (p : ℤ) % 8 = 5 := by exact_mod_cast hp8
  have hQ8 : (q : ℤ) % 8 = 7 := by exact_mod_cast hq8
  have hPQ8 : ((p : ℤ) * q) % 8 = 3 := by rw [Int.mul_emod, hP8, hQ8]; rfl
  have hodd2 : (r - s) % 2 = 1 := Int.odd_iff.mp hodd
  have hcop := not_dvd_both hQ hc
  obtain ⟨A, B, C, D, hA, hB, hC, hD, H⟩ := four_factor_two_primes hP hP0 hQ hQ0 hc
    (isCoprime_left_sub hc) (isCoprime_left_add hc) (isCoprime_right_sub hc)
    (isCoprime_right_add hc) (isCoprime_sub_add_of_odd hc hodd) (by omega) hs (by omega)
    (by omega) h
  rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  all_goals try kill8
  · -- `r = p A²`, `s = q B²`: `C² − p A² = −q B²`
    exfalso
    obtain ⟨-, hA'⟩ := dvd_of_dvd_sq_sub_mul_sq hpq
      (⟨-B ^ 2, by linear_combination -h3 + h1 - h2⟩ : (q : ℤ) ∣ C ^ 2 - p * A ^ 2)
    exact hcop ⟨by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _,
      ⟨B ^ 2, h2⟩⟩
  · -- `r = p A²`, `r − s = q C²`: `B² − p A² = −q C²`
    exfalso
    obtain ⟨hB', hA'⟩ := dvd_of_dvd_sq_sub_mul_sq hpq
      (⟨-C ^ 2, by linear_combination h1 - h2 - h3⟩ : (q : ℤ) ∣ B ^ 2 - p * A ^ 2)
    exact hcop ⟨by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _,
      by rw [h2]; exact dvd_mul_of_dvd_right (dvd_pow hB' two_ne_zero) _⟩
  · -- `s = p q B²`: Fermat's halving step
    exact descend_odd (by omega) hA hC hD hs hc hodd (by rw [h1]; ring) (by rw [h2])
      (by rw [h3]; ring) (by rw [h4]; ring)
  · -- `s = p B²`, `r − s = q C²`: `A² − p B² = q C²`
    exfalso
    obtain ⟨hA', hB'⟩ := dvd_of_dvd_sq_sub_mul_sq hpq
      (⟨C ^ 2, by linear_combination -h1 + h2 + h3⟩ : (q : ℤ) ∣ A ^ 2 - p * B ^ 2)
    exact hcop ⟨by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _,
      by rw [h2]; exact dvd_mul_of_dvd_right (dvd_pow hB' two_ne_zero) _⟩

/-! ### (C6) `2 p q`, `p ≡ q ≡ 3 (mod 8)` -/

/-- **Descent step for `2 p q`, `p ≡ q ≡ 3 (mod 8)`.** -/
theorem descent_two_pq_three_three {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp8 : p % 8 = 3)
    (hq8 : q % 8 = 3) {r s w : ℤ} (hs : 0 < s) (hsr : s < r) (hc : IsCoprime r s)
    (hodd : Odd (r - s)) (h : r * s * (r - s) * (r + s) = 2 * (p * q) * w ^ 2) :
    ∃ r' s' w' : ℤ, 0 < s' ∧ s' < r' ∧ IsCoprime r' s' ∧ Odd (r' - s') ∧
      r' * s' * (r' - s') * (r' + s') = 2 * (p * q) * w' ^ 2 ∧ r' < r := by
  have := Fact.mk hp
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hQ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hP0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hQ0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hP8 : (p : ℤ) % 8 = 3 := by exact_mod_cast hp8
  have hQ8 : (q : ℤ) % 8 = 3 := by exact_mod_cast hq8
  have hPQ8 : ((p : ℤ) * q) % 8 = 1 := by rw [Int.mul_emod, hP8, hQ8]; rfl
  have hodd2 : (r - s) % 2 = 1 := Int.odd_iff.mp hodd
  have hcop := not_dvd_both hP hc
  have hn2 : ¬ IsSquare (((2 : ℤ)) : ZMod p) := by
    rw [Int.cast_ofNat, ZMod.exists_sq_eq_two_iff (by omega)]
    omega
  rcases even_split hP hP0 hQ hQ0 hs hsr hc hodd h with
    ⟨s₁, hs₁, A, B, C, D, hA, hB, hC, hD, H⟩ | ⟨r₁, hr₁, A, B, C, D, hA, hB, hC, hD, H⟩
  · rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    all_goals try kill8
    · -- `r = p q A²`, `s = 2 B²`: `D² − 2 B² = p q A²`
      exfalso
      obtain ⟨hD', hB'⟩ := dvd_of_dvd_sq_sub_mul_sq hn2
        (⟨q * A ^ 2, by linear_combination h1 + 2 * h2 - h4 + hs₁⟩ :
          (p : ℤ) ∣ D ^ 2 - 2 * B ^ 2)
      exact hcop ⟨⟨q * A ^ 2, by rw [h1]; ring⟩, by
        rw [hs₁, h2]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
          (dvd_pow hB' two_ne_zero) _) _⟩
    · -- `s = 2 p q B²`: Fermat's halving step
      exact descend_even (by omega) hA hC hD hs hc hodd (by rw [h1]; ring) hs₁ (by rw [h2])
        (by rw [h3]; ring) (by rw [h4]; ring)
    · -- `r − s = p q C²`: `D² − 2 A² = −p q C²`
      exfalso
      obtain ⟨hD', hA'⟩ := dvd_of_dvd_sq_sub_mul_sq hn2
        (⟨-(q * C ^ 2), by linear_combination 2 * h1 - h3 - h4⟩ : (p : ℤ) ∣ D ^ 2 - 2 * A ^ 2)
      have hr : (p : ℤ) ∣ r := by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _
      have hrs : (p : ℤ) ∣ r + s := by
        rw [h4]; exact dvd_mul_of_dvd_right (dvd_pow hD' two_ne_zero) _
      exact hcop ⟨hr, by simpa using dvd_sub hrs hr⟩
    · -- `r + s = p q D²`: `C² − 2 A² = −p q D²`
      exfalso
      obtain ⟨hC', hA'⟩ := dvd_of_dvd_sq_sub_mul_sq hn2
        (⟨-(q * D ^ 2), by linear_combination 2 * h1 - h3 - h4⟩ : (p : ℤ) ∣ C ^ 2 - 2 * A ^ 2)
      have hr : (p : ℤ) ∣ r := by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow hA' two_ne_zero) _
      have hrs : (p : ℤ) ∣ r - s := by
        rw [h3]; exact dvd_mul_of_dvd_right (dvd_pow hC' two_ne_zero) _
      exact hcop ⟨hr, by simpa using dvd_sub hr hrs⟩
  · rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    all_goals kill8

/-! ### (C7) `2 p q`, `p ≡ 3`, `q ≡ 7 (mod 8)`, `(p/q) = −1` -/

/-- **Descent step for `2 p q`, `p ≡ 3`, `q ≡ 7 (mod 8)`, `p` not a square mod `q`.** -/
theorem descent_two_pq_three_seven {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp8 : p % 8 = 3)
    (hq8 : q % 8 = 7) (hpq : ¬ IsSquare (((p : ℤ)) : ZMod q)) {r s w : ℤ} (hs : 0 < s)
    (hsr : s < r) (hc : IsCoprime r s) (hodd : Odd (r - s))
    (h : r * s * (r - s) * (r + s) = 2 * (p * q) * w ^ 2) :
    ∃ r' s' w' : ℤ, 0 < s' ∧ s' < r' ∧ IsCoprime r' s' ∧ Odd (r' - s') ∧
      r' * s' * (r' - s') * (r' + s') = 2 * (p * q) * w' ^ 2 ∧ r' < r := by
  have := Fact.mk hq
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hQ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hP0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hQ0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hP8 : (p : ℤ) % 8 = 3 := by exact_mod_cast hp8
  have hQ8 : (q : ℤ) % 8 = 7 := by exact_mod_cast hq8
  have hPQ8 : ((p : ℤ) * q) % 8 = 5 := by rw [Int.mul_emod, hP8, hQ8]; rfl
  have hodd2 : (r - s) % 2 = 1 := Int.odd_iff.mp hodd
  have hcop := not_dvd_both hQ hc
  rcases even_split hP hP0 hQ hQ0 hs hsr hc hodd h with
    ⟨s₁, hs₁, A, B, C, D, hA, hB, hC, hD, H⟩ | ⟨r₁, hr₁, A, B, C, D, hA, hB, hC, hD, H⟩
  · rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    all_goals try kill8
    · -- `s = 2 p q B²`: Fermat's halving step
      exact descend_even (by omega) hA hC hD hs hc hodd (by rw [h1]; ring) hs₁ (by rw [h2])
        (by rw [h3]; ring) (by rw [h4]; ring)
    · -- `s = 2 B²`, `r − s = q C²`, `r + s = p D²`: `(2B)² − p D² = −q C²`
      exfalso
      obtain ⟨hB', hD'⟩ := dvd_of_dvd_sq_sub_mul_sq hpq
        (⟨-C ^ 2, by linear_combination -4 * h2 + h4 - h3 - 2 * hs₁⟩ :
          (q : ℤ) ∣ (2 * B) ^ 2 - p * D ^ 2)
      have hs' : (q : ℤ) ∣ s := by
        rw [hs₁, h2]
        have := dvd_mul_of_dvd_right hB' B
        rwa [show B * (2 * B) = 2 * (1 * B ^ 2) by ring] at this
      have hrs : (q : ℤ) ∣ r + s := by
        rw [h4]; exact dvd_mul_of_dvd_right (dvd_pow hD' two_ne_zero) _
      exact hcop ⟨by simpa using dvd_sub hrs hs', hs'⟩
  · rcases H with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    all_goals try kill8
    · -- `r = 2 p A²`, `r − s = q C²`: `D² − p (2A)² = −q C²`
      exfalso
      obtain ⟨hD', hA'⟩ := dvd_of_dvd_sq_sub_mul_sq hpq
        (⟨-C ^ 2, by linear_combination 4 * h1 - h4 - h3 + 2 * hr₁⟩ :
          (q : ℤ) ∣ D ^ 2 - p * (2 * A) ^ 2)
      have hr : (q : ℤ) ∣ r := by
        rw [hr₁, h1]
        have := dvd_mul_of_dvd_right hA' (p * A)
        rwa [show (p : ℤ) * A * (2 * A) = 2 * (p * A ^ 2) by ring] at this
      have hrs : (q : ℤ) ∣ r + s := by
        rw [h4]; exact dvd_mul_of_dvd_right (dvd_pow hD' two_ne_zero) _
      exact hcop ⟨hr, by simpa using dvd_sub hrs hr⟩
    · -- `s = q B²`, `r − s = p C²`: `D² − p C² = 2 q B²`
      exfalso
      obtain ⟨hD', hC'⟩ := dvd_of_dvd_sq_sub_mul_sq hpq
        (⟨2 * B ^ 2, by linear_combination 2 * h2 + h3 - h4⟩ : (q : ℤ) ∣ D ^ 2 - p * C ^ 2)
      have hs' : (q : ℤ) ∣ s := ⟨B ^ 2, h2⟩
      have hrs : (q : ℤ) ∣ r - s := by
        rw [h3]; exact dvd_mul_of_dvd_right (dvd_pow hC' two_ne_zero) _
      exact hcop ⟨by simpa using dvd_add hrs hs', hs'⟩

/-! ### The theorems -/

theorem squarefree_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Squarefree (p * q) :=
  Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hp hq).mpr hpq, hp.prime.squarefree,
    hq.prime.squarefree⟩

theorem squarefree_two_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) : Squarefree (2 * (p * q)) :=
  Nat.squarefree_mul_iff.mpr
    ⟨Nat.Coprime.mul_right ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
      ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)),
      Nat.squarefree_two, squarefree_pq hp hq hpq⟩

/-- **(C1)** `p q` is not congruent for distinct primes `p ≡ q ≡ 3 (mod 8)`. -/
theorem not_isCongruent_pq_three_three {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp8 : p % 8 = 3) (hq8 : q % 8 = 3) (hpq : p ≠ q) :
    ¬ PerfectCuboid.CongruentRank.IsCongruent ((p * q : ℕ) : ℚ) := fun hC ↦ by
  obtain ⟨r, s, w, hs, hsr, hc, hodd, h⟩ := exists_rs_of_isCongruent (squarefree_pq hp hq hpq) hC
  exact ne_mul_sq_of_descent (descent_pq_three_three hp hq hp8 hq8) hs hsr hc hodd
    (by push_cast at h; exact h)

/-- **(C2)** `p q` is not congruent for primes `p ≡ 1`, `q ≡ 3 (mod 8)` with `(p/q) = −1`. -/
theorem not_isCongruent_pq_one_three {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp8 : p % 8 = 1) (hq8 : q % 8 = 3) (hpq : @legendreSym q ⟨hq⟩ p = -1) :
    ¬ PerfectCuboid.CongruentRank.IsCongruent ((p * q : ℕ) : ℚ) := fun hC ↦ by
  have := Fact.mk hq
  have hns : ¬ IsSquare (((p : ℤ)) : ZMod q) := (legendreSym.eq_neg_one_iff q).mp hpq
  obtain ⟨r, s, w, hs, hsr, hc, hodd, h⟩ :=
    exists_rs_of_isCongruent (squarefree_pq hp hq (by omega)) hC
  exact ne_mul_sq_of_descent (descent_pq_one_three hp hq hp8 hq8 hns) hs hsr hc hodd
    (by push_cast at h; exact h)

/-- **(C3)** `2 p q` is not congruent for distinct primes `p ≡ q ≡ 5 (mod 8)`. -/
theorem not_isCongruent_two_pq_five_five {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp8 : p % 8 = 5) (hq8 : q % 8 = 5) (hpq : p ≠ q) :
    ¬ PerfectCuboid.CongruentRank.IsCongruent ((2 * (p * q) : ℕ) : ℚ) := fun hC ↦ by
  obtain ⟨r, s, w, hs, hsr, hc, hodd, h⟩ :=
    exists_rs_of_isCongruent (squarefree_two_pq hp hq hpq (by omega) (by omega)) hC
  exact ne_mul_sq_of_descent (descent_two_pq_five_five hp hq hp8 hq8) hs hsr hc hodd
    (by push_cast at h; exact h)

/-- **(C4)** `2 p q` is not congruent for primes `p ≡ 1`, `q ≡ 5 (mod 8)` with `(p/q) = −1`. -/
theorem not_isCongruent_two_pq_one_five {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp8 : p % 8 = 1) (hq8 : q % 8 = 5) (hpq : @legendreSym q ⟨hq⟩ p = -1) :
    ¬ PerfectCuboid.CongruentRank.IsCongruent ((2 * (p * q) : ℕ) : ℚ) := fun hC ↦ by
  have := Fact.mk hq
  have hns : ¬ IsSquare (((p : ℤ)) : ZMod q) := (legendreSym.eq_neg_one_iff q).mp hpq
  obtain ⟨r, s, w, hs, hsr, hc, hodd, h⟩ :=
    exists_rs_of_isCongruent (squarefree_two_pq hp hq (by omega) (by omega) (by omega)) hC
  exact ne_mul_sq_of_descent (descent_two_pq_one_five hp hq hp8 hq8 hns) hs hsr hc hodd
    (by push_cast at h; exact h)


/-- **(C5)** `p q` is not congruent for primes `p ≡ 5`, `q ≡ 7 (mod 8)` with `(p/q) = −1`. -/
theorem not_isCongruent_pq_five_seven {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp8 : p % 8 = 5) (hq8 : q % 8 = 7) (hpq : @legendreSym q ⟨hq⟩ p = -1) :
    ¬ PerfectCuboid.CongruentRank.IsCongruent ((p * q : ℕ) : ℚ) := fun hC ↦ by
  have := Fact.mk hq
  have hns : ¬ IsSquare (((p : ℤ)) : ZMod q) := (legendreSym.eq_neg_one_iff q).mp hpq
  obtain ⟨r, s, w, hs, hsr, hc, hodd, h⟩ :=
    exists_rs_of_isCongruent (squarefree_pq hp hq (by omega)) hC
  exact ne_mul_sq_of_descent (descent_pq_five_seven hp hq hp8 hq8 hns) hs hsr hc hodd
    (by push_cast at h; exact h)

/-- **(C6)** `2 p q` is not congruent for distinct primes `p ≡ q ≡ 3 (mod 8)`. -/
theorem not_isCongruent_two_pq_three_three {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp8 : p % 8 = 3) (hq8 : q % 8 = 3) (hpq : p ≠ q) :
    ¬ PerfectCuboid.CongruentRank.IsCongruent ((2 * (p * q) : ℕ) : ℚ) := fun hC ↦ by
  obtain ⟨r, s, w, hs, hsr, hc, hodd, h⟩ :=
    exists_rs_of_isCongruent (squarefree_two_pq hp hq hpq (by omega) (by omega)) hC
  exact ne_mul_sq_of_descent (descent_two_pq_three_three hp hq hp8 hq8) hs hsr hc hodd
    (by push_cast at h; exact h)

/-- **(C7)** `2 p q` is not congruent for primes `p ≡ 3`, `q ≡ 7 (mod 8)` with `(p/q) = −1`. -/
theorem not_isCongruent_two_pq_three_seven {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp8 : p % 8 = 3) (hq8 : q % 8 = 7) (hpq : @legendreSym q ⟨hq⟩ p = -1) :
    ¬ PerfectCuboid.CongruentRank.IsCongruent ((2 * (p * q) : ℕ) : ℚ) := fun hC ↦ by
  have := Fact.mk hq
  have hns : ¬ IsSquare (((p : ℤ)) : ZMod q) := (legendreSym.eq_neg_one_iff q).mp hpq
  obtain ⟨r, s, w, hs, hsr, hc, hodd, h⟩ :=
    exists_rs_of_isCongruent (squarefree_two_pq hp hq (by omega) (by omega) (by omega)) hC
  exact ne_mul_sq_of_descent (descent_two_pq_three_seven hp hq hp8 hq8 hns) hs hsr hc hodd
    (by push_cast at h; exact h)

/-- **(C1)**, in the form `¬ IsCongruent (p * q : ℚ)`. -/
theorem not_isCongruent_pq_three_three' {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp8 : p % 8 = 3) (hq8 : q % 8 = 3) (hpq : p ≠ q) :
    ¬ PerfectCuboid.CongruentRank.IsCongruent ((p : ℚ) * q) := by
  have := not_isCongruent_pq_three_three hp hq hp8 hq8 hpq
  push_cast at this
  exact this

end FermatTriangle

/-! ### Cuboid corollaries -/

namespace PerfectCuboid

open CongruentRank

/-- A congruent number is never `N m²` for a non-congruent `N`. -/
theorem ne_mul_sq_of_not_isCongruent {D N : ℕ} (hD : IsCongruent (D : ℚ))
    (hN : ¬ IsCongruent (N : ℚ)) (m : ℕ) : D ≠ N * m ^ 2 := by
  rintro rfl
  have hm : (m : ℚ) ≠ 0 := by
    rintro h0
    have := hD.pos
    push_cast [h0] at this
    simp at this
  push_cast at hD
  rw [mul_comm, isCongruent_mul_sq_iff hm] at hD
  exact hN hD

/-- `D` is not in any of the square classes C1–C7: `D ≠ N m²` for `N = p q` (C1, C2) or
`N = 2 p q` (C3, C4). -/
def TwoPrimeAvoid (D : ℕ) : Prop :=
  ∀ (p q m : ℕ) (_hp : p.Prime) (hq : q.Prime),
    ((p % 8 = 3 ∧ q % 8 = 3 ∧ p ≠ q) → D ≠ p * q * m ^ 2) ∧
    ((p % 8 = 1 ∧ q % 8 = 3 ∧ @legendreSym q ⟨hq⟩ p = -1) → D ≠ p * q * m ^ 2) ∧
    ((p % 8 = 5 ∧ q % 8 = 5 ∧ p ≠ q) → D ≠ 2 * (p * q) * m ^ 2) ∧
    ((p % 8 = 1 ∧ q % 8 = 5 ∧ @legendreSym q ⟨hq⟩ p = -1) → D ≠ 2 * (p * q) * m ^ 2) ∧
    ((p % 8 = 5 ∧ q % 8 = 7 ∧ @legendreSym q ⟨hq⟩ p = -1) → D ≠ p * q * m ^ 2) ∧
    ((p % 8 = 3 ∧ q % 8 = 3 ∧ p ≠ q) → D ≠ 2 * (p * q) * m ^ 2) ∧
    ((p % 8 = 3 ∧ q % 8 = 7 ∧ @legendreSym q ⟨hq⟩ p = -1) → D ≠ 2 * (p * q) * m ^ 2)

/-- A congruent number avoids the classes C1–C7. -/
theorem twoPrimeAvoid_of_isCongruent {D : ℕ} (hD : IsCongruent (D : ℚ)) : TwoPrimeAvoid D :=
  fun _ _ m hp hq ↦
  ⟨fun ⟨h1, h2, h3⟩ ↦ ne_mul_sq_of_not_isCongruent hD
      (FermatTriangle.not_isCongruent_pq_three_three hp hq h1 h2 h3) m,
    fun ⟨h1, h2, h3⟩ ↦ ne_mul_sq_of_not_isCongruent hD
      (FermatTriangle.not_isCongruent_pq_one_three hp hq h1 h2 h3) m,
    fun ⟨h1, h2, h3⟩ ↦ ne_mul_sq_of_not_isCongruent hD
      (FermatTriangle.not_isCongruent_two_pq_five_five hp hq h1 h2 h3) m,
    fun ⟨h1, h2, h3⟩ ↦ ne_mul_sq_of_not_isCongruent hD
      (FermatTriangle.not_isCongruent_two_pq_one_five hp hq h1 h2 h3) m,
    fun ⟨h1, h2, h3⟩ ↦ ne_mul_sq_of_not_isCongruent hD
      (FermatTriangle.not_isCongruent_pq_five_seven hp hq h1 h2 h3) m,
    fun ⟨h1, h2, h3⟩ ↦ ne_mul_sq_of_not_isCongruent hD
      (FermatTriangle.not_isCongruent_two_pq_three_three hp hq h1 h2 h3) m,
    fun ⟨h1, h2, h3⟩ ↦ ne_mul_sq_of_not_isCongruent hD
      (FermatTriangle.not_isCongruent_two_pq_three_seven hp hq h1 h2 h3) m⟩

variable {a b c : ℕ}

/-- **`(a+d)(a+e)(g+d)(g+e)` avoids the classes C1–C7.** -/
theorem IsPerfectCuboid.diag_prod_ed_twoPrimeAvoid (h : IsPerfectCuboid a b c) {d e g : ℕ}
    (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    TwoPrimeAvoid ((a + d) * (a + e) * (g + d) * (g + e)) :=
  twoPrimeAvoid_of_isCongruent (h.isCongruent_ed hd he hg)

/-- **`(b+d)(b+f)(g+d)(g+f)` avoids the classes C1–C7.** -/
theorem IsPerfectCuboid.diag_prod_fd_twoPrimeAvoid (h : IsPerfectCuboid a b c) {d f g : ℕ}
    (hd : d ^ 2 = a ^ 2 + b ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    TwoPrimeAvoid ((b + d) * (b + f) * (g + d) * (g + f)) :=
  twoPrimeAvoid_of_isCongruent (h.isCongruent_fd hd hf hg)

/-- **`(c+e)(c+f)(g+e)(g+f)` avoids the classes C1–C7.** -/
theorem IsPerfectCuboid.diag_prod_fe_twoPrimeAvoid (h : IsPerfectCuboid a b c) {e f g : ℕ}
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    TwoPrimeAvoid ((c + e) * (c + f) * (g + e) * (g + f)) :=
  twoPrimeAvoid_of_isCongruent (h.isCongruent_fe he hf hg)

/-- **`(a+d)(a+e)(g+d)(g+e) ≠ p q m²` for distinct primes `p ≡ q ≡ 3 (mod 8)`**
(the other eleven class/diagonal
combinations are the other components of `diag_prod_*_twoPrimeAvoid`). -/
theorem IsPerfectCuboid.diag_prod_ed_ne_pq_mul_sq (h : IsPerfectCuboid a b c) {d e g : ℕ}
    (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp8 : p % 8 = 3) (hq8 : q % 8 = 3) (hpq : p ≠ q) (m : ℕ) :
    (a + d) * (a + e) * (g + d) * (g + e) ≠ p * q * m ^ 2 :=
  (h.diag_prod_ed_twoPrimeAvoid hd he hg p q m hp hq).1 ⟨hp8, hq8, hpq⟩

/-- **The squarefree part `N` of `abcg/2` avoids the classes C1–C7** (with `m = 1`). -/
theorem IsPerfectCuboid.squarefree_part_twoPrimeAvoid (h : IsPerfectCuboid a b c) :
    ∃ N : ℕ, Squarefree N ∧ (∃ (g : ℕ) (s : ℚ), g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 ∧
      (a * b * c * g : ℚ) / 2 = N * s ^ 2) ∧ TwoPrimeAvoid N := by
  obtain ⟨N, hsq, g, s, hg, hs, hN, -⟩ := h.isCongruent
  exact ⟨N, hsq, ⟨g, s, hg, hs⟩, twoPrimeAvoid_of_isCongruent hN⟩

end PerfectCuboid
