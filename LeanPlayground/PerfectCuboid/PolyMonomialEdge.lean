module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolynomialCuboid

/-!
# Polynomial cuboids II: a monomial edge of any degree forces proportionality

Round 13 (`PolynomialCuboid.lean`) proved that an edge `α X^k` coprime to the other two edges is
impossible, and that a linear edge `α X` forces proportional edges. Here we remove the coprimality
assumption for every `k`:

* **Theorem M** (`IsPolyCuboid.proportional_of_monomial_edge`): if `(α X^k, b, c)` is a polynomial
  cuboid then `b = β X^k` and `c = γ X^k`. The face `b² + c²` is not used
  (`monomial_edge_proportional`, face-cuboid form).
* Cases: `monomial_leg_X_pow` (leg structure without coprimality), `not_squares_monomial_mixed`,
  `not_squares_monomial_equal`, `not_squares_monomial_strict`.
* `IsPolyCuboid.proportional_of_single_root_edge`: the same for an edge `α (X − r)^k`;
  `exists_isPolyCuboid_single_root_iff`: a polynomial cuboid with an edge having a single root
  (of any multiplicity) exists iff an integer perfect cuboid exists;
  `IsPolyCuboid.edge_ne_C_mul_X_sub_C_pow_of_not_proportional`: a non-proportional polynomial
  cuboid has no such edge.

The engine is a lemma on sparse squares:

* **Lemma S** (`sq_sparse_recursion`, `coeff_eq_zero_of_sq_sparse`, `coeff_ne_zero_of_sq_sparse`):
  if `F² ≡ f₀² + c X^m (mod X^N)` with `f₀ = F(0) ≠ 0`, `c ≠ 0`, then below `N` the coefficients of
  `F` vanish off the multiples of `m` and never vanish on them (the ODE `2 F' Q = Q' F`,
  `Q = f₀² + c X^m`, read on coefficients).
* **Lemma F** (`not_isSquare_four_term`): `u² + u'² X^m + v'² X^(2n−m) + v² X^(2n)` with
  `u u' v' v ≠ 0`, `0 < m < n`, is never a square in `K[X]` (`K` any ordered field).

Lemmas S and F are stated over an arbitrary ordered field; the cuboid theorems are over `ℚ`.
-/
@[expose] public section

open Polynomial

namespace PerfectCuboid.Poly

/-! ### Lemma S: sparse square roots

Stated over any ordered field `K` (Lemma S only needs characteristic zero; the case `n = 2m` of
Lemma F uses the order). -/

section SparseSquares

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The recursion behind Lemma S.** If `F² ≡ f₀² + c X^m (mod X^N)` then for `j + 1 < N`,
`2 f₀² (j+1) f_{j+1} = c (3m − 2(j+1)) f_{j+1−m}` (and `= 0` when `j + 1 < m`). -/
theorem sq_sparse_recursion {F : K[X]} {c : K} {m N : ℕ} (hm : 0 < m)
    (h : ∀ j < N, (F ^ 2).coeff j = (C (F.coeff 0 ^ 2) + C c * X ^ m).coeff j)
    (j : ℕ) (hj : j + 1 < N) :
    2 * F.coeff 0 ^ 2 * ((j : K) + 1) * F.coeff (j + 1) =
      if m ≤ j + 1 then c * (3 * (m : K) - 2 * ((j : K) + 1)) * F.coeff (j + 1 - m) else 0 := by
  set a := F.coeff 0 ^ 2 with ha
  set Q : K[X] := C a + C c * X ^ m with hQ
  set G : K[X] := F ^ 2 - Q with hG
  have hGd : X ^ N ∣ G := X_pow_dvd_iff.mpr fun d hd => by
    rw [hG, coeff_sub, h d hd, sub_self]
  have hG'd : X ^ (N - 1) ∣ derivative G := pow_sub_one_dvd_derivative_of_pow_dvd hGd
  have hQ' : derivative Q = C (c * m) * X ^ (m - 1) := by
    rw [hQ, derivative_add, derivative_C, zero_add, derivative_C_mul_X_pow]
  have e1 : derivative G = 2 * F * derivative F - derivative Q := by
    rw [hG, derivative_sub, derivative_sq, map_ofNat]
  have key0 : 2 * derivative F * Q - derivative Q * F =
      derivative G * F - 2 * derivative F * G := by
    rw [e1, hG]; ring
  have key : C (2 * a) * derivative F + C (2 * c) * (derivative F * X ^ m) -
      C (c * m) * (F * X ^ (m - 1)) = derivative G * F - 2 * derivative F * G := by
    rw [← key0, hQ', hQ]
    simp only [map_mul, map_ofNat]
    ring
  have hR : (derivative G * F - 2 * derivative F * G).coeff j = 0 := by
    have hd : X ^ (N - 1) ∣ derivative G * F - 2 * derivative F * G :=
      dvd_sub (dvd_mul_of_dvd_left hG'd _)
        (dvd_mul_of_dvd_right ((pow_dvd_pow X (Nat.sub_le N 1)).trans hGd) _)
    exact X_pow_dvd_iff.mp hd j (by omega)
  rw [← key, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_mul_X_pow',
    coeff_mul_X_pow', coeff_derivative] at hR
  rcases lt_trichotomy m (j + 1) with hlt | heq | hgt
  · have h1 : m ≤ j := by omega
    have h2 : m - 1 ≤ j := by omega
    rw [ite_eq_left h1, ite_eq_left h2, coeff_derivative] at hR
    rw [ite_eq_left hlt.le]
    have e2 : j - m + 1 = j + 1 - m := by omega
    have e3 : j - (m - 1) = j + 1 - m := by omega
    rw [e2, e3] at hR
    have e4 : ((j - m : ℕ) : K) = (j : K) - m := by push_cast [Nat.cast_sub h1]; ring
    rw [e4] at hR
    linear_combination hR
  · have h1 : ¬ m ≤ j := by omega
    have h2 : m - 1 ≤ j := by omega
    rw [ite_eq_right h1, ite_eq_left h2] at hR
    rw [ite_eq_left heq.le]
    have e3 : j - (m - 1) = j + 1 - m := by omega
    rw [e3] at hR
    have e5 : (m : K) = j + 1 := by exact_mod_cast heq
    rw [e5] at hR ⊢
    linear_combination hR
  · have h1 : ¬ m ≤ j := by omega
    have h2 : ¬ m - 1 ≤ j := by omega
    rw [ite_eq_right h1, ite_eq_right h2] at hR
    rw [ite_eq_right (by omega)]
    linear_combination hR

/-- **Lemma S (a).** Sparse square roots: if `F² ≡ f₀² + c X^m (mod X^N)` with `f₀ = F.coeff 0 ≠ 0`,
then below `N` the coefficients of `F` vanish off the multiples of `m`. -/
theorem coeff_eq_zero_of_sq_sparse {F : K[X]} {c : K} {m N : ℕ} (hm : 0 < m) (_hc : c ≠ 0)
    (h0 : F.coeff 0 ≠ 0)
    (h : ∀ j < N, (F ^ 2).coeff j = (C (F.coeff 0 ^ 2) + C c * X ^ m).coeff j) :
    ∀ j < N, ¬ m ∣ j → F.coeff j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjN hmj
    rcases j with _ | j
    · exact absurd (dvd_zero m) hmj
    · have hrec := sq_sparse_recursion hm h j hjN
      have hne : 2 * F.coeff 0 ^ 2 * ((j : K) + 1) ≠ 0 := by positivity
      split_ifs at hrec with hmj1
      · have hdv : ¬ m ∣ j + 1 - m := by
          intro hd
          apply hmj
          have : j + 1 = (j + 1 - m) + m := by omega
          rw [this]
          exact dvd_add hd dvd_rfl
        rw [ih (j + 1 - m) (by omega) (by omega) hdv, mul_zero] at hrec
        exact (mul_eq_zero.mp hrec).resolve_left hne
      · exact (mul_eq_zero.mp hrec).resolve_left hne

/-- **Lemma S (b).** In the situation of Lemma S, the coefficients of `F` at the multiples of `m`
below `N` never vanish (because `3 − 2i ≠ 0` for every integer `i`). -/
theorem coeff_ne_zero_of_sq_sparse {F : K[X]} {c : K} {m N : ℕ} (hm : 0 < m) (hc : c ≠ 0)
    (h0 : F.coeff 0 ≠ 0)
    (h : ∀ j < N, (F ^ 2).coeff j = (C (F.coeff 0 ^ 2) + C c * X ^ m).coeff j) :
    ∀ i, i * m < N → F.coeff (i * m) ≠ 0 := by
  intro i
  induction i with
  | zero => intro _; rwa [zero_mul]
  | succ i ih =>
    intro hiN
    set M := i * m with hM
    have hsucc : (i + 1) * m = M + m := by rw [hM]; ring
    rw [hsucc] at hiN ⊢
    have hrec := sq_sparse_recursion hm h (M + m - 1) (by omega)
    have e1 : M + m - 1 + 1 = M + m := by omega
    have e2 : ((M + m - 1 : ℕ) : K) + 1 = (M : K) + m := by
      have : ((M + m - 1 : ℕ) : K) = (M : K) + m - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; ring
    rw [e1, e2, ite_eq_left (by omega), show M + m - m = M by omega] at hrec
    have hfM := ih (by omega)
    have h3 : (3 * (m : K) - 2 * ((M : K) + m)) ≠ 0 := by
      intro h3
      have h4 : (m : K) * (1 - 2 * (i : K)) = 0 := by
        rw [hM] at h3; push_cast at h3; linear_combination h3
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd (by exact_mod_cast h5 : m = 0) (by omega)
      · have h7 : (2 * (i : K)) = 1 := by linear_combination -h5
        have h6 : (2 * i : ℕ) = 1 := by exact_mod_cast h7
        omega
    intro hzero
    rw [hzero, mul_zero] at hrec
    exact mul_ne_zero (mul_ne_zero hc h3) hfM hrec.symm

/-! ### Lemma F: four-term squares -/

/-- **Four-term squares (Lemma F).** `u² + u'² X^m + v'² X^(2n−m) + v² X^(2n)` with all four
coefficients nonzero squares and `0 < m < n` is never a square in `K[X]`. (Positivity matters:
over `ℂ`, `(1 + 2X − 2X²)² = 1 + 4X − 8X³ + 4X⁴`.) -/
theorem not_isSquare_four_term {u u' v' v : K} {m n : ℕ} (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hv' : v' ≠ 0) (hv : v ≠ 0) (hm : 0 < m) (hmn : m < n) :
    ¬ IsSquare (C (u ^ 2) + C (u' ^ 2) * X ^ m + C (v' ^ 2) * X ^ (2 * n - m) +
      C (v ^ 2) * X ^ (2 * n)) := by
  rintro ⟨F, hF⟩
  set P := C (u ^ 2) + C (u' ^ 2) * X ^ m + C (v' ^ 2) * X ^ (2 * n - m) +
      C (v ^ 2) * X ^ (2 * n) with hPdef
  have hPc : ∀ j, P.coeff j = ((if j = 0 then u ^ 2 else 0) + (if j = m then u' ^ 2 else 0) +
      (if j = 2 * n - m then v' ^ 2 else 0) + (if j = 2 * n then v ^ 2 else 0)) := by
    intro j
    simp only [hPdef, coeff_add, coeff_C_mul_X_pow, coeff_C]
  have hP2n : P.coeff (2 * n) = v ^ 2 := by
    rw [hPc]; split_ifs <;> first | (exfalso; omega) | ring
  have hP0 : P.coeff 0 = u ^ 2 := by
    rw [hPc]; split_ifs <;> first | (exfalso; omega) | ring
  have hPdeg : P.natDegree = 2 * n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      rw [hPc]
      split_ifs <;> first | (exfalso; omega) | ring
    · rw [hP2n]; positivity
  have hF0 : F ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hF
    have := hP2n
    rw [hF, coeff_zero] at this
    exact pow_ne_zero 2 hv this.symm
  have hFdeg : F.natDegree = n := by
    have := hPdeg
    rw [hF, natDegree_mul hF0 hF0] at this
    omega
  have hf0 : F.coeff 0 ^ 2 = u ^ 2 := by rw [sq, ← mul_coeff_zero, ← hF, hP0]
  have hlc : F.leadingCoeff ^ 2 = v ^ 2 := by
    rw [sq, ← leadingCoeff_mul, ← hF, leadingCoeff, hPdeg, hP2n]
  have hF00 : F.coeff 0 ≠ 0 := by
    intro h0
    rw [h0] at hf0
    exact pow_ne_zero 2 hu (by rw [← hf0]; ring)
  have hS : ∀ j < 2 * n - m,
      (F ^ 2).coeff j = (C (F.coeff 0 ^ 2) + C (u' ^ 2) * X ^ m).coeff j := by
    intro j hj
    rw [sq, ← hF, hPc, hf0, coeff_add, coeff_C, coeff_C_mul_X_pow]
    split_ifs <;> first | (exfalso; omega) | ring
  have hu'2 : u' ^ 2 ≠ 0 := pow_ne_zero 2 hu'
  have hv'2 : v' ^ 2 ≠ 0 := pow_ne_zero 2 hv'
  by_cases hmn' : m ∣ n
  · obtain ⟨q, rfl⟩ := hmn'
    have hq : 2 ≤ q := by
      rcases Nat.lt_or_ge q 2 with hq | hq
      · interval_cases q <;> omega
      · exact hq
    rcases hq.eq_or_lt with hq2 | hq3
    · -- `n = 2m`: `F = a + b X^m + d X^(2m)`
      subst hq2
      have hz : ∀ j, j ≠ 0 → j ≠ m → j ≠ 2 * m → F.coeff j = 0 := by
        intro j h1 h2 h3
        by_cases hj : j < 3 * m
        · refine coeff_eq_zero_of_sq_sparse hm hu'2 hF00 hS j (by omega) ?_
          rintro ⟨t, rfl⟩
          have ht : t < 3 := by
            by_contra ht
            have : m * 3 ≤ m * t := Nat.mul_le_mul_left m (by omega)
            omega
          interval_cases t <;> omega
        · exact coeff_eq_zero_of_natDegree_lt (by rw [hFdeg]; omega)
      set a := F.coeff 0
      set b := F.coeff m
      set d := F.coeff (2 * m)
      have hFexp : F = C a + C b * X ^ m + C d * X ^ (2 * m) := by
        ext j
        simp only [coeff_add, coeff_C, coeff_C_mul_X_pow]
        by_cases h1 : j = 0
        · subst h1; split_ifs <;> first | (exfalso; omega) | simp [a]
        by_cases h2 : j = m
        · subst h2; split_ifs <;> first | (exfalso; omega) | simp [b]
        by_cases h3 : j = 2 * m
        · subst h3; split_ifs <;> first | (exfalso; omega) | simp [d]
        rw [hz j h1 h2 h3]
        split_ifs; simp
      have hsq : F * F = C (a ^ 2) + C (2 * a * b) * X ^ m + C (b ^ 2 + 2 * a * d) * X ^ (2 * m) +
          C (2 * b * d) * X ^ (3 * m) + C (d ^ 2) * X ^ (4 * m) := by
        rw [hFexp]
        simp only [map_add, map_mul, map_pow, map_ofNat]
        ring
      have hcoef : ∀ j, P.coeff j = (F * F).coeff j := fun j => by rw [hF]
      have e1 : u' ^ 2 = 2 * a * b := by
        have := hcoef m
        rw [hPc, hsq] at this
        simp only [coeff_add, coeff_C, coeff_C_mul_X_pow] at this
        split_ifs at this <;> first | (exfalso; omega) | linarith
      have e2 : 0 = b ^ 2 + 2 * a * d := by
        have := hcoef (2 * m)
        rw [hPc, hsq] at this
        simp only [coeff_add, coeff_C, coeff_C_mul_X_pow] at this
        split_ifs at this <;> first | (exfalso; omega) | linarith
      have e3 : v' ^ 2 = 2 * b * d := by
        have := hcoef (3 * m)
        rw [hPc, hsq] at this
        simp only [coeff_add, coeff_C, coeff_C_mul_X_pow] at this
        split_ifs at this <;> first | (exfalso; omega) | linarith
      have e4 : (u' * v') ^ 2 + 2 * b ^ 4 = 0 := by
        linear_combination v' ^ 2 * e1 + 2 * a * b * e3 - 2 * b ^ 2 * e2
      have : 0 < (u' * v') ^ 2 := by positivity
      nlinarith [pow_two_nonneg (b ^ 2)]
    · -- `n = qm` with `q ≥ 3`: the coefficient at `(q+1) m` would be nonzero
      have h3 : m * 3 ≤ m * q := Nat.mul_le_mul_left m hq3
      have hsucc : (q + 1) * m = m * q + m := by ring
      apply coeff_ne_zero_of_sq_sparse hm hu'2 hF00 hS (q + 1) (by rw [hsucc]; omega)
      exact coeff_eq_zero_of_natDegree_lt (by rw [hFdeg, hsucc]; omega)
  · -- `m ∤ n`: apply Lemma S to the reversed polynomial
    set R := F.reverse with hRdef
    have hR2 : R * R = P.reverse := by rw [hF, reverse_mul_of_domain]
    have hR0 : R.coeff 0 = F.leadingCoeff := coeff_zero_reverse F
    have hRc0 : R.coeff 0 ≠ 0 := by
      rw [hR0]; exact leadingCoeff_ne_zero.mpr hF0
    have hS' : ∀ j < 2 * n - m,
        (R ^ 2).coeff j = (C (R.coeff 0 ^ 2) + C (v' ^ 2) * X ^ m).coeff j := by
      intro j hj
      rw [sq, hR2, coeff_reverse, hPdeg, revAt_le (by omega), hPc, hR0, hlc, coeff_add, coeff_C,
        coeff_C_mul_X_pow]
      split_ifs <;> first | (exfalso; omega) | ring
    have hRn := coeff_eq_zero_of_sq_sparse hm hv'2 hRc0 hS' n (by omega) hmn'
    rw [hRdef, coeff_reverse, hFdeg, revAt_le le_rfl, Nat.sub_self] at hRn
    exact hF00 hRn

end SparseSquares

/-! ### Powers of `X` dividing squares; the leg structure -/

/-- `X^(2k) ∣ d²` forces `X^k ∣ d`. -/
theorem X_pow_dvd_of_X_pow_dvd_sq {d : ℚ[X]} {k : ℕ} (h : X ^ (2 * k) ∣ d ^ 2) : X ^ k ∣ d := by
  rw [mul_comm, pow_mul] at h
  exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).mp h

/-- If `g² = X^(2i) S` then `g = X^i g₁` with `g₁² = S`. -/
theorem exists_eq_X_pow_mul_of_sq_eq {g S : ℚ[X]} {i : ℕ} (h : g ^ 2 = X ^ (2 * i) * S) :
    ∃ g₁, g = X ^ i * g₁ ∧ g₁ ^ 2 = S := by
  obtain ⟨g₁, rfl⟩ := X_pow_dvd_of_X_pow_dvd_sq ⟨S, h⟩
  refine ⟨g₁, rfl, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (2 * i) (X_ne_zero (R := ℚ)))
  linear_combination h

theorem isCoprime_C_mul_X_pow_of_not_dvd {α : ℚ} {b : ℚ[X]} {k : ℕ} (hα : α ≠ 0)
    (hX : ¬ X ∣ b) : IsCoprime (C α * X ^ k) b := by
  have hC : IsCoprime (C α) b := ⟨C α⁻¹, 0, by rw [← C_mul, inv_mul_cancel₀ hα, C_1]; ring⟩
  exact hC.mul_left ((irreducible_X.coprime_iff_not_dvd).mpr hX).pow_left

/-- **Leg structure for a monomial leg, no coprimality.** In a face `(α X^k, X^i b₁, d)` with
`X ∤ b₁`, either `i = k` and `b₁` is a nonzero constant, or `i < k` and
`2 b₁ = v X^(2(k−i)) − u` with `u v = α²`. -/
theorem monomial_leg_X_pow {α : ℚ} {k i : ℕ} {b₁ d : ℚ[X]} (hα : α ≠ 0) (_hk : 0 < k)
    (hb₁ : b₁ ≠ 0) (hX : ¬ X ∣ b₁) (h : (C α * X ^ k) ^ 2 + (X ^ i * b₁) ^ 2 = d ^ 2) :
    (i = k ∧ ∃ β : ℚ, β ≠ 0 ∧ b₁ = C β) ∨
    (i < k ∧ ∃ u v : ℚ, u * v = α ^ 2 ∧ 2 * b₁ = C v * X ^ (2 * (k - i)) - C u) := by
  rcases le_or_gt k i with hki | hik
  · left
    obtain ⟨r, rfl⟩ : ∃ r, i = k + r := ⟨i - k, by omega⟩
    have h1 : d ^ 2 = X ^ (2 * k) * ((C α) ^ 2 + (X ^ r * b₁) ^ 2) := by rw [← h]; ring
    obtain ⟨d₁, -, hd₁⟩ := exists_eq_X_pow_mul_of_sq_eq h1
    have h2 := (natDegree_eq_zero_of_leg (C_ne_zero.mpr hα) (natDegree_C α) hd₁.symm).1
    rw [natDegree_mul (pow_ne_zero r X_ne_zero) hb₁, natDegree_X_pow] at h2
    have hb₁C := eq_C_of_natDegree_eq_zero (show b₁.natDegree = 0 by omega)
    refine ⟨by omega, b₁.coeff 0, ?_, hb₁C⟩
    intro h0
    apply hb₁
    rw [hb₁C, h0, C_0]
  · right
    obtain ⟨e, rfl⟩ : ∃ e, k = i + e := ⟨k - i, by omega⟩
    have h1 : d ^ 2 = X ^ (2 * i) * ((C α * X ^ e) ^ 2 + b₁ ^ 2) := by rw [← h]; ring
    obtain ⟨d₁, -, hd₁⟩ := exists_eq_X_pow_mul_of_sq_eq h1
    obtain ⟨u, v, huv, hb⟩ := monomial_leg hα (isCoprime_C_mul_X_pow_of_not_dvd hα hX) hd₁.symm
    exact ⟨hik, u, v, huv, by rw [show i + e - i = e by omega]; exact hb⟩

theorem ne_zero_of_mul_eq_sq {u v α : ℚ} (hα : α ≠ 0) (huv : u * v = α ^ 2) : u ≠ 0 ∧ v ≠ 0 := by
  have : u * v ≠ 0 := by rw [huv]; positivity
  exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩

/-! ### The three cases of Theorem M -/

/-- **Mixed case `(i < k, k)`.** `(α X^k, X^i b₁, γ X^k)` with `2 b₁ = v X^(2(k−i)) − u`,
`u v = α²`, `γ ≠ 0`: the space diagonal is not a square. -/
theorem not_squares_monomial_mixed {α γ u v : ℚ} {i k : ℕ} {b₁ g : ℚ[X]} (hα : α ≠ 0)
    (hγ : γ ≠ 0) (hik : i < k) (huv : u * v = α ^ 2)
    (hb : 2 * b₁ = C v * X ^ (2 * (k - i)) - C u)
    (h : (C α * X ^ k) ^ 2 + (X ^ i * b₁) ^ 2 + (C γ * X ^ k) ^ 2 = g ^ 2) : False := by
  obtain ⟨e, rfl⟩ : ∃ e, k = i + e := ⟨k - i, by omega⟩
  rw [show i + e - i = e by omega] at hb
  have hv := (ne_zero_of_mul_eq_sq hα huv).2
  have hCuv : C u * C v = C α ^ 2 := by rw [← C_mul, huv, C_pow]
  have key : (2 * g) ^ 2 = X ^ (2 * i) * (C (v ^ 2) * X ^ (2 * (2 * e)) +
      C (2 * α ^ 2 + 4 * γ ^ 2) * X ^ (2 * e) + C (u ^ 2)) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    linear_combination (-4) * h + X ^ (2 * i) * (2 * b₁ + (C v * X ^ (2 * e) - C u)) * hb +
      (-2 * X ^ (2 * i) * X ^ (2 * e)) * hCuv
  obtain ⟨g₁, -, hg₁⟩ := exists_eq_X_pow_mul_of_sq_eq key
  have hd := quad_disc (n := 2 * e) (by omega) (pow_ne_zero 2 hv) hg₁
  have h1 : (u * v) ^ 2 = (α ^ 2) ^ 2 := by rw [huv]
  have h2 : γ ^ 2 * (α ^ 2 + γ ^ 2) = 0 := by linear_combination (hd + 4 * h1) / 16
  have h3 : 0 < γ ^ 2 * (α ^ 2 + γ ^ 2) := by positivity
  linarith

/-- **Equal case `(i = i' < k)`.** -/
theorem not_squares_monomial_equal {α u v u' v' : ℚ} {i k : ℕ} {b₁ c₁ g : ℚ[X]} (hα : α ≠ 0)
    (hik : i < k) (huv : u * v = α ^ 2) (huv' : u' * v' = α ^ 2)
    (hb : 2 * b₁ = C v * X ^ (2 * (k - i)) - C u) (hc : 2 * c₁ = C v' * X ^ (2 * (k - i)) - C u')
    (h : (C α * X ^ k) ^ 2 + (X ^ i * b₁) ^ 2 + (X ^ i * c₁) ^ 2 = g ^ 2) : False := by
  obtain ⟨e, rfl⟩ : ∃ e, k = i + e := ⟨k - i, by omega⟩
  rw [show i + e - i = e by omega] at hb hc
  have hu := (ne_zero_of_mul_eq_sq hα huv).1
  have hv := (ne_zero_of_mul_eq_sq hα huv).2
  have hCuv : C u * C v = C α ^ 2 := by rw [← C_mul, huv, C_pow]
  have hCuv' : C u' * C v' = C α ^ 2 := by rw [← C_mul, huv', C_pow]
  have key : (2 * g) ^ 2 = X ^ (2 * i) * (C (v ^ 2 + v' ^ 2) * X ^ (2 * (2 * e)) +
      C 0 * X ^ (2 * e) + C (u ^ 2 + u' ^ 2)) := by
    simp only [map_add, map_pow, map_zero, zero_mul, add_zero]
    linear_combination (-4) * h + X ^ (2 * i) * (2 * b₁ + (C v * X ^ (2 * e) - C u)) * hb +
      X ^ (2 * i) * (2 * c₁ + (C v' * X ^ (2 * e) - C u')) * hc +
      (-2 * X ^ (2 * i) * X ^ (2 * e)) * hCuv + (-2 * X ^ (2 * i) * X ^ (2 * e)) * hCuv'
  obtain ⟨g₁, -, hg₁⟩ := exists_eq_X_pow_mul_of_sq_eq key
  have hA : v ^ 2 + v' ^ 2 ≠ 0 := by positivity
  have hd := quad_disc (n := 2 * e) (by omega) hA hg₁
  have hpos : 0 < 4 * (v ^ 2 + v' ^ 2) * (u ^ 2 + u' ^ 2) := by positivity
  linarith

/-- **Strict case `(i < i' < k)`**, via the four-term lemma `not_isSquare_four_term`. -/
theorem not_squares_monomial_strict {α u v u' v' : ℚ} {i i' k : ℕ} {b₁ c₁ g : ℚ[X]}
    (hα : α ≠ 0) (hii' : i < i') (hi'k : i' < k) (huv : u * v = α ^ 2) (huv' : u' * v' = α ^ 2)
    (hb : 2 * b₁ = C v * X ^ (2 * (k - i)) - C u)
    (hc : 2 * c₁ = C v' * X ^ (2 * (k - i')) - C u')
    (h : (C α * X ^ k) ^ 2 + (X ^ i * b₁) ^ 2 + (X ^ i' * c₁) ^ 2 = g ^ 2) : False := by
  obtain ⟨p, rfl⟩ : ∃ p, i' = i + p := ⟨i' - i, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, k = i + p + q := ⟨k - (i + p), by omega⟩
  rw [show i + p + q - i = p + q by omega] at hb
  rw [show i + p + q - (i + p) = q by omega] at hc
  have hu := (ne_zero_of_mul_eq_sq hα huv).1
  have hv := (ne_zero_of_mul_eq_sq hα huv).2
  have hu' := (ne_zero_of_mul_eq_sq hα huv').1
  have hv' := (ne_zero_of_mul_eq_sq hα huv').2
  have hCuv : C u * C v = C α ^ 2 := by rw [← C_mul, huv, C_pow]
  have hCuv' : C u' * C v' = C α ^ 2 := by rw [← C_mul, huv', C_pow]
  have key0 : (2 * g) ^ 2 = X ^ (2 * i) * (C (u ^ 2) + C (u' ^ 2) * X ^ (2 * p) +
      C (v' ^ 2) * X ^ (2 * p + 4 * q) + C (v ^ 2) * X ^ (2 * (2 * (p + q)))) := by
    simp only [map_pow]
    linear_combination (-4) * h +
      (X ^ i) ^ 2 * (2 * b₁ + (C v * X ^ (2 * (p + q)) - C u)) * hb +
      (X ^ (i + p)) ^ 2 * (2 * c₁ + (C v' * X ^ (2 * q) - C u')) * hc +
      (-2 * X ^ (2 * i) * X ^ (2 * (p + q))) * hCuv +
      (-2 * X ^ (2 * (i + p)) * X ^ (2 * q)) * hCuv'
  have key : (2 * g) ^ 2 = X ^ (2 * i) * (C (u ^ 2) + C (u' ^ 2) * X ^ (2 * p) +
      C (v' ^ 2) * X ^ (2 * (2 * (p + q)) - 2 * p) + C (v ^ 2) * X ^ (2 * (2 * (p + q)))) := by
    rw [show 2 * (2 * (p + q)) - 2 * p = 2 * p + 4 * q by omega]; exact key0
  obtain ⟨g₁, -, hg₁⟩ := exists_eq_X_pow_mul_of_sq_eq key
  exact not_isSquare_four_term hu hu' hv' hv (by omega : 0 < 2 * p)
    (by omega : 2 * p < 2 * (p + q)) ⟨g₁, by rw [← hg₁, sq]⟩

/-! ### Theorem M -/

/-- **Monomial common edge forces proportionality (face-cuboid form).** If `α ≠ 0`, `k ≥ 1`,
`b, c ≠ 0` and `(α X^k)² + b²`, `(α X^k)² + c²`, `(α X^k)² + b² + c²` are squares in `ℚ[X]`, then
`b = β X^k` and `c = γ X^k`. (The face `b² + c²` is not used.) -/
theorem monomial_edge_proportional {α : ℚ} {k : ℕ} {b c : ℚ[X]} (hα : α ≠ 0) (hk : 0 < k)
    (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsSquare ((C α * X ^ k) ^ 2 + b ^ 2))
    (hac : IsSquare ((C α * X ^ k) ^ 2 + c ^ 2))
    (habc : IsSquare ((C α * X ^ k) ^ 2 + b ^ 2 + c ^ 2)) :
    ∃ β γ : ℚ, b = C β * X ^ k ∧ c = C γ * X ^ k := by
  obtain ⟨d, hd⟩ := eq_sq_of_isSquare hab
  obtain ⟨e, he⟩ := eq_sq_of_isSquare hac
  obtain ⟨g, hg⟩ := eq_sq_of_isSquare habc
  obtain ⟨b₁, hbdec, hXb⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd b hb 0
  obtain ⟨c₁, hcdec, hXc⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd c hc 0
  simp only [map_zero, sub_zero] at hbdec hXb hcdec hXc
  generalize b.rootMultiplicity 0 = i at hbdec
  generalize c.rootMultiplicity 0 = i' at hcdec
  have hb₁ : b₁ ≠ 0 := by rintro rfl; exact hb (by rw [hbdec, mul_zero])
  have hc₁ : c₁ ≠ 0 := by rintro rfl; exact hc (by rw [hcdec, mul_zero])
  subst hbdec hcdec
  rcases monomial_leg_X_pow hα hk hb₁ hXb hd with ⟨hik, β, hβ, rfl⟩ | ⟨hik, u, v, huv, hb2⟩ <;>
    rcases monomial_leg_X_pow hα hk hc₁ hXc he with ⟨hi'k, γ, hγ, rfl⟩ | ⟨hi'k, u', v', huv', hc2⟩
  · subst hik hi'k
    exact ⟨β, γ, mul_comm _ _, mul_comm _ _⟩
  · subst hik
    exact (not_squares_monomial_mixed hα hβ hi'k huv' hc2 (g := g) (by linear_combination hg)).elim
  · subst hi'k
    exact (not_squares_monomial_mixed hα hγ hik huv hb2 (g := g) (by linear_combination hg)).elim
  · exfalso
    rcases lt_trichotomy i i' with hii | rfl | hii
    · exact not_squares_monomial_strict hα hii hi'k huv huv' hb2 hc2 hg
    · exact not_squares_monomial_equal hα hik huv huv' hb2 hc2 hg
    · exact not_squares_monomial_strict hα hii hik huv' huv hc2 hb2 (g := g)
        (by linear_combination hg)

/-- **Theorem M.** A polynomial cuboid with a monomial edge `α X^k` has proportional edges:
`b = β X^k`, `c = γ X^k`. -/
theorem IsPolyCuboid.proportional_of_monomial_edge {α : ℚ} {k : ℕ} {b c : ℚ[X]}
    (h : IsPolyCuboid (C α * X ^ k) b c) : ∃ β γ : ℚ, b = C β * X ^ k ∧ c = C γ * X ^ k := by
  have hα : α ≠ 0 := by rintro rfl; exact h.ne_a (by simp)
  have hk : 0 < k := by
    have := h.natDegree_pos.1
    rwa [natDegree_C_mul_X_pow k α hα] at this
  exact monomial_edge_proportional hα hk h.ne_b h.ne_c h.sq_ab h.sq_ac h.sq_abc

/-- A polynomial cuboid with an edge `α (X − r)^k` has the other edges `β (X − r)^k`,
`γ (X − r)^k`. -/
theorem IsPolyCuboid.proportional_of_single_root_edge {α r : ℚ} {k : ℕ} {b c : ℚ[X]}
    (h : IsPolyCuboid (C α * (X - C r) ^ k) b c) :
    ∃ β γ : ℚ, b = C β * (X - C r) ^ k ∧ c = C γ * (X - C r) ^ k := by
  have h' := h.comp_X_add_C r
  have hφa : (C α * (X - C r) ^ k).comp (X + C r) = C α * X ^ k := by simp
  rw [hφa] at h'
  obtain ⟨β, γ, hb, hc⟩ := h'.proportional_of_monomial_edge
  refine ⟨β, γ, ?_, ?_⟩
  · rw [← comp_X_add_C_comp_X_sub_C b r, hb]; simp
  · rw [← comp_X_add_C_comp_X_sub_C c r, hc]; simp

/-- A polynomial cuboid with a monomial edge gives an integer perfect cuboid. -/
theorem IsPolyCuboid.exists_isPerfectCuboid_of_monomial_edge {α : ℚ} {k : ℕ} {b c : ℚ[X]}
    (h : IsPolyCuboid (C α * X ^ k) b c) : ∃ A B C : ℕ, IsPerfectCuboid A B C := by
  obtain ⟨β, γ, hb, hc⟩ := h.proportional_of_monomial_edge
  exact h.exists_isPerfectCuboid_of_proportional rfl hb hc

/-- **A polynomial cuboid with an edge `α (X − r)^k` (an edge with a single root, of any
multiplicity) exists iff an integer perfect cuboid exists.** -/
theorem exists_isPolyCuboid_single_root_iff :
    (∃ (α r : ℚ) (k : ℕ) (b c : ℚ[X]), IsPolyCuboid (C α * (X - C r) ^ k) b c) ↔
      ∃ A B C : ℕ, IsPerfectCuboid A B C := by
  constructor
  · rintro ⟨α, r, k, b, c, h⟩
    obtain ⟨β, γ, hb, hc⟩ := h.proportional_of_single_root_edge
    exact h.exists_isPerfectCuboid_of_proportional rfl hb hc
  · rintro ⟨p, q, s, h⟩
    refine ⟨p, 0, 1, C (q : ℚ) * X, C (s : ℚ) * X, ?_⟩
    rw [map_zero, sub_zero, pow_one]
    exact h.isPolyCuboid

/-- A **non-proportional** polynomial cuboid has no edge with a single root: no edge is
`α (X − r)^k`. -/
theorem IsPolyCuboid.edge_ne_C_mul_X_sub_C_pow_of_not_proportional {a b c : ℚ[X]}
    (h : IsPolyCuboid a b c)
    (hnp : ¬ ∃ (q : ℚ[X]) (α β γ : ℚ), a = C α * q ∧ b = C β * q ∧ c = C γ * q)
    (α r : ℚ) (k : ℕ) : a ≠ C α * (X - C r) ^ k := by
  rintro rfl
  obtain ⟨β, γ, hb, hc⟩ := h.proportional_of_single_root_edge
  exact hnp ⟨_, α, β, γ, rfl, hb, hc⟩

end PerfectCuboid.Poly
