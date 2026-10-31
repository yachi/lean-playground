module

public import Mathlib

/-!
# `(x^(2m) − 1)(x^(2n) − 1)` is never a square (the Pell framework)

**Theorem P.** For integers `x ≥ 2` and `m ≠ n` positive, `(x^(2m) − 1)(x^(2n) − 1)` is not a
perfect square (`pow_sub_one_mul_pow_sub_one_not_square`).

## Proof

Let `g = gcd(m, n)`, `a = x^g`, `m = g m'`, `n = g n'`. Then
`gcd(x^(2m) − 1, x^(2n) − 1) = x^(2g) − 1 = a² − 1 =: G` (`Nat.pow_sub_one_gcd_pow_sub_one`), and
the two cofactors are coprime, so if the product is a square both cofactors are squares:
`a^(2m') − 1 = G s²`, `a^(2n') − 1 = G t²`. One of `m', n'` is `≥ 2`, so it suffices to show
(`pow_sub_one_ne_mul_sq`): **for `a ≥ 2` and `k ≥ 2`, `a^(2k) − 1 ≠ (a² − 1) s²`.**

If `a^(2k) − 1 = (a² − 1)s²`, then `(a^k, s)` solves the Pell equation `X² − (a² − 1)Y² = 1`,
whose solutions are `(xₙ, yₙ)` with `xₙ = Tₙ(a)` (Chebyshev; `Pell.eq_pell`, `xn_eq_C`). So
`Tₙ(a) = a^k` for some `n`.

* `n` even: `Tₙ(a) ≡ ±1 (mod a²)`, but `a ∣ a^k`. Contradiction.
* `n = 1`: `a = a^k`, contradicting `k ≥ 2`.
* `n ≥ 3` odd: the key lemma `factorization_C` (a lifting-the-exponent statement) says that for
  every prime `q ∣ a`, `v_q(Tₙ(a)) = v_q(a) + v_q(n)`. Its proof: write `n = ℓ n'` with `ℓ` the
  least prime factor; `Tₙ(a) = T_ℓ(b)` with `b = T_{n'}(a)` (`Polynomial.Chebyshev.T_mul`), and
  for odd `ℓ`, `T_ℓ(b) = b·(±ℓ + b² R)` (`C_odd_even`), so `v_q(T_ℓ(b)) = v_q(b) + v_q(ℓ)` as
  `q ∣ b`. Hence `k v_q(a) = v_q(a) + v_q(n)`, i.e. `a^(k−1) ∣ n`. But `a^k = Tₙ(a) ≥ a^n`, so
  `n ≤ k` and `2^(n−1) ≤ a^(n−1) ≤ a^(k−1) ≤ n`, impossible for `n ≥ 3`.

## Literature

Theorem P is a special case of known results on `(A^N − 1)(B^N − 1) = x²` (with `N = 1`,
`A = x^(2m)`, `B = x^(2n)`, `A^n = B^m`): Hajdu–Szalay (Period. Math. Hungar. 40 (2000)) treat
`B = A^k`, Cohn (Period. Math. Hungar. 44 (2002)) the case `A^k = B^l`. Its core
`(a^(2k) − 1)/(a² − 1) ≠ □` is also a special case of Ljunggren's theorem on
`(X^n − 1)/(X − 1) = y²` with `X = a²`. The proof here is self-contained and elementary (Pell +
Chebyshev + LTE); the formalization is new.
-/

@[expose] public section

namespace PerfectCuboid.PellLeg

open Polynomial

/-- The Chebyshev value `Tₙ(a)`, which is the `x`-coordinate of `(a + √(a² − 1))ⁿ`. -/
noncomputable def C (a : ℤ) (n : ℕ) : ℤ := (Polynomial.Chebyshev.T ℤ (n : ℤ)).eval a

theorem C_zero (a : ℤ) : C a 0 = 1 := by simp [C]

theorem C_one (a : ℤ) : C a 1 = a := by simp [C]

theorem C_add_two (a : ℤ) (n : ℕ) : C a (n + 2) = 2 * a * C a (n + 1) - C a n := by
  have h := Polynomial.Chebyshev.T_add_two ℤ (n : ℤ)
  simp only [C]
  push_cast
  rw [h]
  simp

theorem C_mul (a : ℤ) (m n : ℕ) : C a (m * n) = C (C a n) m := by
  simp only [C]
  push_cast
  rw [Polynomial.Chebyshev.T_mul, Polynomial.eval_comp]

/-- `T_{2s}(b) ≡ (−1)^s (mod b²)` and `T_{2s+1}(b) = b·((−1)^s (2s+1) + b² R)`. -/
theorem C_odd_even (b : ℤ) (s : ℕ) :
    (∃ R : ℤ, C b (2 * s) = (-1) ^ s + b ^ 2 * R) ∧
    (∃ R : ℤ, C b (2 * s + 1) = b * ((-1) ^ s * (2 * s + 1) + b ^ 2 * R)) := by
  induction s with
  | zero => exact ⟨⟨0, by simp [C_zero]⟩, ⟨0, by simp [C_one]⟩⟩
  | succ s ih =>
    obtain ⟨⟨R1, h1⟩, ⟨R2, h2⟩⟩ := ih
    have e1 : C b (2 * (s + 1)) = 2 * b * C b (2 * s + 1) - C b (2 * s) := by
      rw [show 2 * (s + 1) = 2 * s + 2 by ring, C_add_two]
    have e1' : C b (2 * (s + 1)) = (-1) ^ (s + 1) + b ^ 2 * (2 * ((-1) ^ s * (2 * s + 1) +
        b ^ 2 * R2) - R1) := by
      rw [e1, h1, h2]; ring
    refine ⟨⟨_, e1'⟩, ⟨2 * (2 * ((-1) ^ s * (2 * s + 1) + b ^ 2 * R2) - R1) - R2, ?_⟩⟩
    have e2 : C b (2 * (s + 1) + 1) = 2 * b * C b (2 * (s + 1)) - C b (2 * s + 1) := by
      rw [show 2 * (s + 1) + 1 = 2 * s + 1 + 2 by ring, C_add_two]
      congr 2
    rw [e2, e1', h2]
    push_cast
    ring

/-- For `a ≥ 1`: `a·Tₙ(a) ≤ T_{n+1}(a)` and `Tₙ(a) ≥ aⁿ`. -/
theorem C_ge (a : ℤ) (ha : 1 ≤ a) (n : ℕ) : a * C a n ≤ C a (n + 1) ∧ a ^ n ≤ C a n := by
  induction n with
  | zero => simp [C_zero, C_one]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hpos : 0 ≤ C a n := le_trans (by positivity) h2
    refine ⟨?_, ?_⟩
    · have h3 : C a n ≤ C a (n + 1) := by nlinarith
      have h4 : 0 ≤ C a (n + 1) := le_trans hpos h3
      rw [C_add_two]; nlinarith [mul_le_mul_of_nonneg_right ha h4]
    · rw [pow_succ]; nlinarith

theorem C_pos (a : ℤ) (ha : 1 ≤ a) (n : ℕ) : 0 < C a n :=
  lt_of_lt_of_le (by positivity) (C_ge a ha n).2

/-- Mathlib's Pell `x`-coordinates are Chebyshev values. -/
theorem xn_eq_C {a : ℕ} (a1 : 1 < a) (n : ℕ) : (Pell.xn a1 n : ℤ) = C a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [Pell.xn_zero, C_zero]
    | 1, _ => simp [C_one]
    | k + 2, ih =>
      have h := Pell.xz_succ_succ a1 k
      simp only [Pell.xz] at h
      rw [h, C_add_two, ih k (by omega), ih (k + 1) (by omega)]
      push_cast; ring

/-- If `q ∣ n`, `q² ∤ n` and `n ≠ 0`, then `v_q(n) = 1`. -/
theorem factorization_eq_one {q n : ℕ} (hq : q.Prime) (hn : n ≠ 0) (h1 : q ∣ n)
    (h2 : ¬ q ^ 2 ∣ n) : n.factorization q = 1 := by
  have a1 : 1 ≤ n.factorization q := (hq.pow_dvd_iff_le_factorization hn).1 (by simpa using h1)
  have a2 : ¬ 2 ≤ n.factorization q := fun h ↦ h2 ((hq.pow_dvd_iff_le_factorization hn).2 h)
  omega

theorem dvd_of_dvd_neg_one_pow_mul {q X : ℤ} (s : ℕ) (h : q ∣ (-1) ^ s * X) : q ∣ X := by
  have := dvd_mul_of_dvd_right h ((-1) ^ s)
  rwa [← mul_assoc, ← mul_pow, show (-1 : ℤ) * (-1) = 1 by norm_num, one_pow, one_mul] at this

/-- **Lifting the exponent for Chebyshev values.** For a prime `q ∣ a`, `a ≥ 1`, and odd `n`,
`v_q(Tₙ(a)) = v_q(a) + v_q(n)`. -/
theorem factorization_C {q : ℕ} (hq : q.Prime) {a : ℤ} (ha : 1 ≤ a) (hqa : (q : ℤ) ∣ a) :
    ∀ n : ℕ, Odd n →
      (C a n).natAbs.factorization q = a.natAbs.factorization q + n.factorization q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by obtain ⟨t, ht⟩ := hn; omega
      subst this; simp [C_one]
    · set ℓ := n.minFac with hℓ
      have hℓp : ℓ.Prime := Nat.minFac_prime (by omega)
      obtain ⟨n', hn'⟩ : ℓ ∣ n := Nat.minFac_dvd n
      have hn0 : n ≠ 0 := by omega
      have hn'0 : n' ≠ 0 := by rintro rfl; simp at hn'; omega
      have hℓodd : Odd ℓ := (Nat.odd_mul.1 (hn' ▸ hn)).1
      have hn'odd : Odd n' := (Nat.odd_mul.1 (hn' ▸ hn)).2
      have hlt : n' < n := by
        rw [hn']; have := hℓp.two_le
        nlinarith [Nat.pos_of_ne_zero hn'0]
      have IH := ih n' hlt hn'odd
      obtain ⟨s, hs⟩ := hℓodd
      set b := C a n' with hb
      have hb0 : b ≠ 0 := (C_pos a ha n').ne'
      have ha0 : a.natAbs ≠ 0 := by omega
      have hqa' : 1 ≤ a.natAbs.factorization q :=
        (hq.pow_dvd_iff_le_factorization ha0).1 (by simpa using Int.natCast_dvd.1 hqa)
      have hqb : (q : ℤ) ∣ b := by
        apply Int.natCast_dvd.2
        exact (hq.dvd_iff_one_le_factorization (by simpa using hb0)).2 (by omega)
      obtain ⟨-, R, hR⟩ := C_odd_even b s
      set W : ℤ := (-1) ^ s * (2 * s + 1) + b ^ 2 * R with hW
      have hCn : C a n = b * W := by
        rw [hn', C_mul, ← hb, hs, ← hR]
      have hq2b : (q : ℤ) ^ 2 ∣ b ^ 2 * R := Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hqb 2) _
      -- the factorization of `W` at `q` equals that of `ℓ`
      have hWf : W.natAbs.factorization q = ℓ.factorization q := by
        by_cases hlq : ℓ = q
        · have hℓ' : (2 * s + 1 : ℤ) = q := by rw [← hlq, hs]; push_cast; ring
          have hdvd : (q : ℤ) ∣ W := by
            rw [hW, hℓ']
            exact dvd_add (Dvd.intro_left _ rfl)
              (Dvd.dvd.mul_right (dvd_pow hqb two_ne_zero) _)
          have hndvd : ¬ (q : ℤ) ^ 2 ∣ W := by
            intro h2
            have h3 : (q : ℤ) ^ 2 ∣ (-1) ^ s * (q : ℤ) := by
              have := dvd_sub h2 hq2b
              rw [hW, hℓ'] at this; simpa using this
            rw [pow_two, mul_comm ((-1 : ℤ) ^ s)] at h3
            have h4 : (q : ℤ) ∣ (-1) ^ s * 1 := by
              rw [mul_one]; exact (mul_dvd_mul_iff_left (by exact_mod_cast hq.ne_zero)).1 h3
            have h5 : (q : ℤ) ∣ ((1 : ℕ) : ℤ) := by simpa using dvd_of_dvd_neg_one_pow_mul s h4
            exact hq.ne_one (Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 h5))
          have hW0 : W ≠ 0 := by rintro h0; rw [h0] at hdvd; exact hndvd (by simp [h0])
          rw [hlq, hq.factorization_self]
          exact factorization_eq_one hq (by simpa using hW0) (Int.natCast_dvd.1 hdvd)
              (by intro h; exact hndvd (by
                have := Int.natCast_dvd.2 h; push_cast at this; exact this))
        · have hqℓ : ¬ q ∣ ℓ := fun h ↦ hlq ((Nat.prime_dvd_prime_iff_eq hq hℓp).1 h).symm
          have hndvd : ¬ (q : ℤ) ∣ W := by
            intro h
            have h1 : (q : ℤ) ∣ (-1) ^ s * (2 * s + 1) :=
              (dvd_add_left (Dvd.dvd.mul_right (dvd_pow hqb two_ne_zero) _)).1
                (by rw [← hW]; exact h)
            have h2 : (q : ℤ) ∣ (2 * s + 1) := dvd_of_dvd_neg_one_pow_mul s h1
            have h3 : (q : ℤ) ∣ (ℓ : ℤ) := by rw [hs]; push_cast; exact h2
            exact hqℓ (Int.natCast_dvd_natCast.1 h3)
          rw [Nat.factorization_eq_zero_of_not_dvd (fun h ↦ hndvd (Int.natCast_dvd.2 h)),
            Nat.factorization_eq_zero_of_not_dvd hqℓ]
      have hW0 : W ≠ 0 := by
        rintro h0
        have := (C_pos a ha n).ne'
        rw [hCn, h0, mul_zero] at this
        exact this rfl
      rw [hCn, Int.natAbs_mul, Nat.factorization_mul (by simpa using hb0) (by simpa using hW0),
        Finsupp.add_apply, IH, hWf, hn', Nat.factorization_mul hℓp.ne_zero hn'0,
        Finsupp.add_apply]
      ring

/-- `n < 2^(n−1)` for `n ≥ 3`. -/
theorem lt_two_pow_pred {n : ℕ} (hn : 3 ≤ n) : n < 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show n + 1 - 1 = n - 1 + 1 by omega, pow_succ]; omega

/-- **Core lemma.** For `a ≥ 2` and `k ≥ 2`, `a^(2k) − 1 ≠ (a² − 1)s²`; equivalently
`1 + a² + a⁴ + ⋯ + a^(2k−2)` is not a square. -/
theorem pow_sub_one_ne_mul_sq {a k s : ℕ} (ha : 2 ≤ a) (hk : 2 ≤ k) :
    a ^ (2 * k) - 1 ≠ (a ^ 2 - 1) * s ^ 2 := by
  intro h
  have a1 : 1 < a := ha
  have hpell : a ^ k * a ^ k - (a * a - 1) * s * s = 1 := by
    have e1 : a ^ k * a ^ k = a ^ (2 * k) := by rw [← pow_add]; ring_nf
    have e2 : (a * a - 1) * s * s = (a ^ 2 - 1) * s ^ 2 := by ring_nf
    have : 1 ≤ a ^ (2 * k) := Nat.one_le_pow _ _ (by omega)
    rw [e1, e2, ← h]; omega
  obtain ⟨n, hn, -⟩ := Pell.eq_pell a1 hpell
  have hC : ((a : ℤ)) ^ k = C a n := by rw [← xn_eq_C a1, ← hn]; push_cast; ring
  have haz : (1 : ℤ) ≤ a := by exact_mod_cast a1.le
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- even index: `T_{2t}(a) ≡ ±1 (mod a)`
    obtain ⟨⟨R, hR⟩, -⟩ := C_odd_even (a : ℤ) t
    have hd : (a : ℤ) ∣ (-1) ^ t := by
      have h1 : (a : ℤ) ∣ (a : ℤ) ^ k := dvd_pow_self _ (by omega)
      rw [hC, hR] at h1
      exact (dvd_add_left (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _)).1 h1
    have : (a : ℤ) ∣ 1 := by
      rcases neg_one_pow_eq_or ℤ t with h' | h' <;> rw [h'] at hd
      · exact hd
      · exact (dvd_neg).1 hd
    have := Int.le_of_dvd one_pos this
    omega
  · rcases Nat.lt_or_ge t 1 with ht | ht
    · -- `n = 1`: `a^k = a`
      have : t = 0 := by omega
      subst this
      simp only [mul_zero, zero_add, C_one] at hC
      have h2 : (a : ℤ) ^ k = (a : ℤ) ^ 1 := by rw [hC, pow_one]
      have := Nat.pow_right_injective ha (by exact_mod_cast h2)
      omega
    · -- `n ≥ 3` odd: valuations
      set n := 2 * t + 1 with hn'
      have hn3 : 3 ≤ n := by omega
      have hnk : n ≤ k := by
        have h1 := (C_ge (a : ℤ) haz n).2
        rw [← hC] at h1
        exact (Nat.pow_le_pow_iff_right a1).1 (by exact_mod_cast h1)
      have hdiv : a ^ (k - 1) ∣ n := by
        have ha0 : a ≠ 0 := by omega
        rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ ha0) (by omega)]
        intro q
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        by_cases hq : q.Prime
        · by_cases hqa : q ∣ a
          · have hv := factorization_C hq haz (Int.natCast_dvd_natCast.2 hqa) n ⟨t, rfl⟩
            rw [← hC] at hv
            have e1 : ((a : ℤ) ^ k).natAbs = a ^ k := by rw [Int.natAbs_pow]; simp
            rw [e1, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
              Int.natAbs_natCast] at hv
            have : (k - 1) * a.factorization q + a.factorization q = k * a.factorization q := by
              rw [← Nat.succ_mul]; congr 1; omega
            omega
          · rw [Nat.factorization_eq_zero_of_not_dvd hqa]; simp
        · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
      have h1 : a ^ (k - 1) ≤ n := Nat.le_of_dvd (by omega) hdiv
      have h2 : 2 ^ (n - 1) ≤ a ^ (n - 1) := Nat.pow_le_pow_left ha _
      have h3 : a ^ (n - 1) ≤ a ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have := lt_two_pow_pred hn3
      omega

/-- **Theorem P.** For `x ≥ 2` and distinct positive `m, n`, `(x^(2m) − 1)(x^(2n) − 1)` is not a
perfect square. -/
theorem pow_sub_one_mul_pow_sub_one_not_square {x m n : ℕ} (hx : 2 ≤ x) (hm : 0 < m)
    (hn : 0 < n) (hmn : m ≠ n) : ¬ IsSquare ((x ^ (2 * m) - 1) * (x ^ (2 * n) - 1)) := by
  rintro ⟨r, hr⟩
  set g := Nat.gcd m n with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hm
  obtain ⟨m', hm'⟩ : g ∣ m := Nat.gcd_dvd_left m n
  obtain ⟨n', hn'⟩ : g ∣ n := Nat.gcd_dvd_right m n
  set a := x ^ g with ha
  have ha2 : 2 ≤ a := le_trans hx (Nat.le_self_pow hg0.ne' x)
  set P := x ^ (2 * m) - 1 with hP
  set Q := x ^ (2 * n) - 1 with hQ
  have hPa : P = a ^ (2 * m') - 1 := by rw [hP, ha, ← pow_mul, hm']; ring_nf
  have hQa : Q = a ^ (2 * n') - 1 := by rw [hQ, ha, ← pow_mul, hn']; ring_nf
  have hG : Nat.gcd P Q = a ^ 2 - 1 := by
    rw [hP, hQ, Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_mul_left, ← hg, ha, ← pow_mul,
      mul_comm]
  have hG0 : 0 < a ^ 2 - 1 := by
    have : 4 ≤ a ^ 2 := by nlinarith
    omega
  have hcop := Nat.coprime_div_gcd_div_gcd (m := P) (n := Q) (by rw [hG]; exact hG0)
  rw [hG] at hcop
  set A := P / (a ^ 2 - 1)
  set B := Q / (a ^ 2 - 1)
  have hPA : P = (a ^ 2 - 1) * A := by
    rw [Nat.mul_div_cancel' (hG ▸ Nat.gcd_dvd_left P Q)]
  have hQB : Q = (a ^ 2 - 1) * B := by
    rw [Nat.mul_div_cancel' (hG ▸ Nat.gcd_dvd_right P Q)]
  -- `G ∣ r` and `A * B = (r / G)²`
  have hGr : (a ^ 2 - 1) ∣ r := by
    have : (a ^ 2 - 1) ^ 2 ∣ r ^ 2 := ⟨A * B, by rw [sq r, ← hr]; rw [hPA, hQB]; ring⟩
    exact (Nat.pow_dvd_pow_iff two_ne_zero).1 this
  obtain ⟨r', rfl⟩ := hGr
  have hAB : A * B = r' ^ 2 := by
    have : (a ^ 2 - 1) * (a ^ 2 - 1) * (A * B) = (a ^ 2 - 1) * (a ^ 2 - 1) * r' ^ 2 := by
      calc (a ^ 2 - 1) * (a ^ 2 - 1) * (A * B) = P * Q := by rw [hPA, hQB]; ring
        _ = _ := by rw [hr]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hunit : IsUnit (gcd A B) := by
    rw [Nat.isUnit_iff]; exact hcop
  have hunit' : IsUnit (gcd B A) := by
    rw [Nat.isUnit_iff]; exact hcop.symm
  obtain ⟨s, hs⟩ := exists_eq_pow_of_mul_eq_pow hunit hAB
  obtain ⟨t, ht⟩ := exists_eq_pow_of_mul_eq_pow hunit' (by rw [mul_comm]; exact hAB)
  have hm'0 : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm'; omega)
  have hn'0 : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn'; omega)
  have hne : m' ≠ n' := by rintro rfl; exact hmn (hm'.trans hn'.symm)
  rcases Nat.lt_or_ge m' 2 with h1 | h1
  · exact pow_sub_one_ne_mul_sq (k := n') (s := t) ha2 (by omega) (by rw [← hQa, hQB, ht])
  · exact pow_sub_one_ne_mul_sq (k := m') (s := s) ha2 h1 (by rw [← hPa, hPA, hs])

end PerfectCuboid.PellLeg
