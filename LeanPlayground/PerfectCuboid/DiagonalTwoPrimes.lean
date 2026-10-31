module

public import Mathlib
public import LeanPlayground.PerfectCuboid.DiagonalPrimePower

/-!
# Even face diagonals `2 ^ s * p ^ k`: the family F1

Let `x, y, z > 0` be the edges of a perfect cuboid with no prime dividing all three, `H` the
diagonal of the face `(y, z)`, `E² = x² + y²`, `F² = x² + z²`, `g² = x² + y² + z²`, and suppose
`H = 2 ^ s * p ^ k` with `p` an odd prime. Then `y, z` are even, `x` is odd, and
`(g − x)(g + x) = H²` with `g ± x` even, so `g − x = 2 ^ α * p ^ i` with `α ∈ {1, 2s − 1}`.
Round 10 called **F1** the family `α = 1`, `i ≤ k`, i.e. `g − x = 2 p ^ i` with `i ≤ k`.
This file proves that F1 is empty (`face_diagonal_ne_two_pow_mul_prime_pow_of_F1`).

## The argument (new in round 11; simpler than the round-10 proof)

Put `P = p ^ i` and `C = 2 ^ (s-1) * p ^ (k-i)`, so `H = 2PC`. From `(g − x)(g + x) = H²`:
`x = P (C² − 1)`, `g = P (C² + 1)`, hence `g + H = P (C + 1)²` (the Euclid parametrisation of the
triangle `(x, H, g)`).

* **Size.** Lemma A of `DiagonalPrimePower` (`(g − x)² > 2(g + x)`) reads `4P² > 4PC²`, i.e.
  `C² < P`. Hence `x < P²` and `g + H = P (C + 1)² < 2 P²` (as `C ≥ 2`; `C = 1` gives `x = 0`).
* **Divisibility.** `p ∣ x` (as `i ≥ 1`), so by primitivity `p ∤ y` (and then `p ∤ z`, since
  `p ∣ H`). In `x² = (E − y)(E + y)` the prime `p` divides at most one factor, and
  `P² ∣ x²`; it cannot be `E − y < x < P²`, so `P² ∣ E + y`. Likewise `P² ∣ F + z`.
* **Collision.** `0 < E + y < g + H < 2 P²` forces `E + y = P²`, and likewise `F + z = P²`; then
  `E − y = x² / P² = F − z`, so `y = z` and `H² = 2 y²`, impossible.

The core (`not_F1_core`) is stated without any hypothesis on the shape of `H`: a perfect cuboid
cannot have `g = x + 2P`, `H = 2PC` with `P = p ^ i` and `p ∤ 2y`, `p ∤ 2z`.

The key lemma `key_lemma` (a prime power `p ^ n ∣ x²` with `x < p ^ n`, `p ∤ 2y`, `p ∤ 2z` and
`g + H < 2 p ^ n` is impossible) is the reusable "divisibility vs size" engine. Families F2
(`α = 2s − 1`, or `α = 1` with `i > k`) remain open; see the round-11 report 3.

Near-miss check: the degenerate solution `(x, y, 0)` is excluded only through `0 < z`
(used in Lemma A and to get `E + y`, `F + z` comparable to `g + H`).
-/

@[expose] public section

namespace PerfectCuboid.DiagonalTwoPrimes

open DiagonalPrimePower

/-- `H² = 2 y²` has no solution with `y > 0`. -/
theorem sq_ne_two_mul_sq : ∀ (y H : ℕ), 0 < y → H ^ 2 ≠ 2 * y ^ 2 := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro H hy h
    have h2H : 2 ∣ H := Nat.prime_two.dvd_of_dvd_pow (n := 2) ⟨y ^ 2, h⟩
    obtain ⟨H', rfl⟩ := h2H
    have h' : y ^ 2 = 2 * H' ^ 2 := by nlinarith
    have h2y : 2 ∣ y := Nat.prime_two.dvd_of_dvd_pow (n := 2) ⟨H' ^ 2, h'⟩
    obtain ⟨y', rfl⟩ := h2y
    have hy' : 0 < y' := by omega
    exact ih y' (by omega) H' hy' (by nlinarith)

/-- One leg: if `x² + y² = E²`, `p ^ n ∣ x²`, `x < p ^ n`, `p ∤ 2y`, then `E = y + σ` with
`p ^ n ∣ 2y + σ` and `x² = σ (2y + σ)`. -/
theorem leg_dvd {p n x y E : ℕ} (hp : p.Prime) (hy2 : ¬ p ∣ 2 * y) (hx : 0 < x)
    (hE : x ^ 2 + y ^ 2 = E ^ 2) (hdvd : p ^ n ∣ x ^ 2) (hxlt : x < p ^ n) :
    ∃ σ, E = y + σ ∧ x ^ 2 = σ * (2 * y + σ) ∧ p ^ n ∣ 2 * y + σ := by
  have hyE : y < E := by
    have : y ^ 2 < E ^ 2 := by rw [← hE]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  obtain ⟨σ, rfl⟩ : ∃ σ, E = y + σ := ⟨E - y, by omega⟩
  have hfac : x ^ 2 = σ * (2 * y + σ) := by nlinarith [hE]
  refine ⟨σ, rfl, hfac, ?_⟩
  rw [hfac] at hdvd
  by_cases hσ : p ∣ σ
  · exfalso
    have h2 : ¬ p ∣ 2 * y + σ := fun h => hy2 ((Nat.dvd_add_left hσ).mp h)
    have hc : Nat.Coprime (p ^ n) (2 * y + σ) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr h2)
    have hσd : p ^ n ∣ σ := hc.dvd_of_dvd_mul_right hdvd
    have hσ0 : 0 < σ := by
      rcases Nat.eq_zero_or_pos σ with h0 | h0
      · subst h0; simp at hfac; omega
      · exact h0
    have hle : p ^ n ≤ σ := Nat.le_of_dvd hσ0 hσd
    -- `σ < x` since `σ² < σ (2y + σ) = x²`
    have hσx : σ < x := by
      have : σ ^ 2 ≤ x ^ 2 := by rw [hfac]; nlinarith
      have h' : σ ≤ x := (Nat.pow_le_pow_iff_left (by norm_num)).mp this
      rcases Nat.lt_or_ge σ x with h | h
      · exact h
      · exfalso
        have : σ = x := le_antisymm h' h
        subst this
        have : y = 0 := by nlinarith
        exact hy2 (by rw [this]; simp)
    omega
  · have hc : Nat.Coprime (p ^ n) σ :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hσ)
    exact hc.dvd_of_dvd_mul_left hdvd

/-- **Key lemma (divisibility vs size).** In a perfect cuboid, a prime power `p ^ n` with
`p ^ n ∣ x²`, `x < p ^ n`, `p ∤ 2y`, `p ∤ 2z` and `g + H < 2 p ^ n` is impossible. -/
theorem key_lemma {x y z E F H g p n : ℕ} (hp : p.Prime) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z)
    (hE : x ^ 2 + y ^ 2 = E ^ 2) (hF : x ^ 2 + z ^ 2 = F ^ 2) (hH : y ^ 2 + z ^ 2 = H ^ 2)
    (hg : x ^ 2 + y ^ 2 + z ^ 2 = g ^ 2)
    (hy2 : ¬ p ∣ 2 * y) (hz2 : ¬ p ∣ 2 * z) (hdvd : p ^ n ∣ x ^ 2) (hxlt : x < p ^ n)
    (hlt : g + H < 2 * p ^ n) : False := by
  obtain ⟨σ, hEσ, hfy, hdy⟩ := leg_dvd hp hy2 hx hE hdvd hxlt
  obtain ⟨ρ, hFρ, hfz, hdz⟩ := leg_dvd hp hz2 hx hF hdvd hxlt
  -- `E < g`, `y < H`, `F < g`, `z < H`
  have hEg : E < g := by
    have : E ^ 2 < g ^ 2 := by rw [← hg, ← hE]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hFg : F < g := by
    have : F ^ 2 < g ^ 2 := by rw [← hg, ← hF]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hyH : y < H := by
    have : y ^ 2 < H ^ 2 := by rw [← hH]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hzH : z < H := by
    have : z ^ 2 < H ^ 2 := by rw [← hH]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hpn : 0 < p ^ n := pow_pos hp.pos n
  -- `E + y = p ^ n`
  have hone {w τ : ℕ} (hw : p ^ n ∣ 2 * w + τ) (hlt' : 2 * w + τ < 2 * p ^ n)
      (hpos : 0 < 2 * w + τ) : 2 * w + τ = p ^ n := by
    obtain ⟨m, hm⟩ := hw
    rcases m with _ | _ | m
    · omega
    · simpa using hm
    · exfalso
      rw [hm] at hlt'
      have : p ^ n * 2 ≤ p ^ n * (m + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
  have h1 : 2 * y + σ = p ^ n := hone hdy (by omega) (by omega)
  have h2 : 2 * z + ρ = p ^ n := hone hdz (by omega) (by omega)
  have hσρ : σ = ρ := by
    have : σ * p ^ n = ρ * p ^ n :=
      calc σ * p ^ n = σ * (2 * y + σ) := by rw [h1]
        _ = x ^ 2 := hfy.symm
        _ = ρ * (2 * z + ρ) := hfz
        _ = ρ * p ^ n := by rw [h2]
    exact Nat.eq_of_mul_eq_mul_right hpn this
  have hyz : y = z := by omega
  subst hyz
  exact sq_ne_two_mul_sq y H hy (by rw [← hH]; ring)

/-- **F1 core.** A perfect cuboid cannot have `g = x + 2 p ^ i`, `H = 2 p ^ i C` with
`p ∤ 2y`, `p ∤ 2z` (`p` prime). -/
theorem not_F1_core {x y z E F H g p i C : ℕ} (hp : p.Prime) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z)
    (hE : x ^ 2 + y ^ 2 = E ^ 2) (hF : x ^ 2 + z ^ 2 = F ^ 2) (hH : y ^ 2 + z ^ 2 = H ^ 2)
    (hg : x ^ 2 + y ^ 2 + z ^ 2 = g ^ 2)
    (hy2 : ¬ p ∣ 2 * y) (hz2 : ¬ p ∣ 2 * z)
    (hgx : g = x + 2 * p ^ i) (hHC : H = 2 * p ^ i * C) : False := by
  set P := p ^ i with hP
  have hP0 : 0 < P := pow_pos hp.pos i
  subst hgx
  have hA := lemmaA hx hy hz hE hF hg.symm
  -- `x + P = P C²`
  have hprod : 2 * P * (2 * x + 2 * P) = H ^ 2 := by
    rw [← hH]; nlinarith [hg]
  have hxC : x + P = P * C ^ 2 := by
    rw [hHC] at hprod
    have : (4 * P) * (x + P) = (4 * P) * (P * C ^ 2) := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  -- Lemma A: `C² < P`
  have hCP : C ^ 2 < P := by
    have : 4 * (P * C ^ 2) < 4 * (P * P) := by nlinarith
    have : P * C ^ 2 < P * P := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hC2 : 2 ≤ C := by
    rcases Nat.lt_or_ge C 2 with h | h
    · interval_cases C <;> simp at hxC <;> omega
    · exact h
  -- `x < P²`, `P² ∣ x²`, `g + H < 2 P²`
  have hxP : x < P ^ 2 := by nlinarith
  have hdx : P ∣ x := ⟨C ^ 2 - 1, by
    have : 1 ≤ C ^ 2 := by nlinarith
    rw [Nat.mul_sub, mul_one]; omega⟩
  have hdvd : p ^ (2 * i) ∣ x ^ 2 := by
    rw [pow_mul', ← hP]; exact pow_dvd_pow_of_dvd hdx 2
  have hlt : x + 2 * P + H < 2 * p ^ (2 * i) := by
    rw [pow_mul', ← hP, hHC]
    nlinarith
  exact key_lemma hp hx hy hz hE hF hH hg hy2 hz2 hdvd (by rw [pow_mul', ← hP]; exact hxP) hlt

/-- **F1 is empty.** Let `x, y, z > 0` be the edges of a perfect cuboid with no prime dividing all
three, `H` the diagonal of the face `(y, z)`, and `H = 2 ^ s * p ^ k` with `p` an odd prime.
Then `g − x = 2 p ^ i` with `i ≤ k` is impossible. (Partial result towards
`face_diagonal_ne_two_pow_mul_prime_pow`; the family F2 is open.) -/
theorem face_diagonal_ne_two_pow_mul_prime_pow_of_F1 {x y z E F H g : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hE : x ^ 2 + y ^ 2 = E ^ 2) (hF : x ^ 2 + z ^ 2 = F ^ 2) (hH : y ^ 2 + z ^ 2 = H ^ 2)
    (hg : x ^ 2 + y ^ 2 + z ^ 2 = g ^ 2)
    {p s k i : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (prim : p ∣ x → p ∣ y → p ∣ z → False)
    (hHk : H = 2 ^ s * p ^ k) (hgx : g = x + 2 * p ^ i) (hik : i ≤ k) : False := by
  have hA := lemmaA (τ := 2 * p ^ i) hx hy hz hE hF (by rw [← hgx]; exact hg.symm)
  -- `i ≥ 1`
  have hi : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; simp at hA; omega
    · exact h0
  -- `s ≥ 1`: `H² = (g − x)(g + x)` is even
  have hprod : 2 * p ^ i * (2 * x + 2 * p ^ i) = H ^ 2 := by
    rw [← hH]; subst hgx; nlinarith [hg]
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · exfalso
      subst h0
      have h2H : 2 ∣ H := Nat.prime_two.dvd_of_dvd_pow (n := 2) ⟨p ^ i *
          (2 * x + 2 * p ^ i), by rw [← hprod]; ring⟩
      rw [hHk, pow_zero, one_mul] at h2H
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.prime_two.dvd_of_dvd_pow h2H)).symm
    · exact h0
  have hHC : H = 2 * p ^ i * (2 ^ (s - 1) * p ^ (k - i)) := by
    rw [hHk]
    have e1 : 2 ^ s = 2 * 2 ^ (s - 1) := by rw [← pow_succ']; congr 1; omega
    have e2 : p ^ k = p ^ i * p ^ (k - i) := by rw [← pow_add]; congr 1; omega
    rw [e1, e2]; ring
  -- `p ∣ x`, hence `p ∤ y`, `p ∤ z`
  have hpx : p ∣ x := by
    have hxC : p ^ i ∣ 2 * x + 2 * p ^ i := by
      have : 2 * p ^ i * (2 * x + 2 * p ^ i) =
          2 * p ^ i * (2 * p ^ i * (2 ^ (s - 1) * p ^ (k - i)) ^ 2) := by
        rw [hprod, hHC]; ring
      have := Nat.eq_of_mul_eq_mul_left (by have := pow_pos hp.pos i; omega) this
      exact ⟨2 * (2 ^ (s - 1) * p ^ (k - i)) ^ 2, by rw [this]; ring⟩
    have h2x : p ^ i ∣ 2 * x := (Nat.dvd_add_left (dvd_mul_left _ _)).mp hxC
    have hcop : Nat.Coprime (p ^ i) 2 :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    exact (dvd_pow_self p (by omega)).trans (hcop.dvd_of_dvd_mul_left h2x)
  have hpH : p ∣ H := by
    rw [hHk]; exact dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
  have hp2H : p ∣ H ^ 2 := dvd_pow hpH two_ne_zero
  have not2 (w : ℕ) (hw : ¬ p ∣ w) : ¬ p ∣ 2 * w := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    · exact hw h'
  have hpy : ¬ p ∣ y := by
    intro hpy
    have : p ∣ z ^ 2 := by
      have : z ^ 2 = H ^ 2 - y ^ 2 := by omega
      rw [this]; exact Nat.dvd_sub hp2H (dvd_pow hpy two_ne_zero)
    exact prim hpx hpy (hp.dvd_of_dvd_pow this)
  have hpz : ¬ p ∣ z := by
    intro hpz
    have : p ∣ y ^ 2 := by
      have : y ^ 2 = H ^ 2 - z ^ 2 := by omega
      rw [this]; exact Nat.dvd_sub hp2H (dvd_pow hpz two_ne_zero)
    exact prim hpx (hp.dvd_of_dvd_pow this) hpz
  exact not_F1_core hp hx hy hz hE hF hH hg (not2 y hpy) (not2 z hpz) hgx hHC

/-- **Odd analogue of the F1 core.** A perfect cuboid cannot have `g = x + p ^ i`,
`H = p ^ i U` with `p ∤ 2y`, `p ∤ 2z` (`p` prime). -/
theorem not_odd_core {x y z E F H g p i U : ℕ} (hp : p.Prime) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z)
    (hE : x ^ 2 + y ^ 2 = E ^ 2) (hF : x ^ 2 + z ^ 2 = F ^ 2) (hH : y ^ 2 + z ^ 2 = H ^ 2)
    (hg : x ^ 2 + y ^ 2 + z ^ 2 = g ^ 2)
    (hy2 : ¬ p ∣ 2 * y) (hz2 : ¬ p ∣ 2 * z)
    (hgx : g = x + p ^ i) (hHU : H = p ^ i * U) : False := by
  have hp2 : p ≠ 2 := by rintro rfl; exact hy2 (dvd_mul_right 2 y)
  set P := p ^ i with hP
  have hP0 : 0 < P := pow_pos hp.pos i
  subst hgx
  have hA := lemmaA hx hy hz hE hF hg.symm
  have hprod : P * (2 * x + P) = H ^ 2 := by
    rw [← hH]; nlinarith [hg]
  have hxU : 2 * x + P = P * U ^ 2 := by
    rw [hHU] at hprod
    have : P * (2 * x + P) = P * (P * U ^ 2) := by rw [hprod]; ring
    exact Nat.eq_of_mul_eq_mul_left hP0 this
  have hUP : 2 * U ^ 2 < P := by
    have : P * (2 * U ^ 2) < P * P := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  have hU2 : 2 ≤ U := by
    rcases Nat.lt_or_ge U 2 with h | h
    · interval_cases U <;> simp at hxU <;> omega
    · exact h
  have hxP : x < P ^ 2 := by nlinarith
  have hdx : P ∣ x := by
    have h2x : P ∣ 2 * x := ⟨U ^ 2 - 1, by
      have : 1 ≤ U ^ 2 := by nlinarith
      rw [Nat.mul_sub, mul_one]; omega⟩
    have hcop : Nat.Coprime P 2 :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    exact hcop.dvd_of_dvd_mul_left h2x
  have hdvd : p ^ (2 * i) ∣ x ^ 2 := by
    rw [pow_mul', ← hP]; exact pow_dvd_pow_of_dvd hdx 2
  have hlt : x + P + H < 2 * p ^ (2 * i) := by
    rw [pow_mul', ← hP, hHU]
    nlinarith
  exact key_lemma hp hx hy hz hE hF hH hg hy2 hz2 hdvd (by rw [pow_mul', ← hP]; exact hxP) hlt

/-- **General form (new).** Let `x, y, z > 0` be the edges of a perfect cuboid with no odd prime
`p` dividing all three, and `H` the diagonal of the face `(y, z)`. Then `g − x` is neither a
power `p ^ i` dividing `H`, nor twice a power `2 p ^ i` dividing `H` (`p` an odd prime). -/
theorem g_sub_ne_prime_pow {x y z E F H g : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hE : x ^ 2 + y ^ 2 = E ^ 2) (hF : x ^ 2 + z ^ 2 = F ^ 2) (hH : y ^ 2 + z ^ 2 = H ^ 2)
    (hg : x ^ 2 + y ^ 2 + z ^ 2 = g ^ 2)
    {p i δ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (prim : p ∣ x → p ∣ y → p ∣ z → False)
    (hδ : δ = p ^ i ∨ δ = 2 * p ^ i) (hgx : g = x + δ) (hδH : δ ∣ H) : False := by
  have hA := lemmaA (τ := δ) hx hy hz hE hF (by rw [← hgx]; exact hg.symm)
  have hi : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; rcases hδ with rfl | rfl
      · simp at hA
      · simp at hA; omega
    · exact h0
  have hprod : δ * (2 * x + δ) = H ^ 2 := by
    rw [← hH]; subst hgx; nlinarith [hg]
  obtain ⟨U, hU⟩ := hδH
  have hδ0 : 0 < δ := by
    have := pow_pos hp.pos i
    rcases hδ with rfl | rfl <;> omega
  have h2x : δ ∣ 2 * x := by
    have : δ * (2 * x + δ) = δ * (δ * U ^ 2) := by rw [hprod, hU]; ring
    have := Nat.eq_of_mul_eq_mul_left hδ0 this
    have : δ ∣ 2 * x + δ := ⟨δ / δ * U ^ 2, by rw [this, Nat.div_self hδ0]; ring⟩
    exact (Nat.dvd_add_left (dvd_refl δ)).mp this
  have hcop : Nat.Coprime (p ^ i) 2 :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hPx : p ^ i ∣ x := by
    have : p ^ i ∣ 2 * x := by
      rcases hδ with rfl | rfl
      · exact h2x
      · exact (dvd_mul_left _ _).trans h2x
    exact hcop.dvd_of_dvd_mul_left this
  have hpx : p ∣ x := (dvd_pow_self p (by omega)).trans hPx
  have hpH : p ∣ H := by
    rw [hU]; apply dvd_mul_of_dvd_left
    rcases hδ with rfl | rfl
    · exact dvd_pow_self p (by omega)
    · exact dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
  have hp2H : p ∣ H ^ 2 := dvd_pow hpH two_ne_zero
  have not2 (w : ℕ) (hw : ¬ p ∣ w) : ¬ p ∣ 2 * w := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    · exact hw h'
  have hpy : ¬ p ∣ y := by
    intro hpy
    have : p ∣ z ^ 2 := by
      have : z ^ 2 = H ^ 2 - y ^ 2 := by omega
      rw [this]; exact Nat.dvd_sub hp2H (dvd_pow hpy two_ne_zero)
    exact prim hpx hpy (hp.dvd_of_dvd_pow this)
  have hpz : ¬ p ∣ z := by
    intro hpz
    have : p ∣ y ^ 2 := by
      have : y ^ 2 = H ^ 2 - z ^ 2 := by omega
      rw [this]; exact Nat.dvd_sub hp2H (dvd_pow hpz two_ne_zero)
    exact prim hpx (hp.dvd_of_dvd_pow this) hpz
  rcases hδ with rfl | rfl
  · exact not_odd_core hp hx hy hz hE hF hH hg (not2 y hpy) (not2 z hpz) hgx hU
  · exact not_F1_core hp hx hy hz hE hF hH hg (not2 y hpy) (not2 z hpz) hgx
      (by rw [hU])

end PerfectCuboid.DiagonalTwoPrimes
