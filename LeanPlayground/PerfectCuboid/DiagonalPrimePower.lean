module

public import Mathlib
public import LeanPlayground.PerfectCuboid.Basic

/-!
# No face diagonal of a perfect cuboid is a prime power

Proof: for the edge `x` opposite the face with diagonal
`H = p ^ k`, `g − x` and `g + x` are powers of `p`. Lemma A (`(g − x)² > 2 (g + x)`, from
`E² + F² = g² + x²` and `E + F > g + x`) forces `g − x = p ^ i` with `i ≥ 1`, so `p ^ i ∣ x`.
Lemma B (a prime power `p ^ m ∣ x²` with `p ∤ 2y` satisfies `p ^ m ≤ E + y < x + 2y`) and
`y < H` then contradict Lemma A. Common factors `p` of all edges are divided out by induction.
-/

@[expose] public section

namespace PerfectCuboid.DiagonalPrimePower

/-- **Lemma A.** If `x, y, z > 0`, `E² = x² + y²`, `F² = x² + z²` and `(x + τ)² = x² + y² + z²`,
then `τ² ≥ 2 (2x + τ) + 1`, i.e. `(g − x)² > 2 (g + x)` for `g = x + τ`. -/
theorem lemmaA {x y z E F τ : ℕ} (_hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hE : x ^ 2 + y ^ 2 = E ^ 2) (hF : x ^ 2 + z ^ 2 = F ^ 2)
    (hg : (x + τ) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2) :
    2 * (2 * x + τ) + 1 ≤ τ ^ 2 := by
  have hg' : (x + τ) ^ 2 = x ^ 2 + (y ^ 2 + z ^ 2) := by rw [hg]; ring
  have hEF : (E * F) ^ 2 = ((x + τ) * x) ^ 2 + (y * z) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, ← hE, ← hF, hg']; ring
  have hyz : 0 < y * z := Nat.mul_pos hy hz
  have hlt : (x + τ) * x < E * F := by
    have h1 : 0 < (y * z) ^ 2 := by positivity
    have : ((x + τ) * x) ^ 2 < (E * F) ^ 2 := by rw [hEF]; omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have e1 : (E + F) ^ 2 = E ^ 2 + F ^ 2 + 2 * (E * F) := by ring
  have e2 : (2 * x + τ) ^ 2 = (x + τ) ^ 2 + x ^ 2 + 2 * ((x + τ) * x) := by ring
  have e3 : E ^ 2 + F ^ 2 = (x + τ) ^ 2 + x ^ 2 := by rw [← hE, ← hF, hg']; ring
  have hsum : 2 * x + τ + 1 ≤ E + F := by
    have : (2 * x + τ) ^ 2 < (E + F) ^ 2 := by rw [e1, e2, e3]; omega
    have := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
    omega
  have hid : τ ^ 2 + (2 * x + τ) ^ 2 = 2 * E ^ 2 + 2 * F ^ 2 := by
    have : τ ^ 2 + (2 * x + τ) ^ 2 = 2 * ((x + τ) ^ 2 + x ^ 2) := by ring
    rw [this, ← e3]; ring
  have h3 : (2 * x + τ + 1) ^ 2 ≤ (E + F) ^ 2 := Nat.pow_le_pow_left hsum 2
  have h4 : (E + F) ^ 2 ≤ 2 * E ^ 2 + 2 * F ^ 2 := by
    have : (E + F) ^ 2 + ((E : ℤ) - F) ^ 2 = 2 * E ^ 2 + 2 * F ^ 2 := by ring
    have h5 : (0:ℤ) ≤ ((E : ℤ) - F) ^ 2 := sq_nonneg _
    have : ((E + F) ^ 2 : ℤ) ≤ 2 * E ^ 2 + 2 * F ^ 2 := by linarith
    exact_mod_cast this
  have e4 : (2 * x + τ + 1) ^ 2 = (2 * x + τ) ^ 2 + 2 * (2 * x + τ) + 1 := by ring
  omega

/-- **Lemma B.** If `p` is a prime, `p ∤ 2y`, `p ^ m ∣ x²`, and `E² = x² + y²` with `x, y > 0`,
then `p ^ m < x + 2y`. -/
theorem lemmaB {p m x y E : ℕ} (hp : p.Prime) (hy2 : ¬ p ∣ 2 * y) (hx : 0 < x) (hy : 0 < y)
    (hE : x ^ 2 + y ^ 2 = E ^ 2) (hdvd : p ^ m ∣ x ^ 2) : p ^ m < x + 2 * y := by
  have hyE : y < E := by
    have : y ^ 2 < E ^ 2 := by rw [← hE]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hEx : E < x + y := by
    have : E ^ 2 < (x + y) ^ 2 := by rw [← hE]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  obtain ⟨σ, rfl⟩ : ∃ σ, E = y + σ := ⟨E - y, by omega⟩
  have hfac : x ^ 2 = σ * (2 * y + σ) := by nlinarith [hE]
  rw [hfac] at hdvd
  have key : p ^ m ≤ 2 * y + σ := by
    by_cases hσ : p ∣ σ
    · have h2 : ¬ p ∣ 2 * y + σ := by
        intro h
        exact hy2 ((Nat.dvd_add_left hσ).mp h)
      have hc : Nat.Coprime (p ^ m) (2 * y + σ) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr h2)
      have : p ^ m ∣ σ := hc.dvd_of_dvd_mul_right hdvd
      have hσ0 : 0 < σ := by
        rcases Nat.eq_zero_or_pos σ with h0 | h0
        · subst h0; simp at hfac; omega
        · exact h0
      exact (Nat.le_of_dvd hσ0 this).trans (by omega)
    · have hc : Nat.Coprime (p ^ m) σ :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hσ)
      exact Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left hdvd)
  omega

theorem two_dvd_of_four_dvd_sq_add_sq {y z : ℕ} (h : 4 ∣ y ^ 2 + z ^ 2) : 2 ∣ y ∧ 2 ∣ z := by
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' y <;> obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' z
  · exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  · exfalso
    have : (2 * a) ^ 2 + (2 * b + 1) ^ 2 = 4 * (a ^ 2 + b ^ 2 + b) + 1 := by ring
    omega
  · exfalso
    have : (2 * a + 1) ^ 2 + (2 * b) ^ 2 = 4 * (a ^ 2 + a + b ^ 2) + 1 := by ring
    omega
  · exfalso
    have : (2 * a + 1) ^ 2 + (2 * b + 1) ^ 2 = 4 * (a ^ 2 + a + b ^ 2 + b) + 2 := by ring
    omega

/-- **Core of the face-diagonal theorem.** Edges `x, y, z > 0` of a perfect cuboid with no prime
dividing all three; `H` is the diagonal of the face `(y, z)`. Then `H` is not a prime power. -/
theorem face_diagonal_ne_prime_pow_of_not_dvd {x y z E F H g : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hE : x ^ 2 + y ^ 2 = E ^ 2) (hF : x ^ 2 + z ^ 2 = F ^ 2) (hH : y ^ 2 + z ^ 2 = H ^ 2)
    (hg : x ^ 2 + y ^ 2 + z ^ 2 = g ^ 2)
    {p k : ℕ} (hp : p.Prime) (prim : p ∣ x → p ∣ y → p ∣ z → False) : H ≠ p ^ k := by
  intro hHk
  have hp1 := hp.one_lt
  -- `g = x + τ`
  have hxg : x < g := by
    have : x ^ 2 < g ^ 2 := by rw [← hg]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  obtain ⟨τ, rfl⟩ : ∃ τ, g = x + τ := ⟨g - x, by omega⟩
  have hA := lemmaA hx hy hz hE hF hg.symm
  have hprod : τ * (2 * x + τ) = p ^ (2 * k) := by
    rw [pow_mul', ← hHk, ← hH]; nlinarith [hg]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro _ hprod)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left _ hprod)
  have hij : i + j = 2 * k := by
    apply Nat.pow_right_injective hp.two_le
    simp only [pow_add, ← hi, ← hj, hprod]
  have hlt : i < j := (Nat.pow_lt_pow_iff_right hp1).mp (by rw [← hi, ← hj]; omega)
  have hkj : k < j := by omega
  have hi0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0, pow_zero] at hi; subst hi; nlinarith
    · exact h0
  -- `p ^ i ∣ 2 x`
  have h2x : 2 * x + p ^ i = p ^ i * p ^ (j - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hlt.le, ← hj, hi]
  have hdvd2x : p ^ i ∣ 2 * x := by
    have : p ^ i ∣ 2 * x + p ^ i := ⟨_, h2x⟩
    exact (Nat.dvd_add_left (dvd_refl _)).mp this
  by_cases hp2 : p = 2
  · subst hp2
    rcases Nat.lt_or_ge i 2 with h1 | h2
    · -- `τ = 2`, contradicting Lemma A
      have : i = 1 := by omega
      subst this
      have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hi] at hA
      norm_num at hA
      omega
    · -- `4 ∣ 2x`, so `x` and `g` are even, so `y, z` are even
      have h4 : 4 ∣ 2 * x := (pow_dvd_pow 2 h2).trans hdvd2x
      have hx2 : 2 ∣ x := by omega
      have hk2 : 1 ≤ k := by omega
      have h4H : 4 ∣ y ^ 2 + z ^ 2 := by
        rw [hH, hHk, ← pow_mul, show (4:ℕ) = 2 ^ 2 by norm_num]
        exact pow_dvd_pow 2 (by omega)
      obtain ⟨hy2, hz2⟩ := two_dvd_of_four_dvd_sq_add_sq h4H
      exact prim hx2 hy2 hz2
  · -- odd `p`: `p ^ i ∣ x`, and `p` misses `y` or `z`
    have hcop2 : Nat.Coprime (p ^ i) 2 :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have hdx : p ^ i ∣ x := hcop2.dvd_of_dvd_mul_left hdvd2x
    have hpx : p ∣ x := (dvd_pow_self p hi0.ne').trans hdx
    have hsq : p ^ (2 * i) ∣ x ^ 2 := by rw [pow_mul']; exact pow_dvd_pow_of_dvd hdx 2
    have not2 (w : ℕ) (hw : ¬ p ∣ w) : ¬ p ∣ 2 * w := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
      · exact hw h'
    -- the final inequality, for whichever of `y, z` is prime to `p`
    have final (w : ℕ) (W : ℕ) (hw0 : 0 < w) (hw : ¬ p ∣ w) (hW : x ^ 2 + w ^ 2 = W ^ 2)
        (hwH : w < p ^ k) : False := by
      have hB := lemmaB hp (not2 w hw) hx hw0 hW hsq
      have hτ : τ = p ^ i := hi
      have hpow : p ^ (2 * i) = τ ^ 2 := by rw [hτ, ← pow_mul, mul_comm]
      have hjk : p * p ^ k ≤ p ^ j := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right hp.pos hkj
      have h2pk : 2 * p ^ k ≤ p ^ j := le_trans (Nat.mul_le_mul_right _ hp.two_le) hjk
      rw [hpow] at hB
      rw [← hj] at h2pk
      nlinarith
    have hyH : y < p ^ k := by
      rw [← hHk]
      have : y ^ 2 < H ^ 2 := by rw [← hH]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
    have hzH : z < p ^ k := by
      rw [← hHk]
      have : z ^ 2 < H ^ 2 := by rw [← hH]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
    by_cases hpy : p ∣ y
    · by_cases hpz : p ∣ z
      · exact prim hpx hpy hpz
      · exact final z F hz hpz hF hzH
    · exact final y E hy hpy hE hyH

/-- Dividing a cuboid relation by a common prime factor. -/
theorem div_of_dvd {p x y E : ℕ} (hp : p.Prime) (hx : p ∣ x) (hy : p ∣ y)
    (hE : x ^ 2 + y ^ 2 = E ^ 2) : p ∣ E ∧ (x / p) ^ 2 + (y / p) ^ 2 = (E / p) ^ 2 := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  have hE' : p ∣ E := hp.dvd_of_dvd_pow (n := 2) ⟨p * (x' ^ 2 + y' ^ 2), by rw [← hE]; ring⟩
  obtain ⟨E', rfl⟩ := hE'
  refine ⟨dvd_mul_right _ _, ?_⟩
  simp only [Nat.mul_div_cancel_left _ hp.pos]
  have : p ^ 2 * (x' ^ 2 + y' ^ 2) = p ^ 2 * E' ^ 2 := by rw [← mul_pow, ← hE]; ring
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) this

/-- **General form.** If `x, y, z > 0` are the edges of a perfect cuboid (all face diagonals
and the space diagonal integral), the diagonal `H` of the face `(y, z)` is not a prime power. No
primitivity is needed. -/
theorem face_diagonal_ne_prime_pow {p : ℕ} (hp : p.Prime) :
    ∀ (k : ℕ) {x y z E F H g : ℕ}, 0 < x → 0 < y → 0 < z →
    x ^ 2 + y ^ 2 = E ^ 2 → x ^ 2 + z ^ 2 = F ^ 2 → y ^ 2 + z ^ 2 = H ^ 2 →
    x ^ 2 + y ^ 2 + z ^ 2 = g ^ 2 → H ≠ p ^ k := by
  intro k
  induction k with
  | zero =>
    intro x y z E F H g hx hy hz _ _ hH _ hHk
    rw [pow_zero] at hHk; subst hHk
    nlinarith
  | succ k ih =>
    intro x y z E F H g hx hy hz hE hF hH hg hHk
    refine face_diagonal_ne_prime_pow_of_not_dvd hx hy hz hE hF hH hg hp ?_ hHk
    intro hpx hpy hpz
    obtain ⟨-, hE'⟩ := div_of_dvd hp hpx hpy hE
    obtain ⟨-, hF'⟩ := div_of_dvd hp hpx hpz hF
    obtain ⟨-, hH'⟩ := div_of_dvd hp hpy hpz hH
    have hpg : p ∣ g := hp.dvd_of_dvd_pow (n := 2) (by
      rw [← hg]; exact dvd_add (dvd_add (dvd_pow hpx two_ne_zero) (dvd_pow hpy two_ne_zero))
        (dvd_pow hpz two_ne_zero))
    have hg' : (x / p) ^ 2 + (y / p) ^ 2 + (z / p) ^ 2 = (g / p) ^ 2 := by
      obtain ⟨x', rfl⟩ := hpx; obtain ⟨y', rfl⟩ := hpy; obtain ⟨z', rfl⟩ := hpz
      obtain ⟨g', rfl⟩ := hpg
      simp only [Nat.mul_div_cancel_left _ hp.pos]
      have : p ^ 2 * (x' ^ 2 + y' ^ 2 + z' ^ 2) = p ^ 2 * g' ^ 2 := by rw [← mul_pow, ← hg]; ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) this
    have pos {w : ℕ} (hw : 0 < w) (hpw : p ∣ w) : 0 < w / p :=
      Nat.div_pos (Nat.le_of_dvd hw hpw) hp.pos
    refine ih (pos hx hpx) (pos hy hpy) (pos hz hpz) hE' hF' hH' hg' ?_
    rw [hHk, pow_succ, Nat.mul_div_cancel _ hp.pos]

/-- No face diagonal of a perfect cuboid is a prime power. -/
theorem _root_.PerfectCuboid.IsPerfectCuboid.face_diagonal_ne_prime_pow {a b c : ℕ}
    (h : IsPerfectCuboid a b c) {d : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2) {p k : ℕ} (hp : p.Prime) :
    d ≠ p ^ k := by
  obtain ⟨e, he⟩ := h.sq_ca
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  exact DiagonalPrimePower.face_diagonal_ne_prime_pow hp k h.pos_c h.pos_a h.pos_b
    (E := e) (F := f) (g := g)
    (by rw [sq e, ← he]) (by rw [sq f, ← hf]; ring) hd.symm (by rw [sq g, ← hg]; ring)

end PerfectCuboid.DiagonalPrimePower
