module

public import LeanPlayground.PerfectCuboid.Basic
public import Mathlib.NumberTheory.PythagoreanTriples

/-!
# Saunderson's Euler bricks are never perfect (Pocklington 1912, Spohn 1972)

Saunderson's parametrization (1740, `PerfectCuboid.saunderson` in `Basic.lean`) turns every
Pythagorean triple `u² + v² = w²` into the Euler brick
`a = u·|4v² − w²|`, `b = v·|4u² − w²|`, `c = 4uvw`, with face diagonals
`w³`, `u (4v² + w²)` and `v (4u² + w²)`. Its space diagonal satisfies the identity
`a² + b² + c² = w² (u⁴ + 18 u² v² + v⁴)`, so it is a perfect cuboid exactly when
`u⁴ + 18 u² v² + v⁴` is a square. Pocklington (1912) proved that this never happens, and
Spohn (1972) drew the conclusion that no Saunderson brick is perfect.

## Main results

* `pocklington_quartic` — `x⁴ + 18 x² y² + y⁴ = z²` forces `x = 0` or `y = 0`.
* `saunderson_space_diag_sq` — the identity `a² + b² + c² = w² (u⁴ + 18 u² v² + v⁴)`.
* `not_isPerfectCuboid_saunderson`, `not_isPerfectCuboid_saunderson_int` — **Spohn's
  theorem**: no Saunderson brick is a perfect cuboid.
* `saunderson_gcd` — for a primitive triple (`u` odd, `v` even, coprime) the six gcds that
  define the λ-invariant are `gcd(a,c) = u`, `gcd(b,c) = v`, `gcd(c,d) = w` and
  `gcd(a,b) = gcd(a,f) = gcd(b,e) = 1`; so their product is `u v w`.
* `saunderson_gcd_prod_mn` — the same product for `(u, v, w) = (m² − n², 2mn, m² + n²)` is
  `2 m n (m⁴ − n⁴)`, which is the gcd product of the degenerate cuboid `(u, v, 0)`.

## The descent

For coprime `x, y` both odd, `x⁴ + 18x²y² + y⁴ ≡ 20 (mod 32)`, which is not a square.
Otherwise say `x` is odd and `y = 2t`. Then `(x² + y²)² + (4xy)² = z²` is a primitive
Pythagorean triple with odd leg `x² + y²`, so `x² + y² = m² − n²`, `xy = mn/2`, `z = m² + n²`
with `m` odd and `4 ∣ n = 4n'`. Write `x t = m n'` as `x = αβ`, `t = γδ`, `m = αγ`, `n' = βδ`.
Then `β² (α² + 16δ²) = γ² (α² − 4δ²)`, so `α² − 4δ² = kβ²`, `α² + 16δ² = kγ²` with `k ∣ 5`.
`k = 5` is impossible modulo 8, and `k = 1` gives a primitive triple `β² + (2δ)² = α²`,
hence `β = p² − q²`, `δ = pq`, `α = p² + q²` and `γ² = p⁴ + 18p²q² + q⁴` with
`γ ≤ m < z`.

(The congruence argument in some expositions misses the case `4 ∣ y`; the descent above
covers it, and in fact covers every `y` even.)
-/

@[expose] public section

namespace PerfectCuboid

namespace Pocklington

/-! ### Small helpers -/

/-- Rewrite a coprimality statement along `X = A + k Y`. -/
theorem isCoprime_of_eq_add_mul {A X Y : ℤ} (h : IsCoprime A Y) (k : ℤ) (hX : X = A + k * Y) :
    IsCoprime X Y := by
  obtain ⟨α, β, hab⟩ := h
  exact ⟨α, β - α * k, by rw [hX]; linear_combination hab⟩

theorem isCoprime_two_of_odd {W : ℤ} (h : W % 2 = 1) : IsCoprime W 2 :=
  ⟨1, -(W / 2), by omega⟩

theorem emod_two_of_dvd {a x : ℤ} (hx : x % 2 = 1) (h : a ∣ x) : a % 2 = 1 := by
  obtain ⟨b, rfl⟩ := h
  have : Odd (a * b) := Int.odd_iff.mpr hx
  exact Int.odd_iff.mp (Int.odd_mul.mp this).1

theorem sq_emod_eight_of_odd {z : ℤ} (h : z % 2 = 1) : z ^ 2 % 8 = 1 := by
  have h0 : 0 ≤ z % 8 := Int.emod_nonneg z (by norm_num)
  have h1 : z % 8 < 8 := Int.emod_lt_of_pos z (by norm_num)
  have h2 : z % 2 = z % 8 % 2 := (Int.emod_emod_of_dvd z (by norm_num)).symm
  have : z ^ 2 % 8 = (z % 8) ^ 2 % 8 := by rw [pow_two, pow_two, Int.mul_emod]
  rw [this]
  interval_cases hz : z % 8 <;> simp_all

theorem sq_emod_thirtytwo_ne (z : ℤ) : z ^ 2 % 32 ≠ 20 := by
  have h0 : 0 ≤ z % 32 := Int.emod_nonneg z (by norm_num)
  have h1 : z % 32 < 32 := Int.emod_lt_of_pos z (by norm_num)
  have : z ^ 2 % 32 = (z % 32) ^ 2 % 32 := by rw [pow_two, pow_two, Int.mul_emod]
  rw [this]
  interval_cases (z % 32) <;> norm_num

/-- `xt = mn` with all four positive splits as `x = ab`, `t = cd`, `m = ac`, `n = bd`. -/
theorem four_factor {x t m n : ℤ} (hx : 0 < x) (hm : 0 < m) (hn : 0 < n)
    (h : x * t = m * n) :
    ∃ a b c d : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ IsCoprime b c ∧
      x = a * b ∧ t = c * d ∧ m = a * c ∧ n = b * d := by
  obtain ⟨g, b, c, hg0, hbc, rfl, rfl⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left m hx.ne')
  have hg : (0 : ℤ) < g := by exact_mod_cast hg0
  have hb : 0 < b := by
    by_contra hb
    rw [not_lt] at hb
    nlinarith
  have hc : 0 < c := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  have hbc' : IsCoprime b c := Int.isCoprime_iff_gcd_eq_one.mpr hbc
  have h' : b * t = c * n := by
    have : (g : ℤ) * (b * t) = g * (c * n) := by linear_combination h
    exact mul_left_cancel₀ hg.ne' this
  obtain ⟨d, rfl⟩ : b ∣ n := hbc'.dvd_of_dvd_mul_left ⟨t, by linear_combination -h'⟩
  have hd : 0 < d := by
    by_contra hd
    rw [not_lt] at hd
    nlinarith
  have ht' : t = c * d := by
    have : b * t = b * (c * d) := by linear_combination h'
    exact mul_left_cancel₀ hb.ne' this
  exact ⟨g, b, c, d, hg, hb, hc, hd, hbc', by ring, ht', by ring, rfl⟩

/-! ### The descent -/

/-- Coprime odd `x`, `y` never give a square: the quartic is `20` modulo `32`. -/
theorem not_odd_odd {x y z : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : x ^ 4 + 18 * x ^ 2 * y ^ 2 + y ^ 4 = z ^ 2) : False := by
  have hx8 := sq_emod_eight_of_odd hx
  have hy8 := sq_emod_eight_of_odd hy
  obtain ⟨k, hk⟩ : ∃ k, x ^ 2 = 8 * k + 1 := ⟨x ^ 2 / 8, by omega⟩
  obtain ⟨l, hl⟩ : ∃ l, y ^ 2 = 8 * l + 1 := ⟨y ^ 2 / 8, by omega⟩
  have hz : z ^ 2 = 32 * (2 * k ^ 2 + 2 * l ^ 2 + 36 * k * l + 5 * k + 5 * l) + 20 := by
    have : z ^ 2 = (x ^ 2) ^ 2 + 18 * x ^ 2 * y ^ 2 + (y ^ 2) ^ 2 := by rw [← h]; ring
    rw [this, hk, hl]
    ring
  exact sq_emod_thirtytwo_ne z (by omega)

/-- One descent step, for `x` odd and `y` even. -/
theorem descent_of_odd {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hc : IsCoprime x y)
    (hxo : x % 2 = 1) (hye : y % 2 = 0) (h : x ^ 4 + 18 * x ^ 2 * y ^ 2 + y ^ 4 = z ^ 2) :
    ∃ p q c : ℤ, 0 < p ∧ 0 < q ∧ 0 < c ∧ IsCoprime p q ∧
      p ^ 4 + 18 * p ^ 2 * q ^ 2 + q ^ 4 = c ^ 2 ∧ c < z := by
  obtain ⟨t, rfl⟩ : ∃ t, y = 2 * t := ⟨y / 2, by omega⟩
  have ht : 0 < t := by omega
  obtain ⟨s, hs⟩ : ∃ s, x = 2 * s + 1 := ⟨x / 2, by omega⟩
  have hW4 : x ^ 2 + (2 * t) ^ 2 = 4 * (s ^ 2 + s + t ^ 2) + 1 := by rw [hs]; ring
  have hWodd : (x ^ 2 + (2 * t) ^ 2) % 2 = 1 := by omega
  -- the primitive Pythagorean triple `(x² + y²)² + (4xy)² = z²`
  have hpt : PythagoreanTriple (x ^ 2 + (2 * t) ^ 2) (4 * x * (2 * t)) z := by
    unfold PythagoreanTriple
    linear_combination h
  have hcop : IsCoprime (x ^ 2 + (2 * t) ^ 2) (4 * x * (2 * t)) := by
    have h2 := isCoprime_two_of_odd hWodd
    have hWx : IsCoprime (x ^ 2 + (2 * t) ^ 2) x :=
      isCoprime_of_eq_add_mul (hc.symm.pow_left (m := 2)) x (by ring)
    have hWt : IsCoprime (x ^ 2 + (2 * t) ^ 2) (2 * t) :=
      isCoprime_of_eq_add_mul (hc.pow_left (m := 2)) (2 * t) (by ring)
    rw [show (4 : ℤ) * x * (2 * t) = 2 * 2 * x * (2 * t) by ring]
    exact ((h2.mul_right h2).mul_right hWx).mul_right hWt
  obtain ⟨m, n, hWm, h4, hzm, hmn, hpar, hm0⟩ :=
    hpt.coprime_classification' (Int.isCoprime_iff_gcd_eq_one.mp hcop) hWodd hz
  have hxt : 0 < x * t := mul_pos hx ht
  have hmn' : m * n = 4 * (x * t) := by
    have : 2 * (m * n) = 2 * (4 * (x * t)) := by linear_combination -h4
    exact mul_left_cancel₀ two_ne_zero this
  have hm : 0 < m := by
    rcases hm0.lt_or_eq with hm | rfl
    · exact hm
    · simp at hmn'
      omega
  have hn : 0 < n := by
    by_contra hn
    rw [not_lt] at hn
    have := mul_nonpos_of_nonneg_of_nonpos hm.le hn
    linarith
  -- `m` is odd and `n` is even
  have hmo : m % 2 = 1 := by
    rcases hpar with ⟨hm2, hn2⟩ | ⟨hm2, -⟩
    · exfalso
      obtain ⟨a, rfl⟩ : ∃ a, m = 2 * a := ⟨m / 2, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, n = 2 * b + 1 := ⟨n / 2, by omega⟩
      have : (2 * a) ^ 2 - (2 * b + 1) ^ 2 = 4 * (a ^ 2 - b ^ 2 - b) - 1 := by ring
      omega
    · exact hm2
  -- `4 ∣ n`
  have h4m : IsCoprime 4 m := by
    have h2 := isCoprime_two_of_odd hmo
    have := h2.mul_right h2
    norm_num at this
    exact this.symm
  obtain ⟨n', rfl⟩ : (4 : ℤ) ∣ n := h4m.dvd_of_dvd_mul_left ⟨x * t, hmn'⟩
  have hn' : 0 < n' := by omega
  have hxtmn : x * t = m * n' := by
    have : (4 : ℤ) * (x * t) = 4 * (m * n') := by linear_combination -hmn'
    exact mul_left_cancel₀ (by norm_num) this
  obtain ⟨a, b, c, d, ha, hb, hc0, hd, hbc, rfl, rfl, rfl, rfl⟩ :=
    four_factor hx hm hn' hxtmn
  have hkey : b ^ 2 * (a ^ 2 + 16 * d ^ 2) = c ^ 2 * (a ^ 2 - 4 * d ^ 2) := by
    linear_combination hWm
  -- `a² − 4d² = k b²` and `a² + 16 d² = k c²`
  obtain ⟨k, hk⟩ : b ^ 2 ∣ a ^ 2 - 4 * d ^ 2 :=
    (hbc.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left ⟨_, hkey.symm⟩
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb.ne'
  have hk2 : a ^ 2 + 16 * d ^ 2 = c ^ 2 * k := by
    have : b ^ 2 * (a ^ 2 + 16 * d ^ 2) = b ^ 2 * (c ^ 2 * k) := by
      rw [hkey, hk]; ring
    exact mul_left_cancel₀ hb2 this
  have hk0 : 0 < k := by
    by_contra hk0
    rw [not_lt] at hk0
    have : 0 < a ^ 2 + 16 * d ^ 2 := by positivity
    have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) hk0
    linarith
  -- `k ∣ 5`
  have hao : a % 2 = 1 := emod_two_of_dvd hxo (dvd_mul_right a b)
  have hbo : b % 2 = 1 := emod_two_of_dvd hxo (dvd_mul_left b a)
  have hco : c % 2 = 1 := emod_two_of_dvd hmo (dvd_mul_left c a)
  have had : IsCoprime a (2 * d) := by
    have hmn1 : IsCoprime (a * c) (4 * (b * d)) := Int.isCoprime_iff_gcd_eq_one.mpr hmn
    have : IsCoprime a d := hmn1.of_mul_left_left.of_mul_right_right.of_mul_right_right
    exact (isCoprime_two_of_odd hao).mul_right this
  obtain ⟨r, s', hrs⟩ := had.pow (m := 2) (n := 2)
  have hk5 : k ∣ 5 :=
    ⟨r * (4 * b ^ 2 + c ^ 2) + s' * (c ^ 2 - b ^ 2), by
      linear_combination -5 * hrs + r * (4 * hk + hk2) + s' * (hk2 - hk)⟩
  have hkle : k ≤ 5 := Int.le_of_dvd (by norm_num) hk5
  interval_cases k
  · -- `k = 1`: a smaller solution
    have hpt' : PythagoreanTriple b (2 * d) a := by
      unfold PythagoreanTriple
      linear_combination -hk
    have hbd : IsCoprime b (2 * d) :=
      (hc.of_mul_left_right).of_isCoprime_of_dvd_right (mul_dvd_mul_left 2 (dvd_mul_left d c))
    obtain ⟨p, q, hbp, hdq, hap, hpq, -, hp0⟩ :=
      hpt'.coprime_classification' (Int.isCoprime_iff_gcd_eq_one.mp hbd) hbo ha
    have hdpq : d = p * q := by linarith
    have hp : 0 < p := by
      rcases hp0.lt_or_eq with hp | rfl
      · exact hp
      · simp at hdpq
        omega
    have hq : 0 < q := by
      by_contra hq
      rw [not_lt] at hq
      have := mul_nonpos_of_nonneg_of_nonpos hp.le hq
      linarith
    refine ⟨p, q, c, hp, hq, hc0, Int.isCoprime_iff_gcd_eq_one.mpr hpq, ?_, ?_⟩
    · rw [hap, hdpq] at hk2
      linear_combination hk2
    · have h1 : c ≤ a * c := le_mul_of_one_le_left hc0.le (by omega)
      have h2 : a * c ≤ (a * c) ^ 2 := by
        rw [sq]; exact le_mul_of_one_le_left (by positivity) (by nlinarith)
      have h3 : 0 < (4 * (b * d)) ^ 2 := by positivity
      linarith
  · omega
  · omega
  · omega
  · -- `k = 5` is impossible modulo 8
    have := sq_emod_eight_of_odd hao
    have := sq_emod_eight_of_odd hco
    omega

/-- No coprime positive solution: the descent cannot go on forever. -/
theorem not_coprime_sol :
    ∀ (N : ℕ) {x y z : ℤ}, 0 < x → 0 < y → 0 < z → z ≤ N → IsCoprime x y →
      x ^ 4 + 18 * x ^ 2 * y ^ 2 + y ^ 4 = z ^ 2 → False := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x y z hx hy hz hzN hc h
    have step : ∀ {x y : ℤ}, 0 < x → 0 < y → IsCoprime x y → x % 2 = 1 → y % 2 = 0 →
        x ^ 4 + 18 * x ^ 2 * y ^ 2 + y ^ 4 = z ^ 2 → False := by
      intro x y hx hy hc hxo hye h
      obtain ⟨p, q, c, hp, hq, hc0, hpq, h', hlt⟩ := descent_of_odd hx hy hz hc hxo hye h
      exact ih c.toNat (by omega) hp hq hc0 (Int.self_le_toNat c) hpq h'
    rcases Int.emod_two_eq_zero_or_one x with hx2 | hx2 <;>
      rcases Int.emod_two_eq_zero_or_one y with hy2 | hy2
    · have : IsUnit (2 : ℤ) :=
        hc.isUnit_of_dvd' (Int.dvd_of_emod_eq_zero hx2) (Int.dvd_of_emod_eq_zero hy2)
      rw [Int.isUnit_iff] at this
      omega
    · exact step hy hx hc.symm hy2 hx2 (by linear_combination h)
    · exact step hx hy hc hx2 hy2 h
    · exact not_odd_odd hx2 hy2 h

end Pocklington

open Pocklington in
/-- **Pocklington (1912).** `x⁴ + 18 x² y² + y⁴` is a square only when `x y = 0`. -/
theorem pocklington_quartic {x y z : ℤ} (h : x ^ 4 + 18 * x ^ 2 * y ^ 2 + y ^ 4 = z ^ 2) :
    x = 0 ∨ y = 0 := by
  by_contra hxy
  rw [not_or] at hxy
  obtain ⟨hx, hy⟩ := hxy
  have h' : |x| ^ 4 + 18 * |x| ^ 2 * |y| ^ 2 + |y| ^ 4 = |z| ^ 2 := by
    rw [show |x| ^ 4 = (|x| ^ 2) ^ 2 by ring, show |y| ^ 4 = (|y| ^ 2) ^ 2 by ring,
      sq_abs, sq_abs, sq_abs]
    linear_combination h
  obtain ⟨g, x', y', hg0, hcop, hx', hy'⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left |y| (abs_ne_zero.mpr hx))
  have hg : (0 : ℤ) < g := by exact_mod_cast hg0
  have hxa : 0 < |x| := abs_pos.mpr hx
  have hya : 0 < |y| := abs_pos.mpr hy
  have hx0 : 0 < x' := by
    by_contra h0
    rw [not_lt] at h0
    nlinarith
  have hy0 : 0 < y' := by
    by_contra h0
    rw [not_lt] at h0
    nlinarith
  rw [hx', hy'] at h'
  obtain ⟨z', hz'⟩ : (g : ℤ) ^ 2 ∣ |z| := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero]
    exact ⟨x' ^ 4 + 18 * x' ^ 2 * y' ^ 2 + y' ^ 4, by linear_combination -h'⟩
  have hg4 : ((g : ℤ) ^ 2) ^ 2 ≠ 0 := by positivity
  have hq : x' ^ 4 + 18 * x' ^ 2 * y' ^ 2 + y' ^ 4 = z' ^ 2 := by
    have : ((g : ℤ) ^ 2) ^ 2 * (x' ^ 4 + 18 * x' ^ 2 * y' ^ 2 + y' ^ 4) =
        ((g : ℤ) ^ 2) ^ 2 * z' ^ 2 := by
      rw [← mul_pow, ← hz']; linear_combination h'
    exact mul_left_cancel₀ hg4 this
  have hz0 : 0 < z' := by
    have h1 : 0 ≤ |z| := abs_nonneg z
    have h2 : 0 ≤ z' := by
      by_contra h0
      rw [not_le] at h0
      nlinarith
    rcases h2.lt_or_eq with h2 | rfl
    · exact h2
    · have : 0 < x' ^ 4 + 18 * x' ^ 2 * y' ^ 2 + y' ^ 4 := by positivity
      nlinarith
  exact not_coprime_sol z'.toNat hx0 hy0 hz0 (Int.self_le_toNat z')
    (Int.isCoprime_iff_gcd_eq_one.mpr hcop) hq

/-! ### Spohn's theorem -/

/-- The space diagonal of a Saunderson brick: `a² + b² + c² = w² (u⁴ + 18u²v² + v⁴)`. -/
theorem saunderson_space_diag_sq {u v w : ℤ} (h : u ^ 2 + v ^ 2 = w ^ 2) :
    (u * (4 * v ^ 2 - w ^ 2)) ^ 2 + (v * (4 * u ^ 2 - w ^ 2)) ^ 2 + (4 * u * v * w) ^ 2 =
      w ^ 2 * (u ^ 4 + 18 * u ^ 2 * v ^ 2 + v ^ 4) := by
  linear_combination (16 * u ^ 2 * v ^ 2 - u ^ 2 * w ^ 2 - v ^ 2 * w ^ 2) * h

/-- The space diagonal of a Saunderson brick with `u v ≠ 0` is never an integer. -/
theorem saunderson_space_diag_ne_sq {u v w : ℤ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : u ^ 2 + v ^ 2 = w ^ 2) (r : ℤ) :
    (u * (4 * v ^ 2 - w ^ 2)) ^ 2 + (v * (4 * u ^ 2 - w ^ 2)) ^ 2 + (4 * u * v * w) ^ 2 ≠
      r ^ 2 := by
  intro hr
  rw [saunderson_space_diag_sq h] at hr
  have hw : w ^ 2 ≠ 0 := by
    rw [← h]
    have : 0 < u ^ 2 := by positivity
    positivity
  obtain ⟨r', rfl⟩ : w ∣ r := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero]
    exact ⟨_, hr.symm⟩
  have hq : u ^ 4 + 18 * u ^ 2 * v ^ 2 + v ^ 4 = r' ^ 2 := by
    have : w ^ 2 * (u ^ 4 + 18 * u ^ 2 * v ^ 2 + v ^ 4) = w ^ 2 * r' ^ 2 := by
      rw [hr]; ring
    exact mul_left_cancel₀ hw this
  rcases pocklington_quartic hq with h0 | h0
  · exact hu h0
  · exact hv h0

/-- **Spohn (1972).** No Saunderson brick is a perfect cuboid (integer form). -/
theorem not_isPerfectCuboid_saunderson_int {u v w : ℤ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : u ^ 2 + v ^ 2 = w ^ 2) :
    ¬ IsPerfectCuboid (u * (4 * v ^ 2 - w ^ 2)).natAbs (v * (4 * u ^ 2 - w ^ 2)).natAbs
      (4 * u * v * w).natAbs := by
  rintro ⟨-, r, hr⟩
  have hr' : ((u * (4 * v ^ 2 - w ^ 2)).natAbs : ℤ) ^ 2 +
      ((v * (4 * u ^ 2 - w ^ 2)).natAbs : ℤ) ^ 2 + ((4 * u * v * w).natAbs : ℤ) ^ 2 =
      (r : ℤ) ^ 2 := by
    rw [sq (r : ℤ)]; exact_mod_cast hr
  simp only [Int.natCast_natAbs, sq_abs] at hr'
  exact saunderson_space_diag_ne_sq hu hv h r hr'

/-- **Spohn (1972).** No Saunderson brick is a perfect cuboid: the Euler brick
`PerfectCuboid.saunderson` built from a Pythagorean triple `u² + v² = w²` with `u, v > 0`
never has an integer space diagonal. -/
theorem not_isPerfectCuboid_saunderson {u v w : ℕ} (hu : 0 < u) (hv : 0 < v)
    (h : u ^ 2 + v ^ 2 = w ^ 2) :
    ¬ IsPerfectCuboid (u * ((4 * v ^ 2 : ℤ) - w ^ 2).natAbs)
      (v * ((4 * u ^ 2 : ℤ) - w ^ 2).natAbs) (4 * u * v * w) := by
  rintro ⟨-, r, hr⟩
  have hz : (u : ℤ) ^ 2 + v ^ 2 = w ^ 2 := by exact_mod_cast h
  have hr' : ((u : ℤ) * (4 * v ^ 2 - w ^ 2)) ^ 2 + ((v : ℤ) * (4 * u ^ 2 - w ^ 2)) ^ 2 +
      (4 * u * v * w : ℤ) ^ 2 = (r : ℤ) ^ 2 := by
    have := congrArg (Nat.cast : ℕ → ℤ) hr
    push_cast at this
    simp only [mul_pow, sq_abs] at this
    rw [mul_pow, mul_pow, sq (r : ℤ)]
    linear_combination this
  exact saunderson_space_diag_ne_sq (by exact_mod_cast hu.ne') (by exact_mod_cast hv.ne') hz r hr'

/-! ### The gcds of a primitive Saunderson brick -/

open Pocklington in
/-- For a primitive Pythagorean triple (`u` odd, `v` even, `u, v` coprime), the Saunderson
brick `a = u (4v² − w²)`, `b = v (4u² − w²)`, `c = 4uvw` with face diagonals `d = w³`,
`e = u (4v² + w²)`, `f = v (4u² + w²)` has `gcd(a,c) = |u|`, `gcd(b,c) = |v|`, `gcd(c,d) = |w|`
and `gcd(a,b) = gcd(a,f) = gcd(b,e) = 1`. -/
theorem saunderson_gcd {u v w : ℤ} (huv : IsCoprime u v) (hu : u % 2 = 1) (hv : v % 2 = 0)
    (h : u ^ 2 + v ^ 2 = w ^ 2) :
    Int.gcd (u * (4 * v ^ 2 - w ^ 2)) (4 * u * v * w) = u.natAbs ∧
    Int.gcd (v * (4 * u ^ 2 - w ^ 2)) (4 * u * v * w) = v.natAbs ∧
    Int.gcd (4 * u * v * w) (w ^ 3) = w.natAbs ∧
    Int.gcd (u * (4 * v ^ 2 - w ^ 2)) (v * (4 * u ^ 2 - w ^ 2)) = 1 ∧
    Int.gcd (u * (4 * v ^ 2 - w ^ 2)) (v * (4 * u ^ 2 + w ^ 2)) = 1 ∧
    Int.gcd (v * (4 * u ^ 2 - w ^ 2)) (u * (4 * v ^ 2 + w ^ 2)) = 1 := by
  obtain ⟨s, hs⟩ : ∃ s, u = 2 * s + 1 := ⟨u / 2, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, v = 2 * t := ⟨v / 2, by omega⟩
  -- parities
  have hwo : w % 2 = 1 := by
    have e : w ^ 2 = 2 * (2 * s ^ 2 + 2 * s + 2 * t ^ 2) + 1 := by rw [← h, hs, ht]; ring
    rcases Int.emod_two_eq_zero_or_one w with h0 | h0
    · obtain ⟨w', rfl⟩ : ∃ w', w = 2 * w' := ⟨w / 2, by omega⟩
      have : (2 * w') ^ 2 = 2 * (2 * w' ^ 2) := by ring
      omega
    · exact h0
  have hXo : (4 * v ^ 2 - w ^ 2) % 2 = 1 := by
    have e : 4 * v ^ 2 - w ^ 2 = 2 * (6 * t ^ 2 - 2 * s ^ 2 - 2 * s - 1) + 1 := by
      rw [← h, hs, ht]; ring
    omega
  have hYo : (4 * u ^ 2 - w ^ 2) % 2 = 1 := by
    have e : 4 * u ^ 2 - w ^ 2 = 2 * (6 * s ^ 2 + 6 * s + 1 - 2 * t ^ 2) + 1 := by
      rw [← h, hs, ht]; ring
    omega
  -- basic coprimalities
  have huw : IsCoprime u w := by
    have : IsCoprime (w ^ 2) u := isCoprime_of_eq_add_mul (huv.symm.pow_left (m := 2)) u
      (by rw [← h]; ring)
    exact (this.of_isCoprime_of_dvd_left (dvd_pow_self w two_ne_zero)).symm
  have hvw : IsCoprime v w := by
    have : IsCoprime (w ^ 2) v := isCoprime_of_eq_add_mul (huv.pow_left (m := 2)) v
      (by rw [← h]; ring)
    exact (this.of_isCoprime_of_dvd_left (dvd_pow_self w two_ne_zero)).symm
  have h2u := isCoprime_two_of_odd hu
  have h2w := isCoprime_two_of_odd hwo
  have h2X := isCoprime_two_of_odd hXo
  have h2Y := isCoprime_two_of_odd hYo
  -- `X = 4v² − w²`
  have hXv : IsCoprime (4 * v ^ 2 - w ^ 2) v :=
    isCoprime_of_eq_add_mul ((huv.pow_left (m := 2)).neg_left) (3 * v)
      (by rw [← h]; ring)
  have hXw : IsCoprime (4 * v ^ 2 - w ^ 2) w := by
    have : IsCoprime (4 * v ^ 2) w := (IsCoprime.mul_left (h2w.symm.mul_left h2w.symm)
      (hvw.pow_left (m := 2)))
    exact isCoprime_of_eq_add_mul this (-w) (by ring)
  -- `Y = 4u² − w²`
  have hYu : IsCoprime (4 * u ^ 2 - w ^ 2) u :=
    isCoprime_of_eq_add_mul ((huv.symm.pow_left (m := 2)).neg_left) (3 * u)
      (by rw [← h]; ring)
  have hYw : IsCoprime (4 * u ^ 2 - w ^ 2) w := by
    have : IsCoprime (4 * u ^ 2) w := (IsCoprime.mul_left (h2w.symm.mul_left h2w.symm)
      (huw.pow_left (m := 2)))
    exact isCoprime_of_eq_add_mul this (-w) (by ring)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `gcd(a, c) = |u|`
    rw [show 4 * u * v * w = u * (2 * 2 * v * w) by ring, Int.gcd_mul_left,
      Int.isCoprime_iff_gcd_eq_one.mp (((h2X.mul_right h2X).mul_right hXv).mul_right hXw),
      mul_one]
  · -- `gcd(b, c) = |v|`
    rw [show 4 * u * v * w = v * (2 * 2 * u * w) by ring, Int.gcd_mul_left,
      Int.isCoprime_iff_gcd_eq_one.mp (((h2Y.mul_right h2Y).mul_right hYu).mul_right hYw),
      mul_one]
  · -- `gcd(c, d) = |w|`
    have : IsCoprime (2 * 2 * u * v) (w * w) := by
      have hw : IsCoprime (2 * 2 * u * v) w :=
        ((h2w.symm.mul_left h2w.symm).mul_left huw).mul_left hvw
      exact hw.mul_right hw
    rw [show 4 * u * v * w = w * (2 * 2 * u * v) by ring, show w ^ 3 = w * (w * w) by ring,
      Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp this, mul_one]
  · -- `gcd(a, b) = 1`
    apply Int.isCoprime_iff_gcd_eq_one.mp
    have hXY : IsCoprime (4 * v ^ 2 - w ^ 2) (4 * u ^ 2 - w ^ 2) := by
      have h8 : IsCoprime (4 * v ^ 2 - w ^ 2) (2 * 2 * 2 * v ^ 2) :=
        ((h2X.mul_right h2X).mul_right h2X).mul_right (hXv.pow_right (n := 2))
      exact (isCoprime_of_eq_add_mul h8.symm (-3) (X := 4 * u ^ 2 - w ^ 2)
        (by rw [← h]; ring)).symm
    have hu' : IsCoprime u (v * (4 * u ^ 2 - w ^ 2)) := huv.mul_right hYu.symm
    have hX' : IsCoprime (4 * v ^ 2 - w ^ 2) (v * (4 * u ^ 2 - w ^ 2)) := hXv.mul_right hXY
    exact hu'.mul_left hX'
  · -- `gcd(a, f) = 1`
    apply Int.isCoprime_iff_gcd_eq_one.mp
    have hZu : IsCoprime (4 * u ^ 2 + w ^ 2) u :=
      isCoprime_of_eq_add_mul (huw.symm.pow_left (m := 2)) (4 * u) (by ring)
    have hXZ : IsCoprime (4 * v ^ 2 - w ^ 2) (4 * u ^ 2 + w ^ 2) := by
      have h4 : IsCoprime (2 * 2 * w ^ 2) (4 * v ^ 2 - w ^ 2) :=
        ((h2X.mul_right h2X).mul_right (hXw.pow_right (n := 2))).symm
      exact (isCoprime_of_eq_add_mul h4 (-1) (by rw [← h]; ring)).symm
    exact (huv.mul_right hZu.symm).mul_left (hXv.mul_right hXZ)
  · -- `gcd(b, e) = 1`
    apply Int.isCoprime_iff_gcd_eq_one.mp
    have hZv : IsCoprime (4 * v ^ 2 + w ^ 2) v :=
      isCoprime_of_eq_add_mul (hvw.symm.pow_left (m := 2)) (4 * v) (by ring)
    have hYZ : IsCoprime (4 * u ^ 2 - w ^ 2) (4 * v ^ 2 + w ^ 2) := by
      have h4 : IsCoprime (2 * 2 * w ^ 2) (4 * u ^ 2 - w ^ 2) :=
        ((h2Y.mul_right h2Y).mul_right (hYw.pow_right (n := 2))).symm
      exact (isCoprime_of_eq_add_mul h4 (-1) (by rw [← h]; ring)).symm
    exact (huv.symm.mul_right hZv.symm).mul_left (hYu.mul_right hYZ)

/-- The λ-invariant gcd product of a primitive Saunderson brick is `|u v w|`, the same as for the
degenerate cuboid `(u, v, 0)`. -/
theorem saunderson_gcd_prod {u v w : ℤ} (huv : IsCoprime u v) (hu : u % 2 = 1) (hv : v % 2 = 0)
    (h : u ^ 2 + v ^ 2 = w ^ 2) :
    Int.gcd (u * (4 * v ^ 2 - w ^ 2)) (v * (4 * u ^ 2 - w ^ 2)) *
      Int.gcd (u * (4 * v ^ 2 - w ^ 2)) (4 * u * v * w) *
      Int.gcd (v * (4 * u ^ 2 - w ^ 2)) (4 * u * v * w) *
      Int.gcd (u * (4 * v ^ 2 - w ^ 2)) (v * (4 * u ^ 2 + w ^ 2)) *
      Int.gcd (v * (4 * u ^ 2 - w ^ 2)) (u * (4 * v ^ 2 + w ^ 2)) *
      Int.gcd (4 * u * v * w) (w ^ 3) = (u * v * w).natAbs := by
  obtain ⟨hac, hbc, hcd, hab, haf, hbe⟩ := saunderson_gcd huv hu hv h
  rw [hac, hbc, hcd, hab, haf, hbe, Int.natAbs_mul, Int.natAbs_mul]
  ring

open Pocklington in
/-- For `(u, v, w) = (m² − n², 2mn, m² + n²)` with `m, n` coprime of opposite parity, the gcd
product of the Saunderson brick is `2 m n (m⁴ − n⁴)` (up to sign): the λ-invariant of the
Saunderson brick equals that of the degenerate cuboid `(m² − n², 2mn, 0)`. -/
theorem saunderson_gcd_prod_mn {m n : ℤ} (hmn : IsCoprime m n) (hpar : (m + n) % 2 = 1) :
    let u := m ^ 2 - n ^ 2
    let v := 2 * m * n
    let w := m ^ 2 + n ^ 2
    Int.gcd (u * (4 * v ^ 2 - w ^ 2)) (v * (4 * u ^ 2 - w ^ 2)) *
      Int.gcd (u * (4 * v ^ 2 - w ^ 2)) (4 * u * v * w) *
      Int.gcd (v * (4 * u ^ 2 - w ^ 2)) (4 * u * v * w) *
      Int.gcd (u * (4 * v ^ 2 - w ^ 2)) (v * (4 * u ^ 2 + w ^ 2)) *
      Int.gcd (v * (4 * u ^ 2 - w ^ 2)) (u * (4 * v ^ 2 + w ^ 2)) *
      Int.gcd (4 * u * v * w) (w ^ 3) = (2 * m * n * (m ^ 4 - n ^ 4)).natAbs := by
  intro u v w
  have hu : u % 2 = 1 := by
    have e : u = (m + n) * (m + n) - 2 * (n * (m + n)) := by simp only [u]; ring
    obtain ⟨k, hk⟩ : ∃ k, m + n = 2 * k + 1 := ⟨(m + n) / 2, by omega⟩
    rw [e, hk]
    have : (2 * k + 1) * (2 * k + 1) - 2 * (n * (2 * k + 1)) =
      2 * (2 * k ^ 2 + 2 * k - n * (2 * k + 1)) + 1 := by ring
    rw [this]
    omega
  have hv : v % 2 = 0 := by
    have : v = 2 * (m * n) := by simp only [v]; ring
    omega
  have huv : IsCoprime u v := by
    have h2 : IsCoprime u 2 := isCoprime_two_of_odd hu
    have hm : IsCoprime u m :=
      isCoprime_of_eq_add_mul (hmn.symm.pow_left (m := 2)).neg_left m (by simp only [u]; ring)
    have hn : IsCoprime u n :=
      isCoprime_of_eq_add_mul (hmn.pow_left (m := 2)) (-n) (by simp only [u]; ring)
    exact (h2.mul_right hm).mul_right hn
  have h : u ^ 2 + v ^ 2 = w ^ 2 := by simp only [u, v, w]; ring
  rw [saunderson_gcd_prod huv hu hv h]
  congr 1
  simp only [u, v, w]
  ring

end PerfectCuboid
