module

public import LeanPlayground.PerfectCuboid.EulerSecondFamily
public import LeanPlayground.PerfectCuboid.FermatTriangle

/-!
# Colman's degree-14 family of Euler bricks is never perfect

Colman, *Some observations on the classical cuboid and its parametric solutions*,
Fibonacci Quart. 26 (1988) 338–343, formula (4.8), gives (with `b = m`, `c = n`)
`a = (n² − m²)((m² + n²)² M² − 16 m² n² k²)`, `b = 8mn(n⁴ − m⁴) M k`,
`c = 2mn(m⁶ − 41m⁴n² + 27m²n⁴ + 5n⁶)(5m⁶ + 27m⁴n² − 41m²n⁴ + n⁶)`,
where `M = m⁴ + 18m²n² + n⁴` and `k = 3m⁴ − 10m²n² + 3n⁴`. For `(m, n) = (2, 1)` this is
`(570843, 234960, 1128524)`.

Its space diagonal is `a² + b² + c² = (m² + n²)² · O · P` with `O` Euler's octic
(`EulerFamily.octic`, Pocklington's quartic at `(m² − n², 2mn)`) and `P` of degree 16 with
`P = O² + (16 m n R)²`, `R = m⁶ − 15m⁴n² + 15m²n⁴ − n⁶ = Re (m + i n)⁶`.

The proof: for coprime `m, n` of opposite parity, `O` is odd and coprime to `16 m n R`
(Bezout identities with right-hand sides `4096 n¹²`, `4096 m¹²`), hence to `P`; so `O P = □`
forces `O = □`, and Pocklington (`euler_octic_ne_sq`) gives `m n (m² − n²) = 0`. For `m, n`
both odd put `m = u + v`, `n = u − v`: then `O(m, n) = 16 O(u, v)` and
`P(m, n) = 256 (O(u, v)² + (16 u v J)²)` with `J = (u² − v²)(3u⁴ − 10u²v² + 3v⁴)`, and the same
argument applies to `(u, v)`.
-/

@[expose] public section

namespace PerfectCuboid

namespace ColmanFamily

/-- `m⁴ + 18m²n² + n⁴`. -/
def M (m n : ℤ) : ℤ := m ^ 4 + 18 * m ^ 2 * n ^ 2 + n ^ 4

/-- `3m⁴ − 10m²n² + 3n⁴ = (3m² − n²)(m² − 3n²)`. -/
def k (m n : ℤ) : ℤ := 3 * m ^ 4 - 10 * m ^ 2 * n ^ 2 + 3 * n ^ 4

def a (m n : ℤ) : ℤ :=
  (n ^ 2 - m ^ 2) * ((m ^ 2 + n ^ 2) ^ 2 * M m n ^ 2 - 16 * m ^ 2 * n ^ 2 * k m n ^ 2)

def b (m n : ℤ) : ℤ := 8 * m * n * (n ^ 4 - m ^ 4) * M m n * k m n

def c (m n : ℤ) : ℤ :=
  2 * m * n * (m ^ 6 - 41 * m ^ 4 * n ^ 2 + 27 * m ^ 2 * n ^ 4 + 5 * n ^ 6) *
    (5 * m ^ 6 + 27 * m ^ 4 * n ^ 2 - 41 * m ^ 2 * n ^ 4 + n ^ 6)

/-- `Re (m + i n)⁶`. -/
def R (m n : ℤ) : ℤ := m ^ 6 - 15 * m ^ 4 * n ^ 2 + 15 * m ^ 2 * n ^ 4 - n ^ 6

/-- `(m² − n²)(3m⁴ − 10m²n² + 3n⁴)`. -/
def J (m n : ℤ) : ℤ := (m ^ 2 - n ^ 2) * k m n

/-- The degree-16 factor of the space diagonal. -/
def P (m n : ℤ) : ℤ :=
  m ^ 16 + 392 * m ^ 14 * n ^ 2 - 3300 * m ^ 12 * n ^ 4 + 48824 * m ^ 10 * n ^ 6 -
    91578 * m ^ 8 * n ^ 8 + 48824 * m ^ 6 * n ^ 10 - 3300 * m ^ 4 * n ^ 12 +
    392 * m ^ 2 * n ^ 14 + n ^ 16

end ColmanFamily

open ColmanFamily

/-! ### The identities -/

theorem colman_sq_ab (m n : ℤ) :
    a m n ^ 2 + b m n ^ 2 = ((m ^ 2 - n ^ 2) * (m ^ 12 + 182 * m ^ 10 * n ^ 2 -
      561 * m ^ 8 * n ^ 4 + 2612 * m ^ 6 * n ^ 6 - 561 * m ^ 4 * n ^ 8 + 182 * m ^ 2 * n ^ 10 +
      n ^ 12)) ^ 2 := by
  simp only [a, b, M, k]; ring

theorem colman_sq_ac (m n : ℤ) :
    a m n ^ 2 + c m n ^ 2 = ((m ^ 2 + n ^ 2) * (m ^ 12 - 58 * m ^ 10 * n ^ 2 +
      2063 * m ^ 8 * n ^ 4 - 3948 * m ^ 6 * n ^ 6 + 2063 * m ^ 4 * n ^ 8 - 58 * m ^ 2 * n ^ 10 +
      n ^ 12)) ^ 2 := by
  simp only [a, c, M, k]; ring

theorem colman_sq_bc (m n : ℤ) :
    b m n ^ 2 + c m n ^ 2 = (2 * m * n * (13 * m ^ 12 + 94 * m ^ 10 * n ^ 2 +
      1027 * m ^ 8 * n ^ 4 - 2204 * m ^ 6 * n ^ 6 + 1027 * m ^ 4 * n ^ 8 + 94 * m ^ 2 * n ^ 10 +
      13 * n ^ 12)) ^ 2 := by
  simp only [b, c, M, k]; ring

/-- The space diagonal: `a² + b² + c² = (m² + n²)² · (O · P)`. -/
theorem colman_space_diag_sq (m n : ℤ) :
    a m n ^ 2 + b m n ^ 2 + c m n ^ 2 =
      (m ^ 2 + n ^ 2) ^ 2 * (EulerFamily.octic m n * P m n) := by
  simp only [a, b, c, M, k, P, EulerFamily.octic]; ring

theorem colman_P_eq (m n : ℤ) :
    P m n = EulerFamily.octic m n ^ 2 + (16 * m * n * R m n) ^ 2 := by
  simp only [P, R, EulerFamily.octic]; ring

theorem colman_P_add_sub (u v : ℤ) :
    P (u + v) (u - v) =
      256 * (EulerFamily.octic u v ^ 2 + (16 * u * v * J u v) ^ 2) := by
  simp only [P, J, k, EulerFamily.octic]; ring

theorem octic_add_sub (u v : ℤ) :
    EulerFamily.octic (u + v) (u - v) = 16 * EulerFamily.octic u v := by
  simp only [EulerFamily.octic]; ring

theorem octic_eq_sq_add (m n : ℤ) :
    EulerFamily.octic m n = (m ^ 2 + n ^ 2) ^ 4 + 64 * m ^ 2 * n ^ 2 * (m ^ 2 - n ^ 2) ^ 2 := by
  simp only [EulerFamily.octic]; ring

theorem octic_eq_left (m n : ℤ) :
    EulerFamily.octic m n =
      n ^ 8 + (m ^ 7 + 68 * m ^ 5 * n ^ 2 - 122 * m ^ 3 * n ^ 4 + 68 * m * n ^ 6) * m := by
  simp only [EulerFamily.octic]; ring

theorem octic_eq_right (m n : ℤ) :
    EulerFamily.octic m n =
      m ^ 8 + (68 * m ^ 6 * n - 122 * m ^ 4 * n ^ 3 + 68 * m ^ 2 * n ^ 5 + n ^ 7) * n := by
  simp only [EulerFamily.octic]; ring

/-! ### Bezout identities: `O` and `R`, `O` and `J` generate an ideal containing `4096 n¹²`
and `4096 m¹²` (the resultants are `2⁴⁸`). -/

theorem bezout_R (m n : ℤ) :
    (39 * m ^ 4 - 602 * m ^ 2 * n ^ 2 + 819 * n ^ 4) * EulerFamily.octic m n +
      (-39 * m ^ 6 - 2635 * m ^ 4 * n ^ 2 + 5935 * m ^ 2 * n ^ 4 - 3277 * n ^ 6) * R m n =
      4096 * n ^ 12 := by
  simp only [R, EulerFamily.octic]; ring

theorem bezout_R' (m n : ℤ) :
    (819 * m ^ 4 - 602 * m ^ 2 * n ^ 2 + 39 * n ^ 4) * EulerFamily.octic m n +
      (3277 * m ^ 6 - 5935 * m ^ 4 * n ^ 2 + 2635 * m ^ 2 * n ^ 4 + 39 * n ^ 6) * R m n =
      4096 * m ^ 12 := by
  simp only [R, EulerFamily.octic]; ring

theorem bezout_J (m n : ℤ) :
    (-9 * m ^ 4 - 90 * m ^ 2 * n ^ 2 + 355 * n ^ 4) * EulerFamily.octic m n +
      (3 * m ^ 6 + 247 * m ^ 4 * n ^ 2 + 2613 * m ^ 2 * n ^ 4 - 1247 * n ^ 6) * J m n =
      4096 * n ^ 12 := by
  simp only [J, k, EulerFamily.octic]; ring

theorem bezout_J' (m n : ℤ) :
    (355 * m ^ 4 - 90 * m ^ 2 * n ^ 2 - 9 * n ^ 4) * EulerFamily.octic m n +
      (1247 * m ^ 6 - 2613 * m ^ 4 * n ^ 2 - 247 * m ^ 2 * n ^ 4 - 3 * n ^ 6) * J m n =
      4096 * m ^ 12 := by
  simp only [J, k, EulerFamily.octic]; ring

/-! ### The coprimality argument -/

theorem octic_odd {x y : ℤ} (hodd : Odd (x + y)) : EulerFamily.octic x y % 2 = 1 := by
  have h1 : Odd (x ^ 2 + y ^ 2) := by
    have e : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    rw [e]
    exact hodd.pow.sub_even (even_two_mul _)
  have e : EulerFamily.octic x y =
      (x ^ 2 + y ^ 2) ^ 4 + 2 * (32 * x ^ 2 * y ^ 2 * (x ^ 2 - y ^ 2) ^ 2) := by
    simp only [EulerFamily.octic]; ring
  rw [e]
  exact Int.odd_iff.mp (h1.pow.add_even (even_two_mul _))

theorem octic_pos {x y : ℤ} (hodd : Odd (x + y)) : 0 < EulerFamily.octic x y := by
  have h1 : (x ^ 2 + y ^ 2) % 2 = 1 := by
    have e : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    rw [e]
    exact Int.odd_iff.mp (hodd.pow.sub_even (even_two_mul _))
  have hs : x ^ 2 + y ^ 2 ≠ 0 := by
    intro h0
    rw [h0] at h1
    norm_num at h1
  have hs' : 0 < x ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hs)
  have h4 : 0 < (x ^ 2 + y ^ 2) ^ 4 := pow_pos hs' 4
  have h5 : 0 ≤ 64 * x ^ 2 * y ^ 2 * (x ^ 2 - y ^ 2) ^ 2 := by positivity
  rw [octic_eq_sq_add]
  linarith

/-- The key step: for coprime `x, y` of opposite parity and any `G` satisfying the two Bezout
identities, `O · (O² + (16 x y G)²) = □` forces `x y (x² − y²) = 0`. -/
theorem key_step {x y G w α β α' β' : ℤ} (hxy : IsCoprime x y) (hodd : Odd (x + y))
    (h1 : α * EulerFamily.octic x y + β * G = 4096 * y ^ 12)
    (h2 : α' * EulerFamily.octic x y + β' * G = 4096 * x ^ 12)
    (hw : EulerFamily.octic x y * (EulerFamily.octic x y ^ 2 + (16 * x * y * G) ^ 2) = w ^ 2) :
    x = 0 ∨ y = 0 ∨ x ^ 2 = y ^ 2 := by
  have hO2 : IsCoprime (EulerFamily.octic x y) 2 :=
    Pocklington.isCoprime_two_of_odd (octic_odd hodd)
  have hOG : IsCoprime (EulerFamily.octic x y) G := by
    obtain ⟨p, q, hpq⟩ : IsCoprime (x ^ 12) (y ^ 12) := hxy.pow
    obtain ⟨r, s, hrs⟩ : IsCoprime (EulerFamily.octic x y) (2 ^ 12) := hO2.pow_right
    exact ⟨r + s * (p * α' + q * α), s * (p * β' + q * β), by
      linear_combination hrs + s * p * h2 + s * q * h1 + 4096 * s * hpq⟩
  have hOx : IsCoprime (EulerFamily.octic x y) x :=
    Pocklington.isCoprime_of_eq_add_mul (hxy.symm.pow_left : IsCoprime (y ^ 8) x) _
      (octic_eq_left x y)
  have hOy : IsCoprime (EulerFamily.octic x y) y :=
    Pocklington.isCoprime_of_eq_add_mul (hxy.pow_left : IsCoprime (x ^ 8) y) _
      (octic_eq_right x y)
  have hO16 : IsCoprime (EulerFamily.octic x y) 16 := by
    rw [show (16 : ℤ) = 2 ^ 4 by norm_num]
    exact hO2.pow_right
  have hOK : IsCoprime (EulerFamily.octic x y) (16 * x * y * G) :=
    ((hO16.mul_right hOx).mul_right hOy).mul_right hOG
  have hKO : IsCoprime ((16 * x * y * G) ^ 2) (EulerFamily.octic x y) := hOK.symm.pow_left
  have hPO : IsCoprime (EulerFamily.octic x y ^ 2 + (16 * x * y * G) ^ 2)
      (EulerFamily.octic x y) :=
    Pocklington.isCoprime_of_eq_add_mul hKO (EulerFamily.octic x y) (by ring)
  have hOP := hPO.symm
  obtain ⟨r, -, hr⟩ := FermatTriangle.exists_sq_eq_of_isCoprime hOP hw (octic_pos hodd)
  exact euler_octic_ne_sq hr

/-- Coprime `m, n`: `O · P = □` forces `m n (m² − n²) = 0`. -/
theorem octic_mul_P_coprime {m n w : ℤ} (hmn : IsCoprime m n)
    (hw : EulerFamily.octic m n * P m n = w ^ 2) : m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2 := by
  by_cases hodd : Odd (m + n)
  · rw [colman_P_eq] at hw
    exact key_step hmn hodd (bezout_R m n) (bezout_R' m n) hw
  · -- `m + n` even: write `m = u + v`, `n = u − v`.
    obtain ⟨u, hu⟩ : Even (m + n) := Int.not_odd_iff_even.mp hodd
    obtain ⟨v, hv⟩ : ∃ v, v = u - n := ⟨_, rfl⟩
    have hm : m = u + v := by omega
    have hn : n = u - v := by omega
    have huv : IsCoprime u v :=
      FermatTriangle.isCoprime_of_isCoprime_add_sub (by rw [← hm, ← hn]; exact hmn)
    have hodd' : Odd (u + v) := by
      rw [← hm]
      by_contra hme
      obtain ⟨p, hp⟩ : Even m := Int.not_odd_iff_even.mp hme
      have h2 := hmn.isUnit_of_dvd' (show (2 : ℤ) ∣ m from ⟨p, by omega⟩)
        (show (2 : ℤ) ∣ n from ⟨u - p, by omega⟩)
      rw [Int.isUnit_iff] at h2
      omega
    rw [hm, hn, octic_add_sub, colman_P_add_sub] at hw
    have h64 : (64 : ℤ) ^ 2 ∣ w ^ 2 :=
      ⟨EulerFamily.octic u v * (EulerFamily.octic u v ^ 2 + (16 * u * v * J u v) ^ 2), by
        rw [← hw]; ring⟩
    obtain ⟨w', rfl⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp h64
    have hw' : EulerFamily.octic u v * (EulerFamily.octic u v ^ 2 + (16 * u * v * J u v) ^ 2) =
        w' ^ 2 :=
      mul_left_cancel₀ (by norm_num : (4096 : ℤ) ≠ 0) (by linear_combination hw)
    rcases key_step huv hodd' (bezout_J u v) (bezout_J' u v) hw' with h0 | h0 | h0
    · right; right
      linear_combination (4 * v) * h0 + (m + u + v) * hm - (n + u - v) * hn
    · right; right
      linear_combination (4 * u) * h0 + (m + u + v) * hm - (n + u - v) * hn
    · have h3 : (u + v) * (u - v) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp h3 with h4 | h4
      · left; rw [hm]; exact h4
      · right; left; rw [hn]; exact h4

/-- **`O · P` is a square only on the degenerate lines `m n (m² − n²) = 0`.** -/
theorem octic_mul_P_ne_sq {m n w : ℤ} (hw : EulerFamily.octic m n * P m n = w ^ 2) :
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2 := by
  rcases eq_or_ne m 0 with hm | hm
  · exact Or.inl hm
  obtain ⟨g, m', n', hg0, hcop, rfl, rfl⟩ := Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left n hm)
  have hg : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
  have e : EulerFamily.octic (m' * g) (n' * g) * P (m' * g) (n' * g) =
      ((g : ℤ) ^ 12) ^ 2 * (EulerFamily.octic m' n' * P m' n') := by
    simp only [EulerFamily.octic, P]; ring
  rw [e] at hw
  obtain ⟨w', rfl⟩ : (g : ℤ) ^ 12 ∣ w := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨_, hw.symm⟩
  have hw' : EulerFamily.octic m' n' * P m' n' = w' ^ 2 :=
    mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero 12 hg)) (by linear_combination hw)
  rcases octic_mul_P_coprime (Int.isCoprime_iff_gcd_eq_one.mpr hcop) hw' with h | h | h
  · left; rw [h, zero_mul]
  · right; left; rw [h, zero_mul]
  · right; right; rw [mul_pow, mul_pow, h]

/-! ### No brick of the family is perfect -/

/-- `(m, n) = (2, 1)` gives Colman's brick `(570843, 234960, 1128524)`. -/
theorem colman_two_one :
    ((a 2 1).natAbs, (b 2 1).natAbs, (c 2 1).natAbs) = (570843, 234960, 1128524) := by
  decide

theorem colman_space_diag_ne_sq {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ^ 2 ≠ n ^ 2)
    (r : ℤ) : a m n ^ 2 + b m n ^ 2 + c m n ^ 2 ≠ r ^ 2 := by
  intro hr
  rw [colman_space_diag_sq] at hr
  have hw : (m ^ 2 + n ^ 2) ^ 2 ≠ 0 := by positivity
  obtain ⟨r', rfl⟩ : m ^ 2 + n ^ 2 ∣ r := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero]
    exact ⟨_, hr.symm⟩
  have hq : EulerFamily.octic m n * P m n = r' ^ 2 :=
    mul_left_cancel₀ hw (by linear_combination hr)
  rcases octic_mul_P_ne_sq hq with h0 | h0 | h0
  · exact hm h0
  · exact hn h0
  · exact hmn h0

/-- **No brick of Colman's family (4.8) is a perfect cuboid.** -/
theorem not_isPerfectCuboid_colman {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ^ 2 ≠ n ^ 2) :
    ¬ IsPerfectCuboid (a m n).natAbs (b m n).natAbs (c m n).natAbs := by
  rintro ⟨-, r, hr⟩
  have hr' : ((a m n).natAbs : ℤ) ^ 2 + ((b m n).natAbs : ℤ) ^ 2 + ((c m n).natAbs : ℤ) ^ 2 =
      (r : ℤ) ^ 2 := by
    rw [sq (r : ℤ)]; exact_mod_cast hr
  simp only [Int.natCast_natAbs, sq_abs] at hr'
  exact colman_space_diag_ne_sq hm hn hmn r hr'

end PerfectCuboid
