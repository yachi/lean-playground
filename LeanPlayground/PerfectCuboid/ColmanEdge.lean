module

public import LeanPlayground.PerfectCuboid.Saunderson

/-!
# The Bromhead–Colman edge cuboids never have an integral third edge

Colman, *On certain semi-perfect cuboids*, Fibonacci Quart. 26 (1988) 54–57, formula (4.12),
generalizing Bromhead (Math. Gaz. 44 (1960) 219–220; Bromhead's family is `p = t + 1`, `q = t`):
`a = 2pq(p⁴ + 4p²q² − q⁴)(q⁴ + 4p²q² − p⁴)`,
`b = p²(q⁴ + 4p²q² − p⁴)² − q²(p⁴ + 4p²q² − q⁴)²`,
`c = 32p²q²(p⁴ − q⁴)²(p⁸ + 14p⁴q⁴ + q⁸)`.
Then `a² + b²`, `a² + c`, `b² + c` and `a² + b² + c` are squares, so `(a, b, √c)` is an edge
cuboid; `(p, q) = (2, 1)` gives `(124, 957, √13852800)`. Colman proved that `c` is never a
square. We give a short 2-adic proof: `c = 2 E (4pq(p⁴ − q⁴))²` with `E = p⁸ + 14p⁴q⁴ + q⁸`,
and `2E` has odd 2-adic valuation (`E` is odd if `p + q` is odd, and `E ≡ 16 (mod 32)` if
`p, q` are both odd).
-/

@[expose] public section

namespace PerfectCuboid

namespace ColmanEdge

def a (p q : ℤ) : ℤ :=
  2 * p * q * (p ^ 4 + 4 * p ^ 2 * q ^ 2 - q ^ 4) * (q ^ 4 + 4 * p ^ 2 * q ^ 2 - p ^ 4)

def b (p q : ℤ) : ℤ :=
  p ^ 2 * (q ^ 4 + 4 * p ^ 2 * q ^ 2 - p ^ 4) ^ 2 - q ^ 2 * (p ^ 4 + 4 * p ^ 2 * q ^ 2 - q ^ 4) ^ 2

/-- The square of the missing edge. -/
def c (p q : ℤ) : ℤ :=
  32 * p ^ 2 * q ^ 2 * (p ^ 4 - q ^ 4) ^ 2 * (p ^ 8 + 14 * p ^ 4 * q ^ 4 + q ^ 8)

def E (p q : ℤ) : ℤ := p ^ 8 + 14 * p ^ 4 * q ^ 4 + q ^ 8

end ColmanEdge

open ColmanEdge

/-! ### The identities -/

theorem colmanEdge_sq_ab (p q : ℤ) :
    a p q ^ 2 + b p q ^ 2 = ((p ^ 2 + q ^ 2) * (p ^ 8 - 8 * p ^ 6 * q ^ 2 + 30 * p ^ 4 * q ^ 4 -
      8 * p ^ 2 * q ^ 6 + q ^ 8)) ^ 2 := by
  simp only [a, b]; ring

theorem colmanEdge_sq_ac (p q : ℤ) :
    a p q ^ 2 + c p q = (2 * p * q * (p ^ 4 + 3 * q ^ 4) * (3 * p ^ 4 + q ^ 4)) ^ 2 := by
  simp only [a, c]; ring

theorem colmanEdge_sq_bc (p q : ℤ) :
    b p q ^ 2 + c p q = ((p ^ 2 - q ^ 2) * (p ^ 4 - 2 * p ^ 3 * q + 6 * p ^ 2 * q ^ 2 -
      2 * p * q ^ 3 + q ^ 4) * (p ^ 4 + 2 * p ^ 3 * q + 6 * p ^ 2 * q ^ 2 + 2 * p * q ^ 3 +
      q ^ 4)) ^ 2 := by
  simp only [b, c]; ring

theorem colmanEdge_sq_abc (p q : ℤ) :
    a p q ^ 2 + b p q ^ 2 + c p q = ((p ^ 2 + q ^ 2) * (p ^ 8 + 8 * p ^ 6 * q ^ 2 -
      2 * p ^ 4 * q ^ 4 + 8 * p ^ 2 * q ^ 6 + q ^ 8)) ^ 2 := by
  simp only [a, b, c]; ring

theorem colmanEdge_c_eq (p q : ℤ) :
    c p q = 2 * E p q * (4 * p * q * (p ^ 4 - q ^ 4)) ^ 2 := by
  simp only [c, E]; ring

/-- `(p, q) = (2, 1)` gives Bromhead's edge cuboid `(124, 957, √13852800)`. -/
theorem colmanEdge_two_one :
    ((a 2 1).natAbs, (b 2 1).natAbs, (c 2 1).natAbs) = (124, 957, 13852800) := by
  decide

/-! ### `2E` is never a square -/

theorem sq_emod_four_ne_two (z : ℤ) : z ^ 2 % 4 ≠ 2 := by
  have h0 : 0 ≤ z % 4 := Int.emod_nonneg z (by norm_num)
  have h1 : z % 4 < 4 := Int.emod_lt_of_pos z (by norm_num)
  have : z ^ 2 % 4 = (z % 4) ^ 2 % 4 := by rw [pow_two, pow_two, Int.mul_emod]
  rw [this]
  interval_cases (z % 4) <;> norm_num

theorem sq_emod_sixtyfour_ne (z : ℤ) : z ^ 2 % 64 ≠ 32 := by
  have h0 : 0 ≤ z % 64 := Int.emod_nonneg z (by norm_num)
  have h1 : z % 64 < 64 := Int.emod_lt_of_pos z (by norm_num)
  have : z ^ 2 % 64 = (z % 64) ^ 2 % 64 := by rw [pow_two, pow_two, Int.mul_emod]
  rw [this]
  interval_cases (z % 64) <;> norm_num

theorem colmanEdge_E_odd {p q : ℤ} (hodd : Odd (p + q)) : E p q % 2 = 1 := by
  have h1 : Odd (p ^ 2 + q ^ 2) := by
    have e : p ^ 2 + q ^ 2 = (p + q) ^ 2 - 2 * (p * q) := by ring
    rw [e]
    exact hodd.pow.sub_even (even_two_mul _)
  have h2 : Odd (p ^ 4 + q ^ 4) := by
    have e : p ^ 4 + q ^ 4 = (p ^ 2 + q ^ 2) ^ 2 - 2 * (p ^ 2 * q ^ 2) := by ring
    rw [e]
    exact h1.pow.sub_even (even_two_mul _)
  have e : E p q = (p ^ 4 + q ^ 4) ^ 2 + 2 * (6 * p ^ 4 * q ^ 4) := by simp only [E]; ring
  rw [e]
  exact Int.odd_iff.mp (h2.pow.add_even (even_two_mul _))

theorem colmanEdge_E_mod {p q : ℤ} (hp : p % 2 = 1) (hq : q % 2 = 1) : E p q % 32 = 16 := by
  have hp8 := Pocklington.sq_emod_eight_of_odd hp
  have hq8 := Pocklington.sq_emod_eight_of_odd hq
  obtain ⟨k, hk⟩ : ∃ k, p ^ 2 = 8 * k + 1 := ⟨p ^ 2 / 8, by omega⟩
  obtain ⟨l, hl⟩ : ∃ l, q ^ 2 = 8 * l + 1 := ⟨q ^ 2 / 8, by omega⟩
  have hE : E p q = 32 * (128 * k ^ 4 + 64 * k ^ 3 + 1792 * k ^ 2 * l ^ 2 + 448 * k ^ 2 * l +
      40 * k ^ 2 + 448 * k * l ^ 2 + 112 * k * l + 8 * k + 128 * l ^ 4 + 64 * l ^ 3 +
      40 * l ^ 2 + 8 * l) + 16 := by
    have e : E p q = (p ^ 2) ^ 4 + 14 * (p ^ 2) ^ 2 * (q ^ 2) ^ 2 + (q ^ 2) ^ 4 := by
      simp only [E]; ring
    rw [e, hk, hl]; ring
  omega

theorem two_E_coprime {p q s : ℤ} (hpq : IsCoprime p q) (h : 2 * E p q = s ^ 2) : False := by
  by_cases hodd : Odd (p + q)
  · have := colmanEdge_E_odd hodd
    exact sq_emod_four_ne_two s (by omega)
  · obtain ⟨u, hu⟩ : Even (p + q) := Int.not_odd_iff_even.mp hodd
    have hp : p % 2 = 1 := by
      by_contra hp'
      have h2 := hpq.isUnit_of_dvd' (show (2 : ℤ) ∣ p from ⟨p / 2, by omega⟩)
        (show (2 : ℤ) ∣ q from ⟨u - p / 2, by omega⟩)
      rw [Int.isUnit_iff] at h2
      omega
    have hq : q % 2 = 1 := by omega
    have := colmanEdge_E_mod hp hq
    exact sq_emod_sixtyfour_ne s (by omega)

/-- `2 (p⁸ + 14p⁴q⁴ + q⁸)` is a square only for `p = q = 0`. -/
theorem two_E_ne_sq {p q s : ℤ} (h : 2 * E p q = s ^ 2) : p = 0 ∧ q = 0 := by
  by_contra hpq0
  have hg : 0 < Int.gcd p q := by
    rcases not_and_or.mp hpq0 with h0 | h0
    · exact Int.gcd_pos_of_ne_zero_left q h0
    · exact Int.gcd_pos_of_ne_zero_right p h0
  obtain ⟨g, p', q', hg0, hcop, rfl, rfl⟩ := Int.exists_gcd_one' hg
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
  have e : 2 * E (p' * g) (q' * g) = ((g : ℤ) ^ 4) ^ 2 * (2 * E p' q') := by
    simp only [E]; ring
  rw [e] at h
  obtain ⟨s', rfl⟩ : (g : ℤ) ^ 4 ∣ s := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨_, h.symm⟩
  have h' : 2 * E p' q' = s' ^ 2 :=
    mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero 4 hgz)) (by linear_combination h)
  exact two_E_coprime (Int.isCoprime_iff_gcd_eq_one.mpr hcop) h'

/-- **Colman (1988).** For `p q (p⁴ − q⁴) ≠ 0` the missing edge `√c` of the edge cuboid is
never an integer: `c` is not a square. -/
theorem colmanEdge_c_ne_sq {p q : ℤ} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ^ 4 ≠ q ^ 4) (r : ℤ) :
    c p q ≠ r ^ 2 := by
  intro hr
  rw [colmanEdge_c_eq] at hr
  have hL : 4 * p * q * (p ^ 4 - q ^ 4) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero four_ne_zero hp) hq) (sub_ne_zero.mpr hpq)
  obtain ⟨r', rfl⟩ : 4 * p * q * (p ^ 4 - q ^ 4) ∣ r :=
    (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨2 * E p q, by rw [← hr]; ring⟩
  have h2 : 2 * E p q = r' ^ 2 :=
    mul_left_cancel₀ (pow_ne_zero 2 hL) (by linear_combination hr)
  exact hp (two_E_ne_sq h2).1

/-- **No member of the Bromhead–Colman family is a perfect cuboid**: a perfect cuboid with
edges `|a|`, `|b|` and third edge `e` would need `e² = c`. -/
theorem not_isPerfectCuboid_colmanEdge {p q : ℤ} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ^ 4 ≠ q ^ 4)
    (e : ℕ) (he : (e : ℤ) ^ 2 = c p q) :
    ¬ IsPerfectCuboid (a p q).natAbs (b p q).natAbs e :=
  fun _ ↦ colmanEdge_c_ne_sq hp hq hpq e he.symm

end PerfectCuboid
