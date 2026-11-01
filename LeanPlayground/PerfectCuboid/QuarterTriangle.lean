module

public import Mathlib
public import LeanPlayground.PerfectCuboid.Basic
public import LeanPlayground.PerfectCuboid.FaceCuboid
public import LeanPlayground.PerfectCuboid.LeechEdge

/-!
# Quarter triangles: the integer side of the quarter condition

Write a positive integer right triangle `(U, V, H)` as `k·(m² − n², 2mn, m² + n²)` with
`k = gcd(U, V)`, `m > n > 0` coprime of opposite parity (`exists_generators`, when `U / k` is
odd). On the congruent-number curve `E_N : Y² = X³ − N²X` the point `Q` with abscissa
`x = −N U/(H + V) = −N(m − n)/(m + n)` (`abscissa_eq`) lies in `U + 2E_N(ℚ)` only if
`−N x` and `−2N(x − N)` are rational squares (`KummerDescent.lean`, `two_smul_add_U`; the
converse is the standard fact `ker κ = 2E_N(ℚ)` of 2-descent, not formalised in this
repository). This file proves the integer theory of that square condition.

## Main results

* `IsQuarterPair m n`: `m`, `m − n`, `m + n` are all squares.
* `quarter_iff` (**Q1**): for coprime opposite-parity `m > n > 0`,
  `(m − n)(m + n) = □ ∧ m(m + n) = □ ↔ IsQuarterPair m n`.
* `quarterX_iff` (**Q5**): `−N x ∈ ℚ²` and `−2N(x − N) ∈ ℚ²` for `x = −N(m − n)/(m + n)` iff
  `IsQuarterPair m n`; triangle level: `quarterTriangle_iff` (`U / k` odd) ⟺ `IsQuarterTriangle`,
  and `quarterX_even_impossible` (`U / k` even: never).
* The other sign cases: `not_isSquare_mul_and_two_mul` (**Q2**: `mn = □` and `2m(m + n) = □`
  never both hold; note that `2m(m + n) = □` alone is possible, `(m, n) = (8, 1)`,
  `two_mul_example`), hence `odd_leg_S_impossible`, `even_leg_U_impossible`, and
  `even_leg_S_iff` (even leg, `S`-translate ⟺ quarter pair; the two `S`-versions use the area
  relation `N s² = k² m n (m² − n²)`).
* `isQuarterPair_iff_exists` (**Q3**): `m = τ²`, `m + n = σ²`, `m − n = δ²`, `σ² + δ² = 2τ²`;
  `IsQuarterPair.double`: the quarter triangle is `((r² − s²)², 4rsτ², τ⁴ + 4r²s²)` with
  `r² + s² = τ²` (the identity only; that this is the `E_N`-double of the triangle `(r, s, τ)`
  is the planner's interpretation, not formalised); `IsQuarterPair.odd_four_dvd`: `m` odd,
  `4 ∣ n`.
* `fermat_two_sq` (**Q4**): `x⁴ + y⁴ = 2z² ⇒ x² = y²` (from `fermat_sub`), hence
  `IsQuarterPair.hyp_not_square` and `IsQuarterTriangle.hyp_not_square`.
* `quarter_T₁_iff` (**Q6**): for a box with `d² = a² + b²`, `e² = a² + c²`, `g² = a² + b² + c²`
  (no `f` needed) and `ag` odd, the condition for `x₁ = −N·ag/(de + bc)` holds iff
  `(ag, bc, de)` is a quarter triangle. `IsQuarterTriangle.forms`: the resulting system
  `ag = k(σδ)²`, `de + bc = kσ⁴`, `de − bc = kδ⁴`, `de + ag = 2kτ⁴`, `σ² + δ² = 2τ²`.
* Example: `(49, 1200, 1201)` (`(m, n) = (25, 24)`, area `6·140²`) is a quarter triangle
  (`isQuarterTriangle_49_1200_1201`); `(5, 4)` is not a quarter pair.

Theorem K (no derived triangle of a perfect cuboid is a quarter triangle) is **not** proved here.
Near-miss check: the degenerate box `(a, b, 0)` gives `bc = 0`, i.e. `n = 0`, which every
statement above excludes through `0 < n` (resp. `0 < V`).
-/

@[expose] public section

namespace PerfectCuboid.Quarter

/-- Generators `m > n > 0` of a primitive triangle; the quarter condition. -/
def IsQuarterPair (m n : ℕ) : Prop := IsSquare m ∧ IsSquare (m - n) ∧ IsSquare (m + n)

/-! ### Squares and coprimality -/

/-- Coprime product squares. -/
theorem isSquare_mul_iff_of_coprime {u v : ℕ} (h : Nat.Coprime u v) :
    IsSquare (u * v) ↔ IsSquare u ∧ IsSquare v := by
  constructor
  · rintro ⟨c, hc⟩
    have hu : IsUnit (gcd u v) := by rw [Nat.isUnit_iff]; exact h
    have hv : IsUnit (gcd v u) := by rw [Nat.isUnit_iff]; exact h.symm
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hu (k := 2) (c := c) (by rw [hc]; ring)
    obtain ⟨e, he⟩ := exists_eq_pow_of_mul_eq_pow hv (k := 2) (c := c)
      (by rw [mul_comm, hc]; ring)
    exact ⟨⟨d, by rw [hd]; ring⟩, ⟨e, by rw [he]; ring⟩⟩
  · rintro ⟨hu, hv⟩
    exact hu.mul hv

/-- For `m = n + t`, coprime with `m + n` odd: the four numbers `t, n + t, 2n + t` are pairwise
coprime (and coprime to `n`). -/
theorem coprime_facts {n t : ℕ} (hcop : Nat.Coprime (n + t) n) (hpar : (2 * n + t) % 2 = 1) :
    Nat.Coprime t (2 * n + t) ∧ Nat.Coprime (n + t) (2 * n + t) ∧ Nat.Coprime t n := by
  have htn : Nat.Coprime t n := by
    have := hcop
    rwa [add_comm, Nat.coprime_add_self_left] at this
  have ht2 : Nat.Coprime t 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  refine ⟨?_, ?_, htn⟩
  · rw [add_comm, Nat.coprime_self_add_right]
    exact Nat.Coprime.mul_right ht2 htn
  · have : 2 * n + t = n + (n + t) := by ring
    rw [this, Nat.coprime_add_self_right]
    exact hcop


/-! ### Q1: the two abscissa squares are the quarter condition -/

/-- **Q1.** For coprime generators `m > n > 0` of opposite parity,
`(m − n)(m + n)` and `m(m + n)` are both squares iff `m`, `m − n`, `m + n` are. -/
theorem quarter_iff {m n : ℕ} (_hn : 0 < n) (hmn : n < m) (hcop : Nat.Coprime m n)
    (hpar : (m + n) % 2 = 1) :
    (IsSquare ((m - n) * (m + n)) ∧ IsSquare (m * (m + n))) ↔ IsQuarterPair m n := by
  obtain ⟨t, rfl⟩ : ∃ t, m = n + t := ⟨m - n, by omega⟩
  have e1 : n + t - n = t := by omega
  have e2 : n + t + n = 2 * n + t := by ring
  rw [e2] at hpar
  obtain ⟨h1, h2, -⟩ := coprime_facts hcop hpar
  unfold IsQuarterPair
  rw [e1, e2, isSquare_mul_iff_of_coprime h1, isSquare_mul_iff_of_coprime h2]
  tauto

/-- The third Kummer-type product `m(m − n)` is then a square as well. -/
theorem IsQuarterPair.sq_sub {m n : ℕ} (h : IsQuarterPair m n) : IsSquare (m * (m - n)) :=
  h.1.mul h.2.1

/-! ### Q2: the impossible sign cases -/

/-- **Q2.** For coprime `m > 0`, `n` with `m + n` odd, `m n` and `2 m (m + n)` are never both
squares. (`2m(m+n)` alone *can* be a square: `(m, n) = (8, 1)` gives `144`, see
`two_mul_example`; the extra square `m n` comes from the area relation, see
`odd_leg_S_impossible`, or from the abscissa itself, see `even_leg_U_impossible`.) -/
theorem not_isSquare_mul_and_two_mul {m n : ℕ} (hcop : Nat.Coprime m n)
    (hpar : (m + n) % 2 = 1) (hm : 0 < m) :
    ¬ (IsSquare (m * n) ∧ IsSquare (2 * m * (m + n))) := by
  rintro ⟨hmn, ⟨c, hc⟩⟩
  obtain ⟨⟨a, rfl⟩, -⟩ := (isSquare_mul_iff_of_coprime hcop).1 hmn
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp at hm
    · exact h
  have hdvd : a ^ 2 ∣ c ^ 2 := ⟨2 * (a * a + n), by rw [sq, sq, ← hc]; ring⟩
  obtain ⟨c', rfl⟩ := (Nat.pow_dvd_pow_iff two_ne_zero).1 hdvd
  have h2 : 2 * (a * a + n) = c' * c' := by
    have : a * a * (2 * (a * a + n)) = a * a * (c' * c') := by nlinarith [hc]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hc2 : 2 ∣ c' := by
    have : 2 ∣ c' * c' := ⟨_, h2.symm⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 this with h | h <;> exact h
  obtain ⟨c'', rfl⟩ := hc2
  have h3 : a * a + n = 2 * (c'' * c'') := by nlinarith
  rw [h3] at hpar
  simp [Nat.mul_mod_right] at hpar

/-- `2 m (m + n)` alone can be a square for coprime opposite-parity generators. -/
theorem two_mul_example : Nat.Coprime 8 1 ∧ IsSquare (2 * 8 * (8 + 1)) :=
  ⟨by norm_num, ⟨12, by norm_num⟩⟩

/-! ### Rational transfer -/

theorem isSquare_sq_mul_iff {r q : ℚ} (hr : r ≠ 0) : IsSquare (r ^ 2 * q) ↔ IsSquare q := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t / r, ?_⟩
    field_simp
    linear_combination ht
  · rintro ⟨t, rfl⟩
    exact ⟨r * t, by ring⟩

/-- **Q5, odd leg.** `U = k(m² − n²)`, `V = 2kmn`, `H = k(m² + n²)` give
`x = −N U/(H + V) = −N (m − n)/(m + n)`. -/
theorem abscissa_eq {N k m n : ℚ} (hk : k ≠ 0) (hmn : m + n ≠ 0) :
    -N * (k * (m ^ 2 - n ^ 2)) / (k * (m ^ 2 + n ^ 2) + 2 * k * m * n) =
      -N * (m - n) / (m + n) := by
  have : k * (m ^ 2 + n ^ 2) + 2 * k * m * n = k * (m + n) ^ 2 := by ring
  rw [this]
  field_simp
  ring

/-- **Q5, even leg.** `U = 2kmn`, `V = k(m² − n²)`, `H = k(m² + n²)` give `x = −N n/m`. -/
theorem abscissa_eq_even {N k m n : ℚ} (hk : k ≠ 0) (hm : m ≠ 0) :
    -N * (2 * k * m * n) / (k * (m ^ 2 + n ^ 2) + k * (m ^ 2 - n ^ 2)) = -N * n / m := by
  have : k * (m ^ 2 + n ^ 2) + k * (m ^ 2 - n ^ 2) = 2 * k * m ^ 2 := by ring
  rw [this]
  field_simp

/-- **Q5 (odd leg, `U`-translate version = brief 1's condition).** With
`x = −N(m − n)/(m + n)`: `−N x ∈ ℚ²` and `−2N(x − N) ∈ ℚ²` iff `(m, n)` is a quarter pair. -/
theorem quarterX_iff {N : ℚ} (hN : N ≠ 0) {m n : ℕ} (hn : 0 < n) (hmn : n < m)
    (hcop : Nat.Coprime m n) (hpar : (m + n) % 2 = 1) :
    (IsSquare (-N * (-N * ((m : ℚ) - n) / (m + n))) ∧
      IsSquare (-2 * N * (-N * ((m : ℚ) - n) / (m + n) - N))) ↔ IsQuarterPair m n := by
  have hp : ((m : ℚ) + n) ≠ 0 := by positivity
  have e1 : -N * (-N * ((m : ℚ) - n) / (m + n)) =
      (N / (m + n)) ^ 2 * (((m - n) * (m + n) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub hmn.le]
    field_simp
  have e2 : -2 * N * (-N * ((m : ℚ) - n) / (m + n) - N) =
      (2 * N / (m + n)) ^ 2 * ((m * (m + n) : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  rw [e1, e2, isSquare_sq_mul_iff (div_ne_zero hN hp),
    isSquare_sq_mul_iff (div_ne_zero (mul_ne_zero two_ne_zero hN) hp),
    Rat.isSquare_natCast_iff, Rat.isSquare_natCast_iff]
  exact quarter_iff hn hmn hcop hpar

/-- **Q5 (odd leg, `S`-translate version).** If `N s² = k² m n (m² − n²)` (the area of the
triangle is `N s²`), then `−x` and `−N(x − N)` are never both squares,
`x = −N(m − n)/(m + n)`: they are `(k(m−n)/s)²·mn` and `(N/(m+n))²·2m(m+n)`. -/
theorem odd_leg_S_impossible {N s k : ℚ} {m n : ℕ} (hs : s ≠ 0) (hk : k ≠ 0) (hn : 0 < n)
    (hmn : n < m) (hcop : Nat.Coprime m n) (hpar : (m + n) % 2 = 1)
    (harea : N * s ^ 2 = k ^ 2 * m * n * ((m : ℚ) ^ 2 - n ^ 2)) :
    ¬ (IsSquare (-(-N * ((m : ℚ) - n) / (m + n))) ∧
      IsSquare (-N * (-N * ((m : ℚ) - n) / (m + n) - N))) := by
  have hp : ((m : ℚ) + n) ≠ 0 := by positivity
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have hd : ((m : ℚ) - n) ≠ 0 := by
    have : (n : ℚ) < m := by exact_mod_cast hmn
    linarith
  have hNe : N = k ^ 2 * m * n * ((m : ℚ) ^ 2 - n ^ 2) / s ^ 2 := by
    field_simp; linarith
  have hN : N ≠ 0 := by
    rw [hNe]
    have : (m : ℚ) ^ 2 - n ^ 2 = (m - n) * (m + n) := by ring
    rw [this]
    have : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    positivity
  have e1 : -(-N * ((m : ℚ) - n) / (m + n)) = (k * (m - n) / s) ^ 2 * ((m * n : ℕ) : ℚ) := by
    rw [hNe]; push_cast; field_simp; ring
  have e2 : -N * (-N * ((m : ℚ) - n) / (m + n) - N) =
      (N / (m + n)) ^ 2 * ((2 * m * (m + n) : ℕ) : ℚ) := by
    push_cast; field_simp; ring
  rw [e1, e2, isSquare_sq_mul_iff (div_ne_zero (mul_ne_zero hk hd) hs),
    isSquare_sq_mul_iff (div_ne_zero hN hp), Rat.isSquare_natCast_iff, Rat.isSquare_natCast_iff]
  exact not_isSquare_mul_and_two_mul hcop hpar (by omega)

/-- **Q5 (even leg, `U`-translate version).** With `x = −N n/m` (even leg `U = 2kmn` in the
numerator), `−N x` and `−2N(x − N)` are never both squares: they are `(N/m)²·mn` and
`(N/m)²·2m(m+n)`. -/
theorem even_leg_U_impossible {N : ℚ} (hN : N ≠ 0) {m n : ℕ} (hm : 0 < m)
    (hcop : Nat.Coprime m n) (hpar : (m + n) % 2 = 1) :
    ¬ (IsSquare (-N * (-N * (n : ℚ) / m)) ∧ IsSquare (-2 * N * (-N * (n : ℚ) / m - N))) := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have e1 : -N * (-N * (n : ℚ) / m) = (N / m) ^ 2 * ((m * n : ℕ) : ℚ) := by
    push_cast; field_simp
  have e2 : -2 * N * (-N * (n : ℚ) / m - N) = (N / m) ^ 2 * ((2 * m * (m + n) : ℕ) : ℚ) := by
    push_cast; field_simp; ring
  rw [e1, e2, isSquare_sq_mul_iff (div_ne_zero hN hm'), isSquare_sq_mul_iff (div_ne_zero hN hm'),
    Rat.isSquare_natCast_iff, Rat.isSquare_natCast_iff]
  exact not_isSquare_mul_and_two_mul hcop hpar hm

/-- **Q5 (even leg, `S`-translate version).** With `x = −N n/m` and the area relation
`N s² = k² m n (m² − n²)`: `−x ∈ ℚ²` and `−N(x − N) ∈ ℚ²` iff `(m, n)` is a quarter pair
(`−x = (kn/s)²·(m−n)(m+n)`, `−N(x − N) = (N/m)²·m(m+n)`). -/
theorem even_leg_S_iff {N s k : ℚ} {m n : ℕ} (hs : s ≠ 0) (hk : k ≠ 0) (hn : 0 < n)
    (hmn : n < m) (hcop : Nat.Coprime m n) (hpar : (m + n) % 2 = 1)
    (harea : N * s ^ 2 = k ^ 2 * m * n * ((m : ℚ) ^ 2 - n ^ 2)) :
    (IsSquare (-(-N * (n : ℚ) / m)) ∧ IsSquare (-N * (-N * (n : ℚ) / m - N))) ↔
      IsQuarterPair m n := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd : ((m : ℚ) - n) ≠ 0 := by
    have : (n : ℚ) < m := by exact_mod_cast hmn
    linarith
  have hp : ((m : ℚ) + n) ≠ 0 := by positivity
  have hNe : N = k ^ 2 * m * n * ((m : ℚ) ^ 2 - n ^ 2) / s ^ 2 := by
    field_simp; linarith
  have hN : N ≠ 0 := by
    rw [hNe]
    have : (m : ℚ) ^ 2 - n ^ 2 = (m - n) * (m + n) := by ring
    rw [this]
    positivity
  have e1 : -(-N * (n : ℚ) / m) = (k * n / s) ^ 2 * (((m - n) * (m + n) : ℕ) : ℚ) := by
    rw [hNe]; push_cast [Nat.cast_sub hmn.le]; field_simp; ring
  have e2 : -N * (-N * (n : ℚ) / m - N) = (N / m) ^ 2 * ((m * (m + n) : ℕ) : ℚ) := by
    push_cast; field_simp; ring
  rw [e1, e2, isSquare_sq_mul_iff (div_ne_zero (mul_ne_zero hk hn') hs),
    isSquare_sq_mul_iff (div_ne_zero hN hm'), Rat.isSquare_natCast_iff, Rat.isSquare_natCast_iff]
  exact quarter_iff hn hmn hcop hpar


/-! ### Q3: parametrisation and the doubling structure -/

/-- **Q3.** `m = τ²`, `m + n = σ²`, `m − n = δ²`, so `σ² + δ² = 2τ²`. -/
theorem isQuarterPair_iff_exists {m n : ℕ} (hmn : n ≤ m) :
    IsQuarterPair m n ↔ ∃ σ δ τ : ℕ, σ ^ 2 + δ ^ 2 = 2 * τ ^ 2 ∧ m = τ ^ 2 ∧ m + n = σ ^ 2 ∧
      m - n = δ ^ 2 := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, ⟨δ, hδ⟩, ⟨σ, hσ⟩⟩
    refine ⟨σ, δ, τ, ?_, by rw [hτ]; ring, by rw [hσ]; ring, by rw [hδ]; ring⟩
    have h1 : σ ^ 2 + δ ^ 2 = (m + n) + (m - n) := by rw [hσ, hδ]; ring
    have h2 : (m + n) + (m - n) = 2 * m := by omega
    rw [h1, h2, hτ]; ring
  · rintro ⟨σ, δ, τ, -, h1, h2, h3⟩
    exact ⟨⟨τ, by rw [h1]; ring⟩, ⟨δ, by rw [h3]; ring⟩, ⟨σ, by rw [h2]; ring⟩⟩

/-- Parities: if `m + n` is odd and `(m, n)` is a quarter pair, then `m` is odd and `4 ∣ n`
(`σ, δ` odd give `σ² ≡ δ² ≡ 1 (mod 8)`, `m + n ≡ m − n ≡ 1 (mod 8)`). -/
theorem IsQuarterPair.odd_four_dvd {m n : ℕ} (h : IsQuarterPair m n) (hmn : n ≤ m)
    (hpar : (m + n) % 2 = 1) : m % 2 = 1 ∧ 4 ∣ n := by
  obtain ⟨σ, δ, τ, -, -, h2, h3⟩ := (isQuarterPair_iff_exists hmn).1 h
  have hσ : σ % 2 = 1 := by
    rcases Nat.even_or_odd σ with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exfalso
      have : m + n = 2 * (2 * u * u) := by rw [h2]; ring
      omega
    · omega
  have hδ : δ % 2 = 1 := by
    rcases Nat.even_or_odd δ with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exfalso
      have : m - n = 2 * (2 * u * u) := by rw [h3]; ring
      omega
    · omega
  obtain ⟨u, rfl⟩ : ∃ u, σ = 2 * u + 1 := ⟨σ / 2, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, δ = 2 * v + 1 := ⟨δ / 2, by omega⟩
  obtain ⟨a, ha⟩ := Nat.even_mul_succ_self u
  obtain ⟨b, hb⟩ := Nat.even_mul_succ_self v
  have e2 : m + n = 8 * a + 1 := by rw [h2]; nlinarith [ha]
  have e3 : m - n = 8 * b + 1 := by rw [h3]; nlinarith [hb]
  constructor
  · omega
  · exact ⟨a - b, by omega⟩

/-- **Q3, doubling.** A quarter pair comes from a smaller Pythagorean triangle `(r, s, τ)`:
`m = τ²`, `n = 2rs`, `m² − n² = (r² − s²)²`, `2mn = 4rsτ²`, `m² + n² = τ⁴ + 4r²s²`,
where `r = (σ + δ)/2`, `s = (σ − δ)/2`. (On paper this says the quarter triangle is the
`E_N`-double of `(r, s, τ)`; only the integer identities are proved here.) -/
theorem IsQuarterPair.double {m n : ℕ} (h : IsQuarterPair m n) (hmn : n ≤ m) :
    ∃ r s τ : ℕ, s ≤ r ∧ r ^ 2 + s ^ 2 = τ ^ 2 ∧ m = τ ^ 2 ∧ n = 2 * r * s ∧
      m ^ 2 - n ^ 2 = (r ^ 2 - s ^ 2) ^ 2 ∧ 2 * m * n = 4 * r * s * τ ^ 2 ∧
      m ^ 2 + n ^ 2 = τ ^ 4 + 4 * r ^ 2 * s ^ 2 := by
  obtain ⟨σ, δ, τ, h1, h2, h3, h4⟩ := (isQuarterPair_iff_exists hmn).1 h
  have hm : m = δ ^ 2 + n := (Nat.sub_eq_iff_eq_add hmn).1 h4
  have hle : δ ≤ σ := by
    have : δ ^ 2 ≤ σ ^ 2 := by omega
    exact (Nat.pow_le_pow_iff_left two_ne_zero).1 this
  have hev : Even (σ - δ) := by
    have h5 : Even (σ ^ 2 + δ ^ 2) := ⟨τ ^ 2, by rw [h1]; ring⟩
    rw [Nat.even_add, Nat.even_pow' two_ne_zero, Nat.even_pow' two_ne_zero] at h5
    rw [Nat.even_sub hle]
    exact h5
  obtain ⟨s, hs⟩ := hev
  have hσ : σ = δ + 2 * s := by omega
  subst hσ
  refine ⟨δ + s, s, τ, by omega, ?_, h2, ?_, ?_, ?_, ?_⟩
  · nlinarith [h1]
  · nlinarith [h3, hm]
  · have hn : n = 2 * (δ + s) * s := by nlinarith [h3, hm]
    have e : (δ + s) ^ 2 - s ^ 2 = δ * (δ + 2 * s) := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e]
    apply Nat.sub_eq_of_eq_add
    rw [hm, hn]; ring
  · have hn : n = 2 * (δ + s) * s := by nlinarith [h3, hm]
    rw [← h2, hn]; ring
  · have hn : n = 2 * (δ + s) * s := by nlinarith [h3, hm]
    have : τ ^ 4 = (τ ^ 2) ^ 2 := by ring
    rw [this, ← h2, hn]; ring

/-! ### Q4: Fermat's `x⁴ + y⁴ = 2z²` -/

theorem pow_four_eq_two_mul_sq {y z : ℤ} (h : y ^ 4 = 2 * z ^ 2) : y = 0 := by
  by_cases hz : z = 0
  · subst hz
    have : y ^ 4 = 0 := by simpa using h
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  · exfalso
    apply PerfectCuboid.sq_ne_two_mul_sq (x := (y ^ 2).natAbs) (Int.natAbs_pos.2 hz)
    have : ((((y ^ 2).natAbs ^ 2 : ℕ)) : ℤ) = ((2 * z.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs, sq_abs]
      linear_combination h
    exact_mod_cast this

/-- **Q4 (Fermat).** `x⁴ + y⁴ = 2z²` forces `x² = y²`: with `X = x² + y²`, `Y = x² − y²`,
`X⁴ − Y⁴ = (4xyz)²`, and `fermat_sub`. -/
theorem fermat_two_sq {x y z : ℤ} (h : x ^ 4 + y ^ 4 = 2 * z ^ 2) : x ^ 2 = y ^ 2 := by
  have key : (x ^ 2 + y ^ 2) ^ 4 - (x ^ 2 - y ^ 2) ^ 4 = (4 * x * y * z) ^ 2 := by
    linear_combination (8 * x ^ 2 * y ^ 2) * h
  rcases PerfectCuboid.fermat_sub key with h1 | h1 | h1
  · have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    rw [hx, hy]
  · linear_combination h1
  · have : x = 0 ∨ y = 0 ∨ z = 0 := by
      rcases mul_eq_zero.1 h1 with h2 | h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · rcases mul_eq_zero.1 h3 with h4 | h4
          · norm_num at h4
          · exact Or.inl h4
        · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr h2)
    rcases this with hx | hy | hz
    · subst hx
      have : y = 0 := pow_four_eq_two_mul_sq (z := z) (by linear_combination h)
      subst this; ring
    · subst hy
      have : x = 0 := pow_four_eq_two_mul_sq (z := z) (by linear_combination h)
      subst this; ring
    · subst hz
      have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2)]
      have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2)]
      rw [hx, hy]

/-- A quarter pair with `n > 0` never has a square hypotenuse `m² + n²`:
`2(m² + n²) = σ⁴ + δ⁴`. -/
theorem IsQuarterPair.hyp_not_square {m n : ℕ} (h : IsQuarterPair m n) (hn : 0 < n)
    (hmn : n < m) : ¬ IsSquare (m ^ 2 + n ^ 2) := by
  rintro ⟨w, hw⟩
  obtain ⟨σ, δ, τ, -, -, h3, h4⟩ := (isQuarterPair_iff_exists hmn.le).1 h
  have hm : m = δ ^ 2 + n := (Nat.sub_eq_iff_eq_add hmn.le).1 h4
  have hz : (σ : ℤ) ^ 4 + (δ : ℤ) ^ 4 = 2 * (w : ℤ) ^ 2 := by
    have e3 : (σ : ℤ) ^ 2 = m + n := by exact_mod_cast h3.symm
    have em : (m : ℤ) = δ ^ 2 + n := by exact_mod_cast hm
    have ew : ((m : ℤ)) ^ 2 + (n : ℤ) ^ 2 = w * w := by exact_mod_cast hw
    have : (σ : ℤ) ^ 4 = ((σ : ℤ) ^ 2) ^ 2 := by ring
    rw [this, e3]
    have : (δ : ℤ) ^ 2 = m - n := by rw [em]; ring
    have h' : (δ : ℤ) ^ 4 = ((δ : ℤ) ^ 2) ^ 2 := by ring
    rw [h', this]
    linear_combination 2 * ew
  have := fermat_two_sq hz
  have e3 : (σ : ℤ) ^ 2 = m + n := by exact_mod_cast h3.symm
  have em : (m : ℤ) = δ ^ 2 + n := by exact_mod_cast hm
  have : (n : ℤ) = 0 := by linarith
  omega


/-! ### Q6: generators of an integer right triangle, and the triangle-level statement -/

/-- Generators of a positive Pythagorean triple `U² + V² = H²` whose reduced leg `U / gcd(U, V)`
is odd: `U = k(m² − n²)`, `V = 2kmn`, `H = k(m² + n²)` with `k = gcd(U, V)`, `m > n > 0` coprime of
opposite parity. -/
theorem exists_generators {U V H : ℕ} (hU : 0 < U) (hV : 0 < V) (h : U ^ 2 + V ^ 2 = H ^ 2)
    (hodd : (U / Nat.gcd U V) % 2 = 1) :
    ∃ m n : ℕ, 0 < n ∧ n < m ∧ Nat.Coprime m n ∧ (m + n) % 2 = 1 ∧
      U = Nat.gcd U V * (m ^ 2 - n ^ 2) ∧ V = Nat.gcd U V * (2 * m * n) ∧
      H = Nat.gcd U V * (m ^ 2 + n ^ 2) := by
  set k := Nat.gcd U V with hk
  have hk0 : 0 < k := Nat.gcd_pos_of_pos_left _ hU
  set u := U / k with hu
  set v := V / k with hv
  have hUu : U = k * u := (Nat.mul_div_cancel' (Nat.gcd_dvd_left U V)).symm
  have hVv : V = k * v := (Nat.mul_div_cancel' (Nat.gcd_dvd_right U V)).symm
  have huv : Nat.Coprime u v := Nat.coprime_div_gcd_div_gcd hk0
  have hkH : k ∣ H := by
    have : k ^ 2 ∣ H ^ 2 := ⟨u ^ 2 + v ^ 2, by rw [← h, hUu, hVv]; ring⟩
    exact (Nat.pow_dvd_pow_iff two_ne_zero).1 this
  obtain ⟨w, hw⟩ := hkH
  have hpy : u ^ 2 + v ^ 2 = w ^ 2 := by
    have : k ^ 2 * (u ^ 2 + v ^ 2) = k ^ 2 * w ^ 2 := by
      rw [← mul_pow, ← hw]; rw [← h, hUu, hVv]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0] at hUu; omega
    · exact h0
  have hv0 : 0 < v := by
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · rw [h0] at hVv; omega
    · exact h0
  have hw0 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · rw [h0] at hpy; nlinarith
    · exact h0
  have hT : PythagoreanTriple (u : ℤ) v w := by
    unfold PythagoreanTriple
    have : ((u ^ 2 + v ^ 2 : ℕ) : ℤ) = ((w ^ 2 : ℕ) : ℤ) := by rw [hpy]
    push_cast at this
    linear_combination this
  have hg : Int.gcd (u : ℤ) (v : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact huv
  have hpar : (u : ℤ) % 2 = 1 := by omega
  obtain ⟨m, n, h1, h2, h3, h4, h5, h6⟩ :=
    PythagoreanTriple.coprime_classification' hT hg hpar (by exact_mod_cast hw0)
  have hmn0 : 0 < m * n := by
    have : (0 : ℤ) < v := by exact_mod_cast hv0
    nlinarith
  have hm0 : 0 < m := by
    rcases lt_or_eq_of_le h6 with h' | h'
    · exact h'
    · rw [← h'] at hmn0; simp at hmn0
  have hn0 : 0 < n := by
    by_contra hc
    push Not at hc
    nlinarith
  lift m to ℕ using h6
  lift n to ℕ using hn0.le
  have hnm : n < m := by
    have : (0 : ℤ) < u := by exact_mod_cast hu0
    have : (n : ℤ) ^ 2 < (m : ℤ) ^ 2 := by linarith
    have : n ^ 2 < m ^ 2 := by exact_mod_cast this
    exact (Nat.pow_lt_pow_iff_left two_ne_zero).1 this
  refine ⟨m, n, by exact_mod_cast hn0, hnm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Int.gcd_natCast_natCast] at h4; exact h4
  · omega
  · rw [hUu]
    congr 1
    have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm.le 2
    have : ((u : ℕ) : ℤ) = ((m ^ 2 - n ^ 2 : ℕ) : ℤ) := by
      rw [h1]; push_cast [Nat.cast_sub hle]; ring
    exact_mod_cast this
  · rw [hVv]
    congr 1
    exact_mod_cast h2
  · rw [hw]
    congr 1
    exact_mod_cast h3

/-- A positive integer right triangle `(U, V, H)` whose generators (`exists_generators`) form a
quarter pair. -/
def IsQuarterTriangle (U V H : ℕ) : Prop :=
  ∃ m n : ℕ, 0 < n ∧ n < m ∧ Nat.Coprime m n ∧ (m + n) % 2 = 1 ∧
    U = Nat.gcd U V * (m ^ 2 - n ^ 2) ∧ V = Nat.gcd U V * (2 * m * n) ∧
    H = Nat.gcd U V * (m ^ 2 + n ^ 2) ∧ IsQuarterPair m n

/-- The abscissa of a triangle in terms of any generator data. -/
theorem abscissa_of_generators {N : ℚ} {U V H k m n : ℕ} (hk : 0 < k) (hnm : n < m)
    (hU : U = k * (m ^ 2 - n ^ 2)) (hV : V = k * (2 * m * n)) (hH : H = k * (m ^ 2 + n ^ 2)) :
    -N * (U : ℚ) / ((H : ℚ) + V) = -N * ((m : ℚ) - n) / (m + n) := by
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm.le 2
  subst hU hV hH
  push_cast [Nat.cast_sub hle]
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hmn : ((m : ℚ) + n) ≠ 0 := by
    have : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
    positivity
  rw [← abscissa_eq (N := N) hk' hmn]
  ring_nf

/-- **Triangle-level Q5/Q6.** For a positive integer right triangle `U² + V² = H²` with
`U / gcd(U, V)` odd and `x = −N U/(H + V)`, `N ≠ 0`: brief 1's condition
`−N x ∈ ℚ²`, `−2N(x − N) ∈ ℚ²` holds iff the triangle is a quarter triangle. -/
theorem quarterTriangle_iff {N : ℚ} (hN : N ≠ 0) {U V H : ℕ} (hU : 0 < U) (hV : 0 < V)
    (h : U ^ 2 + V ^ 2 = H ^ 2) (hodd : (U / Nat.gcd U V) % 2 = 1) :
    (IsSquare (-N * (-N * (U : ℚ) / ((H : ℚ) + V))) ∧
      IsSquare (-2 * N * (-N * (U : ℚ) / ((H : ℚ) + V) - N))) ↔ IsQuarterTriangle U V H := by
  have hk0 : 0 < Nat.gcd U V := Nat.gcd_pos_of_pos_left _ hU
  constructor
  · intro hsq
    obtain ⟨m, n, hn, hnm, hcop, hpar, h1, h2, h3⟩ := exists_generators hU hV h hodd
    rw [abscissa_of_generators hk0 hnm h1 h2 h3] at hsq
    exact ⟨m, n, hn, hnm, hcop, hpar, h1, h2, h3, (quarterX_iff hN hn hnm hcop hpar).1 hsq⟩
  · rintro ⟨m, n, hn, hnm, hcop, hpar, h1, h2, h3, hq⟩
    rw [abscissa_of_generators hk0 hnm h1 h2 h3]
    exact (quarterX_iff hN hn hnm hcop hpar).2 hq

/-- **Triangle-level, even leg.** If `U / gcd(U, V)` is even, brief 1's condition never holds for
`x = −N U/(H + V)`. -/
theorem quarterX_even_impossible {N : ℚ} (hN : N ≠ 0) {U V H : ℕ} (hU : 0 < U) (hV : 0 < V)
    (h : U ^ 2 + V ^ 2 = H ^ 2) (heven : (U / Nat.gcd U V) % 2 = 0) :
    ¬ (IsSquare (-N * (-N * (U : ℚ) / ((H : ℚ) + V))) ∧
      IsSquare (-2 * N * (-N * (U : ℚ) / ((H : ℚ) + V) - N))) := by
  have hk0 : 0 < Nat.gcd U V := Nat.gcd_pos_of_pos_left _ hU
  have hcop : Nat.Coprime (U / Nat.gcd U V) (V / Nat.gcd U V) := Nat.coprime_div_gcd_div_gcd hk0
  have hodd : (V / Nat.gcd V U) % 2 = 1 := by
    rw [Nat.gcd_comm]
    by_contra hc
    have h2 : 2 ∣ Nat.gcd (U / Nat.gcd U V) (V / Nat.gcd U V) :=
      Nat.dvd_gcd (by omega) (by omega)
    rw [hcop] at h2
    omega
  obtain ⟨m, n, hn, hnm, hmn, hpar, h1, h2, h3⟩ :=
    exists_generators hV hU (by rw [← h]; ring) hodd
  rw [Nat.gcd_comm] at h1 h2 h3
  set k := Nat.gcd U V
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hm : 0 < m := by omega
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm.le 2
  have hx : -N * (U : ℚ) / ((H : ℚ) + V) = -N * (n : ℚ) / m := by
    rw [h2, h1, h3]
    push_cast [Nat.cast_sub hle]
    rw [← abscissa_eq_even (N := N) (n := (n : ℚ)) hk' hm']
    ring_nf
  rw [hx]
  exact even_leg_U_impossible hN hm hmn hpar

/-! ### The derived triangle `(ag, bc, de)` of a cuboid -/

/-- `(ag)² + (bc)² = (de)²` from `d² = a² + b²`, `e² = a² + c²`, `g² = a² + b² + c²`
(no `f` needed). -/
theorem derived_pyth {a b c d e g : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) : (a * g) ^ 2 + (b * c) ^ 2 = (d * e) ^ 2 := by
  rw [mul_pow, mul_pow, mul_pow, hd, he, hg]; ring

/-- **Q6.** For a box with integral `d, e, g` (in particular a perfect cuboid) with `a g` odd
(true for a primitive perfect cuboid with `a` the odd edge), brief 1's abscissa condition for the
derived triangle `T₁ = (ag, bc, de)`, `x₁ = −N·ag/(de + bc)`, holds iff `T₁` is a quarter
triangle. -/
theorem quarter_T₁_iff {N : ℚ} (hN : N ≠ 0) {a b c d e g : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) (hodd : Odd (a * g)) :
    (IsSquare (-N * (-N * ((a : ℚ) * g) / ((d : ℚ) * e + b * c))) ∧
      IsSquare (-2 * N * (-N * ((a : ℚ) * g) / ((d : ℚ) * e + b * c) - N))) ↔
      IsQuarterTriangle (a * g) (b * c) (d * e) := by
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0] at hg; nlinarith
    · exact h0
  have hU : 0 < a * g := Nat.mul_pos ha hg0
  have hodd' : (a * g / Nat.gcd (a * g) (b * c)) % 2 = 1 := by
    have hdvd := Nat.gcd_dvd_left (a * g) (b * c)
    have e := Nat.mul_div_cancel' hdvd
    rw [← Nat.odd_iff]
    rw [← e] at hodd
    exact (Nat.odd_mul.1 hodd).2
  have := quarterTriangle_iff hN hU (Nat.mul_pos hb hc) (derived_pyth hd he hg) hodd'
  push_cast at this
  exact this

/-- A quarter triangle with `U > 0` never has a square reduced hypotenuse `H / gcd(U, V)`.
(`U > 0` excludes the empty triangle `(0, 0, 0)`, for which `gcd = 0`.) -/
theorem IsQuarterTriangle.hyp_not_square {U V H : ℕ} (h : IsQuarterTriangle U V H)
    (hU : 0 < U) : ¬ IsSquare (H / Nat.gcd U V) := by
  obtain ⟨m, n, hn, hnm, -, -, -, -, h3, hq⟩ := h
  intro hsq
  rw [h3, Nat.mul_div_cancel_left _ (Nat.gcd_pos_of_pos_left _ hU)] at hsq
  exact hq.hyp_not_square hn hnm hsq

/-- **The quarter system.** For a quarter triangle `(U, V, H)` with `k = gcd(U, V)` there are
`σ, δ, τ` with `σ² + δ² = 2τ²`, `U = k(σδ)²`, `H + V = kσ⁴`, `H = V + kδ⁴`, `H + U = 2kτ⁴`.
For `T₁ = (ag, bc, de)` of a cuboid this is the system of Theorem K:
`ag = k(σδ)²`, `de + bc = kσ⁴`, `de − bc = kδ⁴`, `de + ag = 2kτ⁴`. -/
theorem IsQuarterTriangle.forms {U V H : ℕ} (h : IsQuarterTriangle U V H) :
    ∃ σ δ τ : ℕ, σ ^ 2 + δ ^ 2 = 2 * τ ^ 2 ∧ U = Nat.gcd U V * (σ * δ) ^ 2 ∧
      H + V = Nat.gcd U V * σ ^ 4 ∧ H = V + Nat.gcd U V * δ ^ 4 ∧
      H + U = 2 * Nat.gcd U V * τ ^ 4 := by
  obtain ⟨m, n, -, hnm, -, -, h1, h2, h3, hq⟩ := h
  obtain ⟨σ, δ, τ, e0, e1, e2, e3⟩ := (isQuarterPair_iff_exists hnm.le).1 hq
  have hm : m = δ ^ 2 + n := (Nat.sub_eq_iff_eq_add hnm.le).1 e3
  have hσ : σ ^ 2 = δ ^ 2 + 2 * n := by rw [← e2, hm]; ring
  have hsub : m ^ 2 - n ^ 2 = (σ * δ) ^ 2 := by
    apply Nat.sub_eq_of_eq_add
    rw [mul_pow, hσ, hm]; ring
  set k := Nat.gcd U V
  have hσ4 : σ ^ 4 = (δ ^ 2 + 2 * n) ^ 2 := by rw [← hσ]; ring
  have hτ4 : τ ^ 4 = m ^ 2 := by rw [e1]; ring
  refine ⟨σ, δ, τ, e0, by rw [h1, hsub], ?_, ?_, ?_⟩
  · rw [h3, h2, hσ4, hm]; ring
  · rw [h3, h2, hm]; ring
  · rw [h3, h1, hsub, hτ4, mul_pow, hσ, hm]; ring

/-! ### Examples -/

/-- `(m, n) = (25, 24)`: the triangle `(49, 1200, 1201)` (area `6·140²`) is a quarter triangle. -/
theorem isQuarterTriangle_49_1200_1201 : IsQuarterTriangle 49 1200 1201 :=
  ⟨25, 24, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, ⟨5, by norm_num⟩, ⟨1, by norm_num⟩, ⟨7, by norm_num⟩⟩

/-- `(m, n) = (5, 4)` (triangle `(9, 40, 41)`) is not a quarter pair. -/
theorem not_isQuarterPair_5_4 : ¬ IsQuarterPair 5 4 := by
  rintro ⟨⟨r, hr⟩, -, -⟩
  have : r ≤ 2 := by nlinarith
  interval_cases r <;> omega

end PerfectCuboid.Quarter
