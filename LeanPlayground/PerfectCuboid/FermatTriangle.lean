module

public import Mathlib.NumberTheory.PythagoreanTriples
public import Mathlib.Tactic.LinearCombination

/-!
# Fermat's right triangle theorem

**Theorem (Fermat, c. 1640).** No right triangle with integer sides has an area that is a
perfect square. Equivalently, `1` is not a congruent number: no right triangle with rational
sides has area `1`.

This is the only theorem Fermat proved in full in writing, and the first recorded proof by
infinite descent. Mathlib has the closely related `not_fermat_42` (`a⁴ + b⁴ = c²` has no
nontrivial solution), but not this one, and neither follows from the other in one line.

## Why it matters for perfect cuboids

The fiber-by-fiber attacks on the perfect cuboid problem (Peschmann, arXiv:2604.28072;
Cipollini, arXiv:2609.14526) parametrize a primitive Euler brick by two Pythagorean pairs
`(a, b)` and `(m, n)`. The one step in those papers that is uniform in `(m, n)` is the elimination
of the "infinity class", and it rests on exactly this theorem: the area `mn(m² − n²)` of the
Pythagorean triangle `(m² − n², 2mn, m² + n²)` is never a square
(`not_isSquare_mul_mul_sq_sub_sq`).

## Main results

* `not_isSqAreaTriangle` — the theorem itself, for integers.
* `not_isSquare_mul_mul_sq_sub_sq` — `m n (m² − n²)` is not a square for `0 < n < m`.
* `not_isSquare_sq_add_sq_and_sq_sub_sq` — `a² + b²` and `a² − b²` are not both squares.
* `not_congruent_one` — no right triangle with rational sides has area `1`.

## The descent

Take a primitive triangle `x² + y² = z²` with `x y = 2 s²` and `z` minimal. Euclid's
parametrization gives `x = m² − n²`, `y = 2mn`, so `m n (m − n)(m + n) = s²` with the four factors
pairwise coprime. Hence all four are squares: `m = a²`, `n = b²`, `m + n = c²`, `m − n = d²`.
Then `u = (c + d)/2` and `v = (c − d)/2` are coprime integers with `u² + v² = a²` and
`u v = 2 (b/2)²`: a primitive triangle of the same kind with hypotenuse `a < a² = m < z`.
-/

@[expose] public section

namespace FermatTriangle

/-- A Pythagorean triangle with integer legs `x, y`, hypotenuse `z` and area `s²`: so
`x² + y² = z²` and `x y / 2 = s²`. Fermat's theorem says there is none. -/
def IsSqAreaTriangle (x y z s : ℤ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < s ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ x * y = 2 * s ^ 2

namespace IsSqAreaTriangle

variable {x y z s : ℤ}

theorem swap (h : IsSqAreaTriangle x y z s) : IsSqAreaTriangle y x z s := by
  obtain ⟨hx, hy, hs, h1, h2⟩ := h
  exact ⟨hy, hx, hs, by linear_combination h1, by linear_combination h2⟩

theorem abs_hyp (h : IsSqAreaTriangle x y z s) : IsSqAreaTriangle x y |z| s := by
  obtain ⟨hx, hy, hs, h1, h2⟩ := h
  exact ⟨hx, hy, hs, by rw [sq_abs]; exact h1, h2⟩

theorem hyp_pos (h : IsSqAreaTriangle x y z s) (hz : 0 ≤ z) : 0 < z := by
  obtain ⟨hx, hy, -, h1, -⟩ := h
  rcases hz.lt_or_eq with hz | rfl
  · exact hz
  · nlinarith

end IsSqAreaTriangle

/-! ### Coprime factors of a square are squares -/

/-- If `a b = c²` with `a, b` coprime and `a > 0`, then `a` is the square of a positive integer. -/
theorem exists_sq_eq_of_isCoprime {a b c : ℤ} (h : IsCoprime a b) (heq : a * b = c ^ 2)
    (ha : 0 < a) : ∃ r : ℤ, 0 < r ∧ a = r ^ 2 := by
  obtain ⟨r, hr | hr⟩ := Int.sq_of_isCoprime h heq
  · refine ⟨|r|, abs_pos.mpr ?_, by rw [sq_abs, hr]⟩
    rintro rfl
    simp at hr
    omega
  · nlinarith [sq_nonneg r]

/-- If `a b = c²` with `a, b` coprime and positive, then both are squares. -/
theorem exists_sq_sq_eq_of_isCoprime {a b c : ℤ} (h : IsCoprime a b) (heq : a * b = c ^ 2)
    (ha : 0 < a) (hb : 0 < b) : ∃ r t : ℤ, 0 < r ∧ 0 < t ∧ a = r ^ 2 ∧ b = t ^ 2 := by
  obtain ⟨r, hr, hr'⟩ := exists_sq_eq_of_isCoprime h heq ha
  obtain ⟨t, ht, ht'⟩ := exists_sq_eq_of_isCoprime h.symm (by rw [mul_comm]; exact heq) hb
  exact ⟨r, t, hr, ht, hr', ht'⟩

/-! ### Coprimality of `m, n, m - n, m + n` -/

theorem isCoprime_left_sub {m n : ℤ} (h : IsCoprime m n) : IsCoprime m (m - n) := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨u + v, -v, by linear_combination huv⟩

theorem isCoprime_left_add {m n : ℤ} (h : IsCoprime m n) : IsCoprime m (m + n) := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨u - v, v, by linear_combination huv⟩

theorem isCoprime_right_sub {m n : ℤ} (h : IsCoprime m n) : IsCoprime n (m - n) := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨v + u, u, by linear_combination huv⟩

theorem isCoprime_right_add {m n : ℤ} (h : IsCoprime m n) : IsCoprime n (m + n) := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨v - u, u, by linear_combination huv⟩

/-- For coprime `m, n` of opposite parity, `m - n` and `m + n` are coprime. -/
theorem isCoprime_sub_add_of_odd {m n : ℤ} (h : IsCoprime m n) (hodd : Odd (m - n)) :
    IsCoprime (m - n) (m + n) := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨k, hk⟩ := hodd
  exact ⟨1 - k * (u - v), -(k * (u + v)), by linear_combination (-2 * k) * huv + hk⟩

/-- Coprime `u + v` and `u - v` force coprime `u` and `v`. -/
theorem isCoprime_of_isCoprime_add_sub {u v : ℤ} (h : IsCoprime (u + v) (u - v)) :
    IsCoprime u v := by
  obtain ⟨α, β, hαβ⟩ := h
  exact ⟨α + β, α - β, by linear_combination hαβ⟩

/-! ### The descent step -/

/-- One step of Fermat's descent, for a primitive triangle whose odd leg is `x`. -/
theorem descent_of_odd {x y z s : ℤ} (h : IsSqAreaTriangle x y z s) (hz : 0 < z)
    (hc : IsCoprime x y) (hx : x % 2 = 1) :
    ∃ x' y' z' s', IsSqAreaTriangle x' y' z' s' ∧ 0 < z' ∧ IsCoprime x' y' ∧ z' < z := by
  obtain ⟨hx0, hy0, hs0, h1, h2⟩ := h
  have hpt : PythagoreanTriple x y z := by unfold PythagoreanTriple; linear_combination h1
  obtain ⟨m, n, rfl, rfl, rfl, hmn, hpar, hm0⟩ :=
    hpt.coprime_classification' (Int.isCoprime_iff_gcd_eq_one.mp hc) hx hz
  have hm : 0 < m := by
    rcases hm0.lt_or_eq with hm | rfl
    · exact hm
    · simp at hy0
  have hn : 0 < n := by
    by_contra hn
    rw [not_lt] at hn
    nlinarith
  have hnm : n < m := by
    by_contra hnm
    rw [not_lt] at hnm
    nlinarith
  have hcop : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn
  have hodd : Odd (m - n) := by
    rw [Int.odd_iff]
    rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hprod : m * (n * ((m - n) * (m + n))) = s ^ 2 := by
    have : 2 * (m * (n * ((m - n) * (m + n)))) = 2 * s ^ 2 := by linear_combination h2
    exact mul_left_cancel₀ two_ne_zero this
  have hsub : 0 < m - n := by omega
  have hadd : 0 < m + n := by omega
  -- the four pairwise coprime factors are squares
  have hc1 : IsCoprime m (n * ((m - n) * (m + n))) :=
    hcop.mul_right ((isCoprime_left_sub hcop).mul_right (isCoprime_left_add hcop))
  obtain ⟨a, e, ha, -, ham, hen⟩ := exists_sq_sq_eq_of_isCoprime hc1 hprod hm (by positivity)
  have hc2 : IsCoprime n ((m - n) * (m + n)) :=
    (isCoprime_right_sub hcop).mul_right (isCoprime_right_add hcop)
  obtain ⟨b, f, hb, -, hbn, hf⟩ := exists_sq_sq_eq_of_isCoprime hc2 hen hn (by positivity)
  have hc3 : IsCoprime (m - n) (m + n) := isCoprime_sub_add_of_odd hcop hodd
  obtain ⟨d, c, hd, hc, hdmn, hcmn⟩ := exists_sq_sq_eq_of_isCoprime hc3 hf hsub hadd
  -- `c` and `d` have the same parity, so `u = (c + d)/2` and `v = (c - d)/2` are integers
  have hcd : Even (c + d) := by
    have h2m : Even (c ^ 2 + d ^ 2) := ⟨m, by linear_combination -hcmn - hdmn⟩
    rw [Int.even_add, Int.even_pow' two_ne_zero, Int.even_pow' two_ne_zero] at h2m
    exact Int.even_add.mpr h2m
  obtain ⟨u, hu⟩ := hcd
  obtain ⟨v, rfl⟩ : ∃ v, c = u + v := ⟨c - u, by ring⟩
  obtain rfl : d = u - v := by omega
  have hv : 0 < v := by nlinarith
  have hu0 : 0 < u := by omega
  -- the new triangle
  have hsq : u ^ 2 + v ^ 2 = a ^ 2 := by
    have : 2 * (u ^ 2 + v ^ 2) = 2 * a ^ 2 := by linear_combination -hcmn - hdmn + 2 * ham
    exact mul_left_cancel₀ two_ne_zero this
  have h2uv : 2 * (u * v) = b ^ 2 := by
    have : 2 * (2 * (u * v)) = 2 * b ^ 2 := by linear_combination hdmn - hcmn + 2 * hbn
    exact mul_left_cancel₀ two_ne_zero this
  have hbe : Even b := by
    rw [← Int.even_pow' two_ne_zero, ← h2uv]
    exact even_two_mul _
  obtain ⟨b', rfl⟩ := hbe
  have hb' : 0 < b' := by omega
  have huv : u * v = 2 * b' ^ 2 := by
    have : 2 * (u * v) = 2 * (2 * b' ^ 2) := by linear_combination h2uv
    exact mul_left_cancel₀ two_ne_zero this
  have hcop' : IsCoprime u v := by
    apply isCoprime_of_isCoprime_add_sub
    have := hc3.symm
    rw [hcmn, hdmn] at this
    exact (this.of_isCoprime_of_dvd_left (dvd_pow_self _ two_ne_zero)).of_isCoprime_of_dvd_right
      (dvd_pow_self _ two_ne_zero)
  have hlt : a < m ^ 2 + n ^ 2 := by
    have h1 : a ≤ a ^ 2 := by rw [sq]; exact le_mul_of_one_le_left ha.le (by omega)
    have h2 : m ≤ m ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hm.le (by omega)
    have h3 : 1 ≤ n ^ 2 := by rw [sq]; exact one_le_mul_of_one_le_of_one_le (by omega) (by omega)
    linarith
  exact ⟨u, v, a, b', ⟨hu0, hv, hb', hsq, huv⟩, ha, hcop', hlt⟩

/-- One step of Fermat's descent: a primitive triangle with square area and hypotenuse `z`
gives one with hypotenuse `z' < z`. -/
theorem descent {x y z s : ℤ} (h : IsSqAreaTriangle x y z s) (hz : 0 < z) (hc : IsCoprime x y) :
    ∃ x' y' z' s', IsSqAreaTriangle x' y' z' s' ∧ 0 < z' ∧ IsCoprime x' y' ∧ z' < z := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx
  · rcases Int.emod_two_eq_zero_or_one y with hy | hy
    · exfalso
      have : IsUnit (2 : ℤ) :=
        hc.isUnit_of_dvd' (Int.dvd_of_emod_eq_zero hx) (Int.dvd_of_emod_eq_zero hy)
      rw [Int.isUnit_iff] at this
      omega
    · exact descent_of_odd h.swap hz hc.symm hy
  · exact descent_of_odd h hz hc hx

/-- No primitive triangle with square area: the descent cannot go on forever. -/
theorem not_isSqAreaTriangle_of_isCoprime :
    ∀ (k : ℕ) {x y z s : ℤ}, 0 < z → z ≤ k → IsSqAreaTriangle x y z s → IsCoprime x y → False := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x y z s hz hzk h hc
    obtain ⟨x', y', z', s', h', hz', hc', hlt⟩ := descent h hz hc
    refine ih z'.toNat ?_ hz' (Int.self_le_toNat z') h' hc'
    omega

/-! ### Removing a common factor -/

/-- Dividing a triangle with square area by `gcd (x, y)` gives a primitive one. -/
theorem IsSqAreaTriangle.exists_isCoprime {x y z s : ℤ} (h : IsSqAreaTriangle x y z s) :
    ∃ x' y' z' s', IsSqAreaTriangle x' y' z' s' ∧ IsCoprime x' y' := by
  obtain ⟨hx, hy, hs, h1, h2⟩ := h
  obtain ⟨g, x', y', hg0, hcop, rfl, rfl⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left y hx.ne')
  have hg : (0 : ℤ) < g := by exact_mod_cast hg0
  have hg2 : (g : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hg.ne'
  have hx' : 0 < x' := by
    by_contra hx'
    rw [not_lt] at hx'
    nlinarith
  have hy' : 0 < y' := by
    by_contra hy'
    rw [not_lt] at hy'
    nlinarith
  -- `g ∣ z`
  obtain ⟨z', rfl⟩ : (g : ℤ) ∣ z := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero]
    exact ⟨x' ^ 2 + y' ^ 2, by linear_combination -h1⟩
  have h1' : x' ^ 2 + y' ^ 2 = z' ^ 2 := by
    have : (g : ℤ) ^ 2 * (x' ^ 2 + y' ^ 2) = (g : ℤ) ^ 2 * z' ^ 2 := by linear_combination h1
    exact mul_left_cancel₀ hg2 this
  -- `g ∣ s`, in two steps: `g ∣ 2 s`, and the quotient is even
  obtain ⟨t, ht⟩ : (g : ℤ) ∣ 2 * s := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero]
    exact ⟨2 * (x' * y'), by linear_combination -2 * h2⟩
  have ht2 : t ^ 2 = 2 * (x' * y') := by
    have : (g : ℤ) ^ 2 * t ^ 2 = (g : ℤ) ^ 2 * (2 * (x' * y')) := by
      linear_combination -(2 * s + g * t) * ht - 2 * h2
    exact mul_left_cancel₀ hg2 this
  have hte : Even t := by
    rw [← Int.even_pow' two_ne_zero, ht2]
    exact even_two_mul _
  obtain ⟨t', rfl⟩ := hte
  have hs' : s = g * t' := by
    have : 2 * s = 2 * (g * t') := by linear_combination ht
    exact mul_left_cancel₀ two_ne_zero this
  have hxy : x' * y' = 2 * t' ^ 2 := by
    have : 2 * (x' * y') = 2 * (2 * t' ^ 2) := by linear_combination -ht2
    exact mul_left_cancel₀ two_ne_zero this
  have ht' : 0 < t' := by
    by_contra ht'
    rw [not_lt] at ht'
    nlinarith
  exact ⟨x', y', z', t', ⟨hx', hy', ht', h1', hxy⟩, Int.isCoprime_iff_gcd_eq_one.mpr hcop⟩

/-! ### Fermat's theorem -/

/-- **Fermat's right triangle theorem.** No Pythagorean triangle with integer sides has an area
that is a perfect square. -/
theorem not_isSqAreaTriangle (x y z s : ℤ) : ¬ IsSqAreaTriangle x y z s := by
  intro h
  obtain ⟨x', y', z', s', h', hc⟩ := h.exists_isCoprime
  have h'' := h'.abs_hyp
  exact not_isSqAreaTriangle_of_isCoprime |z'|.toNat (h''.hyp_pos (abs_nonneg _))
    (Int.self_le_toNat _) h'' hc

/-- The area `m n (m² − n²)` of the Pythagorean triangle `(m² − n², 2mn, m² + n²)` is never a
square. This is the form used in the fiber-by-fiber attacks on the perfect cuboid problem. -/
theorem not_isSquare_mul_mul_sq_sub_sq {m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    ¬ IsSquare (m * n * (m ^ 2 - n ^ 2)) := by
  rintro ⟨s, hs⟩
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm.le 2
  have hlt : n ^ 2 < m ^ 2 := Nat.pow_lt_pow_left hnm two_ne_zero
  apply not_isSqAreaTriangle ((m : ℤ) ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2) s
  have hs' : (m : ℤ) * n * (m ^ 2 - n ^ 2) = s * s := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_sub hle]
    exact_mod_cast hs
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hn.trans hnm
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hn
  have hsub : (0 : ℤ) < m ^ 2 - n ^ 2 := by
    have : (n : ℤ) ^ 2 < m ^ 2 := by exact_mod_cast hlt
    linarith
  have hs0 : (0 : ℤ) < s := by
    have : (0 : ℤ) < m * n * (m ^ 2 - n ^ 2) := mul_pos (mul_pos hm0 hn0) hsub
    rw [hs'] at this
    nlinarith
  exact ⟨hsub, mul_pos (mul_pos two_pos hm0) hn0, hs0, by ring, by linear_combination 2 * hs'⟩

/-- `a² + b²` and `a² − b²` are never both squares, for `0 < b < a`. Fermat deduced this from
his right triangle theorem: the triangle with legs `c + d, c − d` has hypotenuse `2a` and
area `b²`. -/
theorem not_isSquare_sq_add_sq_and_sq_sub_sq {a b : ℕ} (hb : 0 < b) (hba : b < a) :
    ¬ (IsSquare (a ^ 2 + b ^ 2) ∧ IsSquare (a ^ 2 - b ^ 2)) := by
  rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
  have hle : b ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hba.le 2
  have hc' : (a : ℤ) ^ 2 + b ^ 2 = c * c := by exact_mod_cast hc
  have hd' : (a : ℤ) ^ 2 - b ^ 2 = d * d := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_sub hle]
    exact_mod_cast hd
  have hcd : (d : ℤ) < c := by
    by_contra h
    rw [not_lt] at h
    have : (c : ℤ) * c ≤ d * d := by
      have h0 : (0 : ℤ) ≤ c := by positivity
      nlinarith
    have : (0 : ℤ) < b := by exact_mod_cast hb
    nlinarith
  apply not_isSqAreaTriangle ((c : ℤ) + d) (c - d) (2 * a) b
  have : (0 : ℤ) ≤ d := by positivity
  have : (0 : ℤ) < b := by exact_mod_cast hb
  exact ⟨by omega, by omega, this, by linear_combination -2 * hc' - 2 * hd',
    by linear_combination -hc' + hd'⟩

/-- **`1` is not a congruent number.** No right triangle with rational sides has area `1`. -/
theorem not_congruent_one : ¬ ∃ x y z : ℚ, 0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ x * y = 2 := by
  rintro ⟨x, y, z, hx, hy, h1, h2⟩
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
  apply not_isSqAreaTriangle (x.num * y.den * z.den) (y.num * x.den * z.den)
    (z.num * x.den * y.den) D
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (0 : ℚ) < x.num * y.den * z.den := by rw [hX]; positivity
    exact_mod_cast this
  · have : (0 : ℚ) < y.num * x.den * z.den := by rw [hY]; positivity
    exact_mod_cast this
  · exact_mod_cast hD0
  · have : ((x.num : ℚ) * y.den * z.den) ^ 2 + ((y.num : ℚ) * x.den * z.den) ^ 2 =
        ((z.num : ℚ) * x.den * y.den) ^ 2 := by
      rw [hX, hY, hZ]; linear_combination (D : ℚ) ^ 2 * h1
    exact_mod_cast this
  · have : ((x.num : ℚ) * y.den * z.den) * ((y.num : ℚ) * x.den * z.den) = 2 * (D : ℚ) ^ 2 := by
      rw [hX, hY]; linear_combination (D : ℚ) ^ 2 * h2
    exact_mod_cast this

end FermatTriangle
