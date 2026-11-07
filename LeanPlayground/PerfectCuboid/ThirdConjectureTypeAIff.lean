module

public import LeanPlayground.PerfectCuboid.ThirdConjectureTypeA

/-!
# The third cuboid conjecture: the factor `X² + m²` is equivalent to a type-A box

`ThirdConjectureTypeA.lean` shows that a factor `X² + m²` of Sharipov's third cuboid polynomial
(for a non-exceptional triple) gives a type-A box. This file proves the converse, so that ruling
out the factor `X² + m²` is **exactly** open problem 11 of the README (do type-A boxes exist?).

**Key identity (`sextic_neg_one`).** At `y = −1` the sextic is, up to sign, the type-A equation
written in half-angle tangents:
`f_{a,b,c}(−1) = −[4c²(1−a²)²(1−b²)² − 4b²(1−a²)²(1−c²)² − 4a²(1−b²)²(1−c²)²`
`− ((1−a²)(1−b²)(1−c²))²]`.
With `Y/W = 2a/(1−a²)`, `X/W = 2b/(1−b²)`, `g/W = 2c/(1−c²)` this is
`W⁻² ((1−a²)(1−b²)(1−c²))² (g² − X² − Y² − W²)` (`typeAForm_mul`).

**Converse (`exists_dvd_of_isTypeA`).** For a type-A box `(x, y, z)` with `x² + z² = p²`,
`y² + z² = q²`, `x² + y² + z² = g²`, `x² + y² + 2z² = h²`, the half-angle tangents
`a = y/(z+q)`, `b = x/(z+p)`, `c = g/(z+h)` (or `1/a`, `1/b` in place of `a`, `b`, to avoid the
exceptional cases `ac = b²`, `bc = a²`) satisfy `f_{a,b,c}(−1) = 0`. Clearing denominators and
dividing by common primes gives positive integers `a, b, c, m` with `gcd(a, b, c) = 1`, a
non-exceptional triple, and `X² + m² ∣ cuboidThreePoly a b c`.

**Main theorem (`exists_dvd_iff_exists_isTypeA`).** Some non-exceptional positive coprime triple
has a factor `X² + m²` (`m > 0`) of its third cuboid polynomial if and only if a type-A box exists.
-/

@[expose] public section

namespace PerfectCuboid.ThirdConjecture

open Polynomial

/-! ### The sextic at `y = −1` -/

/-- The type-A equation in half-angle tangents. -/
def typeAForm (a b c : ℚ) : ℚ :=
  4 * c ^ 2 * (1 - a ^ 2) ^ 2 * (1 - b ^ 2) ^ 2 - 4 * b ^ 2 * (1 - a ^ 2) ^ 2 * (1 - c ^ 2) ^ 2
    - 4 * a ^ 2 * (1 - b ^ 2) ^ 2 * (1 - c ^ 2) ^ 2 - ((1 - a ^ 2) * (1 - b ^ 2) * (1 - c ^ 2)) ^ 2

/-- **Key identity.** `f_{a,b,c}(−1)` is minus the type-A form. -/
theorem sextic_neg_one (a b c : ℚ) : sextic a b c (-1) = -typeAForm a b c := by
  unfold sextic typeAForm; ring

/-- The sextic is homogeneous of degree 12 (with `y` of weight 2). -/
theorem sextic_smul (k a b c y : ℚ) :
    sextic (k * a) (k * b) (k * c) (k ^ 2 * y) = k ^ 12 * sextic a b c y := by
  unfold sextic; ring

/-- `excPoly` is homogeneous of degree 17. -/
theorem excPoly_smul (k a b c : ℚ) : excPoly (k * a) (k * b) (k * c) = k ^ 17 * excPoly a b c := by
  unfold excPoly; ring

/-- **Half-angle form.** If `2a/(1−a²) = ±Y/W`, `2b/(1−b²) = ±X/W`, `2c/(1−c²) = ±g/W`, then
`typeAForm a b c · W² = ((1−a²)(1−b²)(1−c²))² (g² − X² − Y² − W²)`. -/
theorem typeAForm_mul {a b c X Y W g : ℚ} (hA : (2 * a * W) ^ 2 = (Y * (1 - a ^ 2)) ^ 2)
    (hB : (2 * b * W) ^ 2 = (X * (1 - b ^ 2)) ^ 2) (hC : (2 * c * W) ^ 2 = (g * (1 - c ^ 2)) ^ 2) :
    typeAForm a b c * W ^ 2 =
      ((1 - a ^ 2) * (1 - b ^ 2) * (1 - c ^ 2)) ^ 2 * (g ^ 2 - X ^ 2 - Y ^ 2 - W ^ 2) := by
  unfold typeAForm
  linear_combination (1 - a ^ 2) ^ 2 * (1 - b ^ 2) ^ 2 * hC
    - (1 - a ^ 2) ^ 2 * (1 - c ^ 2) ^ 2 * hB - (1 - b ^ 2) ^ 2 * (1 - c ^ 2) ^ 2 * hA

/-- The half-angle tangent `t = Y/(W + q)` of a right triangle `Y² + W² = q²` satisfies
`2tW = Y(1 − t²)`. -/
theorem half_angle {Y W q : ℚ} (hq : q ^ 2 = Y ^ 2 + W ^ 2) (h : W + q ≠ 0) :
    2 * (Y / (W + q)) * W = Y * (1 - (Y / (W + q)) ^ 2) := by
  field_simp
  linear_combination (-Y) * hq

/-- The other half-angle tangent `(W + q)/Y = 1/t`, which satisfies `2tW = −Y(1 − t²)`. -/
theorem half_angle_inv {Y W q : ℚ} (hq : q ^ 2 = Y ^ 2 + W ^ 2) (hY : Y ≠ 0) :
    2 * ((W + q) / Y) * W = -(Y * (1 - ((W + q) / Y) ^ 2)) := by
  field_simp
  linear_combination (-1) * hq

/-- A positive triple with `a, b, c` pairwise distinct, `ac ≠ b²` and `bc ≠ a²` is not
exceptional. -/
theorem excPoly_ne_zero_of_pos {a b c : ℚ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (h1 : a * c ≠ b ^ 2) (h2 : b * c ≠ a ^ 2) : excPoly a b c ≠ 0 := by
  have sq_ne {u v : ℚ} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) : u ^ 2 - v ^ 2 ≠ 0 :=
    sub_ne_zero.mpr fun h => huv ((pow_left_inj₀ hu.le hv.le two_ne_zero).mp h)
  unfold excPoly
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero ha.ne' hb.ne') hc.ne') (sq_ne ha hb hab))
    (sq_ne ha hc hac)) (sq_ne hb hc hbc)) (sub_ne_zero.mpr h1)) ?_) (sub_ne_zero.mpr h2)) ?_
  · positivity
  · positivity

/-! ### From a type-A box to a rational root `y = −1` -/

set_option maxHeartbeats 2000000 in
-- many small `nlinarith` calls on order facts
/-- **Converse, rational form.** A type-A box gives a positive non-exceptional rational triple
with `f_{a,b,c}(−1) = 0`. -/
theorem exists_rat_of_isTypeA {x y z : ℕ} (H : Adjacency.IsTypeA x y z) :
    ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧ excPoly a b c ≠ 0 ∧ sextic a b c (-1) = 0 := by
  obtain ⟨p, hp⟩ := H.sq_ac
  obtain ⟨q, hq⟩ := H.sq_bc
  obtain ⟨g, hg⟩ := H.sq_abc
  obtain ⟨h, hh⟩ := H.sq_g_c
  have hx : (0 : ℚ) < x := by exact_mod_cast H.pos_a
  have hy : (0 : ℚ) < y := by exact_mod_cast H.pos_b
  have hz : (0 : ℚ) < z := by exact_mod_cast H.pos_c
  set X : ℚ := (x : ℚ) with hXdef
  set Y : ℚ := (y : ℚ) with hYdef
  set W : ℚ := (z : ℚ) with hWdef
  have hp' : (p : ℚ) ^ 2 = X ^ 2 + W ^ 2 := by
    have : ((x ^ 2 + z ^ 2 : ℕ) : ℚ) = ((p * p : ℕ) : ℚ) := by rw [hp]
    push_cast at this; linear_combination -this
  have hq' : (q : ℚ) ^ 2 = Y ^ 2 + W ^ 2 := by
    have : ((y ^ 2 + z ^ 2 : ℕ) : ℚ) = ((q * q : ℕ) : ℚ) := by rw [hq]
    push_cast at this; linear_combination -this
  have hg' : (g : ℚ) ^ 2 = X ^ 2 + Y ^ 2 + W ^ 2 := by
    have : ((x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ℚ) = ((g * g : ℕ) : ℚ) := by rw [hg]
    push_cast at this; linear_combination -this
  have hh' : (h : ℚ) ^ 2 = X ^ 2 + Y ^ 2 + 2 * W ^ 2 := by
    have : ((x ^ 2 + y ^ 2 + 2 * z ^ 2 : ℕ) : ℚ) = ((h * h : ℕ) : ℚ) := by rw [hh]
    push_cast at this; linear_combination -this
  have hp0 : (0 : ℚ) ≤ p := by positivity
  have hq0 : (0 : ℚ) ≤ q := by positivity
  have hg0 : (0 : ℚ) ≤ g := by positivity
  have hh0 : (0 : ℚ) ≤ h := by positivity
  -- `g² + W² = h²`
  have hgh : (h : ℚ) ^ 2 = g ^ 2 + W ^ 2 := by linear_combination hh' - hg'
  have hpX : X < p := lt_of_pow_lt_pow_left₀ 2 hp0 (by rw [hp']; linarith [pow_pos hz 2])
  have hqY : Y < q := lt_of_pow_lt_pow_left₀ 2 hq0 (by rw [hq']; linarith [pow_pos hz 2])
  have hgpos : 0 < (g : ℚ) := lt_of_pow_lt_pow_left₀ 2 hg0 (by rw [hg']; positivity)
  have hhg : (g : ℚ) < h := lt_of_pow_lt_pow_left₀ 2 hh0 (by rw [hgh]; linarith [pow_pos hz 2])
  -- the half-angle tangents
  obtain ⟨a, ha⟩ : ∃ a : ℚ, a = Y / (W + q) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℚ, b = X / (W + p) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℚ, c = (g : ℚ) / (W + h) := ⟨_, rfl⟩
  have hWq : 0 < W + q := by linarith
  have hWp : 0 < W + p := by linarith
  have hWh : 0 < W + h := by linarith
  have ea := half_angle hq' hWq.ne'
  have eb := half_angle hp' hWp.ne'
  have ec := half_angle hgh hWh.ne'
  rw [← ha] at ea
  rw [← hb] at eb
  rw [← hc] at ec
  have ha0 : 0 < a := ha ▸ div_pos hy hWq
  have hb0 : 0 < b := hb ▸ div_pos hx hWp
  have hc0 : 0 < c := hc ▸ div_pos hgpos hWh
  have ha1 : a < 1 := ha ▸ (div_lt_one hWq).mpr (by linarith)
  have hb1 : b < 1 := hb ▸ (div_lt_one hWp).mpr (by linarith)
  have hc1 : c < 1 := hc ▸ (div_lt_one hWh).mpr (by linarith)
  have hab : a ≠ b := by
    intro hab
    rw [← hab] at eb
    have ha2 : 0 < 1 - a ^ 2 := by nlinarith [mul_lt_mul'' ha1 ha1 ha0.le ha0.le]
    have hXY : X = Y := by
      have : (X - Y) * (1 - a ^ 2) = 0 := by linear_combination ea - eb
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · linarith
    apply PerfectCuboid.CongruentRank.sq_ne_two ((h : ℚ) / p)
    have : (0 : ℚ) < p := by linarith
    rw [div_pow, div_eq_iff (by positivity)]
    rw [hh', hp', hXY]; ring
  have hac : a ≠ c := by
    intro hac
    rw [← hac] at ec
    have ha2 : 0 < 1 - a ^ 2 := by nlinarith [mul_lt_mul'' ha1 ha1 ha0.le ha0.le]
    have : ((g : ℚ) - Y) * (1 - a ^ 2) = 0 := by linear_combination ea - ec
    rcases mul_eq_zero.mp this with h' | h'
    · have hgY : (g : ℚ) = Y := by linarith
      rw [hgY] at hg'
      nlinarith
    · linarith
  have hbc : b ≠ c := by
    intro hbc
    rw [← hbc] at ec
    have hb2 : 0 < 1 - b ^ 2 := by nlinarith [mul_lt_mul'' hb1 hb1 hb0.le hb0.le]
    have : ((g : ℚ) - X) * (1 - b ^ 2) = 0 := by linear_combination eb - ec
    rcases mul_eq_zero.mp this with h' | h'
    · have hgX : (g : ℚ) = X := by linarith
      rw [hgX] at hg'
      nlinarith
    · linarith
  have hW2 : W ^ 2 ≠ 0 := by positivity
  have hsq {t L : ℚ} (e : 2 * t * W = L * (1 - t ^ 2)) :
      (2 * t * W) ^ 2 = (L * (1 - t ^ 2)) ^ 2 := by
    rw [e]
  have hsq' {t L : ℚ} (e : 2 * t * W = -(L * (1 - t ^ 2))) :
      (2 * t * W) ^ 2 = (L * (1 - t ^ 2)) ^ 2 := by
    rw [e]; ring
  have root {a' b' : ℚ} (hA : (2 * a' * W) ^ 2 = (Y * (1 - a' ^ 2)) ^ 2)
      (hB : (2 * b' * W) ^ 2 = (X * (1 - b' ^ 2)) ^ 2) : sextic a' b' c (-1) = 0 := by
    rw [sextic_neg_one, neg_eq_zero]
    have := typeAForm_mul hA hB (hsq ec)
    rw [hg', show (X ^ 2 + Y ^ 2 + W ^ 2 - X ^ 2 - Y ^ 2 - W ^ 2 : ℚ) = 0 by ring,
      mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hW2
  by_cases hcab : c = a * b ^ 2
  · -- use `(a, 1/b, c)`
    have eb' := half_angle_inv hp' hx.ne'
    have hbinv : (W + p) / X = 1 / b := by rw [hb]; field_simp
    rw [hbinv] at eb'
    have hb1' : 1 < 1 / b := by rw [lt_div_iff₀ hb0]; linarith
    refine ⟨a, 1 / b, c, ha0, by positivity, hc0, ?_, root (hsq ea) (hsq' eb')⟩
    refine excPoly_ne_zero_of_pos ha0 (by positivity) hc0 (by intro h'; linarith) hac
      (by intro h'; linarith) ?_ ?_
    · intro h'
      have : a * c < 1 := by nlinarith
      have : 1 < (1 / b) ^ 2 := by nlinarith
      linarith
    · intro h'
      apply hab
      have h'' : c = a ^ 2 * b := by
        field_simp at h'; linear_combination h'
      have : a * b * (b - a) = 0 := by linear_combination h'' - hcab
      rcases mul_eq_zero.mp this with h3 | h3
      · exact absurd h3 (by positivity)
      · linarith
  · -- use `(1/a, b, c)`
    have ea' := half_angle_inv hq' hy.ne'
    have hainv : (W + q) / Y = 1 / a := by rw [ha]; field_simp
    rw [hainv] at ea'
    have ha1' : 1 < 1 / a := by rw [lt_div_iff₀ ha0]; linarith
    refine ⟨1 / a, b, c, by positivity, hb0, hc0, ?_, root (hsq' ea') (hsq eb)⟩
    refine excPoly_ne_zero_of_pos (by positivity) hb0 hc0 (by intro h'; linarith)
      (by intro h'; linarith) hbc ?_ ?_
    · intro h'
      apply hcab
      field_simp at h'; linear_combination h'
    · intro h'
      have : b * c < 1 := by nlinarith
      have : 1 < (1 / a) ^ 2 := by nlinarith
      linarith

/-! ### Integer triples and the factor `X² + m²` -/

/-- The sextic `f_{a,b,c}` as a polynomial over `ℤ`. -/
noncomputable def sexticPoly (a b c : ℤ) : ℤ[X] :=
  X ^ 6 + C (6 * c ^ 2 - 2 * a ^ 2 - 2 * b ^ 2) * X ^ 5
    + C (c ^ 4 + b ^ 4 + a ^ 4 + 4 * a ^ 2 * c ^ 2 + 4 * b ^ 2 * c ^ 2 - 12 * b ^ 2 * a ^ 2)
    * X ^ 4 + C (6 * a ^ 4 * c ^ 2 + 6 * c ^ 2 * b ^ 4 - 8 * a ^ 2 * b ^ 2 * c ^ 2
    - 2 * c ^ 4 * a ^ 2 - 2 * c ^ 4 * b ^ 2 - 2 * a ^ 4 * b ^ 2 - 2 * b ^ 4 * a ^ 2)
    * X ^ 3 + C (4 * c ^ 2 * b ^ 4 * a ^ 2 + 4 * a ^ 4 * c ^ 2 * b ^ 2
    - 12 * c ^ 4 * a ^ 2 * b ^ 2 + c ^ 4 * a ^ 4 + c ^ 4 * b ^ 4 + a ^ 4 * b ^ 4) * X ^ 2
    + C (6 * a ^ 4 * c ^ 2 * b ^ 4 - 2 * c ^ 4 * a ^ 4 * b ^ 2 - 2 * c ^ 4 * a ^ 2 * b ^ 4)
    * X + C (c ^ 4 * a ^ 4 * b ^ 4)

theorem cuboidThreePoly_eq_comp (a b c : ℤ) :
    cuboidThreePoly a b c = (sexticPoly a b c).comp (X ^ 2) := by
  simp only [cuboidThreePoly, sexticPoly, add_comp, mul_comp, pow_comp, X_comp, C_comp]
  ring

theorem eval_sexticPoly (a b c y : ℤ) :
    (((sexticPoly a b c).eval y : ℤ) : ℚ) = sextic a b c y := by
  simp only [sexticPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X, sextic]
  push_cast; ring

/-- A root `y = −m²` of the sextic gives the factor `X² + m²` of the third cuboid polynomial. -/
theorem dvd_of_sextic_eq_zero {a b c m : ℤ} (h : sextic a b c (-(m : ℚ) ^ 2) = 0) :
    X ^ 2 + C (m ^ 2) ∣ cuboidThreePoly a b c := by
  have hroot : (sexticPoly a b c).IsRoot (-m ^ 2) := by
    have := eval_sexticPoly a b c (-m ^ 2)
    push_cast at this
    rw [h] at this
    exact_mod_cast this
  obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  refine ⟨Q.comp (X ^ 2), ?_⟩
  rw [cuboidThreePoly_eq_comp, hQ, mul_comp, sub_comp, X_comp, C_comp, map_neg, sub_neg_eq_add]

/-- **Coprime reduction.** A common prime factor of `a, b, c` in a root `y = −m²` also divides
`m`, so it can be divided out. -/
theorem exists_coprime_of_sextic :
    ∀ (n : ℕ) {a b c m : ℤ}, m.toNat = n → 0 < a → 0 < b → 0 < c → 0 < m →
      excPoly a b c ≠ 0 → sextic a b c (-(m : ℚ) ^ 2) = 0 →
      ∃ a b c m : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < m ∧ Int.gcd a (Int.gcd b c) = 1 ∧
        excPoly a b c ≠ 0 ∧ sextic a b c (-(m : ℚ) ^ 2) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c m hn ha hb hc hm hE h
    by_cases hg : Int.gcd a (Int.gcd b c) = 1
    · exact ⟨a, b, c, m, ha, hb, hc, hm, hg, hE, h⟩
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
    have hpd' : (p : ℤ) ∣ (Int.gcd a (Int.gcd b c) : ℤ) := Int.natCast_dvd_natCast.mpr hpd
    have hpa : (p : ℤ) ∣ a := hpd'.trans (Int.gcd_dvd_left _ _)
    have hpbc : (p : ℤ) ∣ (Int.gcd b c : ℤ) := hpd'.trans (Int.gcd_dvd_right _ _)
    have hpb : (p : ℤ) ∣ b := hpbc.trans (Int.gcd_dvd_left _ _)
    have hpc : (p : ℤ) ∣ c := hpbc.trans (Int.gcd_dvd_right _ _)
    -- `p ∣ m`
    have hZ : (sexticPoly a b c).eval (-m ^ 2) = 0 := by
      have := eval_sexticPoly a b c (-m ^ 2)
      push_cast at this
      rw [h] at this
      exact_mod_cast this
    have hpm : (p : ℤ) ∣ m := by
      have := Fact.mk hp
      have h0 := congrArg (Int.cast : ℤ → ZMod p) hZ
      simp only [sexticPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X] at h0
      push_cast at h0
      rw [(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hpa,
        (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mpr hpb,
        (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mpr hpc] at h0
      have h1 : ((m : ZMod p)) ^ 12 = 0 := by linear_combination h0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp (pow_eq_zero_iff (by norm_num) |>.mp h1)
    obtain ⟨a', rfl⟩ := hpa
    obtain ⟨b', rfl⟩ := hpb
    obtain ⟨c', rfl⟩ := hpc
    obtain ⟨m', rfl⟩ := hpm
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have ha' : 0 < a' := pos_of_mul_pos_right ha hp0.le
    have hb' : 0 < b' := pos_of_mul_pos_right hb hp0.le
    have hc' : 0 < c' := pos_of_mul_pos_right hc hp0.le
    have hm' : 0 < m' := pos_of_mul_pos_right hm hp0.le
    have hpQ : ((p : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
    have hE' : excPoly a' b' c' ≠ 0 := by
      intro h0
      apply hE
      push_cast
      rw [excPoly_smul, h0, mul_zero]
    have h' : sextic a' b' c' (-(m' : ℚ) ^ 2) = 0 := by
      push_cast at h
      rw [show -((p : ℚ) * m') ^ 2 = (p : ℚ) ^ 2 * (-(m' : ℚ) ^ 2) by ring, sextic_smul] at h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (by exact_mod_cast hp0.ne'))
    have hlt : m'.toNat < n := by
      have : m' < (p : ℤ) * m' := by nlinarith
      rw [← hn]; omega
    exact ih _ hlt rfl ha' hb' hc' hm' hE' h'

/-- **Converse.** A type-A box gives a non-exceptional coprime positive triple `(a, b, c)` and
`m > 0` with `X² + m² ∣ cuboidThreePoly a b c`. -/
theorem exists_dvd_of_isTypeA {x y z : ℕ} (H : Adjacency.IsTypeA x y z) :
    ∃ a b c m : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < m ∧ Int.gcd a (Int.gcd b c) = 1 ∧
      excPoly a b c ≠ 0 ∧ X ^ 2 + C (m ^ 2) ∣ cuboidThreePoly a b c := by
  obtain ⟨a, b, c, ha, hb, hc, hE, h⟩ := exists_rat_of_isTypeA H
  set M : ℤ := a.den * b.den * c.den with hM
  have hM0 : (0 : ℤ) < M := by rw [hM]; positivity
  have hMQ : (0 : ℚ) < M := by exact_mod_cast hM0
  obtain ⟨A, hA⟩ := exists_int_mul (x := a) (M := M) ⟨b.den * c.den, by rw [hM]; ring⟩
  obtain ⟨B, hB⟩ := exists_int_mul (x := b) (M := M) ⟨a.den * c.den, by rw [hM]; ring⟩
  obtain ⟨C', hC⟩ := exists_int_mul (x := c) (M := M) ⟨a.den * b.den, by rw [hM]; ring⟩
  have hA0 : 0 < A := by exact_mod_cast (show (0 : ℚ) < A by rw [hA]; positivity)
  have hB0 : 0 < B := by exact_mod_cast (show (0 : ℚ) < B by rw [hB]; positivity)
  have hC0 : 0 < C' := by exact_mod_cast (show (0 : ℚ) < C' by rw [hC]; positivity)
  have hE' : excPoly A B C' ≠ 0 := by
    rw [hA, hB, hC, excPoly_smul]
    exact mul_ne_zero (pow_ne_zero _ hMQ.ne') hE
  have h' : sextic A B C' (-(M : ℚ) ^ 2) = 0 := by
    rw [hA, hB, hC, show -(M : ℚ) ^ 2 = (M : ℚ) ^ 2 * (-1) by ring, sextic_smul, h, mul_zero]
  obtain ⟨a, b, c, m, ha, hb, hc, hm, hg, hE, h⟩ :=
    exists_coprime_of_sextic _ rfl hA0 hB0 hC0 hM0 hE' h'
  exact ⟨a, b, c, m, ha, hb, hc, hm, hg, hE, dvd_of_sextic_eq_zero h⟩

/-- **Main theorem.** Some non-exceptional coprime positive triple `(a, b, c)` has a factor
`X² + m²` (`m > 0`) of its third cuboid polynomial **if and only if** a type-A box exists
(open problem 11 of the README). -/
theorem exists_dvd_iff_exists_isTypeA :
    (∃ a b c m : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < m ∧ Int.gcd a (Int.gcd b c) = 1 ∧
      excPoly a b c ≠ 0 ∧ X ^ 2 + C (m ^ 2) ∣ cuboidThreePoly a b c) ↔
      ∃ x y z : ℕ, Adjacency.IsTypeA x y z := by
  constructor
  · rintro ⟨a, b, c, m, -, -, -, hm, -, hE, h⟩
    exact exists_isTypeA_of_dvd hE hm.ne' h
  · rintro ⟨x, y, z, H⟩
    exact exists_dvd_of_isTypeA H

end PerfectCuboid.ThirdConjecture
