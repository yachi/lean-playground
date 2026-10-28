module

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity

/-!
# `x⁴ ± y⁴ = z²` and `y² = x⁵ − x` over the Gaussian integers

Elementary descent in `ℤ[i]`, following Hilbert's *Zahlbericht*, Satz 169 (see also Najman,
arXiv:1005.1528, and Szabó, *Integers* 4 (2004) A16). Throughout `ω = 1 + i` is the prime above
`2` and `ι = i`; "odd" means "not divisible by `ω`".

* `even_descent`: `x⁴ + s y⁴ = z²` (`s = ±1`) has no coprime solution with `x` odd and `y ≠ 0`
  even. Strong induction on `N(y)`: from `y = ωY` one gets `x² ∓ z = 2A`, `x² ± z = 2B` with
  `(sA)B = Y⁴` and `A, B` coprime, so `sA = η₁a⁴`, `B = η₂b⁴`, `x² = sη₁a⁴ + η₂b⁴`; exactly one
  of `a, b` is even, and reducing mod `2` forces the unit in front of the odd one to be `±1`.
  This gives a smaller solution `(b, a)` or `(a, b)`.
* `quartic_one`: **Hilbert, Satz 169.** `x⁴ ± y⁴ = z²` has only trivial solutions in `ℤ[i]`.
  If `x` and `y` are both odd, the doubling identities
  `(x⁴ + y⁴)⁴ − (2xyz)⁴ = (x⁸ − 6x⁴y⁴ + y⁸)²` and `(x⁴ − y⁴)⁴ + (2xyz)⁴ = (x⁸ + 6x⁴y⁴ + y⁸)²`
  give a solution with one variable even.
* `quartic_i`: `x⁴ − y⁴ = i z²` has only trivial solutions.
* `quartic`: `X⁴ − Y⁴ = u w²` (`u` a unit) forces `X Y w = 0`.
* `genus_two`: `p q (p⁴ − q⁴) = u V²` forces `p = 0`, `q = 0` or `p⁴ = q⁴`. That is, the genus-two
  curve `B : y² = x⁵ − x` and its twist by `i` have only their six Weierstrass points over
  `ℚ(i)`. (The Jacobian of `B` has rank `0` over `ℚ(i)`; this proof avoids it.)

`BeauvilleLambda.lean` applies `genus_two` to perfect cuboids.
-/

@[expose] public section

namespace PerfectCuboid.GaussianQuartic

local notation "G" => GaussianInt

/-- `ω = 1 + i`. -/
def ω : G := ⟨1, 1⟩
/-- `i`. -/
def ι : G := ⟨0, 1⟩

theorem ι_sq : ι ^ 2 = -1 := by ext <;> simp [ι, pow_two]

theorem dvd_iff_re_im (n : ℤ) (a : G) : (n : G) ∣ a ↔ n ∣ a.re ∧ n ∣ a.im := Zsqrtd.intCast_dvd n a

theorem ω_dvd_iff (a : G) : ω ∣ a ↔ 2 ∣ a.re + a.im := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.re, by simp [ω]; ring⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨k, k - a.re⟩, by ext <;> simp [ω]; linarith⟩

theorem two_eq : (2 : G) = -ι * ω ^ 2 := by ext <;> simp [ι, ω, pow_two]

theorem ω_four : ω ^ 4 = -4 := by ext <;> simp [ω, pow_succ]

theorem norm_ω : ω.norm = 2 := by simp [ω, Zsqrtd.norm]

theorem isUnit_iff (u : G) : IsUnit u ↔ u = 1 ∨ u = -1 ∨ u = ι ∨ u = -ι := by
  rw [← Zsqrtd.norm_eq_one_iff' (by norm_num)]
  constructor
  · intro h
    have h' : u.re * u.re + u.im * u.im = 1 := by simpa [Zsqrtd.norm] using h
    have hr' : -1 ≤ u.re ∧ u.re ≤ 1 := by constructor <;> nlinarith
    have hi' : -1 ≤ u.im ∧ u.im ≤ 1 := by constructor <;> nlinarith
    obtain ⟨r, m⟩ := u
    simp only at hr' hi' h' ⊢
    rcases hr' with ⟨h1, h2⟩; rcases hi' with ⟨h3, h4⟩
    interval_cases r <;> interval_cases m <;> simp_all [Zsqrtd.ext_iff, ι]
  · rintro (rfl | rfl | rfl | rfl) <;> rfl

theorem isUnit_ι : IsUnit ι := (isUnit_iff ι).2 (by simp)

theorem unit_pow_four {u : G} (hu : IsUnit u) : u ^ 4 = 1 := by
  rcases (isUnit_iff u).1 hu with rfl | rfl | rfl | rfl <;> rfl

theorem unit_sq {u : G} (hu : IsUnit u) : u ^ 2 = 1 ∨ u ^ 2 = -1 := by
  rcases (isUnit_iff u).1 hu with rfl | rfl | rfl | rfl <;> simp [ι_sq]

theorem not_isUnit_ω : ¬ IsUnit ω := by
  rw [← Zsqrtd.norm_eq_one_iff' (by norm_num), norm_ω]; norm_num

theorem prime_ω : Prime ω := by
  refine Irreducible.prime ⟨not_isUnit_ω, fun a b hab => ?_⟩
  have h := congrArg Zsqrtd.norm hab
  rw [Zsqrtd.norm_mul, norm_ω] at h
  have ha := Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) a
  have hb := Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) b
  rw [← Zsqrtd.norm_eq_one_iff' (by norm_num), ← Zsqrtd.norm_eq_one_iff' (by norm_num)]
  have hb0 : b.norm ≠ 0 := by rintro h0; rw [h0] at h; norm_num at h
  have ha0 : a.norm ≠ 0 := by rintro h0; rw [h0] at h; norm_num at h
  have : a.norm ≤ 2 := by nlinarith [lt_of_le_of_ne hb (Ne.symm hb0)]
  interval_cases hn : a.norm
  · exact absurd rfl ha0
  · exact Or.inl rfl
  · right; linarith

theorem pow_four_re (a : G) : (a ^ 4).re = a.re ^ 4 - 6 * a.re ^ 2 * a.im ^ 2 + a.im ^ 4 := by
  simp [pow_succ]; ring
theorem pow_four_im (a : G) : (a ^ 4).im = 4 * a.re ^ 3 * a.im - 4 * a.re * a.im ^ 3 := by
  simp [pow_succ]; ring
theorem sq_re (a : G) : (a ^ 2).re = a.re ^ 2 - a.im ^ 2 := by simp [pow_succ]; ring
theorem sq_im (a : G) : (a ^ 2).im = 2 * a.re * a.im := by simp [pow_succ]; ring

theorem zmod_dvd {n : ℕ} {x : ℤ} (h : ((x : ℤ) : ZMod n) = 0) : (n : ℤ) ∣ x :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x n).1 h

theorem odd_cast {a : G} (ha : ¬ ω ∣ a) : ((4 * (a.re + a.im) : ℤ) : ZMod 8) ≠ 0 := by
  rw [ω_dvd_iff] at ha
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; omega

theorem eight_dvd_pow_four_sub_one {a : G} (ha : ¬ ω ∣ a) : (8 : G) ∣ a ^ 4 - 1 := by
  have key : ∀ r m : ZMod 8, 4 * (r + m) ≠ 0 →
      r ^ 4 - 6 * r ^ 2 * m ^ 2 + m ^ 4 - 1 = 0 ∧ 4 * r ^ 3 * m - 4 * r * m ^ 3 = 0 := by decide
  obtain ⟨k1, k2⟩ := key a.re a.im (by exact_mod_cast odd_cast ha)
  have : ((8 : ℤ) : G) ∣ a ^ 4 - 1 := by
    rw [dvd_iff_re_im, Zsqrtd.re_sub, Zsqrtd.im_sub, pow_four_re, pow_four_im]
    simp only [Zsqrtd.re_one, Zsqrtd.im_one, sub_zero]
    exact ⟨zmod_dvd (n := 8) (by push_cast; exact k1), zmod_dvd (n := 8) (by push_cast; exact k2)⟩
  simpa using this

theorem two_dvd_sq_sub_one {a : G} (ha : ¬ ω ∣ a) : (2 : G) ∣ a ^ 2 - 1 := by
  have key : ∀ r m : ZMod 8, 4 * (r + m) ≠ 0 →
      4 * (r ^ 2 - m ^ 2 - 1) = 0 ∧ 4 * (2 * r * m) = 0 := by decide
  obtain ⟨k1, k2⟩ := key a.re a.im (by exact_mod_cast odd_cast ha)
  have : ((2 : ℤ) : G) ∣ a ^ 2 - 1 := by
    rw [dvd_iff_re_im, Zsqrtd.re_sub, Zsqrtd.im_sub, sq_re, sq_im]
    simp only [Zsqrtd.re_one, Zsqrtd.im_one, sub_zero]
    have h1 := zmod_dvd (n := 8) (x := 4 * (a.re ^ 2 - a.im ^ 2 - 1)) (by push_cast; exact k1)
    have h2 := zmod_dvd (n := 8) (x := 4 * (2 * a.re * a.im)) (by push_cast; exact k2)
    constructor <;> omega
  simpa using this

theorem two_dvd_sub_one_of_four_dvd {z : G} (h : (4 : G) ∣ z ^ 2 - 1) : (2 : G) ∣ z - 1 := by
  have h' : ((4 : ℤ) : G) ∣ z ^ 2 - 1 := by simpa using h
  rw [dvd_iff_re_im, Zsqrtd.re_sub, Zsqrtd.im_sub, sq_re, sq_im] at h'
  simp only [Zsqrtd.re_one, Zsqrtd.im_one, sub_zero] at h'
  have key : ∀ r m : ZMod 8, 2 * (r ^ 2 - m ^ 2 - 1) = 0 → 2 * (2 * r * m) = 0 →
      4 * (r - 1) = 0 ∧ 4 * m = 0 := by decide
  obtain ⟨d1, d2⟩ := h'
  have e1 : ((2 * (z.re ^ 2 - z.im ^ 2 - 1) : ℤ) : ZMod 8) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
  have e2 : ((2 * (2 * z.re * z.im) : ℤ) : ZMod 8) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
  push_cast at e1 e2
  obtain ⟨k1, k2⟩ := key _ _ e1 e2
  have h1 := zmod_dvd (n := 8) (x := 4 * (z.re - 1)) (by push_cast; exact k1)
  have h2 := zmod_dvd (n := 8) (x := 4 * z.im) (by push_cast; exact k2)
  have : ((2 : ℤ) : G) ∣ z - 1 := by
    rw [dvd_iff_re_im]
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one, sub_zero]
    constructor <;> omega
  simpa using this


/-! ### Divisibility tools -/

theorem not_dvd_of_isCoprime {x y : G} (h : IsCoprime x y) (hx : ω ∣ x) (hy : ω ∣ y) : False :=
  not_isUnit_ω (h.isUnit_of_dvd' hx hy)

theorem dvd_of_sq_dvd_sq {c b : G} (h : c ^ 2 ∣ b ^ 2) : c ∣ b :=
  (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 h

theorem exists_sq_of_mul {c a b : G} (hc : c ≠ 0) (h : c ^ 2 * a = b ^ 2) : ∃ d, a = d ^ 2 := by
  obtain ⟨d, rfl⟩ := dvd_of_sq_dvd_sq ⟨a, h.symm⟩
  refine ⟨d, ?_⟩
  have : c ^ 2 * a = c ^ 2 * d ^ 2 := by rw [h]; ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hc) this

theorem unit_eq_one_of_pow_four {u W Y : G} (hu : IsUnit u) (hW : W ≠ 0) (h : u * W ^ 4 = Y ^ 4) :
    u = 1 := by
  have hd : W ^ 4 ∣ Y ^ 4 := ⟨u, by rw [← h]; ring⟩
  obtain ⟨c, rfl⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff four_ne_zero).1 hd
  have h' : W ^ 4 * u = W ^ 4 * c ^ 4 := by rw [mul_comm, h]; ring
  have hc : u = c ^ 4 := mul_left_cancel₀ (pow_ne_zero 4 hW) h'
  rw [hc, unit_pow_four (isUnit_pow_iff four_ne_zero |>.1 (hc ▸ hu))]

theorem unit_sq_of_sq {u W Y : G} (hu : IsUnit u) (hW : W ≠ 0) (h : u * W ^ 2 = Y ^ 2) :
    u = 1 ∨ u = -1 := by
  have hd : W ^ 2 ∣ Y ^ 2 := ⟨u, by rw [← h]; ring⟩
  obtain ⟨c, rfl⟩ := dvd_of_sq_dvd_sq hd
  have h' : W ^ 2 * u = W ^ 2 * c ^ 2 := by rw [mul_comm, h]; ring
  have hc : u = c ^ 2 := mul_left_cancel₀ (pow_ne_zero 2 hW) h'
  rw [hc]; exact unit_sq (isUnit_pow_iff two_ne_zero |>.1 (hc ▸ hu))

theorem exists_coprime (x y : G) (hy : y ≠ 0) :
    ∃ g x' y', g ≠ 0 ∧ x = g * x' ∧ y = g * y' ∧ IsCoprime x' y' := by
  set g := EuclideanDomain.gcd x y
  have hg : g ≠ 0 := fun h => hy (EuclideanDomain.gcd_eq_zero_iff.1 h).2
  obtain ⟨x', hx⟩ := EuclideanDomain.gcd_dvd_left x y
  obtain ⟨y', hy'⟩ := EuclideanDomain.gcd_dvd_right x y
  refine ⟨g, x', y', hg, hx, hy', EuclideanDomain.gcdA x y, EuclideanDomain.gcdB x y, ?_⟩
  have h := EuclideanDomain.gcd_eq_gcd_ab x y
  refine mul_left_cancel₀ hg ?_
  rw [mul_one]
  calc g * (EuclideanDomain.gcdA x y * x' + EuclideanDomain.gcdB x y * y')
      = (g * x') * EuclideanDomain.gcdA x y + (g * y') * EuclideanDomain.gcdB x y := by ring
    _ = g := by rw [← hx, ← hy']; exact h.symm

/-- Coprime factors of `u • V^k` are units times `k`-th powers. -/
theorem pow_split {a b u V : G} {k : ℕ} (hab : IsCoprime a b) (hu : IsUnit u)
    (h : a * b = u * V ^ k) : ∃ η s, IsUnit η ∧ a = η * s ^ k := by
  obtain ⟨v, rfl⟩ := hu
  have h' : (↑v⁻¹ * a) * b = V ^ k := by
    rw [mul_assoc, h, ← mul_assoc, Units.inv_mul, one_mul]
  have hc : IsCoprime (↑v⁻¹ * a) b := (isCoprime_mul_unit_left_left v⁻¹.isUnit a b).2 hab
  obtain ⟨s, w, hs⟩ := exists_associated_pow_of_mul_eq_pow' hc h'
  refine ⟨v * w, s, (v * w).isUnit, ?_⟩
  have : s ^ k * ↑w = ↑v⁻¹ * a := hs
  calc a = ↑v * (↑v⁻¹ * a) := by rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = ↑v * (s ^ k * ↑w) := by rw [this]
    _ = _ := by ring

/-! ### Unit lemmas -/

theorem two_dvd_iff (a : G) : (2 : G) ∣ a ↔ 2 ∣ a.re ∧ 2 ∣ a.im := by
  simpa using dvd_iff_re_im 2 a

theorem not_two_dvd_add_sub_one {u v : G} (hu : IsUnit u) (hv : IsUnit v) :
    ¬ (2 : G) ∣ u + v - 1 := by
  rw [two_dvd_iff]
  rcases (isUnit_iff u).1 hu with rfl | rfl | rfl | rfl <;>
  rcases (isUnit_iff v).1 hv with rfl | rfl | rfl | rfl <;> norm_num [ι]

theorem eq_one_or_of_two_dvd_sub_one {u : G} (hu : IsUnit u) (h : (2 : G) ∣ u - 1) :
    u = 1 ∨ u = -1 := by
  rw [two_dvd_iff] at h
  rcases (isUnit_iff u).1 hu with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  all_goals norm_num [ι] at h

theorem exists_sq_of_unit_mul {ε x P : G} (hε : ε = 1 ∨ ε = -1) (h : ε * x ^ 2 = P) :
    ∃ z, P = z ^ 2 := by
  rcases hε with rfl | rfl
  · exact ⟨x, by rw [← h]; ring⟩
  · exact ⟨ι * x, by rw [← h, mul_pow, ι_sq]⟩

theorem natAbs_norm_lt {a b Y : G} (hb : b ≠ 0) (hY : Y ≠ 0) (h : (a * b) ^ 4 = Y ^ 4) :
    a.norm.natAbs < (ω * Y).norm.natAbs := by
  have e : (a.norm * b.norm) ^ 4 = Y.norm ^ 4 := by
    have := congrArg Zsqrtd.norm h
    simpa only [pow_succ, pow_zero, one_mul, Zsqrtd.norm_mul] using this
  have na := GaussianInt.norm_nonneg a
  have nb := GaussianInt.norm_pos.2 hb
  have nY := GaussianInt.norm_pos.2 hY
  have e' : a.norm * b.norm = Y.norm :=
    (pow_left_inj₀ (by positivity) nY.le four_ne_zero).1 e
  rw [Zsqrtd.norm_mul, norm_ω]
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt na (by nlinarith)

/-! ### Descent for `x⁴ ± y⁴ = z²` with `y` even -/

theorem even_descent (s : G) (hs : s = 1 ∨ s = -1) (n : ℕ) : ∀ x y z : G, y.norm.natAbs = n →
    ¬ ω ∣ x → ω ∣ y → y ≠ 0 → IsCoprime x y → x ^ 4 + s * y ^ 4 = z ^ 2 → False := by
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsu : IsUnit s := by rcases hs with rfl | rfl <;> simp
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y z hn hx hy hy0 hxy h
  obtain ⟨Y, rfl⟩ := hy
  have hY0 : Y ≠ 0 := by rintro rfl; simp at hy0
  have hy4 : (ω * Y) ^ 4 = -4 * Y ^ 4 := by rw [mul_pow, ω_four]
  obtain ⟨k1, hk1⟩ := eight_dvd_pow_four_sub_one hx
  have h4 : (4 : G) ∣ z ^ 2 - 1 := ⟨2 * k1 - s * Y ^ 4, by linear_combination -h + hk1 + s * hy4⟩
  obtain ⟨k2, hk2⟩ := two_dvd_sub_one_of_four_dvd h4
  obtain ⟨k3, hk3⟩ := two_dvd_sq_sub_one hx
  obtain ⟨A, hA⟩ : (2 : G) ∣ x ^ 2 - z := ⟨k3 - k2, by linear_combination hk3 - hk2⟩
  have hAB : (s * A) * (A + z) = 1 * Y ^ 4 := by
    have : (4 : G) * ((s * A) * (A + z)) = 4 * (1 * Y ^ 4) := by
      linear_combination s * h - s ^ 2 * hy4 + 4 * Y ^ 4 * hs2 - s * (x ^ 2 + z + 2 * A) * hA
    exact mul_left_cancel₀ (by norm_num) this
  -- coprimality of `A` and `B = A + z`
  have hc : IsCoprime (A + (A + z)) ((-4 * s) * (A * (A + z))) := by
    have := (IsCoprime.pow_iff (m := 2) (n := 4) two_pos four_pos).2 hxy
    convert this using 1
    · linear_combination -hA
    · linear_combination (-4 : G) * hAB - hy4
  obtain ⟨u, v, huv⟩ := hc.of_mul_right_right.of_mul_right_left
  have hcop : IsCoprime (s * A) (A + z) :=
    (isCoprime_mul_unit_left_left hsu A _).2 ⟨u + v, u, by linear_combination huv⟩
  obtain ⟨η₁, a, hη₁, ha⟩ := pow_split hcop isUnit_one hAB
  obtain ⟨η₂, b, hη₂, hb⟩ := pow_split hcop.symm isUnit_one (by rw [mul_comm]; exact hAB)
  have hprod : (η₁ * η₂) * (a * b) ^ 4 = Y ^ 4 := by
    linear_combination -(η₂ * b ^ 4) * ha - (s * A) * hb + hAB
  have hab0 : a * b ≠ 0 := by
    rintro h0; rw [h0] at hprod; simp at hprod
    exact hY0 (pow_eq_zero_iff four_ne_zero |>.1 hprod.symm)
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab0
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hab0
  have hη : η₁ * η₂ = 1 := unit_eq_one_of_pow_four (hη₁.mul hη₂) hab0 hprod
  have hab4 : (a * b) ^ 4 = Y ^ 4 := by rw [← hprod, hη, one_mul]
  have hx2 : x ^ 2 = s * η₁ * a ^ 4 + η₂ * b ^ 4 := by
    linear_combination hA + s * ha + hb - A * hs2
  have hcab : IsCoprime a b := by
    rw [ha, hb] at hcop
    exact (IsCoprime.pow_iff four_pos four_pos).1 hcop.of_mul_left_right.of_mul_right_right
  -- one descent step: `x² = μ p⁴ + ν q⁴` with `p` odd, `q` even
  have step : ∀ p q μ ν : G, IsUnit μ → IsUnit ν → μ * ν = s → x ^ 2 = μ * p ^ 4 + ν * q ^ 4 →
      ¬ ω ∣ p → ω ∣ q → q ≠ 0 → IsCoprime p q → q.norm.natAbs < n → False := by
    intro p q μ ν hμ hν hμν hx2' hp hq hq0 hpq hlt
    obtain ⟨q', rfl⟩ := hq
    obtain ⟨k4, hk4⟩ := eight_dvd_pow_four_sub_one hp
    have hq4 : (ω * q') ^ 4 = -4 * q' ^ 4 := by rw [mul_pow, ω_four]
    have h2 : (2 : G) ∣ μ - 1 :=
      ⟨k3 - 4 * μ * k4 + 2 * ν * q' ^ 4, by linear_combination -hx2' + hk3 - μ * hk4 - ν * hq4⟩
    have hμ1 := eq_one_or_of_two_dvd_sub_one hμ h2
    have hμ2 : μ ^ 2 = 1 := by rcases hμ1 with rfl | rfl <;> norm_num
    obtain ⟨z', hz'⟩ := exists_sq_of_unit_mul hμ1
      (by linear_combination μ * hx2' + p ^ 4 * hμ2 + (ω * q') ^ 4 * hμν :
        μ * x ^ 2 = p ^ 4 + s * (ω * q') ^ 4)
    exact ih _ hlt p (ω * q') z' rfl hp (dvd_mul_right _ _) hq0 hpq hz'
  by_cases ha' : ω ∣ a <;> by_cases hb' : ω ∣ b
  · exact not_dvd_of_isCoprime hcab ha' hb'
  · exact step b a η₂ (s * η₁) hη₂ (hsu.mul hη₁) (by linear_combination s * hη)
      (by rw [hx2]; ring) hb' ha' ha0 hcab.symm (hn ▸ natAbs_norm_lt hb0 hY0 hab4)
  · exact step a b (s * η₁) η₂ (hsu.mul hη₁) hη₂ (by linear_combination s * hη) hx2 ha' hb' hb0
      hcab (hn ▸ natAbs_norm_lt ha0 hY0 (by rw [mul_comm]; exact hab4))
  · obtain ⟨k5, hk5⟩ := eight_dvd_pow_four_sub_one ha'
    obtain ⟨k6, hk6⟩ := eight_dvd_pow_four_sub_one hb'
    exact not_two_dvd_add_sub_one (hsu.mul hη₁) hη₂
      ⟨k3 - 4 * s * η₁ * k5 - 4 * η₂ * k6,
        by linear_combination -hx2 + hk3 - s * η₁ * hk5 - η₂ * hk6⟩

/-! ### Reduction to coprime solutions -/

theorem reduce {s u X Y W : G} (hu : IsUnit u) (hY : Y ≠ 0) (h : X ^ 4 + s * Y ^ 4 = u * W ^ 2) :
    ∃ g X' Y' W', g ≠ 0 ∧ X = g * X' ∧ Y = g * Y' ∧ W = g ^ 2 * W' ∧ IsCoprime X' Y' ∧
      X' ^ 4 + s * Y' ^ 4 = u * W' ^ 2 := by
  obtain ⟨g, X', Y', hg, rfl, rfl, hc⟩ := exists_coprime X Y hY
  have hd : (g ^ 2) ^ 2 ∣ W ^ 2 := by
    rw [← hu.dvd_mul_left]
    exact ⟨X' ^ 4 + s * Y' ^ 4, by rw [← h]; ring⟩
  obtain ⟨W', rfl⟩ := dvd_of_sq_dvd_sq hd
  refine ⟨g, X', Y', W', hg, rfl, rfl, rfl, hc, ?_⟩
  refine mul_left_cancel₀ (pow_ne_zero 4 hg) ?_
  linear_combination h

theorem not_ω_dvd_of_dvd {g a : G} (ha : ¬ ω ∣ a) (hg : g ∣ a) : ¬ ω ∣ g :=
  fun h => ha (h.trans hg)

/-- `X⁴ + s Y⁴ = W²` has no solution with `X` odd and `Y ≠ 0` even. -/
theorem no_odd_even (s : G) (hs : s = 1 ∨ s = -1) {X Y W : G} (hX : ¬ ω ∣ X) (hY : ω ∣ Y)
    (hY0 : Y ≠ 0) (h : X ^ 4 + s * Y ^ 4 = W ^ 2) : False := by
  obtain ⟨g, X', Y', W', hg, rfl, rfl, -, hc, h'⟩ :=
    reduce (u := 1) isUnit_one hY0 (by rw [h, one_mul])
  have hg' : ¬ ω ∣ g := not_ω_dvd_of_dvd hX (dvd_mul_right _ _)
  have hY' : ω ∣ Y' := (prime_ω.dvd_or_dvd hY).resolve_left hg'
  exact even_descent s hs _ X' Y' W' rfl (fun h => hX (h.mul_left g)) hY'
    (right_ne_zero_of_mul hY0) hc (by rw [h', one_mul])

theorem not_ω_dvd_one_add_four (m : G) : ¬ ω ∣ 1 + 4 * m := by
  intro h
  have h4 : ω ∣ 4 * m := ⟨-ω ^ 3 * m, by linear_combination m * ω_four⟩
  exact not_isUnit_ω (isUnit_of_dvd_one (by simpa using dvd_sub h h4))

theorem not_four_dvd_two : ¬ (4 : G) ∣ 2 := by
  intro h
  have := (dvd_iff_re_im 4 2).1 (by simpa using h)
  norm_num at this

theorem not_two_dvd_ι_sub_one : ¬ (2 : G) ∣ ι - 1 := by
  rw [two_dvd_iff]; norm_num [ι]

theorem ω_ne_zero : ω ≠ 0 := by
  intro h; simpa [ω] using congrArg Zsqrtd.re h

theorem not_ω_dvd_mul3 {a b c : G} (ha : ¬ ω ∣ a) (hb : ¬ ω ∣ b) (hc : ¬ ω ∣ c) :
    ¬ ω ∣ a * b * c := by
  intro h
  rcases prime_ω.dvd_or_dvd h with h | h
  · rcases prime_ω.dvd_or_dvd h with h | h
    exacts [ha h, hb h]
  · exact hc h

theorem ω_sq : ω ^ 2 = 2 * ι := by ext <;> simp [ι, ω, pow_two]

/-! ### `x⁴ ± y⁴ = z²` -/

/-- Hilbert, *Zahlbericht*, Satz 169: `x⁴ ± y⁴ = z²` has only trivial solutions in `ℤ[i]`. -/
theorem quartic_one (s : G) (hs : s = 1 ∨ s = -1) {x y z : G} (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (h : x ^ 4 + s * y ^ 4 = z ^ 2) : False := by
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨g, x, y, z, hg, rfl, rfl, rfl, hc, h⟩ :=
    reduce (u := 1) isUnit_one hy (by rw [h, one_mul])
  rw [one_mul] at h
  replace hx := right_ne_zero_of_mul hx
  replace hy := right_ne_zero_of_mul hy
  replace hz := right_ne_zero_of_mul hz
  by_cases hy' : ω ∣ y
  · exact no_odd_even s hs (fun hx' => not_dvd_of_isCoprime hc hx' hy') hy' hy h
  by_cases hx' : ω ∣ x
  · obtain ⟨z', hz'⟩ := exists_sq_of_unit_mul hs
      (by linear_combination -s * h + y ^ 4 * hs2 : s * z ^ 2 = y ^ 4 + s * x ^ 4)
    exact no_odd_even s hs hy' hx' hx hz'
  obtain ⟨k1, hk1⟩ := eight_dvd_pow_four_sub_one hx'
  obtain ⟨k2, hk2⟩ := eight_dvd_pow_four_sub_one hy'
  rcases hs with rfl | rfl
  · -- `x⁴ + y⁴ = z²`, both odd
    have hωz : ω ∣ z := prime_ω.dvd_of_dvd_pow (n := 2)
      ⟨-ι * ω * (1 + 4 * (k1 + k2)),
        by linear_combination -h + hk1 + hk2 + (1 + 4 * (k1 + k2)) * two_eq⟩
    obtain ⟨z₁, rfl⟩ := hωz
    have hz₁ : ¬ ω ∣ z₁ := by
      rintro ⟨m, rfl⟩
      exact not_four_dvd_two ⟨-m ^ 2 - 2 * (k1 + k2),
        by linear_combination h - hk1 - hk2 + m ^ 2 * ω_four⟩
    set k := k1 - k2
    have hk : x ^ 4 - y ^ 4 = 8 * k := by linear_combination hk1 - hk2
    have hk0 : k ≠ 0 := by
      intro hk0
      rw [hk0, mul_zero, sub_eq_zero] at hk
      rcases unit_sq_of_sq (u := -ι) (W := ω * x ^ 2) (Y := ω * z₁) (isUnit_ι.neg)
        (mul_ne_zero ω_ne_zero (pow_ne_zero 2 hx))
        (by linear_combination h + hk - x ^ 4 * two_eq)
        with h1 | h1 <;> simp [ι, Zsqrtd.ext_iff] at h1
    have e : (ω ^ 6) ^ 2 * ((x * y * z₁) ^ 4 + 1 * (ω ^ 3 * k) ^ 4) =
        ((x ^ 4) ^ 2 + 6 * x ^ 4 * y ^ 4 + (y ^ 4) ^ 2) ^ 2 := by
      have e1 : (x ^ 4 - y ^ 4) ^ 4 + (2 * x * y * (ω * z₁)) ^ 4 =
          ((x ^ 4) ^ 2 + 6 * x ^ 4 * y ^ 4 + (y ^ 4) ^ 2) ^ 2 := by
        have hz4 : (ω * z₁) ^ 4 = (x ^ 4 + y ^ 4) ^ 2 := by
          rw [show (ω * z₁) ^ 4 = ((ω * z₁) ^ 2) ^ 2 by ring, ← h]; ring
        linear_combination 16 * x ^ 4 * y ^ 4 * hz4
      have r : (ω ^ 6) ^ 2 * ((x * y * z₁) ^ 4 + 1 * (ω ^ 3 * k) ^ 4) =
          (ω ^ 4) ^ 3 * (x * y * z₁) ^ 4 + (ω ^ 4) ^ 6 * k ^ 4 := by ring
      rw [r, ω_four]
      linear_combination e1 - ((x ^ 4 - y ^ 4) ^ 3 + (x ^ 4 - y ^ 4) ^ 2 * (8 * k) +
        (x ^ 4 - y ^ 4) * (8 * k) ^ 2 + (8 * k) ^ 3) * hk - 16 * (x * y) ^ 4 * z₁ ^ 4 * ω_four
    obtain ⟨W, hW⟩ := exists_sq_of_mul (pow_ne_zero 6 ω_ne_zero) e
    exact no_odd_even 1 (Or.inl rfl) (not_ω_dvd_mul3 hx' hy' hz₁) ⟨ω ^ 2 * k, by ring⟩
      (mul_ne_zero (pow_ne_zero 3 ω_ne_zero) hk0) hW
  · -- `x⁴ - y⁴ = z²`, both odd
    have hωz : ω ∣ z := prime_ω.dvd_of_dvd_pow (n := 2)
      ⟨-ι * ω * 4 * (k1 - k2), by linear_combination -h + hk1 - hk2 + 4 * (k1 - k2) * two_eq⟩
    have hX : 2 * (1 + 4 * (k1 + k2)) = x ^ 4 + y ^ 4 := by linear_combination -hk1 - hk2
    have e : (4 : G) ^ 2 * ((1 + 4 * (k1 + k2)) ^ 4 + -1 * (x * y * z) ^ 4) =
        ((x ^ 4) ^ 2 - 6 * x ^ 4 * y ^ 4 + (y ^ 4) ^ 2) ^ 2 := by
      have h16 : (2 * (1 + 4 * (k1 + k2))) ^ 4 = (x ^ 4 + y ^ 4) ^ 4 := by rw [hX]
      have hz4 : z ^ 4 = (x ^ 4 - y ^ 4) ^ 2 := by
        rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, ← h]; ring
      linear_combination h16 - 16 * x ^ 4 * y ^ 4 * hz4
    obtain ⟨W, hW⟩ := exists_sq_of_mul (by norm_num) e
    exact no_odd_even (-1) (Or.inr rfl) (not_ω_dvd_one_add_four _) (dvd_mul_of_dvd_right hωz _)
      (by simp [hx, hy, hz]) hW

/-! ### `x⁴ - y⁴ = i z²` -/

theorem not_two_dvd_one : ¬ (2 : G) ∣ 1 := by
  rw [two_dvd_iff]; norm_num

theorem not_two_dvd_ι_mul_sq_sub_one (W : G) : ¬ (2 : G) ∣ ι * W ^ 2 - 1 := by
  rintro ⟨c, hc⟩
  by_cases hW : ω ∣ W
  · obtain ⟨m, rfl⟩ := hW
    exact not_two_dvd_one
      ⟨-m ^ 2 - c, by linear_combination -hc + ι * m ^ 2 * ω_sq + 2 * m ^ 2 * ι_sq⟩
  · obtain ⟨k, hk⟩ := two_dvd_sq_sub_one hW
    exact not_two_dvd_ι_sub_one ⟨c - ι * k, by linear_combination hc - ι * hk⟩

theorem odd_even_i {X Y W : G} (hX : ¬ ω ∣ X) (hY : ω ∣ Y) (h : X ^ 4 + -1 * Y ^ 4 = ι * W ^ 2) :
    False := by
  obtain ⟨k, hk⟩ := eight_dvd_pow_four_sub_one hX
  obtain ⟨Y₁, rfl⟩ := hY
  exact not_two_dvd_ι_mul_sq_sub_one W
    ⟨4 * k + 2 * Y₁ ^ 4, by linear_combination -h + hk - (Y₁ ^ 4) * ω_four⟩

theorem pow_four_add_ne_zero {a b : G} (hb : b ≠ 0) : a ^ 4 + b ^ 4 ≠ 0 := by
  intro h
  have := unit_eq_one_of_pow_four isUnit_one.neg hb (by linear_combination -h : -1 * b ^ 4 = a ^ 4)
  simp [Zsqrtd.ext_iff] at this

theorem quartic_i {x y w : G} (hx : x ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0)
    (h : x ^ 4 - y ^ 4 = ι * w ^ 2) : False := by
  obtain ⟨g, x, y, w, hg, rfl, rfl, rfl, hc, h⟩ :=
    reduce (s := -1) (X := x) (W := w) isUnit_ι hy (by linear_combination h)
  replace hx := right_ne_zero_of_mul hx
  replace hy := right_ne_zero_of_mul hy
  replace hw := right_ne_zero_of_mul hw
  by_cases hy' : ω ∣ y
  · exact odd_even_i (fun hx' => not_dvd_of_isCoprime hc hx' hy') hy' h
  by_cases hx' : ω ∣ x
  · exact odd_even_i hy' hx' (W := ι * w) (by linear_combination -h - ι * w ^ 2 * ι_sq)
  have hw4 : w ^ 4 = -(x ^ 4 - y ^ 4) ^ 2 := by
    linear_combination (x ^ 4 - y ^ 4 + ι * w ^ 2) * h + w ^ 4 * ι_sq
  have e : (x ^ 4 + y ^ 4) ^ 4 + 1 * (2 * x * y * w) ^ 4 =
      ((x ^ 4) ^ 2 - 6 * x ^ 4 * y ^ 4 + (y ^ 4) ^ 2) ^ 2 := by
    linear_combination 16 * x ^ 4 * y ^ 4 * hw4
  have hY : 2 * x * y * w ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hx) hy) hw
  refine quartic_one 1 (Or.inl rfl) (pow_four_add_ne_zero hy) hY ?_ e
  intro h0
  rw [h0, one_mul] at e
  exact pow_four_add_ne_zero hY (by rw [e]; ring)

/-- `X⁴ - Y⁴ = u w²` (`u` a unit) has only trivial solutions in `ℤ[i]`. -/
theorem quartic {u X Y w : G} (hu : IsUnit u) (h : X ^ 4 - Y ^ 4 = u * w ^ 2) :
    X = 0 ∨ Y = 0 ∨ w = 0 := by
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hX, hY, hw⟩ := hne
  rcases (isUnit_iff u).1 hu with rfl | rfl | rfl | rfl
  · exact quartic_one (-1) (Or.inr rfl) hX hY hw (by linear_combination h)
  · exact quartic_one (-1) (Or.inr rfl) hY hX hw (by linear_combination -h)
  · exact quartic_i hX hY hw h
  · exact quartic_i hY hX hw (by linear_combination -h)

/-! ### The genus-two curve `y² = x⁵ - x` -/

/-- `p q (p⁴ - q⁴) = u V²` (`u` a unit) forces `p = 0`, `q = 0` or `p⁴ = q⁴`: the curve
`y² = x⁵ - x` and its twist by `i` have only their Weierstrass points over `ℚ(i)`. -/
theorem genus_two {u p q V : G} (hu : IsUnit u) (h : p * q * (p ^ 4 - q ^ 4) = u * V ^ 2) :
    p = 0 ∨ q = 0 ∨ p ^ 4 = q ^ 4 := by
  by_cases hq : q = 0
  · exact Or.inr (Or.inl hq)
  obtain ⟨g, p, q, hg, rfl, rfl, hc⟩ := exists_coprime p q hq
  have hd : (g ^ 3) ^ 2 ∣ V ^ 2 := by
    rw [← hu.dvd_mul_left]
    exact ⟨p * q * (p ^ 4 - q ^ 4), by rw [← h]; ring⟩
  obtain ⟨V, rfl⟩ := dvd_of_sq_dvd_sq hd
  have h' : p * (q * (p ^ 4 - q ^ 4)) = u * V ^ 2 :=
    mul_left_cancel₀ (pow_ne_zero 6 hg) (by linear_combination h)
  have hpr : IsCoprime p (p ^ 4 - q ^ 4) := by
    have := ((hc.pow_right (n := 4)).neg_right).add_mul_left_right (p ^ 3)
    convert this using 1; ring
  have hqr : IsCoprime q (p ^ 4 - q ^ 4) := by
    have := (hc.symm.pow_right (n := 4)).add_mul_left_right (-q ^ 3)
    convert this using 1; ring
  obtain ⟨η₁, s, hη₁, hp⟩ := pow_split (hc.mul_right hpr) hu h'
  obtain ⟨η₂, t, hη₂, hq⟩ := pow_split (hc.symm.mul_right hqr) hu
    (by linear_combination h' : q * (p * (p ^ 4 - q ^ 4)) = u * V ^ 2)
  obtain ⟨η₃, w, hη₃, hr⟩ := pow_split (hpr.symm.mul_right hqr.symm) hu
    (by linear_combination h' : (p ^ 4 - q ^ 4) * (p * q) = u * V ^ 2)
  have hr' : (s ^ 2) ^ 4 - (t ^ 2) ^ 4 = η₃ * w ^ 2 := by
    rw [hp, hq, mul_pow, mul_pow, unit_pow_four hη₁, unit_pow_four hη₂, one_mul, one_mul] at hr
    exact hr
  rcases quartic hη₃ hr' with h0 | h0 | h0
  · left; rw [hp, pow_eq_zero_iff two_ne_zero |>.1 h0]; ring
  · right; left; rw [hq, pow_eq_zero_iff two_ne_zero |>.1 h0]; ring
  · right; right
    rw [h0, sq, zero_mul, mul_zero, sub_eq_zero] at hr
    rw [mul_pow, mul_pow, hr]

end PerfectCuboid.GaussianQuartic
