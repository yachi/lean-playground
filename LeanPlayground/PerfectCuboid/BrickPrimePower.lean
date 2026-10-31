module

public import LeanPlayground.PerfectCuboid.EdgePrimePower
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Euler bricks with a prime-power edge: the reduction to one equation, and an exponent gap

Korec (1984) proved that no edge of a *perfect cuboid* is a prime power
(`IsPerfectCuboid.edge_ne_prime_pow`). His proof uses the space diagonal. For *Euler bricks*
(all three face diagonals integral, space diagonal arbitrary) the question is open; numerically
no Euler brick has a prime-power edge (round 10: `p < 500`, `k ≤ 10`; round 11:
`p < 300`, exponents `≤ 12`, and `p = 2` up to exponent `40`). This file reduces the question to a
single two-parameter equation and proves a uniform restriction on the exponents.

## The reduction

If the edge `p ^ k` is the common leg of two right triangles of the brick, the legs are
`2b = p ^ i (p ^ (2(k-i)) - 1)` and `2c = p ^ j (p ^ (2(k-j)) - 1)` (`leg_of_prime_pow`), and
`i ≠ j` (else `f² = 2b²`). Say `i < j`, and put `P = p ^ (2(j-i))`, `Q = p ^ (2(k-j))`. Dividing
`(2b)² + (2c)² = (2f)²` by `p ^ (2i)` gives

  `(E)   (P Q - 1)² + P (Q - 1)² = F²`.

Conversely a solution of `(E)` with `P = p ^ (2m)`, `Q = p ^ (2s)`, `m, s ≥ 1`, gives the Euler
brick
`(p ^ (m+s+1), p (P Q - 1)/2, p ^ (m+1) (Q - 1)/2)`. Hence (`exists_isEulerBrick_prime_pow_iff`)

  *some Euler brick has an edge `p ^ k`  ⟺  `(E)` has a solution with `m, s ≥ 1`.*

(`s = 0`, i.e. `Q = 1`, is the degenerate solution `F = P - 1`: the near-miss `j = k`, a zero leg.)
Multiplying `(E)` by `P + 1` gives the Pell-type form `(P+1) F² = P Y² + (P-1)²`,
`Y = (P+1) Q - 2` (`brickEq_iff_pell`).

## The exponent gap (new)

Put `A = P Q - 1` and `x = F - A > 0`. Then `x (x + 2A) = P (Q - 1)²`, and `2x < Q` because
`P (Q-1)² ≤ Q (P Q - 1)`. Since `p ∤ A`, the prime `p` cannot divide both `x` and `x + 2A` unless
`p = 2`, and in every case `P ∣ 2x` or `P ∣ 2(x + 2A)`.
* If `P ∣ 2x` then `P ≤ 2x < Q`.
* If `P ∣ 2(x + 2A) = 2x + 4PQ - 4` then `P ∣ 2x - 4`; `x = 1` and `x = 2` are impossible
  (`P ∣ 1`, resp. `(Q-1)² = 4Q`), so `P ≤ 2x - 4 < Q`.
Hence `Q > P`, i.e. **`s > m`** for every prime `p` (`BrickEq.lt`).

For odd `p` we push one step further, writing `Q = P R` (now legitimate since `s > m`):
* **Case I** (`x = P α`): cancelling `P`, `2α + 1 = P (α² + 2PRα - PR² + 2R)`, so `2α + 1 = cP` with
  `c` odd. If `c = 1` then `P(P-1) = 2x < PR` gives `R ≥ P`, and then `4(PR-1)²` exceeds
  `(P-1)(P(P-1) + 4P²R - 4)`, contradicting the equation. If `c ≥ 3` then
  `P(3P-1) ≤ 2x < PR`.
* **Case II** (`x = 2 + Pλ`, `λ ≥ 1`): cancelling `P`, `2λ - 1 = P(PR² - 6R - λ² - 2PRλ)`, so
  `2λ - 1 ≥ P` and `4 + P(P+1) ≤ 2x < PR`.
In both cases `R > P`, i.e. **`s > 2m`** (`BrickEq.two_mul_lt`).

In terms of the brick (`IsEulerBrick.prime_pow_exponents`): if an Euler brick has the edge `p ^ k`
and the two triangles on that edge have divisor exponents `i < j` (`d - b = p ^ i`,
`e - c = p ^ j`),
then `k - j > j - i`, and `k - j > 2 (j - i)` when `p` is odd. For `p = 2` also `j - i ≥ 2`
(`BrickEq.two_le_of_two`, a mod-8 argument).

The `p`-adic iteration of Case II continues (`λ ≡ (P+1)/2`, then `λ ≡ (P+1)/2 - 5P/8 (mod P²)`,
…) but each step needs a non-vanishing `p`-adic digit of a fixed `p`-adic number, so it does not
close the problem uniformly; see the round-11 report 5.
-/

@[expose] public section

namespace PerfectCuboid
namespace BrickPrimePower

/-- The brick equation `(E)`: `(P Q - 1)² + P (Q - 1)² = F²` with `P = p ^ (2m)`, `Q = p ^ (2s)`. -/
def BrickEq (p m s : ℕ) : Prop :=
  ∃ F : ℤ, ((p : ℤ) ^ (2 * m) * (p : ℤ) ^ (2 * s) - 1) ^ 2
    + (p : ℤ) ^ (2 * m) * ((p : ℤ) ^ (2 * s) - 1) ^ 2 = F ^ 2

/-! ### Elementary lemmas -/

/-- `x² = 2y²` has no solution with `y > 0`. -/
theorem sq_ne_two_mul_sq {x y : ℕ} (hy : 0 < y) : x ^ 2 ≠ 2 * y ^ 2 := by
  intro h
  have hirr : Irrational √((2 : ℕ) : ℝ) := Nat.Prime.irrational_sqrt Nat.prime_two
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have e : ((2 : ℕ) : ℝ) = ((x : ℝ) / y) ^ 2 := by
    rw [div_pow, eq_div_iff (by positivity)]
    exact_mod_cast h.symm
  exact hirr ⟨(x : ℚ) / y, by rw [e, Real.sqrt_sq (by positivity)]; push_cast; rfl⟩

/-- If `4X = Y²` then `X` is a square. -/
theorem isSquare_of_four_mul {X Y : ℕ} (h : 4 * X = Y ^ 2) : IsSquare X := by
  have h2 : 2 ∣ Y := Nat.prime_two.dvd_of_dvd_pow (n := 2) ⟨2 * X, by rw [← h]; ring⟩
  obtain ⟨Z, rfl⟩ := h2
  exact ⟨Z, by nlinarith⟩

/-- `p ^ a (p ^ n - 1)` is even for `a ≥ 1`. -/
theorem two_dvd_pow_mul_pow_sub_one {p a n : ℕ} (ha : 0 < a) :
    2 ∣ p ^ a * (p ^ n - 1) := by
  rcases Nat.even_or_odd p with he | ho
  · exact Dvd.dvd.mul_right ((he.pow_of_ne_zero ha.ne').two_dvd) _
  · exact Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd (ho.pow) odd_one)) _

theorem four_le_pow {p n : ℕ} (hp : p.Prime) (hn : 0 < n) : (4 : ℤ) ≤ (p : ℤ) ^ (2 * n) := by
  have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  calc (4 : ℤ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (2 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ ≤ (p : ℤ) ^ (2 * n) := pow_le_pow_left₀ (by norm_num) h2 _

/-! ### The core of the gap argument -/

/-- Bounds for `x = F - (PQ - 1)`: `0 < x` and `2x < Q`, together with `x (x + 2A) = P (Q-1)²`. -/
theorem core_bounds {P Q F : ℤ} (hP : 4 ≤ P) (hQ : 4 ≤ Q) (hF : 0 ≤ F)
    (h : (P * Q - 1) ^ 2 + P * (Q - 1) ^ 2 = F ^ 2) :
    0 < F - (P * Q - 1) ∧ 2 * (F - (P * Q - 1)) < Q ∧
      (F - (P * Q - 1)) * ((F - (P * Q - 1)) + 2 * (P * Q - 1)) = P * (Q - 1) ^ 2 := by
  have hA : 0 < P * Q - 1 := by nlinarith
  have hW : 0 < P * (Q - 1) ^ 2 := by
    have : 0 < Q - 1 := by linarith
    positivity
  have heq : (F - (P * Q - 1)) * ((F - (P * Q - 1)) + 2 * (P * Q - 1)) = P * (Q - 1) ^ 2 := by
    linear_combination h.symm
  have hx : 0 < F - (P * Q - 1) := by
    by_contra hc
    have hc := not_lt.mp hc
    nlinarith
  refine ⟨hx, ?_, heq⟩
  by_contra hc
  have hc := not_lt.mp hc
  -- x (x + 2A) ≥ x · 2A ≥ Q A > P (Q-1)²
  have h1 : (F - (P * Q - 1)) * (2 * (P * Q - 1)) ≥ Q * (P * Q - 1) := by nlinarith
  have h2 : Q * (P * Q - 1) > P * (Q - 1) ^ 2 := by nlinarith
  nlinarith

/-- In `x y = p ^ n W` with `y - x = 2A` and `p ∤ A`: `p ^ n ∣ 2x` or `p ^ n ∣ 2y`. -/
theorem pow_dvd_two_mul {p n : ℕ} (hp : p.Prime) {A W x y : ℤ} (hA : ¬ (p : ℤ) ∣ A)
    (hxy : x * y = (p : ℤ) ^ n * W) (hyx : y - x = 2 * A) :
    (p : ℤ) ^ n ∣ 2 * x ∨ (p : ℤ) ^ n ∣ 2 * y := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd : (p : ℤ) ^ n ∣ x * y := ⟨W, hxy⟩
  have cop : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → IsCoprime ((p : ℤ) ^ n) z := fun z hz ↦
    ((Prime.coprime_iff_not_dvd hpZ).2 hz).pow_left
  by_cases hx : (p : ℤ) ∣ x
  · by_cases hy : (p : ℤ) ∣ y
    · have h2A : (p : ℤ) ∣ 2 * A := hyx ▸ dvd_sub hy hx
      rcases hpZ.dvd_or_dvd h2A with h2 | h2
      · have hp2 : p = 2 := by
          have : p ∣ 2 := by exact_mod_cast h2
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
        subst hp2
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        have hA' : y' - x' = A := by push_cast at hyx; linarith
        push_cast at hdvd cop ⊢
        by_cases hy2 : (2 : ℤ) ∣ y'
        · have hx2 : ¬ (2 : ℤ) ∣ x' := fun hx2 ↦ hA (by push_cast; exact hA' ▸ dvd_sub hy2 hx2)
          right
          have h' : (2 : ℤ) ^ n ∣ (2 * (2 * y')) * x' := by
            have : (2 * x') * (2 * y') = (2 * (2 * y')) * x' := by ring
            rwa [this] at hdvd
          exact (cop x' hx2).dvd_of_dvd_mul_right h'
        · left
          have h' : (2 : ℤ) ^ n ∣ (2 * (2 * x')) * y' := by
            have : (2 * x') * (2 * y') = (2 * (2 * x')) * y' := by ring
            rwa [this] at hdvd
          exact (cop y' hy2).dvd_of_dvd_mul_right h'
      · exact absurd h2 hA
    · left
      have := (cop y hy).dvd_of_dvd_mul_right hdvd
      exact Dvd.dvd.mul_left this 2
  · right
    have := (cop x hx).dvd_of_dvd_mul_left hdvd
    exact Dvd.dvd.mul_left this 2

/-- `x = 1` is impossible in `x (x + 2A) = P (Q-1)²` (it would give `P ∣ 1`). -/
theorem x_ne_one {P Q x : ℤ} (hP : 4 ≤ P) (heq : x * (x + 2 * (P * Q - 1)) = P * (Q - 1) ^ 2) :
    x ≠ 1 := by
  rintro rfl
  have h : P ∣ 1 := ⟨2 * Q - (Q - 1) ^ 2, by linear_combination -heq⟩
  have := Int.le_of_dvd one_pos h
  linarith

/-- `x = 2` is impossible in `x (x + 2A) = P (Q-1)²` (it would give `(Q-1)² = 4Q`). -/
theorem x_ne_two {P Q x : ℤ} (hP : 4 ≤ P) (hQ : 4 ≤ Q)
    (heq : x * (x + 2 * (P * Q - 1)) = P * (Q - 1) ^ 2) : x ≠ 2 := by
  rintro rfl
  have h1 : P * ((Q - 1) ^ 2 - 4 * Q) = 0 := by linear_combination -heq
  have h2 : (Q - 1) ^ 2 - 4 * Q = 0 := (mul_eq_zero.mp h1).resolve_left (by positivity)
  have h3 : Q ∣ 1 := ⟨6 - Q, by linear_combination h2⟩
  have := Int.le_of_dvd one_pos h3
  linarith

/-- **The gap, abstractly.** If `P ∣ 2x` or `P ∣ 2(x + 2A)` then `P < Q`. -/
theorem gap_core {P Q x : ℤ} (hP : 4 ≤ P) (hQ : 4 ≤ Q) (hx : 0 < x) (hxQ : 2 * x < Q)
    (heq : x * (x + 2 * (P * Q - 1)) = P * (Q - 1) ^ 2)
    (hd : P ∣ 2 * x ∨ P ∣ 2 * (x + 2 * (P * Q - 1))) : P < Q := by
  rcases hd with hd | hd
  · have := Int.le_of_dvd (by linarith) hd
    linarith
  · have hd' : P ∣ 2 * x - 4 := by
      have : 2 * x - 4 = 2 * (x + 2 * (P * Q - 1)) - P * (4 * Q) := by ring
      rw [this]
      exact dvd_sub hd (dvd_mul_right P _)
    rcases lt_trichotomy (2 * x - 4) 0 with hlt | h0 | hgt
    · exact absurd (by omega : x = 1) (x_ne_one hP heq)
    · exact absurd (by omega : x = 2) (x_ne_two hP hQ heq)
    · have := Int.le_of_dvd hgt hd'
      linarith

/-- **The odd gap, abstractly.** With `Q = P R`, `P` odd, `P ≥ 9`, `P ∣ x` or `P ∣ x + 2A`:
then `P < R`. -/
theorem gap_odd_core {P R x : ℤ} (hP : 9 ≤ P) (hPodd : Odd P) (hx : 0 < x)
    (hxQ : 2 * x < P * R)
    (heq : x * (x + 2 * (P * (P * R) - 1)) = P * (P * R - 1) ^ 2)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2)
    (hd : P ∣ x ∨ P ∣ x + 2 * (P * (P * R) - 1)) : P < R := by
  have hP0 : 0 < P := by linarith
  rcases hd with ⟨α, rfl⟩ | hd
  · -- Case I: `x = P α`
    have h1 : P * (α * (P * α + 2 * (P * (P * R)) - 2) - (P * R - 1) ^ 2) = 0 := by
      linear_combination heq
    have h2 : α * (P * α + 2 * (P * (P * R)) - 2) = (P * R - 1) ^ 2 := by
      have := (mul_eq_zero.mp h1).resolve_left hP0.ne'
      linarith
    set c := α ^ 2 + 2 * P * R * α - P * R ^ 2 + 2 * R with hc
    have h3 : 2 * α + 1 = P * c := by rw [hc]; linear_combination -h2
    have hα : 0 < α := pos_of_mul_pos_right hx hP0.le
    have hc0 : 0 < c := by
      by_contra hneg
      have : P * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hP0.le (not_lt.mp hneg)
      linarith
    obtain ⟨t, ht⟩ := hPodd
    rcases (show c = 1 ∨ c = 2 ∨ 3 ≤ c by omega) with hc1 | hc2 | hc3
    · -- `c = 1`: `P = 2α + 1`, `R ≥ P`, and the equation is violated
      rw [hc1, mul_one] at h3
      have hR : P - 1 < R := by
        have : P * (P - 1) < P * R := by nlinarith
        exact lt_of_mul_lt_mul_left this hP0.le
      have hRt : 0 ≤ R - P := by linarith
      exfalso
      have hα4 : 4 ≤ α := by linarith
      nlinarith [mul_nonneg (mul_nonneg hP0.le hP0.le) hRt, mul_nonneg hP0.le hRt,
        mul_nonneg (mul_nonneg (mul_nonneg hP0.le hP0.le) hRt) hα.le]
    · exfalso
      rw [hc2] at h3
      omega
    · have h4 : P * (3 * P - 1) < P * R := by nlinarith
      have := lt_of_mul_lt_mul_left h4 hP0.le
      linarith
  · -- Case II: `x = 2 + P λ`
    have hd' : P ∣ x - 2 := by
      have : x - 2 = (x + 2 * (P * (P * R) - 1)) - P * (2 * (P * R)) := by ring
      rw [this]
      exact dvd_sub hd (dvd_mul_right P _)
    obtain ⟨l, hl⟩ := hd'
    have hx3 : 2 < x := by omega
    have hl0 : 0 < l := by
      by_contra hneg
      have : P * l ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hP0.le (not_lt.mp hneg)
      linarith
    have hxl : x = 2 + P * l := by linarith
    subst hxl
    have h1 : P * ((2 + P * l) * (l + 2 * P * R) - (P * R - 1) ^ 2) = 0 := by
      linear_combination heq
    have h2 : (2 + P * l) * (l + 2 * P * R) = (P * R - 1) ^ 2 := by
      have := (mul_eq_zero.mp h1).resolve_left hP0.ne'
      linarith
    have h3 : 2 * l - 1 = P * (P * R ^ 2 - 6 * R - l ^ 2 - 2 * P * R * l) := by
      linear_combination h2
    have h4 : P ≤ 2 * l - 1 := Int.le_of_dvd (by omega) ⟨_, h3⟩
    have h5 : P * (P + 1) < P * R := by nlinarith
    have := lt_of_mul_lt_mul_left h5 hP0.le
    linarith

/-! ### The gap theorems for `(E)` -/

/-- `p` does not divide `P Q - 1`. -/
theorem not_dvd_pred {p m s : ℕ} (hp : p.Prime) (hm : 0 < m) :
    ¬ (p : ℤ) ∣ (p : ℤ) ^ (2 * m) * (p : ℤ) ^ (2 * s) - 1 := by
  intro h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h1 : (p : ℤ) ∣ (p : ℤ) ^ (2 * m) * (p : ℤ) ^ (2 * s) :=
    Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
  have h2 := dvd_sub h1 h
  rw [sub_sub_cancel] at h2
  exact hpZ.not_dvd_one h2

/-- **Exponent gap.** In every solution of `(E)` with `m, s ≥ 1` we have `s > m`, i.e. `Q > P`.
Valid for every prime `p`, including `p = 2`. -/
theorem BrickEq.lt {p m s : ℕ} (hp : p.Prime) (hm : 0 < m) (hs : 0 < s) (h : BrickEq p m s) :
    m < s := by
  obtain ⟨F, hF⟩ := h
  have hP := four_le_pow hp hm
  have hQ := four_le_pow hp hs
  have hF' : ((p : ℤ) ^ (2 * m) * (p : ℤ) ^ (2 * s) - 1) ^ 2
      + (p : ℤ) ^ (2 * m) * ((p : ℤ) ^ (2 * s) - 1) ^ 2 = |F| ^ 2 := by rw [sq_abs]; exact hF
  obtain ⟨hx, hxQ, heq⟩ := core_bounds hP hQ (abs_nonneg F) hF'
  have hd := pow_dvd_two_mul hp (not_dvd_pred hp hm (s := s)) heq (by ring)
  have hPQ := gap_core hP hQ hx hxQ heq hd
  have := (pow_lt_pow_iff_right₀ (by exact_mod_cast hp.one_lt : (1 : ℤ) < p)).1 hPQ
  omega

/-- **Odd exponent gap.** For an odd prime `p`, every solution of `(E)` with `m, s ≥ 1` has
`s > 2m`, i.e. `Q > P²`. -/
theorem BrickEq.two_mul_lt {p m s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 0 < m) (hs : 0 < s)
    (h : BrickEq p m s) : 2 * m < s := by
  have hms := h.lt hp hm hs
  obtain ⟨F, hF⟩ := h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hP := four_le_pow hp hm
  have hQ := four_le_pow hp hs
  have hF' : ((p : ℤ) ^ (2 * m) * (p : ℤ) ^ (2 * s) - 1) ^ 2
      + (p : ℤ) ^ (2 * m) * ((p : ℤ) ^ (2 * s) - 1) ^ 2 = |F| ^ 2 := by rw [sq_abs]; exact hF
  obtain ⟨hx, hxQ, heq⟩ := core_bounds hP hQ (abs_nonneg F) hF'
  have hd := pow_dvd_two_mul hp (not_dvd_pred hp hm (s := s)) heq (by ring)
  have hx1 := x_ne_one hP heq
  have hx2 := x_ne_two hP hQ heq
  -- `P` is coprime to `2`
  have hp2' : ¬ (p : ℤ) ∣ 2 := by
    intro h2
    have : p ∣ 2 := by exact_mod_cast h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have cop : IsCoprime ((p : ℤ) ^ (2 * m)) 2 := ((Prime.coprime_iff_not_dvd hpZ).2 hp2').pow_left
  have hd' : (p : ℤ) ^ (2 * m) ∣ |F| - _ ∨ (p : ℤ) ^ (2 * m) ∣ (|F| - _) + 2 * _ :=
    hd.imp cop.dvd_of_dvd_mul_left cop.dvd_of_dvd_mul_left
  -- `Q = P R`
  have hQR : (p : ℤ) ^ (2 * s) = (p : ℤ) ^ (2 * m) * (p : ℤ) ^ (2 * (s - m)) := by
    rw [← pow_add]; congr 1; omega
  have h3 : (3 : ℤ) ≤ p := by
    have := hp.two_le
    have : p ≠ 2 := hp2
    exact_mod_cast (by omega : 3 ≤ p)
  have hP9 : (9 : ℤ) ≤ (p : ℤ) ^ (2 * m) := by
    calc (9 : ℤ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ (p : ℤ) ^ (2 * m) := pow_le_pow_left₀ (by norm_num) h3 _
  have hPodd : Odd ((p : ℤ) ^ (2 * m)) := by
    have : Odd (p : ℤ) := by exact_mod_cast hp.odd_of_ne_two hp2
    exact this.pow
  set x := |F| - ((p : ℤ) ^ (2 * m) * (p : ℤ) ^ (2 * s) - 1) with hxdef
  clear_value x
  rw [hQR] at heq hxQ hd'
  have hPR := gap_odd_core hP9 hPodd hx hxQ heq hx1 hx2 hd'
  have := (pow_lt_pow_iff_right₀ (by exact_mod_cast hp.one_lt : (1 : ℤ) < p)).1 hPR
  omega

/-- **`p = 2` needs `m ≥ 2`.** For `P = 4` the equation `(E)` reads `F² ≡ 5 (mod 8)`. -/
theorem BrickEq.not_two_one {s : ℕ} (hs : 0 < s) : ¬ BrickEq 2 1 s := by
  rintro ⟨F, hF⟩
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (2 : ℤ) ^ (2 * s) = 4 * t :=
    ⟨2 ^ (2 * (s - 1)), by rw [show 2 * s = 2 + 2 * (s - 1) by omega, pow_add]; norm_num⟩
  push_cast at hF
  rw [ht] at hF
  have h8 : F ^ 2 = 8 * (40 * t ^ 2 - 8 * t) + 5 := by linear_combination -hF
  rcases Int.even_or_odd F with ⟨v, hv⟩ | ⟨v, hv⟩
  · subst hv
    have : (2 * v) ^ 2 = 4 * v ^ 2 := by ring
    rw [show v + v = 2 * v by ring, this] at h8
    generalize v ^ 2 = w at h8
    generalize 40 * t ^ 2 - 8 * t = u at h8
    omega
  · subst hv
    obtain ⟨r, hr⟩ := Int.even_mul_succ_self v
    have : (2 * v + 1) ^ 2 = 4 * (v * (v + 1)) + 1 := by ring
    rw [this, hr] at h8
    generalize 40 * t ^ 2 - 8 * t = u at h8
    omega

/-- For `p = 2`, every solution of `(E)` with `m, s ≥ 1` has `m ≥ 2`. -/
theorem BrickEq.two_le_of_two {m s : ℕ} (hm : 0 < m) (hs : 0 < s) (h : BrickEq 2 m s) :
    2 ≤ m := by
  by_contra hlt
  have : m = 1 := by omega
  subst this
  exact BrickEq.not_two_one hs h

/-! ### The reduction: Euler bricks with a prime-power edge ⟺ `(E)` -/

/-- **Pell form.** `(E)` is equivalent to `(P + 1) F² = P Y² + (P - 1)²` with `Y = (P + 1) Q - 2`;
this is the norm equation `X² - P(P+1) Z² = (P+1)(P-1)²` (`X = (P+1)F`, `Z = Y`) whose unit group
is generated by `2P + 1 + 2√(P(P+1))`. -/
theorem brickEq_iff_pell {p m s : ℕ} : BrickEq p m s ↔ ∃ F : ℤ,
    ((p : ℤ) ^ (2 * m) + 1) * F ^ 2 = (p : ℤ) ^ (2 * m) * (((p : ℤ) ^ (2 * m) + 1) *
      (p : ℤ) ^ (2 * s) - 2) ^ 2 + ((p : ℤ) ^ (2 * m) - 1) ^ 2 := by
  have hP1 : ((p : ℤ) ^ (2 * m) + 1) ≠ 0 := by positivity
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F, by rw [← hF]; ring⟩
  · rintro ⟨F, hF⟩
    refine ⟨F, mul_left_cancel₀ hP1 ?_⟩
    rw [hF]; ring

/-- The legs `2b = p^i B`, `2c = p^j C` with `i < j` and `b² + c² = f²` give a solution of `(E)`
with `m = j - i`, `s = k - j`. -/
theorem brickEq_of_legs {p k i j B C b c f : ℕ} (hp : p.Prime) (hij : i < j) (hjk : j < k)
    (hb : 2 * b = p ^ i * B) (hB : B + 1 = p ^ (2 * (k - i)))
    (hc : 2 * c = p ^ j * C) (hC : C + 1 = p ^ (2 * (k - j)))
    (hf : b ^ 2 + c ^ 2 = f ^ 2) : BrickEq p (j - i) (k - j) := by
  have hj : p ^ j = p ^ i * p ^ (j - i) := by rw [← pow_add]; congr 1; omega
  have hW : (2 * f) ^ 2 = (p ^ i) ^ 2 * (B ^ 2 + p ^ (2 * (j - i)) * C ^ 2) := by
    have : (2 * f) ^ 2 = (2 * b) ^ 2 + (2 * c) ^ 2 := by rw [mul_pow, mul_pow, mul_pow, ← hf]; ring
    rw [this, hb, hc, hj, pow_mul]; ring
  obtain ⟨F, hF⟩ : p ^ i ∣ 2 * f := (Nat.pow_dvd_pow_iff two_ne_zero).1 ⟨_, hW⟩
  have hF2 : F ^ 2 = B ^ 2 + p ^ (2 * (j - i)) * C ^ 2 := by
    rw [hF, mul_pow] at hW
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos hp.pos i) 2) hW
  refine ⟨F, ?_⟩
  have hPQ : p ^ (2 * (j - i)) * p ^ (2 * (k - j)) = B + 1 := by
    rw [hB, ← pow_add]; congr 1; omega
  have hPQ' : (p : ℤ) ^ (2 * (j - i)) * (p : ℤ) ^ (2 * (k - j)) = (B : ℤ) + 1 := by
    exact_mod_cast hPQ
  have hC' : (p : ℤ) ^ (2 * (k - j)) = (C : ℤ) + 1 := by exact_mod_cast hC.symm
  rw [hPQ', hC']
  have : ((F : ℤ)) ^ 2 = (B : ℤ) ^ 2 + (p : ℤ) ^ (2 * (j - i)) * (C : ℤ) ^ 2 := by
    exact_mod_cast hF2
  rw [this]; ring

/-- **Reduction (forward).** If an Euler brick has the edge `p ^ k`, then `(E)` has a solution
`(m, s)` with `m, s ≥ 1` and `i + m + s = k`, where `p ^ i` (`i ≥ 0`) is the smaller of the two
divisors `d - b`, `e - c`. -/
theorem _root_.PerfectCuboid.IsEulerBrick.exists_brickEq {p k b c : ℕ} (hp : p.Prime)
    (h : IsEulerBrick (p ^ k) b c) :
    ∃ i m s, i + m + s = k ∧ 0 < m ∧ 0 < s ∧ BrickEq p m s := by
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ca
  obtain ⟨f, hf⟩ := h.sq_bc
  have hb0 := h.pos_b
  have hc0 := h.pos_c
  obtain ⟨i, hi, B, hb, hB⟩ := leg_of_prime_pow hp hb0 (by rw [hd]; ring)
  obtain ⟨j, hj, C, hc, hC⟩ := leg_of_prime_pow hp hc0 (by rw [add_comm, he]; ring)
  have hf2 : b ^ 2 + c ^ 2 = f ^ 2 := by rw [hf]; ring
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact ⟨i, j - i, k - j, by omega, by omega, by omega,
      brickEq_of_legs hp hij hj hb hB hc hC hf2⟩
  · exfalso
    have hBC : B = C := Nat.add_right_cancel (hB.trans hC.symm)
    subst hBC
    have hcb : c = b := by omega
    subst hcb
    exact sq_ne_two_mul_sq hb0 (by rw [← hf2]; ring)
  · exact ⟨j, i - j, k - i, by omega, by omega, by omega,
      brickEq_of_legs hp hij hi hc hC hb hB (by rw [← hf2]; ring)⟩

/-- **Reduction (converse).** A solution of `(E)` with `m, s ≥ 1` gives the Euler brick
`(p ^ (m+s+1), p (p^(2(m+s)) - 1)/2, p ^ (m+1) (p^(2s) - 1)/2)`. -/
theorem isEulerBrick_of_brickEq {p m s : ℕ} (hp : p.Prime) (hm : 0 < m) (hs : 0 < s)
    (h : BrickEq p m s) : ∃ b c, 2 * b = p * (p ^ (2 * (m + s)) - 1) ∧
      2 * c = p ^ (m + 1) * (p ^ (2 * s) - 1) ∧ IsEulerBrick (p ^ (m + s + 1)) b c := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨b, hb⟩ := two_dvd_pow_mul_pow_sub_one (p := p) (a := 1) (n := 2 * (m + s)) one_pos
  obtain ⟨c, hc⟩ := two_dvd_pow_mul_pow_sub_one (p := p) (a := m + 1) (n := 2 * s) (by omega)
  rw [pow_one] at hb
  obtain ⟨N, hN⟩ : ∃ N, p ^ (2 * (m + s)) = N + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (pow_pos hp.pos _)).symm⟩
  obtain ⟨C, hC⟩ : ∃ C, p ^ (2 * s) = C + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (pow_pos hp.pos _)).symm⟩
  have hN4 : (4 : ℤ) ≤ (p : ℤ) ^ (2 * (m + s)) := four_le_pow hp (by omega)
  have hC4 : (4 : ℤ) ≤ (p : ℤ) ^ (2 * s) := four_le_pow hp hs
  rw [hN, Nat.add_sub_cancel] at hb
  rw [hC, Nat.add_sub_cancel] at hc
  have hN3 : 3 ≤ N := by
    have : (4 : ℤ) ≤ (N : ℤ) + 1 := by exact_mod_cast (hN ▸ (by exact_mod_cast hN4 :
      (4 : ℕ) ≤ p ^ (2 * (m + s))))
    omega
  have hC3 : 3 ≤ C := by
    have : (4 : ℤ) ≤ (C : ℤ) + 1 := by exact_mod_cast (hC ▸ (by exact_mod_cast hC4 :
      (4 : ℕ) ≤ p ^ (2 * s)))
    omega
  have hp0 := hp.pos
  refine ⟨b, c, by rw [hN, Nat.add_sub_cancel]; exact hb.symm,
    by rw [hC, Nat.add_sub_cancel]; exact hc.symm, ?_⟩
  have ha2 : (p ^ (m + s + 1)) ^ 2 = p ^ 2 * (N + 1) := by rw [← hN]; ring
  have ha2' : (p ^ (m + s + 1)) ^ 2 = (p ^ (m + 1)) ^ 2 * (C + 1) := by rw [← hC]; ring
  refine ⟨pow_pos hp0 _, ?_, ?_, ?_, ?_, ?_⟩
  · have : 0 < p * N := Nat.mul_pos hp0 (by omega)
    omega
  · have : 0 < p ^ (m + 1) * C := Nat.mul_pos (pow_pos hp0 _) (by omega)
    omega
  · refine isSquare_of_four_mul (Y := p * (N + 2)) ?_
    have : 4 * ((p ^ (m + s + 1)) ^ 2 + b ^ 2) = 4 * (p ^ (m + s + 1)) ^ 2 + (2 * b) ^ 2 := by
      ring
    rw [this, ha2, ← hb]; ring
  · -- `4 (b² + c²) = (p |F|)²`
    refine isSquare_of_four_mul (Y := p * F.natAbs) ?_
    have hPQ : (p : ℤ) ^ (2 * m) * (p : ℤ) ^ (2 * s) = (N : ℤ) + 1 := by
      rw [← pow_add, show 2 * m + 2 * s = 2 * (m + s) by ring]; exact_mod_cast hN
    have hQ : (p : ℤ) ^ (2 * s) = (C : ℤ) + 1 := by exact_mod_cast hC
    rw [hPQ, hQ] at hF
    have hb' : 2 * (b : ℤ) = p * N := by exact_mod_cast hb.symm
    have hc' : 2 * (c : ℤ) = (p : ℤ) ^ (m + 1) * C := by exact_mod_cast hc.symm
    have : ((4 * (b ^ 2 + c ^ 2) : ℕ) : ℤ) = ((p * F.natAbs) ^ 2 : ℕ) := by
      push_cast
      rw [mul_pow, sq_abs, ← hF]
      have e1 : 4 * ((b : ℤ) ^ 2 + (c : ℤ) ^ 2) = (2 * (b : ℤ)) ^ 2 + (2 * (c : ℤ)) ^ 2 := by ring
      rw [e1, hb', hc']
      ring
    exact_mod_cast this
  · refine isSquare_of_four_mul (Y := p ^ (m + 1) * (C + 2)) ?_
    have : 4 * (c ^ 2 + (p ^ (m + s + 1)) ^ 2) = (2 * c) ^ 2 + 4 * (p ^ (m + s + 1)) ^ 2 := by
      ring
    rw [this, ha2', ← hc]; ring

/-- **The reduction theorem.** Some Euler brick has an edge equal to a power of the prime `p` if
and only if `(PQ - 1)² + P(Q - 1)² = F²` has a solution with `P = p^(2m)`, `Q = p^(2s)`,
`m, s ≥ 1`. -/
theorem exists_isEulerBrick_prime_pow_iff {p : ℕ} (hp : p.Prime) :
    (∃ k b c, IsEulerBrick (p ^ k) b c) ↔ ∃ m s, 0 < m ∧ 0 < s ∧ BrickEq p m s := by
  constructor
  · rintro ⟨k, b, c, h⟩
    obtain ⟨i, m, s, -, hm, hs, hE⟩ := h.exists_brickEq hp
    exact ⟨m, s, hm, hs, hE⟩
  · rintro ⟨m, s, hm, hs, hE⟩
    obtain ⟨b, c, -, -, h⟩ := isEulerBrick_of_brickEq hp hm hs hE
    exact ⟨_, b, c, h⟩

/-- **Exponent restrictions for an Euler brick with a prime-power edge.**
If `IsEulerBrick (p^k) b c`
then `k = i + m + s` where `p ^ i < p ^ (i+m)` are the divisors `d - b`, `e - c` (in some order),
`m ≥ 1`, `s > m`, `s > 2m` if `p` is odd, `m ≥ 2` if `p = 2`, and `(E)` holds. In the notation of
the divisor framework: `k - j > j - i`, and `k - j > 2(j - i)` for odd `p`. -/
theorem _root_.PerfectCuboid.IsEulerBrick.prime_pow_exponents {p k b c : ℕ} (hp : p.Prime)
    (h : IsEulerBrick (p ^ k) b c) :
    ∃ i m s, i + m + s = k ∧ 0 < m ∧ m < s ∧ (p ≠ 2 → 2 * m < s) ∧ (p = 2 → 2 ≤ m) ∧
      BrickEq p m s := by
  obtain ⟨i, m, s, hk, hm, hs, hE⟩ := h.exists_brickEq hp
  refine ⟨i, m, s, hk, hm, hE.lt hp hm hs, fun h2 ↦ hE.two_mul_lt hp h2 hm hs, ?_, hE⟩
  rintro rfl
  exact hE.two_le_of_two hm hs

/-- **Small exponents.** If an Euler brick has the edge `p ^ k` then `k ≥ 4`, and `k ≥ 5` when
`p = 2` (from `k ≥ m + s` with `s > 2m ≥ 2`, resp. `s > m ≥ 2`). -/
theorem _root_.PerfectCuboid.IsEulerBrick.prime_pow_exponent_ge {p k b c : ℕ} (hp : p.Prime)
    (h : IsEulerBrick (p ^ k) b c) : 4 ≤ k ∧ (p = 2 → 5 ≤ k) := by
  obtain ⟨i, m, s, hk, hm, hms, hodd, h2, -⟩ := h.prime_pow_exponents hp
  refine ⟨?_, fun hp2 ↦ ?_⟩
  · by_cases hp2 : p = 2
    · have := h2 hp2; omega
    · have := hodd hp2; omega
  · have := h2 hp2; omega

end BrickPrimePower
end PerfectCuboid
