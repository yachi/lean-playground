module

public import LeanPlayground.PerfectCuboid.SpaceDiagonal
public import Mathlib.NumberTheory.SumTwoSquares
public import Mathlib.RingTheory.Int.Basic

/-!
# Korec: the space diagonal is neither a prime power nor a product of two primes

I. Korec, *Lower bounds for perfect rational cuboids*, Math. Slovaca 42 (1992), 565–582,
Theorem 5.1: the space diagonal `g` of a perfect cuboid is neither a prime power nor a product of
two primes.

## Main results

* `IsPerfectCuboid.ne_prime_pow`: `g ≠ p ^ k` for every prime `p`.
* `IsPerfectCuboid.ne_prime_mul_prime`: `g ≠ p * q` for all primes `p`, `q`.

## The idea

A perfect cuboid with edges `a, b, c`, face diagonals `d² = a² + b²`, `e² = a² + c²`,
`f² = b² + c²` and space diagonal `g` writes `g²` as a sum of two squares in three ways:
`g² = a² + f² = e² + b² = d² + c²`. In a primitive cuboid exactly one edge, say `a`, is odd, so
each pair has one odd member (`a, e, d`) and one even member (`f, b, c`). Two of the pairs cannot
agree up to sign: that would force `c = 0`, `b = 0`, or `f² = 2b²`.

**Prime powers** (`sq_add_sq_unique`). If `p` is an odd prime, `p ^ m` has at most one
representation `X² + Y²` with `p ∤ X`, up to order and signs. The proof is Euler's: two such
representations satisfy `(XW − YZ)(XW + YZ) = p ^ m (X² − Z²)`, `p` divides only one factor, and
`(XZ + YW)² + (XW − YZ)² = p ^ (2m)` leaves only `XW − YZ ∈ {0, ±p ^ m}`. So for `g = p ^ k` at
least two of the three pairs are divisible by `p`, and then `p` divides all three edges.

**Two primes.** For `g = pq`, Korec uses his parametrization of cuboids with diagonal `nq` and
Pocklington's theorem that `x⁴ + 18x²y² + y⁴` is never a square. We give a shorter argument.
Fix `u₁² + w₁² = p²` and `u₂² + w₂² = q²` with `u₁, u₂` odd (`exists_rep`). Dividing off a
representation of `p²` (`sq_add_sq_factor`, which is unique factorization in `ℤ[i]` written out
by hand) shows that the even member `v` of every pair satisfies one of
`v² = (u₁w₂ + w₁u₂)²`, `(w₁u₂ − u₁w₂)²`, `p²w₂²`, `q²w₁²` (`classify`). The relation
`f² = b² + c²` then leaves twelve cases (`Reps.case_A_BP` and friends), each a polynomial
identity: six have a factor that cannot vanish, two give `m y² = 2 x²` with `m` odd
(`odd_mul_sq_ne_two_mul_sq`), and four give `p² w₂ = ±4 u₁u₂w₁`. In the last case `u₂ = ±p²`
and `q² = p⁴ + 16 u₁²w₁²`; since `q` is prime, `(q − p²)/2` and `(q + p²)/2` are coprime squares
`s²`, `(s + 1)²`, and `2 |u₁w₁| = s (s + 1)` exceeds `p² = 2s + 1 ≥ 2 |u₁w₁|`
(`not_sq_eq_pow_four_add`).
-/

@[expose] public section

namespace PerfectCuboid.Korec

/-! ### Sums of two squares -/

/-- `m y² ≠ 2 x²` for odd `m` and `x ≠ 0`, since the `2`-adic valuations have different
parities. -/
theorem odd_mul_sq_ne_two_mul_sq {m : ℤ} (hm : Odd m) :
    ∀ (n : ℕ) {x y : ℤ}, x.natAbs = n → x ≠ 0 → m * y ^ 2 ≠ 2 * x ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn hx hxy
    have hy : (2 : ℤ) ∣ y := by
      rcases Int.prime_two.dvd_or_dvd (⟨x ^ 2, hxy⟩ : (2 : ℤ) ∣ m * y ^ 2) with h | h
      · exact absurd (even_iff_two_dvd.mpr h) (Int.not_even_iff_odd.mpr hm)
      · exact Int.prime_two.dvd_of_dvd_pow h
    obtain ⟨y', rfl⟩ := hy
    have hx2 : (2 : ℤ) ∣ x := by
      refine Int.prime_two.dvd_of_dvd_pow (n := 2) ⟨m * y' ^ 2, ?_⟩
      have : 2 * x ^ 2 = 2 * (2 * (m * y' ^ 2)) := by linear_combination -hxy
      exact mul_left_cancel₀ two_ne_zero this
    obtain ⟨x', rfl⟩ := hx2
    have hx' : x' ≠ 0 := by rintro rfl; simp at hx
    refine ih x'.natAbs ?_ rfl hx' (y := y') ?_
    · rw [← hn, Int.natAbs_mul]
      have := Int.natAbs_pos.mpr hx'
      simp only [Int.reduceAbs]
      omega
    · have : 4 * (m * y' ^ 2) = 4 * (2 * x' ^ 2) := by linear_combination hxy
      exact mul_left_cancel₀ four_ne_zero this

/-- `y² ≠ 2 x²` for `x ≠ 0`. -/
theorem sq_ne_two_mul_sq {x y : ℤ} (hx : x ≠ 0) : y ^ 2 ≠ 2 * x ^ 2 := by
  simpa using odd_mul_sq_ne_two_mul_sq odd_one _ rfl hx (y := y)

/-- An odd number and an even number have different squares. -/
theorem sq_ne_sq_of_odd_of_even {x y : ℤ} (hx : Odd x) (hy : Even y) : x ^ 2 ≠ y ^ 2 := by
  intro h
  have h1 : Odd (x ^ 2) := hx.pow
  rw [h] at h1
  exact Int.not_even_iff_odd.mpr h1 (hy.pow_of_ne_zero two_ne_zero)

/-- Euler's step: if `n ∣ XW − YZ` for two representations of `n`, they agree up to order and
signs. -/
theorem eq_of_dvd_sub {n X Y Z W : ℤ} (hn : n ≠ 0) (h₁ : X ^ 2 + Y ^ 2 = n)
    (h₂ : Z ^ 2 + W ^ 2 = n) (hd : n ∣ X * W - Y * Z) :
    X ^ 2 = Z ^ 2 ∧ Y ^ 2 = W ^ 2 ∨ X ^ 2 = W ^ 2 ∧ Y ^ 2 = Z ^ 2 := by
  obtain ⟨t, ht⟩ := hd
  have key : (X * Z + Y * W) ^ 2 + n ^ 2 * t ^ 2 = n ^ 2 := by
    linear_combination (-(X * W - Y * Z + n * t)) * ht + (Z ^ 2 + W ^ 2) * h₁ + n * h₂
  have hn2 : 0 < n ^ 2 := by positivity
  have ht1 : t ^ 2 ≤ 1 := by
    have : n ^ 2 * t ^ 2 ≤ n ^ 2 * 1 := by nlinarith [sq_nonneg (X * Z + Y * W)]
    exact le_of_mul_le_mul_left this hn2
  have : -1 ≤ t ∧ t ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have ht' : t = 0 ∨ t ^ 2 = 1 := by
    rcases (show t = -1 ∨ t = 0 ∨ t = 1 by omega) with h | h | h <;> simp [h]
  rcases ht' with h | h
  · subst h
    left
    have : n * X ^ 2 = n * Z ^ 2 := by
      linear_combination (X * W + Y * Z) * ht + Z ^ 2 * h₁ - X ^ 2 * h₂
    have hXZ := mul_left_cancel₀ hn this
    exact ⟨hXZ, by linear_combination h₁ - h₂ - hXZ⟩
  · have h0 : (X * Z + Y * W) ^ 2 = 0 := by linear_combination key - n ^ 2 * h
    have h0' : X * Z + Y * W = 0 := pow_eq_zero_iff two_ne_zero |>.mp h0
    right
    have : n * (X ^ 2 + Z ^ 2) = n * n := by
      linear_combination (X * Z - Y * W) * h0' + (n - Z ^ 2) * h₁ + Y ^ 2 * h₂
    have hXZ := mul_left_cancel₀ hn this
    exact ⟨by linear_combination hXZ - h₂, by linear_combination h₁ - hXZ⟩

theorem not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ 2 := by
  intro h
  have : p ∣ 2 := by exact_mod_cast h
  rcases (Nat.dvd_prime Nat.prime_two).mp this with h | h
  · exact hp.one_lt.ne' h
  · exact hp2 h

/-- **Uniqueness for prime powers.** An odd prime power `p ^ m` has at most one representation
`X² + Y²` with `p ∤ X`, up to order and signs. -/
theorem sq_add_sq_unique {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} (hm : 0 < m)
    {X Y Z W : ℤ} (h₁ : X ^ 2 + Y ^ 2 = (p : ℤ) ^ m) (h₂ : Z ^ 2 + W ^ 2 = (p : ℤ) ^ m)
    (hX : ¬ (p : ℤ) ∣ X) (hZ : ¬ (p : ℤ) ∣ Z) :
    X ^ 2 = Z ^ 2 ∧ Y ^ 2 = W ^ 2 ∨ X ^ 2 = W ^ 2 ∧ Y ^ 2 = Z ^ 2 := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpm : (p : ℤ) ∣ (p : ℤ) ^ m := dvd_pow_self _ hm.ne'
  have hW : ¬ (p : ℤ) ∣ W := by
    intro hW
    apply hZ
    refine hpi.dvd_of_dvd_pow (n := 2) ?_
    rw [show Z ^ 2 = (p : ℤ) ^ m - W ^ 2 by linear_combination h₂]
    exact dvd_sub hpm (dvd_pow hW two_ne_zero)
  have hn : ((p : ℤ) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have key : (X * W - Y * Z) * (X * W + Y * Z) = (p : ℤ) ^ m * (X ^ 2 - Z ^ 2) := by
    linear_combination X ^ 2 * h₂ - Z ^ 2 * h₁
  have hdvd : (p : ℤ) ^ m ∣ (X * W - Y * Z) * (X * W + Y * Z) := ⟨_, key⟩
  by_cases h : (p : ℤ) ∣ X * W + Y * Z
  · have h' : ¬ (p : ℤ) ∣ X * W - Y * Z := by
      intro h'
      have : (p : ℤ) ∣ 2 * (X * W) := by
        have := dvd_add h h'
        rwa [show X * W + Y * Z + (X * W - Y * Z) = 2 * (X * W) by ring] at this
      rcases hpi.dvd_or_dvd this with h2 | h2
      · exact not_dvd_two hp hp2 h2
      · rcases hpi.dvd_or_dvd h2 with h3 | h3
        · exact hX h3
        · exact hW h3
    have hc : IsCoprime ((p : ℤ) ^ m) (X * W - Y * Z) :=
      ((Prime.coprime_iff_not_dvd hpi).mpr h').pow_left
    have := eq_of_dvd_sub hn h₁ (show Z ^ 2 + (-W) ^ 2 = _ by rw [neg_sq]; exact h₂)
      (by rw [show X * -W - Y * Z = -(X * W + Y * Z) by ring]
          exact (dvd_neg).mpr (hc.dvd_of_dvd_mul_left hdvd))
    simpa [neg_sq] using this
  · have hc : IsCoprime ((p : ℤ) ^ m) (X * W + Y * Z) :=
      ((Prime.coprime_iff_not_dvd hpi).mpr h).pow_left
    exact eq_of_dvd_sub hn h₁ h₂ (hc.dvd_of_dvd_mul_right hdvd)

/-- **Dividing off a representation of `p²`.** If `u² + w² = p²` with `p ∤ u`, then every
`X² + Y² = p² N` with `p ∤ X` is `(u + i w)(X' + i Y')` up to the sign of `Y`, with
`X'² + Y'² = N`. -/
theorem sq_add_sq_factor {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {u w X Y N : ℤ}
    (hu : u ^ 2 + w ^ 2 = (p : ℤ) ^ 2) (hpu : ¬ (p : ℤ) ∣ u)
    (hX : X ^ 2 + Y ^ 2 = (p : ℤ) ^ 2 * N) (hpX : ¬ (p : ℤ) ∣ X) :
    ∃ X' Y', X' ^ 2 + Y' ^ 2 = N ∧ X = u * X' - w * Y' ∧ Y ^ 2 = (w * X' + u * Y') ^ 2 := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hpw : ¬ (p : ℤ) ∣ w := by
    intro hw
    apply hpu
    refine hpi.dvd_of_dvd_pow (n := 2) ?_
    rw [show u ^ 2 = (p : ℤ) ^ 2 - w ^ 2 by linear_combination hu]
    exact dvd_sub (dvd_pow_self _ two_ne_zero) (dvd_pow hw two_ne_zero)
  -- choose the sign `s` of `Y` with `p² ∣ X w − s Y u`
  obtain ⟨s, hs, hd⟩ : ∃ s : ℤ, s ^ 2 = 1 ∧ (p : ℤ) ^ 2 ∣ X * w - s * Y * u := by
    have key : (X * w - Y * u) * (X * w + Y * u) = (p : ℤ) ^ 2 * (X ^ 2 - N * u ^ 2) := by
      linear_combination X ^ 2 * hu - u ^ 2 * hX
    have hdvd : (p : ℤ) ^ 2 ∣ (X * w - Y * u) * (X * w + Y * u) := ⟨_, key⟩
    by_cases h : (p : ℤ) ∣ X * w + Y * u
    · have h' : ¬ (p : ℤ) ∣ X * w - Y * u := by
        intro h'
        have : (p : ℤ) ∣ 2 * (X * w) := by
          have := dvd_add h h'
          rwa [show X * w + Y * u + (X * w - Y * u) = 2 * (X * w) by ring] at this
        rcases hpi.dvd_or_dvd this with h2 | h2
        · exact not_dvd_two hp hp2 h2
        · rcases hpi.dvd_or_dvd h2 with h3 | h3
          · exact hpX h3
          · exact hpw h3
      have hc : IsCoprime ((p : ℤ) ^ 2) (X * w - Y * u) :=
        ((Prime.coprime_iff_not_dvd hpi).mpr h').pow_left
      exact ⟨-1, by norm_num, by
        rw [show X * w - -1 * Y * u = X * w + Y * u by ring]
        exact hc.dvd_of_dvd_mul_left hdvd⟩
    · have hc : IsCoprime ((p : ℤ) ^ 2) (X * w + Y * u) :=
        ((Prime.coprime_iff_not_dvd hpi).mpr h).pow_left
      exact ⟨1, by norm_num, by rw [one_mul]; exact hc.dvd_of_dvd_mul_right hdvd⟩
  obtain ⟨r, hr⟩ := hd
  have hsq : (X * u + s * Y * w) ^ 2 = ((p : ℤ) ^ 2) ^ 2 * (N - r ^ 2) := by
    linear_combination (X ^ 2 + s ^ 2 * Y ^ 2) * hu + (p : ℤ) ^ 2 * hX
      + (Y ^ 2 * (p : ℤ) ^ 2) * hs
      - (X * w - s * Y * u + (p : ℤ) ^ 2 * r) * hr
  have hdiv : (p : ℤ) ^ 2 ∣ X * u + s * Y * w :=
    (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨_, hsq⟩
  obtain ⟨X', hX'⟩ := hdiv
  refine ⟨X', -r, ?_, ?_, ?_⟩
  · have : ((p : ℤ) ^ 2) ^ 2 * (X' ^ 2 + (-r) ^ 2) = ((p : ℤ) ^ 2) ^ 2 * N := by
      linear_combination hsq - (X * u + s * Y * w + (p : ℤ) ^ 2 * X') * hX'
    exact mul_left_cancel₀ (pow_ne_zero 2 hp0) this
  · have : (p : ℤ) ^ 2 * X = (p : ℤ) ^ 2 * (u * X' - w * -r) := by
      linear_combination (-X) * hu + u * hX' + w * hr
    exact mul_left_cancel₀ hp0 this
  · have : (p : ℤ) ^ 2 * (s * Y) = (p : ℤ) ^ 2 * (w * X' + u * -r) := by
      linear_combination (-(s * Y)) * hu + w * hX' - u * hr
    have h2 := mul_left_cancel₀ hp0 this
    rw [← h2]
    linear_combination (-Y ^ 2) * hs

/-! ### Reduction to primitive cuboids -/

/-- Dividing a perfect cuboid by `gcd(a, b, c)` gives a primitive perfect cuboid whose space
diagonal divides the original one. -/
theorem exists_primitive_dvd {a b c g : ℕ} (h : IsPerfectCuboid a b c)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    ∃ a' b' c' g', IsPerfectCuboid a' b' c' ∧ Nat.gcd a' (Nat.gcd b' c') = 1 ∧
      a' ^ 2 + b' ^ 2 + c' ^ 2 = g' ^ 2 ∧ g' ∣ g := by
  set G := Nat.gcd a (Nat.gcd b c) with hG
  have hG0 : 0 < G := Nat.gcd_pos_of_pos_left _ h.pos_a
  have hbc : G ∣ Nat.gcd b c := Nat.gcd_dvd_right _ _
  obtain ⟨x, hx⟩ : G ∣ a := Nat.gcd_dvd_left _ _
  obtain ⟨y, hy⟩ : G ∣ b := hbc.trans (Nat.gcd_dvd_left _ _)
  obtain ⟨z, hz⟩ : G ∣ c := hbc.trans (Nat.gcd_dvd_right _ _)
  obtain ⟨g', hg'⟩ : G ∣ g := (Nat.pow_dvd_pow_iff two_ne_zero).mp
    ⟨x ^ 2 + y ^ 2 + z ^ 2, by rw [← hg, hx, hy, hz]; ring⟩
  have pos {u v : ℕ} (huv : u = G * v) (hu : 0 < u) : 0 < v := by
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · omega
    · exact hv
  have sq2 {u v : ℕ} (huv : IsSquare ((G * u) ^ 2 + (G * v) ^ 2)) : IsSquare (u ^ 2 + v ^ 2) :=
    isSquare_of_sq_mul hG0 (by rw [mul_add, ← mul_pow, ← mul_pow]; exact huv)
  have hsum : x ^ 2 + y ^ 2 + z ^ 2 = g' ^ 2 := by
    have : G ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) = G ^ 2 * g' ^ 2 := by
      rw [← mul_pow, ← hg', ← hg, hx, hy, hz]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  refine ⟨x, y, z, g', ⟨⟨pos hx h.pos_a, pos hy h.pos_b, pos hz h.pos_c, ?_, ?_, ?_⟩, ?_⟩, ?_,
    hsum, ⟨G, by rw [hg', mul_comm]⟩⟩
  · exact sq2 (hx ▸ hy ▸ h.sq_ab)
  · exact sq2 (hy ▸ hz ▸ h.sq_bc)
  · exact sq2 (hz ▸ hx ▸ h.sq_ca)
  · exact ⟨g', by rw [← sq]; exact hsum⟩
  · have e : Nat.gcd (G * x) (Nat.gcd (G * y) (G * z)) = G * Nat.gcd x (Nat.gcd y z) := by
      rw [Nat.gcd_mul_left, Nat.gcd_mul_left]
    rw [← hx, ← hy, ← hz, ← hG] at e
    exact (Nat.mul_eq_left hG0.ne').mp e.symm

/-- The data of a primitive perfect cuboid over `ℤ`, with the odd edge first: edges `a, b, c`,
face diagonals `d, e, f` opposite `c, b, a`, and space diagonal `g`. -/
structure Cuboid (a b c d e f g : ℤ) : Prop where
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  hd : a ^ 2 + b ^ 2 = d ^ 2
  he : a ^ 2 + c ^ 2 = e ^ 2
  hf : b ^ 2 + c ^ 2 = f ^ 2
  hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2
  odd_a : Odd a
  even_b : Even b
  even_c : Even c
  prim : ∀ r : ℤ, Prime r → r ∣ a → r ∣ b → r ∣ c → False

namespace Cuboid

variable {a b c d e f g : ℤ}

theorem odd_e (C : Cuboid a b c d e f g) : Odd e := by
  have : Odd (e ^ 2) := by
    rw [← C.he]; exact C.odd_a.pow.add_even (C.even_c.pow_of_ne_zero two_ne_zero)
  exact (Int.odd_pow' two_ne_zero).mp this

theorem odd_d (C : Cuboid a b c d e f g) : Odd d := by
  have : Odd (d ^ 2) := by
    rw [← C.hd]; exact C.odd_a.pow.add_even (C.even_b.pow_of_ne_zero two_ne_zero)
  exact (Int.odd_pow' two_ne_zero).mp this

theorem af (C : Cuboid a b c d e f g) : a ^ 2 + f ^ 2 = g ^ 2 := by
  linear_combination C.hg - C.hf
theorem eb (C : Cuboid a b c d e f g) : e ^ 2 + b ^ 2 = g ^ 2 := by
  linear_combination C.hg - C.he
theorem dc (C : Cuboid a b c d e f g) : d ^ 2 + c ^ 2 = g ^ 2 := by
  linear_combination C.hg - C.hd

theorem f_ne_zero (C : Cuboid a b c d e f g) : f ≠ 0 := by
  rintro rfl
  nlinarith [C.hf, C.pos_b, C.pos_c]

/-- The pairs `(a, f)` and `(e, b)` never agree up to order and signs. -/
theorem not_af_eb (C : Cuboid a b c d e f g) :
    ¬ (a ^ 2 = e ^ 2 ∧ f ^ 2 = b ^ 2 ∨ a ^ 2 = b ^ 2 ∧ f ^ 2 = e ^ 2) := by
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · nlinarith [C.he, C.pos_c]
  · exact sq_ne_sq_of_odd_of_even C.odd_a C.even_b h

/-- The pairs `(a, f)` and `(d, c)` never agree up to order and signs. -/
theorem not_af_dc (C : Cuboid a b c d e f g) :
    ¬ (a ^ 2 = d ^ 2 ∧ f ^ 2 = c ^ 2 ∨ a ^ 2 = c ^ 2 ∧ f ^ 2 = d ^ 2) := by
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · nlinarith [C.hd, C.pos_b]
  · exact sq_ne_sq_of_odd_of_even C.odd_a C.even_c h

/-- The pairs `(e, b)` and `(d, c)` never agree up to order and signs. -/
theorem not_eb_dc (C : Cuboid a b c d e f g) :
    ¬ (e ^ 2 = d ^ 2 ∧ b ^ 2 = c ^ 2 ∨ e ^ 2 = c ^ 2 ∧ b ^ 2 = d ^ 2) := by
  rintro (⟨-, h⟩ | ⟨h, -⟩)
  · exact sq_ne_two_mul_sq C.pos_b.ne' (y := f) (by linear_combination -C.hf - h)
  · exact sq_ne_sq_of_odd_of_even C.odd_e C.even_c h

theorem dvd_of_dvd_sq {r x : ℤ} (hr : Prime r) (h : r ∣ x ^ 2) : r ∣ x :=
  hr.dvd_of_dvd_pow h

/-- No prime dividing `g` divides two of the odd members `a, e, d`. -/
theorem not_dvd_two_of {r : ℤ} (C : Cuboid a b c d e f g) (hr : Prime r) (hg : r ∣ g) :
    ¬ (r ∣ a ∧ r ∣ e) ∧ ¬ (r ∣ a ∧ r ∣ d) ∧ ¬ (r ∣ e ∧ r ∣ d) := by
  have sq {x : ℤ} (h : r ∣ x) : r ∣ x ^ 2 := dvd_pow h two_ne_zero
  have hg2 := sq hg
  refine ⟨fun ⟨ha, he⟩ ↦ ?_, fun ⟨ha, hd⟩ ↦ ?_, fun ⟨he, hd⟩ ↦ ?_⟩
  · have hc : r ∣ c := hr.dvd_of_dvd_pow (n := 2)
      (by rw [show c ^ 2 = e ^ 2 - a ^ 2 by linear_combination C.he]; exact dvd_sub (sq he) (sq ha))
    have hb : r ∣ b := hr.dvd_of_dvd_pow (n := 2)
      (by rw [show b ^ 2 = g ^ 2 - a ^ 2 - c ^ 2 by linear_combination C.hg]
          exact dvd_sub (dvd_sub hg2 (sq ha)) (sq hc))
    exact C.prim r hr ha hb hc
  · have hb : r ∣ b := hr.dvd_of_dvd_pow (n := 2)
      (by rw [show b ^ 2 = d ^ 2 - a ^ 2 by linear_combination C.hd]; exact dvd_sub (sq hd) (sq ha))
    have hc : r ∣ c := hr.dvd_of_dvd_pow (n := 2)
      (by rw [show c ^ 2 = g ^ 2 - a ^ 2 - b ^ 2 by linear_combination C.hg]
          exact dvd_sub (dvd_sub hg2 (sq ha)) (sq hb))
    exact C.prim r hr ha hb hc
  · have hb : r ∣ b := hr.dvd_of_dvd_pow (n := 2)
      (by rw [show b ^ 2 = g ^ 2 - e ^ 2 by linear_combination C.eb]; exact dvd_sub hg2 (sq he))
    have hc : r ∣ c := hr.dvd_of_dvd_pow (n := 2)
      (by rw [show c ^ 2 = g ^ 2 - d ^ 2 by linear_combination C.dc]; exact dvd_sub hg2 (sq hd))
    have ha : r ∣ a := hr.dvd_of_dvd_pow (n := 2)
      (by rw [show a ^ 2 = d ^ 2 - b ^ 2 by linear_combination C.hd]; exact dvd_sub (sq hd) (sq hb))
    exact C.prim r hr ha hb hc

/-- **Korec, Theorem 5.1, prime powers (primitive case).** -/
theorem not_prime_pow (C : Cuboid a b c d e f g) {p k : ℕ} (hp : p.Prime)
    (hgk : g = (p : ℤ) ^ k) : False := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have := C.hg
      rw [hgk, pow_zero] at this
      nlinarith [C.pos_a, C.pos_b, C.pos_c]
    · exact hk
  have hg2 : g ^ 2 = (p : ℤ) ^ (2 * k) := by rw [hgk, ← pow_mul, mul_comm]
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hodd : Odd (g ^ 2) := by
      rw [← C.hg]
      exact (C.odd_a.pow.add_even (C.even_b.pow_of_ne_zero two_ne_zero)).add_even
        (C.even_c.pow_of_ne_zero two_ne_zero)
    rw [hg2] at hodd
    exact Int.not_even_iff_odd.mpr hodd ((Int.even_pow' (by omega)).mpr even_two)
  have hm : 0 < 2 * k := by omega
  have hpg : (p : ℤ) ∣ g := hgk ▸ dvd_pow_self _ hk.ne'
  obtain ⟨h1, h2, h3⟩ := C.not_dvd_two_of hpi hpg
  have uniq {X Y Z W : ℤ} (hX : X ^ 2 + Y ^ 2 = g ^ 2) (hZ : Z ^ 2 + W ^ 2 = g ^ 2)
      (hpX : ¬ (p : ℤ) ∣ X) (hpZ : ¬ (p : ℤ) ∣ Z) :=
    sq_add_sq_unique hp hp2 hm (hX.trans hg2) (hZ.trans hg2) hpX hpZ
  by_cases ha : (p : ℤ) ∣ a <;> by_cases he : (p : ℤ) ∣ e <;> by_cases hd : (p : ℤ) ∣ d
  · exact h1 ⟨ha, he⟩
  · exact h1 ⟨ha, he⟩
  · exact h2 ⟨ha, hd⟩
  · exact C.not_eb_dc (uniq C.eb C.dc he hd)
  · exact h3 ⟨he, hd⟩
  · exact C.not_af_dc (uniq C.af C.dc ha hd)
  · exact C.not_af_eb (uniq C.af C.eb ha he)
  · exact C.not_af_eb (uniq C.af C.eb ha he)

end Cuboid

/-- A primitive perfect cuboid, with its diagonals, as a `Cuboid` (after putting the odd edge
first). -/
theorem exists_cuboid {a b c g : ℕ} (h : IsPerfectCuboid a b c) (hp : Nat.gcd a (Nat.gcd b c) = 1)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    ∃ a' b' c' d' e' f' : ℤ, Cuboid a' b' c' d' e' f' g := by
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨e, he⟩ := h.sq_ca
  have hd' : (a : ℤ) ^ 2 + b ^ 2 = d ^ 2 := by rw [sq (d : ℤ)]; exact_mod_cast hd
  have hf' : (b : ℤ) ^ 2 + c ^ 2 = f ^ 2 := by rw [sq (f : ℤ)]; exact_mod_cast hf
  have he' : (c : ℤ) ^ 2 + a ^ 2 = e ^ 2 := by rw [sq (e : ℤ)]; exact_mod_cast he
  have hg' : (a : ℤ) ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 := by exact_mod_cast hg
  have ha := h.pos_a
  have hb := h.pos_b
  have hc := h.pos_c
  have prim (r : ℤ) (hr : Prime r) (ha : r ∣ a) (hb : r ∣ b) (hc : r ∣ c) : False := by
    have h1 : r.natAbs ∣ Nat.gcd a (Nat.gcd b c) :=
      Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr ha) (Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr hb)
        (Int.natAbs_dvd_natAbs.mpr hc))
    rw [hp, Nat.dvd_one] at h1
    exact hr.not_isUnit (Int.isUnit_iff_natAbs_eq.mpr h1)
  have odd2 {x : ℕ} (hx : ¬ 2 ∣ x) : Odd (x : ℤ) := by
    exact Int.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact_mod_cast hx)
  have even2 {x : ℕ} (hx : 2 ∣ x) : Even (x : ℤ) := by
    rw [even_iff_two_dvd]; exact_mod_cast hx
  rcases h.one_odd hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨a, b, c, d, e, f, by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hc,
      hd', by linear_combination he', hf', hg', odd2 h1, even2 h2, even2 h3, prim⟩
  · exact ⟨b, a, c, d, f, e, by exact_mod_cast hb, by exact_mod_cast ha, by exact_mod_cast hc,
      by linear_combination hd', hf', by linear_combination he', by linear_combination hg',
      odd2 h2, even2 h1, even2 h3, fun r hr h₁ h₂ h₃ ↦ prim r hr h₂ h₁ h₃⟩
  · exact ⟨c, a, b, e, f, d, by exact_mod_cast hc, by exact_mod_cast ha, by exact_mod_cast hb,
      he', by linear_combination hf', hd', by linear_combination hg',
      odd2 h3, even2 h1, even2 h2, fun r hr h₁ h₂ h₃ ↦ prim r hr h₂ h₃ h₁⟩

/-! ### Two primes -/

theorem ne_zero_of_odd {x : ℤ} (hx : Odd x) : x ≠ 0 := by
  rintro rfl
  exact Int.not_even_iff_odd.mpr hx ⟨0, rfl⟩

/-- A prime `p ≡ 1 (mod 4)` gives `u² + w² = p²` with `u` odd, `w` even and `p ∤ u`. -/
theorem exists_rep {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∃ u w : ℤ, u ^ 2 + w ^ 2 = (p : ℤ) ^ 2 ∧ ¬ (p : ℤ) ∣ u ∧ Odd u ∧ Even w := by
  have := Fact.mk hp
  obtain ⟨x, y, hxy⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  have hxy' : (x : ℤ) ^ 2 + y ^ 2 = p := by exact_mod_cast hxy
  have hp2 : p ≠ 2 := by omega
  have hpo : Odd (p : ℤ) := (Int.odd_coe_nat p).mpr (hp.odd_of_ne_two hp2)
  refine ⟨x ^ 2 - y ^ 2, 2 * x * y, by rw [← hxy']; ring, ?_, ?_, ⟨x * y, by ring⟩⟩
  · intro hd
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have h2 : (p : ℤ) ∣ 2 * x ^ 2 := by
      have := dvd_add hd (dvd_refl (p : ℤ))
      rwa [show (x : ℤ) ^ 2 - y ^ 2 + p = 2 * x ^ 2 by rw [← hxy']; ring] at this
    rcases hpi.dvd_or_dvd h2 with h | h
    · exact not_dvd_two hp hp2 h
    · have hx : p ∣ x := by exact_mod_cast hpi.dvd_of_dvd_pow h
      rcases Nat.eq_zero_or_pos x with rfl | hx0
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at hxy
        exact Nat.Prime.not_prime_pow le_rfl (hxy ▸ hp)
      · have := Nat.le_of_dvd hx0 hx
        have : p * p ≤ x ^ 2 := by nlinarith
        nlinarith [hp.two_le]
  · rw [show (x : ℤ) ^ 2 - y ^ 2 = p - 2 * y ^ 2 by rw [← hxy']; ring]
    exact hpo.sub_even ⟨y ^ 2, by ring⟩

/-- Representations `u₁² + w₁² = p²` and `u₂² + w₂² = q²` of the squares of two distinct odd
primes, with `u₁, u₂` odd. -/
structure Reps (p q : ℕ) (u₁ w₁ u₂ w₂ : ℤ) : Prop where
  hp : p.Prime
  hq : q.Prime
  hp2 : p ≠ 2
  hq2 : q ≠ 2
  hpq : p ≠ q
  h₁ : u₁ ^ 2 + w₁ ^ 2 = (p : ℤ) ^ 2
  h₂ : u₂ ^ 2 + w₂ ^ 2 = (q : ℤ) ^ 2
  hpu : ¬ (p : ℤ) ∣ u₁
  hqu : ¬ (q : ℤ) ∣ u₂
  odd_u₁ : Odd u₁
  even_w₁ : Even w₁
  odd_u₂ : Odd u₂
  even_w₂ : Even w₂

namespace Reps

variable {p q : ℕ} {u₁ w₁ u₂ w₂ : ℤ}

theorem symm (R : Reps p q u₁ w₁ u₂ w₂) : Reps q p u₂ w₂ u₁ w₁ :=
  ⟨R.hq, R.hp, R.hq2, R.hp2, R.hpq.symm, R.h₂, R.h₁, R.hqu, R.hpu, R.odd_u₂, R.even_w₂,
    R.odd_u₁, R.even_w₁⟩

theorem not_dvd_w₁ (R : Reps p q u₁ w₁ u₂ w₂) : ¬ (p : ℤ) ∣ w₁ := by
  intro hw
  apply R.hpu
  refine (Nat.prime_iff_prime_int.mp R.hp).dvd_of_dvd_pow (n := 2) ?_
  rw [show u₁ ^ 2 = (p : ℤ) ^ 2 - w₁ ^ 2 by linear_combination R.h₁]
  exact dvd_sub (dvd_pow_self _ two_ne_zero) (dvd_pow hw two_ne_zero)

theorem w₁_ne_zero (R : Reps p q u₁ w₁ u₂ w₂) : w₁ ≠ 0 := by
  rintro rfl
  exact R.not_dvd_w₁ (dvd_zero _)

theorem w₂_ne_zero (R : Reps p q u₁ w₁ u₂ w₂) : w₂ ≠ 0 := R.symm.w₁_ne_zero

theorem not_dvd_q (R : Reps p q u₁ w₁ u₂ w₂) : ¬ (p : ℤ) ∣ q := by
  intro h
  exact R.hpq ((Nat.prime_dvd_prime_iff_eq R.hp R.hq).mp (by exact_mod_cast h))

set_option maxHeartbeats 400000 in -- many `linear_combination`s over a large context
/-- The case `p² w₂ = ±4 u₁u₂w₁`: then `u₂ = ±p²`, `q² = p⁴ + 16 u₁²w₁²`, and since `q` is prime,
`(q − p²)/2 = s²` and `(q + p²)/2 = (s + 1)²`, so `2 |u₁w₁| = s (s + 1) > 2s + 1 = p²`. -/
theorem not_sq_eq_pow_four_add (R : Reps p q u₁ w₁ u₂ w₂)
    (h : ((p : ℤ) ^ 2 * w₂) ^ 2 = (4 * u₁ * u₂ * w₁) ^ 2) : False := by
  set P : ℤ := (p : ℤ) with hP
  set Q : ℤ := (q : ℤ) with hQ
  have hpi : Prime P := Nat.prime_iff_prime_int.mp R.hp
  have hqi : Prime Q := Nat.prime_iff_prime_int.mp R.hq
  have hP0 : P ^ 2 ≠ 0 := pow_ne_zero _ hpi.ne_zero
  -- `p² ∣ u₂`
  have hc : IsCoprime (P ^ 4) ((2 : ℤ) ^ 4 * u₁ ^ 2 * w₁ ^ 2) := by
    have c2 : IsCoprime P 2 := (Prime.coprime_iff_not_dvd hpi).mpr (not_dvd_two R.hp R.hp2)
    have cu : IsCoprime P u₁ := (Prime.coprime_iff_not_dvd hpi).mpr R.hpu
    have cw : IsCoprime P w₁ := (Prime.coprime_iff_not_dvd hpi).mpr R.not_dvd_w₁
    exact ((c2.pow_right.mul_right cu.pow_right).mul_right cw.pow_right).pow_left
  have hPu : P ^ 2 ∣ u₂ := by
    refine (Int.pow_dvd_pow_iff two_ne_zero).mp ?_
    rw [← pow_mul]
    exact hc.dvd_of_dvd_mul_left ⟨w₂ ^ 2, by linear_combination -h⟩
  -- `u₂ ∣ p²`
  have hcw : IsCoprime u₂ w₂ := by
    have c1 : IsCoprime u₂ (Q ^ 2) :=
      ((Prime.coprime_iff_not_dvd hqi).mpr R.hqu).symm.pow_right
    rw [show Q ^ 2 = w₂ ^ 2 + u₂ * u₂ by linear_combination -R.h₂] at c1
    exact (IsCoprime.pow_right_iff two_pos).mp c1.of_add_mul_left_right
  have huP : u₂ ∣ P ^ 2 := by
    refine hcw.dvd_of_dvd_mul_right ((Int.pow_dvd_pow_iff two_ne_zero).mp ?_)
    exact ⟨(4 * u₁ * w₁) ^ 2, by rw [h]; ring⟩
  obtain ⟨k, hk⟩ := hPu
  obtain ⟨l, hl⟩ := huP
  have hkl : k * l = 1 := by
    have : P ^ 2 * (k * l) = P ^ 2 * 1 := by linear_combination -l * hk - hl
    exact mul_left_cancel₀ hP0 this
  have hk2 : k ^ 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hkl with rfl | rfl <;> norm_num
  have hu2 : u₂ ^ 2 = P ^ 4 := by rw [hk]; linear_combination P ^ 4 * hk2
  have hw2 : w₂ ^ 2 = (4 * u₁ * w₁) ^ 2 := by
    have : P ^ 4 * w₂ ^ 2 = P ^ 4 * (4 * u₁ * w₁) ^ 2 := by
      linear_combination h + 16 * u₁ ^ 2 * w₁ ^ 2 * hu2
    exact mul_left_cancel₀ (pow_ne_zero _ hpi.ne_zero) this
  have hQ2 : Q ^ 2 = (P ^ 2) ^ 2 + 4 * (2 * u₁ * w₁) ^ 2 := by
    linear_combination -R.h₂ + hu2 + hw2
  -- `(q − p²)/2` and `(q + p²)/2` are coprime with product `(2u₁w₁)²`
  have hM : 2 * u₁ * w₁ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (ne_zero_of_odd R.odd_u₁))
    R.w₁_ne_zero
  have hQpos : 0 < Q := by rw [hQ]; exact_mod_cast R.hq.pos
  have hQP : P ^ 2 < Q := by
    by_contra hle
    rw [not_lt] at hle
    have := pow_le_pow_left₀ hQpos.le hle 2
    have : 0 < (2 * u₁ * w₁) ^ 2 := by positivity
    linarith
  obtain ⟨kq, hkq⟩ : Odd Q := (Int.odd_coe_nat q).mpr (R.hq.odd_of_ne_two R.hq2)
  obtain ⟨kp, hkp⟩ : Odd (P ^ 2) := ((Int.odd_coe_nat p).mpr (R.hp.odd_of_ne_two R.hp2)).pow
  obtain ⟨A, hA⟩ : ∃ A, Q - P ^ 2 = 2 * A := ⟨kq - kp, by rw [hkq, hkp]; ring⟩
  obtain ⟨B, hB⟩ : ∃ B, Q + P ^ 2 = 2 * B := ⟨kq + kp + 1, by rw [hkq, hkp]; ring⟩
  have hPBA : P ^ 2 = B - A := by linarith
  have hQAB : Q = A + B := by linarith
  have hAB : A * B = (2 * u₁ * w₁) ^ 2 := by
    have : 4 * (A * B) = 4 * (2 * u₁ * w₁) ^ 2 := by
      linear_combination hQ2 - (Q + P ^ 2) * hA - 2 * A * hB
    exact mul_left_cancel₀ four_ne_zero this
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith [sq_nonneg P]
  have hcop : IsCoprime A B := by
    obtain ⟨x, y, hxy⟩ := ((Prime.coprime_iff_not_dvd hpi).mpr R.not_dvd_q).pow_left (m := 2)
    exact ⟨y - x, x + y, by linear_combination hxy - x * hPBA - y * hQAB⟩
  obtain ⟨s₀, hs₀⟩ := Int.sq_of_isCoprime hcop hAB
  obtain ⟨t₀, ht₀⟩ := Int.sq_of_isCoprime hcop.symm (by rw [mul_comm]; exact hAB)
  have hAs : A = |s₀| ^ 2 := by
    rw [sq_abs]
    rcases hs₀ with h | h
    · exact h
    · nlinarith [sq_nonneg s₀]
  have hBt : B = |t₀| ^ 2 := by
    rw [sq_abs]
    rcases ht₀ with h | h
    · exact h
    · nlinarith [sq_nonneg t₀]
  set s := |s₀|
  set t := |t₀|
  have hs : 0 ≤ s := abs_nonneg _
  have ht : 0 ≤ t := abs_nonneg _
  have hs1 : 0 < s := by
    rcases hs.lt_or_eq with h | h
    · exact h
    · rw [← h] at hAs; omega
  have hdiff : (t - s) * (t + s) = P ^ 2 := by linear_combination -hBt + hAs - hPBA
  have hPpos : 0 < P ^ 2 := pow_pos (by rw [hP]; exact_mod_cast R.hp.pos) 2
  have hts : s < t := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hc) (add_nonneg ht hs)]
  -- `t − s = 1`, since `p` divides at most one of `t − s`, `t + s`
  have hts1 : t - s = 1 := by
    have hdvd₁ : t - s ∣ P ^ 2 := ⟨t + s, hdiff.symm⟩
    have hdvd₂ : t + s ∣ P ^ 2 := ⟨t - s, by rw [← hdiff]; ring⟩
    by_cases hd : P ∣ t - s
    · have hd' : ¬ P ∣ t + s := by
        intro hd'
        have h2t : P ∣ 2 * t := by
          have := dvd_add hd hd'; rwa [show t - s + (t + s) = 2 * t by ring] at this
        have h2s : P ∣ 2 * s := by
          have := dvd_sub hd' hd; rwa [show t + s - (t - s) = 2 * s by ring] at this
        have ht' : P ∣ t := (hpi.dvd_or_dvd h2t).resolve_left (not_dvd_two R.hp R.hp2)
        have hs' : P ∣ s := (hpi.dvd_or_dvd h2s).resolve_left (not_dvd_two R.hp R.hp2)
        have : Q = s ^ 2 + t ^ 2 := by linear_combination hQAB + hAs + hBt
        have hPQ : P ∣ Q := by
          rw [this]; exact dvd_add (dvd_pow hs' two_ne_zero) (dvd_pow ht' two_ne_zero)
        exact R.not_dvd_q hPQ
      have hu := ((Prime.coprime_iff_not_dvd hpi).mpr hd').symm.pow_right (n := 2)
        |>.isUnit_of_dvd' (dvd_refl _) hdvd₂
      rcases Int.isUnit_iff.mp hu with h | h <;> omega
    · have hu := ((Prime.coprime_iff_not_dvd hpi).mpr hd).symm.pow_right (n := 2)
        |>.isUnit_of_dvd' (dvd_refl _) hdvd₁
      rcases Int.isUnit_iff.mp hu with h | h <;> omega
  -- the size contradiction
  have hP2 : P ^ 2 = 2 * s + 1 := by
    rw [← hdiff, hts1]; linear_combination hts1
  have hle : (2 * u₁ * w₁) ^ 2 ≤ (P ^ 2) ^ 2 := by
    rw [← R.h₁]; nlinarith [sq_nonneg (u₁ ^ 2 - w₁ ^ 2)]
  have hst : (s * t) ^ 2 ≤ (2 * s + 1) ^ 2 := by
    rw [← hP2, mul_pow, ← hAs, ← hBt, hAB]; exact hle
  have hst' : s * t ≤ 2 * s + 1 :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hst
  have hp3 : (3 : ℤ) ≤ P := by
    have := R.hp.two_le
    have : p ≠ 2 := R.hp2
    have : 3 ≤ p := by omega
    rw [hP]; exact_mod_cast this
  have ht' : t = s + 1 := by linarith
  rw [ht'] at hst'
  have hs1' : s ≤ 1 := by nlinarith
  have : s = 1 := le_antisymm hs1' hs1
  rw [this] at hP2
  nlinarith

theorem case_A_BP (R : Reps p q u₁ w₁ u₂ w₂)
    (h : (w₁ * u₂ - u₁ * w₂) ^ 2 + (p : ℤ) ^ 2 * w₂ ^ 2 = (u₁ * w₂ + w₁ * u₂) ^ 2) : False := by
  have : w₂ * ((p : ℤ) ^ 2 * w₂ - 4 * u₁ * u₂ * w₁) = 0 := by linear_combination h
  have := (mul_eq_zero.mp this).resolve_left R.w₂_ne_zero
  exact R.not_sq_eq_pow_four_add (by rw [show (p : ℤ) ^ 2 * w₂ = 4 * u₁ * u₂ * w₁ by linarith])

theorem case_B_AP (R : Reps p q u₁ w₁ u₂ w₂)
    (h : (u₁ * w₂ + w₁ * u₂) ^ 2 + (p : ℤ) ^ 2 * w₂ ^ 2 = (w₁ * u₂ - u₁ * w₂) ^ 2) : False := by
  have : w₂ * ((p : ℤ) ^ 2 * w₂ + 4 * u₁ * u₂ * w₁) = 0 := by linear_combination h
  have := (mul_eq_zero.mp this).resolve_left R.w₂_ne_zero
  exact R.not_sq_eq_pow_four_add
    (by rw [show (p : ℤ) ^ 2 * w₂ = -(4 * u₁ * u₂ * w₁) by linarith]; ring)

theorem case_P_AB (R : Reps p q u₁ w₁ u₂ w₂)
    (h : (u₁ * w₂ + w₁ * u₂) ^ 2 + (w₁ * u₂ - u₁ * w₂) ^ 2 = (p : ℤ) ^ 2 * w₂ ^ 2) : False := by
  have hm : Odd (w₁ ^ 2 - u₁ ^ 2) := by
    rw [← Int.not_even_iff_odd]
    intro he
    have := (he.add (R.even_w₁.pow_of_ne_zero two_ne_zero)).sub
      (he.add (R.even_w₁.pow_of_ne_zero two_ne_zero))
    exact Int.not_even_iff_odd.mpr R.odd_u₁.pow
      (by simpa using (R.even_w₁.pow_of_ne_zero two_ne_zero).sub he)
  exact odd_mul_sq_ne_two_mul_sq hm _ rfl (mul_ne_zero R.w₁_ne_zero (ne_zero_of_odd R.odd_u₂))
    (y := w₂) (by linear_combination -h + w₂ ^ 2 * R.h₁)

theorem case_A_PQ (R : Reps p q u₁ w₁ u₂ w₂)
    (h : (p : ℤ) ^ 2 * w₂ ^ 2 + (q : ℤ) ^ 2 * w₁ ^ 2 = (u₁ * w₂ + w₁ * u₂) ^ 2) : False := by
  have : 2 * w₁ * w₂ * (w₁ * w₂ - u₁ * u₂) = 0 := by
    linear_combination h + w₂ ^ 2 * R.h₁ + w₁ ^ 2 * R.h₂
  have hodd : Odd (w₁ * w₂ - u₁ * u₂) :=
    (R.even_w₁.mul_right w₂).sub_odd (R.odd_u₁.mul R.odd_u₂)
  rcases mul_eq_zero.mp this with h0 | h0
  · exact mul_ne_zero (mul_ne_zero two_ne_zero R.w₁_ne_zero) R.w₂_ne_zero h0
  · exact ne_zero_of_odd hodd h0

theorem case_B_PQ (R : Reps p q u₁ w₁ u₂ w₂)
    (h : (p : ℤ) ^ 2 * w₂ ^ 2 + (q : ℤ) ^ 2 * w₁ ^ 2 = (w₁ * u₂ - u₁ * w₂) ^ 2) : False := by
  have : 2 * w₁ * w₂ * (w₁ * w₂ + u₁ * u₂) = 0 := by
    linear_combination h + w₂ ^ 2 * R.h₁ + w₁ ^ 2 * R.h₂
  have hodd : Odd (w₁ * w₂ + u₁ * u₂) :=
    (R.even_w₁.mul_right w₂).add_odd (R.odd_u₁.mul R.odd_u₂)
  rcases mul_eq_zero.mp this with h0 | h0
  · exact mul_ne_zero (mul_ne_zero two_ne_zero R.w₁_ne_zero) R.w₂_ne_zero h0
  · exact ne_zero_of_odd hodd h0

theorem case_P_AQ (R : Reps p q u₁ w₁ u₂ w₂) (hA : (u₁ * w₂ + w₁ * u₂) ^ 2 ≠ 0)
    (h : (u₁ * w₂ + w₁ * u₂) ^ 2 + (q : ℤ) ^ 2 * w₁ ^ 2 = (p : ℤ) ^ 2 * w₂ ^ 2) : False := by
  have : 2 * u₂ * w₁ * (u₁ * w₂ + w₁ * u₂) = 0 := by
    linear_combination h - w₂ ^ 2 * R.h₁ + w₁ ^ 2 * R.h₂
  rcases mul_eq_zero.mp this with h0 | h0
  · exact mul_ne_zero (mul_ne_zero two_ne_zero (ne_zero_of_odd R.odd_u₂)) R.w₁_ne_zero h0
  · exact hA (by rw [h0]; ring)

theorem case_P_BQ (R : Reps p q u₁ w₁ u₂ w₂) (hB : (w₁ * u₂ - u₁ * w₂) ^ 2 ≠ 0)
    (h : (w₁ * u₂ - u₁ * w₂) ^ 2 + (q : ℤ) ^ 2 * w₁ ^ 2 = (p : ℤ) ^ 2 * w₂ ^ 2) : False := by
  have : 2 * u₂ * w₁ * (w₁ * u₂ - u₁ * w₂) = 0 := by
    linear_combination h - w₂ ^ 2 * R.h₁ + w₁ ^ 2 * R.h₂
  rcases mul_eq_zero.mp this with h0 | h0
  · exact mul_ne_zero (mul_ne_zero two_ne_zero (ne_zero_of_odd R.odd_u₂)) R.w₁_ne_zero h0
  · exact hB (by rw [h0]; ring)

/-! The remaining six cases are the six above with `p` and `q` swapped (`Reps.symm`). -/

theorem case_A_BQ (R : Reps p q u₁ w₁ u₂ w₂)
    (h : (w₁ * u₂ - u₁ * w₂) ^ 2 + (q : ℤ) ^ 2 * w₁ ^ 2 = (u₁ * w₂ + w₁ * u₂) ^ 2) : False :=
  R.symm.case_A_BP (by linear_combination h)

theorem case_B_AQ (R : Reps p q u₁ w₁ u₂ w₂)
    (h : (u₁ * w₂ + w₁ * u₂) ^ 2 + (q : ℤ) ^ 2 * w₁ ^ 2 = (w₁ * u₂ - u₁ * w₂) ^ 2) : False :=
  R.symm.case_B_AP (by linear_combination h)

theorem case_Q_AB (R : Reps p q u₁ w₁ u₂ w₂)
    (h : (u₁ * w₂ + w₁ * u₂) ^ 2 + (w₁ * u₂ - u₁ * w₂) ^ 2 = (q : ℤ) ^ 2 * w₁ ^ 2) : False :=
  R.symm.case_P_AB (by linear_combination h)

theorem case_Q_AP (R : Reps p q u₁ w₁ u₂ w₂) (hA : (u₁ * w₂ + w₁ * u₂) ^ 2 ≠ 0)
    (h : (u₁ * w₂ + w₁ * u₂) ^ 2 + (p : ℤ) ^ 2 * w₂ ^ 2 = (q : ℤ) ^ 2 * w₁ ^ 2) : False :=
  R.symm.case_P_AQ (by convert hA using 1; ring) (by linear_combination h)

theorem case_Q_BP (R : Reps p q u₁ w₁ u₂ w₂) (hB : (w₁ * u₂ - u₁ * w₂) ^ 2 ≠ 0)
    (h : (w₁ * u₂ - u₁ * w₂) ^ 2 + (p : ℤ) ^ 2 * w₂ ^ 2 = (q : ℤ) ^ 2 * w₁ ^ 2) : False :=
  R.symm.case_P_BQ (by convert hB using 1; ring) (by linear_combination h)

/-- A representation `o² + v² = (pq)²` with `p ∣ o` and `o` odd has `v² = p² w₂²`. -/
theorem classify_dvd (R : Reps p q u₁ w₁ u₂ w₂) {o v : ℤ}
    (h : o ^ 2 + v ^ 2 = ((p : ℤ) * q) ^ 2) (ho : Odd o) (hv : v ≠ 0) (hpo : (p : ℤ) ∣ o) :
    v ^ 2 = (p : ℤ) ^ 2 * w₂ ^ 2 := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp R.hp
  have hqi : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp R.hq
  have hpv : (p : ℤ) ∣ v := by
    refine hpi.dvd_of_dvd_pow (n := 2) ?_
    rw [show v ^ 2 = (p : ℤ) ^ 2 * q ^ 2 - o ^ 2 by linear_combination h]
    exact dvd_sub (dvd_mul_of_dvd_left (dvd_pow_self _ two_ne_zero) _) (dvd_pow hpo two_ne_zero)
  obtain ⟨o', rfl⟩ := hpo
  obtain ⟨v', rfl⟩ := hpv
  have hp0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ hpi.ne_zero
  have h' : o' ^ 2 + v' ^ 2 = (q : ℤ) ^ 2 := by
    have : (p : ℤ) ^ 2 * (o' ^ 2 + v' ^ 2) = (p : ℤ) ^ 2 * (q : ℤ) ^ 2 := by
      linear_combination h
    exact mul_left_cancel₀ hp0 this
  have ho' : Odd o' := (Int.odd_mul.mp ho).2
  have hv' : v' ≠ 0 := by rintro rfl; simp at hv
  have hqo : ¬ (q : ℤ) ∣ o' := by
    intro hqo
    have hqv : (q : ℤ) ∣ v' := by
      refine hqi.dvd_of_dvd_pow (n := 2) ?_
      rw [show v' ^ 2 = (q : ℤ) ^ 2 - o' ^ 2 by linear_combination h']
      exact dvd_sub (dvd_pow_self _ two_ne_zero) (dvd_pow hqo two_ne_zero)
    have := Int.le_of_dvd (by positivity) (pow_dvd_pow_of_dvd hqv 2)
    have : o' ^ 2 ≤ 0 := by linarith
    exact ne_zero_of_odd ho' (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (sq_nonneg _)))
  rcases sq_add_sq_unique R.hq R.hq2 two_pos h' R.h₂ hqo R.hqu with ⟨-, h2⟩ | ⟨h2, -⟩
  · rw [mul_pow, h2]
  · exact absurd h2 (sq_ne_sq_of_odd_of_even ho' R.even_w₂)

/-- **Classification.** The even member `v` of a representation `o² + v² = (pq)²` with `o` odd
satisfies one of four equations. -/
theorem classify (R : Reps p q u₁ w₁ u₂ w₂) {o v : ℤ} (h : o ^ 2 + v ^ 2 = ((p : ℤ) * q) ^ 2)
    (ho : Odd o) (hv : v ≠ 0) :
    v ^ 2 = (u₁ * w₂ + w₁ * u₂) ^ 2 ∨ v ^ 2 = (w₁ * u₂ - u₁ * w₂) ^ 2 ∨
      v ^ 2 = (p : ℤ) ^ 2 * w₂ ^ 2 ∨ v ^ 2 = (q : ℤ) ^ 2 * w₁ ^ 2 := by
  by_cases hpo : (p : ℤ) ∣ o
  · exact Or.inr (Or.inr (Or.inl (R.classify_dvd h ho hv hpo)))
  by_cases hqo : (q : ℤ) ∣ o
  · exact Or.inr (Or.inr (Or.inr
      (R.symm.classify_dvd (by rw [mul_comm]; exact h) ho hv hqo)))
  obtain ⟨X, Y, hXY, ho', hv'⟩ := sq_add_sq_factor R.hp R.hp2 R.h₁ R.hpu
    (by rw [h, mul_pow]) hpo
  have hX : Odd X := by
    rw [← Int.not_even_iff_odd]
    intro hX
    rw [ho'] at ho
    exact Int.not_even_iff_odd.mpr ho ((hX.mul_left u₁).sub (R.even_w₁.mul_right Y))
  have hqX : ¬ (q : ℤ) ∣ X := by
    intro hqX
    have hqi : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp R.hq
    have hqY : (q : ℤ) ∣ Y := by
      refine hqi.dvd_of_dvd_pow (n := 2) ?_
      rw [show Y ^ 2 = (q : ℤ) ^ 2 - X ^ 2 by linear_combination hXY]
      exact dvd_sub (dvd_pow_self _ two_ne_zero) (dvd_pow hqX two_ne_zero)
    exact hqo (ho' ▸ dvd_sub (dvd_mul_of_dvd_right hqX _) (dvd_mul_of_dvd_right hqY _))
  rcases sq_add_sq_unique R.hq R.hq2 two_pos hXY R.h₂ hqX R.hqu with ⟨h1, h2⟩ | ⟨h1, -⟩
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with rfl | rfl <;>
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with rfl | rfl
    · exact Or.inl (by rw [hv']; ring)
    · exact Or.inr (Or.inl (by rw [hv']; ring))
    · exact Or.inr (Or.inl (by rw [hv']; ring))
    · exact Or.inl (by rw [hv']; ring)
  · exact absurd h1 (sq_ne_sq_of_odd_of_even hX R.even_w₂)

end Reps

namespace Cuboid

variable {a b c d e f g : ℤ}

/-- **Korec, Theorem 5.1, two primes (primitive case).** -/
theorem not_prime_mul_prime (C : Cuboid a b c d e f g) {p q : ℕ} {u₁ w₁ u₂ w₂ : ℤ}
    (R : Reps p q u₁ w₁ u₂ w₂) (hg : g = (p : ℤ) * q) : False := by
  subst hg
  have hf0 : f ^ 2 ≠ 0 := pow_ne_zero _ C.f_ne_zero
  have hb0 : b ^ 2 ≠ 0 := pow_ne_zero _ C.pos_b.ne'
  have hc0 : c ^ 2 ≠ 0 := pow_ne_zero _ C.pos_c.ne'
  have hF := R.classify C.af C.odd_a C.f_ne_zero
  have hB := R.classify C.eb C.odd_e C.pos_b.ne'
  have hC := R.classify C.dc C.odd_d C.pos_c.ne'
  have hrel := C.hf
  have not_fb (h : f ^ 2 = b ^ 2) : False := hc0 (by linear_combination h + hrel)
  have not_fc (h : f ^ 2 = c ^ 2) : False := hb0 (by linear_combination h + hrel)
  have not_bc (h : b ^ 2 = c ^ 2) : False :=
    sq_ne_two_mul_sq C.pos_b.ne' (y := f) (by linear_combination -hrel - h)
  rcases hF with hF | hF | hF | hF <;> rcases hB with hB | hB | hB | hB <;>
    rcases hC with hC | hC | hC | hC <;>
    first
    | exact not_fb (hF.trans hB.symm)
    | exact not_fc (hF.trans hC.symm)
    | exact not_bc (hB.trans hC.symm)
    | rw [hF, hB, hC] at hrel
      rw [hF] at hf0
      rw [hB] at hb0
      rw [hC] at hc0
      first
      | exact R.case_A_BP hrel
      | exact R.case_A_BP (by linear_combination hrel)
      | exact R.case_B_AP hrel
      | exact R.case_B_AP (by linear_combination hrel)
      | exact R.case_P_AB hrel
      | exact R.case_P_AB (by linear_combination hrel)
      | exact R.case_A_BQ hrel
      | exact R.case_A_BQ (by linear_combination hrel)
      | exact R.case_B_AQ hrel
      | exact R.case_B_AQ (by linear_combination hrel)
      | exact R.case_Q_AB hrel
      | exact R.case_Q_AB (by linear_combination hrel)
      | exact R.case_A_PQ hrel
      | exact R.case_A_PQ (by linear_combination hrel)
      | exact R.case_B_PQ hrel
      | exact R.case_B_PQ (by linear_combination hrel)
      | exact R.case_P_AQ hb0 hrel
      | exact R.case_P_AQ hc0 (by linear_combination hrel)
      | exact R.case_P_BQ hb0 hrel
      | exact R.case_P_BQ hc0 (by linear_combination hrel)
      | exact R.case_Q_AP hb0 hrel
      | exact R.case_Q_AP hc0 (by linear_combination hrel)
      | exact R.case_Q_BP hb0 hrel
      | exact R.case_Q_BP hc0 (by linear_combination hrel)

end Cuboid

end PerfectCuboid.Korec

namespace PerfectCuboid.IsPerfectCuboid

open Korec

variable {a b c : ℕ}

/-- **Korec, Theorem 5.1 (first part).** The space diagonal of a perfect cuboid is not a prime
power. -/
theorem ne_prime_pow (h : IsPerfectCuboid a b c) {g : ℕ} (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : g ≠ p ^ k := by
  rintro rfl
  obtain ⟨a', b', c', g', h', hp', hg', hdvd⟩ := exists_primitive_dvd h hg
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, C⟩ := exists_cuboid h' hp' hg'
  exact C.not_prime_pow hp (by push_cast; rfl)

/-- **Korec, Theorem 5.1 (second part).** The space diagonal of a perfect cuboid is not a product
of two primes. -/
theorem ne_prime_mul_prime (h : IsPerfectCuboid a b c) {g : ℕ}
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) : g ≠ p * q := by
  rintro rfl
  by_cases hpq : p = q
  · subst hpq
    exact h.ne_prime_pow hg hp 2 (by ring)
  obtain ⟨a', b', c', g', h', hp', hg', hdvd⟩ := exists_primitive_dvd h hg
  obtain ⟨k₁, k₂, hk₁, hk₂, rfl⟩ := Nat.dvd_mul.mp hdvd
  rcases (Nat.dvd_prime hp).mp hk₁ with h₁ | h₁ <;>
    rcases (Nat.dvd_prime hq).mp hk₂ with h₂ | h₂ <;> rw [h₁, h₂] at hg'
  · exact h'.ne_prime_pow hg' hp 0 (by simp)
  · exact h'.ne_prime_pow hg' hq 1 (by simp)
  · exact h'.ne_prime_pow hg' hp 1 (by simp)
  have hp4 := h'.prime_dvd_space_diagonal hp' hg' hp (dvd_mul_right _ _)
  have hq4 := h'.prime_dvd_space_diagonal hp' hg' hq (dvd_mul_left _ _)
  obtain ⟨u₁, w₁, h₁, hpu, ou₁, ew₁⟩ := exists_rep hp hp4
  obtain ⟨u₂, w₂, h₂, hqu, ou₂, ew₂⟩ := exists_rep hq hq4
  have R : Reps p q u₁ w₁ u₂ w₂ :=
    ⟨hp, hq, by omega, by omega, hpq, h₁, h₂, hpu, hqu, ou₁, ew₁, ou₂, ew₂⟩
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, C⟩ := exists_cuboid h' hp' hg'
  exact C.not_prime_mul_prime R (by push_cast; rfl)

end PerfectCuboid.IsPerfectCuboid
