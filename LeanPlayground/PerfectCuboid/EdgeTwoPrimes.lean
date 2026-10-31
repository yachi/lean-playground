module

public import LeanPlayground.PerfectCuboid.EdgePrimePower

/-!
# Every edge of a perfect cuboid has at least three distinct prime factors

I. Korec (*Nonexistence of a small perfect rational cuboid*, Acta Math. Univ. Comenian. 44/45
(1984), 39–48) proved that an edge of a perfect cuboid is not a prime power, and excluded the
two-prime edges `p^m q^n` only under side conditions (as listed by R. van Luijk, *On perfect
cuboids*, 2000, §2: `p ≡ q ≡ 3 (mod 4)`, or `m = 1`, or `n = 1`, or `m + n ≤ 4`; and `2^m q^n`
with `q ≡ 3 (mod 4)`, or `m ≤ 3`, or `n = 1`). Here we remove all side conditions.

## Main results

* `IsPerfectCuboid.edge_ne_two_prime_pow` (and `_b`, `_c`): no edge of a perfect cuboid equals
  `p ^ k * q ^ l` for primes `p ≠ q` and any `k, l ≥ 0` (so also no edge is `2^s p^k`, and the
  prime-power case of `EdgePrimePower.lean` is re-proved). No primitivity is assumed.
* `IsPerfectCuboid.three_le_primeFactors_card`: every edge has at least three distinct prime
  factors; `IsPerfectCuboid.two_le_oddPrimeFactors_card`: at least two odd ones;
  `IsPerfectCuboid.three_le_oddPrimeFactors_card_of_odd`: an odd edge has three odd ones.
* `res_no_solution`: the *residual equation* `(U² − X²)(V²Y² − 1) = (UV − XY)²` (written as the
  Pythagorean relation `(XVY − U)² + (UV − XY)² = (UVY − X)²`) has no solution with
  `U = p^a, V = p^b, X = q^c, Y = q^d`, `p ≠ q` primes, `a, b, d > 0`.
* `config_false`: the exponent form of the main theorem.

## The proof

Let `x = p^k q^l` be the edge and `(x, yₘ, zₘ)` (`m = 1, 2, 3`) the three right triangles with
leg `x`: `y₁, y₂` are the other two edges and `y₃` the face diagonal through them, so
`y₁² + y₂² = y₃²`. Put `tₘ = zₘ − yₘ`, `uₘ = zₘ + yₘ`; then `tₘ uₘ = x²`, so `tₘ = p^iₘ q^jₘ`,
`uₘ = p^aₘ q^bₘ` with `iₘ + aₘ = 2k`, `jₘ + bₘ = 2l`, and `Yₘ := 2yₘ = uₘ − tₘ` satisfy
`Y₁² + Y₂² = Y₃²`.

1. *Valuation rigidity.* `p^min(iₘ, aₘ) ∣ Yₘ`, and if `iₘ ≠ aₘ` then `p^(min(iₘ, aₘ)+1) ∤ Yₘ`.
   In `Y₁² + Y₂² = Y₃²` no index can carry a strictly smallest exact power of `p`; hence either
   `iₘ = aₘ = k` for all `m`, or the minimum of `min(iₘ, aₘ)` is `< k` and is attained at two
   indices (`two_min`). The same holds at `q`.
2. *Order facts.* `t₃ < t₁, t₂` (the hypotenuse leg is longest), `tₘ < uₘ'` for all `m, m'`
   (`tₘ < x < uₘ'`), `t₁ ≠ t₂` (else `y₃² = 2y₁²`), and, by the divisor inequality
   `inv_sq_add_inv_sq_gt` of `EdgePrimePower.lean`, `t₃` does not divide both `t₁` and `t₂`.
   Since `p^i q^j ≤ p^i' q^j'` when `i ≤ i'`, `j ≤ j'`, all these become *linear* conditions on
   the twelve exponents.
3. *Case tree* (`two_min`, `caseA0`, …, `case23_12`; every leaf is closed by `omega`). The index
   sets attaining the minimum at `p` and at `q` share an index `m*`; it is not `3`, and
   `t_m* = g·p^0 q^(2N)` or `g·p^(2M) q^0` (`g = p^s q^σ` the common part). The only survivors
   are eight *RES shapes*; e.g. `t₁ = g p^e`, `t₂ = g q^(2N)`, `t₃ = g q^c`, which after
   removing `g` is exactly RES with `U = p^e`, `V = p^(2M−e)`, `X = q^c`, `Y = q^(2N−c)`.
4. *RES has no solutions* (`res_core`). From the equation, `U ≠ X` and the sign of the right side,
   `U > X`. Reducing the equation modulo `X` and modulo `U` (coprime) gives
   `X ∣ V²Y² − V² − 1` and `U ∣ V²Y² + Y² − 1`; with `X, Y²` (resp. `U, V²`) comparable under
   divisibility this gives `X ∣ V² + 1` or `Y² ∣ V² + 1`, and `U ∣ Y² − 1` or `V² ∣ Y² − 1`.
   If `UV > XY`, the equation as an inequality gives `X > 2Y² − 4 ≥ Y²`, whence `Y² ∣ V² + 1`
   and `V² ∣ Y² − 1`, i.e. `Y² = V² + 1`: impossible. If `UV < XY` it gives `X ≥ 2V²`, whence
   `Y² ∣ V² + 1`, while `V < Y`: again `Y² = V² + 1`. (`UV = XY` forces `U = X`.)

The third triangle `(x, y₃, z₃)` (the one through the space diagonal) is used essentially: the
leg `Y₃` enters the valuation rule and the divisor inequality. Without it the statement is false:
the face cuboid `(104, 153, 672)` has the two-prime edges `104 = 2³·13`, `153 = 3²·17`.
Positivity of `y₁, y₂, y₃` is used only through `tₘ < uₘ` and `t₃ < t₁, t₂`; degenerate boxes
`(a, b, 0)` fail exactly there.
-/

@[expose] public section

namespace PerfectCuboid

/-- **The residual equation has no solutions (core inequality/divisibility argument).**
Let `U, X > 0`, `V, Y ≥ 2` be integers with `U ≠ X`, `U, X` coprime, and suppose `U` is
comparable with `V²` and `X` with `Y²` under divisibility (as happens when `U, V` are powers of
one prime and `X, Y` powers of another). Then `(XVY − U)² + (UV − XY)² ≠ (UVY − X)²`. -/
theorem res_core {U V X Y : ℤ} (hU : 0 < U) (hX : 0 < X) (hV : 2 ≤ V) (hY : 2 ≤ Y)
    (hUX : U ≠ X) (hcop : IsCoprime U X) (hXY : X ∣ Y ^ 2 ∨ Y ^ 2 ∣ X)
    (hUV : U ∣ V ^ 2 ∨ V ^ 2 ∣ U)
    (h : (X * V * Y - U) ^ 2 + (U * V - X * Y) ^ 2 = (U * V * Y - X) ^ 2) : False := by
  have E1 : (U ^ 2 - X ^ 2) * (V ^ 2 * Y ^ 2 - 1) = (U * V - X * Y) ^ 2 := by
    linear_combination -h
  have hV2 : 4 ≤ V ^ 2 := by nlinarith
  have hY2 : 4 ≤ Y ^ 2 := by nlinarith
  have hVY : 0 < V ^ 2 * Y ^ 2 - 1 := by nlinarith
  -- Step 0: `U > X`.
  have hUX' : X < U := by
    by_contra hle
    push Not at hle
    have : U ^ 2 < X ^ 2 := by
      have := lt_of_le_of_ne hle hUX
      nlinarith
    nlinarith [sq_nonneg (U * V - X * Y), mul_pos (by linarith : (0:ℤ) < X ^ 2 - U ^ 2) hVY]
  have hU1 : X + 1 ≤ U := hUX'
  have hgap : 2 * X + 1 ≤ U ^ 2 - X ^ 2 := by nlinarith
  -- Step 1: divisibilities.
  have dX : X ∣ V ^ 2 * Y ^ 2 - V ^ 2 - 1 := by
    have h1 : X ∣ U ^ 2 * (V ^ 2 * Y ^ 2 - V ^ 2 - 1) :=
      ⟨X * (V ^ 2 * Y ^ 2 + Y ^ 2 - 1) - 2 * U * V * Y, by linear_combination E1⟩
    exact (hcop.symm.pow_right (n := 2)).dvd_of_dvd_mul_left h1
  have dU : U ∣ V ^ 2 * Y ^ 2 + Y ^ 2 - 1 := by
    have h1 : U ∣ X ^ 2 * (V ^ 2 * Y ^ 2 + Y ^ 2 - 1) :=
      ⟨U * (V ^ 2 * Y ^ 2 - V ^ 2 - 1) + 2 * X * V * Y, by linear_combination -E1⟩
    exact (hcop.pow_right (n := 2)).dvd_of_dvd_mul_left h1
  have dX1 : X ∣ Y ^ 2 → X ∣ V ^ 2 + 1 := fun h' ↦ by
    have := dvd_sub (Dvd.dvd.mul_left h' (V ^ 2)) dX
    rwa [show V ^ 2 * Y ^ 2 - (V ^ 2 * Y ^ 2 - V ^ 2 - 1) = V ^ 2 + 1 by ring] at this
  have dX2 : Y ^ 2 ∣ X → Y ^ 2 ∣ V ^ 2 + 1 := fun h' ↦ by
    have := dvd_sub (dvd_mul_left (Y ^ 2) (V ^ 2)) (dvd_trans h' dX)
    rwa [show V ^ 2 * Y ^ 2 - (V ^ 2 * Y ^ 2 - V ^ 2 - 1) = V ^ 2 + 1 by ring] at this
  have dU1 : U ∣ V ^ 2 → U ∣ Y ^ 2 - 1 := fun h' ↦ by
    have := dvd_sub dU (Dvd.dvd.mul_right h' (Y ^ 2))
    rwa [show V ^ 2 * Y ^ 2 + Y ^ 2 - 1 - V ^ 2 * Y ^ 2 = Y ^ 2 - 1 by ring] at this
  have dU2 : V ^ 2 ∣ U → V ^ 2 ∣ Y ^ 2 - 1 := fun h' ↦ by
    have := dvd_sub (dvd_trans h' dU) (dvd_mul_right (V ^ 2) (Y ^ 2))
    rwa [show V ^ 2 * Y ^ 2 + Y ^ 2 - 1 - V ^ 2 * Y ^ 2 = Y ^ 2 - 1 by ring] at this
  have final : ∀ {V Y : ℤ}, 2 ≤ V → V ^ 2 + 1 = Y ^ 2 → False := by
    intro V Y hV h
    have hYV : V < |Y| := by
      have : V ^ 2 < |Y| ^ 2 := by rw [sq_abs]; omega
      nlinarith [abs_nonneg Y]
    nlinarith [sq_abs Y]
  rcases lt_trichotomy (U * V) (X * Y) with hlt | heq | hgt
  · -- Case ii
    have h1 : (U ^ 2 - X ^ 2) * (V ^ 2 * Y ^ 2 - 1) < X ^ 2 * Y ^ 2 := by
      rw [E1]; nlinarith [mul_pos hU (by linarith : (0:ℤ) < V)]
    have h2 : (2 * X + 1) * (V ^ 2 * Y ^ 2 - 1) < X ^ 2 * Y ^ 2 := by nlinarith
    have hX2 : 2 * V ^ 2 ≤ X := by
      by_contra hc
      push Not at hc
      have : X ^ 2 * Y ^ 2 ≤ X * (2 * V ^ 2 - 1) * Y ^ 2 := by
        have : X ≤ 2 * V ^ 2 - 1 := by linarith
        have := mul_le_mul_of_nonneg_left this hX.le
        nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0:ℤ) ≤ Y ^ 2)]
      nlinarith
    have hYV : Y ^ 2 ∣ V ^ 2 + 1 := by
      rcases hXY with d | d
      · have := Int.le_of_dvd (by positivity) (dX1 d); nlinarith
      · exact dX2 d
    have hVY' : V < Y := by
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_left hc hU.le]
    have := Int.le_of_dvd (by positivity) hYV
    exact final hV (by nlinarith)
  · have : (U ^ 2 - X ^ 2) * (V ^ 2 * Y ^ 2 - 1) = 0 := by rw [E1, heq]; ring
    rcases mul_eq_zero.1 this with h0 | h0
    · nlinarith
    · linarith
  · -- Case i
    have h1 : (U ^ 2 - X ^ 2) * (V ^ 2 * Y ^ 2 - 1) < U ^ 2 * V ^ 2 := by
      rw [E1]; nlinarith [mul_pos hX (by linarith : (0:ℤ) < Y)]
    have h2 : (U ^ 2 - X ^ 2) * (Y ^ 2 - 1) < U ^ 2 := by
      have : (U ^ 2 - X ^ 2) * (Y ^ 2 - 1) * V ^ 2 < U ^ 2 * V ^ 2 := by
        nlinarith [mul_pos (by linarith : (0:ℤ) < U ^ 2 - X ^ 2) (by linarith : (0:ℤ) < V ^ 2 - 1)]
      exact lt_of_mul_lt_mul_right this (by positivity)
    have h3 : 2 * (Y ^ 2 - 2) < X := by
      have : (X + 1) ^ 2 * (Y ^ 2 - 2) ≤ U ^ 2 * (Y ^ 2 - 2) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
      nlinarith
    have hXY2 : Y ^ 2 < X := by linarith
    have hYV : Y ^ 2 ∣ V ^ 2 + 1 := by
      rcases hXY with d | d
      · have := Int.le_of_dvd (by positivity) d; linarith
      · exact dX2 d
    have hVY : V ^ 2 ∣ Y ^ 2 - 1 := by
      rcases hUV with d | d
      · have := Int.le_of_dvd (by linarith) (dU1 d); linarith
      · exact dU2 d
    have := Int.le_of_dvd (by positivity) hYV
    have := Int.le_of_dvd (by linarith) hVY
    exact final hV (by linarith)


/-- A monomial `p ^ i * q ^ j`, viewed in `ℤ`. -/
def mn (p q i j : ℕ) : ℤ := (p : ℤ) ^ i * (q : ℤ) ^ j

theorem mn_comm (p q i j : ℕ) : mn p q i j = mn q p j i := mul_comm _ _

theorem mn_pos {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (i j : ℕ) : 0 < mn p q i j := by
  unfold mn; have := hp.pos; have := hq.pos; positivity

theorem mn_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {i j i' j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') :
    mn p q i j ≤ mn p q i' j' := by
  unfold mn
  have h1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
  have h2 : (1 : ℤ) ≤ q := by exact_mod_cast hq.one_lt.le
  exact mul_le_mul (pow_le_pow_right₀ h1 hi) (pow_le_pow_right₀ h2 hj) (by positivity)
    (by positivity)

theorem mn_dvd {p q i j i' j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') : mn p q i j ∣ mn p q i' j' :=
  mul_dvd_mul (pow_dvd_pow _ hi) (pow_dvd_pow _ hj)

/-- Strict inequality between monomials excludes the reverse exponent inequalities. -/
theorem not_le_le_of_mn_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {i j i' j' : ℕ}
    (h : mn p q i j < mn p q i' j') : ¬ (i' ≤ i ∧ j' ≤ j) :=
  fun ⟨h1, h2⟩ ↦ absurd (mn_le hp hq h1 h2) (not_le.2 h)

theorem int_not_dvd_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (n : ℕ) :
    ¬ (p : ℤ) ∣ (q : ℤ) ^ n := by
  intro h
  have h' : p ∣ q ^ n := Int.ofNat_dvd.mp (by exact_mod_cast h)
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h'))

theorem mn_sub_swap (p q a b i j : ℕ) :
    mn p q a b - mn p q i j = (q : ℤ) ^ b * (p : ℤ) ^ a - (q : ℤ) ^ j * (p : ℤ) ^ i := by
  unfold mn; ring

/-! ### The residual equation for prime powers -/

/-- **RES has no solutions.** For distinct primes `p, q` and positive exponents, with
`U = p^a, V = p^b, X = q^c, Y = q^d`: `(XVY − U)² + (UV − XY)² ≠ (UVY − X)²`, i.e.
`(U² − X²)(V²Y² − 1) ≠ (UV − XY)²`. -/
theorem res_no_solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    ((q : ℤ) ^ c * (p : ℤ) ^ b * (q : ℤ) ^ d - (p : ℤ) ^ a) ^ 2 +
      ((p : ℤ) ^ a * (p : ℤ) ^ b - (q : ℤ) ^ c * (q : ℤ) ^ d) ^ 2 ≠
      ((p : ℤ) ^ a * (p : ℤ) ^ b * (q : ℤ) ^ d - (q : ℤ) ^ c) ^ 2 := by
  intro h
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
  have pow2 : ∀ {r : ℤ} {n : ℕ}, 2 ≤ r → 0 < n → 2 ≤ r ^ n := fun hr hn ↦
    le_trans (by simpa using hr) (pow_le_pow_right₀ (by linarith) hn)
  have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)
  have hcop' : IsCoprime ((p : ℤ) ^ a) ((q : ℤ) ^ c) := hcop.pow
  refine res_core (U := (p : ℤ) ^ a) (V := (p : ℤ) ^ b) (X := (q : ℤ) ^ c) (Y := (q : ℤ) ^ d)
    (by positivity) (by positivity) (pow2 hp2 hb) (pow2 hq2 hd) ?_ hcop' ?_ ?_ h
  · intro he
    rw [he] at hcop'
    rcases Int.isUnit_iff.1 (isCoprime_self.1 hcop') with h1 | h1
    · have := pow2 hp2 ha; rw [he, h1] at this; norm_num at this
    · have : (0 : ℤ) < (q : ℤ) ^ c := by positivity
      linarith
  · rw [← pow_mul]
    rcases le_total c (d * 2) with h1 | h1
    · exact Or.inl (pow_dvd_pow _ h1)
    · exact Or.inr (pow_dvd_pow _ h1)
  · rw [← pow_mul]
    rcases le_total a (b * 2) with h1 | h1
    · exact Or.inl (pow_dvd_pow _ h1)
    · exact Or.inr (pow_dvd_pow _ h1)

/-- **The RES shape.** The three divisor pairs `(tₘ, uₘ)` of `x² = p^(2(s+M)) q^(2(σ+N))` given by
`t₁ = p^(s+a) q^σ`, `t₂ = p^s q^(σ+c+d)`, `t₃ = p^s q^(σ+c)` (with `a + b = 2M`, `c + d = 2N`)
never satisfy `(u₁ − t₁)² + (u₂ − t₂)² = (u₃ − t₃)²`: after removing `g = p^s q^σ` this is RES. -/
theorem res_shape {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {I1 J1 A1 B1 I2 J2 A2 B2 I3 J3 A3 B3 s σ a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (h1 : I1 = s + a) (h2 : J1 = σ) (h3 : A1 = s + b) (h4 : B1 = σ + c + d)
    (h5 : I2 = s) (h6 : J2 = σ + c + d) (h7 : A2 = s + a + b) (h8 : B2 = σ)
    (h9 : I3 = s) (h10 : J3 = σ + c) (h11 : A3 = s + a + b) (h12 : B3 = σ + d)
    (key : (mn p q A1 B1 - mn p q I1 J1) ^ 2 + (mn p q A2 B2 - mn p q I2 J2) ^ 2 =
      (mn p q A3 B3 - mn p q I3 J3) ^ 2) : False := by
  subst I1 J1 A1 B1 I2 J2 A2 B2 I3 J3 A3 B3
  unfold mn at key
  apply res_no_solution hp hq hpq ha hb hd (c := c)
  have hg : ((p : ℤ) ^ s * (q : ℤ) ^ σ) ^ 2 ≠ 0 := by
    have := hp.pos; have := hq.pos; positivity
  refine mul_left_cancel₀ hg ?_
  simp only [pow_add] at key
  linear_combination key

/-! ### Valuations -/

theorem pow_min_dvd_form (r : ℕ) {i a : ℕ} (A B : ℤ) :
    (r : ℤ) ^ (min i a) ∣ (r : ℤ) ^ a * A - (r : ℤ) ^ i * B :=
  dvd_sub (Dvd.dvd.mul_right (pow_dvd_pow _ (min_le_right _ _)) _)
    (Dvd.dvd.mul_right (pow_dvd_pow _ (min_le_left _ _)) _)

theorem not_pow_min_succ_dvd_form {r : ℕ} (hr : r.Prime) {i a : ℕ} {A B : ℤ}
    (hA : ¬ (r : ℤ) ∣ A) (hB : ¬ (r : ℤ) ∣ B) (hne : i ≠ a) :
    ¬ (r : ℤ) ^ (min i a + 1) ∣ (r : ℤ) ^ a * A - (r : ℤ) ^ i * B := by
  intro h
  have hr0 : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne_zero
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [min_eq_left hlt.le] at h
    have h1 : (r : ℤ) ^ (i + 1) ∣ (r : ℤ) ^ a * A :=
      Dvd.dvd.mul_right (pow_dvd_pow _ hlt) _
    have h2 := (dvd_sub_right h1).1 h
    rw [pow_succ] at h2
    exact hB ((mul_dvd_mul_iff_left (pow_ne_zero _ hr0)).1 h2)
  · rw [min_eq_right hlt.le] at h
    have h1 : (r : ℤ) ^ (a + 1) ∣ (r : ℤ) ^ i * B :=
      Dvd.dvd.mul_right (pow_dvd_pow _ hlt) _
    have h2 := (dvd_sub_left h1).1 h
    rw [pow_succ] at h2
    exact hA ((mul_dvd_mul_iff_left (pow_ne_zero _ hr0)).1 h2)

/-- **Valuation rigidity + "the minimum is attained twice".** If `Y` is determined by `Y'` and
`Y''` up to divisibility (`P ∣ Y' → P ∣ Y'' → P ∣ Y`), then the exact power `r^(min i a)` of
`Y = r^a A − r^i B` (`i ≠ a`) cannot be strictly smaller than the powers dividing `Y'`, `Y''`. -/
theorem val_fact {r : ℕ} (hr : r.Prime) {Y Y' Y'' A B A' B' A'' B'' : ℤ}
    {i a i' a' i'' a'' : ℕ} (hA : ¬ (r : ℤ) ∣ A) (hB : ¬ (r : ℤ) ∣ B)
    (hY : Y = (r : ℤ) ^ a * A - (r : ℤ) ^ i * B) (hY' : Y' = (r : ℤ) ^ a' * A' - (r : ℤ) ^ i' * B')
    (hY'' : Y'' = (r : ℤ) ^ a'' * A'' - (r : ℤ) ^ i'' * B'')
    (hdiv : ∀ P : ℤ, P ∣ Y' → P ∣ Y'' → P ∣ Y) :
    ¬ (i ≠ a ∧ min i a < min i' a' ∧ min i a < min i'' a'') := by
  rintro ⟨hne, h1, h2⟩
  apply not_pow_min_succ_dvd_form hr hA hB hne
  rw [← hY]
  apply hdiv
  · rw [hY']; exact dvd_trans (pow_dvd_pow _ h1) (pow_min_dvd_form r A' B')
  · rw [hY'']; exact dvd_trans (pow_dvd_pow _ h2) (pow_min_dvd_form r A'' B'')

/-! ### Elementary order facts -/

theorem t_lt_of_sq_lt {T1 U1 T3 U3 : ℤ} (hT1 : 0 < T1) (hT3 : 0 < T3) (h : T1 * U1 = T3 * U3)
    (h1 : T1 < U1) (h3 : T3 < U3) (hs : (U1 - T1) ^ 2 < (U3 - T3) ^ 2) : T3 < T1 := by
  by_contra hc
  push Not at hc
  have hU : U3 ≤ U1 := by nlinarith
  nlinarith

theorem t_lt_u {T U T' U' : ℤ} (hT : 0 < T) (hT' : 0 < T') (h : T * U = T' * U') (h1 : T < U)
    (h2 : T' < U') : T < U' := by
  nlinarith

theorem sq_ne_two_mul_sq_int {x y : ℤ} (hy : y ≠ 0) : x ^ 2 ≠ 2 * y ^ 2 := by
  intro h
  have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  have e : (2 : ℝ) = ((x : ℝ) / y) ^ 2 := by
    rw [div_pow, eq_div_iff (by positivity)]
    exact_mod_cast h.symm
  have hirr : Irrational √((2 : ℕ) : ℝ) := Nat.Prime.irrational_sqrt Nat.prime_two
  exact hirr ⟨|(x : ℚ) / y|, by push_cast; rw [e, Real.sqrt_sq_eq_abs]⟩

/-- The divisor inequality excludes `t₃ ∣ t₁`, `t₃ ∣ t₂` (with `t₃ < t₁, t₂`). -/
theorem not_dvd_both {t1 t2 t3 : ℤ} (h : (t1 * t2) ^ 2 < t3 ^ 2 * (t1 ^ 2 + t2 ^ 2))
    (h3 : 0 < t3) (h31 : t3 < t1) (h32 : t3 < t2) (d1 : t3 ∣ t1) (d2 : t3 ∣ t2) : False := by
  obtain ⟨v, rfl⟩ := d1
  obtain ⟨w, rfl⟩ := d2
  have hv : 2 ≤ v := by by_contra hc; push Not at hc; nlinarith
  have hw : 2 ≤ w := by by_contra hc; push Not at hc; nlinarith
  have h4 : 0 < t3 ^ 4 := by positivity
  have : t3 ^ 4 * (v ^ 2 * w ^ 2) < t3 ^ 4 * (v ^ 2 + w ^ 2) := by linear_combination h
  have := lt_of_mul_lt_mul_left this h4.le
  nlinarith [mul_nonneg (by nlinarith : (0:ℤ) ≤ v ^ 2 - 4) (by nlinarith : (0:ℤ) ≤ w ^ 2 - 4)]


/-! ### The case tree, in exponent arithmetic

Write `tₘ = p^iₘ q^jₘ` and `uₘ = p^aₘ q^bₘ` with `iₘ + aₘ = 2k`, `jₘ + bₘ = 2l`. All facts below
are linear in the exponents, and `omega` closes each branch. -/

/-- "The minimum is attained twice": the `p`-adic exponents `min(iₘ, aₘ)` either all equal `k`
(no leg has a `p`-adic jump below `k`) or their minimum is `< k` and attained at two indices. -/
theorem two_min {k i1 i2 i3 a1 a2 a3 : ℕ}
    (e1 : i1 + a1 = 2 * k) (e2 : i2 + a2 = 2 * k) (e3 : i3 + a3 = 2 * k)
    (v1 : ¬ (i1 ≠ a1 ∧ min i1 a1 < min i2 a2 ∧ min i1 a1 < min i3 a3))
    (v2 : ¬ (i2 ≠ a2 ∧ min i2 a2 < min i1 a1 ∧ min i2 a2 < min i3 a3))
    (v3 : ¬ (i3 ≠ a3 ∧ min i3 a3 < min i1 a1 ∧ min i3 a3 < min i2 a2)) :
    (i1 = a1 ∧ i2 = a2 ∧ i3 = a3) ∨
    (min i1 a1 = min i2 a2 ∧ min i1 a1 ≤ min i3 a3 ∧ min i1 a1 < k) ∨
    (min i1 a1 = min i3 a3 ∧ min i1 a1 ≤ min i2 a2 ∧ min i1 a1 < k) ∨
    (min i2 a2 = min i3 a3 ∧ min i2 a2 ≤ min i1 a1 ∧ min i2 a2 < k) := by
  omega

section CaseTree

variable {k l i1 i2 i3 j1 j2 j3 a1 a2 a3 b1 b2 b3 : ℕ}
    (e1 : i1 + a1 = 2 * k) (e2 : i2 + a2 = 2 * k) (e3 : i3 + a3 = 2 * k)
    (f1 : j1 + b1 = 2 * l) (f2 : j2 + b2 = 2 * l) (f3 : j3 + b3 = 2 * l)
    (h11 : ¬ (a1 ≤ i1 ∧ b1 ≤ j1)) (h12 : ¬ (a2 ≤ i1 ∧ b2 ≤ j1)) (h13 : ¬ (a3 ≤ i1 ∧ b3 ≤ j1))
    (h21 : ¬ (a1 ≤ i2 ∧ b1 ≤ j2)) (h22 : ¬ (a2 ≤ i2 ∧ b2 ≤ j2)) (h23 : ¬ (a3 ≤ i2 ∧ b3 ≤ j2))
    (h31 : ¬ (a1 ≤ i3 ∧ b1 ≤ j3)) (h32 : ¬ (a2 ≤ i3 ∧ b2 ≤ j3)) (h33 : ¬ (a3 ≤ i3 ∧ b3 ≤ j3))
    (g1 : ¬ (i1 ≤ i3 ∧ j1 ≤ j3)) (g2 : ¬ (i2 ≤ i3 ∧ j2 ≤ j3)) (g12 : ¬ (i1 = i2 ∧ j1 = j2))
    (hineq : ¬ (i3 ≤ i1 ∧ j3 ≤ j1 ∧ i3 ≤ i2 ∧ j3 ≤ j2))
include e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq

set_option linter.unusedSectionVars false

/-- No `p`-adic jump below `k` at all: then two legs coincide. -/
theorem caseA0 (hA : i1 = a1 ∧ i2 = a2 ∧ i3 = a3)
    (w1 : ¬ (j1 ≠ b1 ∧ min j1 b1 < min j2 b2 ∧ min j1 b1 < min j3 b3))
    (w2 : ¬ (j2 ≠ b2 ∧ min j2 b2 < min j1 b1 ∧ min j2 b2 < min j3 b3))
    (w3 : ¬ (j3 ≠ b3 ∧ min j3 b3 < min j1 b1 ∧ min j3 b3 < min j2 b2)) : False := by
  omega

theorem caseB0 (hB : j1 = b1 ∧ j2 = b2 ∧ j3 = b3)
    (v1 : ¬ (i1 ≠ a1 ∧ min i1 a1 < min i2 a2 ∧ min i1 a1 < min i3 a3))
    (v2 : ¬ (i2 ≠ a2 ∧ min i2 a2 < min i1 a1 ∧ min i2 a2 < min i3 a3))
    (v3 : ¬ (i3 ≠ a3 ∧ min i3 a3 < min i1 a1 ∧ min i3 a3 < min i2 a2)) : False := by
  omega

theorem case12_12 (hA : min i1 a1 = min i2 a2 ∧ min i1 a1 ≤ min i3 a3 ∧ min i1 a1 < k)
    (hB : min j1 b1 = min j2 b2 ∧ min j1 b1 ≤ min j3 b3 ∧ min j1 b1 < l) : False := by
  omega

theorem case13_13 (hA : min i1 a1 = min i3 a3 ∧ min i1 a1 ≤ min i2 a2 ∧ min i1 a1 < k)
    (hB : min j1 b1 = min j3 b3 ∧ min j1 b1 ≤ min j2 b2 ∧ min j1 b1 < l) : False := by
  omega

theorem case23_23 (hA : min i2 a2 = min i3 a3 ∧ min i2 a2 ≤ min i1 a1 ∧ min i2 a2 < k)
    (hB : min j2 b2 = min j3 b3 ∧ min j2 b2 ≤ min j1 b1 ∧ min j2 b2 < l) : False := by
  omega

theorem case13_23 (hA : min i1 a1 = min i3 a3 ∧ min i1 a1 ≤ min i2 a2 ∧ min i1 a1 < k)
    (hB : min j2 b2 = min j3 b3 ∧ min j2 b2 ≤ min j1 b1 ∧ min j2 b2 < l) : False := by
  omega

theorem case23_13 (hA : min i2 a2 = min i3 a3 ∧ min i2 a2 ≤ min i1 a1 ∧ min i2 a2 < k)
    (hB : min j1 b1 = min j3 b3 ∧ min j1 b1 ≤ min j2 b2 ∧ min j1 b1 < l) : False := by
  omega

theorem case12_13 (hA : min i1 a1 = min i2 a2 ∧ min i1 a1 ≤ min i3 a3 ∧ min i1 a1 < k)
    (hB : min j1 b1 = min j3 b3 ∧ min j1 b1 ≤ min j2 b2 ∧ min j1 b1 < l) :
    (j3 = j1 ∧ i2 = a1 ∧ j1 < j2 ∧ j2 < b1 ∧ a1 < i3 ∧ i3 < i1) ∨
    (i2 = i1 ∧ j3 = b1 ∧ b1 < j2 ∧ j2 < j1 ∧ i1 < i3 ∧ i3 < a1) := by
  rcases le_total i1 a1 with hi | hi <;> rcases le_total j1 b1 with hj | hj
  · exfalso; omega
  · right; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · left; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exfalso; omega

theorem case12_23 (hA : min i1 a1 = min i2 a2 ∧ min i1 a1 ≤ min i3 a3 ∧ min i1 a1 < k)
    (hB : min j2 b2 = min j3 b3 ∧ min j2 b2 ≤ min j1 b1 ∧ min j2 b2 < l) :
    (i1 = i2 ∧ j3 = b2 ∧ b2 < j1 ∧ j1 < j2 ∧ i2 < i3 ∧ i3 < a2) ∨
    (j3 = j2 ∧ i1 = a2 ∧ j2 < j1 ∧ j1 < b2 ∧ a2 < i3 ∧ i3 < i2) := by
  rcases le_total i2 a2 with hi | hi <;> rcases le_total j2 b2 with hj | hj
  · exfalso; omega
  · left; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · right; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exfalso; omega

theorem case13_12 (hA : min i1 a1 = min i3 a3 ∧ min i1 a1 ≤ min i2 a2 ∧ min i1 a1 < k)
    (hB : min j1 b1 = min j2 b2 ∧ min j1 b1 ≤ min j3 b3 ∧ min j1 b1 < l) :
    (i3 = i1 ∧ j2 = b1 ∧ i1 < i2 ∧ i2 < a1 ∧ b1 < j3 ∧ j3 < j1) ∨
    (j2 = j1 ∧ i3 = a1 ∧ a1 < i2 ∧ i2 < i1 ∧ j1 < j3 ∧ j3 < b1) := by
  rcases le_total i1 a1 with hi | hi <;> rcases le_total j1 b1 with hj | hj
  · exfalso; omega
  · left; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · right; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exfalso; omega

theorem case23_12 (hA : min i2 a2 = min i3 a3 ∧ min i2 a2 ≤ min i1 a1 ∧ min i2 a2 < k)
    (hB : min j1 b1 = min j2 b2 ∧ min j1 b1 ≤ min j3 b3 ∧ min j1 b1 < l) :
    (i3 = i2 ∧ j1 = b2 ∧ i2 < i1 ∧ i1 < a2 ∧ b2 < j3 ∧ j3 < j2) ∨
    (j1 = j2 ∧ i3 = a2 ∧ a2 < i1 ∧ i1 < i2 ∧ j2 < j3 ∧ j3 < b2) := by
  rcases le_total i2 a2 with hi | hi <;> rcases le_total j2 b2 with hj | hj
  · exfalso; omega
  · left; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · right; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exfalso; omega

end CaseTree


/-- **Main lemma (exponent form).** Let `p ≠ q` be primes, `x = p^k q^l`, and let
`tₘ = p^iₘ q^jₘ < uₘ = p^aₘ q^bₘ` (`iₘ + aₘ = 2k`, `jₘ + bₘ = 2l`, so `tₘ uₘ = x²`) for
`m = 1, 2, 3`. Then `(u₁ − t₁)² + (u₂ − t₂)² ≠ (u₃ − t₃)²`. -/
theorem config_false {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {k l i1 i2 i3 j1 j2 j3 a1 a2 a3 b1 b2 b3 : ℕ}
    (e1 : i1 + a1 = 2 * k) (e2 : i2 + a2 = 2 * k) (e3 : i3 + a3 = 2 * k)
    (f1 : j1 + b1 = 2 * l) (f2 : j2 + b2 = 2 * l) (f3 : j3 + b3 = 2 * l)
    (lt1 : mn p q i1 j1 < mn p q a1 b1) (lt2 : mn p q i2 j2 < mn p q a2 b2)
    (lt3 : mn p q i3 j3 < mn p q a3 b3)
    (key : (mn p q a1 b1 - mn p q i1 j1) ^ 2 + (mn p q a2 b2 - mn p q i2 j2) ^ 2 =
      (mn p q a3 b3 - mn p q i3 j3) ^ 2) : False := by
  have pos := mn_pos hp hq
  have prod : ∀ {i a j b : ℕ}, i + a = 2 * k → j + b = 2 * l →
      mn p q i j * mn p q a b = mn p q (2 * k) (2 * l) := by
    intro i a j b h1 h2; unfold mn; rw [← h1, ← h2]; ring
  have P1 := prod e1 f1
  have P2 := prod e2 f2
  have P3 := prod e3 f3
  -- order facts: `t₃ < t₁, t₂` and `tₘ < uₘ'`
  have hY1 : 0 < mn p q a1 b1 - mn p q i1 j1 := by linarith
  have hY2 : 0 < mn p q a2 b2 - mn p q i2 j2 := by linarith
  have t31 : mn p q i3 j3 < mn p q i1 j1 :=
    t_lt_of_sq_lt (pos _ _) (pos _ _) (P1.trans P3.symm) lt1 lt3 (by nlinarith [pow_pos hY2 2])
  have t32 : mn p q i3 j3 < mn p q i2 j2 :=
    t_lt_of_sq_lt (pos _ _) (pos _ _) (P2.trans P3.symm) lt2 lt3 (by nlinarith [pow_pos hY1 2])
  have cr : ∀ {i a j b i' a' j' b' : ℕ}, mn p q i j * mn p q a b = mn p q i' j' * mn p q a' b' →
      mn p q i j < mn p q a b → mn p q i' j' < mn p q a' b' → ¬ (a' ≤ i ∧ b' ≤ j) :=
    fun h h1 h2 ↦ not_le_le_of_mn_lt hp hq (t_lt_u (pos _ _) (pos _ _) h h1 h2)
  have h11 := cr (P1.trans P1.symm) lt1 lt1
  have h12 := cr (P1.trans P2.symm) lt1 lt2
  have h13 := cr (P1.trans P3.symm) lt1 lt3
  have h21 := cr (P2.trans P1.symm) lt2 lt1
  have h22 := cr (P2.trans P2.symm) lt2 lt2
  have h23 := cr (P2.trans P3.symm) lt2 lt3
  have h31 := cr (P3.trans P1.symm) lt3 lt1
  have h32 := cr (P3.trans P2.symm) lt3 lt2
  have h33 := cr (P3.trans P3.symm) lt3 lt3
  have g1 := not_le_le_of_mn_lt hp hq t31
  have g2 := not_le_le_of_mn_lt hp hq t32
  -- `t₁ ≠ t₂` (else `f² = 2b²`)
  have g12 : ¬ (i1 = i2 ∧ j1 = j2) := by
    rintro ⟨rfl, rfl⟩
    obtain rfl : a1 = a2 := by omega
    obtain rfl : b1 = b2 := by omega
    exact sq_ne_two_mul_sq_int (x := mn p q a3 b3 - mn p q i3 j3) hY1.ne'
      (by linear_combination -key)
  -- the divisor inequality
  have hineq : ¬ (i3 ≤ i1 ∧ j3 ≤ j1 ∧ i3 ≤ i2 ∧ j3 ≤ j2) := by
    rintro ⟨h1, h2, h3, h4⟩
    exact not_dvd_both (inv_sq_add_inv_sq_gt P1 P2 P3 (pos _ _) (pos _ _) (pos _ _) lt1 lt2 key).2
      (pos _ _) t31 t32 (mn_dvd h1 h2) (mn_dvd h3 h4)
  -- valuations
  have dv3 : ∀ P : ℤ, P ∣ mn p q a1 b1 - mn p q i1 j1 → P ∣ mn p q a2 b2 - mn p q i2 j2 →
      P ∣ mn p q a3 b3 - mn p q i3 j3 := fun P h1 h2 ↦
    (Int.pow_dvd_pow_iff two_ne_zero).1 (key ▸ dvd_add (pow_dvd_pow_of_dvd h1 2)
      (pow_dvd_pow_of_dvd h2 2))
  have dv1 : ∀ P : ℤ, P ∣ mn p q a2 b2 - mn p q i2 j2 → P ∣ mn p q a3 b3 - mn p q i3 j3 →
      P ∣ mn p q a1 b1 - mn p q i1 j1 := fun P h2 h3 ↦ by
    refine (Int.pow_dvd_pow_iff two_ne_zero).1 ?_
    rw [show (mn p q a1 b1 - mn p q i1 j1) ^ 2 = (mn p q a3 b3 - mn p q i3 j3) ^ 2 -
      (mn p q a2 b2 - mn p q i2 j2) ^ 2 by linear_combination key]
    exact dvd_sub (pow_dvd_pow_of_dvd h3 2) (pow_dvd_pow_of_dvd h2 2)
  have dv2 : ∀ P : ℤ, P ∣ mn p q a1 b1 - mn p q i1 j1 → P ∣ mn p q a3 b3 - mn p q i3 j3 →
      P ∣ mn p q a2 b2 - mn p q i2 j2 := fun P h1 h3 ↦ by
    refine (Int.pow_dvd_pow_iff two_ne_zero).1 ?_
    rw [show (mn p q a2 b2 - mn p q i2 j2) ^ 2 = (mn p q a3 b3 - mn p q i3 j3) ^ 2 -
      (mn p q a1 b1 - mn p q i1 j1) ^ 2 by linear_combination key]
    exact dvd_sub (pow_dvd_pow_of_dvd h3 2) (pow_dvd_pow_of_dvd h1 2)
  have np := int_not_dvd_pow hp hq hpq
  have nq := int_not_dvd_pow hq hp hpq.symm
  have v1 := val_fact hp (np b1) (np j1) rfl rfl rfl dv1
  have v2 := val_fact hp (np b2) (np j2) rfl rfl rfl dv2
  have v3 := val_fact hp (np b3) (np j3) rfl rfl rfl dv3
  have w1 := val_fact hq (nq a1) (nq i1) (mn_sub_swap ..) (mn_sub_swap ..) (mn_sub_swap ..) dv1
  have w2 := val_fact hq (nq a2) (nq i2) (mn_sub_swap ..) (mn_sub_swap ..) (mn_sub_swap ..) dv2
  have w3 := val_fact hq (nq a3) (nq i3) (mn_sub_swap ..) (mn_sub_swap ..) (mn_sub_swap ..) dv3
  -- the eight residual shapes are all RES
  have S1 : (i3 = i2 ∧ j1 = b2 ∧ i2 < i1 ∧ i1 < a2 ∧ b2 < j3 ∧ j3 < j2) → False := fun h ↦
    res_shape hp hq hpq (I1 := i1) (J1 := j1) (A1 := a1) (B1 := b1) (I2 := i2) (J2 := j2)
        (A2 := a2) (B2 := b2) (I3 := i3) (J3 := j3) (A3 := a3) (B3 := b3)
      (s := i2) (σ := b2) (a := (i1-i2)) (b := (a1-i2)) (c := (j3-b2)) (d := (b3-b2))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S2 : (i1 = i2 ∧ j3 = b2 ∧ b2 < j1 ∧ j1 < j2 ∧ i2 < i3 ∧ i3 < a2) → False := fun h ↦
    res_shape hq hp hpq.symm (I1 := j1) (J1 := i1) (A1 := b1) (B1 := a1) (I2 := b2) (J2 := a2)
        (A2 := j2) (B2 := i2) (I3 := j3) (J3 := i3) (A3 := b3) (B3 := a3)
      (s := b2) (σ := i2) (a := (j1-b2)) (b := (b1-b2)) (c := (i3-i2)) (d := (a3-i2))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S3 : (i3 = i1 ∧ j2 = b1 ∧ i1 < i2 ∧ i2 < a1 ∧ b1 < j3 ∧ j3 < j1) → False := fun h ↦
    res_shape hp hq hpq (I1 := i2) (J1 := j2) (A1 := a2) (B1 := b2) (I2 := i1) (J2 := j1)
        (A2 := a1) (B2 := b1) (I3 := i3) (J3 := j3) (A3 := a3) (B3 := b3)
      (s := i1) (σ := b1) (a := (i2-i1)) (b := (a2-i1)) (c := (j3-b1)) (d := (b3-b1))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S4 : (i2 = i1 ∧ j3 = b1 ∧ b1 < j2 ∧ j2 < j1 ∧ i1 < i3 ∧ i3 < a1) → False := fun h ↦
    res_shape hq hp hpq.symm (I1 := j2) (J1 := i2) (A1 := b2) (B1 := a2) (I2 := b1) (J2 := a1)
        (A2 := j1) (B2 := i1) (I3 := j3) (J3 := i3) (A3 := b3) (B3 := a3)
      (s := b1) (σ := i1) (a := (j2-b1)) (b := (b2-b1)) (c := (i3-i1)) (d := (a3-i1))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S5 : (j3 = j2 ∧ i1 = a2 ∧ j2 < j1 ∧ j1 < b2 ∧ a2 < i3 ∧ i3 < i2) → False := fun h ↦
    res_shape hq hp hpq.symm (I1 := j1) (J1 := i1) (A1 := b1) (B1 := a1) (I2 := j2) (J2 := i2)
        (A2 := b2) (B2 := a2) (I3 := j3) (J3 := i3) (A3 := b3) (B3 := a3)
      (s := j2) (σ := a2) (a := (j1-j2)) (b := (b1-j2)) (c := (i3-a2)) (d := (a3-a2))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S6 : (j1 = j2 ∧ i3 = a2 ∧ a2 < i1 ∧ i1 < i2 ∧ j2 < j3 ∧ j3 < b2) → False := fun h ↦
    res_shape hp hq hpq (I1 := i1) (J1 := j1) (A1 := a1) (B1 := b1) (I2 := a2) (J2 := b2)
        (A2 := i2) (B2 := j2) (I3 := i3) (J3 := j3) (A3 := a3) (B3 := b3)
      (s := a2) (σ := j2) (a := (i1-a2)) (b := (a1-a2)) (c := (j3-j2)) (d := (b3-j2))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S7 : (j3 = j1 ∧ i2 = a1 ∧ j1 < j2 ∧ j2 < b1 ∧ a1 < i3 ∧ i3 < i1) → False := fun h ↦
    res_shape hq hp hpq.symm (I1 := j2) (J1 := i2) (A1 := b2) (B1 := a2) (I2 := j1) (J2 := i1)
        (A2 := b1) (B2 := a1) (I3 := j3) (J3 := i3) (A3 := b3) (B3 := a3)
      (s := j1) (σ := a1) (a := (j2-j1)) (b := (b2-j1)) (c := (i3-a1)) (d := (a3-a1))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S8 : (j2 = j1 ∧ i3 = a1 ∧ a1 < i2 ∧ i2 < i1 ∧ j1 < j3 ∧ j3 < b1) → False := fun h ↦
    res_shape hp hq hpq (I1 := i2) (J1 := j2) (A1 := a2) (B1 := b2) (I2 := a1) (J2 := b1)
        (A2 := i1) (B2 := j1) (I3 := i3) (J3 := j3) (A3 := a3) (B3 := b3)
      (s := a1) (σ := j1) (a := (i2-a1)) (b := (a2-a1)) (c := (j3-j1)) (d := (b3-j1))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  rcases two_min e1 e2 e3 v1 v2 v3 with hA | hA | hA | hA
  · exact caseA0 e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA w1 w2 w3
  all_goals rcases two_min f1 f2 f3 w1 w2 w3 with hB | hB | hB | hB
  all_goals first
    | exact caseB0 e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hB v1 v2 v3
    | exact case12_12 e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA hB
    | exact case13_13 e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA hB
    | exact case23_23 e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA hB
    | exact case13_23 e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA hB
    | exact case23_13 e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA hB
    | exact
        (case12_13 e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA
        hB).elim S7 S4
    | exact
        (case12_23 e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA
        hB).elim S2 S5
    | exact
        (case13_12 e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA
        hB).elim S3 S8
    | exact
        (case23_12 e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA
        hB).elim S1 S6


/-! ### From the cuboid to the exponent configuration -/

/-- **Shape of a leg.** If `(p^k q^l)² + y² = z²` with `y > 0`, then `z − y = p^i q^j` and
`z + y = p^a q^b` with `i + a = 2k`, `j + b = 2l`, so `2y = p^a q^b − p^i q^j`. -/
theorem leg_two {p q k l y z : ℕ} (hp : p.Prime) (hq : q.Prime) (hy : 0 < y)
    (h : (p ^ k * q ^ l) ^ 2 + y ^ 2 = z ^ 2) :
    ∃ i a j b, i + a = 2 * k ∧ j + b = 2 * l ∧ mn p q i j < mn p q a b ∧
      (2 * y : ℤ) = mn p q a b - mn p q i j := by
  have hx : 0 < p ^ k * q ^ l := by have := hp.pos; have := hq.pos; positivity
  have hyz : y < z := by
    have : y ^ 2 < z ^ 2 := by rw [← h]; have := pow_pos hx 2; omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hmul : (z - y) * (z + y) = p ^ (2 * k) * q ^ (2 * l) := by
    have h1 := Nat.sq_sub_sq z y
    have h2 : z ^ 2 - y ^ 2 = (p ^ k * q ^ l) ^ 2 := by omega
    rw [mul_comm, ← h1, h2, mul_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l]
  obtain ⟨t1, t2, ht1, ht2, ht⟩ := dvd_mul.1 (Dvd.intro _ hmul)
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 ht1
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hq).1 ht2
  have hu : z + y = p ^ (2 * k - i) * q ^ (2 * l - j) := by
    have hpos : 0 < p ^ i * q ^ j := by have := hp.pos; have := hq.pos; positivity
    have e : p ^ i * q ^ j * (p ^ (2 * k - i) * q ^ (2 * l - j)) = p ^ (2 * k) * q ^ (2 * l) := by
      rw [mul_mul_mul_comm, ← pow_add, ← pow_add, Nat.add_sub_cancel' hi, Nat.add_sub_cancel' hj]
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [e, ← hmul, ht]
  have hT : mn p q i j = (z : ℤ) - y := by
    unfold mn; rw [← Nat.cast_sub hyz.le, ht]; push_cast; ring
  have hU : mn p q (2 * k - i) (2 * l - j) = (z : ℤ) + y := by
    unfold mn; rw [show ((z : ℤ) + y) = ((z + y : ℕ) : ℤ) by push_cast; ring, hu]; push_cast; ring
  refine ⟨i, 2 * k - i, j, 2 * l - j, by omega, by omega, ?_, ?_⟩
  · rw [hT, hU]; have : (0 : ℤ) < y := by exact_mod_cast hy
    linarith
  · rw [hT, hU]; ring

/-- **Main theorem.** The first edge of a perfect cuboid is not of the form `p^k q^l` with
`p ≠ q` primes (any `k, l ≥ 0`). No primitivity assumption; `p = 2` or `q = 2` is allowed. -/
theorem IsPerfectCuboid.edge_ne_two_prime_pow {a b c : ℕ} (h : IsPerfectCuboid a b c)
    {p q k l : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : a ≠ p ^ k * q ^ l := by
  rintro rfl
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ca
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  have hb0 := h.pos_b
  have hc0 := h.pos_c
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · subst h0; nlinarith
    · exact h0
  obtain ⟨i1, a1, j1, b1, e1, f1, lt1, Y1⟩ := leg_two hp hq hb0 (z := d) (by rw [hd]; ring)
  obtain ⟨i2, a2, j2, b2, e2, f2, lt2, Y2⟩ := leg_two hp hq hc0 (z := e)
    (by rw [add_comm, he]; ring)
  obtain ⟨i3, a3, j3, b3, e3, f3, lt3, Y3⟩ := leg_two (k := k) (l := l) (z := g) hp hq hf0
    (by rw [sq f, ← hf, sq g, ← hg]; ring)
  refine config_false hp hq hpq e1 e2 e3 f1 f2 f3 lt1 lt2 lt3 ?_
  rw [← Y1, ← Y2, ← Y3]
  have : ((b : ℤ) ^ 2 + c ^ 2) = f ^ 2 := by exact_mod_cast (by rw [hf]; ring)
  linear_combination 4 * this

/-- The second edge of a perfect cuboid is not of the form `p^k q^l`. -/
theorem IsPerfectCuboid.edge_ne_two_prime_pow_b {a b c : ℕ} (h : IsPerfectCuboid a b c)
    {p q k l : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : b ≠ p ^ k * q ^ l :=
  IsPerfectCuboid.edge_ne_two_prime_pow (a := b) (b := c) (c := a)
    ⟨h.toIsEulerBrick.rotate, by have := h.sq_abc; rwa [show b ^ 2 + c ^ 2 + a ^ 2 =
      a ^ 2 + b ^ 2 + c ^ 2 by ring]⟩ hp hq hpq

/-- The third edge of a perfect cuboid is not of the form `p^k q^l`. -/
theorem IsPerfectCuboid.edge_ne_two_prime_pow_c {a b c : ℕ} (h : IsPerfectCuboid a b c)
    {p q k l : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : c ≠ p ^ k * q ^ l :=
  IsPerfectCuboid.edge_ne_two_prime_pow (a := c) (b := a) (c := b)
    ⟨h.toIsEulerBrick.rotate.rotate, by have := h.sq_abc; rwa [show c ^ 2 + a ^ 2 + b ^ 2 =
      a ^ 2 + b ^ 2 + c ^ 2 by ring]⟩ hp hq hpq

/-- A positive integer that is not of the form `p^k q^l` (`p ≠ q` primes, `k, l ≥ 0`) has at
least three distinct prime factors. -/
theorem three_le_card_primeFactors_of {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p q k l : ℕ, p.Prime → q.Prime → p ≠ q → n ≠ p ^ k * q ^ l) :
    3 ≤ n.primeFactors.card := by
  by_contra hlt
  have hprod := Nat.prod_primeFactors_pow_factorization hn
  rcases (by omega : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨
      n.primeFactors.card = 2) with hc | hc | hc
  · rw [Finset.card_eq_zero.1 hc, Finset.prod_empty] at hprod
    exact h 2 3 0 0 Nat.prime_two Nat.prime_three (by norm_num) (by simp [hprod])
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.1 hc
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors (hr ▸ Finset.mem_singleton_self r)
    rw [hr, Finset.prod_singleton] at hprod
    by_cases h2 : r = 2
    · exact h r 3 (n.factorization r) 0 hrp Nat.prime_three (by omega)
        (by rw [pow_zero, mul_one]; exact hprod)
    · exact h r 2 (n.factorization r) 0 hrp Nat.prime_two h2
        (by rw [pow_zero, mul_one]; exact hprod)
  · obtain ⟨r, s, hrs, hr⟩ := Finset.card_eq_two.1 hc
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors (by rw [hr]; simp)
    have hsp : s.Prime := Nat.prime_of_mem_primeFactors (by rw [hr]; simp)
    rw [hr, Finset.prod_pair hrs] at hprod
    exact h r s _ _ hrp hsp hrs hprod

/-- **Every edge of a perfect cuboid has at least three distinct prime factors.** -/
theorem IsPerfectCuboid.three_le_primeFactors_card {a b c : ℕ} (h : IsPerfectCuboid a b c) :
    3 ≤ a.primeFactors.card ∧ 3 ≤ b.primeFactors.card ∧ 3 ≤ c.primeFactors.card :=
  ⟨three_le_card_primeFactors_of h.pos_a.ne' fun _ _ _ _ hp hq hpq ↦
      h.edge_ne_two_prime_pow hp hq hpq,
    three_le_card_primeFactors_of h.pos_b.ne' fun _ _ _ _ hp hq hpq ↦
      h.edge_ne_two_prime_pow_b hp hq hpq,
    three_le_card_primeFactors_of h.pos_c.ne' fun _ _ _ _ hp hq hpq ↦
      h.edge_ne_two_prime_pow_c hp hq hpq⟩

/-- Every edge of a perfect cuboid has at least two odd prime factors; an odd edge has at
least three. -/
theorem IsPerfectCuboid.two_le_oddPrimeFactors_card {a b c : ℕ} (h : IsPerfectCuboid a b c) :
    2 ≤ (a.primeFactors.erase 2).card ∧ 2 ≤ (b.primeFactors.erase 2).card ∧
      2 ≤ (c.primeFactors.erase 2).card := by
  obtain ⟨ha, hb, hc⟩ := h.three_le_primeFactors_card
  refine ⟨?_, ?_, ?_⟩ <;> [have := Finset.pred_card_le_card_erase (s := a.primeFactors) (a := 2);
    have := Finset.pred_card_le_card_erase (s := b.primeFactors) (a := 2);
    have := Finset.pred_card_le_card_erase (s := c.primeFactors) (a := 2)] <;> omega

theorem IsPerfectCuboid.three_le_oddPrimeFactors_card_of_odd {a b c : ℕ}
    (h : IsPerfectCuboid a b c) (ha : Odd a) : 3 ≤ (a.primeFactors.erase 2).card := by
  rw [Finset.erase_eq_of_notMem (fun h2 ↦ by
    have := Nat.dvd_of_mem_primeFactors h2
    exact (Nat.not_even_iff_odd.2 ha) (even_iff_two_dvd.2 this))]
  exact h.three_le_primeFactors_card.1

end PerfectCuboid
