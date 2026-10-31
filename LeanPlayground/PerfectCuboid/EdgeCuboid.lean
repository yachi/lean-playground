module

public import LeanPlayground.PerfectCuboid.Basic
public import LeanPlayground.PerfectCuboid.EdgePrimePower
public import LeanPlayground.PerfectCuboid.Leech

/-!
# Edge cuboids: the irrational edge is not a prime power, and a Leech table

An *edge cuboid* is a box with two integer edges `a, b`, an irrational third edge `√N`
(`N > 0` not a square) and all face diagonals and the space diagonal integral:
`a² + b² = d²`, `a² + N = e²`, `b² + N = f²`, `a² + b² + N = g²`.
Leech's example is `a = 520`, `b = 576`, `N = 618849 = 3²·7·11·19·47` with
`(d, e, f, g) = (776, 943, 975, 1105)`.

## The divisor framework for `N`

`N = e² − a² = f² − b² = g² − d²` has three factorizations `N = tₘuₘ` with `tₘ < uₘ`, and the
three "legs" `(uₘ − tₘ)/2 = a, b, d` satisfy `a² + b² = d²`. This is exactly the structure that
the odd edge `a` of a perfect cuboid has with `N = a²` (legs `b, c, f`). Every argument about
that structure which never uses that `N` is a square transfers.

## Main results

* `three_factorizations_ne_prime_pow` (new in this generality): if `N + x² = X²`,
  `N + y² = Y²`, `N + z² = Z²` and `x² + y² = z²` with `x, y > 0`, then `N` is not a prime power
  `p ^ K`, for any `K` (odd or even) and any prime `p` (including `2`).
* `IsEdgeCuboid.N_ne_prime_pow`: the irrational edge of an edge cuboid is never `√(p ^ K)`.
* `IsPerfectCuboid.edge_ne_prime_pow_of_three_factorizations`: Korec's theorem (an edge of a
  perfect cuboid is not a prime power, `EdgePrimePower.lean`) re-derived as the special case
  `N = a²`.
* `IsEdgeCuboid.t_not_dvd_both`: the transfer of the divisor inequality: `g − d` does not divide
  both `e − a` and `f − b`.
* `edge_leech_dvd`, `IsEdgeCuboid.leech_dvd`: **a Leech table for edge cuboids.**
  `2⁸ · 3⁴ · 5⁴ · 7 · 11 · 13 ∣ a · b · N · d · e · f · g`. The local computation shows that each
  exponent is best possible modulo `p ^ j` for the moduli used, and that no prime `p ≥ 17` is
  forced (unlike `17, 19, 29, 37` for perfect cuboids).
* `edge_two_adic`: for `(a, b, N)` not divisible by `(2, 2, 4)`, either `16 ∣ N` and exactly one
  of `a, b` is odd (the other divisible by `4`), or `N ≡ 1 (mod 8)` and `4 ∣ a`, `4 ∣ b`.

## The proof of `three_factorizations_ne_prime_pow`

If `N = p ^ K` then `(X − x)(X + x) = p ^ K` gives `X − x = p ^ i`, `X + x = p ^ (K − i)` with
`2i < K` (as `x > 0`), so `2x = p ^ i · B` with `B + 1 = p ^ (K − 2i)`; in particular `p ∤ B`.
Likewise `2y = p ^ j · C`, `2z = p ^ l · F`. In `(2x)² + (2y)² = (2z)²` the `p`-adic valuation
forces `l = min(i, j)` when `i ≠ j`; say `l = i`. Then `F = B`, so `z = x` and `y = 0`,
contradicting `y > 0` (this is the only place positivity is used). If `i = j` then `x = y` and
`z² = 2x²`, impossible.

## The Leech table

As in `Leech.lean`, modulo `m = pʲ` we run over the *profiles* `(x² mod m, min(v_p x, j))` of
`a` and `b` and over all residues `N mod m`. The descent is now
`(a, b, N) ↦ (a/p, b/p, N/p²)` (it multiplies the product by `p⁸`), so we may assume
`¬ (p ∣ a ∧ p ∣ b ∧ p² ∣ N)`. Whenever the four sums are squares mod `m`, the capped
valuations of `a, b, N` and the forced valuations of the diagonals add up to at least `k`.
-/

@[expose] public section

namespace PerfectCuboid

/-- An *edge cuboid*: integer edges `a, b`, irrational edge `√N`, all diagonals integral. -/
structure IsEdgeCuboid (a b N : ℕ) : Prop where
  pos_a : 0 < a
  pos_b : 0 < b
  pos_N : 0 < N
  not_square_N : ¬ IsSquare N
  sq_ab : IsSquare (a ^ 2 + b ^ 2)
  sq_aN : IsSquare (a ^ 2 + N)
  sq_bN : IsSquare (b ^ 2 + N)
  sq_abN : IsSquare (a ^ 2 + b ^ 2 + N)

/-- Leech's edge cuboid `(520, 576, √618849)`. -/
theorem isEdgeCuboid_520_576 : IsEdgeCuboid 520 576 618849 where
  pos_a := by norm_num
  pos_b := by norm_num
  pos_N := by norm_num
  not_square_N := by
    rintro ⟨r, hr⟩
    rcases le_or_gt r 786 with h | h
    · have : r * r ≤ 786 * 786 := Nat.mul_le_mul h h
      omega
    · have : 787 * 787 ≤ r * r := Nat.mul_le_mul h h
      omega
  sq_ab := ⟨776, by norm_num⟩
  sq_aN := ⟨943, by norm_num⟩
  sq_bN := ⟨975, by norm_num⟩
  sq_abN := ⟨1105, by norm_num⟩

/-- The integer diagonals of an edge cuboid. -/
theorem IsEdgeCuboid.diagonals {a b N : ℕ} (h : IsEdgeCuboid a b N) :
    ∃ d e f g : ℕ, a ^ 2 + b ^ 2 = d ^ 2 ∧ a ^ 2 + N = e ^ 2 ∧ b ^ 2 + N = f ^ 2 ∧
      a ^ 2 + b ^ 2 + N = g ^ 2 := by
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_aN
  obtain ⟨f, hf⟩ := h.sq_bN
  obtain ⟨g, hg⟩ := h.sq_abN
  exact ⟨d, e, f, g, by rw [hd, sq], by rw [he, sq], by rw [hf, sq], by rw [hg, sq]⟩

/-! ### The irrational edge is not a prime power -/

/-- `x² = 2y²` has no solution with `y > 0`. -/
theorem sq_ne_two_mul_sq' {x y : ℕ} (hy : 0 < y) : x ^ 2 ≠ 2 * y ^ 2 := by
  intro h
  have hirr : Irrational √((2 : ℕ) : ℝ) := Nat.Prime.irrational_sqrt Nat.prime_two
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have e : ((2 : ℕ) : ℝ) = ((x : ℝ) / y) ^ 2 := by
    rw [div_pow, eq_div_iff (by positivity)]
    exact_mod_cast h.symm
  exact hirr ⟨(x : ℚ) / y, by rw [e, Real.sqrt_sq (by positivity)]; push_cast; rfl⟩

/-- **The leg formula for a general exponent.** If `p ^ K + x² = X²` with `x > 0`, then
`2x = p ^ i * B` with `2i < K` and `B + 1 = p ^ (K - 2i)`. -/
theorem leg_of_prime_pow_gen {p K x X : ℕ} (hp : p.Prime) (hx : 0 < x)
    (h : p ^ K + x ^ 2 = X ^ 2) :
    ∃ i, 2 * i < K ∧ ∃ B, 2 * x = p ^ i * B ∧ B + 1 = p ^ (K - 2 * i) := by
  have hpK : 0 < p ^ K := pow_pos hp.pos K
  have hxX : x < X := by
    have : x ^ 2 < X ^ 2 := by omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hmul : (X - x) * (X + x) = p ^ K := by
    have h1 := Nat.sq_sub_sq X x
    have h2 : X ^ 2 - x ^ 2 = p ^ K := by omega
    rw [mul_comm, ← h1, h2]
  obtain ⟨i, hi, h1, h2⟩ := eq_pow_of_mul_eq_pow hp hmul
  have hlt : p ^ i < p ^ (K - i) := by rw [← h1, ← h2]; omega
  have hiK : 2 * i < K := by
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
    omega
  refine ⟨i, hiK, p ^ (K - 2 * i) - 1, ?_, ?_⟩
  · have he : K - i = i + (K - 2 * i) := by omega
    rw [he, pow_add] at h2
    rw [Nat.mul_sub_one]
    have : 2 * x = (X + x) - (X - x) := by omega
    rw [this, h1, h2]
  · exact Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)

/-- **Three factorizations of a prime power.** If `N` has three representations
`N + x² = X²`, `N + y² = Y²`, `N + z² = Z²` whose legs satisfy `x² + y² = z²` with `x, y > 0`,
then `N` is not a prime power. No parity, primitivity or non-square assumption is needed. -/
theorem three_factorizations_ne_prime_pow {N x y z X Y Z : ℕ} (hx0 : 0 < x) (hy0 : 0 < y)
    (hxyz : x ^ 2 + y ^ 2 = z ^ 2) (hX : N + x ^ 2 = X ^ 2) (hY : N + y ^ 2 = Y ^ 2)
    (hZ : N + z ^ 2 = Z ^ 2) {p K : ℕ} (hp : p.Prime) : N ≠ p ^ K := by
  rintro rfl
  have hz0 : 0 < z := by
    rcases Nat.eq_zero_or_pos z with h0 | h0
    · subst h0; nlinarith
    · exact h0
  obtain ⟨i, hi, B, hb, hB⟩ := leg_of_prime_pow_gen hp hx0 hX
  obtain ⟨j, hj, C, hc, hC⟩ := leg_of_prime_pow_gen hp hy0 hY
  obtain ⟨l, hl, F, hf', hF⟩ := leg_of_prime_pow_gen hp hz0 hZ
  have hBp := not_dvd_of_succ_eq_pow hp (by omega) hB
  have hCp := not_dvd_of_succ_eq_pow hp (by omega) hC
  have hFp := not_dvd_of_succ_eq_pow hp (by omega) hF
  have key : (p ^ i * B) ^ 2 + (p ^ j * C) ^ 2 = (p ^ l * F) ^ 2 := by
    rw [← hb, ← hc, ← hf']; nlinarith [hxyz]
  rcases lt_trichotomy i j with hij | rfl | hij
  · -- `l = i`, so `z = x` and `y = 0`
    have hli := exp_eq_of_sq_add_sq hp hBp hFp hij key
    subst hli
    have hFB : F = B := Nat.add_right_cancel (hF.trans hB.symm)
    subst hFB
    have hzx : z = x := by omega
    subst hzx
    have : y ^ 2 = 0 := by omega
    exact hy0.ne' (pow_eq_zero_iff two_ne_zero |>.1 this)
  · -- `x = y`, so `z² = 2x²`
    have hBC : B = C := Nat.add_right_cancel (hB.trans hC.symm)
    subst hBC
    have hxy : x = y := by omega
    subst hxy
    exact sq_ne_two_mul_sq' hx0 (by rw [← hxyz]; ring)
  · have hlj := exp_eq_of_sq_add_sq (B := C) (C := B) hp hCp hFp hij (by rw [add_comm]; exact key)
    subst hlj
    have hFC : F = C := Nat.add_right_cancel (hF.trans hC.symm)
    subst hFC
    have hzy : z = y := by omega
    subst hzy
    have : x ^ 2 = 0 := by omega
    exact hx0.ne' (pow_eq_zero_iff two_ne_zero |>.1 this)

/-- **The irrational edge of an edge cuboid is not `√(p ^ K)`.** -/
theorem IsEdgeCuboid.N_ne_prime_pow {a b N : ℕ} (h : IsEdgeCuboid a b N) {p K : ℕ}
    (hp : p.Prime) : N ≠ p ^ K := by
  obtain ⟨d, e, f, g, hd, he, hf, hg⟩ := h.diagonals
  exact three_factorizations_ne_prime_pow h.pos_a h.pos_b hd (by rw [← he]; ring)
    (by rw [← hf]; ring) (by rw [← hg, ← hd]; ring) hp

/-- **Korec (1984) as a special case.** Taking `N = a²` and the legs `b, c, f`
in `three_factorizations_ne_prime_pow` shows again that the first edge of a perfect cuboid is
not a prime power. -/
theorem IsPerfectCuboid.edge_ne_prime_pow_of_three_factorizations {a b c : ℕ}
    (h : IsPerfectCuboid a b c) {p k : ℕ} (hp : p.Prime) : a ≠ p ^ k := by
  rintro rfl
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ca
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  rw [← sq] at hd he hf hg
  refine three_factorizations_ne_prime_pow (N := (p ^ k) ^ 2) (K := 2 * k) h.pos_b h.pos_c hf hd
    (by rw [← he]; ring) (by rw [← hg, ← hf]; ring) hp ?_
  rw [← pow_mul, mul_comm]

/-! ### Hook for two prime factors (depends on brief 1, round 11)

The analogue of the two-prime theorem for a general `N` would read

```
theorem three_factorizations_ne_two_prime_pow {N x y z X Y Z : ℕ} (hx0 : 0 < x) (hy0 : 0 < y)
    (hxyz : x ^ 2 + y ^ 2 = z ^ 2) (hX : N + x ^ 2 = X ^ 2) (hY : N + y ^ 2 = Y ^ 2)
    (hZ : N + z ^ 2 = Z ^ 2) {p q K L : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    N ≠ p ^ K * q ^ L

theorem IsEdgeCuboid.N_ne_two_prime_pow {a b N : ℕ} (h : IsEdgeCuboid a b N)
    {p q K L : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : N ≠ p ^ K * q ^ L := by
  obtain ⟨d, e, f, g, hd, he, hf, hg⟩ := h.diagonals
  exact three_factorizations_ne_two_prime_pow h.pos_a h.pos_b hd (by rw [← he]; ring)
    (by rw [← hf]; ring) (by rw [← hg, ← hd]; ring) hp hq hpq
```

and is left for the merge with the two-prime file (it is not proved here). It is consistent with
the numerical search: no edge cuboid with `N ≤ 10⁹` has `N` with at most two prime factors. -/

/-! ### The divisor inequality for edge cuboids -/

theorem three_factorizations_t_not_dvd_both {N x y z X Y Z : ℤ} (hx0 : 0 < x) (hy0 : 0 < y)
    (hz0 : 0 ≤ z) (hxyz : x ^ 2 + y ^ 2 = z ^ 2) (hX : N + x ^ 2 = X ^ 2)
    (hY : N + y ^ 2 = Y ^ 2) (hZ : N + z ^ 2 = Z ^ 2) (hN : 0 < N) (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hZ0 : 0 ≤ Z) : ¬ (Z - z ∣ X - x ∧ Z - z ∣ Y - y) := by
  rintro ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
  have hxX : x < X := lt_of_pow_lt_pow_left₀ 2 hX0 (by linarith)
  have hyY : y < Y := lt_of_pow_lt_pow_left₀ 2 hY0 (by linarith)
  have hzZ : z < Z := lt_of_pow_lt_pow_left₀ 2 hZ0 (by linarith)
  have hxz : x < z := lt_of_pow_lt_pow_left₀ 2 hz0 (by nlinarith)
  have hyz : y < z := lt_of_pow_lt_pow_left₀ 2 hz0 (by nlinarith)
  have hXZ : X < Z := lt_of_pow_lt_pow_left₀ 2 hZ0 (by nlinarith)
  have hYZ : Y < Z := lt_of_pow_lt_pow_left₀ 2 hZ0 (by nlinarith)
  have hN1 : (X - x) * (X + x) = N := by linear_combination (-1 : ℤ) * hX
  have hN2 : (Y - y) * (Y + y) = N := by linear_combination (-1 : ℤ) * hY
  have hN3 : (Z - z) * (Z + z) = N := by linear_combination (-1 : ℤ) * hZ
  have ht : 0 < Z - z := by linarith
  -- `Z - z < X - x`, since `(Z - z)(Z + z) = (X - x)(X + x)` and `X + x < Z + z`
  have small {U u : ℤ} (hU : (U - u) * (U + u) = N) (hu : 0 < u) (huU : u < U) (huz : u < z)
      (hUZ : U < Z) : Z - z < U - u := by
    by_contra hc
    push Not at hc
    have h1 : (U - u) * (Z + z) ≤ (Z - z) * (Z + z) :=
      mul_le_mul_of_nonneg_right hc (by linarith)
    have h2 : (U - u) * (U + u) < (U - u) * (Z + z) :=
      mul_lt_mul_of_pos_left (by linarith) (by linarith)
    linarith
  have h13 := small hN1 hx0 hxX hxz hXZ
  have h23 := small hN2 hy0 hyY hyz hYZ
  have big {U u m : ℤ} (hm : U - u = (Z - z) * m) (h : Z - z < U - u) : 2 ≤ m := by
    by_contra hc
    have : m ≤ 1 := by omega
    have := mul_le_mul_of_nonneg_left this ht.le
    linarith
  have hv2 := big hv h13
  have hw2 := big hw h23
  have hineq := (inv_sq_add_inv_sq_gt hN1 hN2 hN3 (by linarith) (by linarith) ht
    (by linarith) (by linarith) (by linear_combination 4 * hxyz)).2
  rw [hv, hw] at hineq
  have h4 : 0 < (Z - z) ^ 4 := by positivity
  have e1 : ((Z - z) * v * ((Z - z) * w)) ^ 2 = (Z - z) ^ 4 * (v ^ 2 * w ^ 2) := by ring
  have e2 : (Z - z) ^ 2 * (((Z - z) * v) ^ 2 + ((Z - z) * w) ^ 2) =
      (Z - z) ^ 4 * (v ^ 2 + w ^ 2) := by ring
  rw [e1, e2] at hineq
  have h5 := lt_of_mul_lt_mul_left hineq h4.le
  have hv4 : 3 ≤ v ^ 2 - 1 := by
    have := mul_le_mul hv2 hv2 (by norm_num) (by linarith); rw [sq]; linarith
  have hw4 : 3 ≤ w ^ 2 - 1 := by
    have := mul_le_mul hw2 hw2 (by norm_num) (by linarith); rw [sq]; linarith
  have := mul_le_mul hv4 hw4 (by norm_num) (by linarith)
  linarith [show (v ^ 2 - 1) * (w ^ 2 - 1) = v ^ 2 * w ^ 2 - (v ^ 2 + w ^ 2) + 1 by ring]

/-- For an edge cuboid, `g − d ∤ gcd(e − a, f − b)`. -/
theorem IsEdgeCuboid.t_not_dvd_both {a b N : ℕ} (h : IsEdgeCuboid a b N) {d e f g : ℕ}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + N = e ^ 2) (hf : b ^ 2 + N = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + N = g ^ 2) :
    ¬ ((g : ℤ) - d ∣ (e : ℤ) - a ∧ (g : ℤ) - d ∣ (f : ℤ) - b) := by
  have he' : N + a ^ 2 = e ^ 2 := by rw [← he]; ring
  have hf' : N + b ^ 2 = f ^ 2 := by rw [← hf]; ring
  have hg' : N + d ^ 2 = g ^ 2 := by rw [← hg, ← hd]; ring
  exact three_factorizations_t_not_dvd_both (N := (N : ℤ)) (by exact_mod_cast h.pos_a)
    (by exact_mod_cast h.pos_b) (by positivity) (by exact_mod_cast hd) (by exact_mod_cast he')
    (by exact_mod_cast hf') (by exact_mod_cast hg') (by exact_mod_cast h.pos_N)
    (by positivity) (by positivity) (by positivity)

end PerfectCuboid

/-! ### A Leech table for edge cuboids -/

namespace PerfectCuboid.EdgeLeech

open PerfectCuboid.Leech

/-- The check for the profiles `a`, `b` of the two integer edges and the residue `N`: unless the
triple is not reduced (`p ∣ a`, `p ∣ b`, `p² ∣ N`) or one of the four sums is a non-square, the
capped valuations of `a, b, N, d, e, f, g` add up to at least `k`. -/
def okE (p j k : ℕ) (L : List (ℕ × ℕ)) (a b : ℕ × ℕ) (N : ℕ) : Bool :=
  let m := p ^ j
  let s₂ := (a.1 + N) % m
  let s₃ := (b.1 + N) % m
  let s₄ := (a.1 + b.1 + N) % m
  (decide (0 < a.2) && decide (0 < b.2) && decide (2 ≤ ev p j N)) ||
    !(isSq L s₂ && isSq L s₃ && isSq L s₄) ||
    decide (k ≤ a.2 + b.2 + ev p j N + hv p j ((a.1 + b.1) % m) + hv p j s₂ + hv p j s₃ +
      hv p j s₄)

/-- Run `okE` over all pairs of profiles whose sum of squares is a square mod `pʲ`, and over all
residues `N`. -/
def checkE (p j k : ℕ) (L : List (ℕ × ℕ)) : Bool :=
  L.all fun a => L.all fun b => !isSq L ((a.1 + b.1) % p ^ j) ||
    (List.range (p ^ j)).all fun N => okE p j k L a b N

/-- `L` contains the profile of every residue modulo `pʲ`. -/
def completeE (p j : ℕ) (L : List (ℕ × ℕ)) : Bool :=
  (List.range (p ^ j)).all fun r => L.contains (r ^ 2 % p ^ j, ev p j r)

section Check

variable {p j k : ℕ} {L : List (ℕ × ℕ)}

theorem mem_LE (hc : completeE p j L = true) (hj : 0 < p ^ j) (x : ℕ) :
    (x ^ 2 % p ^ j, ev p j (x % p ^ j)) ∈ L := by
  have := List.all_eq_true.mp hc (x % p ^ j) (List.mem_range.mpr (Nat.mod_lt _ hj))
  simp only [List.contains_iff_mem] at this
  rw [Nat.pow_mod]
  exact this

theorem isSq_of_eqE (hc : completeE p j L = true) (hj : 0 < p ^ j) {s d : ℕ}
    (h : s = d ^ 2 % p ^ j) : isSq L s = true := by
  rw [isSq, List.any_eq_true, h]
  exact ⟨_, mem_LE hc hj d, by simp⟩

theorem dvd_of_ev_pos {x : ℕ} (h : 0 < ev p j (x % p ^ j)) : p ∣ x :=
  (dvd_pow_self p h.ne').trans (pow_ev_dvd_of_mod p j x)

theorem sq_dvd_of_ev {x : ℕ} (h : 2 ≤ ev p j (x % p ^ j)) : p ^ 2 ∣ x :=
  (pow_dvd_pow p h).trans (pow_ev_dvd_of_mod p j x)

/-- The congruence check gives `pᵏ ∣ abNdefg` for a reduced edge cuboid. -/
theorem dvd_of_checkE (hp : p.Prime) (hU : checkE p j k L = true)
    (hc : completeE p j L = true) {a b N d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + N = e ^ 2) (hf : b ^ 2 + N = f ^ 2) (hg : a ^ 2 + b ^ 2 + N = g ^ 2)
    (hn : ¬ (p ∣ a ∧ p ∣ b ∧ p ^ 2 ∣ N)) :
    p ^ k ∣ a * b * N * d * e * f * g := by
  set m := p ^ j with hm
  have hm0 : 0 < m := pow_pos hp.pos j
  have md (x : ℕ) : Nat.ModEq m (x % m) x := Nat.mod_modEq x m
  have e₁ : (a ^ 2 % m + b ^ 2 % m) % m = d ^ 2 % m := by rw [← hd]; exact (md _).add (md _)
  have e₂ : (a ^ 2 % m + N % m) % m = e ^ 2 % m := by rw [← he]; exact (md _).add (md _)
  have e₃ : (b ^ 2 % m + N % m) % m = f ^ 2 % m := by rw [← hf]; exact (md _).add (md _)
  have e₄ : (a ^ 2 % m + b ^ 2 % m + N % m) % m = g ^ 2 % m := by
    rw [← hg]; exact ((md _).add (md _)).add (md _)
  have hab := List.all_eq_true.mp (List.all_eq_true.mp hU _ (mem_LE hc hm0 a)) _
    (mem_LE hc hm0 b)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hab
  rcases hab with h | h
  · rw [e₁, isSq_of_eqE hc hm0 rfl] at h
    exact absurd h (by simp)
  have hok := List.all_eq_true.mp h (N % m) (List.mem_range.mpr (Nat.mod_lt _ hm0))
  simp only [okE, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hok
  rw [e₁, e₂, e₃, e₄] at hok
  have sq (x : ℕ) : isSq L (x ^ 2 % m) = true := isSq_of_eqE hc hm0 rfl
  rcases hok with (h | h) | h
  · exact absurd ⟨dvd_of_ev_pos h.1.1, dvd_of_ev_pos h.1.2, sq_dvd_of_ev h.2⟩ hn
  · simp [sq] at h
  have hdiv : p ^ (ev p j (a % m) + ev p j (b % m) + ev p j (N % m) + hv p j (d ^ 2 % m) +
      hv p j (e ^ 2 % m) + hv p j (f ^ 2 % m) + hv p j (g ^ 2 % m)) ∣
      a * b * N * d * e * f * g := by
    simp only [pow_add]
    exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul
      (pow_ev_dvd_of_mod p j a) (pow_ev_dvd_of_mod p j b)) (pow_ev_dvd_of_mod p j N))
      (pow_hv_dvd hp)) (pow_hv_dvd hp)) (pow_hv_dvd hp)) (pow_hv_dvd hp)
  exact (pow_dvd_pow p h).trans hdiv

/-- Divide out `(p, p, p²)` from `(a, b, N)` as often as possible. -/
theorem dvd_prodE (hp : p.Prime) (_hj : 0 < j) (hU : checkE p j k L = true)
    (hc : completeE p j L = true) {a b N d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + N = e ^ 2) (hf : b ^ 2 + N = f ^ 2) (hg : a ^ 2 + b ^ 2 + N = g ^ 2) :
    p ^ k ∣ a * b * N * d * e * f * g := by
  induction h : a + b using Nat.strong_induction_on generalizing a b N d e f g with
  | _ n ih =>
  by_cases hn : p ∣ a ∧ p ∣ b ∧ p ^ 2 ∣ N
  swap
  · exact dvd_of_checkE hp hU hc hd he hf hg hn
  obtain ⟨ha, hb, hN⟩ := hn
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : a = 0 := by omega
    simp [this]
  have sq {x y z : ℕ} (hx : p ∣ x) (hy : p ^ 2 ∣ y) (h : x ^ 2 + y = z ^ 2) : p ∣ z := by
    refine hp.dvd_of_dvd_pow (n := 2) (h ▸ dvd_add (dvd_pow hx two_ne_zero) ?_)
    exact (dvd_pow_self p two_ne_zero).trans hy
  have hd' := sq ha (pow_dvd_pow_of_dvd hb 2) hd
  have he' := sq ha hN he
  have hf' := sq hb hN hf
  have hg' := sq hd' hN (hd ▸ hg)
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨N, rfl⟩ := hN
  obtain ⟨d, rfl⟩ := hd'
  obtain ⟨e, rfl⟩ := he'
  obtain ⟨f, rfl⟩ := hf'
  obtain ⟨g, rfl⟩ := hg'
  have p2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  have cancel {x y z : ℕ} (h : (p * x) ^ 2 + p ^ 2 * y = (p * z) ^ 2) : x ^ 2 + y = z ^ 2 :=
    mul_left_cancel₀ p2 (by rw [mul_add, ← mul_pow, ← mul_pow]; exact h)
  have hd₀ : a ^ 2 + b ^ 2 = d ^ 2 :=
    mul_left_cancel₀ p2 (by rw [mul_add, ← mul_pow, ← mul_pow, ← mul_pow]; exact hd)
  have hg₀ : a ^ 2 + b ^ 2 + N = g ^ 2 :=
    mul_left_cancel₀ p2 (by rw [mul_add, mul_add, ← mul_pow, ← mul_pow, ← mul_pow]; exact hg)
  have hlt : a + b < n := by
    have := hp.two_le
    rw [← h] at hn ⊢
    nlinarith
  have := ih _ hlt hd₀ (cancel he) (cancel hf) hg₀ rfl
  have := this.mul_left (p ^ 8)
  rwa [show p ^ 8 * (a * b * N * d * e * f * g) =
    p * a * (p * b) * (p ^ 2 * N) * (p * d) * (p * e) * (p * f) * (p * g) by ring] at this

end Check

/-! #### The tables -/

theorem two_pow_dvd {a b N d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + N = e ^ 2)
    (hf : b ^ 2 + N = f ^ 2) (hg : a ^ 2 + b ^ 2 + N = g ^ 2) :
    2 ^ 8 ∣ a * b * N * d * e * f * g :=
  dvd_prodE (j := 7) (L := L_two) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

/-- Profiles `(x² mod 125, min(v_5(x), 3))`. -/
def L_five : List (ℕ × ℕ) := [(0, 2), (0, 3), (1, 0), (4, 0), (6, 0), (9, 0), (11, 0), (14, 0),
  (16, 0), (19, 0), (21, 0), (24, 0), (25, 1), (26, 0), (29, 0), (31, 0), (34, 0), (36, 0),
  (39, 0), (41, 0), (44, 0), (46, 0), (49, 0), (51, 0), (54, 0), (56, 0), (59, 0), (61, 0),
  (64, 0), (66, 0), (69, 0), (71, 0), (74, 0), (76, 0), (79, 0), (81, 0), (84, 0), (86, 0),
  (89, 0), (91, 0), (94, 0), (96, 0), (99, 0), (100, 1), (101, 0), (104, 0), (106, 0), (109, 0),
  (111, 0), (114, 0), (116, 0), (119, 0), (121, 0), (124, 0)]

theorem three_pow_dvd {a b N d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + N = e ^ 2)
    (hf : b ^ 2 + N = f ^ 2) (hg : a ^ 2 + b ^ 2 + N = g ^ 2) :
    3 ^ 4 ∣ a * b * N * d * e * f * g :=
  dvd_prodE (j := 3) (L := L_three) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

set_option maxHeartbeats 4000000 in -- the 5³ table has 364k cases for `decide +kernel`
theorem five_pow_dvd {a b N d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + N = e ^ 2)
    (hf : b ^ 2 + N = f ^ 2) (hg : a ^ 2 + b ^ 2 + N = g ^ 2) :
    5 ^ 4 ∣ a * b * N * d * e * f * g :=
  dvd_prodE (j := 3) (L := L_five) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

theorem seven_dvd {a b N d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + N = e ^ 2)
    (hf : b ^ 2 + N = f ^ 2) (hg : a ^ 2 + b ^ 2 + N = g ^ 2) :
    7 ^ 1 ∣ a * b * N * d * e * f * g :=
  dvd_prodE (j := 1) (L := L_seven) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

theorem eleven_dvd {a b N d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + N = e ^ 2)
    (hf : b ^ 2 + N = f ^ 2) (hg : a ^ 2 + b ^ 2 + N = g ^ 2) :
    11 ^ 1 ∣ a * b * N * d * e * f * g :=
  dvd_prodE (j := 1) (L := L_eleven) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

theorem thirteen_dvd {a b N d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + N = e ^ 2)
    (hf : b ^ 2 + N = f ^ 2) (hg : a ^ 2 + b ^ 2 + N = g ^ 2) :
    13 ^ 1 ∣ a * b * N * d * e * f * g :=
  dvd_prodE (j := 1) (L := L_thirteen) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

/-- **Leech's divisibility for edge cuboids.** If `a² + b² = d²`, `a² + N = e²`, `b² + N = f²`
and `a² + b² + N = g²`, then `2⁸ · 3⁴ · 5⁴ · 7 · 11 · 13 ∣ a · b · N · d · e · f · g`. -/
theorem edge_leech_dvd {a b N d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + N = e ^ 2)
    (hf : b ^ 2 + N = f ^ 2) (hg : a ^ 2 + b ^ 2 + N = g ^ 2) :
    2 ^ 8 * 3 ^ 4 * 5 ^ 4 * 7 * 11 * 13 ∣ a * b * N * d * e * f * g := by
  have h2 := two_pow_dvd hd he hf hg
  have h3 := three_pow_dvd hd he hf hg
  have h5 := five_pow_dvd hd he hf hg
  have h7 := seven_dvd hd he hf hg
  have h11 := eleven_dvd hd he hf hg
  have h13 := thirteen_dvd hd he hf hg
  simp only [pow_one] at *
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h5
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h7
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h11
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h13

end PerfectCuboid.EdgeLeech

namespace PerfectCuboid

/-! ### The 2-adic shape of an edge cuboid -/

/-- The residues of `(a, b, N)` modulo `m` pass the four square tests. -/
theorem edge_residues {a b N d e f g m : ℕ} (hm : 0 < m) (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + N = e ^ 2) (hf : b ^ 2 + N = f ^ 2) (hg : a ^ 2 + b ^ 2 + N = g ^ 2)
    {P : ℕ → ℕ → ℕ → Bool}
    (hP : allRes m (fun x y z ↦ !(IsSqMod m (x ^ 2 + y ^ 2) && IsSqMod m (x ^ 2 + z) &&
      IsSqMod m (y ^ 2 + z) && IsSqMod m (x ^ 2 + y ^ 2 + z)) || P x y z) = true) :
    P (a % m) (b % m) (N % m) = true := by
  have := allRes_spec hP (Nat.mod_lt a hm) (Nat.mod_lt b hm) (Nat.mod_lt N hm)
  have sq {s t : ℕ} (hst : s % m = t % m) {r : ℕ} (hr : t = r ^ 2) : IsSqMod m s = true := by
    rw [← isSqMod_mod, hst, isSqMod_mod]
    exact isSqMod_of_isSquare hm ⟨r, by rw [hr, sq]⟩
  have h1 := sq (s := (a % m) ^ 2 + (b % m) ^ 2) (by simp [Nat.add_mod, Nat.pow_mod]) hd
  have h2 := sq (s := (a % m) ^ 2 + N % m) (by simp [Nat.add_mod, Nat.pow_mod]) he
  have h3 := sq (s := (b % m) ^ 2 + N % m) (by simp [Nat.add_mod, Nat.pow_mod]) hf
  have h4 := sq (s := (a % m) ^ 2 + (b % m) ^ 2 + N % m)
    (by simp [Nat.add_mod, Nat.pow_mod]) hg
  simpa [h1, h2, h3, h4] using this

/-- **The 2-adic shape.** If `(a, b, N)` is not divisible by `(2, 2, 4)`, then either
`16 ∣ N` and exactly one of `a, b` is odd (the other divisible by `4`), or `N ≡ 1 (mod 8)` and
`4 ∣ a`, `4 ∣ b`. Leech's example `(520, 576, 618849)` is of the second kind, `(1443, 1800,
461776)` of the first. -/
theorem edge_two_adic {a b N d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + N = e ^ 2) (hf : b ^ 2 + N = f ^ 2) (hg : a ^ 2 + b ^ 2 + N = g ^ 2)
    (hn : ¬ (2 ∣ a ∧ 2 ∣ b ∧ 4 ∣ N)) :
    (16 ∣ N ∧ ((a % 2 = 1 ∧ 4 ∣ b) ∨ (4 ∣ a ∧ b % 2 = 1))) ∨ (N % 8 = 1 ∧ 4 ∣ a ∧ 4 ∣ b) := by
  have := edge_residues (m := 16) (P := fun x y z ↦ (x % 2 == 0 && y % 2 == 0 && z % 4 == 0) ||
      (z % 16 == 0 && ((x % 2 == 1 && y % 4 == 0) || (x % 4 == 0 && y % 2 == 1))) ||
      (z % 8 == 1 && x % 4 == 0 && y % 4 == 0)) (by norm_num) hd he hf hg (by decide +kernel)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  omega

/-- Leech's divisibility for an edge cuboid and its diagonals. -/
theorem IsEdgeCuboid.leech_dvd {a b N : ℕ} (h : IsEdgeCuboid a b N) :
    ∃ d e f g : ℕ, a ^ 2 + b ^ 2 = d ^ 2 ∧ a ^ 2 + N = e ^ 2 ∧ b ^ 2 + N = f ^ 2 ∧
      a ^ 2 + b ^ 2 + N = g ^ 2 ∧
      2 ^ 8 * 3 ^ 4 * 5 ^ 4 * 7 * 11 * 13 ∣ a * b * N * d * e * f * g := by
  obtain ⟨d, e, f, g, hd, he, hf, hg⟩ := h.diagonals
  exact ⟨d, e, f, g, hd, he, hf, hg, EdgeLeech.edge_leech_dvd hd he hf hg⟩

end PerfectCuboid
