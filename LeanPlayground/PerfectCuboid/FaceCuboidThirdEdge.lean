module

public import Mathlib
public import LeanPlayground.PerfectCuboid.FaceCuboid
public import LeanPlayground.PerfectCuboid.LeechEdge
public import LeanPlayground.PerfectCuboid.FermatTriangle

/-!
# The third edge of a face cuboid is not a prime power (Theorem Q)

A *face cuboid* `(a, b, c)` (`IsFaceCuboid`) has `a² + c²`, `b² + c²`, `a² + b² + c²` square;
`c` is the common leg of the right triangles `(c, a, e)`, `(c, b, f)`. `FaceCuboid.lean` showed
that `a, b` are not prime powers (Theorem P, sign type `(−,−)`). Here we show the same for `c`.

## Main results

* `IsFaceCuboid.c_eq_prime_pow_imp` (**reduction**): if `c = p^k` then
  `(p^(2A) + 1)(p^(2B) + 1)` is a square for some `A > B ≥ 0`, `A ≡ B (mod 2)`.
* `theoremQ` (**Theorem Q**): for `p` prime and `A > B ≥ 1`,
  `(p^(2A) + 1)(p^(2B) + 1)` is not a square.
* `FaceThirdEdge.two_mul_pow_four_add_one_ne_sq`: `2(y⁴ + 1)` is not a square for `y ≥ 2`
  (Fermat; this is the case `B = 0`, `A` even).
* `IsFaceCuboid.edge_ne_prime_pow_c`, `IsFaceCuboid.edge_ne_prime_pow`: no edge of a face
  cuboid is a prime power; `IsPerfectCuboid.edge_ne_prime_pow_of_thirdEdge`: Korec's theorem
  for perfect cuboids once more (every edge of a perfect cuboid is the `c` of a face cuboid).

## The reduction

By the leg formula (`leg_of_prime_pow`), `2a = p^i (p^(2m) − 1)`, `2b = p^j (p^(2n) − 1)` with
`m = k − i`, `n = k − j ≥ 1`; say `i ≤ j`, so `m ≥ n`. Then
`(2g)² = 4p^(2k) + (2a)² + (2b)² = p^(2i) [(p^(2m) + 1)² + p^(2(m−n)) (p^(2n) − 1)²]
       = p^(2i) (p^(2(m+n)) + 1)(p^(2(m−n)) + 1)`,
the Gaussian factorization `(p^(2m) − 1) + i p^(m−n)(p^(2n) + 1) = (p^(m+n) + i)(p^(m−n) + i)`
in norm form. So `p^i ∣ 2g` and `A = m + n > B = m − n` (`reduction_core`).
This is the sign type `(+,+)` of the prime-power-leg framework; `(−,−)` is Theorem P
(`PellLeg.pow_sub_one_mul_pow_sub_one_not_square`), the mixed types do not factor.

## Proof of Theorem Q (elementary; no fundamental-unit theory needed)

Put `x = p²`, `P = x^A + 1`, `Q = x^B + 1`, `h = gcd(P, Q)`, `δ = gcd(A, B)`. If `PQ = W²`
then `P = h r²`, `Q = h s²` (`eq_gcd_mul_sq`). By `gcd_cases` (computed in `ZMod h`: `x^(2δ) ≡ 1`
by the order of `x`, then `x^δ ≡ ±1`), either one of `A, B` is even and `h ∣ 2`, or
`h = x^δ + 1`.
* `A = 2c` even, `h ∈ {1, 2}`: `(p^c)⁴ + 1 = r²` is impossible between consecutive squares, and
  `(p^c)⁴ + 1 = 2r²` gives `r⁴ − (p^c)⁴ = (r² − 1)²`, impossible by Fermat (`fermat_sub`).
  Same for `B` even.
* `h = x^δ + 1`: with `X = p^δ`, `(p^A)² + 1 = (X² + 1) r²`, a solution of the negative Pell
  equation for `D = X² + 1`, whose fundamental unit is explicitly `ε = X + √D`. A descent
  (`descent`: `(u, v) ↦ (Dv − Xu, u − Xv)`) shows `p^A + r√D = ε^j`; the norm forces `j` odd,
  and `j ≠ 1` as `A ≠ δ`. For an odd prime `ℓ ∣ j`: `x(ε^ℓ) ∣ x(ε^j) = p^A` (`re_dvd_re_pow`)
  and `x(ε^ℓ) = X(ℓ + X² t)` with `t ≥ 1` (`eps_pow_odd`), so `ℓ + X² t` is a power of `p`
  exceeding `ℓ`: then `p ∣ ℓ`, `ℓ = p`, and `p² ∣ ℓ + X² t` forces `p² ∣ p`
  (`not_sq_add_one_eq`). This replaces the planner's LTE step by the one-prime congruence
  `x(ε^ℓ) ≡ ℓX (mod X³)`.

## Literature

Theorem Q is a special case of Theorem 1.1 of P. Virbalas, *On the exponential Diophantine
equation `(aⁿ+1)(bⁿ+1) = x²`*, arXiv:2606.31223 (June 2026): for `a, b` distinct powers of one
`t > 1`, `a > 1`, the only solution is `(a, b, x) = (7, 49, 20)`, `n = 1`. That proof uses
Ljunggren-type results and Mihăilescu's theorem; the elementary proof above, its Lean
formalization and the face-cuboid corollary are new.

## Near-misses

For `B = 0, A = 1` the equation `2(p² + 1) = W²` has solutions `p = 7, 41, 239` (negative Pell
for `D = 2`), but `A ≡ B (mod 2)` excludes them. The face cuboid `(153, 672, 104)` has
`c = 104 = 2³·13`: "not a prime power" cannot be improved to "not a product of two prime
powers". Positivity of `a, b` is used only in the leg formula (`i < k`); the degenerate box
`(a, 0, c)` is excluded only there.
-/

@[expose] public section

namespace PerfectCuboid

namespace FaceThirdEdge

/-! ### Fermat: `y⁴ + 1 ≠ 2 r²` -/

/-- **Fermat.** `y⁴ + 1 = 2 r²` has no integer solution with `|y| ≥ 2`. Indeed then
`r⁴ − y⁴ = (r² − 1)²`, and `fermat_sub` forces `r² = 1`, i.e. `y⁴ = 1`. -/
theorem pow_four_add_one_ne_two_mul_sq {y r : ℤ} (hy : 2 ≤ |y|) : y ^ 4 + 1 ≠ 2 * r ^ 2 := by
  intro h
  have h1 : r ^ 4 - y ^ 4 = (r ^ 2 - 1) ^ 2 := by linear_combination -h
  have hy2 : (4 : ℤ) ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
  rcases fermat_sub h1 with h0 | h0 | h0
  · subst h0; nlinarith
  · subst h0; norm_num at hy
  · have : r ^ 2 = 1 := by linarith
    nlinarith

/-- `y⁴ + 1` is neither a square nor twice a square, for `y ≥ 2`. -/
theorem pow_four_add_one_ne {y h r : ℕ} (hy : 2 ≤ y) (hh : h ∣ 2) (e : y ^ 4 + 1 = h * r ^ 2) :
    False := by
  rcases (Nat.dvd_prime Nat.prime_two).1 hh with rfl | rfl
  · rw [one_mul] at e
    rcases le_or_gt r (y ^ 2) with hr | hr
    · have : r ^ 2 ≤ (y ^ 2) ^ 2 := Nat.pow_le_pow_left hr 2
      nlinarith
    · have : (y ^ 2 + 1) ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hr 2
      nlinarith
  · apply pow_four_add_one_ne_two_mul_sq (y := (y : ℤ)) (r := (r : ℤ))
    · rw [abs_of_nonneg (by positivity)]; exact_mod_cast hy
    · exact_mod_cast e

/-- `2 (y⁴ + 1)` is not a square for `y ≥ 2` (Fermat). This is the case `B = 0` of the
exponential equation `(p^(2A) + 1)(p^(2B) + 1) = W²` with `A` even. -/
theorem two_mul_pow_four_add_one_ne_sq {y : ℕ} (hy : 2 ≤ y) : ¬ IsSquare (2 * (y ^ 4 + 1)) := by
  rintro ⟨W, hW⟩
  have h2 : 2 ∣ W := Nat.prime_two.dvd_of_dvd_pow (n := 2) ⟨y ^ 4 + 1, by rw [sq, ← hW]⟩
  obtain ⟨w, rfl⟩ := h2
  exact pow_four_add_one_ne hy (dvd_refl 2) (by nlinarith)

/-! ### Coprime factors -/

/-- If `P Q = W²` then `P = gcd(P, Q) · r²`. -/
theorem eq_gcd_mul_sq {P Q W : ℕ} (hP : 0 < P) (h : P * Q = W ^ 2) :
    ∃ r : ℕ, P = Nat.gcd P Q * r ^ 2 := by
  have hg : 0 < Nat.gcd P Q := Nat.gcd_pos_of_pos_left Q hP
  have hcop := Nat.coprime_div_gcd_div_gcd hg
  obtain ⟨α, hα⟩ := Nat.gcd_dvd_left P Q
  obtain ⟨β, hβ⟩ := Nat.gcd_dvd_right P Q
  rw [Nat.div_eq_of_eq_mul_right hg hα, Nat.div_eq_of_eq_mul_right hg hβ] at hcop
  generalize Nat.gcd P Q = g at *
  subst hα hβ
  have hgW : g ∣ W := by
    rw [← Nat.pow_dvd_pow_iff two_ne_zero, ← h]
    exact ⟨α * β, by ring⟩
  obtain ⟨w, rfl⟩ := hgW
  have hab : α * β = w ^ 2 := by
    have : g ^ 2 * (α * β) = g ^ 2 * w ^ 2 := by rw [← mul_pow, ← h]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hα0 : 0 < α := by
    rcases Nat.eq_zero_or_pos α with h0 | h0
    · rw [h0, mul_zero] at hP; omega
    · exact h0
  obtain ⟨r, -, hr⟩ := FermatTriangle.exists_sq_eq_of_isCoprime (a := (α : ℤ)) (b := β) (c := w)
    (Nat.isCoprime_iff_coprime.mpr hcop) (by exact_mod_cast hab) (by exact_mod_cast hα0)
  refine ⟨r.natAbs, ?_⟩
  congr 1
  have : ((r.natAbs ^ 2 : ℕ) : ℤ) = r ^ 2 := by
    rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs]
  exact_mod_cast hr.trans this.symm

/-! ### `gcd(x^A + 1, x^B + 1)` -/

/-- With `d = gcd(A, B)`: either one of `A, B` is even and `gcd(x^A + 1, x^B + 1) ∣ 2`, or
`gcd(x^A + 1, x^B + 1) = x^d + 1`. -/
theorem gcd_cases {x A B : ℕ} :
    (Even A ∧ Nat.gcd (x ^ A + 1) (x ^ B + 1) ∣ 2) ∨ (Even B ∧ Nat.gcd (x ^ A + 1) (x ^ B + 1) ∣ 2)
      ∨ Nat.gcd (x ^ A + 1) (x ^ B + 1) = x ^ Nat.gcd A B + 1 := by
  set h := Nat.gcd (x ^ A + 1) (x ^ B + 1) with hh
  set d := Nat.gcd A B with hd
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left A B
  obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right A B
  rw [← hd] at ha' hb'
  clear_value d
  set u : ZMod h := (x : ZMod h) with hu
  have hPA : u ^ A = -1 := by
    have : ((x ^ A + 1 : ℕ) : ZMod h) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (Nat.gcd_dvd_left _ _)
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hPB : u ^ B = -1 := by
    have : ((x ^ B + 1 : ℕ) : ZMod h) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (Nat.gcd_dvd_right _ _)
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have h2d : u ^ (2 * d) = 1 := by
    have h1 : u ^ (2 * A) = 1 := by rw [mul_comm, pow_mul, hPA]; norm_num
    have h2 : u ^ (2 * B) = 1 := by rw [mul_comm, pow_mul, hPB]; norm_num
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [Nat.gcd_mul_left, ← hd] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have two_dvd : (1 : ZMod h) = -1 → h ∣ 2 := by
    intro e
    have : ((2 : ℕ) : ZMod h) = 0 := by
      push_cast
      calc (2 : ZMod h) = 1 - (-1) := by ring
        _ = 0 := by rw [← e]; ring
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  rcases Nat.even_or_odd a' with ⟨r, hr⟩ | ⟨r, hr⟩
  · left
    refine ⟨⟨d * r, by rw [ha', hr]; ring⟩, two_dvd ?_⟩
    rw [← hPA, ha', hr, show d * (r + r) = 2 * d * r by ring, pow_mul, h2d, one_pow]
  rcases Nat.even_or_odd b' with ⟨s, hs⟩ | ⟨s, hs⟩
  · right; left
    refine ⟨⟨d * s, by rw [hb', hs]; ring⟩, two_dvd ?_⟩
    rw [← hPB, hb', hs, show d * (s + s) = 2 * d * s by ring, pow_mul, h2d, one_pow]
  right; right
  have hud : u ^ d = -1 := by
    rw [← hPA, ha', hr, show d * (2 * r + 1) = 2 * d * r + d by ring, pow_add, pow_mul, h2d,
      one_pow, one_mul]
  have hdvd : h ∣ x ^ d + 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    push_cast
    rw [← hu, hud]; ring
  apply Nat.dvd_antisymm hdvd
  apply Nat.dvd_gcd
  · have := (show Odd a' from ⟨r, hr⟩).nat_add_dvd_pow_add_pow (x ^ d) 1
    rwa [one_pow, ← pow_mul, ← ha'] at this
  · have := (show Odd b' from ⟨s, hs⟩).nat_add_dvd_pow_add_pow (x ^ d) 1
    rwa [one_pow, ← pow_mul, ← hb'] at this

/-! ### The negative Pell equation `U² − (X² + 1) V² = −1` -/

/-- `ε = X + √(X² + 1)`, a unit of norm `−1` in `ℤ[√(X² + 1)]`. -/
def eps (X : ℤ) : Zsqrtd (X ^ 2 + 1) := ⟨X, 1⟩

@[simp] theorem eps_re (X : ℤ) : (eps X).re = X := rfl

@[simp] theorem eps_im (X : ℤ) : (eps X).im = 1 := rfl

theorem norm_eps_pow (X : ℤ) (j : ℕ) : (eps X ^ j).norm = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ (eps X) j, Zsqrtd.norm_mul, ih, pow_succ (-1 : ℤ) j, Zsqrtd.norm_def]
    simp only [eps_re, eps_im]
    ring

/-- **Descent.** Every solution of `u² − (X² + 1) v² = ±1` in non-negative integers is a power
of `ε = X + √(X² + 1)`: multiplying by `ε⁻¹ = −X + √(X² + 1)` maps `(u, v)` to
`((X² + 1) v − X u, u − X v)`, a non-negative solution with smaller `v`. -/
theorem descent {X : ℤ} (hX : 0 < X) (n : ℕ) : ∀ u v : ℤ, v = n → 0 ≤ u →
    (u ^ 2 - (X ^ 2 + 1) * v ^ 2 = 1 ∨ u ^ 2 - (X ^ 2 + 1) * v ^ 2 = -1) →
    ∃ j : ℕ, (⟨u, v⟩ : Zsqrtd (X ^ 2 + 1)) = eps X ^ j := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u v hvn hu hN
  have hN1 : u ^ 2 - (X ^ 2 + 1) * v ^ 2 ≤ 1 := by rcases hN with h | h <;> linarith
  have hN2 : -1 ≤ u ^ 2 - (X ^ 2 + 1) * v ^ 2 := by rcases hN with h | h <;> linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · subst hvn
    have hu1 : u ^ 2 = 1 := by
      rcases hN with h | h
      · norm_num at h
        rcases h with h | h <;> nlinarith
      · norm_num at h; nlinarith [sq_nonneg u]
    have : (u - 1) * (u + 1) = 0 := by linear_combination hu1
    rcases mul_eq_zero.1 this with h | h
    · have : u = 1 := by linarith
      subst this
      exact ⟨0, by ext <;> simp⟩
    · omega
  · have hv : 1 ≤ v := by rw [hvn]; exact_mod_cast hn
    have h1 : X * v ≤ u := by
      by_contra hc
      push Not at hc
      have : u ^ 2 < (X * v) ^ 2 := pow_lt_pow_left₀ hc hu two_ne_zero
      nlinarith
    have h2 : u < X * v + v := by
      by_contra hc
      push Not at hc
      have : (X * v + v) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hc 2
      nlinarith [mul_pos hX (mul_pos (by linarith : (0:ℤ) < v) (by linarith : (0:ℤ) < v))]
    have h3 : X * u ≤ (X ^ 2 + 1) * v := by
      by_contra hc
      push Not at hc
      have : ((X ^ 2 + 1) * v) ^ 2 < (X * u) ^ 2 :=
        pow_lt_pow_left₀ hc (by positivity) two_ne_zero
      nlinarith [mul_pos hX hX]
    have e : (((u - X * v).toNat : ℕ) : ℤ) = u - X * v := Int.toNat_of_nonneg (by linarith)
    obtain ⟨j, hj⟩ := ih (u - X * v).toNat (by omega) ((X ^ 2 + 1) * v - X * u) (u - X * v)
      e.symm (by linarith) (by
        rcases hN with h | h
        · right; linear_combination -h
        · left; linear_combination -h)
    refine ⟨j + 1, ?_⟩
    rw [pow_succ' (eps X) j, ← hj]
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

/-- Odd powers of `ε`: `x(ε^(2k+1)) = (2k+1) X + X³ t` with `t ≥ 0` (`t ≥ 1` for `k ≥ 1`) and
`y(ε^(2k+1)) ≡ 1 (mod X²)`. -/
theorem eps_pow_odd (X : ℤ) (k : ℕ) : ∃ t s : ℤ, 0 ≤ t ∧ 0 ≤ s ∧ (1 ≤ k → 1 ≤ t) ∧
    (eps X ^ (2 * k + 1)).re = (2 * k + 1) * X + X ^ 3 * t ∧
    (eps X ^ (2 * k + 1)).im = 1 + X ^ 2 * s := by
  induction k with
  | zero => exact ⟨0, 0, le_rfl, le_rfl, by omega, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨t, s, ht, hs, -, hre, him⟩ := ih
    have hk : (0 : ℤ) ≤ k := by positivity
    have hXt : 0 ≤ X ^ 2 * t := mul_nonneg (sq_nonneg X) ht
    have hXs : 0 ≤ X ^ 2 * s := mul_nonneg (sq_nonneg X) hs
    refine ⟨2 * (2 * k + 1) + 2 * X ^ 2 * t + t + 2 * s + 2 + 2 * X ^ 2 * s,
      2 * (2 * k + 1) + 2 * X ^ 2 * t + 2 * X ^ 2 * s + s + 2, by linarith, by linarith,
      fun _ => by linarith, ?_, ?_⟩
    · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, pow_succ (eps X) (2 * k + 1 + 1),
        pow_succ (eps X) (2 * k + 1)]
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, hre, him, eps_re, eps_im]
      push_cast; ring
    · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, pow_succ (eps X) (2 * k + 1 + 1),
        pow_succ (eps X) (2 * k + 1)]
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, hre, him, eps_re, eps_im]
      ring

/-- In any `ℤ[√D]`, `x(η) ∣ x(η^m)` for odd `m` (and `x(η) ∣ y(η^m)` for even `m ≥ 2`). -/
theorem re_dvd_re_pow {D : ℤ} (η : Zsqrtd D) (m : ℕ) :
    η.re ∣ (η ^ (2 * m + 1)).re ∧ η.re ∣ (η ^ (2 * m + 2)).im := by
  induction m with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [show 2 * 0 + 2 = 2 by rfl, pow_two, Zsqrtd.im_mul]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_left _ _)
  | succ m ih =>
    have h1 : η.re ∣ (η ^ (2 * (m + 1) + 1)).re := by
      rw [show 2 * (m + 1) + 1 = 2 * m + 2 + 1 by ring, pow_succ, Zsqrtd.re_mul]
      exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ih.2 _) _)
    refine ⟨h1, ?_⟩
    rw [show 2 * (m + 1) + 2 = 2 * (m + 1) + 1 + 1 by ring, pow_succ, Zsqrtd.im_mul]
    exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_left _ _)

/-- **Key lemma.** If `p` is prime, `d ≥ 1`, `A ≠ d`, then `(p^A)² + 1 ≠ ((p^d)² + 1) V²`.
Proof: by `descent`, `p^A + V√g = ε^j` (`g = p^(2d) + 1`, `ε = p^d + √g`) with `j` odd
(norm `−1`) and `j ≠ 1` (`A ≠ d`). Take an odd prime `ℓ ∣ j`; then `x(ε^ℓ) ∣ x(ε^j) = p^A`
(`re_dvd_re_pow`), and `x(ε^ℓ) = p^d (ℓ + p^(2d) t)` with `t ≥ 1` (`eps_pow_odd`), so
`Q = ℓ + p^(2d) t` is a power of `p` larger than `ℓ`: then `p ∣ ℓ`, `ℓ = p`, `p² ∣ Q`, `p² ∣ p`. -/
theorem not_sq_add_one_eq {p A d : ℕ} (hp : p.Prime) (hd : 1 ≤ d) (hAd : A ≠ d) (V : ℤ)
    (h : ((p : ℤ) ^ A) ^ 2 + 1 = (((p : ℤ) ^ d) ^ 2 + 1) * V ^ 2) : False := by
  set X : ℤ := (p : ℤ) ^ d with hXdef
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hX : 0 < X := by positivity
  obtain ⟨j, hj⟩ := descent hX V.natAbs ((p : ℤ) ^ A) (V.natAbs : ℤ) rfl (by positivity)
    (Or.inr (by rw [Int.natAbs_sq]; linear_combination h))
  have hn := congrArg Zsqrtd.norm hj
  rw [norm_eps_pow, Zsqrtd.norm_def] at hn
  simp only at hn
  have hre := congrArg Zsqrtd.re hj
  simp only at hre
  rcases Nat.even_or_odd j with hje | ⟨k, hk⟩
  · rw [hje.neg_one_pow] at hn
    nlinarith [Int.natAbs_sq V]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · subst hk
    simp only [Nat.mul_zero, Nat.zero_add, pow_one, eps_re, hXdef] at hre
    have : p ^ A = p ^ d := by exact_mod_cast hre
    exact hAd (Nat.pow_right_injective hp.two_le this)
  -- an odd prime `ℓ ∣ j`
  set ℓ := j.minFac with hℓdef
  have hj1 : j ≠ 1 := by omega
  have hℓ : ℓ.Prime := Nat.minFac_prime hj1
  obtain ⟨m, hm⟩ := Nat.minFac_dvd j
  rw [← hℓdef] at hm
  have hjodd : Odd j := ⟨k, hk⟩
  rw [hm] at hjodd
  obtain ⟨hℓodd, hmodd⟩ := Nat.odd_mul.1 hjodd
  obtain ⟨k', hk'⟩ := hℓodd
  obtain ⟨m', hm'⟩ := hmodd
  have hk'1 : 1 ≤ k' := by have := hℓ.two_le; omega
  have hdvd : (eps X ^ ℓ).re ∣ (p : ℤ) ^ A := by
    rw [hre, hm, pow_mul, hm']
    exact (re_dvd_re_pow _ m').1
  obtain ⟨t, s, ht, -, ht1, hxre, -⟩ := eps_pow_odd X k'
  rw [← hk'] at hxre
  rw [hxre] at hdvd
  have ht1 := ht1 hk'1
  -- `Q = ℓ + p^(2d) t` divides `p^A`
  set T := t.toNat with hT
  have hTt : (T : ℤ) = t := Int.toNat_of_nonneg ht
  have hQ : ((ℓ + p ^ (2 * d) * T : ℕ) : ℤ) ∣ (p : ℤ) ^ A := by
    refine dvd_trans ⟨X, ?_⟩ hdvd
    rw [hk']
    push_cast
    rw [hTt, pow_mul', ← hXdef]
    ring
  have hQ' : ℓ + p ^ (2 * d) * T ∣ p ^ A := by exact_mod_cast hQ
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1 hQ'
  have hT1 : 1 ≤ T := by omega
  have hpd : 1 ≤ p ^ (2 * d) := Nat.one_le_pow _ _ hp.pos
  have hbig : ℓ < p ^ f := by rw [← hf]; nlinarith
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := hℓ.two_le
    simp at hbig; omega
  have hpdvd : p ∣ p ^ (2 * d) * T := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
  have hpℓ : p ∣ ℓ := by
    have := dvd_pow_self p hf0
    rw [← hf] at this
    exact (Nat.dvd_add_left hpdvd).1 this
  have hpeq : p = ℓ := (Nat.prime_dvd_prime_iff_eq hp hℓ).1 hpℓ
  have hf2 : 2 ≤ f := by
    by_contra hc
    have : f = 1 := by omega
    rw [this, pow_one, hpeq] at hbig
    omega
  have hp2dvd : p ^ 2 ∣ ℓ := by
    have h1 : p ^ 2 ∣ ℓ + p ^ (2 * d) * T := hf ▸ pow_dvd_pow p hf2
    have h2 : p ^ 2 ∣ p ^ (2 * d) * T := dvd_mul_of_dvd_left (pow_dvd_pow p (by omega)) _
    exact (Nat.dvd_add_left h2).1 h1
  rw [← hpeq] at hp2dvd
  have := Nat.le_of_dvd hp.pos hp2dvd
  have := hp.two_le
  nlinarith

end FaceThirdEdge

open FaceThirdEdge

/-! ### Theorem Q -/

/-- **Theorem Q.** For a prime `p` and `A > B ≥ 1`, `(p^(2A) + 1)(p^(2B) + 1)` is not a square.
(A special case of Theorem 1.1 of arXiv:2606.31223; the proof here is elementary.) -/
theorem theoremQ {p A B : ℕ} (hp : p.Prime) (hB : 1 ≤ B) (hBA : B < A) :
    ¬ IsSquare ((p ^ (2 * A) + 1) * (p ^ (2 * B) + 1)) := by
  rintro ⟨W, hW⟩
  have hp2 := hp.two_le
  rw [pow_mul, pow_mul] at hW
  set x := p ^ 2 with hx
  obtain ⟨r, hr⟩ := eq_gcd_mul_sq (P := x ^ A + 1) (Q := x ^ B + 1) (by positivity)
    (by rw [hW, sq])
  obtain ⟨s, hs⟩ := eq_gcd_mul_sq (P := x ^ B + 1) (Q := x ^ A + 1) (by positivity)
    (by rw [mul_comm, hW, sq])
  rw [Nat.gcd_comm] at hs
  rcases gcd_cases (x := x) (A := A) (B := B) with ⟨⟨c, hc⟩, h2⟩ | ⟨⟨c, hc⟩, h2⟩ | hg
  · have hy : 2 ≤ p ^ c := hp2.trans (Nat.le_self_pow (by omega) p)
    exact pow_four_add_one_ne hy h2 (by rw [← hr, hc, hx]; ring)
  · have hy : 2 ≤ p ^ c := hp2.trans (Nat.le_self_pow (by omega) p)
    exact pow_four_add_one_ne hy h2 (by rw [← hs, hc, hx]; ring)
  · have hd1 : 1 ≤ Nat.gcd A B := Nat.gcd_pos_of_pos_left _ (by omega)
    have hdB : Nat.gcd A B ≤ B := Nat.gcd_le_right _ (by omega)
    apply not_sq_add_one_eq hp hd1 (by omega : A ≠ Nat.gcd A B) (r : ℤ)
    rw [hg, hx] at hr
    have : (p ^ A) ^ 2 + 1 = ((p ^ Nat.gcd A B) ^ 2 + 1) * r ^ 2 := by
      calc (p ^ A) ^ 2 + 1 = (p ^ 2) ^ A + 1 := by ring
        _ = _ := hr
        _ = ((p ^ Nat.gcd A B) ^ 2 + 1) * r ^ 2 := by ring
    exact_mod_cast this

/-! ### The reduction: a prime-power third edge gives a solution of `(p^(2A)+1)(p^(2B)+1) = W²` -/

/-- The core identity of the reduction. With `k = i + n + δ`, `2a = p^i (p^(2(n+δ)) − 1)`,
`2b = p^(i+δ) (p^(2n) − 1)`:
`(2g)² = p^(2i) (p^(2(2n+δ)) + 1)(p^(2δ) + 1)`. -/
theorem FaceThirdEdge.reduction_core {p i n δ a b G Ba Bb : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (ha : 2 * a = p ^ i * Ba) (hBa : Ba + 1 = p ^ (2 * (n + δ)))
    (hb : 2 * b = p ^ (i + δ) * Bb) (hBb : Bb + 1 = p ^ (2 * n))
    (hG : a ^ 2 + b ^ 2 + (p ^ (i + n + δ)) ^ 2 = G ^ 2) :
    ∃ A B W : ℕ, B < A ∧ (A + B) % 2 = 0 ∧ (p ^ (2 * A) + 1) * (p ^ (2 * B) + 1) = W ^ 2 := by
  have key : (2 * G) ^ 2 = (p ^ i) ^ 2 * ((p ^ (2 * (2 * n + δ)) + 1) * (p ^ (2 * δ) + 1)) := by
    have ha' : (2 * a : ℤ) = (p : ℤ) ^ i * Ba := by exact_mod_cast ha
    have hb' : (2 * b : ℤ) = (p : ℤ) ^ (i + δ) * Bb := by exact_mod_cast hb
    have hBa' : (Ba : ℤ) + 1 = (p : ℤ) ^ (2 * (n + δ)) := by exact_mod_cast hBa
    have hBb' : (Bb : ℤ) + 1 = (p : ℤ) ^ (2 * n) := by exact_mod_cast hBb
    have hG' : (a : ℤ) ^ 2 + b ^ 2 + ((p : ℤ) ^ (i + n + δ)) ^ 2 = G ^ 2 := by exact_mod_cast hG
    have : (2 * (G : ℤ)) ^ 2 =
        ((p : ℤ) ^ i) ^ 2 * (((p : ℤ) ^ (2 * (2 * n + δ)) + 1) * ((p : ℤ) ^ (2 * δ) + 1)) := by
      linear_combination (-4) * hG' + (2 * a + (p : ℤ) ^ i * Ba) * ha'
        + (2 * b + (p : ℤ) ^ (i + δ) * Bb) * hb'
        + ((p : ℤ) ^ i) ^ 2 * (Ba + (p : ℤ) ^ (2 * (n + δ)) - 1) * hBa'
        + ((p : ℤ) ^ (i + δ)) ^ 2 * (Bb + (p : ℤ) ^ (2 * n) - 1) * hBb'
    exact_mod_cast this
  obtain ⟨W, hW⟩ : p ^ i ∣ 2 * G := (Nat.pow_dvd_pow_iff two_ne_zero).1 ⟨_, key⟩
  refine ⟨2 * n + δ, δ, W, by omega, by omega, ?_⟩
  rw [hW, mul_pow] at key
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos hp.pos i) 2) key).symm

/-- **The reduction.** If the third edge `c` of a face cuboid is a prime power `p^k`, then
`(p^(2A) + 1)(p^(2B) + 1)` is a square for some `A > B ≥ 0` with `A ≡ B (mod 2)`. -/
theorem IsFaceCuboid.c_eq_prime_pow_imp {a b c p k : ℕ} (h : IsFaceCuboid a b c)
    (hp : p.Prime) (hc : c = p ^ k) :
    ∃ A B W : ℕ, B < A ∧ (A + B) % 2 = 0 ∧ (p ^ (2 * A) + 1) * (p ^ (2 * B) + 1) = W ^ 2 := by
  subst hc
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨G, hG⟩ := h.sq_abc
  obtain ⟨i, hik, Ba, ha, hBa⟩ := leg_of_prime_pow (p := p) (k := k) (b := a) (d := e) hp h.pos_a
    (by rw [sq e, ← he]; ring)
  obtain ⟨j, hjk, Bb, hb, hBb⟩ := leg_of_prime_pow (p := p) (k := k) (b := b) (d := f) hp h.pos_b
    (by rw [sq f, ← hf]; ring)
  rcases le_total i j with hij | hij
  · obtain ⟨δ, rfl⟩ : ∃ δ, j = i + δ := ⟨j - i, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, k = i + n + δ := ⟨k - i - δ, by omega⟩
    exact FaceThirdEdge.reduction_core (i := i) (n := n) (δ := δ) hp (by omega) ha
      (by rw [hBa, show 2 * (i + n + δ - i) = 2 * (n + δ) by omega]) hb
      (by rw [hBb, show 2 * (i + n + δ - (i + δ)) = 2 * n by omega]) (by rw [hG, sq])
  · obtain ⟨δ, rfl⟩ : ∃ δ, i = j + δ := ⟨i - j, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, k = j + n + δ := ⟨k - j - δ, by omega⟩
    exact FaceThirdEdge.reduction_core (i := j) (n := n) (δ := δ) hp (by omega) hb
      (by rw [hBb, show 2 * (j + n + δ - j) = 2 * (n + δ) by omega]) ha
      (by rw [hBa, show 2 * (j + n + δ - (j + δ)) = 2 * n by omega])
      (by rw [sq G, ← hG]; ring)

/-! ### The third edge -/

/-- **The third edge of a face cuboid is not a prime power.** -/
theorem IsFaceCuboid.edge_ne_prime_pow_c {a b c : ℕ} (h : IsFaceCuboid a b c) {p k : ℕ}
    (hp : p.Prime) : c ≠ p ^ k := by
  intro hc
  obtain ⟨A, B, W, hBA, hpar, hW⟩ := h.c_eq_prime_pow_imp hp hc
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · obtain ⟨c', rfl⟩ : ∃ c', A = 2 * c' := ⟨A / 2, by omega⟩
    apply two_mul_pow_four_add_one_ne_sq (y := p ^ c')
      (hp.two_le.trans (Nat.le_self_pow (by omega) p))
    refine ⟨W, ?_⟩
    rw [← sq, ← hW]
    ring
  · exact theoremQ hp hB hBA ⟨W, by rw [hW, sq]⟩

/-- In a face cuboid no edge is a prime power. -/
theorem IsFaceCuboid.edge_ne_prime_pow {a b c : ℕ} (h : IsFaceCuboid a b c) {p k : ℕ}
    (hp : p.Prime) : a ≠ p ^ k ∧ b ≠ p ^ k ∧ c ≠ p ^ k :=
  ⟨h.edge_ne_prime_pow_a hp, h.edge_ne_prime_pow_b hp, h.edge_ne_prime_pow_c hp⟩

/-- Korec's theorem for perfect cuboids once more, now from the third-edge theorem alone: each
edge of a perfect cuboid is the third edge `c` of a face cuboid. -/
theorem IsPerfectCuboid.edge_ne_prime_pow_of_thirdEdge {a b c : ℕ} (h : IsPerfectCuboid a b c)
    {p k : ℕ} (hp : p.Prime) : a ≠ p ^ k ∧ b ≠ p ^ k ∧ c ≠ p ^ k := by
  have hc := h.toIsFaceCuboid
  have ha : IsFaceCuboid b c a :=
    { pos_a := h.pos_b, pos_b := h.pos_c, pos_c := h.pos_a
      sq_ac := by have := h.sq_ab; rwa [add_comm] at this
      sq_bc := h.sq_ca
      sq_abc := by
        have := h.sq_abc; rwa [show a ^ 2 + b ^ 2 + c ^ 2 = b ^ 2 + c ^ 2 + a ^ 2 by ring] at this }
  have hb : IsFaceCuboid c a b :=
    { pos_a := h.pos_c, pos_b := h.pos_a, pos_c := h.pos_b
      sq_ac := by have := h.sq_bc; rwa [add_comm] at this
      sq_bc := h.sq_ab
      sq_abc := by
        have := h.sq_abc; rwa [show a ^ 2 + b ^ 2 + c ^ 2 = c ^ 2 + a ^ 2 + b ^ 2 by ring] at this }
  exact ⟨ha.edge_ne_prime_pow_c hp, hb.edge_ne_prime_pow_c hp, hc.edge_ne_prime_pow_c hp⟩

end PerfectCuboid
