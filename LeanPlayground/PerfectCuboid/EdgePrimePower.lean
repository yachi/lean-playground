module

public import LeanPlayground.PerfectCuboid.Basic

/-!
# No edge of a perfect cuboid is a prime power

I. Korec, *Nonexistence of a small perfect rational cuboid*, Acta Math. Univ. Comenian.
44/45 (1984), 39–48: an edge of a perfect cuboid is not a prime power. We prove it for every
edge, every prime `p` (including `p = 2`) and every exponent, without assuming primitivity.

## Main results

* `IsPerfectCuboid.edge_ne_prime_pow`: `a ≠ p ^ k` for every prime `p` and every `k`; by symmetry
  the same holds for `b` and `c` (`IsPerfectCuboid.edge_ne_prime_pow_b`, `..._c`).
* `inv_sq_add_inv_sq_gt`: the *divisor inequality* `t₁²t₂² < t₃²(t₁² + t₂²)` for the three
  divisors `tₘ = (diagonal) − (leg)` of `a²`; it generalises the inequality `(v² − 1)(w² − 1) < 1`
  for `tᵢ = t₃ v, t₃ w`.

## The idea

The edge `a` is a leg of the three right triangles `(a, b, d)`, `(a, c, e)` and `(a, f, g)`, where
`f² = b² + c²` and `g² = a² + b² + c²`. If `a = p ^ k` then `(d - b)(d + b) = p ^ (2k)`, so
`d - b = p ^ i` and `d + b = p ^ (2k - i)` with `i < k`, and `2b = p ^ i * B` with
`B + 1 = p ^ (2(k - i))`; in particular `p ∤ B`. Likewise `2c = p ^ j * C` and `2f = p ^ l * F`.
In `(2b)² + (2c)² = (2f)²` the exponent of `p` on the right is `2l`, on the left it is `2·min(i, j)`
when `i ≠ j`. So `l = i` (say), hence `F = B` and `f = b`, which forces `c = 0`. If `i = j` then
`b = c` and `f² = 2b²`, impossible.
-/

@[expose] public section

namespace PerfectCuboid

/-- `x² = 2y²` has no solution with `y > 0`, since `√2` is irrational. -/
private theorem sq_ne_two_mul_sq {x y : ℕ} (hy : 0 < y) : x ^ 2 ≠ 2 * y ^ 2 := by
  intro h
  have hirr : Irrational √((2 : ℕ) : ℝ) := Nat.Prime.irrational_sqrt Nat.prime_two
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have e : ((2 : ℕ) : ℝ) = ((x : ℝ) / y) ^ 2 := by
    rw [div_pow, eq_div_iff (by positivity)]
    exact_mod_cast h.symm
  exact hirr ⟨(x : ℚ) / y, by rw [e, Real.sqrt_sq (by positivity)]; push_cast; rfl⟩

/-- A product of two natural numbers that is a power of a prime: both factors are powers. -/
theorem eq_pow_of_mul_eq_pow {p n x y : ℕ} (hp : p.Prime) (h : x * y = p ^ n) :
    ∃ i ≤ n, x = p ^ i ∧ y = p ^ (n - i) := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro y h)
  refine ⟨i, hi, rfl, ?_⟩
  have hn : p ^ n = p ^ i * p ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
  rw [hn] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i) h

/-- **The leg formula.** If `(p ^ k)² + b² = d²` with `b > 0`, then `2b = p ^ i * B` with `i < k`
and `B + 1 = p ^ (2(k - i))`. -/
theorem leg_of_prime_pow {p k b d : ℕ} (hp : p.Prime) (hb : 0 < b)
    (h : (p ^ k) ^ 2 + b ^ 2 = d ^ 2) :
    ∃ i < k, ∃ B, 2 * b = p ^ i * B ∧ B + 1 = p ^ (2 * (k - i)) := by
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  have hbd : b < d := by
    have : b ^ 2 < d ^ 2 := by rw [← h]; have := pow_pos hpk 2; omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hmul : (d - b) * (d + b) = p ^ (2 * k) := by
    have h1 := Nat.sq_sub_sq d b
    have h2 : d ^ 2 - b ^ 2 = (p ^ k) ^ 2 := by omega
    rw [mul_comm, ← h1, h2, ← pow_mul, mul_comm]
  obtain ⟨i, hi, h1, h2⟩ := eq_pow_of_mul_eq_pow hp hmul
  have hlt : p ^ i < p ^ (2 * k - i) := by rw [← h1, ← h2]; omega
  have hik : i < k := by
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
    omega
  refine ⟨i, hik, p ^ (2 * (k - i)) - 1, ?_, ?_⟩
  · have he : 2 * k - i = i + 2 * (k - i) := by omega
    rw [he, pow_add] at h2
    rw [Nat.mul_sub_one]
    have : 2 * b = (d + b) - (d - b) := by omega
    rw [this, h1, h2]
  · exact Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)

/-- If `B + 1` is a positive power of `p` then `p ∤ B`. -/
theorem not_dvd_of_succ_eq_pow {p m B : ℕ} (hp : p.Prime) (hm : 0 < m) (h : B + 1 = p ^ m) :
    ¬ p ∣ B := by
  intro hB
  have h1 : p ∣ B + 1 := h ▸ dvd_pow_self p hm.ne'
  exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hB).1 h1))

/-- **Exact valuation of a sum of two squares.** If `p` divides none of `B, C, F`, `i < j` and
`(p^i B)² + (p^j C)² = (p^l F)²`, then `l = i`. -/
theorem exp_eq_of_sq_add_sq {p i j l B C F : ℕ} (hp : p.Prime) (hB : ¬ p ∣ B) (hF : ¬ p ∣ F)
    (hij : i < j) (h : (p ^ i * B) ^ 2 + (p ^ j * C) ^ 2 = (p ^ l * F) ^ 2) : l = i := by
  set W := B ^ 2 + p ^ (2 * (j - i)) * C ^ 2 with hW
  have hWp : ¬ p ∣ W := by
    intro hd
    have h1 : p ∣ p ^ (2 * (j - i)) * C ^ 2 :=
      Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
    exact hB (hp.dvd_of_dvd_pow ((Nat.dvd_add_left h1).1 hd))
  have hFp : ¬ p ∣ F ^ 2 := fun hd ↦ hF (hp.dvd_of_dvd_pow hd)
  have hL : (p ^ i * B) ^ 2 + (p ^ j * C) ^ 2 = p ^ (2 * i) * W := by
    have : j = i + (j - i) := by omega
    rw [hW, this, Nat.add_sub_cancel_left]
    ring
  rw [hL, mul_pow, ← pow_mul, mul_comm l 2] at h
  have hp0 : ∀ n, 0 < p ^ n := fun n ↦ pow_pos hp.pos n
  rcases lt_trichotomy l i with hli | hli | hli
  · exfalso
    have : p ^ (2 * i) = p ^ (2 * l) * p ^ (2 * (i - l)) := by
      rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (hp0 _) h
    exact hFp (h' ▸ Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _)
  · exact hli
  · exfalso
    have : p ^ (2 * l) = p ^ (2 * i) * p ^ (2 * (l - i)) := by
      rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (hp0 _) h
    exact hWp (h' ▸ Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _)

/-- **Korec (1984).** The first edge of a perfect cuboid is not a prime power. No primitivity or
parity assumption is needed, and `p = 2` is allowed. -/
theorem IsPerfectCuboid.edge_ne_prime_pow {a b c : ℕ} (h : IsPerfectCuboid a b c) {p k : ℕ}
    (hp : p.Prime) : a ≠ p ^ k := by
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
  obtain ⟨i, hi, B, hb, hB⟩ := leg_of_prime_pow hp hb0 (by rw [hd]; ring)
  obtain ⟨j, hj, C, hc, hC⟩ := leg_of_prime_pow hp hc0 (by rw [add_comm, he]; ring)
  obtain ⟨l, hl, F, hf', hF⟩ := leg_of_prime_pow (k := k) (d := g) hp hf0
    (by rw [sq f, ← hf, sq g, ← hg]; ring)
  have hBp := not_dvd_of_succ_eq_pow hp (by omega) hB
  have hCp := not_dvd_of_succ_eq_pow hp (by omega) hC
  have hFp := not_dvd_of_succ_eq_pow hp (by omega) hF
  have key : (p ^ i * B) ^ 2 + (p ^ j * C) ^ 2 = (p ^ l * F) ^ 2 := by
    rw [← hb, ← hc, ← hf']; nlinarith [hf]
  rcases lt_trichotomy i j with hij | rfl | hij
  · -- `l = i`, so `f = b` and `c = 0`
    have hli := exp_eq_of_sq_add_sq hp hBp hFp hij key
    subst hli
    have hFB : F = B := Nat.add_right_cancel (hF.trans hB.symm)
    subst hFB
    have h2 : 2 * f = 2 * b := by rw [hf', hb]
    have hfb : f = b := by omega
    subst hfb
    have h3 : f ^ 2 + c ^ 2 = f ^ 2 + 0 := by rw [hf, sq]; ring
    exact hc0.ne' (pow_eq_zero_iff two_ne_zero |>.1 (Nat.add_left_cancel h3))
  · -- `b = c`, so `f² = 2b²`
    have hBC : B = C := Nat.add_right_cancel (hB.trans hC.symm)
    subst hBC
    have h2 : 2 * c = 2 * b := by rw [hc, hb]
    have hcb : c = b := by omega
    subst hcb
    exact sq_ne_two_mul_sq hb0 (by rw [sq f, ← hf]; ring)
  · have hlj := exp_eq_of_sq_add_sq (B := C) (C := B) hp hCp hFp hij (by rw [add_comm]; exact key)
    subst hlj
    have hFC : F = C := Nat.add_right_cancel (hF.trans hC.symm)
    subst hFC
    have h2 : 2 * f = 2 * c := by rw [hf', hc]
    have hfc : f = c := by omega
    subst hfc
    have h3 : f ^ 2 + b ^ 2 = f ^ 2 + 0 := by rw [add_comm, hf, sq]; ring
    exact hb0.ne' (pow_eq_zero_iff two_ne_zero |>.1 (Nat.add_left_cancel h3))

/-- The second edge of a perfect cuboid is not a prime power. -/
theorem IsPerfectCuboid.edge_ne_prime_pow_b {a b c : ℕ} (h : IsPerfectCuboid a b c) {p k : ℕ}
    (hp : p.Prime) : b ≠ p ^ k :=
  IsPerfectCuboid.edge_ne_prime_pow (a := b) (b := c) (c := a)
    ⟨h.toIsEulerBrick.rotate, by have := h.sq_abc; rwa [show b ^ 2 + c ^ 2 + a ^ 2 =
      a ^ 2 + b ^ 2 + c ^ 2 by ring]⟩ hp

/-- The third edge of a perfect cuboid is not a prime power. -/
theorem IsPerfectCuboid.edge_ne_prime_pow_c {a b c : ℕ} (h : IsPerfectCuboid a b c) {p k : ℕ}
    (hp : p.Prime) : c ≠ p ^ k :=
  IsPerfectCuboid.edge_ne_prime_pow (a := c) (b := a) (c := b)
    ⟨h.toIsEulerBrick.rotate.rotate, by have := h.sq_abc; rwa [show c ^ 2 + a ^ 2 + b ^ 2 =
      a ^ 2 + b ^ 2 + c ^ 2 by ring]⟩ hp

/-- **The divisor inequality.** Let `tₘ uₘ = A` (`tₘ` = diagonal − leg, `uₘ` = diagonal + leg,
`A = a²`) with `tₘ > 0`, and suppose the legs `xₘ = (uₘ − tₘ)/2` satisfy `x₁² + x₂² = x₃²` with
`x₁, x₂ > 0`, i.e. `(u₁ − t₁)² + (u₂ − t₂)² = (u₃ − t₃)²` and `t₁ < u₁`, `t₂ < u₂`. Then
`u₃² < u₁² + u₂²`, equivalently `t₁²t₂² < t₃²(t₁² + t₂²)`. For `t₁ = t₃v`, `t₂ = t₃w` with
`v, w ≥ 2` this fails. -/
theorem inv_sq_add_inv_sq_gt {A t₁ t₂ t₃ u₁ u₂ u₃ : ℤ} (h₁ : t₁ * u₁ = A) (h₂ : t₂ * u₂ = A)
    (h₃ : t₃ * u₃ = A) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (ht₃ : 0 < t₃) (hu₁ : t₁ < u₁)
    (hu₂ : t₂ < u₂) (h : (u₁ - t₁) ^ 2 + (u₂ - t₂) ^ 2 = (u₃ - t₃) ^ 2) :
    u₃ ^ 2 < u₁ ^ 2 + u₂ ^ 2 ∧ (t₁ * t₂) ^ 2 < t₃ ^ 2 * (t₁ ^ 2 + t₂ ^ 2) := by
  have key : u₁ ^ 2 + u₂ ^ 2 - u₃ ^ 2 = 2 * A + t₃ ^ 2 - t₁ ^ 2 - t₂ ^ 2 := by
    linear_combination h + 2 * h₁ + 2 * h₂ - 2 * h₃
  have e₁ : t₁ ^ 2 < A := by nlinarith
  have e₂ : t₂ ^ 2 < A := by nlinarith
  have hu : u₃ ^ 2 < u₁ ^ 2 + u₂ ^ 2 := by nlinarith [sq_nonneg t₃]
  refine ⟨hu, ?_⟩
  have hA : 0 < A := by nlinarith
  have hT : 0 < (t₁ * t₂ * t₃) ^ 2 := by positivity
  have hm : (t₁ * t₂ * t₃) ^ 2 * u₃ ^ 2 < (t₁ * t₂ * t₃) ^ 2 * (u₁ ^ 2 + u₂ ^ 2) :=
    mul_lt_mul_of_pos_left hu hT
  have : A ^ 2 * (t₁ * t₂) ^ 2 < A ^ 2 * (t₃ ^ 2 * (t₁ ^ 2 + t₂ ^ 2)) := by
    have l : (t₁ * t₂ * t₃) ^ 2 * u₃ ^ 2 = A ^ 2 * (t₁ * t₂) ^ 2 := by
      rw [← h₃]; ring
    have r : (t₁ * t₂ * t₃) ^ 2 * (u₁ ^ 2 + u₂ ^ 2) = A ^ 2 * (t₃ ^ 2 * (t₁ ^ 2 + t₂ ^ 2)) := by
      have : A ^ 2 * (t₃ ^ 2 * (t₁ ^ 2 + t₂ ^ 2)) = (t₂ * u₂) ^ 2 * (t₃ * t₁) ^ 2 +
          (t₁ * u₁) ^ 2 * (t₃ * t₂) ^ 2 := by rw [h₁, h₂]; ring
      rw [this]; ring
    rw [← l, ← r]; exact hm
  exact lt_of_mul_lt_mul_left this (by positivity)

end PerfectCuboid
