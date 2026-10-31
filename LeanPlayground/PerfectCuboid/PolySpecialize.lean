module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolynomialCuboid

/-!
# Specializing polynomial cuboids and bricks

A polynomial cuboid `(a, b, c)` over `ℚ` (`IsPolyCuboid`, `PolynomialCuboid.lean`) evaluated at a
rational `r` with `a(r) b(r) c(r) ≠ 0` is a rational perfect cuboid, since `Polynomial.eval r`
is a ring homomorphism and therefore preserves squares. Such an `r` always exists (`abc ≠ 0` has
finitely many roots and `ℚ` is infinite). Hence

* `IsPolyCuboid.exists_isPerfectCuboid`: **any** polynomial cuboid (proportional or not) gives an
  integer perfect cuboid. Together with `IsPerfectCuboid.isPolyCuboid` this shows that
  polynomial cuboids exist if and only if integer perfect cuboids exist.

The same argument for three faces gives integer Euler bricks from rational ones
(`exists_isEulerBrick_of_rat`), used for polynomial bricks in `PolyBrick.lean`.

## Main results

* `isSquare_eval`, `exists_eval_ne_zero`.
* `IsPolyCuboid.isRatCuboid_eval`, `IsPolyCuboid.exists_isPerfectCuboid`.
* `exists_isEulerBrick_of_rat`: positive rationals with three square faces give an integer
  Euler brick.
-/
@[expose] public section

open Polynomial

namespace PerfectCuboid.Poly

/-- Evaluation preserves squares. -/
theorem isSquare_eval {p : ℚ[X]} (h : IsSquare p) (r : ℚ) : IsSquare (p.eval r) := by
  simpa using h.map (evalRingHom r)

/-- Three nonzero polynomials over `ℚ` have a common non-root. -/
theorem exists_eval_ne_zero {a b c : ℚ[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ r : ℚ, a.eval r ≠ 0 ∧ b.eval r ≠ 0 ∧ c.eval r ≠ 0 := by
  have hp : a * b * c ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hc
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset (a * b * c).roots.toFinset
  have hr' : (a * b * c).eval r ≠ 0 := by
    intro h0
    apply hr
    rw [Multiset.mem_toFinset, mem_roots hp]
    exact h0
  simp only [eval_mul, mul_ne_zero_iff] at hr'
  exact ⟨r, hr'.1.1, hr'.1.2, hr'.2⟩

/-- A positive rational square has a positive square root. -/
theorem exists_pos_sq_of_isSquare {z : ℚ} (hz : 0 < z) (h : IsSquare z) :
    ∃ s : ℚ, 0 < s ∧ s ^ 2 = z := by
  obtain ⟨s, hs⟩ := h
  refine ⟨|s|, abs_pos.mpr ?_, by rw [sq_abs, hs]; ring⟩
  rintro rfl
  rw [hs] at hz
  simp at hz

/-- **Specialization.** A polynomial cuboid evaluated at a common non-root of its edges is a
rational perfect cuboid (after taking absolute values). -/
theorem IsPolyCuboid.isRatCuboid_eval {a b c : ℚ[X]} (h : IsPolyCuboid a b c) {r : ℚ}
    (ha : a.eval r ≠ 0) (hb : b.eval r ≠ 0) (hc : c.eval r ≠ 0) :
    ∃ d e f g : ℚ, CongruentRank.IsRatCuboid |a.eval r| |b.eval r| |c.eval r| d e f g := by
  have hab := isSquare_eval h.sq_ab r
  have hac := isSquare_eval h.sq_ac r
  have hbc := isSquare_eval h.sq_bc r
  have habc := isSquare_eval h.sq_abc r
  simp only [eval_add, eval_pow] at hab hac hbc habc
  obtain ⟨d, hd0, hd⟩ := exists_pos_sq_of_isSquare (by positivity) hab
  obtain ⟨e, he0, he⟩ := exists_pos_sq_of_isSquare (by positivity) hac
  obtain ⟨f, hf0, hf⟩ := exists_pos_sq_of_isSquare (by positivity) hbc
  obtain ⟨g, hg0, hg⟩ := exists_pos_sq_of_isSquare (by positivity) habc
  refine ⟨d, e, f, g, abs_pos.mpr ha, abs_pos.mpr hb, abs_pos.mpr hc, hd0, he0, hf0, hg0,
    ?_, ?_, ?_, ?_⟩ <;> simp only [sq_abs]
  · exact hd
  · exact he
  · exact hf
  · exact hg

/-- **Every polynomial cuboid gives an integer perfect cuboid** (no proportionality needed).
With `IsPerfectCuboid.isPolyCuboid`, polynomial cuboids exist iff perfect cuboids do. -/
theorem IsPolyCuboid.exists_isPerfectCuboid {a b c : ℚ[X]} (h : IsPolyCuboid a b c) :
    ∃ A B C : ℕ, IsPerfectCuboid A B C := by
  obtain ⟨r, ha, hb, hc⟩ := exists_eval_ne_zero h.ne_a h.ne_b h.ne_c
  obtain ⟨d, e, f, g, hr⟩ := h.isRatCuboid_eval ha hb hc
  exact hr.exists_isPerfectCuboid

/-- **Rational Euler bricks give integer ones.** If `a, b, c` are positive rationals and
`a² + b²`, `a² + c²`, `b² + c²` are rational squares, there is an integer Euler brick. -/
theorem exists_isEulerBrick_of_rat {a b c : ℚ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : IsSquare (a ^ 2 + b ^ 2)) (hac : IsSquare (a ^ 2 + c ^ 2))
    (hbc : IsSquare (b ^ 2 + c ^ 2)) : ∃ A B C : ℕ, IsEulerBrick A B C := by
  obtain ⟨d, hd0, hd⟩ := exists_pos_sq_of_isSquare (by positivity) hab
  obtain ⟨e, he0, he⟩ := exists_pos_sq_of_isSquare (by positivity) hac
  obtain ⟨f, hf0, hf⟩ := exists_pos_sq_of_isSquare (by positivity) hbc
  set M : ℕ := a.den * b.den * c.den * d.den * e.den * f.den with hMdef
  have nat {q : ℚ} (hq : 0 < q) (k : ℕ) (hk : M = q.den * k) :
      ∃ n : ℕ, 0 < n ∧ (n : ℚ) = M * q := by
    have hn := Rat.num_pos.mpr hq
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h0
      · have : 0 < M := by positivity
        omega
      · exact h0
    refine ⟨k * q.num.toNat, Nat.mul_pos hk0 (by omega), ?_⟩
    have h1 : ((q.num.toNat : ℕ) : ℚ) = q.num := by exact_mod_cast Int.toNat_of_nonneg hn.le
    rw [hk]
    push_cast
    rw [h1, ← Rat.mul_den_eq_num]
    ring
  obtain ⟨A, hA0, hA⟩ := nat ha (b.den * c.den * d.den * e.den * f.den) (by rw [hMdef]; ring)
  obtain ⟨B, hB0, hB⟩ := nat hb (a.den * c.den * d.den * e.den * f.den) (by rw [hMdef]; ring)
  obtain ⟨C, hC0, hC⟩ := nat hc (a.den * b.den * d.den * e.den * f.den) (by rw [hMdef]; ring)
  obtain ⟨D, -, hD⟩ := nat hd0 (a.den * b.den * c.den * e.den * f.den) (by rw [hMdef]; ring)
  obtain ⟨E, -, hE⟩ := nat he0 (a.den * b.den * c.den * d.den * f.den) (by rw [hMdef]; ring)
  obtain ⟨F, -, hF⟩ := nat hf0 (a.den * b.den * c.den * d.den * e.den) (by rw [hMdef]; ring)
  refine ⟨A, B, C, hA0, hB0, hC0, ⟨D, ?_⟩, ⟨F, ?_⟩, ⟨E, ?_⟩⟩
  · exact_mod_cast (show (A : ℚ) ^ 2 + B ^ 2 = D * D by
      rw [hA, hB, hD]; linear_combination (M : ℚ) ^ 2 * (-hd))
  · exact_mod_cast (show (B : ℚ) ^ 2 + C ^ 2 = F * F by
      rw [hB, hC, hF]; linear_combination (M : ℚ) ^ 2 * (-hf))
  · exact_mod_cast (show (C : ℚ) ^ 2 + A ^ 2 = E * E by
      rw [hC, hA, hE]; linear_combination (M : ℚ) ^ 2 * (-he))

end PerfectCuboid.Poly
