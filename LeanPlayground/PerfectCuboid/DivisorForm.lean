module

public import LeanPlayground.PerfectCuboid.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Rat.Lemmas

/-!
# The divisor form of the perfect cuboid problem

A perfect cuboid exists iff there are rationals `r₁, r₂, r₃ > 1` with
`r₁² + r₁⁻² + r₂² + r₂⁻² − r₃² − r₃⁻² = 2`.

For a cuboid with edges `a, b, c`, face diagonals `d² = a² + b²`, `e² = c² + a²`, `f² = b² + c²`
and space diagonal `g² = a² + b² + c² = a² + f²`, the three right triangles with leg `a` give
`a² = (d − b)(d + b) = (e − c)(e + c) = (g − f)(g + f)` (`edge_factorizations`), and
`r₁ = (d + b)/a`, `r₂ = (e + c)/a`, `r₃ = (g + f)/a` satisfy `rᵢ⁻¹ = (d − b)/a` etc., so
`rᵢ − rᵢ⁻¹ = 2b/a, 2c/a, 2f/a` and the equation is `b² + c² = f²`.
Conversely `A = 2`, `B = r₁ − r₁⁻¹`, `C = r₂ − r₂⁻¹` is a rational perfect cuboid with diagonals
`r₁ + r₁⁻¹`, `r₂ + r₂⁻¹`, `r₃ − r₃⁻¹`, `r₃ + r₃⁻¹`; clearing denominators gives an integral one.
No parity assumption is needed in either direction.
-/

@[expose] public section

namespace PerfectCuboid

/-- The three factorizations of `a²` coming from the three right triangles with leg `a`. -/
theorem edge_factorizations {a b c d e f g : ℤ} (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + f ^ 2) :
    a ^ 2 = (d - b) * (d + b) ∧ a ^ 2 = (e - c) * (e + c) ∧ a ^ 2 = (g - f) * (g + f) :=
  ⟨by linear_combination -hd, by linear_combination -he, by linear_combination -hg⟩

/-- Finitely many rationals have a common positive denominator. -/
theorem exists_common_den (xs : List ℚ) : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ xs, ∃ z : ℤ, x * N = z := by
  induction xs with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons y ys ih =>
    obtain ⟨N, hN, h⟩ := ih
    refine ⟨y.den * N, Nat.mul_pos y.den_pos hN, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨x.num * N, ?_⟩
      push_cast
      rw [← mul_assoc, Rat.mul_den_eq_num]
    · obtain ⟨z, hz⟩ := h x hx
      refine ⟨z * y.den, ?_⟩
      push_cast
      rw [mul_comm (y.den : ℚ), ← mul_assoc, hz]

/-- A nonnegative rational times a common denominator is a natural number. -/
theorem exists_nat_of_int {x : ℚ} {N : ℕ} {z : ℤ} (hx : 0 ≤ x) (_hN : 0 < N)
    (hz : x * N = z) : ∃ n : ℕ, x * N = n := by
  have hz0 : 0 ≤ z := by
    have : (0 : ℚ) ≤ z := hz ▸ mul_nonneg hx (Nat.cast_nonneg N)
    exact_mod_cast this
  exact ⟨z.toNat, by rw [hz]; exact_mod_cast (Int.toNat_of_nonneg hz0).symm⟩

/-- **Divisor form.** A perfect cuboid exists iff the surface
`r₁² + r₁⁻² + r₂² + r₂⁻² − r₃² − r₃⁻² = 2` has a rational point with all `rᵢ > 1`. -/
theorem exists_isPerfectCuboid_iff_divisor_form :
    (∃ a b c : ℕ, IsPerfectCuboid a b c) ↔
      ∃ r₁ r₂ r₃ : ℚ, 1 < r₁ ∧ 1 < r₂ ∧ 1 < r₃ ∧
        r₁ ^ 2 + r₁⁻¹ ^ 2 + r₂ ^ 2 + r₂⁻¹ ^ 2 - r₃ ^ 2 - r₃⁻¹ ^ 2 = 2 := by
  constructor
  · rintro ⟨a, b, c, h⟩
    obtain ⟨d, hd⟩ := h.sq_ab
    obtain ⟨f, hf⟩ := h.sq_bc
    obtain ⟨e, he⟩ := h.sq_ca
    obtain ⟨g, hg⟩ := h.sq_abc
    have ha : (0 : ℚ) < a := by exact_mod_cast h.pos_a
    have hb : (0 : ℚ) < b := by exact_mod_cast h.pos_b
    have hc : (0 : ℚ) < c := by exact_mod_cast h.pos_c
    have hd' : (a : ℚ) ^ 2 + b ^ 2 = d * d := by exact_mod_cast hd
    have hf' : (b : ℚ) ^ 2 + c ^ 2 = f * f := by exact_mod_cast hf
    have he' : (c : ℚ) ^ 2 + a ^ 2 = e * e := by exact_mod_cast he
    have hg' : (a : ℚ) ^ 2 + b ^ 2 + c ^ 2 = g * g := by exact_mod_cast hg
    have d0 : (0 : ℚ) ≤ d := Nat.cast_nonneg d
    have e0 : (0 : ℚ) ≤ e := Nat.cast_nonneg e
    have f0 : (0 : ℚ) ≤ f := Nat.cast_nonneg f
    have g0 : (0 : ℚ) ≤ g := Nat.cast_nonneg g
    -- each `r = (hyp + leg)/a` exceeds `1` and has inverse `(hyp − leg)/a`
    have key : ∀ x y : ℚ, 0 < y → 0 ≤ x → (a : ℚ) ^ 2 + y ^ 2 = x * x →
        1 < (x + y) / a ∧ ((x + y) / a)⁻¹ = (x - y) / a := by
      intro x y hy hx hxy
      have hax : (a : ℚ) < x := by nlinarith
      refine ⟨(one_lt_div ha).2 (by linarith), ?_⟩
      rw [inv_div, div_eq_div_iff (by linarith) ha.ne']
      linear_combination hxy
    obtain ⟨h1, i1⟩ := key d b hb d0 hd'
    obtain ⟨h2, i2⟩ := key e c hc e0 (by linear_combination he')
    have hfpos : (0 : ℚ) < f := by nlinarith
    obtain ⟨h3, i3⟩ := key g f hfpos g0 (by linear_combination hg' - hf')
    refine ⟨_, _, _, h1, h2, h3, ?_⟩
    rw [i1, i2, i3]
    field_simp
    linear_combination (-2 : ℚ) * hd' - 2 * he' + 2 * hg' + 2 * hf'
  · rintro ⟨r₁, r₂, r₃, h1, h2, h3, hE⟩
    have p1 : 0 < r₁ := by linarith
    have p2 : 0 < r₂ := by linarith
    have p3 : 0 < r₃ := by linarith
    -- `r − r⁻¹ > 0` and `(r + r⁻¹)² = 4 + (r − r⁻¹)²`
    have pos : ∀ r : ℚ, 1 < r → 0 < r - r⁻¹ := fun r hr => by
      have : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
      linarith
    have sqr : ∀ r : ℚ, 0 < r → (r + r⁻¹) ^ 2 = 2 ^ 2 + (r - r⁻¹) ^ 2 := fun r hr => by
      field_simp; ring
    have pyth : (r₃ - r₃⁻¹) ^ 2 = (r₁ - r₁⁻¹) ^ 2 + (r₂ - r₂⁻¹) ^ 2 := by
      have h1' : r₁ * r₁⁻¹ = 1 := mul_inv_cancel₀ p1.ne'
      have h2' : r₂ * r₂⁻¹ = 1 := mul_inv_cancel₀ p2.ne'
      have h3' : r₃ * r₃⁻¹ = 1 := mul_inv_cancel₀ p3.ne'
      linear_combination -hE + 2 * h1' + 2 * h2' - 2 * h3'
    obtain ⟨N, hN, hden⟩ := exists_common_den
      [2, r₁ - r₁⁻¹, r₂ - r₂⁻¹, r₁ + r₁⁻¹, r₂ + r₂⁻¹, r₃ - r₃⁻¹, r₃ + r₃⁻¹]
    have nat : ∀ x : ℚ, 0 ≤ x →
        x ∈ [2, r₁ - r₁⁻¹, r₂ - r₂⁻¹, r₁ + r₁⁻¹, r₂ + r₂⁻¹, r₃ - r₃⁻¹, r₃ + r₃⁻¹] →
        ∃ n : ℕ, x * N = n := fun x hx hmem => by
      obtain ⟨z, hz⟩ := hden x hmem
      exact exists_nat_of_int hx hN hz
    have q1 := pos r₁ h1
    have q2 := pos r₂ h2
    have q3 := pos r₃ h3
    have i1 : 0 < r₁⁻¹ := inv_pos.2 p1
    have i2 : 0 < r₂⁻¹ := inv_pos.2 p2
    have i3 : 0 < r₃⁻¹ := inv_pos.2 p3
    obtain ⟨nA, hA⟩ := nat 2 (by norm_num) (by simp)
    obtain ⟨nB, hB⟩ := nat _ q1.le (by simp)
    obtain ⟨nC, hC⟩ := nat _ q2.le (by simp)
    obtain ⟨nD, hD⟩ := nat (r₁ + r₁⁻¹) (by linarith) (by simp)
    obtain ⟨nE, hE'⟩ := nat (r₂ + r₂⁻¹) (by linarith) (by simp)
    obtain ⟨nF, hF⟩ := nat _ q3.le (by simp)
    obtain ⟨nG, hG⟩ := nat (r₃ + r₃⁻¹) (by linarith) (by simp)
    have hN' : (0 : ℚ) < N := by exact_mod_cast hN
    have posn : ∀ (x : ℚ) (n : ℕ), 0 < x → x * N = n → 0 < n := fun x n hx h => by
      have : (0 : ℚ) < n := h ▸ mul_pos hx hN'
      exact_mod_cast this
    -- every relation holds after multiplying by `N²`, then it is a relation in `ℕ`
    have rel : ∀ (x y z : ℚ) (nx ny nz : ℕ), x * N = nx → y * N = ny → z * N = nz →
        z ^ 2 = x ^ 2 + y ^ 2 → nz * nz = nx ^ 2 + ny ^ 2 := fun x y z nx ny nz hx hy hz h => by
      have : (nz : ℚ) * nz = (nx : ℚ) ^ 2 + (ny : ℚ) ^ 2 := by
        rw [← hx, ← hy, ← hz]; linear_combination (N : ℚ) ^ 2 * h
      exact_mod_cast this
    refine ⟨nA, nB, nC, ⟨⟨posn _ _ (by norm_num) hA, posn _ _ q1 hB, posn _ _ q2 hC,
      ⟨nD, (rel _ _ _ _ _ _ hA hB hD (sqr r₁ p1)).symm⟩,
      ⟨nF, (rel _ _ _ _ _ _ hB hC hF pyth).symm⟩,
      ⟨nE, ?_⟩⟩, ⟨nG, ?_⟩⟩⟩
    · rw [add_comm]; exact (rel _ _ _ _ _ _ hA hC hE' (sqr r₂ p2)).symm
    · have h4 : nG * nG = nA ^ 2 + nF ^ 2 := rel _ _ _ _ _ _ hA hF hG (sqr r₃ p3)
      have h5 : nF * nF = nB ^ 2 + nC ^ 2 := rel _ _ _ _ _ _ hB hC hF pyth
      rw [h4, pow_two nF, h5]; ring

end PerfectCuboid
