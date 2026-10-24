module

public import LeanPlayground.PerfectCuboid.Basic
public import Mathlib.Data.Int.Lemmas
public import Mathlib.RingTheory.Int.Basic

/-!
# The fiber `(m, n) = (2, 1)`: no perfect cuboid has two edges in ratio `3 : 4`

If a perfect cuboid `(X, Y, Z)` has `3 Z = 4 X`, then `X = 3k`, `Z = 4k` and both the face
diagonal `√(Y² + 16k²)` and the space diagonal `√(Y² + 25k²)` are integers. This is the fiber
`(m, n) = (2, 1)` of Peschmann's master-tuple parametrization (arXiv:2604.28072). We show that
it is empty by an elementary infinite descent: there are no integers `M, e ≠ 0` with
`M² + 16e²` and `M² + 25e²` both squares.

The underlying curve is `y² = x (x + 16)(x + 25)` (conductor 15, rank 0, torsion `ℤ/4 × ℤ/2`).
Rank 0 is not in Mathlib, so the descent is done by hand, in Fermat's style, and the elliptic
curve is never mentioned in the Lean code.

## Main results

* `not_sq_add_sixteen_sq_and_sq_add_twentyfive_sq` — if `p, q ≠ 0` and `p² + 16q² = r²`, then
  `p² + 25q²` is not a square.
* `not_isSquare_sq_add_sixteen_and_sq_add_twentyfive` — the same over `ℚ`: for `t ≠ 0`,
  `t² + 16` and `t² + 25` are not both squares.
* `not_isPerfectCuboid_three_four` — no perfect cuboid has `3 Z = 4 X`.

## The descent

Let `t = M/e`, `t² + 16 = z²`, `t² + 25 = w²`. Put `z + t = 4k`, `z − t = 4/k` and
`w + t = 5j`, `w − t = 5/j`. Then `t = 2(k − 1/k) = (5/2)(j − 1/j)`, so `(k, j)` lies on the
curve `4 j (k² − 1) = 5 k (j² − 1)`. (On the elliptic curve, the point with `x = t²` is twice the
point `R` with `x(R) = 20 k j`.) In lowest terms `k = k₁/k₂`, `j = j₁/j₂` this reads
`4 j₁j₂ (k₁² − k₂²) = 5 k₁k₂ (j₁² − j₂²)`, and `k₁k₂ ∣ 2e` (`exists_smaller`).

Since `k₁k₂` is coprime to `k₁² − k₂²`, and likewise for `j`, there is `λ ∣ 20` with
`4 j₁j₂ = λ k₁k₂` and `λ (k₁² − k₂²) = 5 (j₁² − j₂²)` (`core`). Replacing `k` by `−1/k` changes
the sign of `λ`, so `λ > 0`. For `λ = 2, 10` the left side of the second equation is `2 mod 4`,
which a difference of squares times an odd number never is (`false_of_two_mul`). In the four
remaining cases the four-number lemma writes `k₁, k₂, j₁, j₂` as products of `α, β, γ, δ`, and the
second equation becomes `α² X(β, γ) = δ² Y(β, γ)`. Coprimality gives `X = ρ δ²`, `Y = ρ α²`
with `ρ ∣ 9`; signs and a congruence mod 3 leave `ρ = 1` or `ρ = 9`. Each case gives a new
solution `t'` (up to the symmetries `k ↔ 1/k`, `j ↔ 1/j`):

| `λ` | `(k₁, k₂, j₁, j₂)` | equations (`ρ = 1`) | new `t'` |
|---|---|---|---|
| 20 | `(αβ, γδ, 5αγ, βδ)` | `β² − 4γ² = α²`, `25γ² − 4β² = δ²` | `2δ/α` |
| 5 | `(4αβ, γδ, 5αγ, βδ)` | `β² − γ² = α²`, `25γ² − 16β² = δ²` | `δ/α` |
| 5 | `(αβ, 4γδ, 5αγ, βδ)` | `β² − 16γ² = α²`, `25γ² − β² = δ²` | `4δ/α` |
| 4 | `(αβ, γδ, αγ, βδ)` | `5β² − 4γ² = α²`, `5γ² − 4β² = δ²` | `(βγ + αδ)/(β² − γ²)` |
| 1 | `(4αβ, γδ, αγ, βδ)` | `5β² − γ² = α²`, `5γ² − 16β² = δ²` | `2(βγ + αδ)/(4β² − γ²)` |

For `λ = 5, 20` the point `R` is itself twice a point and `t'` is a ratio of two of the new
variables. For `λ = 1, 4` the point `R` lies in the other class modulo `2E(ℚ)`; translating by
the 4-torsion point `(20, 180)` gives `t'`, and the square roots are again quadratic, e.g. for
`λ = 4`: `(βγ + αδ)² + 16(β² − γ²)² = (αγ + βδ)²` and
`(βγ + αδ)² + 25(β² − γ²)² = (αβ + γδ)²`.

In every case the new denominator `e'` satisfies `4e'² < (k₁k₂)² ≤ 4e²`, so `|e|` strictly
decreases (`not_isSol`). The inequality uses `(βγ + αδ)(βγ − αδ) = 20(β² − γ²)²` for `λ = 4` and
`= 5(4β² − γ²)²` for `λ = 1`, which also show that `t' ≠ 0`.
-/

@[expose] public section

namespace PerfectCuboid

namespace FiberTwoOne

/-- An integer solution of `M² + 16 e² = r²`, `M² + 25 e² = s²` with `M, e ≠ 0`. -/
def IsSol (M e r s : ℤ) : Prop :=
  M ≠ 0 ∧ e ≠ 0 ∧ M ^ 2 + 16 * e ^ 2 = r ^ 2 ∧ M ^ 2 + 25 * e ^ 2 = s ^ 2

/-! ### Small arithmetic facts -/

theorem three_dvd_of_three_dvd_sq_add_sq {a b : ℤ} (h : 3 ∣ a ^ 2 + b ^ 2) : 3 ∣ a ∧ 3 ∣ b := by
  have h' : (a ^ 2 + b ^ 2) % 3 = 0 := Int.emod_eq_zero_of_dvd h
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rw [Int.add_emod, pow_two, pow_two, Int.mul_emod, Int.mul_emod b] at h'
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> simp [ha, hb] at h'
  omega

theorem false_of_isCoprime_of_dvd {a b p : ℤ} (h : IsCoprime a b) (hp : 2 ≤ p) (ha : p ∣ a)
    (hb : p ∣ b) : False := by
  have := h.isUnit_of_dvd' ha hb
  rw [Int.isUnit_iff] at this
  omega

/-- `3 ∣ a² + b²` is impossible for coprime `a, b`. -/
theorem false_of_isCoprime_of_three_dvd {a b w : ℤ} (h : IsCoprime a b)
    (hab : 3 * (a ^ 2 + b ^ 2) = 3 * (3 * w)) : False := by
  obtain ⟨ha, hb⟩ :=
    three_dvd_of_three_dvd_sq_add_sq ⟨w, mul_left_cancel₀ three_ne_zero hab⟩
  exact false_of_isCoprime_of_dvd h (by norm_num) ha hb

theorem isCoprime_mul_sq_sub {a b : ℤ} (h : IsCoprime a b) : IsCoprime (a * b) (a ^ 2 - b ^ 2) := by
  have h1 : IsCoprime a (a ^ 2 - b ^ 2) := by
    have := (h.pow_right (n := 2)).neg_right.add_mul_left_right a
    convert this using 1
    ring
  have h2 : IsCoprime b (a ^ 2 - b ^ 2) := by
    have := (h.symm.pow_right (n := 2)).add_mul_left_right (-b)
    convert this using 1
    ring
  exact h1.mul_left h2

/-- If `a b = c d` then `a = αβ`, `b = γδ`, `c = αγ`, `d = βδ`. -/
theorem four_numbers {a b c d : ℤ} (h : a * b = c * d) (ha : a ≠ 0) :
    ∃ α β γ δ, a = α * β ∧ b = γ * δ ∧ c = α * γ ∧ d = β * δ := by
  obtain ⟨α, β, ⟨γ, rfl⟩, ⟨δ, rfl⟩, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (⟨b, h.symm⟩ : a ∣ c * d)
  refine ⟨α, β, γ, δ, rfl, ?_, rfl, rfl⟩
  exact mul_left_cancel₀ ha (by linear_combination h)

theorem four_dvd_or {a b : ℤ} (hc : IsCoprime a b) (h : 4 ∣ a * b) : 4 ∣ a ∨ 4 ∣ b := by
  have key : ∀ {x y : ℤ}, IsCoprime x y → 2 ∣ x → 4 ∣ x * y → 4 ∣ x := by
    intro x y hc hx h
    have hy : ¬ (2 : ℤ) ∣ y := fun hy => false_of_isCoprime_of_dvd hc le_rfl hx hy
    obtain ⟨k, hk⟩ : Odd y := Int.not_even_iff_odd.mp (fun he => hy (even_iff_two_dvd.mp he))
    have h4 : IsCoprime (4 : ℤ) y := ⟨-(k ^ 2 + k), y, by rw [hk]; ring⟩
    exact h4.dvd_of_dvd_mul_right h
  rcases Int.prime_two.dvd_or_dvd (dvd_trans ⟨2, by norm_num⟩ h) with ha | hb
  · exact Or.inl (key hc ha h)
  · exact Or.inr (key hc.symm hb (by rw [mul_comm]; exact h))

theorem five_dvd_or {a b : ℤ} (h : 5 ∣ a * b) : 5 ∣ a ∨ 5 ∣ b :=
  (Int.prime_iff_natAbs_prime.mpr (show Nat.Prime (Int.natAbs 5) from Nat.prime_five)).dvd_or_dvd h

/-- Coprime factors: `α² X = δ² Y` with `α, δ` coprime forces `X = ρ δ²`, `Y = ρ α²`. -/
theorem exists_rho {α δ X Y : ℤ} (hc : IsCoprime α δ) (hα : α ≠ 0)
    (h : α ^ 2 * X = δ ^ 2 * Y) : ∃ ρ, X = ρ * δ ^ 2 ∧ Y = ρ * α ^ 2 := by
  obtain ⟨ρ, hρ⟩ : α ^ 2 ∣ Y :=
    (hc.pow (m := 2) (n := 2)).dvd_of_dvd_mul_right ⟨X, by linear_combination -h⟩
  refine ⟨ρ, ?_, by rw [hρ]; ring⟩
  exact mul_left_cancel₀ (pow_ne_zero 2 hα) (by rw [h, hρ]; ring)

theorem dvd_nine {ρ β γ : ℤ} (hc : IsCoprime β γ) (h1 : ρ ∣ 9 * β ^ 2) (h2 : ρ ∣ 9 * γ ^ 2) :
    ρ ∣ 9 := by
  obtain ⟨u, v, huv⟩ := hc.pow (m := 2) (n := 2)
  have : (9 : ℤ) = u * (9 * β ^ 2) + v * (9 * γ ^ 2) := by linear_combination -9 * huv
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)

theorem rho_cases {ρ : ℤ} (h : ρ ∣ 9) : ρ = 1 ∨ ρ = 9 ∨ ρ = 3 ∨ ρ < 0 := by
  have h9 : ρ ≤ 9 := Int.le_of_dvd (by norm_num) h
  rcases lt_or_ge ρ 0 with hρ | hρ
  · exact Or.inr (Or.inr (Or.inr hρ))
  · interval_cases ρ <;> omega

theorem eq_of_nine_mul {a b : ℤ} (h : 9 * a = 9 * b) : a = b :=
  mul_left_cancel₀ (by norm_num) h

theorem four_mul_lt {a b c : ℤ} (ha : 0 < a) (hb : 5 ≤ b) (hc : 1 ≤ c) : 4 * a < a * b * c := by
  nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg ha.le (by omega : (0 : ℤ) ≤ b))]

theorem one_le_sq {a : ℤ} (ha : a ≠ 0) : 1 ≤ a ^ 2 := by
  have : 0 < a ^ 2 := by positivity
  omega

/-- `λ = 2` and `λ = 10` are impossible: the left side is `2` modulo `4`, the right side is not. -/
theorem false_of_two_mul {k1 k2 j1 j2 c : ℤ} (hk : IsCoprime k1 k2) (h2 : 2 ∣ k1 * k2)
    (hc : Odd c) (h : 2 * (k1 ^ 2 - k2 ^ 2) = c * (j1 ^ 2 - j2 ^ 2)) : False := by
  have hodd : Odd (k1 ^ 2 - k2 ^ 2) := by
    rw [← Int.not_even_iff_odd, Int.even_sub, Int.even_pow' two_ne_zero,
      Int.even_pow' two_ne_zero, even_iff_two_dvd, even_iff_two_dvd]
    rcases Int.prime_two.dvd_or_dvd h2 with h1 | h1
    · have : ¬ (2 : ℤ) ∣ k2 := fun h' => false_of_isCoprime_of_dvd hk le_rfl h1 h'
      tauto
    · have : ¬ (2 : ℤ) ∣ k1 := fun h' => false_of_isCoprime_of_dvd hk le_rfl h' h1
      tauto
  obtain ⟨m, hm⟩ := hodd
  rcases Int.even_or_odd (j1 - j2) with ⟨p, hp⟩ | ⟨p, hp⟩
  · have hj1 : j1 = p + p + j2 := by omega
    rw [hj1] at h
    have : 4 * m + 2 = 4 * (c * p * (p + j2)) := by linear_combination h - 2 * hm
    omega
  · have hj1 : j1 = 2 * p + 1 + j2 := by omega
    rw [hj1] at h
    have hodd' : Odd (c * ((2 * p + 1) * (2 * (p + j2) + 1))) :=
      hc.mul ((odd_two_mul_add_one p).mul (odd_two_mul_add_one _))
    apply Int.not_even_iff_odd.mpr hodd'
    exact ⟨2 * m + 1, by linear_combination -h + 2 * hm⟩

/-! ### The five descent cases -/

theorem caseS20 {α β γ δ : ℤ} (hα : α ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (had : IsCoprime α δ) (hbg : IsCoprime β γ)
    (h : α ^ 2 * (25 * γ ^ 2 - 4 * β ^ 2) = δ ^ 2 * (β ^ 2 - 4 * γ ^ 2)) :
    ∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (α * β * (γ * δ)) ^ 2 := by
  obtain ⟨ρ, hX, hY⟩ := exists_rho had hα h
  have h9 : ρ ∣ 9 := dvd_nine hbg ⟨4 * δ ^ 2 + 25 * α ^ 2, by linear_combination 4 * hX + 25 * hY⟩
    ⟨δ ^ 2 + 4 * α ^ 2, by linear_combination hX + 4 * hY⟩
  have ha2 := one_le_sq hα
  have hg2 := one_le_sq hγ
  have hd2 := one_le_sq hδ
  have hprod : (α * β * (γ * δ)) ^ 2 = α ^ 2 * β ^ 2 * (γ ^ 2 * δ ^ 2) := by ring
  have hgd : 1 ≤ γ ^ 2 * δ ^ 2 := one_le_mul_of_one_le_of_one_le hg2 hd2
  rcases rho_cases h9 with rfl | rfl | rfl | hneg
  · refine ⟨2 * δ, α, 6 * γ, 3 * β, ⟨mul_ne_zero two_ne_zero hδ, hα, ?_, ?_⟩, ?_⟩
    · linear_combination -4 * hX - 16 * hY
    · linear_combination -4 * hX - 25 * hY
    · rw [hprod]; exact four_mul_lt (by omega) (by nlinarith) hgd
  · refine ⟨2 * δ, α, 2 * γ, β, ⟨mul_ne_zero two_ne_zero hδ, hα, ?_, ?_⟩, ?_⟩
    · exact eq_of_nine_mul (by linear_combination -4 * hX - 16 * hY)
    · exact eq_of_nine_mul (by linear_combination -4 * hX - 25 * hY)
    · rw [hprod]; exact four_mul_lt (by omega) (by nlinarith) hgd
  · exact (false_of_isCoprime_of_three_dvd had.symm (w := γ ^ 2 - α ^ 2)
      (by linear_combination -hX - 4 * hY)).elim
  · nlinarith [mul_neg_of_neg_of_pos hneg (by positivity : (0 : ℤ) < δ ^ 2 + 4 * α ^ 2)]

theorem caseS5a {α β γ δ : ℤ} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (had : IsCoprime α δ) (hbg : IsCoprime β γ)
    (h : α ^ 2 * (25 * γ ^ 2 - 16 * β ^ 2) = δ ^ 2 * (β ^ 2 - γ ^ 2)) :
    ∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (4 * (α * β) * (γ * δ)) ^ 2 := by
  obtain ⟨ρ, hX, hY⟩ := exists_rho had hα h
  have h9 : ρ ∣ 9 := dvd_nine hbg ⟨δ ^ 2 + 25 * α ^ 2, by linear_combination hX + 25 * hY⟩
    ⟨δ ^ 2 + 16 * α ^ 2, by linear_combination hX + 16 * hY⟩
  have ha2 := one_le_sq hα
  have hb2 := one_le_sq hβ
  have hg2 := one_le_sq hγ
  have hd2 := one_le_sq hδ
  have hprod : (4 * (α * β) * (γ * δ)) ^ 2 = α ^ 2 * (16 * β ^ 2) * (γ ^ 2 * δ ^ 2) := by ring
  have hgd : 1 ≤ γ ^ 2 * δ ^ 2 := one_le_mul_of_one_le_of_one_le hg2 hd2
  rcases rho_cases h9 with rfl | rfl | rfl | hneg
  · refine ⟨δ, α, 3 * γ, 3 * β, ⟨hδ, hα, ?_, ?_⟩, ?_⟩
    · linear_combination -hX - 16 * hY
    · linear_combination -hX - 25 * hY
    · rw [hprod]; exact four_mul_lt (by omega) (by omega) hgd
  · refine ⟨δ, α, γ, β, ⟨hδ, hα, ?_, ?_⟩, ?_⟩
    · exact eq_of_nine_mul (by linear_combination -hX - 16 * hY)
    · exact eq_of_nine_mul (by linear_combination -hX - 25 * hY)
    · rw [hprod]; exact four_mul_lt (by omega) (by omega) hgd
  · exact (false_of_isCoprime_of_three_dvd had.symm (w := γ ^ 2 - 5 * α ^ 2)
      (by linear_combination -hX - 16 * hY)).elim
  · nlinarith [mul_neg_of_neg_of_pos hneg (by positivity : (0 : ℤ) < δ ^ 2 + 16 * α ^ 2)]

theorem caseS5b {α β γ δ : ℤ} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (had : IsCoprime α δ) (hbg : IsCoprime β γ)
    (h : α ^ 2 * (25 * γ ^ 2 - β ^ 2) = δ ^ 2 * (β ^ 2 - 16 * γ ^ 2)) :
    ∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (α * β * (4 * (γ * δ))) ^ 2 := by
  obtain ⟨ρ, hX, hY⟩ := exists_rho had hα h
  have h9 : ρ ∣ 9 := dvd_nine hbg
    ⟨16 * δ ^ 2 + 25 * α ^ 2, by linear_combination 16 * hX + 25 * hY⟩
    ⟨δ ^ 2 + α ^ 2, by linear_combination hX + hY⟩
  have ha2 := one_le_sq hα
  have hb2 := one_le_sq hβ
  have hg2 := one_le_sq hγ
  have hd2 := one_le_sq hδ
  have hprod : (α * β * (4 * (γ * δ))) ^ 2 = α ^ 2 * (16 * β ^ 2) * (γ ^ 2 * δ ^ 2) := by ring
  have hgd : 1 ≤ γ ^ 2 * δ ^ 2 := one_le_mul_of_one_le_of_one_le hg2 hd2
  rcases rho_cases h9 with rfl | rfl | rfl | hneg
  · refine ⟨4 * δ, α, 12 * γ, 3 * β, ⟨mul_ne_zero (by norm_num) hδ, hα, ?_, ?_⟩, ?_⟩
    · linear_combination -16 * hX - 16 * hY
    · linear_combination -16 * hX - 25 * hY
    · rw [hprod]; exact four_mul_lt (by omega) (by omega) hgd
  · refine ⟨4 * δ, α, 4 * γ, β, ⟨mul_ne_zero (by norm_num) hδ, hα, ?_, ?_⟩, ?_⟩
    · exact eq_of_nine_mul (by linear_combination -16 * hX - 16 * hY)
    · exact eq_of_nine_mul (by linear_combination -16 * hX - 25 * hY)
    · rw [hprod]; exact four_mul_lt (by omega) (by omega) hgd
  · exact (false_of_isCoprime_of_three_dvd had.symm (w := γ ^ 2)
      (by linear_combination -hX - hY)).elim
  · nlinarith [mul_neg_of_neg_of_pos hneg (by positivity : (0 : ℤ) < δ ^ 2 + α ^ 2)]

theorem caseS4 {α β γ δ : ℤ} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (had : IsCoprime α δ) (hbg : IsCoprime β γ) (hne : (α * β) ^ 2 ≠ (γ * δ) ^ 2)
    (h : α ^ 2 * (5 * γ ^ 2 - 4 * β ^ 2) = δ ^ 2 * (5 * β ^ 2 - 4 * γ ^ 2)) :
    ∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (α * β * (γ * δ)) ^ 2 := by
  obtain ⟨ρ, hX, hY⟩ := exists_rho had hα h
  have h9 : ρ ∣ 9 := dvd_nine hbg ⟨4 * δ ^ 2 + 5 * α ^ 2, by linear_combination 4 * hX + 5 * hY⟩
    ⟨5 * δ ^ 2 + 4 * α ^ 2, by linear_combination 5 * hX + 4 * hY⟩
  have ha2 := one_le_sq hα
  have hd2 := one_le_sq hδ
  rcases rho_cases h9 with rfl | rfl | rfl | hneg
  · have hid : (β * γ + α * δ) * (β * γ - α * δ) = 20 * (β ^ 2 - γ ^ 2) ^ 2 := by
      linear_combination α ^ 2 * hX + (5 * γ ^ 2 - 4 * β ^ 2) * hY
    have he : β ^ 2 - γ ^ 2 ≠ 0 := by
      intro h0
      have hu : IsUnit (β ^ 2) := by
        rw [← isCoprime_self]
        have := hbg.pow (m := 2) (n := 2)
        rwa [show γ ^ 2 = β ^ 2 by linear_combination -h0] at this
      rw [Int.isUnit_iff] at hu
      have hb1 : β ^ 2 = 1 := hu.resolve_right (by nlinarith [sq_nonneg β])
      have hg1 : γ ^ 2 = 1 := by linarith
      have ha1 : α ^ 2 = 1 := by linarith
      have hd1 : δ ^ 2 = 1 := by linarith
      exact hne (by rw [mul_pow, mul_pow, ha1, hb1, hg1, hd1])
    have hM : β * γ + α * δ ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hid
      exact he (pow_eq_zero_iff two_ne_zero |>.mp (by linarith))
    refine ⟨β * γ + α * δ, β ^ 2 - γ ^ 2, α * γ + β * δ, α * β + γ * δ,
      ⟨hM, he, ?_, ?_⟩, ?_⟩
    · linear_combination (-4 * (β ^ 2 - γ ^ 2)) * hX + (-(δ ^ 2 - γ ^ 2)) * hY
    · refine mul_left_cancel₀ (four_ne_zero (α := ℤ)) ?_
      linear_combination (α ^ 2 - 25 * β ^ 2 + 24 * γ ^ 2) * hX + (-5 * (δ ^ 2 - γ ^ 2)) * hY
    · have had2 : 1 ≤ α ^ 2 * δ ^ 2 := one_le_mul_of_one_le_of_one_le ha2 hd2
      have hbg2 : 0 ≤ β ^ 2 * γ ^ 2 := by positivity
      have : β ^ 2 * γ ^ 2 * 1 ≤ β ^ 2 * γ ^ 2 * (α ^ 2 * δ ^ 2) :=
        mul_le_mul_of_nonneg_left had2 hbg2
      have e1 : (α * β * (γ * δ)) ^ 2 = β ^ 2 * γ ^ 2 * (α ^ 2 * δ ^ 2) := by ring
      have e2 : (β * γ + α * δ) * (β * γ - α * δ) = β ^ 2 * γ ^ 2 - α ^ 2 * δ ^ 2 := by ring
      rw [e1]
      nlinarith [sq_nonneg (β ^ 2 - γ ^ 2)]
  · exact (false_of_isCoprime_of_three_dvd hbg (w := 3 * (δ ^ 2 + α ^ 2))
      (by linear_combination 3 * hX + 3 * hY)).elim
  · exact (false_of_isCoprime_of_three_dvd hbg (w := δ ^ 2 + α ^ 2)
      (by linear_combination 3 * hX + 3 * hY)).elim
  · nlinarith [mul_neg_of_neg_of_pos hneg (by positivity : (0 : ℤ) < δ ^ 2 + α ^ 2),
      sq_nonneg β, sq_nonneg γ]

theorem caseS1 {α β γ δ : ℤ} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (hk : IsCoprime (4 * (α * β)) (γ * δ))
    (h : α ^ 2 * (5 * γ ^ 2 - 16 * β ^ 2) = δ ^ 2 * (5 * β ^ 2 - γ ^ 2)) :
    ∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (4 * (α * β) * (γ * δ)) ^ 2 := by
  have hk' := hk.of_mul_left_right
  have had : IsCoprime α δ := hk'.of_mul_left_left.of_mul_right_right
  have hbg : IsCoprime β γ := hk'.of_mul_left_right.of_mul_right_left
  obtain ⟨ρ, hX, hY⟩ := exists_rho had hα h
  have h9 : ρ ∣ 9 := dvd_nine hbg ⟨δ ^ 2 + 5 * α ^ 2, by linear_combination hX + 5 * hY⟩
    ⟨5 * δ ^ 2 + 16 * α ^ 2, by linear_combination 5 * hX + 16 * hY⟩
  have ha2 := one_le_sq hα
  have hd2 := one_le_sq hδ
  rcases rho_cases h9 with rfl | rfl | rfl | hneg
  · have hid : (β * γ + α * δ) * (β * γ - α * δ) = 5 * (4 * β ^ 2 - γ ^ 2) ^ 2 := by
      linear_combination α ^ 2 * hX + (5 * γ ^ 2 - 16 * β ^ 2) * hY
    have he : 4 * β ^ 2 - γ ^ 2 ≠ 0 := by
      intro h0
      have h2 : (2 : ℤ) ∣ γ := by
        rcases (Commute.all γ (2 * β)).sq_eq_sq_iff_eq_or_eq_neg.mp
          (by linear_combination -h0) with h | h
        · exact ⟨β, h⟩
        · exact ⟨-β, by rw [h]; ring⟩
      exact false_of_isCoprime_of_dvd hk le_rfl ⟨2 * (α * β), by ring⟩ (dvd_mul_of_dvd_left h2 δ)
    have hM : 2 * (β * γ + α * δ) ≠ 0 := by
      intro h0
      have h0' : β * γ + α * δ = 0 := by linarith
      rw [h0', zero_mul] at hid
      exact he (pow_eq_zero_iff two_ne_zero |>.mp (by linarith))
    refine ⟨2 * (β * γ + α * δ), 4 * β ^ 2 - γ ^ 2, 2 * (α * γ + β * δ), 4 * (α * β) + γ * δ,
      ⟨hM, he, ?_, ?_⟩, ?_⟩
    · linear_combination (-4 * (4 * β ^ 2 - γ ^ 2)) * hX + (-4 * (δ ^ 2 - γ ^ 2)) * hY
    · linear_combination (α ^ 2 - 25 * β ^ 2 + 6 * γ ^ 2) * hX + (-5 * (δ ^ 2 - γ ^ 2)) * hY
    · have had2 : 1 ≤ α ^ 2 * δ ^ 2 := one_le_mul_of_one_le_of_one_le ha2 hd2
      have hbg2 : 0 ≤ β ^ 2 * γ ^ 2 := by positivity
      have : β ^ 2 * γ ^ 2 * 1 ≤ β ^ 2 * γ ^ 2 * (α ^ 2 * δ ^ 2) :=
        mul_le_mul_of_nonneg_left had2 hbg2
      have e1 : (4 * (α * β) * (γ * δ)) ^ 2 = 16 * (β ^ 2 * γ ^ 2 * (α ^ 2 * δ ^ 2)) := by ring
      have e2 : (β * γ + α * δ) * (β * γ - α * δ) = β ^ 2 * γ ^ 2 - α ^ 2 * δ ^ 2 := by ring
      rw [e1]
      nlinarith [sq_nonneg (4 * β ^ 2 - γ ^ 2)]
  · exact (false_of_isCoprime_of_three_dvd hbg (w := 2 * β ^ 2 - 3 * α ^ 2)
      (by linear_combination -3 * hY)).elim
  · exact (false_of_isCoprime_of_three_dvd hbg (w := 2 * β ^ 2 - α ^ 2)
      (by linear_combination -3 * hY)).elim
  · nlinarith [mul_neg_of_neg_of_pos hneg (by positivity : (0 : ℤ) < δ ^ 2 + 5 * α ^ 2),
      sq_nonneg β, sq_nonneg γ]

/-! ### The cases `λ = 1, 4, 5, 20` -/

theorem lam1 {k1 k2 j1 j2 : ℤ} (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0) (hk : IsCoprime k1 k2)
    (h4k : 4 ∣ k1) (h4 : 4 * (j1 * j2) = 1 * (k1 * k2))
    (h5 : 1 * (k1 ^ 2 - k2 ^ 2) = 5 * (j1 ^ 2 - j2 ^ 2)) :
    ∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (k1 * k2) ^ 2 := by
  obtain ⟨a, rfl⟩ := h4k
  have ha : a ≠ 0 := right_ne_zero_of_mul hk1
  obtain ⟨α, β, γ, δ, rfl, rfl, rfl, rfl⟩ :=
    four_numbers (mul_left_cancel₀ four_ne_zero (by linear_combination -h4) : a * k2 = j1 * j2) ha
  exact caseS1 (left_ne_zero_of_mul ha) (right_ne_zero_of_mul ha) (left_ne_zero_of_mul hk2)
    (right_ne_zero_of_mul hk2) hk (by linear_combination -h5)

theorem lam4 {k1 k2 j1 j2 : ℤ} (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0) (hk : IsCoprime k1 k2)
    (hne : k1 ^ 2 ≠ k2 ^ 2) (h4 : k1 * k2 = j1 * j2)
    (h5 : 4 * (k1 ^ 2 - k2 ^ 2) = 5 * (j1 ^ 2 - j2 ^ 2)) :
    ∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (k1 * k2) ^ 2 := by
  obtain ⟨α, β, γ, δ, rfl, rfl, rfl, rfl⟩ := four_numbers h4 hk1
  exact caseS4 (left_ne_zero_of_mul hk1) (right_ne_zero_of_mul hk1) (left_ne_zero_of_mul hk2)
    (right_ne_zero_of_mul hk2) hk.of_mul_left_left.of_mul_right_right
    hk.of_mul_left_right.of_mul_right_left hne (by linear_combination -h5)

theorem lam5 {k1 k2 j1 j2 : ℤ} (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0) (hk : IsCoprime k1 k2)
    (h5j : 5 ∣ j1) (h4 : 4 * (j1 * j2) = 5 * (k1 * k2))
    (h5 : 5 * (k1 ^ 2 - k2 ^ 2) = 5 * (j1 ^ 2 - j2 ^ 2)) :
    ∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (k1 * k2) ^ 2 := by
  have h5' : k1 ^ 2 - k2 ^ 2 = j1 ^ 2 - j2 ^ 2 := mul_left_cancel₀ (by norm_num) h5
  obtain ⟨b, rfl⟩ := h5j
  have h4' : k1 * k2 = 4 * (b * j2) :=
    mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) (by linear_combination -h4)
  rcases four_dvd_or hk ⟨b * j2, h4'⟩ with ⟨a, rfl⟩ | ⟨c, rfl⟩
  · have ha : a ≠ 0 := right_ne_zero_of_mul hk1
    obtain ⟨α, β, γ, δ, rfl, rfl, rfl, rfl⟩ :=
      four_numbers (mul_left_cancel₀ four_ne_zero (by linear_combination h4') : a * k2 = b * j2) ha
    have hk' := hk.of_mul_left_right
    exact caseS5a (left_ne_zero_of_mul ha) (right_ne_zero_of_mul ha) (left_ne_zero_of_mul hk2)
      (right_ne_zero_of_mul hk2) hk'.of_mul_left_left.of_mul_right_right
      hk'.of_mul_left_right.of_mul_right_left (by linear_combination -h5')
  · have hc : c ≠ 0 := right_ne_zero_of_mul hk2
    obtain ⟨α, β, γ, δ, rfl, rfl, rfl, rfl⟩ :=
      four_numbers (mul_left_cancel₀ four_ne_zero (by linear_combination h4') : k1 * c = b * j2)
        hk1
    have hk' := hk.of_mul_right_right
    exact caseS5b (left_ne_zero_of_mul hk1) (right_ne_zero_of_mul hk1) (left_ne_zero_of_mul hc)
      (right_ne_zero_of_mul hc) hk'.of_mul_left_left.of_mul_right_right
      hk'.of_mul_left_right.of_mul_right_left (by linear_combination -h5')

theorem lam20 {k1 k2 j1 j2 : ℤ} (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0) (hk : IsCoprime k1 k2)
    (h5j : 5 ∣ j1) (h4 : 4 * (j1 * j2) = 20 * (k1 * k2))
    (h5 : 20 * (k1 ^ 2 - k2 ^ 2) = 5 * (j1 ^ 2 - j2 ^ 2)) :
    ∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (k1 * k2) ^ 2 := by
  have h5' : 4 * (k1 ^ 2 - k2 ^ 2) = j1 ^ 2 - j2 ^ 2 :=
    mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) (by linear_combination h5)
  obtain ⟨b, rfl⟩ := h5j
  obtain ⟨α, β, γ, δ, rfl, rfl, rfl, rfl⟩ :=
    four_numbers (mul_left_cancel₀ (by norm_num : (20 : ℤ) ≠ 0) (by linear_combination -h4) :
      k1 * k2 = b * j2) hk1
  exact caseS20 (left_ne_zero_of_mul hk1) (left_ne_zero_of_mul hk2) (right_ne_zero_of_mul hk2)
    hk.of_mul_left_left.of_mul_right_right hk.of_mul_left_right.of_mul_right_left
    (by linear_combination -h5')

/-- The descent for a point of the curve `4 j (k² − 1) = 5 k (j² − 1)` with `λ > 0`. -/
theorem core_pos {k1 k2 j1 j2 l : ℤ} (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0) (hk : IsCoprime k1 k2)
    (hne : k1 ^ 2 ≠ k2 ^ 2) (hl : 0 < l) (hl20 : l ∣ 20) (h4 : 4 * (j1 * j2) = l * (k1 * k2))
    (h5 : l * (k1 ^ 2 - k2 ^ 2) = 5 * (j1 ^ 2 - j2 ^ 2)) :
    ∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (k1 * k2) ^ 2 := by
  have hle : l ≤ 20 := Int.le_of_dvd (by norm_num) hl20
  have swap : (∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (k2 * k1) ^ 2) →
      ∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (k1 * k2) ^ 2 := by
    rintro ⟨M, e, r, s, hs, hb⟩
    exact ⟨M, e, r, s, hs, by rw [mul_comm k1]; exact hb⟩
  interval_cases l <;> try omega
  · rcases four_dvd_or hk ⟨j1 * j2, by linear_combination -h4⟩ with h | h
    · exact lam1 hk1 hk2 hk h h4 h5
    · exact swap (lam1 (j1 := j2) (j2 := j1) hk2 hk1 hk.symm h (by linear_combination h4)
        (by linear_combination -h5))
  · exact (false_of_two_mul hk ⟨j1 * j2, by linarith⟩ ⟨2, by norm_num⟩ h5).elim
  · exact lam4 hk1 hk2 hk hne (by linarith) h5
  · have h5d : (5 : ℤ) ∣ j1 * j2 * 4 := ⟨k1 * k2, by linear_combination h4⟩
    have hc54 : IsCoprime (5 : ℤ) 4 := ⟨1, -1, by norm_num⟩
    rcases five_dvd_or (hc54.dvd_of_dvd_mul_right h5d) with h | h
    · exact lam5 hk1 hk2 hk h h4 h5
    · exact swap (lam5 (j1 := j2) (j2 := j1) hk2 hk1 hk.symm h (by linear_combination h4)
        (by linear_combination -h5))
  · have h2d : (2 : ℤ) ∣ k1 * k2 * 5 := ⟨j1 * j2, by linarith⟩
    exact (false_of_two_mul (j1 := j1) (j2 := j2) hk
      (IsCoprime.dvd_of_dvd_mul_right (⟨-2, 1, by norm_num⟩ : IsCoprime (2 : ℤ) 5) h2d) odd_one
      (by linarith)).elim
  · rcases five_dvd_or (⟨k1 * k2, by linarith⟩ : (5 : ℤ) ∣ j1 * j2) with h | h
    · exact lam20 hk1 hk2 hk h h4 h5
    · exact swap (lam20 (j1 := j2) (j2 := j1) hk2 hk1 hk.symm h (by linear_combination h4)
        (by linear_combination -h5))

/-- The descent for a point of the curve `4 j (k² − 1) = 5 k (j² − 1)`, `k = k₁/k₂`,
`j = j₁/j₂`. -/
theorem core {k1 k2 j1 j2 : ℤ} (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0) (hj1 : j1 ≠ 0) (hj2 : j2 ≠ 0)
    (hk : IsCoprime k1 k2) (hj : IsCoprime j1 j2) (hne : k1 ^ 2 ≠ k2 ^ 2)
    (hC : 4 * (j1 * j2) * (k1 ^ 2 - k2 ^ 2) = 5 * (k1 * k2) * (j1 ^ 2 - j2 ^ 2)) :
    ∃ M e r s, IsSol M e r s ∧ 4 * e ^ 2 < (k1 * k2) ^ 2 := by
  have hA : k1 * k2 ≠ 0 := mul_ne_zero hk1 hk2
  have hJ : j1 * j2 ≠ 0 := mul_ne_zero hj1 hj2
  obtain ⟨l, hl⟩ : k1 * k2 ∣ 4 * (j1 * j2) := (isCoprime_mul_sq_sub hk).dvd_of_dvd_mul_right
    ⟨5 * (j1 ^ 2 - j2 ^ 2), by linear_combination hC⟩
  obtain ⟨μ, hμ⟩ : j1 * j2 ∣ 5 * (k1 * k2) := (isCoprime_mul_sq_sub hj).dvd_of_dvd_mul_right
    ⟨4 * (k1 ^ 2 - k2 ^ 2), by linear_combination -hC⟩
  have hlμ : l * μ = 20 := by
    refine mul_left_cancel₀ (mul_ne_zero hA hJ) ?_
    linear_combination (-(k1 * k2 * l)) * hμ - 5 * (k1 * k2) * hl
  have h5 : l * (k1 ^ 2 - k2 ^ 2) = 5 * (j1 ^ 2 - j2 ^ 2) := by
    refine mul_left_cancel₀ hA ?_
    linear_combination hC - (k1 ^ 2 - k2 ^ 2) * hl
  have h4 : 4 * (j1 * j2) = l * (k1 * k2) := by rw [hl]; ring
  rcases lt_or_gt_of_ne (show l ≠ 0 by rintro rfl; simp at hlμ) with hneg | hpos
  · obtain ⟨M, e, r, s, hs, hb⟩ := core_pos (k1 := -k2) (k2 := k1) (j1 := j1) (j2 := j2)
      (l := -l) (neg_ne_zero.mpr hk2) hk1 hk.symm.neg_left (by rw [neg_sq]; exact Ne.symm hne)
      (by linarith) ⟨-μ, by linear_combination -hlμ⟩ (by linear_combination h4)
      (by linear_combination h5)
    exact ⟨M, e, r, s, hs, by linear_combination hb⟩
  · exact core_pos hk1 hk2 hk hne hpos ⟨μ, hlμ.symm⟩ h4 h5

/-! ### From a solution to a point of the curve, and the descent -/

theorem exists_smaller {M e r s : ℤ} (h : IsSol M e r s) :
    ∃ M' e' r' s', IsSol M' e' r' s' ∧ e' ^ 2 < e ^ 2 := by
  obtain ⟨hM, he, hr, hs⟩ := h
  have he2 : 0 < e ^ 2 := by positivity
  have hrM : r + M ≠ 0 := fun h0 => by
    rw [show r = -M by linarith] at hr
    linarith
  have hsM : s + M ≠ 0 := fun h0 => by
    rw [show s = -M by linarith] at hs
    linarith
  obtain ⟨g, k1, k2, hg, hkg, hk1g, hk2g⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left (4 * e) hrM)
  obtain ⟨g', j1, j2, hg', hjg, hj1g, hj2g⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left (5 * e) hsM)
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hg0' : (g' : ℤ) ≠ 0 := by exact_mod_cast hg'.ne'
  have hk : IsCoprime k1 k2 := Int.isCoprime_iff_gcd_eq_one.mpr hkg
  have hj : IsCoprime j1 j2 := Int.isCoprime_iff_gcd_eq_one.mpr hjg
  have hk1 : k1 ≠ 0 := by rintro rfl; exact hrM (by rw [hk1g]; ring)
  have hk2 : k2 ≠ 0 := by rintro rfl; exact he (by linarith)
  have hj1 : j1 ≠ 0 := by rintro rfl; exact hsM (by rw [hj1g]; ring)
  have hj2 : j2 ≠ 0 := by rintro rfl; exact he (by linarith)
  have hk3 : k1 * (r - M) = k2 ^ 2 * g := by
    refine mul_left_cancel₀ hg0 ?_
    linear_combination -(r - M) * hk1g - hr + (4 * e + k2 * g) * hk2g
  have hj3 : j1 * (s - M) = j2 ^ 2 * g' := by
    refine mul_left_cancel₀ hg0' ?_
    linear_combination -(s - M) * hj1g - hs + (5 * e + j2 * g') * hj2g
  have R1 : 2 * e * (k1 ^ 2 - k2 ^ 2) = M * (k1 * k2) := by
    refine mul_left_cancel₀ (mul_ne_zero two_ne_zero hg0) ?_
    linear_combination g * (k1 ^ 2 - k2 ^ 2) * hk2g - g * k1 * k2 * hk1g + g * k2 * hk3
  have R2 : 5 * e * (j1 ^ 2 - j2 ^ 2) = 2 * M * (j1 * j2) := by
    refine mul_left_cancel₀ (mul_ne_zero two_ne_zero hg0') ?_
    linear_combination 2 * g' * (j1 ^ 2 - j2 ^ 2) * hj2g - 2 * g' * j1 * j2 * hj1g
      + 2 * g' * j2 * hj3
  have hC : 4 * (j1 * j2) * (k1 ^ 2 - k2 ^ 2) = 5 * (k1 * k2) * (j1 ^ 2 - j2 ^ 2) := by
    refine mul_left_cancel₀ (mul_ne_zero (by norm_num : (10 : ℤ) ≠ 0) he) ?_
    linear_combination 20 * (j1 * j2) * R1 - 10 * (k1 * k2) * R2
  have hne : k1 ^ 2 ≠ k2 ^ 2 := by
    intro h0
    rw [h0, sub_self, mul_zero] at R1
    exact mul_ne_zero hM (mul_ne_zero hk1 hk2) R1.symm
  have hdvd : k1 * k2 ∣ 2 * e :=
    (isCoprime_mul_sq_sub hk).dvd_of_dvd_mul_right ⟨M, by linear_combination R1⟩
  have hle : (k1 * k2) ^ 2 ≤ (2 * e) ^ 2 :=
    Int.natAbs_le_iff_sq_le.mp (Int.natAbs_le_of_dvd_ne_zero hdvd (mul_ne_zero two_ne_zero he))
  obtain ⟨M', e', r', s', hs', hlt⟩ := core hk1 hk2 hj1 hj2 hk hj hne hC
  exact ⟨M', e', r', s', hs', by nlinarith⟩

/-- **The Diophantine lemma**, in the form used by the descent. -/
theorem not_isSol (M e r s : ℤ) : ¬ IsSol M e r s := by
  suffices ∀ n : ℕ, ∀ M e r s : ℤ, e.natAbs = n → ¬ IsSol M e r s from this _ M e r s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M e r s hn h
    obtain ⟨M', e', r', s', h', hlt⟩ := exists_smaller h
    exact ih _ (hn ▸ Int.natAbs_lt_iff_sq_lt.mpr hlt) M' e' r' s' rfl h'

end FiberTwoOne

/-! ### Main results -/

/-- **No two right triangles `(p, 4q)` and `(p, 5q)` with rational hypotenuses.** There are no
integers `p, q ≠ 0` such that `p² + 16 q²` and `p² + 25 q²` are both squares. -/
theorem not_sq_add_sixteen_sq_and_sq_add_twentyfive_sq {p q r s : ℤ} (hp : p ≠ 0)
    (hq : q ≠ 0) (hr : p ^ 2 + 16 * q ^ 2 = r ^ 2) : p ^ 2 + 25 * q ^ 2 ≠ s ^ 2 :=
  fun hs => FiberTwoOne.not_isSol p q r s ⟨hp, hq, hr, hs⟩

/-- The same statement over `ℚ`: for rational `t ≠ 0`, `t² + 16` and `t² + 25` are not both
squares. -/
theorem not_isSquare_sq_add_sixteen_and_sq_add_twentyfive {t : ℚ} (ht : t ≠ 0) :
    ¬ (IsSquare (t ^ 2 + 16) ∧ IsSquare (t ^ 2 + 25)) := by
  rintro ⟨h16, h25⟩
  have hd : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_nz
  have ht' : t = t.num / t.den := (Rat.num_div_den t).symm
  have key : ∀ c : ℤ, IsSquare (t ^ 2 + c) → IsSquare (t.num ^ 2 + c * (t.den : ℤ) ^ 2) := by
    rintro c ⟨a, ha⟩
    rw [← Rat.isSquare_intCast_iff]
    refine ⟨a * t.den, ?_⟩
    push_cast
    rw [← Rat.mul_den_eq_num]
    linear_combination (t.den : ℚ) ^ 2 * ha
  obtain ⟨r, hr⟩ := key 16 (by exact_mod_cast h16)
  obtain ⟨s, hs⟩ := key 25 (by exact_mod_cast h25)
  exact not_sq_add_sixteen_sq_and_sq_add_twentyfive_sq (q := (t.den : ℤ))
    (Rat.num_ne_zero.mpr ht) (by exact_mod_cast t.den_nz) (by rw [hr]; ring) (by rw [hs]; ring)

/-- **No perfect cuboid has two edges in ratio `3 : 4`.** This is the fiber `(m, n) = (2, 1)` of
Peschmann's master-tuple parametrization: with `X = 3k`, `Z = 4k`, the face diagonal
`√(Y² + 16k²)` and the space diagonal `√(Y² + 25k²)` cannot both be integers. -/
theorem not_isPerfectCuboid_three_four {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) :
    3 * Z ≠ 4 * X := by
  intro hXZ
  obtain ⟨k, rfl⟩ : 3 ∣ X := by omega
  obtain rfl : Z = 4 * k := by omega
  obtain ⟨r, hr⟩ := h.sq_bc
  obtain ⟨s, hs⟩ := h.sq_abc
  have hY := h.pos_b
  have hk : 0 < k := by have := h.pos_a; omega
  apply FiberTwoOne.not_isSol (Y : ℤ) k r s
  refine ⟨by exact_mod_cast hY.ne', by exact_mod_cast hk.ne', ?_, ?_⟩
  · have : ((Y ^ 2 + (4 * k) ^ 2 : ℕ) : ℤ) = ((r * r : ℕ) : ℤ) := by rw [hr]
    push_cast at this
    linear_combination this
  · have : (((3 * k) ^ 2 + Y ^ 2 + (4 * k) ^ 2 : ℕ) : ℤ) = ((s * s : ℕ) : ℤ) := by rw [hs]
    push_cast at this
    linear_combination this

end PerfectCuboid
