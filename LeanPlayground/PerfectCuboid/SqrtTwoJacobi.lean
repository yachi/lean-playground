module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The Jacobi lemma for `ℤ[√2]`

Let `ℓ` be a prime that splits in `ℤ[√2]`, `ℓ = π π'` with `π = c₀ + c₁√2` and
`π' = c₀ − c₁√2`, `c₀, c₁ ≥ 0`. Since `π + π' = 2 c₀`, we have `π' ≡ 2 c₀ (mod π)`, and
`ℤ[√2]/(π) = 𝔽_ℓ`, so the quadratic residue symbol `(π'/π)` equals the Legendre symbol
`(2 c₀ / ℓ) = (c₀ / ℓ)` (as `(2/ℓ) = 1` for `ℓ ≡ ±1 (mod 8)`). This file computes that symbol by
quadratic reciprocity:

* `jacobiSym_c0_of_sq_sub_two_sq`: if `ℓ ≡ 7 (mod 8)` then `(c₀/ℓ) = (2/c₀)`, hence
  `(c₀/ℓ) = 1 ↔ ℓ ≡ 15 (mod 16)`.
* `jacobiSym_c0_of_sq_sub_two_sq_one_mod_eight`: if `ℓ ≡ 1 (mod 8)` then `(c₀/ℓ) = (−2/c₀)`.

## Why it matters for perfect cuboids

In the 2-descent over `F = ℚ(√2)` for the quadratic twists `E₁^{(±ℓ)}` (j = 8000) the symbol
`(π'/π)` is the only Selmer input that Hilbert reciprocity does not fix. The first statement says
`(π'/π) = −1` exactly when `ℓ ≡ 7 (mod 16)`, which is the case where the 2-Selmer group is
`δ(E[2])` (theorem T1′ of the round-7/8 reports). Only the elementary symbol computation is
formalized here; the descent itself is not.
-/

@[expose] public section

namespace SqrtTwoJacobi

open ZMod

/-- Residues: `c₀² = ℓ + 2c₁²` with `ℓ ≡ 7 (mod 8)` forces `c₀, c₁` odd, and
`ℓ ≡ 15 (mod 16) ↔ c₀ ≡ ±1 (mod 8)`. -/
theorem residues_seven {ℓ c₀ c₁ : ℕ} (h : c₀ ^ 2 = ℓ + 2 * c₁ ^ 2) (h8 : ℓ % 8 = 7) :
    c₀ % 2 = 1 ∧ c₁ % 2 = 1 ∧ (ℓ % 16 = 15 ↔ c₀ % 8 = 1 ∨ c₀ % 8 = 7) := by
  have h16 : c₀ ^ 2 % 16 = (ℓ + 2 * c₁ ^ 2) % 16 := by rw [h]
  rw [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, Nat.pow_mod c₁] at h16
  have hx : c₀ % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hy : c₁ % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hl : ℓ % 16 = 7 ∨ ℓ % 16 = 15 := by omega
  interval_cases hx' : c₀ % 16 <;> interval_cases hy' : c₁ % 16 <;> omega

/-- Residues: `c₀² = ℓ + 2c₁²` with `ℓ` odd forces `c₀` odd. -/
theorem odd_c0 {ℓ c₀ c₁ : ℕ} (h : c₀ ^ 2 = ℓ + 2 * c₁ ^ 2) (h2 : ℓ % 2 = 1) : c₀ % 2 = 1 := by
  have h4 : c₀ ^ 2 % 2 = (ℓ + 2 * c₁ ^ 2) % 2 := by rw [h]
  rw [Nat.pow_mod, Nat.add_mod, Nat.mul_mod] at h4
  have hx : c₀ % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases hx' : c₀ % 2 <;> omega

/-- If `c₀² − 2c₁² = ℓ` is prime then `gcd(c₁, c₀) = 1`. -/
theorem coprime_c1_c0 {ℓ c₀ c₁ : ℕ} (hℓ : ℓ.Prime) (h : c₀ ^ 2 = ℓ + 2 * c₁ ^ 2) :
    Nat.gcd c₁ c₀ = 1 := by
  set g := Nat.gcd c₁ c₀ with hg
  have h0 : g ^ 2 ∣ c₀ ^ 2 := pow_dvd_pow_of_dvd (Nat.gcd_dvd_right _ _) 2
  have h1 : g ^ 2 ∣ 2 * c₁ ^ 2 :=
    Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left _ _) 2) 2
  have hgl : g ^ 2 ∣ ℓ := by
    have : g ^ 2 ∣ ℓ + 2 * c₁ ^ 2 := h ▸ h0
    exact (Nat.dvd_add_left h1).mp this
  have hgl' : g ∣ ℓ := (Dvd.intro_left _ (sq g).symm).trans hgl
  rcases (Nat.dvd_prime hℓ).mp hgl' with h1 | h1
  · exact h1
  · exfalso
    rw [h1] at hgl
    have hpos : 0 < ℓ := hℓ.pos
    have := Nat.le_of_dvd hpos hgl
    have h2 := hℓ.two_le
    nlinarith

/-- **Key step.** If `ℓ = c₀² − 2c₁²` is prime, then `(ℓ / c₀) = (−2 / c₀)`. -/
theorem jacobiSym_l_c0 {ℓ c₀ c₁ : ℕ} (hℓ : ℓ.Prime) (h : (c₀ : ℤ) ^ 2 - 2 * (c₁ : ℤ) ^ 2 = ℓ) :
    jacobiSym (ℓ : ℤ) c₀ = jacobiSym (-2) c₀ := by
  have hN : c₀ ^ 2 = ℓ + 2 * c₁ ^ 2 := by
    have : ((c₀ ^ 2 : ℕ) : ℤ) = ((ℓ + 2 * c₁ ^ 2 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  have hmod : (ℓ : ℤ) % (c₀ : ℤ) = (-2 * (c₁ : ℤ) ^ 2) % (c₀ : ℤ) := by
    have : (ℓ : ℤ) = -2 * (c₁ : ℤ) ^ 2 + (c₀ : ℤ) * c₀ := by linear_combination -h
    rw [this, Int.add_mul_emod_self_left]
  have hcop : Int.gcd (c₁ : ℤ) (c₀ : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact coprime_c1_c0 hℓ hN
  rw [jacobiSym.mod_left' hmod, jacobiSym.mul_left, jacobiSym.sq_one' hcop, mul_one]

/-- **Jacobi lemma for `ℤ[√2]`.** If `ℓ ≡ 7 (mod 8)` is prime and `ℓ = c₀² − 2c₁²`, then
`(c₀ / ℓ) = (2 / c₀)`; hence `(c₀ / ℓ) = 1 ↔ ℓ ≡ 15 (mod 16)`. -/
theorem jacobiSym_c0_of_sq_sub_two_sq {ℓ : ℕ} (hℓ : ℓ.Prime) (h8 : ℓ % 8 = 7) {c₀ c₁ : ℕ}
    (h : (c₀ : ℤ) ^ 2 - 2 * (c₁ : ℤ) ^ 2 = ℓ) :
    jacobiSym (c₀ : ℤ) ℓ = jacobiSym 2 c₀ ∧ (jacobiSym (c₀ : ℤ) ℓ = 1 ↔ ℓ % 16 = 15) := by
  have hN : c₀ ^ 2 = ℓ + 2 * c₁ ^ 2 := by
    have : ((c₀ ^ 2 : ℕ) : ℤ) = ((ℓ + 2 * c₁ ^ 2 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨hc0, -, h16⟩ := residues_seven hN h8
  have hc0o : Odd c₀ := Nat.odd_iff.mpr hc0
  have hl2 : ℓ % 2 = 1 := by omega
  have hkey := jacobiSym_l_c0 hℓ h
  -- quadratic reciprocity, `ℓ ≡ 3 (mod 4)`
  have hqr := jacobiSym.quadratic_reciprocity_if hc0 hl2
  rw [jacobiSym.at_neg_two hc0o] at hkey
  rw [jacobiSym.at_two hc0o]
  have hJ : jacobiSym (c₀ : ℤ) ℓ = χ₈ c₀ := by
    rw [← hqr, hkey, ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈'_nat_eq_if_mod_eight]
    have hx : c₀ % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases hx' : c₀ % 8 <;> simp_all <;> omega
  refine ⟨hJ, ?_⟩
  rw [hJ, ZMod.χ₈_nat_eq_if_mod_eight, h16]
  have hx : c₀ % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases hx' : c₀ % 8 <;> simp_all

/-- **Companion for `ℓ ≡ 1 (mod 8)`.** If `ℓ ≡ 1 (mod 8)` is prime and `ℓ = c₀² − 2c₁²`, then
`(c₀ / ℓ) = (−2 / c₀)`, i.e. `(c₀ / ℓ) = 1 ↔ c₀ ≡ 1, 3 (mod 8)`. -/
theorem jacobiSym_c0_of_sq_sub_two_sq_one_mod_eight {ℓ : ℕ} (hℓ : ℓ.Prime) (h8 : ℓ % 8 = 1)
    {c₀ c₁ : ℕ} (h : (c₀ : ℤ) ^ 2 - 2 * (c₁ : ℤ) ^ 2 = ℓ) :
    jacobiSym (c₀ : ℤ) ℓ = jacobiSym (-2) c₀ ∧
      (jacobiSym (c₀ : ℤ) ℓ = 1 ↔ c₀ % 8 = 1 ∨ c₀ % 8 = 3) := by
  have hN : c₀ ^ 2 = ℓ + 2 * c₁ ^ 2 := by
    have : ((c₀ ^ 2 : ℕ) : ℤ) = ((ℓ + 2 * c₁ ^ 2 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  have hc0 := odd_c0 hN (by omega)
  have hc0o : Odd c₀ := Nat.odd_iff.mpr hc0
  have hJ : jacobiSym (c₀ : ℤ) ℓ = jacobiSym (-2) c₀ := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hc0o (by omega), jacobiSym_l_c0 hℓ h]
  refine ⟨hJ, ?_⟩
  rw [hJ, jacobiSym.at_neg_two hc0o, ZMod.χ₈'_nat_eq_if_mod_eight]
  have hx : c₀ % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases hx' : c₀ % 8 <;> simp_all

end SqrtTwoJacobi
