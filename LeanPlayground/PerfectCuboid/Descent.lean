module

public import LeanPlayground.PerfectCuboid.DescentCheck
public import LeanPlayground.PerfectCuboid.FiberTwoOne

/-!
# A generic descent for two right triangles with a common leg

Fix coprime positive integers `p < q` and put `D = q² − p²`. This file proves,
under a finite check that the kernel runs, that there are no integers `M, e ≠ 0` such that both
`M² + p² e²` and `M² + q² e²` are squares. Geometrically: there is no rational `t ≠ 0` with
`t² + p²` and `t² + q²` both squares, i.e. no point of infinite order on the elliptic curve
`y² = x (x + p²)(x + q²)` with `x` a square. The elliptic curve never appears in the Lean code.

For a fiber `(m, n)` of the master-tuple parametrization, with `U = m² − n²`, `V = 2mn` and
`W = m² + n²`, a perfect cuboid with two edges `U k` and `V k` and third edge `M` has
`M² + U²k²`, `M² + V²k²` and `M² + W²k²` all squares. So it gives such `M, e = k` for the pair
`(p, q) = (V, W)` (`p` even, `D = U²`), for the pair `(p, q) = (U, W)` (`p` odd, `D = V²`) and
for the pair `{p, q} = {U, V}` (`D = |V² − U²|`, not a square), and each successful check for any
of the three pairs rules out the edge ratio `U : V`. The case `(p, q) = (4, 5)` is the `3 : 4`
fiber of `LeanPlayground.PerfectCuboid.FiberTwoOne`, done there by hand.

## The descent

This is the descent of `FiberTwoOne` with `4, 5` replaced by `p, q`.

1. (`exists_point`) Write `t = M/e`. Then `t = (p/2)(k − 1/k) = (q/2)(j − 1/j)` with
   `k = k₁/k₂`, `j = j₁/j₂` in lowest terms, so
   `p j₁j₂ (k₁² − k₂²) = q k₁k₂ (j₁² − j₂²)`, and `κ (k₁k₂)² ≤ p² e²` with `κ = 4` for even `p`
   and `κ = 1` for odd `p` (`boundK`).
2. (`exists_lam`) Since `k₁k₂` is coprime to `k₁² − k₂²` there is `λ ∣ pq` with
   `p j₁j₂ = λ k₁k₂` and `λ (k₁² − k₂²) = q (j₁² − j₂²)`. Replacing `k` by `−1/k` makes `λ > 0`.
3. (`exists_split`) With `g = gcd(p, λ)`, `p' = p/g`, `λ' = λ/g`, the four-number lemma writes
   `k₁ = c₁αβ`, `k₂ = c₂γδ`, `j₁ = c₃αγ`, `j₂ = c₄βδ` with `c₁c₂ = p'`, `c₃c₄ = λ'`.
   The numbers `α, β, γ, δ` are pairwise coprime.
4. (`exists_sigma`) The second equation becomes `α² X = δ² Y`, so `X = −σ δ²`, `Y = −σ α²`:
   `q c₃² γ² − λ c₁² β² = σ δ²` and `q c₄² β² − λ c₂² γ² = σ α²`. Multiplying the two
   inequalities that `σ ≤ 0` would give yields `p² ≥ q²`, so `σ > 0`; also `σ ∣ λ'² D`.
5. Each tuple `(λ, c₁, c₂, c₃, c₄, σ)` either gives a smaller solution or is impossible by a
   congruence (`CasesOK`, checked by `fiberCheck` or replayed from a certificate by
   `fiberCheckCert` or `fiberCheckCertD`, see `LeanPlayground.PerfectCuboid.DescentCheck`). The
   half-point `Q` of the solution has `2`-descent image `(qλ, Dλσ, Dqσ)` modulo squares, and a
   tuple can only come from a rational point if this is the image of a torsion point `T`. Then
   `Q − T` is twice a point and gives the new solution. Since `λ, σ > 0` only two torsion
   classes occur, and their formulas are proved once for all tuples:
   * (`lin_step`, family L) `qλ = W²`, `Dλσ = h²`, `Dqσ = H²` (`T = O`): the new solution is
     `M' = u δ`, `e' = v α` with `u c₃ = v c₂ W`, or the same after the symmetry
     `(α, β, γ, δ, c₁, c₂, c₃, c₄) ↦ (δ, γ, β, α, c₂, c₁, c₄, c₃)`, which swaps the two equations.
   * (`quadD_step`, family QD) `c₁c₂ = w_d²`, `c₃c₄ = w_n²`, `σ (q − p) = h²` (`T` of order `4`):
     the new solution is `M' = w_d ((q − p) c₃c₄ βγ + σαδ) / F`,
     `e' = w_n (c₁c₄β² − c₂c₃γ²) / F` for a suitable common divisor `F`, with
     `pq F² e'² = c₁c₂ ((q − p)² (c₃c₄)² β²γ² − σ² α²δ²)`.
   * (`quadK_step`, family QK) the same point written as `M' = (q/F) w_d (j₁ + j₂)`,
     `e' = (w_n/F)(k₁ − k₂)` with `F = gcd(q, w_n)` and the sign of `δ` chosen so that
     `k₁k₂ ≥ 0`. Some fibers need QD and others QK, because the bounds below differ.
   The new `|e'|` is compared with `|e|` through three bounds: `κ (k₁k₂)² ≤ p² e²` and
   `(j₁j₂)² ≤ q² e²` from step 1, and `(αβγδ)² ≤ e²`, because `αβγδ` divides both `k₁k₂ ∣ pe` and
   `j₁j₂ ∣ qe`, and `gcd(p, q) = 1`. Each family gives `X e'² ≤ Y (αβγδ)²` for explicit `X, Y`,
   and the checker (`boundOK`) tests that one of the three bounds then gives `e'² < e²`. For
   family QK there is a second route (`sq_lt_of_large`): `F² e'² ≤ 2 w_n² (k₁² + k₂²)`, which is
   below `F² (αβγδ)²` as soon as `F |γδ| > 2 w_n c₁` and `F |αβ| > 2 w_n c₂`; the remaining
   `(β, γ)` lie in a finite box that the kernel searches (`smallCheck`), using `E₁`, `E₂` and
   `k₁² ≠ k₂²`. So `|e|` always decreases.

   The method can only work when the `2`-Selmer group of the curve is the image of the torsion
   (rank `0` and `Ш[2] = 0`): a tuple from a point of infinite order or from `Ш` is neither a
   torsion image nor ruled out by any congruence.

## Main results

* `not_isSol_of_casesOK` — the descent, given `CasesOK p q D`.
* `not_isSol` — the descent for `D = a²`, given a certificate `Covered p q a`.
* `not_isSolD` — the descent for any `D`, given a certificate `CoveredD p q D`.
* `torsionOKL_sound` — the three torsion families give a smaller solution.
* `not_isSquare_sq_add_sq_and_sq_add_sq`, `not_isSquare_sq_add_sq_and_sq_add_sqD` — the same
  over `ℚ`.
-/

@[expose] public section

namespace PerfectCuboid

namespace Descent

open FiberTwoOne (isCoprime_mul_sq_sub four_numbers exists_rho one_le_sq)

/-- An integer solution of `M² + p² e² = r²`, `M² + q² e² = s²` with `M, e ≠ 0`. -/
def IsSol (p q M e r s : ℤ) : Prop :=
  M ≠ 0 ∧ e ≠ 0 ∧ M ^ 2 + p ^ 2 * e ^ 2 = r ^ 2 ∧ M ^ 2 + q ^ 2 * e ^ 2 = s ^ 2

/-! ### Step 1: from a solution to a point `(k, j)` -/

theorem exists_point {p q M e r s : ℤ} (hp : 0 < p) (hq : 0 < q) (h : IsSol p q M e r s) :
    ∃ k1 k2 j1 j2 : ℤ, k1 ≠ 0 ∧ k2 ≠ 0 ∧ j1 ≠ 0 ∧ j2 ≠ 0 ∧ IsCoprime k1 k2 ∧ IsCoprime j1 j2 ∧
      k1 ^ 2 ≠ k2 ^ 2 ∧ p * (j1 * j2) * (k1 ^ 2 - k2 ^ 2) = q * (k1 * k2) * (j1 ^ 2 - j2 ^ 2) ∧
      (∀ p₀, p = 2 * p₀ → 4 * (k1 * k2) ^ 2 ≤ p ^ 2 * e ^ 2) ∧ (k1 * k2) ^ 2 ≤ p ^ 2 * e ^ 2 ∧
      (j1 * j2) ^ 2 ≤ q ^ 2 * e ^ 2 ∧ k1 * k2 ∣ p * e ∧ j1 * j2 ∣ q * e ∧
      (M ^ 2 ≠ p * q * e ^ 2 → p * (k1 ^ 2 - k2 ^ 2) ^ 2 ≠ 4 * q * (k1 * k2) ^ 2) := by
  obtain ⟨hM, he, hr, hs⟩ := h
  have he2 : 0 < e ^ 2 := by positivity
  have hrM : r + M ≠ 0 := fun h0 => by
    rw [show r = -M by linarith] at hr
    have : 0 < p ^ 2 * e ^ 2 := by positivity
    linarith
  have hsM : s + M ≠ 0 := fun h0 => by
    rw [show s = -M by linarith] at hs
    have : 0 < q ^ 2 * e ^ 2 := by positivity
    linarith
  obtain ⟨g, k1, k2, hg, hkg, hk1g, hk2g⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left (p * e) hrM)
  obtain ⟨g', j1, j2, hg', hjg, hj1g, hj2g⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left (q * e) hsM)
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hg0' : (g' : ℤ) ≠ 0 := by exact_mod_cast hg'.ne'
  have hk : IsCoprime k1 k2 := Int.isCoprime_iff_gcd_eq_one.mpr hkg
  have hj : IsCoprime j1 j2 := Int.isCoprime_iff_gcd_eq_one.mpr hjg
  have hk1 : k1 ≠ 0 := by rintro rfl; exact hrM (by rw [hk1g]; ring)
  have hk2 : k2 ≠ 0 := by
    rintro rfl
    have : p * e = 0 := by rw [hk2g]; ring
    rcases mul_eq_zero.mp this with h0 | h0
    · omega
    · exact he h0
  have hj1 : j1 ≠ 0 := by rintro rfl; exact hsM (by rw [hj1g]; ring)
  have hj2 : j2 ≠ 0 := by
    rintro rfl
    have : q * e = 0 := by rw [hj2g]; ring
    rcases mul_eq_zero.mp this with h0 | h0
    · omega
    · exact he h0
  have hk3 : k1 * (r - M) = k2 ^ 2 * g := by
    refine mul_left_cancel₀ hg0 ?_
    linear_combination -(r - M) * hk1g - hr + (p * e + k2 * g) * hk2g
  have hj3 : j1 * (s - M) = j2 ^ 2 * g' := by
    refine mul_left_cancel₀ hg0' ?_
    linear_combination -(s - M) * hj1g - hs + (q * e + j2 * g') * hj2g
  have R1 : p * e * (k1 ^ 2 - k2 ^ 2) = 2 * M * (k1 * k2) := by
    refine mul_left_cancel₀ (mul_ne_zero two_ne_zero hg0) ?_
    linear_combination 2 * g * (k1 ^ 2 - k2 ^ 2) * hk2g - 2 * g * k1 * k2 * hk1g
      + 2 * g * k2 * hk3
  have R2 : q * e * (j1 ^ 2 - j2 ^ 2) = 2 * M * (j1 * j2) := by
    refine mul_left_cancel₀ (mul_ne_zero two_ne_zero hg0') ?_
    linear_combination 2 * g' * (j1 ^ 2 - j2 ^ 2) * hj2g - 2 * g' * j1 * j2 * hj1g
      + 2 * g' * j2 * hj3
  have hC : p * (j1 * j2) * (k1 ^ 2 - k2 ^ 2) = q * (k1 * k2) * (j1 ^ 2 - j2 ^ 2) := by
    refine mul_left_cancel₀ he ?_
    linear_combination (j1 * j2) * R1 - (k1 * k2) * R2
  have hne : k1 ^ 2 ≠ k2 ^ 2 := by
    intro h0
    rw [h0, sub_self, mul_zero] at R1
    exact mul_ne_zero (mul_ne_zero two_ne_zero hM) (mul_ne_zero hk1 hk2) R1.symm
  have hdvd : k1 * k2 ∣ p * e :=
    (isCoprime_mul_sq_sub hk).dvd_of_dvd_mul_right ⟨2 * M, by linear_combination R1⟩
  have hle : (k1 * k2) ^ 2 ≤ (p * e) ^ 2 :=
    Int.natAbs_le_iff_sq_le.mp (Int.natAbs_le_of_dvd_ne_zero hdvd (mul_ne_zero hp.ne' he))
  have hdvd' : j1 * j2 ∣ q * e :=
    (isCoprime_mul_sq_sub hj).dvd_of_dvd_mul_right ⟨2 * M, by linear_combination R2⟩
  have hle' : (j1 * j2) ^ 2 ≤ (q * e) ^ 2 :=
    Int.natAbs_le_iff_sq_le.mp (Int.natAbs_le_of_dvd_ne_zero hdvd' (mul_ne_zero hq.ne' he))
  refine ⟨k1, k2, j1, j2, hk1, hk2, hj1, hj2, hk, hj, hne, hC, ?_, by linear_combination hle,
    by linear_combination hle', hdvd, hdvd', fun hT h0 ↦ hT ?_⟩
  swap
  · -- `M² = pq e²` exactly when `p (k₁² − k₂²)² = 4q (k₁k₂)²`, by `R1`
    refine mul_left_cancel₀ (mul_ne_zero four_ne_zero (pow_ne_zero 2 (mul_ne_zero hk1 hk2))) ?_
    linear_combination (-(p * e * (k1 ^ 2 - k2 ^ 2) + 2 * M * (k1 * k2))) * R1 + p * e ^ 2 * h0
  -- for even `p = 2 p₀`, even `k₁k₂ ∣ p₀ e`
  rintro p₀ rfl
  have hp₀ : p₀ ≠ 0 := by rintro rfl; simp at hp
  have R1₀ : p₀ * e * (k1 ^ 2 - k2 ^ 2) = M * (k1 * k2) :=
    mul_left_cancel₀ (two_ne_zero (α := ℤ)) (by linear_combination R1)
  have hdvd₀ : k1 * k2 ∣ p₀ * e :=
    (isCoprime_mul_sq_sub hk).dvd_of_dvd_mul_right ⟨M, by linear_combination R1₀⟩
  have hle₀ : (k1 * k2) ^ 2 ≤ (p₀ * e) ^ 2 :=
    Int.natAbs_le_iff_sq_le.mp (Int.natAbs_le_of_dvd_ne_zero hdvd₀ (mul_ne_zero hp₀ he))
  linear_combination 4 * hle₀

/-! ### Step 2: the number `λ` -/

theorem exists_lam {p q k1 k2 j1 j2 : ℤ} (hpq : 0 < p * q) (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0)
    (hj1 : j1 ≠ 0) (hj2 : j2 ≠ 0) (hk : IsCoprime k1 k2) (hj : IsCoprime j1 j2)
    (hne : k1 ^ 2 ≠ k2 ^ 2)
    (hC : p * (j1 * j2) * (k1 ^ 2 - k2 ^ 2) = q * (k1 * k2) * (j1 ^ 2 - j2 ^ 2)) :
    ∃ (L : ℕ) (k1' k2' : ℤ), 0 < L ∧ (L : ℤ) ∣ p * q ∧ k1' ≠ 0 ∧ k2' ≠ 0 ∧
      IsCoprime k1' k2' ∧ k1' ^ 2 ≠ k2' ^ 2 ∧ (k1' * k2') ^ 2 = (k1 * k2) ^ 2 ∧
      (k1' ^ 2 - k2' ^ 2) ^ 2 = (k1 ^ 2 - k2 ^ 2) ^ 2 ∧
      p * (j1 * j2) = L * (k1' * k2') ∧ (L : ℤ) * (k1' ^ 2 - k2' ^ 2) = q * (j1 ^ 2 - j2 ^ 2) := by
  have hA : k1 * k2 ≠ 0 := mul_ne_zero hk1 hk2
  have hJ : j1 * j2 ≠ 0 := mul_ne_zero hj1 hj2
  obtain ⟨l, hl⟩ : k1 * k2 ∣ p * (j1 * j2) := (isCoprime_mul_sq_sub hk).dvd_of_dvd_mul_right
    ⟨q * (j1 ^ 2 - j2 ^ 2), by linear_combination hC⟩
  obtain ⟨μ, hμ⟩ : j1 * j2 ∣ q * (k1 * k2) := (isCoprime_mul_sq_sub hj).dvd_of_dvd_mul_right
    ⟨p * (k1 ^ 2 - k2 ^ 2), by linear_combination -hC⟩
  have hlμ : l * μ = p * q := by
    refine mul_left_cancel₀ (mul_ne_zero hA hJ) ?_
    linear_combination -(j1 * j2 * μ) * hl - p * (j1 * j2) * hμ
  have h5 : l * (k1 ^ 2 - k2 ^ 2) = q * (j1 ^ 2 - j2 ^ 2) := by
    refine mul_left_cancel₀ hA ?_
    linear_combination hC - (k1 ^ 2 - k2 ^ 2) * hl
  have h4 : p * (j1 * j2) = l * (k1 * k2) := by rw [hl]; ring
  rcases lt_or_gt_of_ne (show l ≠ 0 by rintro rfl; rw [zero_mul] at hlμ; linarith) with hneg | hpos
  · refine ⟨(-l).toNat, -k2, k1, by omega, ⟨-μ, ?_⟩, neg_ne_zero.mpr hk2, hk1, hk.symm.neg_left,
      by rw [neg_sq]; exact Ne.symm hne, by ring, by ring, ?_, ?_⟩
    · rw [Int.toNat_of_nonneg (by omega)]; linear_combination -hlμ
    · rw [Int.toNat_of_nonneg (by omega)]; linear_combination h4
    · rw [Int.toNat_of_nonneg (by omega)]; linear_combination h5
  · refine ⟨l.toNat, k1, k2, by omega, ⟨μ, ?_⟩, hk1, hk2, hk, hne, rfl, rfl, ?_, ?_⟩
    · rw [Int.toNat_of_nonneg hpos.le]; exact hlμ.symm
    · rw [Int.toNat_of_nonneg hpos.le]; exact h4
    · rw [Int.toNat_of_nonneg hpos.le]; exact h5

/-! ### Step 3: the splitting `k₁ = c₁αβ`, `k₂ = c₂γδ`, `j₁ = c₃αγ`, `j₂ = c₄βδ` -/

/-- If `P ∣ k₁k₂` with `k₁, k₂` coprime, then `P = gcd(P, k₁) gcd(P, k₂)`. -/
theorem gcd_mul_gcd {P : ℕ} {k1 k2 : ℤ} (hk : IsCoprime k1 k2) (h : (P : ℤ) ∣ k1 * k2) :
    Nat.gcd P k1.natAbs * Nat.gcd P k2.natAbs = P := by
  have hc : Nat.Coprime k1.natAbs k2.natAbs := Int.isCoprime_iff_gcd_eq_one.mp hk
  rw [← hc.gcd_mul P, ← Int.natAbs_mul]
  exact Nat.gcd_eq_left (Int.natCast_dvd.mp h)

theorem exists_split {P L : ℕ} (hP : 0 < P) (hL : 0 < L) (hPL : Nat.Coprime P L)
    {k1 k2 j1 j2 : ℤ} (hk1 : k1 ≠ 0) (hk : IsCoprime k1 k2) (hj : IsCoprime j1 j2)
    (h : (L : ℤ) * (k1 * k2) = P * (j1 * j2)) :
    ∃ (c1 c2 c3 c4 : ℕ) (α β γ δ : ℤ), c1 * c2 = P ∧ c3 * c4 = L ∧ k1 = c1 * (α * β) ∧
      k2 = c2 * (γ * δ) ∧ j1 = c3 * (α * γ) ∧ j2 = c4 * (β * δ) := by
  have hPL' : IsCoprime (P : ℤ) L := Nat.isCoprime_iff_coprime.mpr hPL
  have hPk : (P : ℤ) ∣ k1 * k2 := hPL'.dvd_of_dvd_mul_left ⟨j1 * j2, by linear_combination h⟩
  have hLj : (L : ℤ) ∣ j1 * j2 :=
    hPL'.symm.dvd_of_dvd_mul_left ⟨k1 * k2, by linear_combination -h⟩
  have h12 := gcd_mul_gcd hk hPk
  have h34 := gcd_mul_gcd hj hLj
  obtain ⟨x1, hx1⟩ : ((Nat.gcd P k1.natAbs : ℕ) : ℤ) ∣ k1 :=
    Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  obtain ⟨x2, hx2⟩ : ((Nat.gcd P k2.natAbs : ℕ) : ℤ) ∣ k2 :=
    Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  obtain ⟨y1, hy1⟩ : ((Nat.gcd L j1.natAbs : ℕ) : ℤ) ∣ j1 :=
    Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  obtain ⟨y2, hy2⟩ : ((Nat.gcd L j2.natAbs : ℕ) : ℤ) ∣ j2 :=
    Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  have hx1' : x1 ≠ 0 := by rintro rfl; exact hk1 (by rw [hx1, mul_zero])
  have hxy : x1 * x2 = y1 * y2 := by
    have hPL0 : ((L : ℤ) * P) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hL.ne') (by exact_mod_cast hP.ne')
    refine mul_left_cancel₀ hPL0 ?_
    have e12 : ((Nat.gcd P k1.natAbs : ℕ) : ℤ) * (Nat.gcd P k2.natAbs : ℕ) = P := by
      exact_mod_cast h12
    have e34 : ((Nat.gcd L j1.natAbs : ℕ) : ℤ) * (Nat.gcd L j2.natAbs : ℕ) = L := by
      exact_mod_cast h34
    rw [hx1, hx2, hy1, hy2] at h
    linear_combination h - L * x1 * x2 * e12 + P * y1 * y2 * e34
  obtain ⟨α, β, γ, δ, rfl, rfl, rfl, rfl⟩ := four_numbers hxy hx1'
  exact ⟨_, _, _, _, α, β, γ, δ, h12, h34, hx1, hx2, hy1, hy2⟩

/-! ### Step 4: the number `σ` -/

/-- If `ρ ∣ x β²` and `ρ ∣ x γ²` with `β, γ` coprime, then `ρ ∣ x`. -/
theorem dvd_of_dvd_sq {ρ x β γ : ℤ} (hc : IsCoprime β γ) (h1 : ρ ∣ x * β ^ 2)
    (h2 : ρ ∣ x * γ ^ 2) : ρ ∣ x := by
  obtain ⟨u, v, huv⟩ := hc.pow (m := 2) (n := 2)
  have : x = u * (x * β ^ 2) + v * (x * γ ^ 2) := by linear_combination -x * huv
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)

theorem exists_sigma {p q D L c1 c2 c3 c4 α β γ δ : ℤ} (hp : 0 < p) (hpq : p < q) (hL : 0 < L)
    (ha : q ^ 2 - p ^ 2 = D) (hrel : L * (c1 * c2) = p * (c3 * c4)) (hc3 : c3 ≠ 0)
    (hc4 : c4 ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (had : IsCoprime α δ) (hbg : IsCoprime β γ)
    (h5 : L * ((c1 * (α * β)) ^ 2 - (c2 * (γ * δ)) ^ 2) =
      q * ((c3 * (α * γ)) ^ 2 - (c4 * (β * δ)) ^ 2)) :
    ∃ σ : ℤ, 0 < σ ∧ σ ∣ D * (c3 * c4) ^ 2 ∧
      q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2 = σ * δ ^ 2 ∧
      q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2 = σ * α ^ 2 := by
  have h : α ^ 2 * (L * c1 ^ 2 * β ^ 2 - q * c3 ^ 2 * γ ^ 2) =
      δ ^ 2 * (L * c2 ^ 2 * γ ^ 2 - q * c4 ^ 2 * β ^ 2) := by linear_combination h5
  obtain ⟨ρ, hX, hY⟩ := exists_rho had hα h
  have hneg : ρ < 0 := by
    by_contra h0
    rw [not_lt] at h0
    have hX0 : q * c3 ^ 2 * γ ^ 2 ≤ L * c1 ^ 2 * β ^ 2 := by
      have : 0 ≤ ρ * δ ^ 2 := by positivity
      linarith
    have hY0 : q * c4 ^ 2 * β ^ 2 ≤ L * c2 ^ 2 * γ ^ 2 := by
      have : 0 ≤ ρ * α ^ 2 := by positivity
      linarith
    have hm := mul_le_mul hX0 hY0
      (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (sq_nonneg _))
      (mul_nonneg (mul_nonneg hL.le (sq_nonneg _)) (sq_nonneg _))
    have e1 : L * c1 ^ 2 * β ^ 2 * (L * c2 ^ 2 * γ ^ 2) = p ^ 2 * (c3 * c4 * β * γ) ^ 2 := by
      linear_combination (L * c1 * c2 + p * c3 * c4) * β ^ 2 * γ ^ 2 * hrel
    have e2 : q * c3 ^ 2 * γ ^ 2 * (q * c4 ^ 2 * β ^ 2) = q ^ 2 * (c3 * c4 * β * γ) ^ 2 := by ring
    rw [e1, e2] at hm
    have hpos : 0 < (c3 * c4 * β * γ) ^ 2 := by positivity
    have : q ^ 2 ≤ p ^ 2 := le_of_mul_le_mul_right hm hpos
    nlinarith
  refine ⟨-ρ, by linarith, ?_, by linear_combination -hX, by linear_combination -hY⟩
  have d1 : ρ ∣ D * (c3 * c4) ^ 2 * β ^ 2 :=
    ⟨-(L * c2 ^ 2 * δ ^ 2 + q * c3 ^ 2 * α ^ 2), by
      linear_combination (-(c3 * c4) ^ 2 * β ^ 2) * ha - L * c2 ^ 2 * hX - q * c3 ^ 2 * hY
        + (L * c1 * c2 + p * c3 * c4) * β ^ 2 * hrel⟩
  have d2 : ρ ∣ D * (c3 * c4) ^ 2 * γ ^ 2 :=
    ⟨-(q * c4 ^ 2 * δ ^ 2 + L * c1 ^ 2 * α ^ 2), by
      linear_combination (-(c3 * c4) ^ 2 * γ ^ 2) * ha - q * c4 ^ 2 * hX - L * c1 ^ 2 * hY
        + (L * c1 * c2 + p * c3 * c4) * γ ^ 2 * hrel⟩
  exact (dvd_of_dvd_sq hbg d1 d2).neg_left

/-! ### Step 5: the torsion translates

The half-point `Q` with `2Q = P` has `2`-descent image `(qλ, Dλσ, Dqσ)` modulo squares, where
`D = q² − p² = (q − p)(q + p)`. The new solution is `x(Q − T)` for a torsion point `T` with the
same image. Since `λ, σ > 0`, either `T = O` (family L: `qλ` and `Dλσ` squares) or `T` is a point
of order `4` with image `(pq, p (p + q), q (p + q))` (families QD and QK: `pλ` and `σ (q − p)`
squares; the factor `D` cancels against `q + p`). Any other tuple comes from no rational point
and is left to the congruences. -/

/-- **Family L**, the trivial torsion class (`qλ = W²`, `Dλσ = h²`, `Dqσ = H²` with
`D = q² − p²`). With `u c₃ = v c₂ W`, the new solution is `M' = u δ`, `e' = v α`:
`c₃² h² (M'² + p² e'²)` is `c₃² (λ v D c₂ γ)²`, and `c₃² H² (M'² + q² e'²)` is
`c₃² (q v D c₄ β)²`. If `q c₃² ≠ λ c₁² + σ`, then `β² = γ² = δ² = 1` is impossible, so
`(βγδ)² ≥ 4`; this is `m = 4`. -/
theorem lin_step {p q D L c1 c2 c3 c4 σ α β γ δ W h H u v m : ℤ}
    (hrel : L * (c1 * c2) = p * (c3 * c4)) (ha : q ^ 2 - p ^ 2 = D)
    (E1 : q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2 = σ * δ ^ 2)
    (E2 : q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2 = σ * α ^ 2)
    (hW : W ^ 2 = q * L) (hh : h ^ 2 = D * L * σ) (hH : H ^ 2 = D * q * σ)
    (huv : u * c3 = v * (c2 * W)) (hc3 : c3 ≠ 0) (hh0 : h ≠ 0) (hH0 : H ≠ 0) (hu : u ≠ 0)
    (hv : v ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (hm : m = 1 ∨ (m = 4 ∧ q * c3 ^ 2 ≠ L * c1 ^ 2 + σ))
    (hne : (c1 * (α * β)) ^ 2 ≠ (c2 * (γ * δ)) ^ 2) (hp : 0 < p) (hq : 0 < q) (hc4 : c4 ≠ 0) :
    ∃ M e r s, IsSol p q M e r s ∧ M ^ 2 ≠ p * q * e ^ 2 ∧
      m * e ^ 2 ≤ v ^ 2 * (α * β * (γ * δ)) ^ 2 := by
  have K1 : c3 ^ 2 * (h ^ 2 * ((u * δ) ^ 2 + p ^ 2 * (v * α) ^ 2)) =
      c3 ^ 2 * (L * v * D * c2 * γ) ^ 2 := by
    linear_combination (c3 ^ 2 * ((u * δ) ^ 2 + p ^ 2 * (v * α) ^ 2)) * hh +
      D * ((-L ^ 2 * c2 ^ 2 * q * v ^ 2) * E1 + (-L * c3 ^ 2 * p ^ 2 * v ^ 2) * E2 +
      (L * σ * δ ^ 2 * (W * c2 * v + c3 * u)) * huv + (c2 ^ 2 * (L * σ) * v ^ 2 * δ ^ 2) * hW +
      (L ^ 2 * c2 ^ 2 * c3 ^ 2 * v ^ 2 * γ ^ 2) * ha +
      (-L * q * v ^ 2 * β ^ 2 * (L * c1 * c2 + c3 * c4 * p)) * hrel)
  have K2 : c3 ^ 2 * (H ^ 2 * ((u * δ) ^ 2 + q ^ 2 * (v * α) ^ 2)) =
      c3 ^ 2 * (q * v * D * c4 * β) ^ 2 := by
    linear_combination (c3 ^ 2 * ((u * δ) ^ 2 + q ^ 2 * (v * α) ^ 2)) * hH +
      D * ((-L * c2 ^ 2 * q ^ 2 * v ^ 2) * E1 + (-c3 ^ 2 * q ^ 3 * v ^ 2) * E2 +
      (q * σ * δ ^ 2 * (W * c2 * v + c3 * u)) * huv + (q * σ * c2 ^ 2 * v ^ 2 * δ ^ 2) * hW +
      (c3 ^ 2 * c4 ^ 2 * q ^ 2 * v ^ 2 * β ^ 2) * ha +
      (-q ^ 2 * v ^ 2 * β ^ 2 * (L * c1 * c2 + c3 * c4 * p)) * hrel)
  have K1' := mul_left_cancel₀ (pow_ne_zero 2 hc3) K1
  have K2' := mul_left_cancel₀ (pow_ne_zero 2 hc3) K2
  obtain ⟨r, hr⟩ : h ∣ L * v * D * c2 * γ := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨_, K1'.symm⟩
  obtain ⟨s, hs⟩ : H ∣ q * v * D * c4 * β := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨_, K2'.symm⟩
  refine ⟨u * δ, v * α, r, s, ⟨mul_ne_zero hu hδ, mul_ne_zero hv hα, ?_, ?_⟩, ?_, ?_⟩
  · exact mul_left_cancel₀ (pow_ne_zero 2 hh0) (by rw [K1', hr]; ring)
  · exact mul_left_cancel₀ (pow_ne_zero 2 hH0) (by rw [K2', hs]; ring)
  · -- `M'² = pq e'²` would give `c₂c₄δ² = c₁c₃α²`, then `c₂c₃γ² = c₁c₄β²`, so `k₁² = k₂²`
    intro h0
    have s1 : v ^ 2 * q * (c2 ^ 2 * L * δ ^ 2 - p * c3 ^ 2 * α ^ 2) = 0 := by
      linear_combination (-(v ^ 2 * c2 ^ 2 * δ ^ 2)) * hW - δ ^ 2 * (v * c2 * W + u * c3) * huv +
        c3 ^ 2 * h0
    have s2 : c2 ^ 2 * L * δ ^ 2 - p * c3 ^ 2 * α ^ 2 = 0 :=
      (mul_eq_zero.mp s1).resolve_left (mul_ne_zero (pow_ne_zero 2 hv) hq.ne')
    have s3 : p * c3 * (c2 * c4 * δ ^ 2 - c1 * c3 * α ^ 2) = 0 := by
      linear_combination (-(c2 * δ ^ 2)) * hrel + c1 * s2
    have s4 := (mul_eq_zero.mp s3).resolve_left (mul_ne_zero hp.ne' hc3)
    have s5 : c3 * c4 * (p + q) * (c2 * c3 * γ ^ 2 - c1 * c4 * β ^ 2) = 0 := by
      linear_combination c2 * c4 * E1 - c1 * c3 * E2 + σ * s4 -
        (c2 * c3 * γ ^ 2 - c1 * c4 * β ^ 2) * hrel
    have s6 := (mul_eq_zero.mp s5).resolve_left
      (mul_ne_zero (mul_ne_zero hc3 hc4) (by positivity))
    have s7 : c3 * c4 * ((c1 * (α * β)) ^ 2 - (c2 * (γ * δ)) ^ 2) = 0 := by
      linear_combination (-(c1 * c4 * β ^ 2)) * s4 - c2 * c4 * δ ^ 2 * s6
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp s7).resolve_left (mul_ne_zero hc3 hc4)))
  · have e4 : v ^ 2 * (α * β * (γ * δ)) ^ 2 = (v * α) ^ 2 * (β * γ * δ) ^ 2 := by ring
    rw [e4]
    have h1 : m ≤ (β * γ * δ) ^ 2 := by
      have hb := one_le_sq hβ
      have hg := one_le_sq hγ
      have hd := one_le_sq hδ
      rcases hm with rfl | ⟨rfl, hnd⟩
      · exact one_le_sq (mul_ne_zero (mul_ne_zero hβ hγ) hδ)
      · by_contra hlt
        have hx : β * γ * δ = 1 ∨ β * γ * δ = -1 := by
          have h0 : β * γ * δ ≠ 0 := mul_ne_zero (mul_ne_zero hβ hγ) hδ
          have : -2 < β * γ * δ ∧ β * γ * δ < 2 := by constructor <;> nlinarith
          omega
        have hx1 : (β * γ * δ) ^ 2 = 1 := by rcases hx with hx | hx <;> rw [hx] <;> norm_num
        have hgd : 1 ≤ γ ^ 2 * δ ^ 2 := one_le_mul_of_one_le_of_one_le hg hd
        have hbd : 1 ≤ β ^ 2 * δ ^ 2 := one_le_mul_of_one_le_of_one_le hb hd
        have hbg : 1 ≤ β ^ 2 * γ ^ 2 := one_le_mul_of_one_le_of_one_le hb hg
        have hb1 : β ^ 2 = 1 := by
          have := mul_le_mul_of_nonneg_left hgd (sq_nonneg β)
          linarith [show β ^ 2 * (γ ^ 2 * δ ^ 2) = 1 by linear_combination hx1]
        have hg1 : γ ^ 2 = 1 := by
          have := mul_le_mul_of_nonneg_left hbd (sq_nonneg γ)
          linarith [show γ ^ 2 * (β ^ 2 * δ ^ 2) = 1 by linear_combination hx1]
        have hd1 : δ ^ 2 = 1 := by
          have := mul_le_mul_of_nonneg_left hbg (sq_nonneg δ)
          linarith [show δ ^ 2 * (β ^ 2 * γ ^ 2) = 1 by linear_combination hx1]
        exact hnd (by linear_combination E1 - q * c3 ^ 2 * hg1 + L * c1 ^ 2 * hb1 + σ * hd1)
    calc m * (v * α) ^ 2 = (v * α) ^ 2 * m := by ring
      _ ≤ (v * α) ^ 2 * (β * γ * δ) ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

/-- If `F₁² (M² + p² e²)` and `F₂² (M² + q² e²)` are squares, then so are `M² + p² e²` and
`M² + q² e²`. -/
theorem exists_isSol {p q F1 F2 M e r0 s0 : ℤ} (hF1 : F1 ≠ 0) (hF2 : F2 ≠ 0) (hM : M ≠ 0)
    (he : e ≠ 0) (G1 : F1 ^ 2 * (M ^ 2 + p ^ 2 * e ^ 2) = r0 ^ 2)
    (G2 : F2 ^ 2 * (M ^ 2 + q ^ 2 * e ^ 2) = s0 ^ 2) : ∃ r s, IsSol p q M e r s := by
  obtain ⟨r, hr⟩ : F1 ∣ r0 := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨_, G1.symm⟩
  obtain ⟨s, hs⟩ : F2 ∣ s0 := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨_, G2.symm⟩
  refine ⟨r, s, hM, he, mul_left_cancel₀ (pow_ne_zero 2 hF1) ?_,
    mul_left_cancel₀ (pow_ne_zero 2 hF2) ?_⟩
  · rw [G1, hr]; ring
  · rw [G2, hs]; ring

/-- The point of family QD is not `±T₄`: `X² ≠ pq Y²` for `X = w_d ((q − p) c₃c₄ βγ + σαδ)` and
`Y = w_n (c₁c₄β² − c₂c₃γ²)`, since `pq Y² = X (X − 2 w_d σαδ)`. -/
theorem qd_ne {p q L c1 c2 c3 c4 σ α β γ δ wn wd : ℤ}
    (hrel : L * (c1 * c2) = p * (c3 * c4))
    (E1 : q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2 = σ * δ ^ 2)
    (E2 : q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2 = σ * α ^ 2)
    (hne : (c1 * (α * β)) ^ 2 ≠ (c2 * (γ * δ)) ^ 2)
    (hwn : wn ^ 2 = c3 * c4) (hwd : wd ^ 2 = c1 * c2)
    (hp : 0 < p) (hq : 0 < q) (hσ : 0 < σ) (hwn0 : wn ≠ 0) (hwd0 : wd ≠ 0) (hα : α ≠ 0)
    (hδ : δ ≠ 0) :
    (wd * ((q - p) * (c3 * c4) * β * γ + σ * α * δ)) ^ 2 ≠
      p * q * (wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) ^ 2 := by
  have hO : wn ^ 2 * p = wd ^ 2 * L := by linear_combination p * hwn - L * hwd - hrel
  have G3 : p * q * (wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) ^ 2 =
      (wd * ((q - p) * (c3 * c4) * β * γ + σ * α * δ)) *
        (wd * ((q - p) * (c3 * c4) * β * γ - σ * α * δ)) := by
    linear_combination (-wd ^ 2 * α ^ 2 * σ) * E1 +
      (-wd ^ 2 * (-L * c1 ^ 2 * β ^ 2 + c3 ^ 2 * q * γ ^ 2)) * E2 +
      (q * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2) ^ 2) * hO +
      (wd ^ 2 * β ^ 2 * γ ^ 2 * (L * c1 * c2 + c3 * c4 * p - 2 * c3 * c4 * q)) * hrel
  have he0 : wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2) ≠ 0 := by
    intro h0
    have he : c1 * c4 * β ^ 2 = c2 * c3 * γ ^ 2 := by
      linear_combination (mul_eq_zero.mp h0).resolve_left hwn0
    have h1 : σ * ((c1 * (α * β)) ^ 2 - (c2 * (γ * δ)) ^ 2) = 0 := by
      linear_combination (c2 ^ 2 * γ ^ 2) * E1 + (-c1 ^ 2 * β ^ 2) * E2 +
        (q * (c1 * c4 * β ^ 2 + c2 * c3 * γ ^ 2)) * he
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hσ.ne'))
  intro h0
  have h1 : wd * ((q - p) * (c3 * c4) * β * γ + σ * α * δ) * (2 * wd * σ * α * δ) = 0 := by
    linear_combination h0 + G3
  rcases mul_eq_zero.mp h1 with h2 | h2
  · rw [h2, zero_mul] at G3
    have : 0 < p * q * (wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) ^ 2 := by positivity
    linarith
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hwd0) hσ.ne') hα) hδ h2

/-- **Family QD**, the class of a `4`-torsion point (`c₁c₂ = w_d²`, `c₃c₄ = w_n²`,
`σ (q − p) = h²`). The new solution is `M' = w_d ((q − p) c₃c₄ βγ + σαδ) / F` and
`e' = w_n (c₁c₄β² − c₂c₃γ²) / F`, with `pq F² e'² = c₁c₂ ((q − p)² (c₃c₄)² β²γ² − σ² α²δ²)`.
The divisor `F` divides `M'` through its coefficients, and `e'` because
`λ c₁ w_n (c₁c₄β² − c₂c₃γ²) = w_n c₄ ((q − p) c₃² γ² − σ δ²)`. For `λ = p`, `cᵢ = 1` and
`F = q − p` this is `M' = βγ + s²αδ`, `e' = (β² − γ²)/(q − p)` when `σ = (q − p) s²`. -/
theorem quadD_step {p q L c1 c2 c3 c4 σ α β γ δ wn wd h F : ℤ}
    (hrel : L * (c1 * c2) = p * (c3 * c4))
    (E1 : q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2 = σ * δ ^ 2)
    (E2 : q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2 = σ * α ^ 2)
    (hne : (c1 * (α * β)) ^ 2 ≠ (c2 * (γ * δ)) ^ 2)
    (hwn : wn ^ 2 = c3 * c4) (hwd : wd ^ 2 = c1 * c2) (hh : σ * (q - p) = h ^ 2)
    (hp : 0 < p) (hq : 0 < q) (hσ : 0 < σ) (hwn0 : wn ≠ 0) (hwd0 : wd ≠ 0) (hα : α ≠ 0)
    (hδ : δ ≠ 0) (hF : 0 < F) (hFM1 : F ∣ wd * (q - p) * (c3 * c4)) (hFM2 : F ∣ wd * σ)
    (hFe1 : F ∣ wn * c4 * c3 ^ 2 * (q - p)) (hFe2 : F ∣ wn * c4 * σ)
    (hFc : IsCoprime F (L * c1)) :
    ∃ M e r s, IsSol p q M e r s ∧ M ^ 2 ≠ p * q * e ^ 2 ∧
      p * q * F ^ 2 * e ^ 2 < c1 * c2 * (q - p) ^ 2 * (c3 * c4) ^ 2 * (α * β * (γ * δ)) ^ 2 := by
  have hX := qd_ne hrel E1 E2 hne hwn hwd hp hq hσ hwn0 hwd0 hα hδ
  have hO : wn ^ 2 * p = wd ^ 2 * L := by linear_combination p * hwn - L * hwd - hrel
  have hw : wn ^ 2 * (c1 * c2) = wd ^ 2 * (c3 * c4) := by
    linear_combination (c1 * c2) * hwn - (c3 * c4) * hwd
  have G1 : (wd * ((q - p) * (c3 * c4) * β * γ + σ * α * δ)) ^ 2 +
      p ^ 2 * (wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) ^ 2 =
      (wd * h * (c3 * α * γ + c4 * β * δ)) ^ 2 := by
    linear_combination (-wd ^ 2 * (c4 ^ 2 * p * β ^ 2 - c4 ^ 2 * q * β ^ 2 + α ^ 2 * σ)) * E1 +
      (-wd ^ 2 * (-L * c1 ^ 2 * β ^ 2 + c3 ^ 2 * p * γ ^ 2)) * E2 +
      (p * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2) ^ 2) * hO +
      (wd ^ 2 * (c3 * α * γ + c4 * β * δ) ^ 2) * hh +
      (-wd ^ 2 * β ^ 2 * γ ^ 2 * (-L * c1 * c2 + c3 * c4 * p)) * hrel
  have G2 : (wd * ((q - p) * (c3 * c4) * β * γ + σ * α * δ)) ^ 2 +
      q ^ 2 * (wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) ^ 2 =
      (wn * h * (c1 * α * β + c2 * γ * δ)) ^ 2 := by
    linear_combination (-c2 ^ 2 * p * wn ^ 2 * γ ^ 2 + c2 ^ 2 * q * wn ^ 2 * γ ^ 2 -
        wd ^ 2 * α ^ 2 * σ) * E1 +
      (L * c1 ^ 2 * wd ^ 2 * β ^ 2 - c1 ^ 2 * p * wn ^ 2 * β ^ 2 + c1 ^ 2 * q * wn ^ 2 * β ^ 2 -
        c3 ^ 2 * q * wd ^ 2 * γ ^ 2) * E2 +
      (-2 * L * c1 ^ 2 * c2 ^ 2 * β ^ 2 * γ ^ 2 + c1 ^ 2 * c4 ^ 2 * q * β ^ 4 +
        c2 ^ 2 * c3 ^ 2 * q * γ ^ 4) * hO +
      (-2 * β * γ * (-L * c1 * c2 * q * β * γ + c3 * c4 * q ^ 2 * β * γ + h ^ 2 * α * δ)) * hw +
      (c1 ^ 2 * wn ^ 2 * α ^ 2 * β ^ 2 + c2 ^ 2 * wn ^ 2 * γ ^ 2 * δ ^ 2 +
        2 * c3 * c4 * wd ^ 2 * α * β * γ * δ) * hh +
      (-wd ^ 2 * β ^ 2 * γ ^ 2 * (L * c1 * c2 + c3 * c4 * p - 2 * c3 * c4 * q)) * hrel
  have G3 : p * q * (wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) ^ 2 =
      (wd * ((q - p) * (c3 * c4) * β * γ + σ * α * δ)) *
        (wd * ((q - p) * (c3 * c4) * β * γ - σ * α * δ)) := by
    linear_combination (-wd ^ 2 * α ^ 2 * σ) * E1 +
      (-wd ^ 2 * (-L * c1 ^ 2 * β ^ 2 + c3 ^ 2 * q * γ ^ 2)) * E2 +
      (q * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2) ^ 2) * hO +
      (wd ^ 2 * β ^ 2 * γ ^ 2 * (L * c1 * c2 + c3 * c4 * p - 2 * c3 * c4 * q)) * hrel
  have G3' : p * q * (wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) ^ 2 =
      c1 * c2 * ((q - p) ^ 2 * (c3 * c4) ^ 2 * (β ^ 2 * γ ^ 2) - σ ^ 2 * (α ^ 2 * δ ^ 2)) := by
    linear_combination G3 +
      ((q - p) ^ 2 * (c3 * c4) ^ 2 * (β ^ 2 * γ ^ 2) - σ ^ 2 * (α ^ 2 * δ ^ 2)) * hwd
  have hediv : L * c1 * (wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) =
      wn * c4 * ((q - p) * c3 ^ 2 * γ ^ 2 - σ * δ ^ 2) := by
    linear_combination (-c4 * wn) * E1 + (-c3 * wn * γ ^ 2) * hrel
  have he0 : wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2) ≠ 0 := by
    intro h0
    have he : c1 * c4 * β ^ 2 = c2 * c3 * γ ^ 2 := by
      linear_combination (mul_eq_zero.mp h0).resolve_left hwn0
    have h1 : σ * ((c1 * (α * β)) ^ 2 - (c2 * (γ * δ)) ^ 2) = 0 := by
      linear_combination (c2 ^ 2 * γ ^ 2) * E1 + (-c1 ^ 2 * β ^ 2) * E2 +
        (q * (c1 * c4 * β ^ 2 + c2 * c3 * γ ^ 2)) * he
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hσ.ne'))
  have hM0 : wd * ((q - p) * (c3 * c4) * β * γ + σ * α * δ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at G3
    have : 0 < p * q * (wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) ^ 2 := by positivity
    linarith
  obtain ⟨M, hM⟩ : F ∣ wd * ((q - p) * (c3 * c4) * β * γ + σ * α * δ) := by
    rw [show wd * ((q - p) * (c3 * c4) * β * γ + σ * α * δ) =
      wd * (q - p) * (c3 * c4) * (β * γ) + wd * σ * (α * δ) by ring]
    exact dvd_add (hFM1.mul_right _) (hFM2.mul_right _)
  obtain ⟨e, he⟩ : F ∣ wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2) := by
    refine hFc.dvd_of_dvd_mul_left ?_
    rw [hediv, show wn * c4 * ((q - p) * c3 ^ 2 * γ ^ 2 - σ * δ ^ 2) =
      wn * c4 * c3 ^ 2 * (q - p) * γ ^ 2 - wn * c4 * σ * δ ^ 2 by ring]
    exact dvd_sub (hFe1.mul_right _) (hFe2.mul_right _)
  rw [hM, he] at hX
  rw [hM] at G1 G2 hM0
  rw [he] at G1 G2 G3' he0
  obtain ⟨r, s, hsol⟩ := exists_isSol (p := p) (q := q) (F1 := F) (F2 := F) (M := M) (e := e)
    (r0 := wd * h * (c3 * α * γ + c4 * β * δ)) (s0 := wn * h * (c1 * α * β + c2 * γ * δ))
    hF.ne' hF.ne'
    (right_ne_zero_of_mul hM0) (right_ne_zero_of_mul he0) (by linear_combination G1)
    (by linear_combination G2)
  refine ⟨M, e, r, s, hsol, fun h0 ↦ hX (by linear_combination F ^ 2 * h0), ?_⟩
  have hc : 0 < c1 * c2 := by rw [← hwd]; positivity
  have k1 : 0 < c1 * c2 * (σ ^ 2 * (α ^ 2 * δ ^ 2)) := by positivity
  have k2 : c1 * c2 * ((q - p) ^ 2 * (c3 * c4) ^ 2 * (β ^ 2 * γ ^ 2)) * 1 ≤
      c1 * c2 * ((q - p) ^ 2 * (c3 * c4) ^ 2 * (β ^ 2 * γ ^ 2)) * (α ^ 2 * δ ^ 2) :=
    mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (one_le_sq hα) (one_le_sq hδ))
      (by positivity)
  have e1 : p * q * F ^ 2 * e ^ 2 = p * q * (F * e) ^ 2 := by ring
  have e2 : c1 * c2 * (q - p) ^ 2 * (c3 * c4) ^ 2 * (α * β * (γ * δ)) ^ 2 =
      c1 * c2 * ((q - p) ^ 2 * (c3 * c4) ^ 2 * (β ^ 2 * γ ^ 2)) * (α ^ 2 * δ ^ 2) := by ring
  rw [e1, e2, G3']
  linarith

theorem sub_sq_le_two_mul {x y : ℤ} : (x - y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x + y)]

/-- **Family QK**, the same point as QD written differently. With `q = F q_F` and `w_n = F w_F`,
the new solution is `M' = q_F w_d (j₁ + j₂)`, `e' = w_F (k₁ − k₂)`; both
`(σ w_d F)² (M'² + p² e'²)` and `(σ w_d F)² (M'² + q² e'²)` are squares. If `k₁k₂ ≥ 0`, then
`(k₁ − k₂)² < (k₁k₂)²`. For `λ = pq`, `q = w²` and `F = w` this is `M' = w (j₁ + j₂)`,
`e' = k₁ − k₂`. -/
theorem quadK_core {p q L c1 c2 c3 c4 σ α β γ δ wn wd h F qF wF : ℤ}
    (hrel : L * (c1 * c2) = p * (c3 * c4))
    (E1 : q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2 = σ * δ ^ 2)
    (E2 : q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2 = σ * α ^ 2)
    (hne : (c1 * (α * β)) ^ 2 ≠ (c2 * (γ * δ)) ^ 2)
    (hwn : wn ^ 2 = c3 * c4) (hwd : wd ^ 2 = c1 * c2) (hh : σ * (q - p) = h ^ 2)
    (hL : 0 < L) (hq : 0 < q) (hσ : 0 < σ) (hwn0 : wn ≠ 0) (hwd0 : wd ≠ 0)
    (hqF : q = F * qF) (hwF : wn = F * wF) (hk1 : c1 * (α * β) ≠ 0) (hk2 : c2 * (γ * δ) ≠ 0)
    (hsign : 0 ≤ c1 * (α * β) * (c2 * (γ * δ))) (hp : 0 < p) :
    ∃ M e r s, IsSol p q M e r s ∧ M ^ 2 ≠ p * q * e ^ 2 ∧
      F ^ 2 * e ^ 2 < wn ^ 2 * (c1 * c2) ^ 2 * (α * β * (γ * δ)) ^ 2 ∧
      F ^ 2 * e ^ 2 ≤ 2 * wn ^ 2 * ((c1 * (α * β)) ^ 2 + (c2 * (γ * δ)) ^ 2) := by
  have hO : wn ^ 2 * p = wd ^ 2 * L := by linear_combination p * hwn - L * hwd - hrel
  have hw : wn ^ 2 * (c1 * c2) = wd ^ 2 * (c3 * c4) := by
    linear_combination (c1 * c2) * hwn - (c3 * c4) * hwd
  have G1 : (σ * wd) ^ 2 * ((q * wd * (c3 * (α * γ) + c4 * (β * δ))) ^ 2 +
      p ^ 2 * (wn * (c1 * (α * β) - c2 * (γ * δ))) ^ 2) =
      (h * ((p + q) * c1 * c2 * wn ^ 2 * β * γ + wd ^ 2 * σ * α * δ)) ^ 2 := by
    linear_combination (-wd ^ 2 * σ * (c2 ^ 2 * p ^ 2 * wn ^ 2 * γ ^ 2 +
        c4 ^ 2 * q ^ 2 * wd ^ 2 * β ^ 2 - h ^ 2 * wd ^ 2 * α ^ 2)) * E1 +
      (-wd ^ 2 * (L * c1 ^ 2 * h ^ 2 * wd ^ 2 * β ^ 2 + c1 ^ 2 * p ^ 2 * wn ^ 2 * β ^ 2 * σ -
        c3 ^ 2 * h ^ 2 * q * wd ^ 2 * γ ^ 2 + c3 ^ 2 * q ^ 2 * wd ^ 2 * γ ^ 2 * σ)) * E2 +
      (-L * c1 ^ 2 * c2 ^ 2 * h ^ 2 * wd ^ 2 * β ^ 2 * γ ^ 2 -
        2 * L * c1 ^ 2 * c2 ^ 2 * p * wd ^ 2 * β ^ 2 * γ ^ 2 * σ -
        c1 ^ 2 * c2 ^ 2 * h ^ 2 * p * wn ^ 2 * β ^ 2 * γ ^ 2 -
        2 * c1 ^ 2 * c2 ^ 2 * h ^ 2 * q * wn ^ 2 * β ^ 2 * γ ^ 2 +
        c1 ^ 2 * c4 ^ 2 * p * q * wd ^ 2 * β ^ 4 * σ -
        2 * c1 * c2 * h ^ 2 * wd ^ 2 * α * β * γ * δ * σ -
        2 * c1 * c2 * p * wd ^ 2 * α * β * γ * δ * σ ^ 2 +
        c2 ^ 2 * c3 ^ 2 * p * q * wd ^ 2 * γ ^ 4 * σ) * hO +
      (-h ^ 2 * q * β * γ * (2 * L * c1 * c2 * wd ^ 2 * β * γ + c1 * c2 * q * wn ^ 2 * β * γ +
        c3 * c4 * q * wd ^ 2 * β * γ + 2 * wd ^ 2 * α * δ * σ)) * hw +
      (wd ^ 4 * (2 * L ^ 2 * c1 ^ 2 * c2 ^ 2 * β ^ 2 * γ ^ 2 - L * c1 ^ 2 * c4 ^ 2 * q * β ^ 4 +
        2 * L * c1 * c2 * c3 * c4 * q * β ^ 2 * γ ^ 2 + 2 * L * c1 * c2 * α * β * γ * δ * σ -
        L * c2 ^ 2 * c3 ^ 2 * q * γ ^ 4 + 2 * c3 ^ 2 * c4 ^ 2 * q ^ 2 * β ^ 2 * γ ^ 2 +
        2 * c3 * c4 * q * α * β * γ * δ * σ)) * hh +
      (-2 * q * wd ^ 4 * β * γ * σ * (L * c1 * c2 * β * γ + c3 * c4 * q * β * γ + α * δ * σ)) *
        hrel
  have G2 : (σ * wd) ^ 2 * ((q * wd * (c3 * (α * γ) + c4 * (β * δ))) ^ 2 +
      q ^ 2 * (wn * (c1 * (α * β) - c2 * (γ * δ))) ^ 2) =
      (q * h * wn * wd * (c1 * c4 * β ^ 2 + c2 * c3 * γ ^ 2)) ^ 2 := by
    linear_combination
      (-q ^ 2 * wd ^ 2 * σ * (c2 ^ 2 * wn ^ 2 * γ ^ 2 + c4 ^ 2 * wd ^ 2 * β ^ 2)) * E1 +
      (-q ^ 2 * wd ^ 2 * σ * (c1 ^ 2 * wn ^ 2 * β ^ 2 + c3 ^ 2 * wd ^ 2 * γ ^ 2)) * E2 +
      (q ^ 2 * wd ^ 2 * σ * (c1 ^ 2 * c4 ^ 2 * β ^ 4 + c2 ^ 2 * c3 ^ 2 * γ ^ 4)) * hO +
      (-2 * q ^ 2 * wd ^ 2 * β * γ * (L * c1 * c2 * β * γ * σ + c3 * c4 * h ^ 2 * β * γ +
        α * δ * σ ^ 2)) * hw +
      (q ^ 2 * wd ^ 2 * (c1 ^ 2 * c4 ^ 2 * wn ^ 2 * β ^ 4 + c2 ^ 2 * c3 ^ 2 * wn ^ 2 * γ ^ 4 +
        2 * c3 ^ 2 * c4 ^ 2 * wd ^ 2 * β ^ 2 * γ ^ 2)) * hh +
      (-2 * c3 * c4 * q ^ 2 * wd ^ 4 * β ^ 2 * γ ^ 2 * σ) * hrel
  have h5 : L * ((c1 * (α * β)) ^ 2 - (c2 * (γ * δ)) ^ 2) =
      q * ((c3 * (α * γ)) ^ 2 - (c4 * (β * δ)) ^ 2) := by
    linear_combination (-α ^ 2) * E1 + δ ^ 2 * E2
  have hF : F ≠ 0 := by rintro rfl; rw [zero_mul] at hwF; exact hwn0 hwF
  have hqF0 : qF ≠ 0 := by rintro rfl; rw [mul_zero] at hqF; exact hq.ne' hqF
  have hwF0 : wF ≠ 0 := by rintro rfl; rw [mul_zero] at hwF; exact hwn0 hwF
  have hj : c3 * (α * γ) + c4 * (β * δ) ≠ 0 := by
    intro h0
    have : (c3 * (α * γ)) ^ 2 = (c4 * (β * δ)) ^ 2 := by
      rw [show c3 * (α * γ) = -(c4 * (β * δ)) by linear_combination h0, neg_sq]
    rw [this, sub_self, mul_zero] at h5
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_left hL.ne'))
  have hk : c1 * (α * β) - c2 * (γ * δ) ≠ 0 := by
    intro h0
    exact hne (by rw [show c1 * (α * β) = c2 * (γ * δ) by linear_combination h0])
  obtain ⟨r, s, hsol⟩ := exists_isSol (p := p) (q := q) (F1 := σ * wd * F) (F2 := σ * wd * F)
    (M := qF * wd * (c3 * (α * γ) + c4 * (β * δ))) (e := wF * (c1 * (α * β) - c2 * (γ * δ)))
    (r0 := h * ((p + q) * c1 * c2 * wn ^ 2 * β * γ + wd ^ 2 * σ * α * δ))
    (s0 := q * h * wn * wd * (c1 * c4 * β ^ 2 + c2 * c3 * γ ^ 2))
    (by positivity) (by positivity) (mul_ne_zero (mul_ne_zero hqF0 hwd0) hj)
    (mul_ne_zero hwF0 hk) (by rw [← G1, hqF, hwF]; ring) (by rw [← G2, hqF, hwF]; ring)
  refine ⟨_, _, r, s, hsol, ?_, ?_, ?_⟩
  · -- the point of QK is the point of QD, which is not `±T₄`
    have hα : α ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hk1)
    have hδ : δ ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hk2)
    have hX := qd_ne hrel E1 E2 hne hwn hwd hp hq hσ hwn0 hwd0 hα hδ
    have hid : q * wd * (c3 * (α * γ) + c4 * (β * δ)) * (wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) =
        wd * ((q - p) * (c3 * c4) * β * γ + σ * α * δ) * (wn * (c1 * (α * β) - c2 * (γ * δ))) := by
      linear_combination (c1 * wd * wn * β * δ) * E2 - (c2 * wd * wn * α * γ) * E1 -
        (wd * wn * β * γ * (c1 * α * β - c2 * γ * δ)) * hrel
    intro h0
    have h1 : (q * wd * (c3 * (α * γ) + c4 * (β * δ))) ^ 2 =
        p * q * (wn * (c1 * (α * β) - c2 * (γ * δ))) ^ 2 := by
      linear_combination F ^ 2 * h0 +
        (q + F * qF) * (wd * (c3 * (α * γ) + c4 * (β * δ))) ^ 2 * hqF -
        p * q * (wn + F * wF) * (c1 * (α * β) - c2 * (γ * δ)) ^ 2 * hwF
    have h2 : (wn * (c1 * (α * β) - c2 * (γ * δ))) ^ 2 *
        (p * q * (wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) ^ 2 -
          (wd * ((q - p) * (c3 * c4) * β * γ + σ * α * δ)) ^ 2) = 0 := by
      linear_combination (-(wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) ^ 2) * h1 +
        (q * wd * (c3 * (α * γ) + c4 * (β * δ)) * (wn * (c1 * c4 * β ^ 2 - c2 * c3 * γ ^ 2)) +
          wd * ((q - p) * (c3 * c4) * β * γ + σ * α * δ) *
            (wn * (c1 * (α * β) - c2 * (γ * δ)))) * hid
    exact hX (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left
      (pow_ne_zero 2 (mul_ne_zero hwn0 hk)))).symm
  swap
  · calc F ^ 2 * (wF * (c1 * (α * β) - c2 * (γ * δ))) ^ 2 =
        wn ^ 2 * (c1 * (α * β) - c2 * (γ * δ)) ^ 2 := by rw [hwF]; ring
      _ ≤ wn ^ 2 * (2 * ((c1 * (α * β)) ^ 2 + (c2 * (γ * δ)) ^ 2)) :=
        mul_le_mul_of_nonneg_left sub_sq_le_two_mul (sq_nonneg _)
      _ = 2 * wn ^ 2 * ((c1 * (α * β)) ^ 2 + (c2 * (γ * δ)) ^ 2) := by ring
  have hX := one_le_sq hk1
  have hY := one_le_sq hk2
  have hXY1 : 1 ≤ c1 * (α * β) * (c2 * (γ * δ)) := by
    have : c1 * (α * β) * (c2 * (γ * δ)) ≠ 0 := mul_ne_zero hk1 hk2
    omega
  have hlt : (c1 * (α * β) - c2 * (γ * δ)) ^ 2 < (c1 * (α * β) * (c2 * (γ * δ))) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hw2 : 0 < wn ^ 2 := by positivity
  calc F ^ 2 * (wF * (c1 * (α * β) - c2 * (γ * δ))) ^ 2 =
      wn ^ 2 * (c1 * (α * β) - c2 * (γ * δ)) ^ 2 := by rw [hwF]; ring
    _ < wn ^ 2 * (c1 * (α * β) * (c2 * (γ * δ))) ^ 2 := mul_lt_mul_of_pos_left hlt hw2
    _ = _ := by ring

/-- `quadK_core` with the sign of `δ` chosen. -/
theorem quadK_step {p q L c1 c2 c3 c4 σ α β γ δ wn wd h F qF wF : ℤ}
    (hrel : L * (c1 * c2) = p * (c3 * c4))
    (E1 : q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2 = σ * δ ^ 2)
    (E2 : q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2 = σ * α ^ 2)
    (hne : (c1 * (α * β)) ^ 2 ≠ (c2 * (γ * δ)) ^ 2)
    (hwn : wn ^ 2 = c3 * c4) (hwd : wd ^ 2 = c1 * c2) (hh : σ * (q - p) = h ^ 2)
    (hL : 0 < L) (hq : 0 < q) (hσ : 0 < σ) (hwn0 : wn ≠ 0) (hwd0 : wd ≠ 0)
    (hqF : q = F * qF) (hwF : wn = F * wF) (hk1 : c1 * (α * β) ≠ 0) (hk2 : c2 * (γ * δ) ≠ 0)
    (hp : 0 < p) :
    ∃ M e r s, IsSol p q M e r s ∧ M ^ 2 ≠ p * q * e ^ 2 ∧
      F ^ 2 * e ^ 2 < wn ^ 2 * (c1 * c2) ^ 2 * (α * β * (γ * δ)) ^ 2 ∧
      F ^ 2 * e ^ 2 ≤ 2 * wn ^ 2 * ((c1 * (α * β)) ^ 2 + (c2 * (γ * δ)) ^ 2) := by
  rcases le_total 0 (c1 * (α * β) * (c2 * (γ * δ))) with hs | hs
  · exact quadK_core hrel E1 E2 hne hwn hwd hh hL hq hσ hwn0 hwd0 hqF hwF hk1 hk2 hs hp
  · obtain ⟨M, e, r, s, hsol, hT, hlt, hle⟩ := quadK_core (δ := -δ) hrel (by rwa [neg_sq]) E2
      (by rwa [mul_neg, mul_neg, neg_sq]) hwn hwd hh hL hq hσ hwn0 hwd0 hqF hwF hk1
      (by rwa [mul_neg, mul_neg, neg_ne_zero])
      (by linarith [show c1 * (α * β) * (c2 * (γ * -δ)) =
        -(c1 * (α * β) * (c2 * (γ * δ))) by ring]) hp
    exact ⟨M, e, r, s, hsol, hT, by rwa [mul_neg, mul_neg, neg_sq] at hlt,
      by rwa [mul_neg, mul_neg, neg_sq] at hle⟩

/-- The new solution of family QK is smaller than `αβγδ` as soon as `F |γδ| > 2 w_n c₁` and
`F |αβ| > 2 w_n c₂`: then `2 w_n² ((c₁αβ)² + (c₂γδ)²) < F² (αβγδ)²`. -/
theorem sq_lt_of_large {u v wn F c1 c2 : ℤ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h1 : (2 * wn * c1) ^ 2 < v ^ 2 * F ^ 2) (h2 : (2 * wn * c2) ^ 2 < u ^ 2 * F ^ 2) :
    2 * wn ^ 2 * ((c1 * u) ^ 2 + (c2 * v) ^ 2) < F ^ 2 * (u * v) ^ 2 := by
  have hu2 : 0 < u ^ 2 := by positivity
  have hv2 : 0 < v ^ 2 := by positivity
  have a := mul_lt_mul_of_pos_right h1 hu2
  have b := mul_lt_mul_of_pos_right h2 hv2
  nlinarith [a, b]

/-! ### Soundness of the torsion families -/

/-- If `X e'² < Y A` and `Y R ≤ X K`, or `X e'² ≤ Y A` and `Y R < X K`, then `K A ≤ R e²` gives
`e'² < e²`. -/
theorem sq_lt_of_bound {X Y K R A e e' : ℤ} (hK : 0 < K) (hX : 0 < X) (hY : 0 ≤ Y) (he : e ≠ 0)
    (hB : K * A ≤ R * e ^ 2)
    (h : X * e' ^ 2 < Y * A ∧ Y * R ≤ X * K ∨ X * e' ^ 2 ≤ Y * A ∧ Y * R < X * K) :
    e' ^ 2 < e ^ 2 := by
  have he2 : 0 < e ^ 2 := by positivity
  have hYB : Y * (K * A) ≤ Y * (R * e ^ 2) := mul_le_mul_of_nonneg_left hB hY
  have key : X * K * e' ^ 2 < X * K * e ^ 2 := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have k1 := mul_lt_mul_of_pos_left h1 hK
      have k2 := mul_le_mul_of_nonneg_right h2 he2.le
      linarith
    · have k1 := mul_le_mul_of_nonneg_left h1 hK.le
      have k2 := mul_lt_mul_of_pos_right h2 he2
      linarith
  exact lt_of_mul_lt_mul_left key (by positivity)

/-- **Soundness of `boundOK`.** -/
theorem boundOK_sound {weak : Bool} {p q P N X Y : ℕ} (h : boundOK weak p q P N X Y = true)
    (hX : 0 < X) (hP : 0 < P) (hN : 0 < N) {A e e' : ℤ} (he : e ≠ 0)
    (B1 : (boundK p : ℤ) * (P : ℤ) ^ 2 * A ≤ (p : ℤ) ^ 2 * e ^ 2)
    (B2 : (N : ℤ) ^ 2 * A ≤ (q : ℤ) ^ 2 * e ^ 2)
    (B3 : A ≤ e ^ 2) (hle : (X : ℤ) * e' ^ 2 ≤ Y * A)
    (hlt : weak = true → (X : ℤ) * e' ^ 2 < Y * A) : e' ^ 2 < e ^ 2 := by
  have key : ∀ {K R : ℕ}, 0 < K → (K : ℤ) * A ≤ R * e ^ 2 → leB weak (Y * R) (X * K) = true →
      e' ^ 2 < e ^ 2 := by
    intro K R hK hB hb
    refine sq_lt_of_bound (X := X) (Y := Y) (K := K) (R := R) (by exact_mod_cast hK)
      (by exact_mod_cast hX) (by positivity) he hB ?_
    cases weak
    · simp only [leB, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hb
      exact Or.inr ⟨hle, by exact_mod_cast hb⟩
    · simp only [leB, ↓reduceIte, decide_eq_true_eq] at hb
      exact Or.inl ⟨hlt rfl, by exact_mod_cast hb⟩
  simp only [boundOK, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact key (K := 1) (R := 1) one_pos (by simpa using B3) (by simpa using h)
  · exact key (K := boundK p * P ^ 2) (R := p ^ 2) (Nat.mul_pos (boundK_pos p) (by positivity))
      (by push_cast; exact B1) h
  · exact key (K := N ^ 2) (R := q ^ 2) (by positivity) (by push_cast; exact B2) h

theorem natCast_sqrt_sq {n : ℕ} (h : isSq n = true) : ((Nat.sqrt n : ℕ) : ℤ) ^ 2 = n := by
  exact_mod_cast (eq_sq_of_isSq h).symm

theorem ne_zero_of_sq_eq {x y : ℤ} (h : x ^ 2 = y) (hy : 0 < y) : x ≠ 0 := by
  rintro rfl
  simp at h
  omega

/-- **Soundness of `torsionOK1L`.** Each of the three families gives a smaller solution. -/
theorem torsionOK1L_sound {lim p q lam c1 c2 c3 c4 σ : ℕ}
    (h : torsionOK1L lim p q lam c1 c2 c3 c4 σ = true) (hp : 0 < p) (hpq : p < q) (hlam : 0 < lam)
    (hσ : 0 < σ) (hc1 : 0 < c1) (hc2 : 0 < c2) (hc3 : 0 < c3) (hc4 : 0 < c4) {α β γ δ e : ℤ}
    (hrel : (lam : ℤ) * (c1 * c2) = p * (c3 * c4))
    (E1 : (q : ℤ) * c3 ^ 2 * γ ^ 2 - lam * c1 ^ 2 * β ^ 2 = σ * δ ^ 2)
    (E2 : (q : ℤ) * c4 ^ 2 * β ^ 2 - lam * c2 ^ 2 * γ ^ 2 = σ * α ^ 2)
    (hne : ((c1 : ℤ) * (α * β)) ^ 2 ≠ (c2 * (γ * δ)) ^ 2)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0) (he : e ≠ 0)
    (B1 : (boundK p : ℤ) * ((c1 : ℤ) * (α * β) * (c2 * (γ * δ))) ^ 2 ≤ p ^ 2 * e ^ 2)
    (B2 : ((c3 : ℤ) * (α * γ) * (c4 * (β * δ))) ^ 2 ≤ q ^ 2 * e ^ 2)
    (B3 : (α * β * (γ * δ)) ^ 2 ≤ e ^ 2) :
    ∃ M' e' r' s', IsSol p q M' e' r' s' ∧ M' ^ 2 ≠ p * q * e' ^ 2 ∧ e' ^ 2 < e ^ 2 := by
  have hq : 0 < q := hp.trans hpq
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hσZ : (0 : ℤ) < σ := by exact_mod_cast hσ
  have hlamZ : (0 : ℤ) < lam := by exact_mod_cast hlam
  have hc1Z : (0 : ℤ) < c1 := by exact_mod_cast hc1
  have hc2Z : (0 : ℤ) < c2 := by exact_mod_cast hc2
  have hc3Z : (0 : ℤ) < c3 := by exact_mod_cast hc3
  have hc4Z : (0 : ℤ) < c4 := by exact_mod_cast hc4
  have fin : ∀ {weak : Bool} {X Y : ℕ} {e' : ℤ}, boundOK weak p q (c1 * c2) (c3 * c4) X Y = true →
      0 < X → (X : ℤ) * e' ^ 2 ≤ Y * (α * β * (γ * δ)) ^ 2 →
      (weak = true → (X : ℤ) * e' ^ 2 < Y * (α * β * (γ * δ)) ^ 2) → e' ^ 2 < e ^ 2 :=
    fun hb hX hle hlt ↦ boundOK_sound hb hX (Nat.mul_pos hc1 hc2) (Nat.mul_pos hc3 hc4) he
      (by push_cast; exact le_of_eq_of_le (by ring) B1)
      (by push_cast; exact le_of_eq_of_le (by ring) B2) B3 hle hlt
  simp only [torsionOK1L, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · -- family L
    simp only [linOK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hW, hh⟩, hH⟩, hb⟩ := h
    have hW' := natCast_sqrt_sq hW
    have hh' := natCast_sqrt_sq hh
    have hH' := natCast_sqrt_sq hH
    have hpq2 : p ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hpq.le 2
    have hDZ : (0 : ℤ) < (q : ℤ) ^ 2 - p ^ 2 :=
      sub_pos.mpr (by exact_mod_cast Nat.pow_lt_pow_left hpq two_ne_zero)
    push_cast [Nat.cast_sub hpq2] at hW' hh' hH'
    have hWpos : 0 < Nat.sqrt (q * lam) := Nat.sqrt_pos.mpr (Nat.mul_pos hq hlam)
    have hd : 0 < Nat.gcd c3 (c2 * Nat.sqrt (q * lam)) := Nat.gcd_pos_of_pos_left _ hc3
    obtain ⟨v, hv⟩ := Nat.gcd_dvd_left c3 (c2 * Nat.sqrt (q * lam))
    obtain ⟨u, hu⟩ := Nat.gcd_dvd_right c3 (c2 * Nat.sqrt (q * lam))
    rw [Nat.div_eq_of_eq_mul_right hd hv] at hb
    have huv : u * c3 = v * (c2 * Nat.sqrt (q * lam)) := by
      calc u * c3 = u * (Nat.gcd c3 (c2 * Nat.sqrt (q * lam)) * v) := by rw [← hv]
        _ = v * (Nat.gcd c3 (c2 * Nat.sqrt (q * lam)) * u) := by ring
        _ = v * (c2 * Nat.sqrt (q * lam)) := by rw [← hu]
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hu
      exact (Nat.mul_pos hc2 hWpos).ne' hu
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hv
      omega
    obtain ⟨m, hm, hb⟩ : ∃ m : ℕ, ((m : ℤ) = 1 ∨ ((m : ℤ) = 4 ∧
        (q : ℤ) * c3 ^ 2 ≠ lam * c1 ^ 2 + σ)) ∧
        boundOK false p q (c1 * c2) (c3 * c4) m (v ^ 2) = true := by
      split_ifs at hb with hc
      · exact ⟨1, Or.inl (by norm_num), hb⟩
      · refine ⟨4, Or.inr ⟨by norm_num, ?_⟩, hb⟩
        simp only [beq_iff_eq] at hc
        exact_mod_cast hc
    obtain ⟨M', e', r', s', hsol, hT, hlt⟩ := lin_step (m := m) (u := u) (v := v) hrel rfl E1 E2
      hW' hh' hH' (by exact_mod_cast huv) hc3Z.ne'
      (ne_zero_of_sq_eq hh' (mul_pos (mul_pos hDZ hlamZ) hσZ))
      (ne_zero_of_sq_eq hH' (mul_pos (mul_pos hDZ hqZ) hσZ)) (by exact_mod_cast hu0)
      (by exact_mod_cast hv0) hα hβ hγ hδ hm hne hpZ hqZ hc4Z.ne'
    exact ⟨M', e', r', s', hsol, hT, fin hb (by rcases hm with h | ⟨h, -⟩ <;> omega)
      (by push_cast; exact hlt) (by simp)⟩
  · -- family QD
    simp only [quadDOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    generalize quadDF p q lam c1 c2 c3 c4 σ = F at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hF⟩, d1⟩, d2⟩, d3⟩, d4⟩, hcop⟩, hb⟩ := h
    have hwd := natCast_sqrt_sq h1
    have hwn := natCast_sqrt_sq h2
    have hh := natCast_sqrt_sq h3
    push_cast [Nat.cast_sub hpq.le] at hwd hwn hh
    have dZ : ∀ {n : ℕ}, n % F = 0 → (F : ℤ) ∣ n :=
      fun h ↦ Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero h)
    have d1' := dZ d1
    have d2' := dZ d2
    have d3' := dZ d3
    have d4' := dZ d4
    push_cast [Nat.cast_sub hpq.le] at d1' d2' d3' d4'
    have hFc : IsCoprime (F : ℤ) (lam * c1) := by
      have := Nat.isCoprime_iff_coprime.mpr (show Nat.Coprime F (lam * c1) from hcop)
      push_cast at this
      exact this
    obtain ⟨M', e', r', s', hsol, hT, hlt⟩ := quadD_step hrel E1 E2 hne hwn hwd hh.symm hpZ hqZ
      hσZ (ne_zero_of_sq_eq hwn (by positivity)) (ne_zero_of_sq_eq hwd (by positivity)) hα hδ
      (by exact_mod_cast hF) d1' d2' d3' d4' hFc
    refine ⟨M', e', r', s', hsol, hT, fin hb (by positivity) ?_ fun _ ↦ ?_⟩
    · push_cast [Nat.cast_sub hpq.le]
      exact hlt.le
    · push_cast [Nat.cast_sub hpq.le]
      exact hlt
  · -- family QK
    simp only [quadKOKL, withNat_eq, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, hb⟩ := h
    have hwd := natCast_sqrt_sq h1
    have hwn := natCast_sqrt_sq h2
    have hh := natCast_sqrt_sq h3
    push_cast [Nat.cast_sub hpq.le] at hwd hwn hh
    have hF : 0 < Nat.gcd q (Nat.sqrt (c3 * c4)) := Nat.gcd_pos_of_pos_left _ hq
    obtain ⟨qF, hqF⟩ := Nat.gcd_dvd_left q (Nat.sqrt (c3 * c4))
    obtain ⟨wF, hwF⟩ := Nat.gcd_dvd_right q (Nat.sqrt (c3 * c4))
    obtain ⟨M', e', r', s', hsol, hT, hlt, hle⟩ :=
      quadK_step (F := (Nat.gcd q (Nat.sqrt (c3 * c4)) : ℤ))
      (qF := qF) (wF := wF) hrel E1 E2 hne hwn hwd hh.symm hlamZ hqZ hσZ
      (ne_zero_of_sq_eq hwn (by positivity)) (ne_zero_of_sq_eq hwd (by positivity))
      (by exact_mod_cast hqF) (by exact_mod_cast hwF)
      (mul_ne_zero hc1Z.ne' (mul_ne_zero hα hβ)) (mul_ne_zero hc2Z.ne' (mul_ne_zero hγ hδ)) hpZ
    refine ⟨M', e', r', s', hsol, hT, ?_⟩
    rcases hb with hb | hb
    · exact fin hb (pow_pos hF 2) (by push_cast; exact hlt.le) fun _ ↦ by push_cast; exact hlt
    -- the small box of QK
    simp only [decide_eq_true_eq] at hb
    have hγδ : γ.natAbs ≤ (γ * δ).natAbs := by
      rw [Int.natAbs_mul]
      exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hδ)
    have hαβ : β.natAbs ≤ (α * β).natAbs := by
      rw [Int.natAbs_mul]
      exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hα)
    -- the natural-number forms of `E1`, `E2`
    have e1 : lam * c1 ^ 2 * β.natAbs ^ 2 < q * c3 ^ 2 * γ.natAbs ^ 2 := by
      have : ((lam * c1 ^ 2 * β.natAbs ^ 2 : ℕ) : ℤ) < ((q * c3 ^ 2 * γ.natAbs ^ 2 : ℕ) : ℤ) := by
        push_cast
        simp only [sq_abs]
        have : 0 < (σ : ℤ) * δ ^ 2 := by positivity
        linarith
      exact_mod_cast this
    have e2 : lam * c2 ^ 2 * γ.natAbs ^ 2 < q * c4 ^ 2 * β.natAbs ^ 2 := by
      have : ((lam * c2 ^ 2 * γ.natAbs ^ 2 : ℕ) : ℤ) < ((q * c4 ^ 2 * β.natAbs ^ 2 : ℕ) : ℤ) := by
        push_cast
        simp only [sq_abs]
        have : 0 < (σ : ℤ) * α ^ 2 := by positivity
        linarith
      exact_mod_cast this
    by_cases hbig : 2 * Nat.sqrt (c3 * c4) * c1 / Nat.gcd q (Nat.sqrt (c3 * c4)) < (γ * δ).natAbs ∧
        2 * Nat.sqrt (c3 * c4) * c2 / Nat.gcd q (Nat.sqrt (c3 * c4)) < (α * β).natAbs
    · -- large variables: `F² e'² ≤ 2 w_n² (k₁² + k₂²) < F² (αβγδ)² ≤ F² e²`
      obtain ⟨hg, ha⟩ := hbig
      rw [Nat.div_lt_iff_lt_mul hF] at hg ha
      have hg' : (2 * (Nat.sqrt (c3 * c4) : ℤ) * c1) ^ 2 <
          (γ * δ) ^ 2 * (Nat.gcd q (Nat.sqrt (c3 * c4)) : ℤ) ^ 2 := by
        have h' : (((2 * Nat.sqrt (c3 * c4) * c1) ^ 2 : ℕ) : ℤ) <
            (((γ * δ).natAbs * Nat.gcd q (Nat.sqrt (c3 * c4))) ^ 2 : ℕ) := by
          exact_mod_cast Nat.pow_lt_pow_left hg two_ne_zero
        push_cast at h'
        simp only [mul_pow, sq_abs] at h'
        linarith
      have ha' : (2 * (Nat.sqrt (c3 * c4) : ℤ) * c2) ^ 2 <
          (α * β) ^ 2 * (Nat.gcd q (Nat.sqrt (c3 * c4)) : ℤ) ^ 2 := by
        have h' : (((2 * Nat.sqrt (c3 * c4) * c2) ^ 2 : ℕ) : ℤ) <
            (((α * β).natAbs * Nat.gcd q (Nat.sqrt (c3 * c4))) ^ 2 : ℕ) := by
          exact_mod_cast Nat.pow_lt_pow_left ha two_ne_zero
        push_cast at h'
        simp only [mul_pow, sq_abs] at h'
        linarith
      have key := sq_lt_of_large (mul_ne_zero hα hβ) (mul_ne_zero hγ hδ) hg' ha'
      have hFZ : (0 : ℤ) < (Nat.gcd q (Nat.sqrt (c3 * c4)) : ℤ) ^ 2 := by positivity
      exact lt_of_lt_of_le (lt_of_mul_lt_mul_left (hle.trans_lt key) hFZ.le) B3
    · -- small variables: `(β, γ)` lie in the box, which `smallCheck` has searched
      exfalso
      rw [not_and_or] at hbig
      simp only [not_lt] at hbig
      rcases hb with ⟨⟨-, -⟩, hb⟩ | ⟨-, hb⟩
      · refine hypCheck_sound hb hσ hlam hc1 hc2 E1 E2 hne ?_ hα hβ hγ hδ hbig
        rw [Nat.cast_zero, zero_mul]
        exact (mul_ne_zero (mul_ne_zero four_ne_zero hqZ.ne') (pow_ne_zero 2 (mul_ne_zero
          (mul_ne_zero hc1Z.ne' (mul_ne_zero hα hβ))
          (mul_ne_zero hc2Z.ne' (mul_ne_zero hγ hδ))))).symm
      rcases hbig with hg | ha
      · refine smallCheck_sound hb hσ E1 E2 hne hα hβ hγ hδ ?_ ?_
        · unfold quadKBoxβ
          refine le_trans ?_ (le_max_left _ _)
          rw [Nat.le_sqrt, Nat.le_div_iff_mul_le (by positivity)]
          have : q * c3 ^ 2 * γ.natAbs ^ 2 ≤
              q * c3 ^ 2 * (2 * Nat.sqrt (c3 * c4) * c1 / Nat.gcd q (Nat.sqrt (c3 * c4))) ^ 2 := by
            gcongr
            exact hγδ.trans hg
          calc β.natAbs * β.natAbs * (lam * c1 ^ 2) = lam * c1 ^ 2 * β.natAbs ^ 2 := by ring
            _ ≤ _ := e1.le.trans this
        · unfold quadKBoxγ
          exact le_trans (hγδ.trans hg) (le_max_left _ _)
      · refine smallCheck_sound hb hσ E1 E2 hne hα hβ hγ hδ ?_ ?_
        · unfold quadKBoxβ
          exact le_trans (hαβ.trans ha) (le_max_right _ _)
        · unfold quadKBoxγ
          refine le_trans ?_ (le_max_right _ _)
          rw [Nat.le_sqrt, Nat.le_div_iff_mul_le (by positivity)]
          have : q * c4 ^ 2 * β.natAbs ^ 2 ≤
              q * c4 ^ 2 * (2 * Nat.sqrt (c3 * c4) * c2 / Nat.gcd q (Nat.sqrt (c3 * c4))) ^ 2 := by
            gcongr
            exact hαβ.trans ha
          calc γ.natAbs * γ.natAbs * (lam * c2 ^ 2) = lam * c2 ^ 2 * γ.natAbs ^ 2 := by ring
            _ ≤ _ := e2.le.trans this

/-- **Soundness of `torsionOKL`**: `torsionOK1L_sound`, possibly after the symmetry
`(α, β, γ, δ, c₁, c₂, c₃, c₄) ↦ (δ, γ, β, α, c₂, c₁, c₄, c₃)`. -/
theorem torsionOKL_sound {lim p q lam c1 c2 c3 c4 σ : ℕ}
    (h : torsionOKL lim p q lam c1 c2 c3 c4 σ = true) (hp : 0 < p) (hpq : p < q) (hlam : 0 < lam)
    (hσ : 0 < σ) (hc1 : 0 < c1) (hc2 : 0 < c2) (hc3 : 0 < c3) (hc4 : 0 < c4) {α β γ δ e : ℤ}
    (hrel : (lam : ℤ) * (c1 * c2) = p * (c3 * c4))
    (E1 : (q : ℤ) * c3 ^ 2 * γ ^ 2 - lam * c1 ^ 2 * β ^ 2 = σ * δ ^ 2)
    (E2 : (q : ℤ) * c4 ^ 2 * β ^ 2 - lam * c2 ^ 2 * γ ^ 2 = σ * α ^ 2)
    (hne : ((c1 : ℤ) * (α * β)) ^ 2 ≠ (c2 * (γ * δ)) ^ 2)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0) (he : e ≠ 0)
    (B1 : (boundK p : ℤ) * ((c1 : ℤ) * (α * β) * (c2 * (γ * δ))) ^ 2 ≤ p ^ 2 * e ^ 2)
    (B2 : ((c3 : ℤ) * (α * γ) * (c4 * (β * δ))) ^ 2 ≤ q ^ 2 * e ^ 2)
    (B3 : (α * β * (γ * δ)) ^ 2 ≤ e ^ 2) :
    ∃ M' e' r' s', IsSol p q M' e' r' s' ∧ M' ^ 2 ≠ p * q * e' ^ 2 ∧ e' ^ 2 < e ^ 2 := by
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · exact torsionOK1L_sound h hp hpq hlam hσ hc1 hc2 hc3 hc4 hrel E1 E2 hne hα hβ hγ hδ he
      B1 B2 B3
  · exact torsionOK1L_sound (α := δ) (β := γ) (γ := β) (δ := α) h hp hpq hlam hσ hc2 hc1 hc4 hc3
      (by linear_combination hrel) E2 E1 (fun h0 ↦ hne (by linear_combination -h0)) hδ hγ hβ
      hα he (le_of_eq_of_le (by ring) B1) (le_of_eq_of_le (by ring) B2)
      (le_of_eq_of_le (by ring) B3)

/-! ### The class lemma -/

/-- An integer that is the square of a rational is the square of an integer. -/
theorem exists_sq_of_rat {z : ℤ} {w : ℚ} (h : (z : ℚ) = w ^ 2) : ∃ W : ℤ, z = W ^ 2 := by
  obtain ⟨W, hW⟩ := Rat.isSquare_intCast_iff.mp ⟨w, by rw [h, sq]⟩
  exact ⟨W, by rw [hW, sq]⟩

/-- **The class lemma.** The half-point of a tuple has `x = qλ (c₁α / (c₄δ))²`,
`x + p² = Dλσ (c₁β / (σδ))²` and `x + q² = Dqσ (c₃γ / (σδ))²`. If `a₀ qλ` and `b₀ Dλσ` are
squares, then `x = a₀ (r/s)²` with `r, s` coprime, and `b₀ (a₀ r² + p² s²)` and
`a₀ b₀ (a₀ r² + q² s²)` are squares, which `classCheck` rules out. -/
theorem classKill_sound {p q D lam c1 c2 c3 c4 σ : ℕ} (hk : ClassKill p q D lam σ)
    {α β γ δ : ℤ} (haZ : (q : ℤ) ^ 2 - p ^ 2 = D) (hrel : (lam : ℤ) * (c1 * c2) = p * (c3 * c4))
    (E1 : (q : ℤ) * c3 ^ 2 * γ ^ 2 - lam * c1 ^ 2 * β ^ 2 = σ * δ ^ 2)
    (E2 : (q : ℤ) * c4 ^ 2 * β ^ 2 - lam * c2 ^ 2 * γ ^ 2 = σ * α ^ 2)
    (hσ : 0 < σ) (hlam : 0 < lam) (hc4 : 0 < c4) (hδ : δ ≠ 0) : False := by
  obtain ⟨a0, b0, N, l, k, hl, hN, hk, h⟩ := hk
  simp only [classKillOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨ha0, hb0⟩, hA⟩, hB⟩, hc⟩ := h
  have hA' := natCast_sqrt_sq hA
  have hB' := natCast_sqrt_sq hB
  set A := Nat.sqrt (q * lam * a0)
  set B := Nat.sqrt (D * lam * σ * b0)
  push_cast at hA' hB'
  have hA'' : (A : ℚ) ^ 2 = q * lam * a0 := by exact_mod_cast hA'
  have hB'' : (B : ℚ) ^ 2 = D * lam * σ * b0 := by exact_mod_cast hB'
  have hσQ : (σ : ℚ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hlQ : (lam : ℚ) ≠ 0 := by exact_mod_cast hlam.ne'
  have ha0Q : (a0 : ℚ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hc4Q : (c4 : ℚ) ≠ 0 := by exact_mod_cast hc4.ne'
  have hδQ : (δ : ℚ) ≠ 0 := by exact_mod_cast hδ
  have E1' : (q : ℚ) * c3 ^ 2 * γ ^ 2 - lam * c1 ^ 2 * β ^ 2 = σ * δ ^ 2 := by exact_mod_cast E1
  have E2' : (q : ℚ) * c4 ^ 2 * β ^ 2 - lam * c2 ^ 2 * γ ^ 2 = σ * α ^ 2 := by exact_mod_cast E2
  have hrel' : (lam : ℚ) * (c1 * c2) = p * (c3 * c4) := by exact_mod_cast hrel
  have haZ' : (q : ℚ) ^ 2 - p ^ 2 = D := by exact_mod_cast haZ
  -- the point
  set x : ℚ := q * lam * c1 ^ 2 * α ^ 2 / (c4 ^ 2 * δ ^ 2)
  set u : ℚ := A * c1 * α / (a0 * c4 * δ)
  have hx : x = a0 * u ^ 2 := by
    simp only [x, u]
    field_simp
    rw [hA'']
    ring
  have P1 : (σ : ℚ) * (q * lam * c1 ^ 2 * α ^ 2 + p ^ 2 * c4 ^ 2 * δ ^ 2) =
      D * lam * c1 ^ 2 * c4 ^ 2 * β ^ 2 := by
    linear_combination (lam * c1 ^ 2 * c4 ^ 2 * β ^ 2 : ℚ) * haZ' -
      (q * γ ^ 2 * (p * c3 * c4 + lam * c1 * c2) : ℚ) * hrel' - (q * lam * c1 ^ 2 : ℚ) * E2' -
      (p ^ 2 * c4 ^ 2 : ℚ) * E1'
  have P2 : (σ : ℚ) * (q * lam * c1 ^ 2 * α ^ 2 + q ^ 2 * c4 ^ 2 * δ ^ 2) =
      D * q * c3 ^ 2 * c4 ^ 2 * γ ^ 2 := by
    linear_combination (q * γ ^ 2 * c3 ^ 2 * c4 ^ 2 : ℚ) * haZ' -
      (q * γ ^ 2 * (p * c3 * c4 + lam * c1 * c2) : ℚ) * hrel' - (q * lam * c1 ^ 2 : ℚ) * E2' -
      (q ^ 2 * c4 ^ 2 : ℚ) * E1'
  have hxp : x + p ^ 2 = D * lam * σ * (c1 * β / (σ * δ)) ^ 2 := by
    simp only [x]
    field_simp
    linear_combination P1
  have hxq : x + q ^ 2 = D * q * σ * (c3 * γ / (σ * δ)) ^ 2 := by
    simp only [x]
    field_simp
    linear_combination P2
  -- `x = a₀ (r/s)²` in lowest terms
  set r := u.num
  set s := u.den
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast u.den_nz
  have hxs : (a0 : ℚ) * (r : ℚ) ^ 2 = x * (s : ℚ) ^ 2 := by
    rw [hx, ← Rat.num_div_den u]
    field_simp
    rfl
  obtain ⟨W1, hW1⟩ := exists_sq_of_rat (z := b0 * (a0 * r ^ 2 + (p ^ 2 : ℕ) * s ^ 2))
    (w := s * B * c1 * β / (σ * δ)) (by
      push_cast
      rw [hxs, show x * (s : ℚ) ^ 2 + p ^ 2 * s ^ 2 = s ^ 2 * (x + p ^ 2) by ring, hxp]
      linear_combination (-(s : ℚ) ^ 2 * (c1 * β / (σ * δ)) ^ 2) * hB'')
  obtain ⟨W2, hW2⟩ := exists_sq_of_rat (z := (a0 * b0 : ℕ) * (a0 * r ^ 2 + (q ^ 2 : ℕ) * s ^ 2))
    (w := s * A * B * c3 * γ / (lam * σ * δ)) (by
      have hw : ((s : ℚ) * A * B * c3 * γ / (lam * σ * δ)) ^ 2 =
          (s : ℚ) ^ 2 * (A ^ 2 * B ^ 2) * c3 ^ 2 * γ ^ 2 / (lam * σ * δ) ^ 2 := by ring
      push_cast
      rw [hw, hA'', hB'', hxs, show x * (s : ℚ) ^ 2 + q ^ 2 * s ^ 2 = s ^ 2 * (x + q ^ 2) by ring,
        hxq]
      field_simp)
  have hrs : IsCoprime r (s : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [r, s, Int.gcd] using u.reduced)
  rw [Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · exact classCheck_sound (a := a0) (b := b0) (c := a0 * b0) (P := p ^ 2) (Q := q ^ 2)
      (W1 := W1) (W2 := W2) hl hN hk hc hrs (by push_cast at hW1 ⊢; linear_combination hW1)
      (by push_cast at hW2 ⊢; linear_combination hW2)
  · exact classCheckE_sound (a := a0) (b := b0) (c := a0 * b0) (P := p ^ 2) (Q := q ^ 2)
      (W1 := W1) (W2 := W2) hl hN hk hc hrs (by push_cast at hW1 ⊢; linear_combination hW1)
      (by push_cast at hW2 ⊢; linear_combination hW2)

/-! ### The descent -/

theorem natCast_div_gcd {p L : ℕ} : ((p / Nat.gcd p L : ℕ) : ℤ) * (Nat.gcd p L : ℕ) = p := by
  exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left p L)

theorem natCast_div_gcd' {p L : ℕ} : ((L / Nat.gcd p L : ℕ) : ℤ) * (Nat.gcd p L : ℕ) = L := by
  exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right p L)

/-- The coprimality of the splitting `k₁ = c₁αβ`, `k₂ = c₂γδ`, `j₁ = c₃αγ`, `j₂ = c₄βδ`, as
`tupleOK_sound` uses it. -/
structure TupleCop (α β γ δ : ℤ) (c1 c2 c3 c4 : ℕ) : Prop where
  ab : IsCoprime α β
  ag : IsCoprime α γ
  ad : IsCoprime α δ
  bg : IsCoprime β γ
  bd : IsCoprime β δ
  gd : IsCoprime γ δ
  c1g : IsCoprime (c1 : ℤ) γ
  c1d : IsCoprime (c1 : ℤ) δ
  c2a : IsCoprime (c2 : ℤ) α
  c2b : IsCoprime (c2 : ℤ) β
  c3b : IsCoprime (c3 : ℤ) β
  c3d : IsCoprime (c3 : ℤ) δ
  c4a : IsCoprime (c4 : ℤ) α
  c4g : IsCoprime (c4 : ℤ) γ

/-- **From a solution to a case.** A solution `(M, e)` gives a case `(λ, c₁, c₂, c₃, c₄, σ)` of
`CasesOK` with a solution `(α, β, γ, δ)` of `E₁`, `E₂` and the bounds of the descent step; `hstep`
turns any such case into the goal. The last hypothesis of `hstep` says that `(M, e)` is `±T₄`
(`M² = pq e²`) when `p (k₁² − k₂²)² = 4q (k₁k₂)²`. -/
theorem exists_case {p q D : ℕ} (hp : 0 < p) (hpq : p < q)
    (ha : q ^ 2 = p ^ 2 + D) (hcop : Nat.Coprime p q) {M e r s : ℤ} (h : IsSol p q M e r s)
    {Goal : Prop}
    (hstep : ∀ ⦃lam c1 c2 c3 c4 σ : ℕ⦄ ⦃α β γ δ : ℤ⦄, 0 < lam → lam ∣ p * q →
      c1 * c2 = p / Nat.gcd p lam → Nat.Coprime c1 c2 → c3 * c4 = lam / Nat.gcd p lam →
      Nat.Coprime c3 c4 → σ ∣ (lam / Nat.gcd p lam) ^ 2 * D → 0 < σ →
      0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → (lam : ℤ) * (c1 * c2) = p * (c3 * c4) →
      (q : ℤ) * c3 ^ 2 * γ ^ 2 - lam * c1 ^ 2 * β ^ 2 = σ * δ ^ 2 →
      (q : ℤ) * c4 ^ 2 * β ^ 2 - lam * c2 ^ 2 * γ ^ 2 = σ * α ^ 2 →
      ((c1 : ℤ) * (α * β)) ^ 2 ≠ (c2 * (γ * δ)) ^ 2 → α ≠ 0 → β ≠ 0 → γ ≠ 0 → δ ≠ 0 →
      (boundK p : ℤ) * ((c1 : ℤ) * (α * β) * (c2 * (γ * δ))) ^ 2 ≤ p ^ 2 * e ^ 2 →
      ((c3 : ℤ) * (α * γ) * (c4 * (β * δ))) ^ 2 ≤ q ^ 2 * e ^ 2 →
      (α * β * (γ * δ)) ^ 2 ≤ e ^ 2 → TupleCop α β γ δ c1 c2 c3 c4 →
      (M ^ 2 ≠ p * q * e ^ 2 → (p : ℤ) * ((c1 * (α * β)) ^ 2 - (c2 * (γ * δ)) ^ 2) ^ 2 ≠
        4 * q * (c1 * (α * β) * (c2 * (γ * δ))) ^ 2) → Goal) : Goal := by
  have hpZ0 : (0 : ℤ) < p := by exact_mod_cast hp
  have hqZ0 : (0 : ℤ) < q := by exact_mod_cast hp.trans hpq
  have hpqZ : (p : ℤ) < q := by exact_mod_cast hpq
  have haZ : (q : ℤ) ^ 2 - p ^ 2 = D := by
    have : ((q ^ 2 : ℕ) : ℤ) = ((p ^ 2 + D : ℕ) : ℤ) := by rw [ha]
    push_cast at this
    linear_combination this
  obtain ⟨k1, k2, j1, j2, hk1, hk2, hj1, hj2, hk, hj, hne, hC, hbound4, hbound, hjbound, hkdvd,
    hjdvd, hT4⟩ := exists_point hpZ0 hqZ0 h
  obtain ⟨L, k1', k2', hL, hLd, hk1', hk2', hk', hne', hsq, hdiff, h4, h5⟩ :=
    exists_lam (by positivity) hk1 hk2 hj1 hj2 hk hj hne hC
  have hg : 0 < Nat.gcd p L := Nat.gcd_pos_of_pos_left _ hp
  have hgZ : ((Nat.gcd p L : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hP' : 0 < p / Nat.gcd p L := Nat.div_pos (Nat.gcd_le_left _ hp) hg
  have hL' : 0 < L / Nat.gcd p L := Nat.div_pos (Nat.gcd_le_right _ hL) hg
  have hrel : ((L / Nat.gcd p L : ℕ) : ℤ) * (k1' * k2') = (p / Nat.gcd p L : ℕ) * (j1 * j2) := by
    refine mul_left_cancel₀ hgZ ?_
    linear_combination (k1' * k2') * natCast_div_gcd' (p := p) (L := L) -
      (j1 * j2) * natCast_div_gcd (p := p) (L := L) - h4
  obtain ⟨c1, c2, c3, c4, α, β, γ, δ, hc12, hc34, rfl, rfl, rfl, rfl⟩ :=
    exists_split hP' hL' (Nat.coprime_div_gcd_div_gcd hg) hk1' hk' hj hrel
  -- nonzero factors
  have hc1 : (c1 : ℤ) ≠ 0 := left_ne_zero_of_mul hk1'
  have hc2 : (c2 : ℤ) ≠ 0 := left_ne_zero_of_mul hk2'
  have hc3 : (c3 : ℤ) ≠ 0 := left_ne_zero_of_mul hj1
  have hc4 : (c4 : ℤ) ≠ 0 := left_ne_zero_of_mul hj2
  have hα : α ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hk1')
  have hβ : β ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hk1')
  have hγ : γ ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hk2')
  have hδ : δ ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hk2')
  -- coprimality
  have K1 := hk'.of_mul_left_right
  have K2 := hk'.of_mul_left_left
  have J1 := hj.of_mul_left_right
  have J2 := hj.of_mul_left_left
  have hag : IsCoprime α γ := K1.of_mul_left_left.of_mul_right_right.of_mul_right_left
  have had : IsCoprime α δ := K1.of_mul_left_left.of_mul_right_right.of_mul_right_right
  have hbg : IsCoprime β γ := K1.of_mul_left_right.of_mul_right_right.of_mul_right_left
  have hbd : IsCoprime β δ := K1.of_mul_left_right.of_mul_right_right.of_mul_right_right
  have hab : IsCoprime α β := J1.of_mul_left_left.of_mul_right_right.of_mul_right_left
  have hgd : IsCoprime γ δ := J1.of_mul_left_right.of_mul_right_right.of_mul_right_right
  have h1g : IsCoprime (c1 : ℤ) γ := K2.of_mul_right_right.of_mul_right_left
  have h1d : IsCoprime (c1 : ℤ) δ := K2.of_mul_right_right.of_mul_right_right
  have h2a : IsCoprime (c2 : ℤ) α := (K1.symm.of_mul_left_left).of_mul_right_left
  have h2b : IsCoprime (c2 : ℤ) β := (K1.symm.of_mul_left_left).of_mul_right_right
  have h3b : IsCoprime (c3 : ℤ) β := J2.of_mul_right_right.of_mul_right_left
  have h3d : IsCoprime (c3 : ℤ) δ := J2.of_mul_right_right.of_mul_right_right
  have h4a : IsCoprime (c4 : ℤ) α := (J1.symm.of_mul_left_left).of_mul_right_left
  have h4g : IsCoprime (c4 : ℤ) γ := (J1.symm.of_mul_left_left).of_mul_right_right
  have hc12' : Nat.Coprime c1 c2 :=
    Nat.isCoprime_iff_coprime.mp (K2.of_mul_right_left)
  have hc34' : Nat.Coprime c3 c4 :=
    Nat.isCoprime_iff_coprime.mp (J2.of_mul_right_left)
  -- σ
  have hrel2 : (L : ℤ) * (c1 * c2) = p * (c3 * c4) := by
    have e12 : (c1 : ℤ) * c2 = (p / Nat.gcd p L : ℕ) := by rw [← Nat.cast_mul, hc12]
    have e34 : (c3 : ℤ) * c4 = (L / Nat.gcd p L : ℕ) := by rw [← Nat.cast_mul, hc34]
    rw [e12, e34]
    refine mul_left_cancel₀ hgZ ?_
    linear_combination (L : ℤ) * natCast_div_gcd (p := p) (L := L) -
      (p : ℤ) * natCast_div_gcd' (p := p) (L := L)
  obtain ⟨σ, hσ, hσd, E1, E2⟩ := exists_sigma hpZ0 hpqZ (by exact_mod_cast hL) haZ hrel2 hc3 hc4
    hα hβ hγ had hbg h5
  obtain ⟨σN, rfl⟩ : ∃ σN : ℕ, σ = σN := ⟨σ.toNat, (Int.toNat_of_nonneg hσ.le).symm⟩
  have hσN : 0 < σN := by exact_mod_cast hσ
  have hσNd : σN ∣ (L / Nat.gcd p L) ^ 2 * D := by
    rw [← hc34]
    have : ((σN : ℕ) : ℤ) ∣ (((c3 * c4) ^ 2 * D : ℕ) : ℤ) := by
      push_cast
      rw [mul_comm]
      exact hσd
    exact_mod_cast this
  -- the three bounds on the new solution: `B1`, `B2` from step 1, and `αβγδ ∣ e`
  have B1 : (boundK p : ℤ) * ((c1 : ℤ) * (α * β) * (c2 * (γ * δ))) ^ 2 ≤ p ^ 2 * e ^ 2 := by
    rw [hsq]
    unfold boundK
    split
    · rename_i hev
      obtain ⟨p₀, hp₀⟩ : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by simpa using hev)
      exact_mod_cast hbound4 p₀ (by exact_mod_cast hp₀)
    · simpa using hbound
  have B3 : (α * β * (γ * δ)) ^ 2 ≤ e ^ 2 := by
    have hd1 : α * β * (γ * δ) ∣ k1 * k2 := by
      refine dvd_trans (b := c1 * (α * β) * (c2 * (γ * δ))) ⟨c1 * c2, by ring⟩ ?_
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_eq_iff_sq_eq.mpr hsq]
    have hpe : α * β * (γ * δ) ∣ (p : ℤ) * e := hd1.trans hkdvd
    have hqe : α * β * (γ * δ) ∣ (q : ℤ) * e :=
      dvd_trans (b := c3 * (α * γ) * (c4 * (β * δ))) ⟨c3 * c4, by ring⟩ hjdvd
    obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) q := Nat.isCoprime_iff_coprime.mpr hcop
    have hdiv : α * β * (γ * δ) ∣ e := by
      rw [show e = u * (p * e) + v * (q * e) by linear_combination (-e) * huv]
      exact dvd_add (dvd_mul_of_dvd_right hpe _) (dvd_mul_of_dvd_right hqe _)
    exact Int.natAbs_le_iff_sq_le.mp (Int.natAbs_le_of_dvd_ne_zero hdiv h.2.1)
  have hLd' : L ∣ p * q := by exact_mod_cast hLd
  exact hstep hL hLd' hc12 hc12' hc34 hc34' hσNd hσN (Nat.pos_of_ne_zero (by exact_mod_cast hc1))
    (Nat.pos_of_ne_zero (by exact_mod_cast hc2)) (Nat.pos_of_ne_zero (by exact_mod_cast hc3))
    (Nat.pos_of_ne_zero (by exact_mod_cast hc4)) hrel2 E1 E2 hne' hα hβ hγ hδ B1 hjbound B3
    ⟨hab, hag, had, hbg, hbd, hgd, h1g, h1d, h2a, h2b, h3b, h3d, h4a, h4g⟩
    fun hT ↦ by rw [hdiff, hsq]; exact hT4 hT

/-- **One descent step.** Given the finite check for `(p, q)`, every solution gives a solution
with a smaller `|e|`. -/
theorem exists_smaller {p q D : ℕ} (hp : 0 < p) (hpq : p < q)
    (ha : q ^ 2 = p ^ 2 + D) (hcop : Nat.Coprime p q)
    (hchk : CasesOK p q D) {M e r s : ℤ} (h : IsSol p q M e r s) :
    ∃ M' e' r' s', IsSol p q M' e' r' s' ∧ e' ^ 2 < e ^ 2 := by
  have haZ : (q : ℤ) ^ 2 - p ^ 2 = D := by
    have : ((q ^ 2 : ℕ) : ℤ) = ((p ^ 2 + D : ℕ) : ℤ) := by rw [ha]
    push_cast at this
    linear_combination this
  refine exists_case hp hpq ha hcop h fun lam c1 c2 c3 c4 σ α β γ δ hL hLd hc12 hc12' hc34 hc34'
    hσd hσ hc1 hc2 hc3 hc4 hrel E1 E2 hne hα hβ hγ hδ B1 B2 B3 hc _ ↦ ?_
  rcases hchk hL hLd hc12 hc12' hc34 hc34' hσd with
    ⟨lim, hT⟩ | ⟨N, l, hN, hl, hlN, hT⟩ | hK
  · obtain ⟨M', e', r', s', hsol, -, hlt⟩ := torsionOKL_sound hT hp hpq hL hσ hc1 hc2 hc3 hc4
      hrel E1 E2 hne hα hβ hγ hδ h.2.1 B1 B2 B3
    exact ⟨M', e', r', s', hsol, hlt⟩
  · exact (tupleOK_sound (by simpa using ⟨hN, hl, hlN⟩) hT hσ hc.ab hc.ag hc.ad hc.bg hc.bd
      hc.gd hc.c1g hc.c1d hc.c2a hc.c2b hc.c3b hc.c3d hc.c4a hc.c4g E1 E2).elim
  · exact (classKill_sound hK haZ hrel E1 E2 hσ (by exact_mod_cast hL) (by exact_mod_cast hc4)
      hδ).elim

/-- **The descent.** If every case is covered (`CasesOK p q D` with `D = q² − p²`), there are no
integers `M, e ≠ 0` with `M² + p² e²` and `M² + q² e²` both squares. -/
theorem not_isSol_of_casesOK {p q D : ℕ} (hp : 0 < p) (hpq : p < q)
    (hD : q ^ 2 = p ^ 2 + D) (hcop : Nat.Coprime p q)
    (hchk : CasesOK p q D) (M e r s : ℤ) :
    ¬ IsSol p q M e r s := by
  suffices ∀ n : ℕ, ∀ M e r s : ℤ, e.natAbs = n → ¬ IsSol p q M e r s from this _ M e r s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M e r s hn h
    obtain ⟨M', e', r', s', h', hlt⟩ := exists_smaller hp hpq hD hcop hchk h
    exact ih _ (hn ▸ Int.natAbs_lt_iff_sq_lt.mpr hlt) M' e' r' s' rfl h'

theorem pos_of_sq_eq_sq_add {p q D : ℕ} (hpq : p < q) (hD : q ^ 2 = p ^ 2 + D) : 0 < D := by
  have := Nat.pow_lt_pow_left hpq two_ne_zero
  omega

/-- **The descent** for `q² − p² = a²`, given a certificate `Covered p q a`. -/
theorem not_isSol {p q a : ℕ} (hp : 0 < p) (hpq : p < q)
    (ha : q ^ 2 = p ^ 2 + a ^ 2) (hcop : Nat.Coprime p q)
    (hchk : Covered p q a) (M e r s : ℤ) :
    ¬ IsSol p q M e r s :=
  not_isSol_of_casesOK hp hpq ha hcop (hchk.casesOK hp (hp.trans hpq)
    (Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at ha; omega)) M e r s

/-- **The descent** for any `q² − p² = D`, given a certificate `CoveredD p q D`. This is the
form used for the pair `(U, V)` of a fiber, where `D = V² − U²` or `U² − V²` is not a square. -/
theorem not_isSolD {p q D : ℕ} (hp : 0 < p) (hpq : p < q)
    (hD : q ^ 2 = p ^ 2 + D) (hcop : Nat.Coprime p q)
    (hchk : CoveredD p q D) (M e r s : ℤ) :
    ¬ IsSol p q M e r s :=
  not_isSol_of_casesOK hp hpq hD hcop
    (hchk.casesOK hp (hp.trans hpq) (pos_of_sq_eq_sq_add hpq hD)) M e r s

/-- The descent over `ℚ`: for rational `t ≠ 0`, `t² + p²` and `t² + q²` are not both squares. -/
theorem not_isSquare_of_casesOK {p q D : ℕ} (hp : 0 < p) (hpq : p < q)
    (hD : q ^ 2 = p ^ 2 + D) (hcop : Nat.Coprime p q)
    (hchk : CasesOK p q D) {t : ℚ} (ht : t ≠ 0) :
    ¬ (IsSquare (t ^ 2 + (p : ℚ) ^ 2) ∧ IsSquare (t ^ 2 + (q : ℚ) ^ 2)) := by
  rintro ⟨hp', hq'⟩
  have key : ∀ c : ℤ, IsSquare (t ^ 2 + (c : ℚ) ^ 2) →
      IsSquare (t.num ^ 2 + c ^ 2 * (t.den : ℤ) ^ 2) := by
    rintro c ⟨w, hw⟩
    rw [← Rat.isSquare_intCast_iff]
    refine ⟨w * t.den, ?_⟩
    push_cast
    rw [← Rat.mul_den_eq_num]
    linear_combination (t.den : ℚ) ^ 2 * hw
  obtain ⟨r, hr⟩ := key p (by exact_mod_cast hp')
  obtain ⟨s, hs⟩ := key q (by exact_mod_cast hq')
  exact not_isSol_of_casesOK hp hpq hD hcop hchk t.num t.den r s
    ⟨Rat.num_ne_zero.mpr ht, by exact_mod_cast t.den_nz, by rw [hr]; ring, by rw [hs]; ring⟩

/-- The descent over `ℚ` for `q² − p² = a²`. -/
theorem not_isSquare_sq_add_sq_and_sq_add_sq {p q a : ℕ} (hp : 0 < p) (hpq : p < q)
    (ha : q ^ 2 = p ^ 2 + a ^ 2) (hcop : Nat.Coprime p q)
    (hchk : Covered p q a) {t : ℚ} (ht : t ≠ 0) :
    ¬ (IsSquare (t ^ 2 + (p : ℚ) ^ 2) ∧ IsSquare (t ^ 2 + (q : ℚ) ^ 2)) :=
  not_isSquare_of_casesOK hp hpq ha hcop (hchk.casesOK hp (hp.trans hpq)
    (Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at ha; omega)) ht

/-- The descent over `ℚ` for any `q² − p² = D`. -/
theorem not_isSquare_sq_add_sq_and_sq_add_sqD {p q D : ℕ} (hp : 0 < p) (hpq : p < q)
    (hD : q ^ 2 = p ^ 2 + D) (hcop : Nat.Coprime p q)
    (hchk : CoveredD p q D) {t : ℚ} (ht : t ≠ 0) :
    ¬ (IsSquare (t ^ 2 + (p : ℚ) ^ 2) ∧ IsSquare (t ^ 2 + (q : ℚ) ^ 2)) :=
  not_isSquare_of_casesOK hp hpq hD hcop
    (hchk.casesOK hp (hp.trans hpq) (pos_of_sq_eq_sq_add hpq hD)) ht

end Descent

end PerfectCuboid
