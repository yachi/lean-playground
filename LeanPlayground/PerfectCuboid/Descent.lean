module

public import LeanPlayground.PerfectCuboid.DescentCheck
public import LeanPlayground.PerfectCuboid.FiberTwoOne

/-!
# A generic descent for two right triangles with a common leg

Fix coprime positive integers `p < q` with `p` even and `q² − p² = a²` a square. This file proves,
under a finite check that the kernel runs, that there are no integers `M, e ≠ 0` such that both
`M² + p² e²` and `M² + q² e²` are squares. Geometrically: there is no rational `t ≠ 0` with
`t² + p²` and `t² + q²` both squares, i.e. no point of infinite order on the elliptic curve
`y² = x (x + p²)(x + q²)` with `x` a square. The elliptic curve never appears in the Lean code.

For a fiber `(m, n)` of the master-tuple parametrization, `(p, q) = (2mn, m² + n²)` and
`a = m² − n²`. A perfect cuboid with two edges `a k` and `2mn k` would give such `M, e`
(`M` the third edge, `e = k`), so each successful check rules out one edge ratio
`(m² − n²) : 2mn`. The case `(p, q) = (4, 5)` is the `3 : 4` fiber of
`LeanPlayground.PerfectCuboid.FiberTwoOne`, done there by hand.

## The descent

This is the descent of `FiberTwoOne` with `4, 5` replaced by `p, q`.

1. (`exists_point`) Write `t = M/e`. Then `t = (p/2)(k − 1/k) = (q/2)(j − 1/j)` with
   `k = k₁/k₂`, `j = j₁/j₂` in lowest terms, so
   `p j₁j₂ (k₁² − k₂²) = q k₁k₂ (j₁² − j₂²)`, and `4 (k₁k₂)² ≤ p² e²`.
2. (`exists_lam`) Since `k₁k₂` is coprime to `k₁² − k₂²` there is `λ ∣ pq` with
   `p j₁j₂ = λ k₁k₂` and `λ (k₁² − k₂²) = q (j₁² − j₂²)`. Replacing `k` by `−1/k` makes `λ > 0`.
3. (`exists_split`) With `g = gcd(p, λ)`, `p' = p/g`, `λ' = λ/g`, the four-number lemma writes
   `k₁ = c₁αβ`, `k₂ = c₂γδ`, `j₁ = c₃αγ`, `j₂ = c₄βδ` with `c₁c₂ = p'`, `c₃c₄ = λ'`.
   The numbers `α, β, γ, δ` are pairwise coprime.
4. (`exists_sigma`) The second equation becomes `α² X = δ² Y`, so `X = −σ δ²`, `Y = −σ α²`:
   `q c₃² γ² − λ c₁² β² = σ δ²` and `q c₄² β² − λ c₂² γ² = σ α²`. Multiplying the two
   inequalities that `σ ≤ 0` would give yields `p² ≥ q²`, so `σ > 0`; also `σ ∣ λ'² a²`.
5. Each tuple `(λ, c₁, c₂, c₃, c₄, σ)` is now either of one of two shapes, or impossible by a
   congruence. The congruences are checked by `fiberCheck`
   (`LeanPlayground.PerfectCuboid.DescentCheck`). The two shapes give a smaller solution:
   * (`classI_step`) `λ = p`, `cᵢ = 1`, `σ = (q − p) s²`: the new solution is
     `M' = βγ + s²αδ`, `e' = (β² − γ²)/(q − p)`, with
     `(βγ + s²αδ)(βγ − s²αδ) = pq e'²`. This is the translate by a `4`-torsion point.
   * (`classII_a`, `classII_b`) `λ = q`, `{c₃, c₄} = {1, q}`, `σ = q s²`: the new solution is
     `M' = c₂ δ`, `e' = α` (or `M' = c₁ α`, `e' = δ`).
   In both cases `p² e'² < 4 (k₁k₂)² ≤ p² e²`, so `|e|` decreases.

## Main results

* `not_isSol` — the descent, given `fiberCheck p q a mods = true`.
* `not_isSquare_sq_add_sq_and_sq_add_sq` — the same over `ℚ`.
-/

@[expose] public section

namespace PerfectCuboid

namespace Descent

open FiberTwoOne (isCoprime_mul_sq_sub four_numbers exists_rho one_le_sq)

/-- An integer solution of `M² + p² e² = r²`, `M² + q² e² = s²` with `M, e ≠ 0`. -/
def IsSol (p q M e r s : ℤ) : Prop :=
  M ≠ 0 ∧ e ≠ 0 ∧ M ^ 2 + p ^ 2 * e ^ 2 = r ^ 2 ∧ M ^ 2 + q ^ 2 * e ^ 2 = s ^ 2

/-! ### Step 1: from a solution to a point `(k, j)` -/

theorem exists_point {p p₀ q M e r s : ℤ} (hp : p = 2 * p₀) (hp₀ : 0 < p₀) (hq : 0 < q)
    (h : IsSol p q M e r s) :
    ∃ k1 k2 j1 j2 : ℤ, k1 ≠ 0 ∧ k2 ≠ 0 ∧ j1 ≠ 0 ∧ j2 ≠ 0 ∧ IsCoprime k1 k2 ∧ IsCoprime j1 j2 ∧
      k1 ^ 2 ≠ k2 ^ 2 ∧ p * (j1 * j2) * (k1 ^ 2 - k2 ^ 2) = q * (k1 * k2) * (j1 ^ 2 - j2 ^ 2) ∧
      4 * (k1 * k2) ^ 2 ≤ p ^ 2 * e ^ 2 := by
  subst hp
  obtain ⟨hM, he, hr, hs⟩ := h
  have he2 : 0 < e ^ 2 := by positivity
  have hrM : r + M ≠ 0 := fun h0 => by
    rw [show r = -M by linarith] at hr
    have : 0 < (2 * p₀) ^ 2 * e ^ 2 := by positivity
    linarith
  have hsM : s + M ≠ 0 := fun h0 => by
    rw [show s = -M by linarith] at hs
    have : 0 < q ^ 2 * e ^ 2 := by positivity
    linarith
  obtain ⟨g, k1, k2, hg, hkg, hk1g, hk2g⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left (2 * p₀ * e) hrM)
  obtain ⟨g', j1, j2, hg', hjg, hj1g, hj2g⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left (q * e) hsM)
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hg0' : (g' : ℤ) ≠ 0 := by exact_mod_cast hg'.ne'
  have hk : IsCoprime k1 k2 := Int.isCoprime_iff_gcd_eq_one.mpr hkg
  have hj : IsCoprime j1 j2 := Int.isCoprime_iff_gcd_eq_one.mpr hjg
  have hk1 : k1 ≠ 0 := by rintro rfl; exact hrM (by rw [hk1g]; ring)
  have hk2 : k2 ≠ 0 := by
    rintro rfl
    have : 2 * p₀ * e = 0 := by rw [hk2g]; ring
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
    linear_combination -(r - M) * hk1g - hr + (2 * p₀ * e + k2 * g) * hk2g
  have hj3 : j1 * (s - M) = j2 ^ 2 * g' := by
    refine mul_left_cancel₀ hg0' ?_
    linear_combination -(s - M) * hj1g - hs + (q * e + j2 * g') * hj2g
  have R1 : p₀ * e * (k1 ^ 2 - k2 ^ 2) = M * (k1 * k2) := by
    refine mul_left_cancel₀ (mul_ne_zero two_ne_zero hg0) ?_
    linear_combination g * (k1 ^ 2 - k2 ^ 2) * hk2g - g * k1 * k2 * hk1g + g * k2 * hk3
  have R2 : q * e * (j1 ^ 2 - j2 ^ 2) = 2 * M * (j1 * j2) := by
    refine mul_left_cancel₀ (mul_ne_zero two_ne_zero hg0') ?_
    linear_combination 2 * g' * (j1 ^ 2 - j2 ^ 2) * hj2g - 2 * g' * j1 * j2 * hj1g
      + 2 * g' * j2 * hj3
  have hC : 2 * p₀ * (j1 * j2) * (k1 ^ 2 - k2 ^ 2) = q * (k1 * k2) * (j1 ^ 2 - j2 ^ 2) := by
    refine mul_left_cancel₀ (mul_ne_zero hq.ne' he) ?_
    linear_combination 2 * q * (j1 * j2) * R1 - q * (k1 * k2) * R2
  have hne : k1 ^ 2 ≠ k2 ^ 2 := by
    intro h0
    rw [h0, sub_self, mul_zero] at R1
    exact mul_ne_zero hM (mul_ne_zero hk1 hk2) R1.symm
  have hdvd : k1 * k2 ∣ p₀ * e :=
    (isCoprime_mul_sq_sub hk).dvd_of_dvd_mul_right ⟨M, by linear_combination R1⟩
  have hle : (k1 * k2) ^ 2 ≤ (p₀ * e) ^ 2 :=
    Int.natAbs_le_iff_sq_le.mp (Int.natAbs_le_of_dvd_ne_zero hdvd (mul_ne_zero hp₀.ne' he))
  refine ⟨k1, k2, j1, j2, hk1, hk2, hj1, hj2, hk, hj, hne, hC, ?_⟩
  linear_combination 4 * hle

/-! ### Step 2: the number `λ` -/

theorem exists_lam {p q k1 k2 j1 j2 : ℤ} (hpq : 0 < p * q) (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0)
    (hj1 : j1 ≠ 0) (hj2 : j2 ≠ 0) (hk : IsCoprime k1 k2) (hj : IsCoprime j1 j2)
    (hne : k1 ^ 2 ≠ k2 ^ 2)
    (hC : p * (j1 * j2) * (k1 ^ 2 - k2 ^ 2) = q * (k1 * k2) * (j1 ^ 2 - j2 ^ 2)) :
    ∃ (L : ℕ) (k1' k2' : ℤ), 0 < L ∧ (L : ℤ) ∣ p * q ∧ k1' ≠ 0 ∧ k2' ≠ 0 ∧
      IsCoprime k1' k2' ∧ k1' ^ 2 ≠ k2' ^ 2 ∧ (k1' * k2') ^ 2 = (k1 * k2) ^ 2 ∧
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
      by rw [neg_sq]; exact Ne.symm hne, by ring, ?_, ?_⟩
    · rw [Int.toNat_of_nonneg (by omega)]; linear_combination -hlμ
    · rw [Int.toNat_of_nonneg (by omega)]; linear_combination h4
    · rw [Int.toNat_of_nonneg (by omega)]; linear_combination h5
  · refine ⟨l.toNat, k1, k2, by omega, ⟨μ, ?_⟩, hk1, hk2, hk, hne, rfl, ?_, ?_⟩
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

theorem exists_sigma {p q a L c1 c2 c3 c4 α β γ δ : ℤ} (hp : 0 < p) (hpq : p < q) (hL : 0 < L)
    (ha : q ^ 2 - p ^ 2 = a ^ 2) (hrel : L * (c1 * c2) = p * (c3 * c4)) (hc3 : c3 ≠ 0)
    (hc4 : c4 ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (had : IsCoprime α δ) (hbg : IsCoprime β γ)
    (h5 : L * ((c1 * (α * β)) ^ 2 - (c2 * (γ * δ)) ^ 2) =
      q * ((c3 * (α * γ)) ^ 2 - (c4 * (β * δ)) ^ 2)) :
    ∃ σ : ℤ, 0 < σ ∧ σ ∣ a ^ 2 * (c3 * c4) ^ 2 ∧
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
  have d1 : ρ ∣ a ^ 2 * (c3 * c4) ^ 2 * β ^ 2 :=
    ⟨-(L * c2 ^ 2 * δ ^ 2 + q * c3 ^ 2 * α ^ 2), by
      linear_combination (-(c3 * c4) ^ 2 * β ^ 2) * ha - L * c2 ^ 2 * hX - q * c3 ^ 2 * hY
        + (L * c1 * c2 + p * c3 * c4) * β ^ 2 * hrel⟩
  have d2 : ρ ∣ a ^ 2 * (c3 * c4) ^ 2 * γ ^ 2 :=
    ⟨-(q * c4 ^ 2 * δ ^ 2 + L * c1 ^ 2 * α ^ 2), by
      linear_combination (-(c3 * c4) ^ 2 * γ ^ 2) * ha - q * c4 ^ 2 * hX - L * c1 ^ 2 * hY
        + (L * c1 * c2 + p * c3 * c4) * γ ^ 2 * hrel⟩
  exact (dvd_of_dvd_sq hbg d1 d2).neg_left

/-! ### Step 5: the two surviving shapes -/

/-- `λ = p`, `c₁ = c₂ = c₃ = c₄ = 1`, `σ = (q − p) s²`: translate by a `4`-torsion point. -/
theorem classI_step {p q s α β γ δ : ℤ} (hp : 0 < p) (hpq : p < q)
    (hcop : IsCoprime (q - p) (q + p)) (hs : s ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (hδ : δ ≠ 0) (hbg : IsCoprime β γ) (hne : (α * β) ^ 2 ≠ (γ * δ) ^ 2)
    (E1 : q * γ ^ 2 - p * β ^ 2 = (q - p) * s ^ 2 * δ ^ 2)
    (E2 : q * β ^ 2 - p * γ ^ 2 = (q - p) * s ^ 2 * α ^ 2) :
    ∃ M e r t, IsSol p q M e r t ∧ p ^ 2 * e ^ 2 < 4 * (α * β * (γ * δ)) ^ 2 := by
  have hqp : q - p ≠ 0 := by linarith
  obtain ⟨e, he⟩ : q - p ∣ β ^ 2 - γ ^ 2 :=
    hcop.dvd_of_dvd_mul_left ⟨s ^ 2 * (α ^ 2 - δ ^ 2), by linear_combination E2 - E1⟩
  have G1 : (β * γ + s ^ 2 * α * δ) ^ 2 + p ^ 2 * e ^ 2 = (s * (α * γ + β * δ)) ^ 2 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hqp) ?_
    linear_combination (p - q) * (α * s - β) * (α * s + β) * E1 +
      p * (β - γ) * (β + γ) * E2 - p ^ 2 * ((q - p) * e + β ^ 2 - γ ^ 2) * he
  have G2 : (β * γ + s ^ 2 * α * δ) ^ 2 + q ^ 2 * e ^ 2 = (s * (α * β + γ * δ)) ^ 2 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hqp) ?_
    linear_combination (p - q) * (α * s - γ) * (α * s + γ) * E1 +
      q * (β - γ) * (β + γ) * E2 - q ^ 2 * ((q - p) * e + β ^ 2 - γ ^ 2) * he
  have G3 : (β * γ + s ^ 2 * α * δ) * (β * γ - s ^ 2 * α * δ) = p * q * e ^ 2 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hqp) ?_
    linear_combination (-α ^ 2 * s ^ 2 * (p - q)) * E1 + (-β ^ 2 * p + γ ^ 2 * q) * E2 +
      p * q * (β ^ 2 - γ ^ 2 + (q - p) * e) * he
  have he0 : e ≠ 0 := by
    rintro rfl
    have h0 : γ ^ 2 = β ^ 2 := by linear_combination -he
    have hu : IsUnit (β ^ 2) := by
      rw [← isCoprime_self]
      have := hbg.pow (m := 2) (n := 2)
      rwa [h0] at this
    rw [Int.isUnit_iff] at hu
    have hb1 : β ^ 2 = 1 := hu.resolve_right (by nlinarith [sq_nonneg β])
    have hg1 : γ ^ 2 = 1 := by linarith
    have hsd : s ^ 2 * δ ^ 2 = 1 := by
      refine mul_left_cancel₀ hqp ?_
      linear_combination -E1 + q * hg1 - p * hb1
    have hsa : s ^ 2 * α ^ 2 = 1 := by
      refine mul_left_cancel₀ hqp ?_
      linear_combination -E2 + q * hb1 - p * hg1
    have hs2 := one_le_sq hs
    have ha2 := one_le_sq hα
    have hd2 := one_le_sq hδ
    have hd1 : δ ^ 2 = 1 := by nlinarith
    have ha1 : α ^ 2 = 1 := by nlinarith
    exact hne (by rw [mul_pow, mul_pow, ha1, hb1, hg1, hd1])
  have hM : β * γ + s ^ 2 * α * δ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at G3
    have hq0 : 0 < q := hp.trans hpq
    have : 0 < p * q * e ^ 2 := by positivity
    linarith
  refine ⟨_, e, _, _, ⟨hM, he0, G1, G2⟩, ?_⟩
  have hs4 : 1 ≤ s ^ 2 * α ^ 2 * δ ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_sq hs)
      (one_le_sq hα)) (one_le_sq hδ)
  have had2 : 1 ≤ α ^ 2 * δ ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_sq hα) (one_le_sq hδ)
  have hbg2 : 0 < β ^ 2 * γ ^ 2 := by positivity
  have hpq4 : p ^ 2 * e ^ 2 ≤ 4 * (p * q * e ^ 2) := by
    have h4 : 0 ≤ 4 * p * q - p ^ 2 := by nlinarith
    nlinarith [mul_nonneg h4 (sq_nonneg e)]
  have k1 : 4 * (p * q * e ^ 2) = 4 * (β ^ 2 * γ ^ 2) - 4 * (s ^ 2 * (s ^ 2 * α ^ 2 * δ ^ 2)) := by
    linear_combination -4 * G3
  have k2 : β ^ 2 * γ ^ 2 ≤ β ^ 2 * γ ^ 2 * (α ^ 2 * δ ^ 2) := le_mul_of_one_le_right hbg2.le had2
  have k3 : 0 < s ^ 2 * (s ^ 2 * α ^ 2 * δ ^ 2) := by positivity
  have e4 : (α * β * (γ * δ)) ^ 2 = β ^ 2 * γ ^ 2 * (α ^ 2 * δ ^ 2) := by ring
  rw [e4]
  linarith

/-- `λ = q`, `c₃ = q`, `c₄ = 1`, `σ = q s²`: the new solution is `(c₂ δ, α)`. -/
theorem classII_a {p q a s c1 c2 α β γ δ : ℤ} (hq : 0 < q) (hpc : p = c1 * c2) (hp : 0 < p)
    (ha : q ^ 2 - p ^ 2 = a ^ 2) (hs : s ≠ 0) (hc2 : c2 ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (E1 : q * q ^ 2 * γ ^ 2 - q * c1 ^ 2 * β ^ 2 = q * s ^ 2 * δ ^ 2)
    (E2 : q * 1 ^ 2 * β ^ 2 - q * c2 ^ 2 * γ ^ 2 = q * s ^ 2 * α ^ 2) :
    ∃ M e r t, IsSol p q M e r t ∧ p ^ 2 * e ^ 2 < 4 * (c1 * (α * β) * (c2 * (γ * δ))) ^ 2 := by
  have E1' : q ^ 2 * γ ^ 2 - c1 ^ 2 * β ^ 2 = s ^ 2 * δ ^ 2 :=
    mul_left_cancel₀ hq.ne' (by linear_combination E1)
  have E2' : β ^ 2 - c2 ^ 2 * γ ^ 2 = s ^ 2 * α ^ 2 :=
    mul_left_cancel₀ hq.ne' (by linear_combination E2)
  have K1 : s ^ 2 * ((c2 * δ) ^ 2 + p ^ 2 * α ^ 2) = (c2 * a * γ) ^ 2 := by
    linear_combination (-c2 ^ 2) * E1' + (-p ^ 2) * E2' + c2 ^ 2 * γ ^ 2 * ha +
      β ^ 2 * (p + c1 * c2) * hpc
  have K2 : s ^ 2 * ((c2 * δ) ^ 2 + q ^ 2 * α ^ 2) = (a * β) ^ 2 := by
    linear_combination (-c2 ^ 2) * E1' + (-q ^ 2) * E2' + β ^ 2 * ha +
      β ^ 2 * (p + c1 * c2) * hpc
  obtain ⟨r, hr⟩ : s ∣ c2 * a * γ := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨_, K1.symm⟩
  obtain ⟨t, ht⟩ : s ∣ a * β := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨_, K2.symm⟩
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  refine ⟨c2 * δ, α, r, t, ⟨mul_ne_zero hc2 hδ, hα, ?_, ?_⟩, ?_⟩
  · exact mul_left_cancel₀ hs2 (by rw [K1, hr]; ring)
  · exact mul_left_cancel₀ hs2 (by rw [K2, ht]; ring)
  · have hb := one_le_sq hβ
    have hg := one_le_sq hγ
    have hd := one_le_sq hδ
    have h1 : 1 ≤ β ^ 2 * γ ^ 2 * δ ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hb hg) hd
    have h2 : 0 < p ^ 2 * α ^ 2 := by positivity
    have e4 : (c1 * (α * β) * (c2 * (γ * δ))) ^ 2 = p ^ 2 * α ^ 2 * (β ^ 2 * γ ^ 2 * δ ^ 2) := by
      rw [hpc]; ring
    rw [e4]
    nlinarith

/-- `λ = q`, `c₃ = 1`, `c₄ = q`, `σ = q s²`: the new solution is `(c₁ α, δ)`. -/
theorem classII_b {p q a s c1 c2 α β γ δ : ℤ} (hq : 0 < q) (hpc : p = c1 * c2) (hp : 0 < p)
    (ha : q ^ 2 - p ^ 2 = a ^ 2) (hs : s ≠ 0) (hc1 : c1 ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (E1 : q * 1 ^ 2 * γ ^ 2 - q * c1 ^ 2 * β ^ 2 = q * s ^ 2 * δ ^ 2)
    (E2 : q * q ^ 2 * β ^ 2 - q * c2 ^ 2 * γ ^ 2 = q * s ^ 2 * α ^ 2) :
    ∃ M e r t, IsSol p q M e r t ∧ p ^ 2 * e ^ 2 < 4 * (c1 * (α * β) * (c2 * (γ * δ))) ^ 2 := by
  have E1' : γ ^ 2 - c1 ^ 2 * β ^ 2 = s ^ 2 * δ ^ 2 :=
    mul_left_cancel₀ hq.ne' (by linear_combination E1)
  have E2' : q ^ 2 * β ^ 2 - c2 ^ 2 * γ ^ 2 = s ^ 2 * α ^ 2 :=
    mul_left_cancel₀ hq.ne' (by linear_combination E2)
  have K1 : s ^ 2 * ((c1 * α) ^ 2 + p ^ 2 * δ ^ 2) = (c1 * a * β) ^ 2 := by
    linear_combination (-p ^ 2) * E1' + (-c1 ^ 2) * E2' + c1 ^ 2 * β ^ 2 * ha +
      γ ^ 2 * (p + c1 * c2) * hpc
  have K2 : s ^ 2 * ((c1 * α) ^ 2 + q ^ 2 * δ ^ 2) = (a * γ) ^ 2 := by
    linear_combination (-q ^ 2) * E1' + (-c1 ^ 2) * E2' + γ ^ 2 * ha +
      γ ^ 2 * (p + c1 * c2) * hpc
  obtain ⟨r, hr⟩ : s ∣ c1 * a * β := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨_, K1.symm⟩
  obtain ⟨t, ht⟩ : s ∣ a * γ := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨_, K2.symm⟩
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  refine ⟨c1 * α, δ, r, t, ⟨mul_ne_zero hc1 hα, hδ, ?_, ?_⟩, ?_⟩
  · exact mul_left_cancel₀ hs2 (by rw [K1, hr]; ring)
  · exact mul_left_cancel₀ hs2 (by rw [K2, ht]; ring)
  · have ha' := one_le_sq hα
    have hb := one_le_sq hβ
    have hg := one_le_sq hγ
    have h1 : 1 ≤ α ^ 2 * β ^ 2 * γ ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha' hb) hg
    have h2 : 0 < p ^ 2 * δ ^ 2 := by positivity
    have e4 : (c1 * (α * β) * (c2 * (γ * δ))) ^ 2 = p ^ 2 * δ ^ 2 * (α ^ 2 * β ^ 2 * γ ^ 2) := by
      rw [hpc]; ring
    rw [e4]
    nlinarith

/-! ### The descent -/

theorem natCast_div_gcd {p L : ℕ} : ((p / Nat.gcd p L : ℕ) : ℤ) * (Nat.gcd p L : ℕ) = p := by
  exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left p L)

theorem natCast_div_gcd' {p L : ℕ} : ((L / Nat.gcd p L : ℕ) : ℤ) * (Nat.gcd p L : ℕ) = L := by
  exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right p L)

/-- **One descent step.** Given the finite check for `(p, q)`, every solution gives a solution
with a smaller `|e|`. -/
theorem exists_smaller {p q a : ℕ} (hp : 0 < p) (hp2 : 2 ∣ p) (hpq : p < q)
    (ha : q ^ 2 = p ^ 2 + a ^ 2) (ha0 : 0 < a) (hcop : Nat.Coprime p q)
    (hcop' : Nat.Coprime (q - p) (q + p)) {mods : List (ℕ × ℕ)}
    (hchk : fiberCheck p q a mods = true) {M e r s : ℤ} (h : IsSol p q M e r s) :
    ∃ M' e' r' s', IsSol p q M' e' r' s' ∧ e' ^ 2 < e ^ 2 := by
  obtain ⟨p₀, hp₀⟩ := hp2
  have hpZ : (p : ℤ) = 2 * (p₀ : ℤ) := by exact_mod_cast hp₀
  have hpZ0 : (0 : ℤ) < p := by exact_mod_cast hp
  have hqZ0 : (0 : ℤ) < q := by exact_mod_cast hp.trans hpq
  have hpqZ : (p : ℤ) < q := by exact_mod_cast hpq
  have haZ : (q : ℤ) ^ 2 - p ^ 2 = a ^ 2 := by
    have : ((q ^ 2 : ℕ) : ℤ) = ((p ^ 2 + a ^ 2 : ℕ) : ℤ) := by rw [ha]
    push_cast at this
    linear_combination this
  obtain ⟨k1, k2, j1, j2, hk1, hk2, hj1, hj2, hk, hj, hne, hC, hbound⟩ :=
    exists_point hpZ (by omega) hqZ0 h
  obtain ⟨L, k1', k2', hL, hLd, hk1', hk2', hk', hne', hsq, h4, h5⟩ :=
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
  have hσNd : σN ∣ (L / Nat.gcd p L) ^ 2 * a ^ 2 := by
    rw [← hc34]
    have : ((σN : ℕ) : ℤ) ∣ (((c3 * c4) ^ 2 * a ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [mul_comm]
      exact hσd
    exact_mod_cast this
  -- the new solution is smaller
  have finish : ∀ M' e' r' s', IsSol p q M' e' r' s' →
      (p : ℤ) ^ 2 * e' ^ 2 < 4 * (c1 * (α * β) * (c2 * (γ * δ))) ^ 2 →
      ∃ M' e' r' s', IsSol p q M' e' r' s' ∧ e' ^ 2 < e ^ 2 := by
    intro M' e' r' s' hs hlt
    refine ⟨M', e', r', s', hs, ?_⟩
    have : (p : ℤ) ^ 2 * e' ^ 2 < p ^ 2 * e ^ 2 := by
      rw [hsq] at hlt
      linarith
    exact lt_of_mul_lt_mul_left this (by positivity)
  rcases fiberCheck_spec hchk hp (hp.trans hpq) ha0 hL (by exact_mod_cast hLd) hc12 hc12' hc34
    hc34' hσNd with hI | hII | hT
  · -- λ = p
    simp only [classI, Bool.and_eq_true, beq_iff_eq] at hI
    obtain ⟨⟨⟨⟨⟨⟨hLp, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hmod⟩, hsq'⟩ := hI
    subst L
    set s := Nat.sqrt (σN / (q - p))
    have hσs : σN = (q - p) * s ^ 2 := by
      rw [← eq_sq_of_isSq hsq', Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)]
    have hσs' : (σN : ℤ) = ((q : ℤ) - p) * (s : ℤ) ^ 2 := by
      rw [hσs]; push_cast [Nat.cast_sub hpq.le]; ring
    have hs : (s : ℤ) ≠ 0 := by
      rintro h0
      have : (σN : ℤ) = 0 := by rw [hσs', h0]; ring
      omega
    have hcopZ : IsCoprime ((q : ℤ) - p) (q + p) := by
      have := Nat.isCoprime_iff_coprime.mpr hcop'
      push_cast [Nat.cast_sub hpq.le] at this
      exact this
    obtain ⟨M', e', r', s', hs', hlt⟩ := classI_step hpZ0 hpqZ hcopZ hs hα hβ hγ hδ hbg
      (by simpa using hne') (by rw [← hσs']; push_cast at E1; linear_combination E1)
      (by rw [← hσs']; push_cast at E2; linear_combination E2)
    exact finish M' e' r' s' hs' (by simpa using hlt)
  · -- λ = q
    simp only [classII, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hII
    obtain ⟨⟨⟨hLq, hc⟩, hmod⟩, hsq'⟩ := hII
    subst L
    set s := Nat.sqrt (σN / q)
    have hσs : (σN : ℤ) = q * (s : ℤ) ^ 2 := by
      have : σN = q * s ^ 2 := by
        rw [← eq_sq_of_isSq hsq', Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)]
      rw [this]; push_cast; ring
    have hs : (s : ℤ) ≠ 0 := by
      rintro h0
      have : (σN : ℤ) = 0 := by rw [hσs, h0]; ring
      omega
    have hpc : (p : ℤ) = c1 * c2 := by
      have : c1 * c2 = p := by rw [hc12, hcop.gcd_eq_one, Nat.div_one]
      exact_mod_cast this.symm
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨M', e', r', s', hs', hlt⟩ := classII_a hqZ0 hpc hpZ0 haZ hs hc2 hα hβ hγ hδ
        (by rw [← hσs]; exact_mod_cast E1) (by rw [← hσs]; exact_mod_cast E2)
      exact finish M' e' r' s' hs' hlt
    · obtain ⟨M', e', r', s', hs', hlt⟩ := classII_b hqZ0 hpc hpZ0 haZ hs hc1 hα hβ hγ hδ
        (by rw [← hσs]; exact_mod_cast E1) (by rw [← hσs]; exact_mod_cast E2)
      exact finish M' e' r' s' hs' hlt
  · exact (tupleOK_sound (fiberCheck_mods hchk) hT hσN hab hag had hbg hbd hgd h1g h1d h2a h2b
      h3b h3d h4a h4g E1 E2).elim

/-- **The descent.** If `fiberCheck p q a mods` succeeds, there are no integers `M, e ≠ 0` with
`M² + p² e²` and `M² + q² e²` both squares. -/
theorem not_isSol {p q a : ℕ} (hp : 0 < p) (hp2 : 2 ∣ p) (hpq : p < q)
    (ha : q ^ 2 = p ^ 2 + a ^ 2) (ha0 : 0 < a) (hcop : Nat.Coprime p q)
    (hcop' : Nat.Coprime (q - p) (q + p)) {mods : List (ℕ × ℕ)}
    (hchk : fiberCheck p q a mods = true) (M e r s : ℤ) : ¬ IsSol p q M e r s := by
  suffices ∀ n : ℕ, ∀ M e r s : ℤ, e.natAbs = n → ¬ IsSol p q M e r s from this _ M e r s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M e r s hn h
    obtain ⟨M', e', r', s', h', hlt⟩ := exists_smaller hp hp2 hpq ha ha0 hcop hcop' hchk h
    exact ih _ (hn ▸ Int.natAbs_lt_iff_sq_lt.mpr hlt) M' e' r' s' rfl h'

/-- The descent over `ℚ`: for rational `t ≠ 0`, `t² + p²` and `t² + q²` are not both squares. -/
theorem not_isSquare_sq_add_sq_and_sq_add_sq {p q a : ℕ} (hp : 0 < p) (hp2 : 2 ∣ p)
    (hpq : p < q) (ha : q ^ 2 = p ^ 2 + a ^ 2) (ha0 : 0 < a) (hcop : Nat.Coprime p q)
    (hcop' : Nat.Coprime (q - p) (q + p)) {mods : List (ℕ × ℕ)}
    (hchk : fiberCheck p q a mods = true) {t : ℚ} (ht : t ≠ 0) :
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
  exact not_isSol hp hp2 hpq ha ha0 hcop hcop' hchk t.num t.den r s
    ⟨Rat.num_ne_zero.mpr ht, by exact_mod_cast t.den_nz, by rw [hr]; ring, by rw [hs]; ring⟩

end Descent

end PerfectCuboid
