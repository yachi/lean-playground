module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

/-!
# Redefining points on the real line: `1/n → 1`

Claims from a Gemini conversation ("Concrete Example: Redefining Points on the Real Line",
2026-11-06).

Let `d₁(x, y) = |x - y|` be the usual metric on `ℝ` and let `φ : ℝ → ℝ` swap `0` and `1`:
`φ 0 = 1`, `φ 1 = 0`, `φ x = x` otherwise. Define `d₂(x, y) = |φ x - φ y|`.

* `φ` is the transposition `Equiv.swap 0 1`, an involution, hence a bijection.
* `d₂` is a metric on `ℝ` (we put it on the type synonym `SwappedReal`).
* **Main claim.** Under `d₂`, the sequence `xₙ = 1/n` converges to `1`.
* It does not converge to `0` under `d₂` (limits in a metric space are unique), and `1` is its
  only `d₂`-limit.
* "Ping Lam's form": `xₙ → L` under `d₂` iff `|φ xₙ - φ L| → 0`. Gemini's later remark that the
  chart's shorthand "`φ xₙ → 0 = φ 1`" is not rigorous is too harsh: since `φ` is an isometry
  `(ℝ, d₂) → (ℝ, d₁)`, the chart's statement is *equivalent* to `xₙ → 1` under `d₂`.
* `φ` is an isometric equivalence `(ℝ, d₂) ≃ (ℝ, d₁)`, so the two spaces are "the same space
  with the labels `0` and `1` swapped"; yet the identity map `(ℝ, d₁) → (ℝ, d₂)` is not
  continuous (at `0`).
-/

open Filter Topology

namespace SwappedMetric

/-! ## The bijection `φ` -/

/-- The map `φ` from the picture: swap `0` and `1`, fix everything else. -/
noncomputable def phi (x : ℝ) : ℝ :=
  if x = 0 then 1 else if x = 1 then 0 else x

@[simp] theorem phi_zero : phi 0 = 1 := by simp [phi]

@[simp] theorem phi_one : phi 1 = 0 := by simp [phi]

theorem phi_of_ne {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) : phi x = x := by
  simp [phi, h0, h1]

/-- `φ` is the transposition of `0` and `1`. -/
theorem phi_eq_swap : phi = ⇑(Equiv.swap (0 : ℝ) 1) := by
  funext x
  rw [Equiv.swap_apply_def]
  rfl

theorem phi_involutive : Function.Involutive phi := by
  rw [phi_eq_swap]
  exact Equiv.swap_apply_self 0 1

theorem phi_bijective : Function.Bijective phi := phi_involutive.bijective

theorem phi_injective : Function.Injective phi := phi_involutive.injective

/-- For `n ≥ 2`, `φ (1/n) = 1/n` (the "otherwise" case). -/
theorem phi_inv_nat {n : ℕ} (hn : 2 ≤ n) : phi (1 / n) = 1 / n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hgt : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  apply phi_of_ne
  · positivity
  · rw [one_div, Ne, inv_eq_one]
    exact hgt.ne'

/-! ## The metric `d₂` -/

/-- `ℝ` with the metric `d₂(x, y) = |φ x - φ y|`. -/
def SwappedReal : Type := ℝ

/-- The identity map `ℝ → SwappedReal` (same points, new metric). -/
def toSwapped : ℝ ≃ SwappedReal := Equiv.refl ℝ

/-- `d₂` is a metric: it is the metric induced by the injective map `φ`. -/
noncomputable instance : MetricSpace SwappedReal :=
  MetricSpace.induced (phi ∘ toSwapped.symm) (phi_injective.comp toSwapped.symm.injective)
    inferInstance

/-- The defining formula `d₂(x, y) = |φ x - φ y|`. -/
theorem dist_toSwapped (x y : ℝ) : dist (toSwapped x) (toSwapped y) = |phi x - phi y| :=
  Real.dist_eq _ _

/-- `d₂` written as a function `ℝ → ℝ → ℝ`. -/
noncomputable def d₂ (x y : ℝ) : ℝ := |phi x - phi y|

theorem d₂_eq_dist (x y : ℝ) : d₂ x y = dist (toSwapped x) (toSwapped y) :=
  (dist_toSwapped x y).symm

/-- The metric axioms for `d₂`, spelled out. -/
theorem d₂_isMetric :
    (∀ x y, d₂ x y = 0 ↔ x = y) ∧ (∀ x y, d₂ x y = d₂ y x) ∧
      (∀ x y z, d₂ x z ≤ d₂ x y + d₂ y z) := by
  simp only [d₂_eq_dist]
  refine ⟨fun x y => ?_, fun x y => dist_comm _ _, fun x y z => dist_triangle _ _ _⟩
  rw [dist_eq_zero]
  exact toSwapped.injective.eq_iff

/-- `d₂(0, 1) = 1`, while `d₂(1/n, 1) = 1/n` and `d₂(1/n, 0) = 1 - 1/n` for `n ≥ 2`. -/
theorem d₂_values {n : ℕ} (hn : 2 ≤ n) :
    d₂ 0 1 = 1 ∧ d₂ (1 / n) 1 = 1 / n ∧ d₂ (1 / n) 0 = 1 - 1 / n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hle : (1 : ℝ) / n ≤ 1 := by
    rw [div_le_one hpos]; exact_mod_cast (by omega : 1 ≤ n)
  refine ⟨by simp [d₂], ?_, ?_⟩
  · simp only [d₂, phi_inv_nat hn, phi_one, sub_zero]
    exact abs_of_nonneg (by positivity)
  · simp only [d₂, phi_inv_nat hn, phi_zero]
    rw [abs_sub_comm]
    exact abs_of_nonneg (by linarith)

/-! ## `φ` is an isometry `(ℝ, d₂) ≃ (ℝ, d₁)` -/

/-- `φ`, viewed as a map `(ℝ, d₂) → (ℝ, d₁)`, is a bijective isometry. -/
noncomputable def phiIsometry : SwappedReal ≃ᵢ ℝ where
  toEquiv := toSwapped.symm.trans (Equiv.swap (0 : ℝ) 1)
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    change dist (Equiv.swap (0 : ℝ) 1 (toSwapped.symm x)) (Equiv.swap (0 : ℝ) 1 (toSwapped.symm y))
      = _
    rw [← phi_eq_swap]
    rfl

@[simp] theorem phiIsometry_apply (x : ℝ) : phiIsometry (toSwapped x) = phi x := by
  change Equiv.swap (0 : ℝ) 1 x = phi x
  rw [phi_eq_swap]

/-! ## Convergence under `d₂` -/

/-- Convergence under `d₂` is the same as convergence of `φ xₙ` to `φ L` in the usual sense.
So the chart's "`φ xₙ → 0 = φ 1`" is a correct proof that `xₙ → 1` under `d₂`. -/
theorem tendsto_toSwapped_iff (x : ℕ → ℝ) (L : ℝ) :
    Tendsto (fun n => toSwapped (x n)) atTop (𝓝 (toSwapped L)) ↔
      Tendsto (fun n => phi (x n)) atTop (𝓝 (phi L)) := by
  have h := phiIsometry.toHomeomorph.isEmbedding.tendsto_nhds_iff
    (f := fun n => toSwapped (x n)) (y := toSwapped L) (l := atTop)
  simpa [Function.comp_def] using h

/-- Ping Lam's form: `xₙ → L` under `d₂` iff `d₂(xₙ, L) = |φ xₙ - φ L| → 0`. -/
theorem tendsto_toSwapped_iff_d₂ (x : ℕ → ℝ) (L : ℝ) :
    Tendsto (fun n => toSwapped (x n)) atTop (𝓝 (toSwapped L)) ↔
      Tendsto (fun n => |phi (x n) - phi L|) atTop (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_toSwapped]

/-- `φ (1/n) → 0 = φ 1` in the usual metric. -/
theorem tendsto_phi_inv_nat :
    Tendsto (fun n : ℕ => phi (1 / n)) atTop (𝓝 (phi 1)) := by
  rw [phi_one]
  refine (tendsto_one_div_atTop_nhds_zero_nat).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (phi_inv_nat hn).symm

/-- **Main claim.** Under `d₂`, the sequence `xₙ = 1/n` converges to `1`. -/
theorem tendsto_one_div_nat_one :
    Tendsto (fun n : ℕ => toSwapped (1 / n)) atTop (𝓝 (toSwapped 1)) :=
  (tendsto_toSwapped_iff _ _).2 tendsto_phi_inv_nat

/-- The same, in the ε-N form: for every `ε > 0` there is `N` with `d₂(1/n, 1) < ε`
for all `n ≥ N`. -/
theorem d₂_one_div_nat_one_lt :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, d₂ (1 / n) 1 < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 tendsto_one_div_nat_one ε hε
  exact ⟨N, fun n hn => by rw [d₂_eq_dist]; exact hN n hn⟩

/-- `1` is the only `d₂`-limit of `1/n`: if `1/n → L` under `d₂` then `L = 1`
(Gemini's argument: `φ L` must be `0`, and only `φ 1 = 0`). -/
theorem limit_eq_one {L : ℝ}
    (h : Tendsto (fun n : ℕ => toSwapped (1 / n)) atTop (𝓝 (toSwapped L))) : L = 1 :=
  toSwapped.injective (tendsto_nhds_unique h tendsto_one_div_nat_one)

/-- Under `d₂`, `1/n` does **not** converge to `0` (its usual limit). -/
theorem not_tendsto_one_div_nat_zero :
    ¬ Tendsto (fun n : ℕ => toSwapped (1 / n)) atTop (𝓝 (toSwapped 0)) := fun h =>
  zero_ne_one (limit_eq_one h)

/-- The identity map `(ℝ, d₁) → (ℝ, d₂)` is not continuous: it is discontinuous at `0`. -/
theorem not_continuous_toSwapped : ¬ Continuous toSwapped := fun h =>
  not_tendsto_one_div_nat_zero
    ((h.tendsto 0).comp (tendsto_one_div_atTop_nhds_zero_nat))

end SwappedMetric
