module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

/-!
# Continuity at an isolated point

Claims from a Gemini conversation ("Continuity at an Isolated Point", 2026-11-04).

* ε-δ form: if no other point lies within `δ₀ > 0` of `p`, every `f` is continuous at `p`
  (take `δ = δ₀`; the only `x` with `dist x p < δ₀` is `p`, and `dist (f p) (f p) = 0 < ε`).
* Topological form: if `{p}` is open, every `f` is continuous at `p`. Relative to a subset `A`,
  if `p` is an isolated point of `A` then every `f` is continuous at `p` within `A`.
* No sequence of points other than `p` converges to an isolated point `p`.
* Convergence and continuity in a metric space: the ε-ball, open-set and sequence versions agree.
* Preimages commute with unions, intersections and complements.
* The four kinds of points of a set `A`: interior, accumulation, isolated, boundary.
* Discrete topology: every function is continuous; a sequence converges iff it is eventually
  constant.
* Indiscrete topology: every sequence converges to every point, and the space is connected.
-/

open Filter Topology Set

namespace IsolatedPoint

/-! ## ε-δ form -/

section Metric

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- Gemini's step-by-step proof: at an isolated point `p` (no other point within `δ₀`),
every function satisfies the ε-δ definition of continuity, with `δ = δ₀`. -/
theorem epsilon_delta_of_isolated (f : X → Y) {p : X} {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hiso : ∀ x, dist x p < δ₀ → x = p) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, dist x p < δ → dist (f x) (f p) < ε := by
  intro ε hε
  refine ⟨δ₀, hδ₀, fun x hx => ?_⟩
  rw [hiso x hx, dist_self]
  exact hε

/-- The same statement as `ContinuousAt`. -/
theorem continuousAt_of_isolated (f : X → Y) {p : X} {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hiso : ∀ x, dist x p < δ₀ → x = p) : ContinuousAt f p :=
  Metric.continuousAt_iff.2 (epsilon_delta_of_isolated f hδ₀ hiso)

/-- "Isolated" in the ε-ball sense means `{p}` is open: `B_{δ₀}(p) = {p}`. -/
theorem ball_eq_singleton_of_isolated {p : X} {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hiso : ∀ x, dist x p < δ₀ → x = p) : Metric.ball p δ₀ = {p} := by
  ext x
  simp only [Metric.mem_ball, mem_singleton_iff]
  exact ⟨hiso x, fun h => by rw [h, dist_self]; exact hδ₀⟩

/-- Metric convergence: `xₙ → p` iff the terms eventually stay in every ε-ball around `p`. -/
theorem tendsto_iff_eventually_ball (x : ℕ → X) (p : X) :
    Tendsto x atTop (𝓝 p) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (x n) p < ε :=
  Metric.tendsto_atTop

/-- In a metric space, continuity is the same as sequential continuity:
`f` is continuous iff `xₙ → p` implies `f xₙ → f p`. -/
theorem continuous_iff_sequential (f : X → Y) :
    Continuous f ↔ ∀ (x : ℕ → X) (p : X), Tendsto x atTop (𝓝 p) →
      Tendsto (f ∘ x) atTop (𝓝 (f p)) := by
  rw [continuous_iff_seqContinuous]
  exact ⟨fun h x p hx => h hx, fun h x p hx => h x p hx⟩

/-- ε-δ continuity everywhere is the same as "preimages of open sets are open". -/
theorem epsilon_delta_iff_preimage_open (f : X → Y) :
    (∀ p, ∀ ε > 0, ∃ δ > 0, ∀ x, dist x p < δ → dist (f x) (f p) < ε) ↔
      ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  rw [← continuous_def, continuous_iff_continuousAt]
  exact forall_congr' fun p => Metric.continuousAt_iff.symm

end Metric

/-! ## Topological form -/

section Topological

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- If `{p}` is open (`p` is an isolated point of the space), every function is continuous
at `p`: any open set around `f p` pulls back to an open set containing `{p}`. -/
theorem continuousAt_of_isOpen_singleton (f : X → Y) {p : X} (hp : IsOpen ({p} : Set X)) :
    ContinuousAt f p := by
  rw [ContinuousAt, (isOpen_singleton_iff_nhds_eq_pure p).1 hp]
  exact tendsto_pure_nhds f p

/-- `p` is an isolated point of the space iff its only neighbourhood filter is `pure p`,
i.e. iff the punctured neighbourhoods of `p` are trivial. -/
theorem isOpen_singleton_iff_nhdsNE_eq_bot {p : X} :
    IsOpen ({p} : Set X) ↔ 𝓝[≠] p = ⊥ :=
  isOpen_singleton_iff_punctured_nhds p

/-- Relative version: if `p ∈ A` has a neighbourhood meeting `A` only at `p` (an isolated
point of `A`), every function is continuous at `p` within `A`. -/
theorem continuousWithinAt_of_isolated (f : X → Y) {A : Set X} {p : X} {U : Set X}
    (hU : U ∈ 𝓝 p) (hiso : U ∩ A ⊆ {p}) : ContinuousWithinAt f A p := by
  intro V hV
  rw [mem_map]
  refine mem_of_superset (inter_mem_nhdsWithin A hU) fun x hx => ?_
  rw [inter_comm] at hx
  change f x ∈ V
  rw [mem_singleton_iff.1 (hiso hx)]
  exact mem_of_mem_nhds hV

/-- Every function on `A` is continuous at an isolated point of `A`, in the subspace
topology of `A`. -/
theorem continuousAt_subtype_of_isolated {A : Set X} (f : A → Y) {p : A} {U : Set X}
    (hU : U ∈ 𝓝 (p : X)) (hiso : U ∩ A ⊆ {(p : X)}) : ContinuousAt f p := by
  refine continuousAt_of_isOpen_singleton f ?_
  obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.1 hU
  refine ⟨V, hV, ?_⟩
  ext ⟨x, hx⟩
  simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff]
  exact ⟨fun h => mem_singleton_iff.1 (hiso ⟨hVU h, hx⟩), fun h => h ▸ hpV⟩

/-- No sequence of points other than `p` converges to an isolated point `p`:
there is no way to approach `p` from outside. -/
theorem not_tendsto_of_isolated {p : X} (hp : IsOpen ({p} : Set X)) (x : ℕ → X)
    (hx : ∀ n, x n ≠ p) : ¬ Tendsto x atTop (𝓝 p) := by
  intro h
  have h' := h (hp.mem_nhds rfl)
  rw [mem_map, mem_atTop_sets] at h'
  obtain ⟨N, hN⟩ := h'
  exact hx N (hN N le_rfl)

/-- Topological convergence: `xₙ → p` iff `xₙ` is eventually in every open set containing `p`. -/
theorem tendsto_iff_eventually_open (x : ℕ → X) (p : X) :
    Tendsto x atTop (𝓝 p) ↔ ∀ U : Set X, IsOpen U → p ∈ U → ∃ N, ∀ n ≥ N, x n ∈ U := by
  rw [tendsto_nhds]
  exact forall_congr' fun U => forall_congr' fun _ => forall_congr' fun _ => eventually_atTop

/-! ### Strategy A: preimages commute with set operations -/

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem preimage_set_ops (f : X → Y) (U V : Set Y) :
    f ⁻¹' (U ∪ V) = f ⁻¹' U ∪ f ⁻¹' V ∧ f ⁻¹' (U ∩ V) = f ⁻¹' U ∩ f ⁻¹' V ∧
      f ⁻¹' Uᶜ = (f ⁻¹' U)ᶜ :=
  ⟨preimage_union, preimage_inter, preimage_compl⟩

/-! ### Strategy B: classifying the points of a set by their neighbourhoods -/

variable (A : Set X) (p : X)

/-- Interior point: some neighbourhood of `p` lies inside `A`. -/
theorem interior_point_iff : p ∈ interior A ↔ ∃ U ∈ 𝓝 p, U ⊆ A :=
  mem_interior_iff_mem_nhds.trans ⟨fun h => ⟨A, h, subset_rfl⟩,
    fun ⟨_, hU, hUA⟩ => mem_of_superset hU hUA⟩

/-- Accumulation point: every neighbourhood of `p` contains a point of `A` other than `p`. -/
theorem accPt_iff : AccPt p (𝓟 A) ↔ ∀ U ∈ 𝓝 p, ∃ y ∈ U, y ≠ p ∧ y ∈ A := by
  rw [accPt_iff_nhds]
  exact forall₂_congr fun U _ =>
    ⟨fun ⟨y, ⟨hyU, hyA⟩, hne⟩ => ⟨y, hyU, hne, hyA⟩,
      fun ⟨y, hyU, hne, hyA⟩ => ⟨y, ⟨hyU, hyA⟩, hne⟩⟩

/-- Isolated point of `A` (a point of `A` that is not an accumulation point of `A`): some
neighbourhood of `p` meets `A` only at `p`. -/
theorem isolated_iff : ¬ AccPt p (𝓟 A) ↔ ∃ U ∈ 𝓝 p, U ∩ A ⊆ {p} := by
  rw [accPt_iff]
  constructor
  · intro h
    by_contra hc
    refine h fun U hU => ?_
    obtain ⟨y, ⟨hyU, hyA⟩, hne⟩ := not_subset.1 (fun hs => hc ⟨U, hU, hs⟩)
    exact ⟨y, hyU, hne, hyA⟩
  · rintro ⟨U, hU, hs⟩ h
    obtain ⟨y, hyU, hne, hyA⟩ := h U hU
    exact hne (mem_singleton_iff.1 (hs ⟨hyU, hyA⟩))

/-- Boundary point: every neighbourhood of `p` meets both `A` and `Aᶜ`. -/
theorem boundary_point_iff :
    p ∈ frontier A ↔ ∀ U ∈ 𝓝 p, (U ∩ A).Nonempty ∧ (U ∩ Aᶜ).Nonempty := by
  rw [frontier_eq_closure_inter_closure, mem_inter_iff, mem_closure_iff_nhds,
    mem_closure_iff_nhds]
  exact ⟨fun ⟨h₁, h₂⟩ U hU => ⟨h₁ U hU, h₂ U hU⟩,
    fun h => ⟨fun U hU => (h U hU).1, fun U hU => (h U hU).2⟩⟩

end Topological

/-! ## Strategy C: discrete and indiscrete topologies -/

section Discrete

variable {X Y : Type*} [TopologicalSpace X] [DiscreteTopology X] [TopologicalSpace Y]

/-- In the discrete topology every point is isolated. -/
theorem isOpen_singleton_discrete (p : X) : IsOpen ({p} : Set X) := isOpen_discrete _

/-- In the discrete topology every function is continuous. -/
theorem continuous_discrete (f : X → Y) : Continuous f := continuous_of_discreteTopology

/-- In the discrete topology a sequence converges iff it is eventually constant. -/
theorem tendsto_discrete_iff (x : ℕ → X) (p : X) :
    Tendsto x atTop (𝓝 p) ↔ ∃ N, ∀ n ≥ N, x n = p := by
  rw [nhds_discrete, tendsto_pure, eventually_atTop]

end Discrete

section Indiscrete

variable {X : Type*} [TopologicalSpace X]

/-- In an indiscrete space (only `∅` and `X` are open) every sequence converges to every
point. -/
theorem tendsto_indiscrete (h : ∀ U : Set X, IsOpen U → U = ∅ ∨ U = univ) (x : ℕ → X)
    (p : X) : Tendsto x atTop (𝓝 p) := by
  rw [tendsto_nhds]
  intro U hU hpU
  rcases h U hU with rfl | rfl
  · exact absurd hpU (notMem_empty p)
  · exact univ_mem

/-- An indiscrete space is connected. -/
theorem preconnectedSpace_indiscrete (h : ∀ U : Set X, IsOpen U → U = ∅ ∨ U = univ) :
    PreconnectedSpace X := by
  refine ⟨fun U V hU hV _ ⟨u, _, hu⟩ ⟨v, _, hv⟩ => ?_⟩
  rcases h U hU with rfl | rfl
  · exact absurd hu (notMem_empty u)
  rcases h V hV with rfl | rfl
  · exact absurd hv (notMem_empty v)
  exact ⟨u, trivial, trivial, trivial⟩

omit [TopologicalSpace X] in
/-- Mathlib's indiscrete topology `⊤` has exactly `∅` and `univ` as open sets. -/
theorem isOpen_top_iff' (U : Set X) : IsOpen[⊤] U ↔ U = ∅ ∨ U = univ :=
  TopologicalSpace.isOpen_top_iff U

end Indiscrete

end IsolatedPoint
