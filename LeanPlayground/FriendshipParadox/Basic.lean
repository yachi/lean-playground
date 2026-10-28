module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The friendship paradox

Scott L. Feld, *Why your friends have more friends than you do*, American Journal of Sociology
96 (1991), 1464–1477. In a finite simple graph `G` on `n` vertices with degrees `d v`:

* **Feld's form** (`SimpleGraph.friendship_paradox`). Pick a person and then one of their friends,
  uniformly among all (person, friend) pairs. The friend's expected number of friends is
  `∑ d v ^ 2 / ∑ d v`, which is at least the average degree `∑ d v / n`. Equality holds iff all
  degrees are equal (`SimpleGraph.friendship_paradox_eq_iff`).
* **Per-person form** (`SimpleGraph.friendship_paradox_local`). Summed over all people, the
  average number of friends of one's friends is at least one's own number of friends:
  `∑ d v ≤ ∑ (∑_{u ~ v} d u) / d v`. Isolated people add `0` to both sides. Equality holds iff
  `d` is constant on every connected component
  (`SimpleGraph.friendship_paradox_local_eq_iff_reachable`).

`friendDegreeSum G v = ∑_{u ~ v} d u` is the total number of friends of `v`'s friends.
Each `u` is counted `d u` times over all `v` (`SimpleGraph.sum_friendDegreeSum`), so the mean
over (person, friend) pairs is `∑ d v ^ 2 / ∑ d v`. Both inequalities come from sums of squares:
`∑_u ∑_v (d u - d v) ^ 2 = 2 (n ∑ d v ^ 2 - (∑ d v) ^ 2)` and, pairing each friendship with its
reverse, `2 (∑_v (∑_{u ~ v} d u) / d v - ∑ d v) = ∑_{u ~ v} (d u - d v) ^ 2 / (d u d v)`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The total number of friends of `v`'s friends, `∑_{u ~ v} d u`. -/
def friendDegreeSum (v : V) : ℕ := ∑ u ∈ G.neighborFinset v, G.degree u

/-- Summing over ordered pairs of adjacent vertices is symmetric. -/
lemma sum_neighbor_swap {M : Type*} [AddCommMonoid M] (f : V → V → M) :
    ∑ v, ∑ u ∈ G.neighborFinset v, f v u = ∑ v, ∑ u ∈ G.neighborFinset v, f u v := by
  simp_rw [neighborFinset_eq_filter, sum_filter]
  rw [sum_comm]
  simp_rw [G.adj_comm]

/-- Each vertex `u` is a friend `d u` times, so the friend-degree sum is `∑ d v ^ 2`. -/
lemma sum_friendDegreeSum : ∑ v, G.friendDegreeSum v = ∑ v, G.degree v ^ 2 := by
  unfold friendDegreeSum
  rw [G.sum_neighbor_swap (fun _ u ↦ G.degree u)]
  simp [sq, card_neighborFinset_eq_degree]

lemma sum_friendDegreeSum_rat :
    ∑ v, (G.friendDegreeSum v : ℚ) = ∑ v, (G.degree v : ℚ) ^ 2 := by
  have := congrArg (Nat.cast : ℕ → ℚ) G.sum_friendDegreeSum
  push_cast at this
  exact this

lemma sum_sum_sub_sq :
    ∑ u, ∑ v, ((G.degree u : ℚ) - G.degree v) ^ 2 =
      2 * (Fintype.card V * ∑ v, (G.degree v : ℚ) ^ 2 - (∑ v, (G.degree v : ℚ)) ^ 2) := by
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
    ← mul_sum]
  rw [← sum_mul, ← mul_sum]
  ring

lemma card_pos_of_sum_degree_pos (hS : 0 < ∑ v, (G.degree v : ℚ)) :
    (0 : ℚ) < Fintype.card V := by
  obtain ⟨v, -, -⟩ := exists_ne_zero_of_sum_ne_zero hS.ne'
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨v⟩

/-- **The friendship paradox** (Feld 1991): the mean degree of a random friend,
`∑ d v ^ 2 / ∑ d v`, is at least the mean degree `∑ d v / n`. -/
theorem friendship_paradox :
    (∑ v, (G.degree v : ℚ)) / Fintype.card V ≤
      (∑ v, (G.friendDegreeSum v : ℚ)) / ∑ v, (G.degree v : ℚ) := by
  rw [G.sum_friendDegreeSum_rat]
  rcases (sum_nonneg fun v _ ↦ (G.degree v).cast_nonneg (α := ℚ)).eq_or_lt with hS | hS
  · rw [← hS]
    simp
  rw [div_le_div_iff₀ (G.card_pos_of_sum_degree_pos hS) hS]
  have := G.sum_sum_sub_sq
  have : 0 ≤ ∑ u, ∑ v, ((G.degree u : ℚ) - G.degree v) ^ 2 := by positivity
  nlinarith

/-- Equality in the friendship paradox holds iff all degrees are equal. -/
theorem friendship_paradox_eq_iff :
    (∑ v, (G.degree v : ℚ)) / Fintype.card V =
        (∑ v, (G.friendDegreeSum v : ℚ)) / ∑ v, (G.degree v : ℚ) ↔
      ∀ u v, G.degree u = G.degree v := by
  rw [G.sum_friendDegreeSum_rat]
  rcases (sum_nonneg fun v _ ↦ (G.degree v).cast_nonneg (α := ℚ)).eq_or_lt with hS | hS
  · have h0 : ∀ v, G.degree v = 0 := by
      intro v
      have := (sum_eq_zero_iff_of_nonneg fun v _ ↦ (G.degree v).cast_nonneg (α := ℚ)).mp
        hS.symm v (mem_univ v)
      exact_mod_cast this
    simp [h0]
  have hn := G.card_pos_of_sum_degree_pos hS
  rw [div_eq_div_iff hn.ne' hS.ne']
  have key := G.sum_sum_sub_sq
  have hzero : ∑ u, ∑ v, ((G.degree u : ℚ) - G.degree v) ^ 2 = 0 ↔
      ∀ u v, G.degree u = G.degree v := by
    rw [sum_eq_zero_iff_of_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _]
    simp_rw [sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _]
    simp [sub_eq_zero]
  rw [← hzero, key]
  constructor <;> intro h <;> linarith

lemma two_mul_sum_friendDegreeSum_div_sub :
    2 * (∑ v, (G.friendDegreeSum v : ℚ) / G.degree v - ∑ v, (G.degree v : ℚ)) =
      ∑ v, ∑ u ∈ G.neighborFinset v,
        ((G.degree u : ℚ) - G.degree v) ^ 2 / (G.degree u * G.degree v) := by
  have hterm : ∀ v, ∀ u ∈ G.neighborFinset v,
      ((G.degree u : ℚ) - G.degree v) ^ 2 / (G.degree u * G.degree v) =
        (G.degree u : ℚ) / G.degree v + (G.degree v : ℚ) / G.degree u - 2 := by
    intro v u hu
    rw [mem_neighborFinset] at hu
    have hv : (0 : ℚ) < G.degree v := by exact_mod_cast G.degree_pos_iff_exists_adj v |>.mpr ⟨u, hu⟩
    have hu' : (0 : ℚ) < G.degree u := by
      exact_mod_cast G.degree_pos_iff_exists_adj u |>.mpr ⟨v, hu.symm⟩
    field_simp
    ring
  rw [sum_congr rfl fun v _ ↦ sum_congr rfl (hterm v)]
  simp only [sum_sub_distrib, sum_add_distrib]
  rw [G.sum_neighbor_swap (fun v u ↦ (G.degree v : ℚ) / G.degree u)]
  simp only [friendDegreeSum, Nat.cast_sum, div_eq_mul_inv, sum_mul, sum_const,
    card_neighborFinset_eq_degree, nsmul_eq_mul]
  rw [← sum_mul]
  ring

/-- **The friendship paradox, per person**: summed over people, the average degree of one's
friends is at least one's own degree. -/
theorem friendship_paradox_local :
    ∑ v, (G.degree v : ℚ) ≤ ∑ v, (G.friendDegreeSum v : ℚ) / G.degree v := by
  have := G.two_mul_sum_friendDegreeSum_div_sub
  have : 0 ≤ ∑ v, ∑ u ∈ G.neighborFinset v,
      ((G.degree u : ℚ) - G.degree v) ^ 2 / (G.degree u * G.degree v) := by positivity
  linarith

/-- Equality in the per-person form holds iff adjacent vertices have equal degree. -/
theorem friendship_paradox_local_eq_iff :
    ∑ v, (G.degree v : ℚ) = ∑ v, (G.friendDegreeSum v : ℚ) / G.degree v ↔
      ∀ u v, G.Adj u v → G.degree u = G.degree v := by
  have key := G.two_mul_sum_friendDegreeSum_div_sub
  have hnn : ∀ v, ∀ u ∈ G.neighborFinset v,
      0 ≤ ((G.degree u : ℚ) - G.degree v) ^ 2 / (G.degree u * G.degree v) :=
    fun _ _ _ ↦ by positivity
  have hzero : ∑ v, ∑ u ∈ G.neighborFinset v,
      ((G.degree u : ℚ) - G.degree v) ^ 2 / (G.degree u * G.degree v) = 0 ↔
      ∀ u v, G.Adj u v → G.degree u = G.degree v := by
    constructor
    · intro h u v huv
      have hu : (0 : ℚ) < G.degree u := by
        exact_mod_cast G.degree_pos_iff_exists_adj u |>.mpr ⟨v, huv⟩
      have hv : (0 : ℚ) < G.degree v := by
        exact_mod_cast G.degree_pos_iff_exists_adj v |>.mpr ⟨u, huv.symm⟩
      have h1 := (sum_eq_zero_iff_of_nonneg fun v _ ↦ sum_nonneg (hnn v)).mp h u (mem_univ u)
      have := (sum_eq_zero_iff_of_nonneg (hnn u)).mp h1 v ((G.mem_neighborFinset u v).mpr huv)
      rw [div_eq_zero_iff, sq_eq_zero_iff, sub_eq_zero] at this
      rcases this with h | h
      · exact_mod_cast h.symm
      · nlinarith
    · intro h
      refine sum_eq_zero fun v _ ↦ sum_eq_zero fun u hu ↦ ?_
      rw [h u v ((G.mem_neighborFinset v u).mp hu).symm]
      simp
  rw [← hzero]
  constructor <;> intro h <;> linarith

/-- Degree is constant on components iff adjacent vertices have equal degree. -/
theorem degree_eq_of_reachable_iff :
    (∀ u v, G.Reachable u v → G.degree u = G.degree v) ↔
      ∀ u v, G.Adj u v → G.degree u = G.degree v := by
  refine ⟨fun h u v huv ↦ h u v huv.reachable, fun h u v huv ↦ ?_⟩
  rw [reachable_iff_reflTransGen] at huv
  induction huv with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (h _ _ hbc)

/-- Equality in the per-person form holds iff the degree is constant on every connected
component. -/
theorem friendship_paradox_local_eq_iff_reachable :
    ∑ v, (G.degree v : ℚ) = ∑ v, (G.friendDegreeSum v : ℚ) / G.degree v ↔
      ∀ u v, G.Reachable u v → G.degree u = G.degree v := by
  rw [friendship_paradox_local_eq_iff, degree_eq_of_reachable_iff]

end SimpleGraph
