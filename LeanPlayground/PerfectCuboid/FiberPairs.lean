module

public import LeanPlayground.PerfectCuboid.Descent

/-!
# Three pairs of Pythagorean legs on a fiber

On the fiber `(m, n)` of Peschmann's master-tuple parametrization, a perfect cuboid has two edges
`X = V k`, `Z = U k` with `U = m² − n²`, `V = 2mn`, `W = m² + n²`, and a third edge `Y`. Then
`Y² + U²k²` (a face diagonal), `Y² + V²k²` (another face diagonal) and `Y² + W²k²` (the space
diagonal) are all squares. So the cuboid gives a solution of `Descent.IsSol p q` for each of the
three pairs `(V, W)`, `(U, W)` and `(U, V)`, and the descent of
`LeanPlayground.PerfectCuboid.Descent` for any one of them rules out the fiber.

The three curves `y² = x (x + p²)(x + q²)` have different ranks: among the `331` fibers with
`m ≤ 40`, `70` have a usable pair `(V, W)` (rank `0`, `Ш[2] = 0`) and `88` a usable pair
`(U, W)`, so `131` have at least one of the two (PARI/GP).

## Main results

* `IsPerfectCuboid.isSol_three_pairs` — `U X = V Z` gives solutions for all three pairs.
* `IsPerfectCuboid.not_onFiber_of_pair` — no solution for one pair rules out the fiber.
-/

@[expose] public section

namespace PerfectCuboid

/-- **A perfect cuboid on a fiber gives a solution for each of the three pairs.** If
`U² + V² = W²` and two edges satisfy `U X = V Z`, then `M = V Y`, `e = X` make `M² + U² e²`,
`M² + V² e²` and `M² + W² e²` all squares (`V` times the diagonals of the faces `YZ`, `XY` and
the space diagonal). -/
theorem IsPerfectCuboid.isSol_three_pairs {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) {U V W : ℤ}
    (hV : V ≠ 0) (hW : U ^ 2 + V ^ 2 = W ^ 2) (hf : U * X = V * Z) :
    ∃ r s t : ℤ, Descent.IsSol V W (V * Y) X r s ∧ Descent.IsSol U W (V * Y) X t s ∧
      Descent.IsSol U V (V * Y) X t r := by
  obtain ⟨r, hr⟩ := h.sq_ab
  obtain ⟨t, ht⟩ := h.sq_bc
  obtain ⟨s, hs⟩ := h.sq_abc
  have hX : (X : ℤ) ≠ 0 := by exact_mod_cast h.pos_a.ne'
  have hM : V * Y ≠ 0 := mul_ne_zero hV (by exact_mod_cast h.pos_b.ne')
  have hr' : (X : ℤ) ^ 2 + Y ^ 2 = r * r := by exact_mod_cast hr
  have ht' : (Y : ℤ) ^ 2 + Z ^ 2 = t * t := by exact_mod_cast ht
  have hs' : (X : ℤ) ^ 2 + Y ^ 2 + Z ^ 2 = s * s := by exact_mod_cast hs
  have hUX : (V * Y) ^ 2 + U ^ 2 * X ^ 2 = (V * t) ^ 2 := by
    linear_combination V ^ 2 * ht' + (U * X + V * Z) * hf
  refine ⟨V * r, V * s, V * t, ⟨hM, hX, ?_, ?_⟩, ⟨hM, hX, hUX, ?_⟩, ⟨hM, hX, hUX, ?_⟩⟩
  · linear_combination V ^ 2 * hr'
  · linear_combination V ^ 2 * hs' + (U * X + V * Z) * hf - X ^ 2 * hW
  · linear_combination V ^ 2 * hs' + (U * X + V * Z) * hf - X ^ 2 * hW
  · linear_combination V ^ 2 * hr'

/-- **The descent for any one of the three pairs rules out a fiber.** On the fiber `(m, n)`, with
`U = m² − n²`, `V = 2mn`, `W = m² + n²`, a perfect cuboid with `U X = V Z` gives solutions of
`IsSol V W`, `IsSol U W` and `IsSol U V` (`isSol_three_pairs`), so it suffices that one of the
three has none. The fibers of `provedFibers` use the pair `(V, W)` or the pair `(U, W)`. -/
theorem IsPerfectCuboid.not_onFiber_of_pair {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) {m n : ℤ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hpair : (∀ M e r s, ¬ Descent.IsSol (2 * m * n) (m ^ 2 + n ^ 2) M e r s) ∨
      (∀ M e r s, ¬ Descent.IsSol (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) M e r s) ∨
      (∀ M e r s, ¬ Descent.IsSol (m ^ 2 - n ^ 2) (2 * m * n) M e r s)) :
    (m ^ 2 - n ^ 2) * X ≠ 2 * m * n * Z := by
  intro hf
  obtain ⟨r, s, t, h1, h2, h3⟩ :=
    h.isSol_three_pairs (W := m ^ 2 + n ^ 2) (mul_ne_zero (mul_ne_zero two_ne_zero hm) hn)
      (by ring) hf
  rcases hpair with hp | hp | hp
  · exact hp _ _ _ _ h1
  · exact hp _ _ _ _ h2
  · exact hp _ _ _ _ h3

end PerfectCuboid
