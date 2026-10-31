module

public import LeanPlayground.PerfectCuboid.Basic
public import LeanPlayground.PerfectCuboid.SpaceDiagonal

/-!
# Prime-support shapes of an Euler brick for `p ≡ 3 (mod 4)`

Let `(a, b, c)` be a primitive Euler brick with face diagonals `d² = a² + b²`, `e² = a² + c²`,
`f² = b² + c²`, and let `p` be a prime with `p ≡ 3 (mod 4)`. Then the set of lengths among
`a, b, c, d, e, f` divisible by `p` is one of the seven sets
`∅, {a}, {b}, {c}, {a,b,d}, {a,c,e}, {b,c,f}` (`IsEulerBrick.support_shape_three_mod_four`).

*Proof.* A prime `p ≡ 3 (mod 4)` dividing `x² + y²` divides `x` and `y`
(`prime_dvd_both_of_dvd_sq_add_sq`), so `p ∣ d ↔ p ∣ a ∧ p ∣ b` (the converse because
`p ∣ d²`), and likewise for `e` and `f`. Primitivity excludes `p ∣ a, b, c`; the remaining seven
patterns of `(p ∣ a, p ∣ b, p ∣ c)` give the seven shapes.

This is the brick analogue of `IsPerfectCuboid.support_shape_three_mod_four` and
`IsFaceCuboid.support_shape_three_mod_four` (`PrimeSupport.lean`); unlike the general-`p` brick
list `Support.BrickShape` (17 shapes) it needs no valuation argument.

All seven shapes occur, already for the brick `(44, 117, 240)` (`d, e, f = 125, 244, 267`) and its
reorderings with `p = 7, 11, 3` (`brickShape3_examples`). Over the 87 primitive bricks with edges
`≤ 2·10⁵`, all six orderings, and every prime `p ≡ 3 (mod 4)` dividing `abcdef` (plus
`7, 19, 23`), the 3468 supports are all among the seven shapes
(`round14/code/b3/brick_shapes3.py`).
-/

@[expose] public section

namespace PerfectCuboid.BrickSupport

/-- The 7 prime-support shapes of a primitive Euler brick for `p ≡ 3 (mod 4)`; the arguments
stand for `p ∣ a, p ∣ b, p ∣ c, p ∣ d, p ∣ e, p ∣ f`. In order:
`∅, {a}, {b}, {c}, {a,b,d}, {a,c,e}, {b,c,f}`. -/
def BrickShape3 (A B C D E F : Prop) : Prop :=
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F) ∨
  (A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F) ∨
  (¬ A ∧ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F) ∨
  (¬ A ∧ ¬ B ∧ C ∧ ¬ D ∧ ¬ E ∧ ¬ F) ∨
  (A ∧ B ∧ ¬ C ∧ D ∧ ¬ E ∧ ¬ F) ∨
  (A ∧ ¬ B ∧ C ∧ ¬ D ∧ E ∧ ¬ F) ∨
  (¬ A ∧ B ∧ C ∧ ¬ D ∧ ¬ E ∧ F)

/-- The propositional core: if `D ↔ A ∧ B`, `E ↔ A ∧ C`, `F ↔ B ∧ C` and not all of `A, B, C`
hold, the pattern is one of the seven shapes. -/
theorem brickShape3_of_iff {A B C D E F : Prop} (hD : D ↔ A ∧ B) (hE : E ↔ A ∧ C)
    (hF : F ↔ B ∧ C) (prim : ¬ (A ∧ B ∧ C)) : BrickShape3 A B C D E F := by
  obtain rfl := propext hD
  obtain rfl := propext hE
  obtain rfl := propext hF
  unfold BrickShape3
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp_all

/-- For `p ≡ 3 (mod 4)` prime and `x² + y² = z²`: `p ∣ z ↔ p ∣ x ∧ p ∣ y`. -/
theorem dvd_hyp_iff {p x y z : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (h : x ^ 2 + y ^ 2 = z ^ 2) :
    p ∣ z ↔ p ∣ x ∧ p ∣ y :=
  ⟨fun hz ↦ prime_dvd_both_of_dvd_sq_add_sq hp h3 (h ▸ dvd_pow hz two_ne_zero),
    fun ⟨hx, hy⟩ ↦ hp.dvd_of_dvd_pow (h ▸ dvd_add (dvd_pow hx two_ne_zero)
      (dvd_pow hy two_ne_zero))⟩

end PerfectCuboid.BrickSupport

namespace PerfectCuboid

open BrickSupport

/-- **Prime support of a primitive Euler brick for `p ≡ 3 (mod 4)`:** the set of lengths among
`a, b, c, d, e, f` divisible by `p` is one of `∅, {a}, {b}, {c}, {a,b,d}, {a,c,e}, {b,c,f}`.
(Positivity of the edges is not used; only primitivity and the three face relations.) -/
theorem IsEulerBrick.support_shape_three_mod_four {a b c : ℕ} (_h : IsEulerBrick a b c)
    (hp : Nat.gcd (Nat.gcd a b) c = 1) {d e f : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) {p : ℕ} (pp : p.Prime)
    (h3 : p % 4 = 3) :
    BrickShape3 (p ∣ a) (p ∣ b) (p ∣ c) (p ∣ d) (p ∣ e) (p ∣ f) := by
  refine brickShape3_of_iff (dvd_hyp_iff pp h3 hd) (dvd_hyp_iff pp h3 he) (dvd_hyp_iff pp h3 hf)
    ?_
  rintro ⟨ha, hb, hc⟩
  have : p ∣ Nat.gcd (Nat.gcd a b) c := Nat.dvd_gcd (Nat.dvd_gcd ha hb) hc
  rw [hp] at this
  exact pp.one_lt.ne' (Nat.dvd_one.mp this)

/-- **All seven shapes occur**, for the brick `(44, 117, 240)` (`d, e, f = 125, 244, 267`) and its
reorderings: `∅` (`p = 7`), `{a}`, `{b}`, `{c}` (`p = 11`), `{a,b,d}`, `{a,c,e}`, `{b,c,f}`
(`p = 3`). Each conjunct is the corresponding disjunct of `BrickShape3`. -/
theorem BrickSupport.brickShape3_examples :
    -- `∅`: `(44, 117, 240; 125, 244, 267)`, `p = 7`
    (¬ 7 ∣ 44 ∧ ¬ 7 ∣ 117 ∧ ¬ 7 ∣ 240 ∧ ¬ 7 ∣ 125 ∧ ¬ 7 ∣ 244 ∧ ¬ 7 ∣ 267) ∧
    -- `{a}`: `(44, 117, 240; 125, 244, 267)`, `p = 11`
    (11 ∣ 44 ∧ ¬ 11 ∣ 117 ∧ ¬ 11 ∣ 240 ∧ ¬ 11 ∣ 125 ∧ ¬ 11 ∣ 244 ∧ ¬ 11 ∣ 267) ∧
    -- `{b}`: `(117, 44, 240; 125, 267, 244)`, `p = 11`
    (¬ 11 ∣ 117 ∧ 11 ∣ 44 ∧ ¬ 11 ∣ 240 ∧ ¬ 11 ∣ 125 ∧ ¬ 11 ∣ 267 ∧ ¬ 11 ∣ 244) ∧
    -- `{c}`: `(117, 240, 44; 267, 125, 244)`, `p = 11`
    (¬ 11 ∣ 117 ∧ ¬ 11 ∣ 240 ∧ 11 ∣ 44 ∧ ¬ 11 ∣ 267 ∧ ¬ 11 ∣ 125 ∧ ¬ 11 ∣ 244) ∧
    -- `{a,b,d}`: `(117, 240, 44; 267, 125, 244)`, `p = 3`
    (3 ∣ 117 ∧ 3 ∣ 240 ∧ ¬ 3 ∣ 44 ∧ 3 ∣ 267 ∧ ¬ 3 ∣ 125 ∧ ¬ 3 ∣ 244) ∧
    -- `{a,c,e}`: `(117, 44, 240; 125, 267, 244)`, `p = 3`
    (3 ∣ 117 ∧ ¬ 3 ∣ 44 ∧ 3 ∣ 240 ∧ ¬ 3 ∣ 125 ∧ 3 ∣ 267 ∧ ¬ 3 ∣ 244) ∧
    -- `{b,c,f}`: `(44, 117, 240; 125, 244, 267)`, `p = 3`
    (¬ 3 ∣ 44 ∧ 3 ∣ 117 ∧ 3 ∣ 240 ∧ ¬ 3 ∣ 125 ∧ ¬ 3 ∣ 244 ∧ 3 ∣ 267) ∧
    -- the reorderings are Euler bricks with these diagonals
    (44 ^ 2 + 117 ^ 2 = 125 ^ 2 ∧ 44 ^ 2 + 240 ^ 2 = 244 ^ 2 ∧ 117 ^ 2 + 240 ^ 2 = 267 ^ 2) := by
  decide

end PerfectCuboid
