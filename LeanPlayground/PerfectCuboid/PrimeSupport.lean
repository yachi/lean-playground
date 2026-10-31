module

public import LeanPlayground.PerfectCuboid.SpaceDiagonal
public import LeanPlayground.PerfectCuboid.FaceCuboidLeech

/-!
# Prime supports of cuboids

For a box with edges `a, b, c`, face diagonals `d, e, f` and space diagonal `g` and a prime `p`,
the **support** of `p` is the set of lengths that `p` divides. The six Pythagorean relations
`(a,b,d), (a,c,e), (b,c,f), (a,f,g), (b,e,g), (c,d,g)` each say that `p` divides all three
lengths of the relation as soon as it divides two of them (`Support.dvd_hyp`, `Support.dvd_leg`,
`Support.dvd_leg'`), and primitivity says that `p` does not divide all three edges.
This file classifies the supports that survive these rules.

* `IsPerfectCuboid.support_shape`: for a primitive perfect cuboid and **every** prime `p`, the
  support of `p` is one of the 17 sets
  `∅, {a}, {b}, {c}, {a,b,d}, {a,c,e}, {b,c,f}, {a,f,g}, {b,e,g}, {c,d,g}, {d}, {e}, {f}, {g},
  {d,e}, {d,f}, {e,f}` (`Support.PerfectShape`). The set `{d,e,f}` is excluded by
  `d² + e² + f² = 2g²` for odd `p` and by parity for `p = 2`.
* `IsPerfectCuboid.support_shape_three_mod_four`: for `p ≡ 3 (mod 4)` only the first seven occur.
* `IsPerfectCuboid.support_two`: the support of `2` is `{b,c,f}`, `{a,c,e}` or `{a,b,d}`.
* Consequences: no prime divides all three face diagonals
  (`IsPerfectCuboid.not_dvd_three_face_diagonals`); a prime dividing two face diagonals divides no
  edge and not the space diagonal (`IsPerfectCuboid.dvd_two_face_diagonals`); every prime divides
  at most three of the seven lengths (`IsPerfectCuboid.card_support_le_three`); a prime of the space
  diagonal divides at most one edge (`IsPerfectCuboid.dvd_space_diagonal_at_most_one_edge`), and if
  it divides `a` its support is `{a,f,g}` (`IsPerfectCuboid.dvd_space_diagonal_dvd_a`); a prime
  dividing two edges divides exactly those two and their face diagonal
  (`IsPerfectCuboid.dvd_two_edges`).
* Face cuboids (`IsFaceCuboid`, lengths `a, b, c, e, f, g`): `IsFaceCuboid.support_shape`
  (14 shapes, `Support.FaceShape`), `IsFaceCuboid.support_shape_three_mod_four` (7 shapes), and
  `IsFaceCuboid.prime_dvd_space_diagonal`: every prime of the space diagonal of a primitive face
  cuboid is `≡ 1 (mod 4)`; `IsFaceCuboid.dvd_space_diagonal_dvd_c`.
* Euler bricks (lengths `a, …, f`): `IsEulerBrick.support_shape` (17 shapes,
  `Support.BrickShape`, among them `{a,f}` and `{d,e,f}`); the brick `(19175, 293832, 112320)`
  realizes `{d,f}` with `p = 17` and `(44, 117, 240)` realizes `{c,d}` with `p = 5`.
* Valuations: `Support.padicValNat_hyp_ge` (`v_p(z) ≥ min(v_p(x), v_p(y))` for `x² + y² = z²`),
  `Support.padicValNat_hyp_eq` (equality when `v_p(x) ≠ v_p(y)`) and
  `Support.padicValNat_sub_add` (`v_p(z − y) + v_p(z + y) = 2 v_p(x)`).

None of the shapes of `support_shape` can be excluded by a local argument that also applies to
Euler bricks or face cuboids: each of them is realized (as a sub-pattern) in the near-miss data.
-/

@[expose] public section

namespace PerfectCuboid.Support

/-! ### Pythagorean closure -/

/-- Closure of divisibility along a Pythagorean relation: a prime dividing both legs divides the
hypotenuse. -/
theorem dvd_hyp {p x y z : ℕ} (h : x ^ 2 + y ^ 2 = z ^ 2) (hp : p.Prime) (hx : p ∣ x)
    (hy : p ∣ y) : p ∣ z :=
  hp.dvd_of_dvd_pow (h ▸ dvd_add (dvd_pow hx two_ne_zero) (dvd_pow hy two_ne_zero))

/-- Closure of divisibility along a Pythagorean relation: a prime dividing a leg and the
hypotenuse divides the other leg. -/
theorem dvd_leg {p x y z : ℕ} (h : x ^ 2 + y ^ 2 = z ^ 2) (hp : p.Prime) (hx : p ∣ x)
    (hz : p ∣ z) : p ∣ y :=
  hp.dvd_of_dvd_pow ((Nat.dvd_add_right (dvd_pow hx two_ne_zero)).mp (h ▸ dvd_pow hz two_ne_zero))

/-- `dvd_leg` for the first leg. -/
theorem dvd_leg' {p x y z : ℕ} (h : x ^ 2 + y ^ 2 = z ^ 2) (hp : p.Prime) (hy : p ∣ y)
    (hz : p ∣ z) : p ∣ x :=
  dvd_leg (by rw [add_comm]; exact h) hp hy hz

/-- The three closure rules of one Pythagorean relation. -/
theorem rel {p x y z : ℕ} (h : x ^ 2 + y ^ 2 = z ^ 2) (hp : p.Prime) :
    (p ∣ x → p ∣ y → p ∣ z) ∧ (p ∣ x → p ∣ z → p ∣ y) ∧ (p ∣ y → p ∣ z → p ∣ x) :=
  ⟨dvd_hyp h hp, dvd_leg h hp, dvd_leg' h hp⟩

/-! ### The shape lists, as predicates on the divisibility statements -/

/-- The 17 prime-support shapes of a primitive perfect cuboid; the arguments stand for
`p ∣ a, p ∣ b, p ∣ c, p ∣ d, p ∣ e, p ∣ f, p ∣ g`. In order: `∅, {a}, {b}, {c}, {a,b,d},
{a,c,e}, {b,c,f}, {a,f,g}, {b,e,g}, {c,d,g}, {d}, {e}, {f}, {g}, {d,e}, {d,f}, {e,f}`. -/
def PerfectShape (A B C D E F G : Prop) : Prop :=
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ ¬ B ∧ C ∧ ¬ D ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (A ∧ B ∧ ¬ C ∧ D ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (A ∧ ¬ B ∧ C ∧ ¬ D ∧ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ B ∧ C ∧ ¬ D ∧ ¬ E ∧ F ∧ ¬ G) ∨
  (A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ F ∧ G) ∨
  (¬ A ∧ B ∧ ¬ C ∧ ¬ D ∧ E ∧ ¬ F ∧ G) ∨
  (¬ A ∧ ¬ B ∧ C ∧ D ∧ ¬ E ∧ ¬ F ∧ G) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ D ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ F ∧ ¬ G) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F ∧ G) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ D ∧ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ D ∧ ¬ E ∧ F ∧ ¬ G) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ E ∧ F ∧ ¬ G)

/-- The 7 prime-support shapes of a primitive perfect cuboid for `p ≡ 3 (mod 4)`:
`∅, {a}, {b}, {c}, {a,b,d}, {a,c,e}, {b,c,f}`. -/
def PerfectShape3 (A B C D E F G : Prop) : Prop :=
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ ¬ B ∧ C ∧ ¬ D ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (A ∧ B ∧ ¬ C ∧ D ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (A ∧ ¬ B ∧ C ∧ ¬ D ∧ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ B ∧ C ∧ ¬ D ∧ ¬ E ∧ F ∧ ¬ G)

/-- The 14 prime-support shapes of a primitive face cuboid; the arguments stand for
`p ∣ a, p ∣ b, p ∣ c, p ∣ e, p ∣ f, p ∣ g` (`e² = a² + c²`, `f² = b² + c²`, `g² = a² + b² + c²`).
In order: `∅, {a}, {b}, {c}, {a,b}, {a,c,e}, {b,c,f}, {a,f,g}, {b,e,g}, {c,g}, {e}, {f}, {g},
{e,f}`. -/
def FaceShape (A B C E F G : Prop) : Prop :=
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (A ∧ ¬ B ∧ ¬ C ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ B ∧ ¬ C ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ ¬ B ∧ C ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (A ∧ B ∧ ¬ C ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (A ∧ ¬ B ∧ C ∧ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ B ∧ C ∧ ¬ E ∧ F ∧ ¬ G) ∨
  (A ∧ ¬ B ∧ ¬ C ∧ ¬ E ∧ F ∧ G) ∨
  (¬ A ∧ B ∧ ¬ C ∧ E ∧ ¬ F ∧ G) ∨
  (¬ A ∧ ¬ B ∧ C ∧ ¬ E ∧ ¬ F ∧ G) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ E ∧ F ∧ ¬ G) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ E ∧ ¬ F ∧ G) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ E ∧ F ∧ ¬ G)

/-- The 7 prime-support shapes of a primitive face cuboid for `p ≡ 3 (mod 4)`:
`∅, {a}, {b}, {c}, {a,b}, {a,c,e}, {b,c,f}`. -/
def FaceShape3 (A B C E F G : Prop) : Prop :=
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (A ∧ ¬ B ∧ ¬ C ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ B ∧ ¬ C ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ ¬ B ∧ C ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (A ∧ B ∧ ¬ C ∧ ¬ E ∧ ¬ F ∧ ¬ G) ∨
  (A ∧ ¬ B ∧ C ∧ E ∧ ¬ F ∧ ¬ G) ∨
  (¬ A ∧ B ∧ C ∧ ¬ E ∧ F ∧ ¬ G)

/-- The 17 prime-support shapes of a primitive Euler brick; the arguments stand for
`p ∣ a, …, p ∣ f`. In order: `∅, {a}, {b}, {c}, {d}, {e}, {f}, {a,b,d}, {a,c,e}, {b,c,f},
{a,f}, {b,e}, {c,d}, {d,e}, {d,f}, {e,f}, {d,e,f}`. -/
def BrickShape (A B C D E F : Prop) : Prop :=
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F) ∨
  (A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F) ∨
  (¬ A ∧ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ ¬ F) ∨
  (¬ A ∧ ¬ B ∧ C ∧ ¬ D ∧ ¬ E ∧ ¬ F) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ D ∧ ¬ E ∧ ¬ F) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ E ∧ ¬ F) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ F) ∨
  (A ∧ B ∧ ¬ C ∧ D ∧ ¬ E ∧ ¬ F) ∨
  (A ∧ ¬ B ∧ C ∧ ¬ D ∧ E ∧ ¬ F) ∨
  (¬ A ∧ B ∧ C ∧ ¬ D ∧ ¬ E ∧ F) ∨
  (A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ ¬ E ∧ F) ∨
  (¬ A ∧ B ∧ ¬ C ∧ ¬ D ∧ E ∧ ¬ F) ∨
  (¬ A ∧ ¬ B ∧ C ∧ D ∧ ¬ E ∧ ¬ F) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ D ∧ E ∧ ¬ F) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ D ∧ ¬ E ∧ F) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D ∧ E ∧ F) ∨
  (¬ A ∧ ¬ B ∧ ¬ C ∧ D ∧ E ∧ F)

/-! ### The combinatorial classification -/

/-- The closed subsets of `{a, …, g}` under the six Pythagorean relations, not containing all
three edges and not containing `{d,e,f}` without `g`, are the 17 shapes. -/
theorem perfectShape_of_closure {A B C D E F G : Prop}
    (abd : A → B → D) (adb : A → D → B) (bda : B → D → A)
    (ace : A → C → E) (aec : A → E → C) (cea : C → E → A)
    (bcf : B → C → F) (bfc : B → F → C) (cfb : C → F → B)
    (afg : A → F → G) (agf : A → G → F) (fga : F → G → A)
    (beg : B → E → G) (bge : B → G → E) (egb : E → G → B)
    (cdg : C → D → G) (cgd : C → G → D) (dgc : D → G → C)
    (prim : ¬ (A ∧ B ∧ C)) (defg : D → E → F → G) : PerfectShape A B C D E F G := by
  unfold PerfectShape
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases hD : D <;>
    by_cases hE : E <;> by_cases hF : F <;> by_cases hG : G <;> simp_all

/-- For `p ≡ 3 (mod 4)` a prime dividing a hypotenuse divides both legs; this cuts the 17 shapes
down to 7. -/
theorem perfectShape3_of_perfectShape {A B C D E F G : Prop} (H : PerfectShape A B C D E F G)
    (hd : D → A ∧ B) (he : E → A ∧ C) (hf : F → B ∧ C) (hg : G → A ∧ F) :
    PerfectShape3 A B C D E F G := by
  unfold PerfectShape at H
  unfold PerfectShape3
  rcases H with ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hD, hE, hF, hG⟩ <;>
    simp_all

/-- The closed subsets of `{a, b, c, e, f, g}` under the four Pythagorean relations of a face
cuboid, not containing all three edges, are the 14 shapes. -/
theorem faceShape_of_closure {A B C E F G : Prop}
    (ace : A → C → E) (aec : A → E → C) (cea : C → E → A)
    (bcf : B → C → F) (bfc : B → F → C) (cfb : C → F → B)
    (afg : A → F → G) (agf : A → G → F) (fga : F → G → A)
    (beg : B → E → G) (bge : B → G → E) (egb : E → G → B)
    (prim : ¬ (A ∧ B ∧ C)) : FaceShape A B C E F G := by
  unfold FaceShape
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;>
    by_cases hE : E <;> by_cases hF : F <;> by_cases hG : G <;> simp_all

theorem faceShape3_of_faceShape {A B C E F G : Prop} (H : FaceShape A B C E F G)
    (he : E → A ∧ C) (hf : F → B ∧ C) (hg : G → A ∧ F) (hcg : C → G → A ∧ B) :
    FaceShape3 A B C E F G := by
  unfold FaceShape at H
  unfold FaceShape3
  rcases H with ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ |
      ⟨hA, hB, hC, hE, hF, hG⟩ <;>
    simp_all

/-- The closed subsets of `{a, …, f}` under the three Pythagorean relations of an Euler brick,
not containing all three edges, are the 17 shapes. -/
theorem brickShape_of_closure {A B C D E F : Prop}
    (abd : A → B → D) (adb : A → D → B) (bda : B → D → A)
    (ace : A → C → E) (aec : A → E → C) (cea : C → E → A)
    (bcf : B → C → F) (bfc : B → F → C) (cfb : C → F → B)
    (prim : ¬ (A ∧ B ∧ C)) : BrickShape A B C D E F := by
  unfold BrickShape
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;>
    by_cases hD : D <;> by_cases hE : E <;> by_cases hF : F <;> simp_all

/-! ### Primitivity -/

theorem not_dvd_three {a b c p : ℕ} (hp : Nat.gcd a (Nat.gcd b c) = 1) (pp : p.Prime) :
    ¬ (p ∣ a ∧ p ∣ b ∧ p ∣ c) := fun ⟨ha, hb, hc⟩ ↦
  pp.one_lt.ne' (Nat.dvd_one.mp (hp ▸ Nat.dvd_gcd ha (Nat.dvd_gcd hb hc)))

theorem not_dvd_three' {a b c p : ℕ} (hp : Nat.gcd (Nat.gcd a b) c = 1) (pp : p.Prime) :
    ¬ (p ∣ a ∧ p ∣ b ∧ p ∣ c) := fun ⟨ha, hb, hc⟩ ↦
  pp.one_lt.ne' (Nat.dvd_one.mp (hp ▸ Nat.dvd_gcd (Nat.dvd_gcd ha hb) hc))

/-! ### Valuations along a Pythagorean relation -/

/-- `v_p(z) ≥ min(v_p(x), v_p(y))` for `x² + y² = z²`, `z > 0`. -/
theorem padicValNat_hyp_ge {p x y z : ℕ} [Fact p.Prime] (h : x ^ 2 + y ^ 2 = z ^ 2)
    (hz : z ≠ 0) : min (padicValNat p x) (padicValNat p y) ≤ padicValNat p z := by
  set m := min (padicValNat p x) (padicValNat p y)
  have hx : p ^ m ∣ x := (pow_dvd_pow p (min_le_left _ _)).trans pow_padicValNat_dvd
  have hy : p ^ m ∣ y := (pow_dvd_pow p (min_le_right _ _)).trans pow_padicValNat_dvd
  have h2 : (p ^ m) ^ 2 ∣ z ^ 2 := h ▸ dvd_add (pow_dvd_pow_of_dvd hx 2) (pow_dvd_pow_of_dvd hy 2)
  exact (padicValNat_dvd_iff_le hz).mp ((Nat.pow_dvd_pow_iff two_ne_zero).mp h2)

/-- `padicValNat_hyp_eq` when `v_p(x) < v_p(y)`. -/
theorem padicValNat_hyp_eq_of_lt {p x y z : ℕ} [Fact p.Prime] (h : x ^ 2 + y ^ 2 = z ^ 2)
    (hx : x ≠ 0) (hy : y ≠ 0) (hl : padicValNat p x < padicValNat p y) :
    padicValNat p z = padicValNat p x := by
  have hz : z ≠ 0 := by
    rintro rfl
    have : x ^ 2 = 0 := by omega
    exact hx (pow_eq_zero_iff two_ne_zero |>.mp this)
  have ge := padicValNat_hyp_ge (p := p) h hz
  rw [min_eq_left hl.le] at ge
  refine le_antisymm ?_ ge
  by_contra hlt
  push Not at hlt
  have hz' : p ^ (padicValNat p x + 1) ∣ z := (padicValNat_dvd_iff_le hz).mpr (by omega)
  have hy' : p ^ (padicValNat p x + 1) ∣ y := (padicValNat_dvd_iff_le hy).mpr (by omega)
  have h2 : (p ^ (padicValNat p x + 1)) ^ 2 ∣ x ^ 2 :=
    (Nat.dvd_add_left (pow_dvd_pow_of_dvd hy' 2)).mp (h ▸ pow_dvd_pow_of_dvd hz' 2)
  have := (padicValNat_dvd_iff_le hx).mp ((Nat.pow_dvd_pow_iff two_ne_zero).mp h2)
  omega

/-- `v_p(z) = min(v_p(x), v_p(y))` for `x² + y² = z²` with `x, y > 0` and `v_p(x) ≠ v_p(y)`. -/
theorem padicValNat_hyp_eq {p x y z : ℕ} [Fact p.Prime] (h : x ^ 2 + y ^ 2 = z ^ 2)
    (hx : x ≠ 0) (hy : y ≠ 0) (hne : padicValNat p x ≠ padicValNat p y) :
    padicValNat p z = min (padicValNat p x) (padicValNat p y) := by
  have hz : z ≠ 0 := by
    rintro rfl
    have : x ^ 2 = 0 := by omega
    exact hx (pow_eq_zero_iff two_ne_zero |>.mp this)
  rcases lt_or_gt_of_ne hne with hl | hl
  · rw [min_eq_left hl.le]
    exact padicValNat_hyp_eq_of_lt h hx hy hl
  · rw [min_eq_right hl.le]
    exact padicValNat_hyp_eq_of_lt (by rw [add_comm]; exact h) hy hx hl

/-- `v_p(z − y) + v_p(z + y) = 2 v_p(x)` for `x² + y² = z²`, `x > 0`. -/
theorem padicValNat_sub_add {p x y z : ℕ} [Fact p.Prime] (h : x ^ 2 + y ^ 2 = z ^ 2)
    (hx : x ≠ 0) : padicValNat p (z - y) + padicValNat p (z + y) = 2 * padicValNat p x := by
  have hzy : y ≤ z := (Nat.pow_le_pow_iff_left two_ne_zero).mp (h ▸ Nat.le_add_left _ _)
  have hprod : (z - y) * (z + y) = x ^ 2 := by
    have h' : ((z : ℤ)) ^ 2 = (x : ℤ) ^ 2 + (y : ℤ) ^ 2 := by exact_mod_cast h.symm
    zify [hzy]
    linear_combination h'
  have h1 : z - y ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact hx (pow_eq_zero_iff two_ne_zero |>.mp hprod.symm)
  have h2 : z + y ≠ 0 := by omega
  rw [← padicValNat.mul h1 h2, hprod, padicValNat.pow x 2]

end PerfectCuboid.Support

namespace PerfectCuboid

open Support

/-! ### Perfect cuboids -/

/-- No prime divides all three face diagonals of a primitive perfect cuboid without dividing the
space diagonal (for `p = 2` the hypothesis is never met). -/
theorem IsPerfectCuboid.dvd_g_of_dvd_def {a b c : ℕ} (h : IsPerfectCuboid a b c)
    (hp : Nat.gcd a (Nat.gcd b c) = 1) {d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    {p : ℕ} (pp : p.Prime) (hpd : p ∣ d) (hpe : p ∣ e) (hpf : p ∣ f) : p ∣ g := by
  rcases pp.eq_two_or_odd' with rfl | hodd
  · exfalso
    rcases h.one_odd hp with ⟨ha, hb, -⟩ | ⟨ha, hb, -⟩ | ⟨ha, -, hc⟩
    · exact ha (dvd_leg' hd Nat.prime_two hb hpd)
    · exact hb (dvd_leg hd Nat.prime_two ha hpd)
    · exact hc (dvd_leg he Nat.prime_two ha hpe)
  · have key : 2 * g ^ 2 = d ^ 2 + e ^ 2 + f ^ 2 := by
      rw [← hg, ← hd, ← he, ← hf]; ring
    have h2 : p ∣ 2 * g ^ 2 := key ▸ dvd_add (dvd_add (dvd_pow hpd two_ne_zero)
      (dvd_pow hpe two_ne_zero)) (dvd_pow hpf two_ne_zero)
    rcases (Nat.Prime.dvd_mul pp).mp h2 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq pp Nat.prime_two).mp h2
      subst this
      exact absurd hodd (by decide)
    · exact pp.dvd_of_dvd_pow h2

/-- **Shape classification.** For a primitive perfect cuboid and any prime `p`, the set of the
seven lengths divisible by `p` is one of the 17 shapes of `Support.PerfectShape`. -/
theorem IsPerfectCuboid.support_shape {a b c : ℕ} (h : IsPerfectCuboid a b c)
    (hp : Nat.gcd a (Nat.gcd b c) = 1) {d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    {p : ℕ} (pp : p.Prime) :
    PerfectShape (p ∣ a) (p ∣ b) (p ∣ c) (p ∣ d) (p ∣ e) (p ∣ f) (p ∣ g) := by
  have hafg : a ^ 2 + f ^ 2 = g ^ 2 := by rw [← hg, ← hf]; ring
  have hbeg : b ^ 2 + e ^ 2 = g ^ 2 := by rw [← hg, ← he]; ring
  have hcdg : c ^ 2 + d ^ 2 = g ^ 2 := by rw [← hg, ← hd]; ring
  obtain ⟨r1, r2, r3⟩ := rel hd pp
  obtain ⟨r4, r5, r6⟩ := rel he pp
  obtain ⟨r7, r8, r9⟩ := rel hf pp
  obtain ⟨r10, r11, r12⟩ := rel hafg pp
  obtain ⟨r13, r14, r15⟩ := rel hbeg pp
  obtain ⟨r16, r17, r18⟩ := rel hcdg pp
  exact perfectShape_of_closure r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
    (not_dvd_three hp pp) (h.dvd_g_of_dvd_def hp hd he hf hg pp)

/-- For `p ≡ 3 (mod 4)` only the seven shapes `∅, {a}, {b}, {c}, {a,b,d}, {a,c,e}, {b,c,f}` occur:
such a prime never divides a face or space diagonal. -/
theorem IsPerfectCuboid.support_shape_three_mod_four {a b c : ℕ} (h : IsPerfectCuboid a b c)
    (hp : Nat.gcd a (Nat.gcd b c) = 1) {d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    {p : ℕ} (pp : p.Prime) (h3 : p % 4 = 3) :
    PerfectShape3 (p ∣ a) (p ∣ b) (p ∣ c) (p ∣ d) (p ∣ e) (p ∣ f) (p ∣ g) := by
  have hafg : a ^ 2 + f ^ 2 = g ^ 2 := by rw [← hg, ← hf]; ring
  have hyp {x y z : ℕ} (hxyz : x ^ 2 + y ^ 2 = z ^ 2) (hz : p ∣ z) : p ∣ x ∧ p ∣ y :=
    prime_dvd_both_of_dvd_sq_add_sq pp h3 (hxyz ▸ dvd_pow hz two_ne_zero)
  exact perfectShape3_of_perfectShape (h.support_shape hp hd he hf hg pp) (hyp hd) (hyp he)
    (hyp hf) (hyp hafg)

/-- The support of `2`: exactly one edge is odd, and `2` divides the other two edges and their
face diagonal and nothing else. -/
theorem IsPerfectCuboid.support_two {a b c : ℕ} (h : IsPerfectCuboid a b c)
    (hp : Nat.gcd a (Nat.gcd b c) = 1) {d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    (¬ 2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c ∧ ¬ 2 ∣ d ∧ ¬ 2 ∣ e ∧ 2 ∣ f ∧ ¬ 2 ∣ g) ∨
    (2 ∣ a ∧ ¬ 2 ∣ b ∧ 2 ∣ c ∧ ¬ 2 ∣ d ∧ 2 ∣ e ∧ ¬ 2 ∣ f ∧ ¬ 2 ∣ g) ∨
    (2 ∣ a ∧ 2 ∣ b ∧ ¬ 2 ∣ c ∧ 2 ∣ d ∧ ¬ 2 ∣ e ∧ ¬ 2 ∣ f ∧ ¬ 2 ∣ g) := by
  have H := h.support_shape hp hd he hf hg Nat.prime_two
  unfold PerfectShape at H
  have := h.one_odd hp
  tauto

/-- **(C1)** No prime divides all three face diagonals of a primitive perfect cuboid. -/
theorem IsPerfectCuboid.not_dvd_three_face_diagonals {a b c : ℕ} (h : IsPerfectCuboid a b c)
    (hp : Nat.gcd a (Nat.gcd b c) = 1) {d e f : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) {p : ℕ} (pp : p.Prime) :
    ¬ (p ∣ d ∧ p ∣ e ∧ p ∣ f) := by
  obtain ⟨g, hg⟩ := h.sq_abc
  have H := h.support_shape hp hd he hf (g := g) (by rw [hg, sq]) pp
  unfold PerfectShape at H
  tauto

/-- **(C2)** A prime dividing two face diagonals divides no edge and not the space diagonal. -/
theorem IsPerfectCuboid.dvd_two_face_diagonals {a b c : ℕ} (h : IsPerfectCuboid a b c)
    (hp : Nat.gcd a (Nat.gcd b c) = 1) {d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    {p : ℕ} (pp : p.Prime) (hpd : p ∣ d) (hpe : p ∣ e) :
    ¬ p ∣ a ∧ ¬ p ∣ b ∧ ¬ p ∣ c ∧ ¬ p ∣ f ∧ ¬ p ∣ g := by
  have H := h.support_shape hp hd he hf hg pp
  unfold PerfectShape at H
  tauto

/-- **(C3)** Every prime divides at most three of the seven lengths. -/
theorem IsPerfectCuboid.card_support_le_three {a b c : ℕ} (h : IsPerfectCuboid a b c)
    (hp : Nat.gcd a (Nat.gcd b c) = 1) {d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    {p : ℕ} (pp : p.Prime) :
    (if p ∣ a then 1 else 0) + (if p ∣ b then 1 else 0) + (if p ∣ c then 1 else 0) +
      (if p ∣ d then 1 else 0) + (if p ∣ e then 1 else 0) + (if p ∣ f then 1 else 0) +
      (if p ∣ g then 1 else 0) ≤ 3 := by
  have H := h.support_shape hp hd he hf hg pp
  unfold PerfectShape at H
  rcases H with ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7⟩ <;>
    simp [h1, h2, h3, h4, h5, h6, h7]

/-- **(C4)** A prime of the space diagonal divides at most one edge. -/
theorem IsPerfectCuboid.dvd_space_diagonal_at_most_one_edge {a b c : ℕ}
    (h : IsPerfectCuboid a b c) (hp : Nat.gcd a (Nat.gcd b c) = 1) {g : ℕ}
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) {p : ℕ} (pp : p.Prime) (hpg : p ∣ g) :
    ¬ (p ∣ a ∧ p ∣ b) ∧ ¬ (p ∣ a ∧ p ∣ c) ∧ ¬ (p ∣ b ∧ p ∣ c) := by
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ca
  obtain ⟨f, hf⟩ := h.sq_bc
  have H := h.support_shape hp (d := d) (e := e) (f := f) (by rw [hd, sq])
    (by rw [add_comm, he, sq]) (by rw [hf, sq]) hg pp
  unfold PerfectShape at H
  tauto

/-- **(C4')** A prime dividing the space diagonal and the edge `a` divides `f` and no other
length. -/
theorem IsPerfectCuboid.dvd_space_diagonal_dvd_a {a b c : ℕ} (h : IsPerfectCuboid a b c)
    (hp : Nat.gcd a (Nat.gcd b c) = 1) {d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    {p : ℕ} (pp : p.Prime) (hpg : p ∣ g) (hpa : p ∣ a) :
    p ∣ f ∧ ¬ p ∣ b ∧ ¬ p ∣ c ∧ ¬ p ∣ d ∧ ¬ p ∣ e := by
  have H := h.support_shape hp hd he hf hg pp
  unfold PerfectShape at H
  tauto

/-- **(C5)** A prime dividing two edges divides their face diagonal and no other length. -/
theorem IsPerfectCuboid.dvd_two_edges {a b c : ℕ} (h : IsPerfectCuboid a b c)
    (hp : Nat.gcd a (Nat.gcd b c) = 1) {d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    {p : ℕ} (pp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) :
    p ∣ d ∧ ¬ p ∣ c ∧ ¬ p ∣ e ∧ ¬ p ∣ f ∧ ¬ p ∣ g := by
  have H := h.support_shape hp hd he hf hg pp
  unfold PerfectShape at H
  tauto

/-! ### Face cuboids -/

/-- **Shape classification for face cuboids.** For a primitive face cuboid and any prime `p`, the
set of the six lengths `a, b, c, e, f, g` divisible by `p` is one of the 14 shapes of
`Support.FaceShape`. -/
theorem IsFaceCuboid.support_shape {a b c : ℕ} (hp : Nat.gcd (Nat.gcd a b) c = 1) {e f g : ℕ}
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    {p : ℕ} (pp : p.Prime) :
    FaceShape (p ∣ a) (p ∣ b) (p ∣ c) (p ∣ e) (p ∣ f) (p ∣ g) := by
  have hafg : a ^ 2 + f ^ 2 = g ^ 2 := by rw [← hg, ← hf]; ring
  have hbeg : b ^ 2 + e ^ 2 = g ^ 2 := by rw [← hg, ← he]; ring
  obtain ⟨r4, r5, r6⟩ := rel he pp
  obtain ⟨r7, r8, r9⟩ := rel hf pp
  obtain ⟨r10, r11, r12⟩ := rel hafg pp
  obtain ⟨r13, r14, r15⟩ := rel hbeg pp
  exact faceShape_of_closure r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 (not_dvd_three' hp pp)

/-- For `p ≡ 3 (mod 4)` only the seven face-cuboid shapes `∅, {a}, {b}, {c}, {a,b}, {a,c,e},
{b,c,f}` occur. -/
theorem IsFaceCuboid.support_shape_three_mod_four {a b c : ℕ} (hp : Nat.gcd (Nat.gcd a b) c = 1)
    {e f g : ℕ} (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) {p : ℕ} (pp : p.Prime) (h3 : p % 4 = 3) :
    FaceShape3 (p ∣ a) (p ∣ b) (p ∣ c) (p ∣ e) (p ∣ f) (p ∣ g) := by
  have hafg : a ^ 2 + f ^ 2 = g ^ 2 := by rw [← hg, ← hf]; ring
  have hyp {x y z : ℕ} (hxyz : x ^ 2 + y ^ 2 = z ^ 2) (hz : p ∣ z) : p ∣ x ∧ p ∣ y :=
    prime_dvd_both_of_dvd_sq_add_sq pp h3 (hxyz ▸ dvd_pow hz two_ne_zero)
  refine faceShape3_of_faceShape (IsFaceCuboid.support_shape hp he hf hg pp) (hyp he) (hyp hf)
    (hyp hafg) fun hc hg' ↦ prime_dvd_both_of_dvd_sq_add_sq pp h3 ?_
  have h1 : p ∣ g ^ 2 := dvd_pow hg' two_ne_zero
  rw [← hg] at h1
  exact (Nat.dvd_add_left (dvd_pow hc two_ne_zero)).mp h1

/-- Every prime of the space diagonal of a primitive face cuboid is `≡ 1 (mod 4)`. -/
theorem IsFaceCuboid.prime_dvd_space_diagonal {a b c : ℕ} (h : IsFaceCuboid a b c)
    (hp : Nat.gcd (Nat.gcd a b) c = 1) {g : ℕ} (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) {p : ℕ}
    (pp : p.Prime) (hpg : p ∣ g) : p % 4 = 1 := by
  have hodd := h.space_diagonal_odd hp hg
  rcases pp.eq_two_or_odd' with rfl | hp2
  · omega
  have hp2' : p % 2 = 1 := Nat.odd_iff.mp hp2
  by_contra h1
  have h3 : p % 4 = 3 := by omega
  obtain ⟨e, f, -, he, hf, -⟩ := FaceLeech.diagonals h
  have H := IsFaceCuboid.support_shape_three_mod_four hp he hf hg pp h3
  unfold FaceShape3 at H
  tauto

/-- Face cuboid: a prime dividing the space diagonal and the common leg `c` divides neither `a`
nor `b` (support `{c, g}`). -/
theorem IsFaceCuboid.dvd_space_diagonal_dvd_c {a b c : ℕ} (h : IsFaceCuboid a b c)
    (hp : Nat.gcd (Nat.gcd a b) c = 1) {g : ℕ} (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) {p : ℕ}
    (pp : p.Prime) (hpg : p ∣ g) (hpc : p ∣ c) : ¬ p ∣ a ∧ ¬ p ∣ b := by
  obtain ⟨e, f, -, he, hf, -⟩ := FaceLeech.diagonals h
  have H := IsFaceCuboid.support_shape hp he hf hg pp
  unfold FaceShape at H
  tauto

/-! ### Euler bricks -/

/-- **Shape classification for Euler bricks.** For a primitive Euler brick and any prime `p`, the
set of the six lengths divisible by `p` is one of the 17 shapes of `Support.BrickShape`. -/
theorem IsEulerBrick.support_shape {a b c : ℕ} (hp : Nat.gcd a (Nat.gcd b c) = 1) {d e f : ℕ}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    {p : ℕ} (pp : p.Prime) :
    BrickShape (p ∣ a) (p ∣ b) (p ∣ c) (p ∣ d) (p ∣ e) (p ∣ f) := by
  obtain ⟨r1, r2, r3⟩ := rel hd pp
  obtain ⟨r4, r5, r6⟩ := rel he pp
  obtain ⟨r7, r8, r9⟩ := rel hf pp
  exact brickShape_of_closure r1 r2 r3 r4 r5 r6 r7 r8 r9 (not_dvd_three hp pp)

/-- The Euler brick `(19175, 293832, 112320)` (face diagonals `294457 = 17·17321`, `113945`,
`314568 = 2³·3²·17·257`). -/
theorem Support.isEulerBrick_19175_293832_112320 : IsEulerBrick 19175 293832 112320 where
  pos_a := by norm_num
  pos_b := by norm_num
  pos_c := by norm_num
  sq_ab := ⟨294457, by norm_num⟩
  sq_bc := ⟨314568, by norm_num⟩
  sq_ca := ⟨113945, by norm_num⟩

/-- The shape `{d, f}` is realized: `17` divides exactly the face diagonals `d` and `f` of the
brick `(19175, 293832, 112320)`. -/
theorem Support.brick_shape_df :
    ¬ 17 ∣ 19175 ∧ ¬ 17 ∣ 293832 ∧ ¬ 17 ∣ 112320 ∧ 17 ∣ 294457 ∧ ¬ 17 ∣ 113945 ∧
      17 ∣ 314568 := by
  decide

/-- The shape `{c, d}` is realized: `5` divides exactly `c = 240` and `d = 125` of the brick
`(44, 117, 240)` (`e = 244`, `f = 267`). In a perfect cuboid this would extend to `{c, d, g}`. -/
theorem Support.brick_shape_cd :
    ¬ 5 ∣ 44 ∧ ¬ 5 ∣ 117 ∧ 5 ∣ 240 ∧ 5 ∣ 125 ∧ ¬ 5 ∣ 244 ∧ ¬ 5 ∣ 267 := by
  decide

/-- The face cuboid `(264, 952, 495)` (`e = 561`, `f = 1073`, `g = 1105`). -/
theorem Support.isFaceCuboid_264_952_495 : IsFaceCuboid 264 952 495 where
  pos_a := by norm_num
  pos_b := by norm_num
  pos_c := by norm_num
  sq_ac := ⟨561, by norm_num⟩
  sq_bc := ⟨1073, by norm_num⟩
  sq_abc := ⟨1105, by norm_num⟩

/-- The face-cuboid shape `{c, g}` is realized: `5` divides exactly `c = 495` and `g = 1105` of
the face cuboid `(264, 952, 495)`; and in `(153, 672, 104)` (`e = 185`, `f = 680`, `g = 697`)
`17` has shape `{a, f, g}` and `5` has shape `{e, f}`. -/
theorem Support.face_shapes :
    (¬ 5 ∣ 264 ∧ ¬ 5 ∣ 952 ∧ 5 ∣ 495 ∧ ¬ 5 ∣ 561 ∧ ¬ 5 ∣ 1073 ∧ 5 ∣ 1105) ∧
    (17 ∣ 153 ∧ ¬ 17 ∣ 672 ∧ ¬ 17 ∣ 104 ∧ ¬ 17 ∣ 185 ∧ 17 ∣ 680 ∧ 17 ∣ 697) ∧
    (¬ 5 ∣ 153 ∧ ¬ 5 ∣ 672 ∧ ¬ 5 ∣ 104 ∧ 5 ∣ 185 ∧ 5 ∣ 680 ∧ ¬ 5 ∣ 697) := by
  decide

end PerfectCuboid
