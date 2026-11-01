module

public import Mathlib
public import LeanPlayground.PerfectCuboid.TwistRigidity
public import LeanPlayground.PerfectCuboid.ConjugateBox
public import LeanPlayground.PerfectCuboid.FaceCuboid
public import LeanPlayground.PerfectCuboid.NearMissTwist
public import LeanPlayground.PerfectCuboid.SpaceDiagonal

/-!
# Perfect cuboids over quadratic rings `ℤ√d`

A *perfect cuboid over `ℤ√d`* (`IsQuadCuboid d a b c`) is a triple of nonzero elements
`a, b, c ∈ ℤ√d` such that the four sums `a² + b²`, `a² + c²`, `b² + c²`, `a² + b² + c²` are squares
of **nonzero** elements of `ℤ√d`. (The nonzero conditions matter: over `ℤ[i]` the triple
`(3i, 4i, 5)` has three nonzero square faces and `a² + b² + c² = 0`.)

## Main results

* `isSquare_intCast_iff`, `isSquare_intCast_iff_ne`: an integer `s` is a square in `ℤ√d` iff
  `s = y²` or `s = d y²` (with `y ≠ 0` for a nonzero root). No hypothesis on `d`.
* `twists_of_isQuadCuboid`, `isQuadCuboid_of_twists`: a *rational-edged* `ℤ√d`-cuboid `(A, B, C)`
  (`A, B, C ∈ ℕ`) is exactly a box with `uᵢ Xᵢ² = Sᵢ`, `uᵢ ∈ {1, d}`, `Xᵢ ≠ 0`.
* `classification` (**classification of rational-edged `ℤ√d`-cuboids**): for squarefree `d ≠ 1`
  at most two of the `uᵢ` equal `d` (this is `TwistRigidity.twist_rigidity`);
  `classification'`: the readable 11-way form — a perfect cuboid, a face cuboid with twist `d`
  in one of three positions, an Euler brick with space twist `d`, a `d`-conjugate box (three
  positions) or a `d`-half-twisted box (three positions). Conversely each of these objects is a
  `ℤ√d`-cuboid (`isQuadCuboid_of_isFaceCuboid`, `isQuadCuboid_of_isEulerBrick`,
  `isQuadCuboid_of_isConjugateBox`, `isQuadCuboid_of_isHalfTwistedBox`,
  `isQuadCuboid_of_isPerfectCuboid`).
* `sq_add_sq_eq_mul_sq`: if a prime `p ≡ 3 (mod 4)` divides the squarefree `d`, then
  `A² + B² = d X²` forces `A = B = X = 0` (infinite descent).
* `three_mod_four`: if some prime `p ≡ 3 (mod 4)` divides the squarefree `d`, every
  rational-edged `ℤ√d`-cuboid is a perfect cuboid over `ℤ`; `neg`: the same for every `d < 0`
  (no squarefree hypothesis), in particular over the Gaussian integers (`gauss`); corollaries
  `three` and `of_mem_small` (`d ∈ {3, 6, 7, 11, 14, 15, 19, 21, 22, 23}`).
* `dvd_of_sq_dvd_mul_sq`, `isQuadCuboid_of_mul`: a common factor of the edges can be divided
  out (`g² ∣ u D²`, `u` squarefree, gives `g ∣ D`).
* `two`: a primitive rational-edged `ℤ√2`-cuboid is a perfect cuboid, a face cuboid whose
  non-square face is `2X²`, or a half-twisted box with `k = 2`. The brick pattern dies by
  `IsEulerBrick.space_twist_mod_24` (`2 ≢ 1 mod 24`), the conjugate-box patterns by
  `IsConjugateBox.prime_mod_eight` (`2 ≢ 1 mod 8`). **Both surviving patterns are open**: no
  face cuboid with twist `2` is known (the 126 known primitive face cuboids have composite
  twist), and half-twisted `k = 2` is not excluded by any congruence because of the degenerate
  box `(a, a, 0)`. `two'` drops the primitivity hypothesis by dividing out `gcd(A, B, C)`.
* Examples: `isQuadCuboid_brick_2929` (Halcke's brick `(44, 117, 240)` is a `ℤ√2929`-cuboid,
  `44² + 117² + 240² = 2929 · 5²`) and `isQuadCuboid_face_52777` (the face cuboid
  `(153, 672, 104)` is a `ℤ√52777`-cuboid, `153² + 672² = 52777 · 3²`), with
  `squarefree_2929`, `squarefree_52777`; `gauss_degenerate`: `(3i, 4i, 5)` over `ℤ[i]` has three
  nonzero square faces and space sum `0`.

Edges are cast `ℕ → ℤ√d` directly; `((A : ℤ) : ℤ√d) = (A : ℤ√d)` is `Int.cast_natCast`.

So rational-edged cuboids over quadratic rings are *exactly* the twisted near-miss objects of
the twist framework; nothing new can be found with rational edges. Cuboids with irrational edges
are a different question (see the round-15 report, brief 1).
-/

@[expose] public section

namespace PerfectCuboid.Quad

open PerfectCuboid.ConjugateBox

/-- A perfect cuboid over `ℤ√d`: nonzero edges and four sums that are squares of nonzero
elements. -/
structure IsQuadCuboid (d : ℤ) (a b c : ℤ√d) : Prop where
  ne_a : a ≠ 0
  ne_b : b ≠ 0
  ne_c : c ≠ 0
  sq_ab : ∃ x : ℤ√d, x ≠ 0 ∧ x * x = a * a + b * b
  sq_ac : ∃ x : ℤ√d, x ≠ 0 ∧ x * x = a * a + c * c
  sq_bc : ∃ x : ℤ√d, x ≠ 0 ∧ x * x = b * b + c * c
  sq_abc : ∃ x : ℤ√d, x ≠ 0 ∧ x * x = a * a + b * b + c * c

/-! ### Q1: integer squares in `ℤ√d` -/

/-- An integer is a square in `ℤ√d` iff it is `y²` or `d y²`. -/
theorem isSquare_intCast_iff (d s : ℤ) :
    (∃ x : ℤ√d, x * x = s) ↔ (∃ y : ℤ, s = y ^ 2) ∨ (∃ y : ℤ, s = d * y ^ 2) := by
  constructor
  · rintro ⟨x, hx⟩
    have hre := congrArg Zsqrtd.re hx
    have him := congrArg Zsqrtd.im hx
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast] at hre him
    have h0 : x.re * x.im = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h | h
    · right; exact ⟨x.im, by rw [← hre, h]; ring⟩
    · left; exact ⟨x.re, by rw [← hre, h]; ring⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨⟨y, 0⟩, by rw [Zsqrtd.intCast_val]; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring⟩
    · exact ⟨⟨0, y⟩, by rw [Zsqrtd.intCast_val]; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring⟩

/-- Nonzero version of `isSquare_intCast_iff`. -/
theorem isSquare_intCast_iff_ne (d s : ℤ) :
    (∃ x : ℤ√d, x ≠ 0 ∧ x * x = s) ↔
      (∃ y : ℤ, y ≠ 0 ∧ s = y ^ 2) ∨ (∃ y : ℤ, y ≠ 0 ∧ s = d * y ^ 2) := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    have hre := congrArg Zsqrtd.re hx
    have him := congrArg Zsqrtd.im hx
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast] at hre him
    have h0 : x.re * x.im = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h | h
    · right
      refine ⟨x.im, fun him0 ↦ hx0 (Zsqrtd.ext h him0), by rw [← hre, h]; ring⟩
    · left
      refine ⟨x.re, fun hre0 ↦ hx0 (Zsqrtd.ext hre0 h), by rw [← hre, h]; ring⟩
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · refine ⟨⟨y, 0⟩, fun h ↦ hy (congrArg Zsqrtd.re h), ?_⟩
      rw [Zsqrtd.intCast_val]; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring
    · refine ⟨⟨0, y⟩, fun h ↦ hy (congrArg Zsqrtd.im h), ?_⟩
      rw [Zsqrtd.intCast_val]; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring

/-! ### Rational-edged cuboids and twists -/

theorem natCast_sum2 {d : ℤ} (A B : ℕ) :
    (A : ℤ√d) * A + (B : ℤ√d) * B = ((A ^ 2 + B ^ 2 : ℕ) : ℤ√d) := by
  push_cast; ring

theorem natCast_sum3 {d : ℤ} (A B C : ℕ) :
    (A : ℤ√d) * A + (B : ℤ√d) * B + (C : ℤ√d) * C = ((A ^ 2 + B ^ 2 + C ^ 2 : ℕ) : ℤ√d) := by
  push_cast; ring

/-- A natural number that is a nonzero square in `ℤ√d` (`d ∈ ℕ`) is `u D²` with `u ∈ {1, d}`,
`D ≠ 0`. -/
theorem twist_nat {d S : ℕ} (h : ∃ x : ℤ√(d : ℤ), x ≠ 0 ∧ x * x = (S : ℤ√(d : ℤ))) :
    ∃ u D : ℕ, (u = 1 ∨ u = d) ∧ D ≠ 0 ∧ u * D ^ 2 = S := by
  have h' : ∃ x : ℤ√(d : ℤ), x ≠ 0 ∧ x * x = ((S : ℤ) : ℤ√(d : ℤ)) := by
    simpa only [Int.cast_natCast] using h
  rcases (isSquare_intCast_iff_ne _ _).1 h' with ⟨y, hy, hs⟩ | ⟨y, hy, hs⟩
  · refine ⟨1, y.natAbs, Or.inl rfl, by simpa using hy, ?_⟩
    zify; rw [sq_abs]; linarith
  · refine ⟨d, y.natAbs, Or.inr rfl, by simpa using hy, ?_⟩
    zify; rw [sq_abs]; linarith

/-- Conversely, `u D²` with `u ∈ {1, d}` and `D ≠ 0` is a nonzero square in `ℤ√d`. -/
theorem sq_of_twist {d u D S : ℕ} (hu : u = 1 ∨ u = d) (hD : D ≠ 0) (h : u * D ^ 2 = S) :
    ∃ x : ℤ√(d : ℤ), x ≠ 0 ∧ x * x = (S : ℤ√(d : ℤ)) := by
  have h' : ∃ x : ℤ√(d : ℤ), x ≠ 0 ∧ x * x = ((S : ℤ) : ℤ√(d : ℤ)) := by
    apply (isSquare_intCast_iff_ne _ _).2
    rcases hu with rfl | rfl
    · left; exact ⟨D, by exact_mod_cast hD, by rw [← h]; push_cast; ring⟩
    · right; exact ⟨D, by exact_mod_cast hD, by rw [← h]; push_cast; ring⟩
  simpa only [Int.cast_natCast] using h'

/-- The twists of a rational-edged `ℤ√d`-cuboid. -/
theorem twists_of_isQuadCuboid {d A B C : ℕ}
    (h : IsQuadCuboid d (A : ℤ√(d : ℤ)) (B : ℤ√(d : ℤ)) (C : ℤ√(d : ℤ))) :
    ∃ u₁ u₂ u₃ u₄ D E F G : ℕ, (u₁ = 1 ∨ u₁ = d) ∧ (u₂ = 1 ∨ u₂ = d) ∧ (u₃ = 1 ∨ u₃ = d) ∧
      (u₄ = 1 ∨ u₄ = d) ∧ D ≠ 0 ∧ E ≠ 0 ∧ F ≠ 0 ∧ G ≠ 0 ∧
      u₁ * D ^ 2 = A ^ 2 + B ^ 2 ∧ u₂ * E ^ 2 = A ^ 2 + C ^ 2 ∧ u₃ * F ^ 2 = B ^ 2 + C ^ 2 ∧
      u₄ * G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2 := by
  obtain ⟨u₁, D, h1, hD0, hD⟩ := twist_nat (by rw [← natCast_sum2]; exact h.sq_ab)
  obtain ⟨u₂, E, h2, hE0, hE⟩ := twist_nat (by rw [← natCast_sum2]; exact h.sq_ac)
  obtain ⟨u₃, F, h3, hF0, hF⟩ := twist_nat (by rw [← natCast_sum2]; exact h.sq_bc)
  obtain ⟨u₄, G, h4, hG0, hG⟩ := twist_nat (by rw [← natCast_sum3]; exact h.sq_abc)
  exact ⟨u₁, u₂, u₃, u₄, D, E, F, G, h1, h2, h3, h4, hD0, hE0, hF0, hG0, hD, hE, hF, hG⟩

/-- Every box with twists in `{1, d}` and positive edges is a rational-edged `ℤ√d`-cuboid. -/
theorem isQuadCuboid_of_twists {d A B C u₁ u₂ u₃ u₄ D E F G : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hu₁ : u₁ = 1 ∨ u₁ = d) (hu₂ : u₂ = 1 ∨ u₂ = d) (hu₃ : u₃ = 1 ∨ u₃ = d)
    (hu₄ : u₄ = 1 ∨ u₄ = d) (hD0 : D ≠ 0) (hE0 : E ≠ 0) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hD : u₁ * D ^ 2 = A ^ 2 + B ^ 2) (hE : u₂ * E ^ 2 = A ^ 2 + C ^ 2)
    (hF : u₃ * F ^ 2 = B ^ 2 + C ^ 2) (hG : u₄ * G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2) :
    IsQuadCuboid d (A : ℤ√(d : ℤ)) (B : ℤ√(d : ℤ)) (C : ℤ√(d : ℤ)) where
  ne_a := by exact_mod_cast hA.ne'
  ne_b := by exact_mod_cast hB.ne'
  ne_c := by exact_mod_cast hC.ne'
  sq_ab := by rw [natCast_sum2]; exact sq_of_twist hu₁ hD0 hD
  sq_ac := by rw [natCast_sum2]; exact sq_of_twist hu₂ hE0 hE
  sq_bc := by rw [natCast_sum2]; exact sq_of_twist hu₃ hF0 hF
  sq_abc := by rw [natCast_sum3]; exact sq_of_twist hu₄ hG0 hG

/-! ### Q2: classification -/

/-- **Classification of rational-edged `ℤ√d`-cuboids.** For squarefree `d ≠ 1` the four sums
have twists `uᵢ ∈ {1, d}` and at most two of them equal `d`. -/
theorem classification {d A B C : ℕ} (hd : Squarefree d) (hd1 : d ≠ 1) (hA : 0 < A)
    (h : IsQuadCuboid d (A : ℤ√(d : ℤ)) (B : ℤ√(d : ℤ)) (C : ℤ√(d : ℤ))) :
    ∃ u₁ u₂ u₃ u₄ D E F G : ℕ, (u₁ = 1 ∨ u₁ = d) ∧ (u₂ = 1 ∨ u₂ = d) ∧ (u₃ = 1 ∨ u₃ = d) ∧
      (u₄ = 1 ∨ u₄ = d) ∧ D ≠ 0 ∧ E ≠ 0 ∧ F ≠ 0 ∧ G ≠ 0 ∧
      u₁ * D ^ 2 = A ^ 2 + B ^ 2 ∧ u₂ * E ^ 2 = A ^ 2 + C ^ 2 ∧ u₃ * F ^ 2 = B ^ 2 + C ^ 2 ∧
      u₄ * G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2 ∧
      ¬ ((u₁ = d ∧ u₂ = d ∧ u₃ = d) ∨ (u₁ = d ∧ u₂ = d ∧ u₄ = d) ∨
        (u₁ = d ∧ u₃ = d ∧ u₄ = d) ∨ (u₂ = d ∧ u₃ = d ∧ u₄ = d)) := by
  obtain ⟨u₁, u₂, u₃, u₄, D, E, F, G, h1, h2, h3, h4, hD0, hE0, hF0, hG0, hD, hE, hF, hG⟩ :=
    twists_of_isQuadCuboid h
  refine ⟨u₁, u₂, u₃, u₄, D, E, F, G, h1, h2, h3, h4, hD0, hE0, hF0, hG0, hD, hE, hF, hG, ?_⟩
  intro h3d
  exact hd1 (TwistRigidity.twist_rigidity hd h1 h2 h3 h4 h3d (Or.inl hA.ne') hD hE hF hG)

theorem isSquare_of_one_mul {D S : ℕ} (h : 1 * D ^ 2 = S) : IsSquare S :=
  ⟨D, by rw [← h]; ring⟩

/-- **Classification, readable form.** A rational-edged `ℤ√d`-cuboid (`d` squarefree, `d ≠ 1`)
is one of: a perfect cuboid; a face cuboid whose non-square face is `d X²` (three positions);
an Euler brick with space sum `d X²`; a `d`-conjugate box (three positions: the edge shared by
the two twisted faces comes first); a `d`-half-twisted box (three positions). -/
theorem classification' {d A B C : ℕ} (hd : Squarefree d) (hd1 : d ≠ 1) (hA : 0 < A)
    (hB : 0 < B) (hC : 0 < C)
    (h : IsQuadCuboid d (A : ℤ√(d : ℤ)) (B : ℤ√(d : ℤ)) (C : ℤ√(d : ℤ))) :
    IsPerfectCuboid A B C ∨
    (∃ X, d * X ^ 2 = A ^ 2 + B ^ 2 ∧ IsFaceCuboid A B C) ∨
    (∃ X, d * X ^ 2 = A ^ 2 + C ^ 2 ∧ IsFaceCuboid A C B) ∨
    (∃ X, d * X ^ 2 = B ^ 2 + C ^ 2 ∧ IsFaceCuboid B C A) ∨
    (∃ X, d * X ^ 2 = A ^ 2 + B ^ 2 + C ^ 2 ∧ IsEulerBrick A B C) ∨
    (∃ D E F G, IsConjugateBox d A B C D E F G) ∨
    (∃ D E F G, IsConjugateBox d B A C D F E G) ∨
    (∃ D E F G, IsConjugateBox d C A B E F D G) ∨
    (∃ D E F G, IsHalfTwistedBox d A B C D E F G) ∨
    (∃ D E F G, IsHalfTwistedBox d A C B E D F G) ∨
    (∃ D E F G, IsHalfTwistedBox d B C A F D E G) := by
  obtain ⟨u₁, u₂, u₃, u₄, D, E, F, G, h1, h2, h3, h4, -, -, -, -, hD, hE, hF, hG, hmax⟩ :=
    classification hd hd1 hA h
  rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2 <;> rcases h3 with e3 | e3 <;>
    rcases h4 with e4 | e4 <;> rw [e1] at hD <;> rw [e2] at hE <;> rw [e3] at hF <;>
    rw [e4] at hG
  -- (1,1,1,1)
  · left
    exact ⟨⟨hA, hB, hC, isSquare_of_one_mul hD, isSquare_of_one_mul hF,
      isSquare_of_one_mul (D := E) (by linarith)⟩, isSquare_of_one_mul hG⟩
  -- (1,1,1,d): brick
  · right; right; right; right; left
    exact ⟨G, hG, hA, hB, hC, isSquare_of_one_mul hD, isSquare_of_one_mul hF,
      isSquare_of_one_mul (D := E) (by linarith)⟩
  -- (1,1,d,1): face, B² + C² twisted
  · right; right; right; left
    exact ⟨F, hF, hB, hC, hA, isSquare_of_one_mul (D := D) (by linarith),
      isSquare_of_one_mul (D := E) (by linarith), isSquare_of_one_mul (D := G) (by linarith)⟩
  -- (1,1,d,d): half-twisted on B² + C²
  · right; right; right; right; right; right; right; right; right; right
    exact ⟨D, E, F, G, hB, hC, hA, hd, hF, by linarith, by linarith, by linarith⟩
  -- (1,d,1,1): face, A² + C² twisted
  · right; right; left
    exact ⟨E, hE, hA, hC, hB, isSquare_of_one_mul hD,
      isSquare_of_one_mul (D := F) (by linarith), isSquare_of_one_mul (D := G) (by linarith)⟩
  -- (1,d,1,d): half-twisted on A² + C²
  · right; right; right; right; right; right; right; right; right; left
    exact ⟨D, E, F, G, hA, hC, hB, hd, hE, by linarith, by linarith, by linarith⟩
  -- (1,d,d,1): conjugate, shared edge C
  · right; right; right; right; right; right; right; left
    exact ⟨D, E, F, G, hC, hA, hB, hd, by linarith, by linarith, by linarith, by linarith⟩
  · exact (hmax (by tauto)).elim
  -- (d,1,1,1): face, A² + B² twisted
  · right; left
    exact ⟨D, hD, hA, hB, hC, isSquare_of_one_mul hE, isSquare_of_one_mul hF,
      isSquare_of_one_mul hG⟩
  -- (d,1,1,d): half-twisted on A² + B²
  · right; right; right; right; right; right; right; right; left
    exact ⟨D, E, F, G, hA, hB, hC, hd, hD, by linarith, by linarith, hG⟩
  -- (d,1,d,1): conjugate, shared edge B
  · right; right; right; right; right; right; left
    exact ⟨D, E, F, G, hB, hA, hC, hd, by linarith, by linarith, by linarith, by linarith⟩
  · exact (hmax (by tauto)).elim
  -- (d,d,1,1): conjugate, shared edge A
  · right; right; right; right; right; left
    exact ⟨D, E, F, G, hA, hB, hC, hd, hD, hE, by linarith, by linarith⟩
  · exact (hmax (by tauto)).elim
  · exact (hmax (by tauto)).elim
  · exact (hmax (by tauto)).elim

/-! ### Converses: the twisted near-miss objects are `ℤ√d`-cuboids -/

theorem one_mul_of_isSquare {S : ℕ} (h : IsSquare S) (hS : 0 < S) :
    ∃ D : ℕ, D ≠ 0 ∧ 1 * D ^ 2 = S := by
  obtain ⟨D, rfl⟩ := h
  exact ⟨D, by rintro rfl; simp at hS, by ring⟩

theorem ne_zero_of_mul_sq {u D S : ℕ} (hS : 0 < S) (h : u * D ^ 2 = S) : D ≠ 0 := by
  rintro rfl
  rw [← h] at hS
  simp at hS

theorem isQuadCuboid_of_isPerfectCuboid {A B C : ℕ} (h : IsPerfectCuboid A B C) (d : ℤ) :
    IsQuadCuboid d (A : ℤ√d) (B : ℤ√d) (C : ℤ√d) := by
  have hA := h.pos_a; have hB := h.pos_b; have hC := h.pos_c
  refine ⟨by exact_mod_cast hA.ne', by exact_mod_cast hB.ne', by exact_mod_cast hC.ne', ?_, ?_,
    ?_, ?_⟩
  · obtain ⟨D, hD, hD'⟩ := one_mul_of_isSquare h.sq_ab (by positivity)
    exact ⟨D, by exact_mod_cast hD, by rw [natCast_sum2, ← hD']; push_cast; ring⟩
  · obtain ⟨D, hD, hD'⟩ := one_mul_of_isSquare h.sq_ca (by positivity)
    exact ⟨D, by exact_mod_cast hD,
      by rw [natCast_sum2, ← add_comm (C ^ 2), ← hD']; push_cast; ring⟩
  · obtain ⟨D, hD, hD'⟩ := one_mul_of_isSquare h.sq_bc (by positivity)
    exact ⟨D, by exact_mod_cast hD, by rw [natCast_sum2, ← hD']; push_cast; ring⟩
  · obtain ⟨D, hD, hD'⟩ := one_mul_of_isSquare h.sq_abc (by positivity)
    exact ⟨D, by exact_mod_cast hD, by rw [natCast_sum3, ← hD']; push_cast; ring⟩

/-- An Euler brick with `s r² = a² + b² + c²` is a `ℤ√s`-cuboid. -/
theorem isQuadCuboid_of_isEulerBrick {A B C s r : ℕ} (h : IsEulerBrick A B C)
    (hr : s * r ^ 2 = A ^ 2 + B ^ 2 + C ^ 2) :
    IsQuadCuboid s (A : ℤ√(s : ℤ)) (B : ℤ√(s : ℤ)) (C : ℤ√(s : ℤ)) := by
  have hA := h.pos_a; have hB := h.pos_b; have hC := h.pos_c
  obtain ⟨D, hD0, hD⟩ := one_mul_of_isSquare h.sq_ab (by positivity)
  obtain ⟨E, hE0, hE⟩ := one_mul_of_isSquare h.sq_ca (by positivity)
  obtain ⟨F, hF0, hF⟩ := one_mul_of_isSquare h.sq_bc (by positivity)
  have hr0 : r ≠ 0 := ne_zero_of_mul_sq (by positivity) hr
  exact isQuadCuboid_of_twists hA hB hC (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
    hD0 hE0 hF0 hr0 hD (by linarith) hF hr

/-- A face cuboid with `s r² = a² + b²` (the non-square face) is a `ℤ√s`-cuboid. -/
theorem isQuadCuboid_of_isFaceCuboid {A B C s r : ℕ} (h : IsFaceCuboid A B C)
    (hr : s * r ^ 2 = A ^ 2 + B ^ 2) :
    IsQuadCuboid s (A : ℤ√(s : ℤ)) (B : ℤ√(s : ℤ)) (C : ℤ√(s : ℤ)) := by
  have hA := h.pos_a; have hB := h.pos_b; have hC := h.pos_c
  obtain ⟨E, hE0, hE⟩ := one_mul_of_isSquare h.sq_ac (by positivity)
  obtain ⟨F, hF0, hF⟩ := one_mul_of_isSquare h.sq_bc (by positivity)
  obtain ⟨G, hG0, hG⟩ := one_mul_of_isSquare h.sq_abc (by positivity)
  have hr0 : r ≠ 0 := ne_zero_of_mul_sq (by positivity) hr
  exact isQuadCuboid_of_twists hA hB hC (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    hr0 hE0 hF0 hG0 hr hE hF hG

theorem isQuadCuboid_of_isConjugateBox {k A B C D E F G : ℕ}
    (h : IsConjugateBox k A B C D E F G) :
    IsQuadCuboid k (A : ℤ√(k : ℤ)) (B : ℤ√(k : ℤ)) (C : ℤ√(k : ℤ)) := by
  have hA := h.pos_a; have hB := h.pos_b; have hC := h.pos_c
  have hD := h.hd; have hE := h.he; have hF := h.hf; have hG := h.hg
  have hk : k ≠ 0 := h.sqfree.ne_zero
  refine isQuadCuboid_of_twists hA hB hC (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
    (D := D) (E := E) (F := F) (G := G) ?_ ?_ ?_ ?_ hD hE (by linarith) (by linarith)
  · exact ne_zero_of_mul_sq (by positivity) hD
  · exact ne_zero_of_mul_sq (by positivity) hE
  · exact ne_zero_of_mul_sq (u := 1) (S := B ^ 2 + C ^ 2) (by positivity)
      (by rw [one_mul]; exact hF)
  · exact ne_zero_of_mul_sq (u := 1) (S := A ^ 2 + B ^ 2 + C ^ 2) (by positivity)
      (by rw [one_mul]; exact hG)

theorem isQuadCuboid_of_isHalfTwistedBox {k A B C D E F G : ℕ}
    (h : IsHalfTwistedBox k A B C D E F G) :
    IsQuadCuboid k (A : ℤ√(k : ℤ)) (B : ℤ√(k : ℤ)) (C : ℤ√(k : ℤ)) := by
  have hA := h.pos_a; have hB := h.pos_b; have hC := h.pos_c
  have hD := h.hd; have hE := h.he; have hF := h.hf; have hG := h.hg
  refine isQuadCuboid_of_twists hA hB hC (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
    (D := D) (E := E) (F := F) (G := G) ?_ ?_ ?_ ?_ hD (by linarith) (by linarith) hG
  · exact ne_zero_of_mul_sq (by positivity) hD
  · exact ne_zero_of_mul_sq (u := 1) (S := A ^ 2 + C ^ 2) (by positivity)
      (by rw [one_mul]; exact hE)
  · exact ne_zero_of_mul_sq (u := 1) (S := B ^ 2 + C ^ 2) (by positivity)
      (by rw [one_mul]; exact hF)
  · exact ne_zero_of_mul_sq (by positivity) hG

/-! ### Examples -/

/-- Halcke's brick `(44, 117, 240)` is a `ℤ√2929`-cuboid: `44² + 117² + 240² = 73225 = 2929·5²`. -/
theorem isQuadCuboid_brick_2929 :
    IsQuadCuboid 2929 ((44 : ℕ) : ℤ√2929) ((117 : ℕ) : ℤ√2929) ((240 : ℕ) : ℤ√2929) :=
  isQuadCuboid_of_isEulerBrick (s := 2929) (r := 5) eulerBrick_44_117_240 (by norm_num)

/-- The face cuboid `(153, 672, 104)` is a `ℤ√52777`-cuboid: `153² + 672² = 52777 · 3²`. -/
theorem isQuadCuboid_face_52777 :
    IsQuadCuboid 52777 ((153 : ℕ) : ℤ√52777) ((672 : ℕ) : ℤ√52777) ((104 : ℕ) : ℤ√52777) :=
  isQuadCuboid_of_isFaceCuboid (s := 52777) (r := 3) isFaceCuboid_153_672_104 (by norm_num)

/-- The space twist `2929 = 29 · 101` of Halcke's brick is squarefree. -/
theorem squarefree_2929 : Squarefree 2929 := by
  rw [show (2929 : ℕ) = 29 * 101 by norm_num, Nat.squarefree_mul_iff]
  exact ⟨by norm_num, (by norm_num : Nat.Prime 29).squarefree,
    (by norm_num : Nat.Prime 101).squarefree⟩

/-- The twist `52777 = 89 · 593` of the face cuboid `(153, 672, 104)` is squarefree. -/
theorem squarefree_52777 : Squarefree 52777 := by
  rw [show (52777 : ℕ) = 89 * 593 by norm_num, Nat.squarefree_mul_iff]
  exact ⟨by norm_num, (by norm_num : Nat.Prime 89).squarefree,
    (by norm_num : Nat.Prime 593).squarefree⟩

/-- Why the nonzero conditions are needed: over `ℤ[i]` the triple `(3i, 4i, 5)` has three
nonzero square faces, `-25 = (5i)²`, `16 = 4²`, `9 = 3²`, but `a² + b² + c² = 0`. -/
theorem gauss_degenerate :
    let a : ℤ√(-1) := ⟨0, 3⟩
    let b : ℤ√(-1) := ⟨0, 4⟩
    let c : ℤ√(-1) := 5
    a * a + b * b = ⟨0, 5⟩ * ⟨0, 5⟩ ∧ a * a + c * c = 4 * 4 ∧ b * b + c * c = 3 * 3 ∧
      a * a + b * b + c * c = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]

/-! ### Q3: primes `≡ 3 (mod 4)` and negative `d` -/

/-- **Descent.** If a prime `p ≡ 3 (mod 4)` divides the squarefree `d`, then `A² + B² = d X²`
only for `A = B = X = 0`. -/
theorem sq_add_sq_eq_mul_sq {p d : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (hpd : p ∣ d)
    (hd : Squarefree d) {A B X : ℕ} (h : A ^ 2 + B ^ 2 = d * X ^ 2) :
    A = 0 ∧ B = 0 ∧ X = 0 := by
  induction X using Nat.strong_induction_on generalizing A B with
  | _ X ih =>
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · have h' : A = 0 ∧ B = 0 := by simpa using h
    exact ⟨h'.1, h'.2, rfl⟩
  · exfalso
    have h1 : p ∣ A ^ 2 + B ^ 2 := h ▸ dvd_mul_of_dvd_left hpd _
    obtain ⟨hA, hB⟩ := prime_dvd_both_of_dvd_sq_add_sq hp hp3 h1
    obtain ⟨A', rfl⟩ := hA
    obtain ⟨B', rfl⟩ := hB
    have h2 : p ^ 2 ∣ d * X ^ 2 := by rw [← h]; exact ⟨A' ^ 2 + B' ^ 2, by ring⟩
    obtain ⟨X', rfl⟩ := TwistRigidity.dvd_of_sq_dvd_mul hp hd h2
    have hp0 : 0 < p := hp.pos
    have h3 : A' ^ 2 + B' ^ 2 = d * X' ^ 2 := by
      have : p ^ 2 * (A' ^ 2 + B' ^ 2) = p ^ 2 * (d * X' ^ 2) := by
        calc p ^ 2 * (A' ^ 2 + B' ^ 2) = (p * A') ^ 2 + (p * B') ^ 2 := by ring
          _ = d * (p * X') ^ 2 := h
          _ = p ^ 2 * (d * X' ^ 2) := by ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    have hX' : 0 < X' := Nat.pos_of_mul_pos_left hX
    have hlt : X' < p * X' := by nlinarith [hp.two_le]
    obtain ⟨-, -, h0⟩ := ih X' hlt h3
    omega

/-- If a prime `p ≡ 3 (mod 4)` divides the squarefree `d`, every rational-edged `ℤ√d`-cuboid
is a perfect cuboid over `ℤ`. -/
theorem three_mod_four {d A B C p : ℕ} (hd : Squarefree d) (hp : p.Prime) (hp3 : p % 4 = 3)
    (hpd : p ∣ d) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : IsQuadCuboid d (A : ℤ√(d : ℤ)) (B : ℤ√(d : ℤ)) (C : ℤ√(d : ℤ))) :
    IsPerfectCuboid A B C := by
  obtain ⟨u₁, u₂, u₃, u₄, D, E, F, G, h1, h2, h3, h4, hD0, -, -, -, hD, hE, hF, hG⟩ :=
    twists_of_isQuadCuboid h
  have k : ∀ {X Y Z : ℕ}, 0 < X → X ^ 2 + Y ^ 2 = d * Z ^ 2 → False := fun hX hXYZ ↦ by
    have := (sq_add_sq_eq_mul_sq hp hp3 hpd hd hXYZ).1
    omega
  have e1 : u₁ = 1 := h1.resolve_right fun e ↦ k (Y := B) (Z := D) hA (by rw [e] at hD; linarith)
  have e2 : u₂ = 1 := h2.resolve_right fun e ↦ k (Y := C) (Z := E) hA (by rw [e] at hE; linarith)
  have e3 : u₃ = 1 := h3.resolve_right fun e ↦ k (Y := C) (Z := F) hB (by rw [e] at hF; linarith)
  rw [e1] at hD
  have e4 : u₄ = 1 := h4.resolve_right fun e ↦
    k (X := D) (Y := C) (Z := G) (Nat.pos_of_ne_zero hD0) (by rw [e] at hG; linarith)
  rw [e2] at hE; rw [e3] at hF; rw [e4] at hG
  exact ⟨⟨hA, hB, hC, isSquare_of_one_mul hD, isSquare_of_one_mul hF,
    isSquare_of_one_mul (D := E) (by linarith)⟩, isSquare_of_one_mul hG⟩

/-- A natural number which is a nonzero square in `ℤ√d`, `d < 0`, is a square. -/
theorem isSquare_of_neg {d : ℤ} (hd : d < 0) {S : ℕ} (hS : 0 < S)
    (h : ∃ x : ℤ√d, x ≠ 0 ∧ x * x = (S : ℤ√d)) : IsSquare S := by
  have h' : ∃ x : ℤ√d, x ≠ 0 ∧ x * x = ((S : ℤ) : ℤ√d) := by
    simpa only [Int.cast_natCast] using h
  rcases (isSquare_intCast_iff_ne _ _).1 h' with ⟨y, -, hs⟩ | ⟨y, hy, hs⟩
  · refine ⟨y.natAbs, ?_⟩
    zify; rw [abs_mul_abs_self]; linarith [sq y]
  · exfalso
    have hy2 : 0 < y ^ 2 := by positivity
    have : (0 : ℤ) < S := by exact_mod_cast hS
    nlinarith [mul_neg_of_neg_of_pos hd hy2]

/-- For `d < 0` every rational-edged `ℤ√d`-cuboid is a perfect cuboid over `ℤ`. -/
theorem neg {d : ℤ} (hd : d < 0) {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : IsQuadCuboid d (A : ℤ√d) (B : ℤ√d) (C : ℤ√d)) : IsPerfectCuboid A B C := by
  have hab := isSquare_of_neg hd (S := A ^ 2 + B ^ 2) (by positivity)
    (by rw [← natCast_sum2]; exact h.sq_ab)
  have hac := isSquare_of_neg hd (S := A ^ 2 + C ^ 2) (by positivity)
    (by rw [← natCast_sum2]; exact h.sq_ac)
  have hbc := isSquare_of_neg hd (S := B ^ 2 + C ^ 2) (by positivity)
    (by rw [← natCast_sum2]; exact h.sq_bc)
  have habc := isSquare_of_neg hd (S := A ^ 2 + B ^ 2 + C ^ 2) (by positivity)
    (by rw [← natCast_sum3]; exact h.sq_abc)
  exact ⟨⟨hA, hB, hC, hab, hbc, by rw [add_comm]; exact hac⟩, habc⟩

/-- Squarefree `d ≤ 23` with a prime factor `≡ 3 (mod 4)`: every rational-edged
`ℤ√d`-cuboid is a perfect cuboid. -/
theorem of_mem_small {d A B C : ℕ} (hd : d ∈ ({3, 6, 7, 11, 14, 15, 19, 21, 22, 23} : Finset ℕ))
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : IsQuadCuboid d (A : ℤ√(d : ℤ)) (B : ℤ√(d : ℤ)) (C : ℤ√(d : ℤ))) :
    IsPerfectCuboid A B C := by
  have key : Squarefree d ∧ ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ p ∣ d := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have p3 : Nat.Prime 3 := Nat.prime_three
    have p7 : Nat.Prime 7 := by norm_num
    have p11 : Nat.Prime 11 := by norm_num
    have p19 : Nat.Prime 19 := by norm_num
    have p23 : Nat.Prime 23 := by norm_num
    have p2 := Nat.prime_two
    have p5 : Nat.Prime 5 := by norm_num
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨p3.squarefree, 3, p3, rfl, dvd_rfl⟩
    · refine ⟨?_, 3, p3, rfl, by norm_num⟩
      rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.squarefree_mul_iff]
      exact ⟨by norm_num, p2.squarefree, p3.squarefree⟩
    · exact ⟨p7.squarefree, 7, p7, rfl, dvd_rfl⟩
    · exact ⟨p11.squarefree, 11, p11, rfl, dvd_rfl⟩
    · refine ⟨?_, 7, p7, rfl, by norm_num⟩
      rw [show (14 : ℕ) = 2 * 7 by norm_num, Nat.squarefree_mul_iff]
      exact ⟨by norm_num, p2.squarefree, p7.squarefree⟩
    · refine ⟨?_, 3, p3, rfl, by norm_num⟩
      rw [show (15 : ℕ) = 3 * 5 by norm_num, Nat.squarefree_mul_iff]
      exact ⟨by norm_num, p3.squarefree, p5.squarefree⟩
    · exact ⟨p19.squarefree, 19, p19, rfl, dvd_rfl⟩
    · refine ⟨?_, 3, p3, rfl, by norm_num⟩
      rw [show (21 : ℕ) = 3 * 7 by norm_num, Nat.squarefree_mul_iff]
      exact ⟨by norm_num, p3.squarefree, p7.squarefree⟩
    · refine ⟨?_, 11, p11, rfl, by norm_num⟩
      rw [show (22 : ℕ) = 2 * 11 by norm_num, Nat.squarefree_mul_iff]
      exact ⟨by norm_num, p2.squarefree, p11.squarefree⟩
    · exact ⟨p23.squarefree, 23, p23, rfl, dvd_rfl⟩
  obtain ⟨hsq, p, hp, hp3, hpd⟩ := key
  exact three_mod_four hsq hp hp3 hpd hA hB hC h

/-- `d = 3`: every rational-edged `ℤ√3`-cuboid is a perfect cuboid. -/
theorem three {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : IsQuadCuboid 3 (A : ℤ√3) (B : ℤ√3) (C : ℤ√3)) : IsPerfectCuboid A B C :=
  three_mod_four (d := 3) Nat.prime_three.squarefree Nat.prime_three rfl dvd_rfl hA hB hC h

/-- `d = -1` (Gaussian integers): every rational-edged `ℤ[i]`-cuboid is a perfect cuboid. -/
theorem gauss {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : IsQuadCuboid (-1) (A : ℤ√(-1)) (B : ℤ√(-1)) (C : ℤ√(-1))) : IsPerfectCuboid A B C :=
  neg (by norm_num) hA hB hC h

/-! ### Scaling: removing a common factor -/

/-- If `g² ∣ u D²` with `u` squarefree, then `g ∣ D`. -/
theorem dvd_of_sq_dvd_mul_sq {u : ℕ} (hu : Squarefree u) {g D : ℕ} (h : g ^ 2 ∣ u * D ^ 2) :
    g ∣ D := by
  induction g using Nat.strong_induction_on generalizing D with
  | _ g ih =>
  rcases Nat.lt_or_ge g 2 with hg | hg
  · interval_cases g
    · have h0 : u * D ^ 2 = 0 := by simpa using h
      rcases mul_eq_zero.1 h0 with h0 | h0
      · exact absurd (h0 ▸ hu) not_squarefree_zero
      · simp at h0; simp [h0]
    · exact one_dvd D
  · obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (show g ≠ 1 by omega)
    obtain ⟨g', rfl⟩ := hpg
    have hp2 : p ^ 2 ∣ u * D ^ 2 := dvd_trans (pow_dvd_pow_of_dvd (dvd_mul_right p g') 2) h
    obtain ⟨D', rfl⟩ := TwistRigidity.dvd_of_sq_dvd_mul hp hu hp2
    have hp0 : 0 < p ^ 2 := by have := hp.pos; positivity
    have h' : g' ^ 2 ∣ u * D' ^ 2 := by
      have : p ^ 2 * g' ^ 2 ∣ p ^ 2 * (u * D' ^ 2) := by
        have e1 : (p * g') ^ 2 = p ^ 2 * g' ^ 2 := by ring
        have e2 : u * (p * D') ^ 2 = p ^ 2 * (u * D' ^ 2) := by ring
        rw [← e1, ← e2]; exact h
      exact Nat.dvd_of_mul_dvd_mul_left hp0 this
    have hg' : 0 < g' := by
      rcases Nat.eq_zero_or_pos g' with h0 | h0
      · subst h0; omega
      · exact h0
    have hlt : g' < p * g' := by nlinarith [hp.two_le]
    exact mul_dvd_mul_left p (ih g' hlt h')

theorem twist_div {d u D g S : ℕ} (hd : Squarefree d) (hu : u = 1 ∨ u = d) (hD : D ≠ 0)
    (hg : 0 < g) (h : u * D ^ 2 = g ^ 2 * S) : ∃ D', D' ≠ 0 ∧ u * D' ^ 2 = S := by
  have hus : Squarefree u := by rcases hu with rfl | rfl; exacts [squarefree_one, hd]
  obtain ⟨D', rfl⟩ := dvd_of_sq_dvd_mul_sq hus (D := D) (g := g) ⟨S, by rw [h]⟩
  refine ⟨D', fun h0 ↦ hD (by simp [h0]), ?_⟩
  have hg2 : 0 < g ^ 2 := by positivity
  apply Nat.eq_of_mul_eq_mul_left hg2
  rw [← h]; ring

/-- Dividing a rational-edged `ℤ√d`-cuboid (`d` squarefree) by a common factor of its edges
gives a rational-edged `ℤ√d`-cuboid. -/
theorem isQuadCuboid_of_mul {d g A B C : ℕ} (hd : Squarefree d) (hg : 0 < g)
    (h : IsQuadCuboid d ((g * A : ℕ) : ℤ√(d : ℤ)) ((g * B : ℕ) : ℤ√(d : ℤ))
      ((g * C : ℕ) : ℤ√(d : ℤ))) :
    IsQuadCuboid d (A : ℤ√(d : ℤ)) (B : ℤ√(d : ℤ)) (C : ℤ√(d : ℤ)) := by
  have pos : ∀ {X : ℕ}, ((g * X : ℕ) : ℤ√(d : ℤ)) ≠ 0 → 0 < X := fun {X} hX ↦ by
    rcases Nat.eq_zero_or_pos X with h0 | h0
    · exact absurd (by simp [h0]) hX
    · exact h0
  obtain ⟨u₁, u₂, u₃, u₄, D, E, F, G, h1, h2, h3, h4, hD0, hE0, hF0, hG0, hD, hE, hF, hG⟩ :=
    twists_of_isQuadCuboid h
  obtain ⟨D', hD', hD'e⟩ := twist_div hd h1 hD0 hg (S := A ^ 2 + B ^ 2) (by rw [hD]; ring)
  obtain ⟨E', hE', hE'e⟩ := twist_div hd h2 hE0 hg (S := A ^ 2 + C ^ 2) (by rw [hE]; ring)
  obtain ⟨F', hF', hF'e⟩ := twist_div hd h3 hF0 hg (S := B ^ 2 + C ^ 2) (by rw [hF]; ring)
  obtain ⟨G', hG', hG'e⟩ := twist_div hd h4 hG0 hg (S := A ^ 2 + B ^ 2 + C ^ 2)
    (by rw [hG]; ring)
  exact isQuadCuboid_of_twists (pos h.ne_a) (pos h.ne_b) (pos h.ne_c) h1 h2 h3 h4 hD' hE' hF'
    hG' hD'e hE'e hF'e hG'e

/-! ### Q4: `d = 2` -/

/-- **`d = 2`.** A primitive rational-edged `ℤ√2`-cuboid is a perfect cuboid, a face cuboid
whose non-square face is `2X²` (three positions), or a half-twisted box with `k = 2` (three
positions). Both surviving non-perfect patterns are open. -/
theorem two {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hp : Nat.gcd A (Nat.gcd B C) = 1)
    (h : IsQuadCuboid 2 (A : ℤ√2) (B : ℤ√2) (C : ℤ√2)) :
    IsPerfectCuboid A B C ∨
    (∃ X, 2 * X ^ 2 = A ^ 2 + B ^ 2 ∧ IsFaceCuboid A B C) ∨
    (∃ X, 2 * X ^ 2 = A ^ 2 + C ^ 2 ∧ IsFaceCuboid A C B) ∨
    (∃ X, 2 * X ^ 2 = B ^ 2 + C ^ 2 ∧ IsFaceCuboid B C A) ∨
    (∃ D E F G, IsHalfTwistedBox 2 A B C D E F G) ∨
    (∃ D E F G, IsHalfTwistedBox 2 A C B E D F G) ∨
    (∃ D E F G, IsHalfTwistedBox 2 B C A F D E G) := by
  rcases classification' (d := 2) Nat.squarefree_two (by norm_num) hA hB hC h with
    h | h | h | h | ⟨X, hX, hb⟩ | ⟨D, E, F, G, hc⟩ | ⟨D, E, F, G, hc⟩ | ⟨D, E, F, G, hc⟩ |
      h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · have := hb.space_twist_mod_24 hp Nat.squarefree_two hX
    norm_num at this
  · have := hc.prime_mod_eight hp Nat.prime_two dvd_rfl
    norm_num at this
  · have := hc.prime_mod_eight (by rw [Nat.gcd_left_comm]; exact hp) Nat.prime_two dvd_rfl
    norm_num at this
  · have := hc.prime_mod_eight (by rw [Nat.gcd_left_comm, Nat.gcd_comm C B]; exact hp)
      Nat.prime_two dvd_rfl
    norm_num at this
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

/-- **`d = 2`, general form.** For any rational-edged `ℤ√2`-cuboid `(A, B, C)`, write
`(A, B, C) = g · (A', B', C')` with `gcd(A', B', C') = 1`; then `(A', B', C')` is a perfect
cuboid, a face cuboid with non-square face `2X²`, or a half-twisted box with `k = 2`. -/
theorem two' {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : IsQuadCuboid 2 (A : ℤ√2) (B : ℤ√2) (C : ℤ√2)) :
    ∃ g A' B' C' : ℕ, 0 < g ∧ A = g * A' ∧ B = g * B' ∧ C = g * C' ∧
      Nat.gcd A' (Nat.gcd B' C') = 1 ∧
      (IsPerfectCuboid A' B' C' ∨
      (∃ X, 2 * X ^ 2 = A' ^ 2 + B' ^ 2 ∧ IsFaceCuboid A' B' C') ∨
      (∃ X, 2 * X ^ 2 = A' ^ 2 + C' ^ 2 ∧ IsFaceCuboid A' C' B') ∨
      (∃ X, 2 * X ^ 2 = B' ^ 2 + C' ^ 2 ∧ IsFaceCuboid B' C' A') ∨
      (∃ D E F G, IsHalfTwistedBox 2 A' B' C' D E F G) ∨
      (∃ D E F G, IsHalfTwistedBox 2 A' C' B' E D F G) ∨
      (∃ D E F G, IsHalfTwistedBox 2 B' C' A' F D E G)) := by
  set g := Nat.gcd A (Nat.gcd B C) with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hA
  have hgA : g ∣ A := Nat.gcd_dvd_left _ _
  have hgB : g ∣ B := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hgC : g ∣ C := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨A', hA'⟩ := hgA
  obtain ⟨B', hB'⟩ := hgB
  obtain ⟨C', hC'⟩ := hgC
  have hcop : Nat.gcd A' (Nat.gcd B' C') = 1 := by
    have h1 : Nat.gcd A (Nat.gcd B C) = g * Nat.gcd A' (Nat.gcd B' C') := by
      rw [hA', hB', hC', Nat.gcd_mul_left, Nat.gcd_mul_left]
    have h2 : g * Nat.gcd A' (Nat.gcd B' C') = g * 1 := by rw [← h1, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hg h2
  have hpos : ∀ {X X' : ℕ}, 0 < X → X = g * X' → 0 < X' := fun {X X'} hX hXe ↦ by
    rcases Nat.eq_zero_or_pos X' with h0 | h0
    · rw [hXe, h0, mul_zero] at hX; exact absurd hX (lt_irrefl 0)
    · exact h0
  have h' : IsQuadCuboid 2 (A' : ℤ√2) (B' : ℤ√2) (C' : ℤ√2) := by
    apply isQuadCuboid_of_mul (d := 2) (g := g) Nat.squarefree_two hg
    rw [← hA', ← hB', ← hC']; exact h
  exact ⟨g, A', B', C', hg, hA', hB', hC', hcop,
    two (hpos hA hA') (hpos hB hB') (hpos hC hC') hcop h'⟩

end PerfectCuboid.Quad
