module

public import LeanPlayground.PerfectCuboid.ThirdConjecture
public import LeanPlayground.PerfectCuboid.Adjacency
public import LeanPlayground.PerfectCuboid.FermatTriangle

/-!
# The third cuboid conjecture: the factor `X² + m²` gives a type-A box

`ThirdConjecture.lean` shows that an even quadratic factor `X² − r` of Sharipov's third cuboid
polynomial has `r = ±m²`, and that `r = m² > 0` gives a rational perfect cuboid. This file treats
the remaining sign, the factor `X² + m²`, i.e. the root `y = −m²` of the sextic `f_{a,b,c}`.

**Theorem.** If `(a, b, c)` is not exceptional (`excPoly a b c ≠ 0`), `m ≠ 0` and
`f_{a,b,c}(−m²) = 0`, then there is a **type-A box** (`Adjacency.IsTypeA`): positive integers
`x, y, z` with `x² + z²`, `y² + z²`, `x² + y² + z²` and `x² + y² + 2z²` all squares
(`exists_isTypeA_of_root`, `exists_isTypeA_of_dvd`).

Together with `ThirdConjecture.lean`: for a non-exceptional integer triple, **an even quadratic
factor `X² − r` (`r ≠ 0`) of `cuboidThreePoly a b c` forces a rational perfect cuboid or a type-A
box** (`exists_isRatCuboid_or_isTypeA_of_dvd`). Type-A boxes are open problem 11 of the README; a
search found none with common edge `≤ 10⁷` (`AdjacencyNearMiss.lean`).

*Proof.* With `y = −m²` the three identities of `ThirdConjecture.lean` read
`u² = D² + V²`, `u² = E² + W²`, `V² + W² = u² + Z²` with `V = m v`, `W = m w`, `Z = m G`,
and `V² + W² = (m K)²`. Then `(E, D, Z)` satisfies `E² + Z² = V²`, `D² + Z² = W²`,
`E² + D² + Z² = u²` and `E² + D² + 2Z² = (m K)²`. Nondegeneracy: `Z ≠ 0` because `y = −c²` and
`y = −a²` are roots only for exceptional triples; and `E ≠ 0`, `D ≠ 0` by Fermat, since
`E = 0` would make `D², D² + Z², D² + 2Z²` three squares in arithmetic progression with square
common difference (`fermat_ap`). No resultant certificate is needed.
-/

@[expose] public section

namespace PerfectCuboid.ThirdConjecture

open Polynomial

/-- **Fermat.** There are no rationals with `G ≠ 0`, `V² = E² + G²` and `F² = E² + 2G²`: the
squares `E², E² + G², E² + 2G²` would be in arithmetic progression with square difference. -/
theorem fermat_ap {E G V F : ℚ} (hG : G ≠ 0) (hV : V ^ 2 = E ^ 2 + G ^ 2)
    (hF : F ^ 2 = E ^ 2 + 2 * G ^ 2) : False := by
  set M : ℤ := E.den * G.den * V.den * F.den with hM
  have hM0 : (M : ℚ) ≠ 0 := by rw [hM]; push_cast; simp [Rat.den_ne_zero]
  obtain ⟨e, he⟩ := exists_int_mul (x := E) (M := M) ⟨G.den * V.den * F.den, by rw [hM]; ring⟩
  obtain ⟨g, hg⟩ := exists_int_mul (x := G) (M := M) ⟨E.den * V.den * F.den, by rw [hM]; ring⟩
  obtain ⟨v, hv⟩ := exists_int_mul (x := V) (M := M) ⟨E.den * G.den * F.den, by rw [hM]; ring⟩
  obtain ⟨f, hf⟩ := exists_int_mul (x := F) (M := M) ⟨E.den * G.den * V.den, by rw [hM]; ring⟩
  have hv' : v ^ 2 = e ^ 2 + g ^ 2 := by
    have : (v : ℚ) ^ 2 = (e : ℚ) ^ 2 + (g : ℚ) ^ 2 := by
      rw [hv, he, hg]; linear_combination (M : ℚ) ^ 2 * hV
    exact_mod_cast this
  have hf' : f ^ 2 = e ^ 2 + 2 * g ^ 2 := by
    have : (f : ℚ) ^ 2 = (e : ℚ) ^ 2 + 2 * (g : ℚ) ^ 2 := by
      rw [hf, he, hg]; linear_combination (M : ℚ) ^ 2 * hF
    exact_mod_cast this
  have hg0 : g ≠ 0 := by
    rintro rfl
    have : (M : ℚ) * G = 0 := by rw [← hg]; simp
    exact (mul_ne_zero hM0 hG) this
  -- the triangle `(|f| + |e|, |f| − |e|, 2|v|)` has area `g²`
  set c := |f|
  set d := |e|
  set a := |v|
  have hc2 : c ^ 2 = f ^ 2 := sq_abs f
  have hd2 : d ^ 2 = e ^ 2 := sq_abs e
  have ha2 : a ^ 2 = v ^ 2 := sq_abs v
  have hd0 : 0 ≤ d := abs_nonneg e
  have hc0 : 0 ≤ c := abs_nonneg f
  have hgpos : 0 < g ^ 2 := by positivity
  have hdc : d < c := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  apply FermatTriangle.not_isSqAreaTriangle (c + d) (c - d) (2 * a) |g|
  refine ⟨by linarith, by linarith, abs_pos.mpr hg0, ?_, ?_⟩
  · linear_combination 2 * hc2 + 2 * hd2 - 4 * ha2 + 2 * hf' - 4 * hv'
  · rw [sq_abs]; linear_combination hc2 - hd2 + hf'

/-- A nonzero rational solution of the type-A system scales to a type-A box in `ℕ`. -/
theorem exists_isTypeA_of_rat {x y z p q g h : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hp : x ^ 2 + z ^ 2 = p ^ 2) (hq : y ^ 2 + z ^ 2 = q ^ 2) (hg : x ^ 2 + y ^ 2 + z ^ 2 = g ^ 2)
    (hh : x ^ 2 + y ^ 2 + 2 * z ^ 2 = h ^ 2) :
    ∃ X Y Z : ℕ, Adjacency.IsTypeA X Y Z := by
  set M : ℤ := x.den * y.den * z.den * p.den * q.den * g.den * h.den with hM
  have hM0 : (M : ℚ) ≠ 0 := by rw [hM]; push_cast; simp [Rat.den_ne_zero]
  obtain ⟨X, hX⟩ := exists_int_mul (x := x) (M := M)
    ⟨y.den * z.den * p.den * q.den * g.den * h.den, by rw [hM]; ring⟩
  obtain ⟨Y, hY⟩ := exists_int_mul (x := y) (M := M)
    ⟨x.den * z.den * p.den * q.den * g.den * h.den, by rw [hM]; ring⟩
  obtain ⟨Z, hZ⟩ := exists_int_mul (x := z) (M := M)
    ⟨x.den * y.den * p.den * q.den * g.den * h.den, by rw [hM]; ring⟩
  obtain ⟨P, hP⟩ := exists_int_mul (x := p) (M := M)
    ⟨x.den * y.den * z.den * q.den * g.den * h.den, by rw [hM]; ring⟩
  obtain ⟨Q, hQ⟩ := exists_int_mul (x := q) (M := M)
    ⟨x.den * y.den * z.den * p.den * g.den * h.den, by rw [hM]; ring⟩
  obtain ⟨G, hG⟩ := exists_int_mul (x := g) (M := M)
    ⟨x.den * y.den * z.den * p.den * q.den * h.den, by rw [hM]; ring⟩
  obtain ⟨H, hH⟩ := exists_int_mul (x := h) (M := M)
    ⟨x.den * y.den * z.den * p.den * q.den * g.den, by rw [hM]; ring⟩
  have ne {u : ℚ} {U : ℤ} (hu : u ≠ 0) (hU : (U : ℚ) = M * u) : 0 < U.natAbs := by
    refine Int.natAbs_pos.mpr fun h0 => ?_
    rw [h0] at hU; push_cast at hU
    exact (mul_ne_zero hM0 hu) hU.symm
  have e1 : (X ^ 2 + Z ^ 2 : ℤ) = P ^ 2 := by
    have : (X : ℚ) ^ 2 + (Z : ℚ) ^ 2 = (P : ℚ) ^ 2 := by
      rw [hX, hZ, hP]; linear_combination (M : ℚ) ^ 2 * hp
    exact_mod_cast this
  have e2 : (Y ^ 2 + Z ^ 2 : ℤ) = Q ^ 2 := by
    have : (Y : ℚ) ^ 2 + (Z : ℚ) ^ 2 = (Q : ℚ) ^ 2 := by
      rw [hY, hZ, hQ]; linear_combination (M : ℚ) ^ 2 * hq
    exact_mod_cast this
  have e3 : (X ^ 2 + Y ^ 2 + Z ^ 2 : ℤ) = G ^ 2 := by
    have : (X : ℚ) ^ 2 + (Y : ℚ) ^ 2 + (Z : ℚ) ^ 2 = (G : ℚ) ^ 2 := by
      rw [hX, hY, hZ, hG]; linear_combination (M : ℚ) ^ 2 * hg
    exact_mod_cast this
  have e4 : (X ^ 2 + Y ^ 2 + 2 * Z ^ 2 : ℤ) = H ^ 2 := by
    have : (X : ℚ) ^ 2 + (Y : ℚ) ^ 2 + 2 * (Z : ℚ) ^ 2 = (H : ℚ) ^ 2 := by
      rw [hX, hY, hZ, hH]; linear_combination (M : ℚ) ^ 2 * hh
    exact_mod_cast this
  have nat {A : ℤ} {n : ℕ} (h : (n : ℤ) = A ^ 2) : IsSquare n :=
    ⟨A.natAbs, by
      have : (n : ℤ) = (A.natAbs : ℤ) * (A.natAbs : ℤ) := by
        rw [h, Int.natCast_natAbs, abs_mul_abs_self, sq]
      exact_mod_cast this⟩
  refine ⟨X.natAbs, Y.natAbs, Z.natAbs,
    { pos_a := ne hx hX, pos_b := ne hy hY, pos_c := ne hz hZ,
      sq_ac := nat (A := P) ?_, sq_bc := nat (A := Q) ?_, sq_abc := nat (A := G) ?_,
      sq_g_c := nat (A := H) ?_ }⟩
  · push_cast; simp only [sq_abs]; exact e1
  · push_cast; simp only [sq_abs]; exact e2
  · push_cast; simp only [sq_abs]; exact e3
  · push_cast; simp only [sq_abs]; exact e4

/-- **The root `−m²`.** For a non-exceptional triple, a root `y = −m²` (`m ≠ 0`) of the third
cuboid sextic gives a type-A box. -/
theorem exists_isTypeA_of_root {a b c m : ℚ} (hE : excPoly a b c ≠ 0) (hm : m ≠ 0)
    (hf : sextic a b c (-m ^ 2) = 0) : ∃ X Y Z : ℕ, Adjacency.IsTypeA X Y Z := by
  obtain ⟨ha, hb, hc, hab, hab', hac, hac', hbc, hbc', -, -, -, -⟩ := factors_ne_zero hE
  obtain ⟨y, hydef⟩ : ∃ y : ℚ, y = -m ^ 2 := ⟨_, rfl⟩
  rw [← hydef] at hf
  have i1 := sextic_identity_one hf
  have i2 := sextic_identity_two hf
  have i3 := sextic_identity_three a b c y
  have i4 := sextic_identity_four a b c y
  -- `y ≠ −c²`
  have hyc : y + c ^ 2 ≠ 0 := by
    intro h0
    have hy' : y = -c ^ 2 := by linear_combination h0
    have : -4 * c ^ 4 * (b - c) ^ 2 * (b + c) ^ 2 * (a - c) ^ 2 * (a + c) ^ 2 = 0 := by
      rw [← hf, hy']; unfold sextic; ring
    revert this
    repeat' apply mul_ne_zero
    all_goals first | exact pow_ne_zero _ ‹_› | norm_num
  -- `dd² + nn² ≠ 0`
  have hsum : dd a b c y ^ 2 + nn a b c y ^ 2 ≠ 0 := by
    intro h0
    have hn : nn a b c y = 0 := by nlinarith [sq_nonneg (dd a b c y), sq_nonneg (nn a b c y)]
    unfold nn at hn
    rcases mul_eq_zero.mp hn with hn | hn
    · rcases mul_eq_zero.mp hn with hn | hn
      · exact hyc hn
      · have : 0 < m ^ 2 + b ^ 2 := by positivity
        rw [hydef] at hn; linarith
    · have hy' : y = -a ^ 2 := by linear_combination hn
      have : 4 * a ^ 4 * (a - c) ^ 2 * (a + c) ^ 2 * (a - b) ^ 2 * (a + b) ^ 2 = 0 := by
        rw [← hf, hy']; unfold sextic; ring
      revert this
      repeat' apply mul_ne_zero
      all_goals first | exact pow_ne_zero _ ‹_› | norm_num
  have hZ : m * diagG a b c y ≠ 0 := by
    unfold diagG; exact mul_ne_zero hm (mul_ne_zero hyc hsum)
  -- the box `(E, D, m G)`
  generalize uu a b c y = u at i1 i2 i3
  generalize vv a b c y = v at i1 i3 i4
  generalize ww a b c y = w at i2 i3 i4
  generalize diagD a b c y = D at i1
  generalize diagE a b c y = E at i2
  generalize diagG a b c y = G at i3 hZ
  generalize (y - c ^ 2) * (dd a b c y ^ 2 + nn a b c y ^ 2) = K at i4
  have j1 : u ^ 2 = D ^ 2 + (m * v) ^ 2 := by linear_combination i1 - v ^ 2 * hydef
  have j2 : u ^ 2 = E ^ 2 + (m * w) ^ 2 := by linear_combination i2 - w ^ 2 * hydef
  have j3 : (m * v) ^ 2 + (m * w) ^ 2 = u ^ 2 + (m * G) ^ 2 := by
    linear_combination -i3 + (v ^ 2 + w ^ 2 - G ^ 2) * hydef
  have j4 : (m * v) ^ 2 + (m * w) ^ 2 = (m * K) ^ 2 := by linear_combination m ^ 2 * i4
  have p1 : E ^ 2 + (m * G) ^ 2 = (m * v) ^ 2 := by linear_combination -j2 - j3
  have p2 : D ^ 2 + (m * G) ^ 2 = (m * w) ^ 2 := by linear_combination -j1 - j3
  have p3 : E ^ 2 + D ^ 2 + (m * G) ^ 2 = u ^ 2 := by linear_combination p1 + p2 + j3
  have p4 : E ^ 2 + D ^ 2 + 2 * (m * G) ^ 2 = (m * K) ^ 2 := by
    linear_combination p3 - j3 + j4
  have hE0 : E ≠ 0 := by
    intro h0
    exact fermat_ap hZ (E := D) (V := m * w) (F := m * K) (by linear_combination -p2)
      (by rw [h0] at p4; linear_combination -p4)
  have hD0 : D ≠ 0 := by
    intro h0
    exact fermat_ap hZ (E := E) (V := m * v) (F := m * K) (by linear_combination -p1)
      (by rw [h0] at p4; linear_combination -p4)
  exact exists_isTypeA_of_rat hE0 hD0 hZ p1 p2 p3 p4

/-- **The factor `X² + m²`.** For a non-exceptional integer triple, `X² + m²` (`m ≠ 0`) dividing
the third cuboid polynomial gives a type-A box. -/
theorem exists_isTypeA_of_dvd {a b c m : ℤ} (hE : excPoly a b c ≠ 0) (hm : m ≠ 0)
    (h : X ^ 2 + C (m ^ 2) ∣ cuboidThreePoly a b c) : ∃ X Y Z : ℕ, Adjacency.IsTypeA X Y Z := by
  have h' : X ^ 2 - C (-(m ^ 2)) ∣ cuboidThreePoly a b c := by
    rwa [map_neg, sub_neg_eq_add]
  have hf := sextic_eq_zero_of_dvd h'
  push_cast at hf
  exact exists_isTypeA_of_root (m := m) hE (by exact_mod_cast hm) hf

/-- **Even quadratic factors, complete reduction.** For a non-exceptional integer triple, if
`X² − r` (`r ≠ 0`) divides the third cuboid polynomial, then a rational perfect cuboid or a
type-A box exists. -/
theorem exists_isRatCuboid_or_isTypeA_of_dvd {a b c r : ℤ} (hE : excPoly a b c ≠ 0) (hr : r ≠ 0)
    (h : X ^ 2 - C r ∣ cuboidThreePoly a b c) :
    (∃ p q s d e f g : ℚ, PerfectCuboid.CongruentRank.IsRatCuboid p q s d e f g) ∨
      ∃ X Y Z : ℕ, Adjacency.IsTypeA X Y Z := by
  have hc : c ≠ 0 := by exact_mod_cast (factors_ne_zero hE).2.2.1
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · right
    rcases isSquare_or_isSquare_neg_of_dvd hc h with ⟨m, hm⟩ | ⟨m, hm⟩
    · nlinarith [mul_self_nonneg m]
    · have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
      refine exists_isTypeA_of_dvd hE hm0 ?_
      have : r = -(m ^ 2) := by linear_combination -hm
      rw [this, map_neg, sub_neg_eq_add] at h
      exact h
  · exact Or.inl (exists_isRatCuboid_of_dvd hE hpos h)

end PerfectCuboid.ThirdConjecture
