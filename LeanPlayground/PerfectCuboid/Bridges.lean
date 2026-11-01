module

public import LeanPlayground.PerfectCuboid.DerivedCuboid
public import LeanPlayground.PerfectCuboid.ConfigCuboid
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Bridge theorems: four equivalent forms of the perfect cuboid problem

Each theorem below is an explicit `↔` between the existence of a perfect cuboid
(`∃ a b c, IsPerfectCuboid a b c`) and a different-looking problem, with nondegeneracy on both
sides, so that neither side is vacuous.

* **B1, Gaussian pair form** (`exists_isPerfectCuboid_iff_gaussian`). A perfect cuboid exists iff
  there are Gaussian integers `u, v` with `N u ≠ N v`, `Re(u v̄) ≠ 0`, `Im(u v̄) ≠ 0` such that
  `N(uv)`, `N(u² − v²)` and `N(u² + v²)` are all squares. The dictionary is
  `a = N u − N v`, `g = N u + N v`, `c + b i = 2 u v̄`, with
  `a² + b² = N(u² − v²)`, `a² + c² = N(u² + v²)`, `b² + c² = 4 N(u v)`, `a² + b² + c² = g²`
  (`gaussian_identities`). Conversely a cuboid gives `u = c − b i`, `v = g − a`.
  This is the integer form of the Stoll–Testa coordinate `ξ = (a + g)/(b − i c)`
  (`BeauvilleLambda.lean`; here `u / v = −i ξ`); what is new is only the explicit iff.
  (Since `N(uv) · N(u⁴ − v⁴) = N(u⁵ v − u v⁵)`, a cuboid gives a point on the Beauville twist of
  `y² = x⁵ − x`; we do not pursue this.)
  Near-miss check: for Halcke's brick `(44, 117, 240)` the construction needs `v = g − a` with
  `g² = 73225 = 5² · 2929` not a square, so it gives no Gaussian pair. The degenerate box
  `(3, 0, 4; 5)` corresponds to `u = 2`, `v = 1`, where all three norms `4, 9, 25` are squares
  but `Im(u v̄) = 0` (`degenerate_gaussian`): the hypothesis `Im(u v̄) ≠ 0` is exactly what
  excludes degenerate solutions.
* **B2, de Gua / Heron / derived brick.** For an Euler brick with face diagonals `d, e, f`,
  `2(d²e² + e²f² + f²d²) − (d⁴ + e⁴ + f⁴) = 4σ₂`, `σ₂ = a²b² + b²c² + c²a²`
  (`sixteen_area_sq`; Heron's `16·Area²` of the triangle with sides `d, e, f`, i.e. de Gua's
  theorem for the trirectangular tetrahedron cut off the box). The derived brick
  `(bc, ca, ab)` is perfect iff `σ₂` is a square (`isSquare_sigma2_iff_derived`), iff the
  face-diagonal triangle is Heronian, i.e. `16·Area²` is a square (`heron_iff_derived`).
  For a perfect cuboid, `(def)² + (abc)² = g² σ₂` (`def_sq_add_abc_sq`). Whether `σ₂` can be a
  square for a perfect cuboid ("double perfect") is open. Near-miss check: for `(44, 117, 240)`,
  `σ₂ = 926501904` is not a square (`not_isSquare_sigma2_44_117_240`), so the face-diagonal
  triangle `(125, 244, 267)` is not Heronian.
* **B3, three Pythagorean direction cosines** (`exists_isPerfectCuboid_iff_cosines`). A perfect
  cuboid exists iff there is a rational point `(x₁, x₂, x₃)` on the unit sphere, in the open
  positive octant, with `1 − xⱼ²` a rational square for each `j`: a perfect cuboid is a rational
  point on the unit sphere whose three direction angles are Pythagorean angles
  (`xⱼ = a/g, b/g, c/g`, `1 − (a/g)² = (f/g)²`). Near misses: an Euler brick gives an
  irrational `g`, so no rational point; a degenerate box `(a, b, 0)` gives `x₃ = 0`, excluded
  by `0 < x₃`.
* **B4, three representations of `g²`** (`exists_isPerfectCuboid_iff_three_hyp`). A perfect
  cuboid exists iff `g² = a² + f² = b² + e² = c² + d²` with `a² + b² + c² = g²` and
  `a, b, c > 0`: the face conditions are then automatic. This is the form in which Korec's
  theorems on `g` live.
-/

@[expose] public section

namespace PerfectCuboid.Bridges

/-! ### B1: Gaussian pair form -/

theorem norm_eq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

/-- The four identities behind the Gaussian pair form, with `a = N u − N v`,
`b = 2 Im(u v̄)`, `c = 2 Re(u v̄)`, `g = N u + N v`. -/
theorem gaussian_identities (u v : GaussianInt) :
    (u.norm - v.norm) ^ 2 + (2 * (u * star v).im) ^ 2 = (u ^ 2 - v ^ 2).norm ∧
    (u.norm - v.norm) ^ 2 + (2 * (u * star v).re) ^ 2 = (u ^ 2 + v ^ 2).norm ∧
    (2 * (u * star v).im) ^ 2 + (2 * (u * star v).re) ^ 2 = 4 * (u * v).norm ∧
    (u.norm - v.norm) ^ 2 + (2 * (u * star v).im) ^ 2 + (2 * (u * star v).re) ^ 2 =
      (u.norm + v.norm) ^ 2 := by
  simp only [norm_eq, sq, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_sub, Zsqrtd.im_sub,
    Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_star, Zsqrtd.im_star]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem isSquare_natAbs {x y : ℤ} (h : IsSquare (x ^ 2 + y ^ 2)) :
    IsSquare (x.natAbs ^ 2 + y.natAbs ^ 2) := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r.natAbs, ?_⟩
  zify
  simp only [sq_abs]
  rw [hr, abs_mul_abs_self]

/-- **B1.** A perfect cuboid exists iff some pair of Gaussian integers `u, v` with
`N u ≠ N v` and `u v̄` off both axes has `N(uv)`, `N(u² − v²)`, `N(u² + v²)` all squares. -/
theorem exists_isPerfectCuboid_iff_gaussian :
    (∃ a b c, IsPerfectCuboid a b c) ↔
      ∃ u v : GaussianInt, u.norm ≠ v.norm ∧ (u * star v).re ≠ 0 ∧ (u * star v).im ≠ 0 ∧
        IsSquare (u * v).norm ∧ IsSquare (u ^ 2 - v ^ 2).norm ∧
        IsSquare (u ^ 2 + v ^ 2).norm := by
  constructor
  · rintro ⟨a, b, c, h⟩
    obtain ⟨d, hd⟩ := h.sq_ab
    obtain ⟨f, hf⟩ := h.sq_bc
    obtain ⟨e, he⟩ := h.sq_ca
    obtain ⟨g, hg⟩ := h.sq_abc
    have ha := h.pos_a
    have hb := h.pos_b
    have hc := h.pos_c
    have hga : a < g := by nlinarith
    -- work in ℤ
    have hd' : (a : ℤ) ^ 2 + b ^ 2 = d * d := by exact_mod_cast hd
    have hf' : (b : ℤ) ^ 2 + c ^ 2 = f * f := by exact_mod_cast hf
    have he' : (c : ℤ) ^ 2 + a ^ 2 = e * e := by exact_mod_cast he
    have hg' : (a : ℤ) ^ 2 + b ^ 2 + c ^ 2 = g * g := by exact_mod_cast hg
    have hga' : (a : ℤ) < g := by exact_mod_cast hga
    have ha' : (0 : ℤ) < a := by exact_mod_cast ha
    have hb' : (0 : ℤ) < b := by exact_mod_cast hb
    have hc' : (0 : ℤ) < c := by exact_mod_cast hc
    refine ⟨⟨c, -b⟩, ⟨g - a, 0⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [norm_eq, norm_eq]
      simp only
      intro hcon
      nlinarith
    · simp only [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star]
      intro hcon
      have : (c : ℤ) * (g - a) = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0 <;> [linarith; linarith]
    · simp only [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
      intro hcon
      have : (b : ℤ) * (g - a) = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0 <;> [linarith; linarith]
    · refine ⟨f * (g - a), ?_⟩
      rw [norm_eq]
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
      linear_combination (g - a) ^ 2 * hf'
    · refine ⟨2 * (g - a) * d, ?_⟩
      rw [norm_eq]
      simp only [sq, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_sub, Zsqrtd.im_sub]
      linear_combination (4 * (g - a) ^ 2) * hd' +
        (-4 * a ^ 2 + 4 * a * g + (a ^ 2 + b ^ 2 + c ^ 2 - g ^ 2)) * hg'
    · refine ⟨2 * (g - a) * e, ?_⟩
      rw [norm_eq]
      simp only [sq, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_add, Zsqrtd.im_add]
      linear_combination (4 * (g - a) ^ 2) * he' +
        (-4 * a ^ 2 + 4 * a * g + (a ^ 2 + b ^ 2 + c ^ 2 - g ^ 2)) * hg'
  · rintro ⟨u, v, hne, hre, him, ⟨r, hr⟩, h₁, h₂⟩
    obtain ⟨i₁, i₂, i₃, i₄⟩ := gaussian_identities u v
    refine ⟨(u.norm - v.norm).natAbs, (2 * (u * star v).im).natAbs,
      (2 * (u * star v).re).natAbs, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
    · exact Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
    · exact Int.natAbs_pos.mpr (mul_ne_zero two_ne_zero him)
    · exact Int.natAbs_pos.mpr (mul_ne_zero two_ne_zero hre)
    · exact isSquare_natAbs (i₁ ▸ h₁)
    · exact isSquare_natAbs (by rw [i₃, hr]; exact ⟨2 * r, by ring⟩)
    · exact isSquare_natAbs (by rw [add_comm, i₂]; exact h₂)
    · refine ⟨(u.norm + v.norm).natAbs, ?_⟩
      zify
      simp only [sq_abs]
      rw [i₄, abs_mul_abs_self, sq]

/-- The degenerate box `(3, 0, 4; 5)` in Gaussian form: `u = 2`, `v = 1` makes all three norms
squares, and fails only `Im(u v̄) ≠ 0`. -/
theorem degenerate_gaussian :
    ((⟨2, 0⟩ : GaussianInt) * star ⟨1, 0⟩).im = 0 ∧
      IsSquare ((⟨2, 0⟩ : GaussianInt) * ⟨1, 0⟩).norm ∧
      IsSquare ((⟨2, 0⟩ : GaussianInt) ^ 2 - (⟨1, 0⟩ : GaussianInt) ^ 2).norm ∧
      IsSquare ((⟨2, 0⟩ : GaussianInt) ^ 2 + (⟨1, 0⟩ : GaussianInt) ^ 2).norm :=
  ⟨by decide, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩⟩

/-! ### B2: de Gua, Heron and the derived brick -/

/-- **de Gua / Heron.** If `d² = a² + b²`, `e² = a² + c²`, `f² = b² + c²`, then Heron's
`16·Area²` of the triangle with sides `d, e, f` equals `4σ₂`, `σ₂ = a²b² + b²c² + c²a²`. -/
theorem sixteen_area_sq {a b c d e f : ℤ} (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2) :
    2 * (d ^ 2 * e ^ 2 + e ^ 2 * f ^ 2 + f ^ 2 * d ^ 2) - (d ^ 4 + e ^ 4 + f ^ 4) =
      4 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  have key : ∀ D E F : ℤ, D = a ^ 2 + b ^ 2 → E = a ^ 2 + c ^ 2 → F = b ^ 2 + c ^ 2 →
      2 * (D * E + E * F + F * D) - (D ^ 2 + E ^ 2 + F ^ 2) =
        4 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
    rintro _ _ _ rfl rfl rfl; ring
  have := key _ _ _ hd he hf
  linear_combination this

/-- The derived brick `(bc, ca, ab)` of an Euler brick is perfect iff `σ₂` is a square. -/
theorem isSquare_sigma2_iff_derived {a b c : ℕ} (h : IsEulerBrick a b c) :
    IsSquare (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ↔
      IsPerfectCuboid (b * c) (c * a) (a * b) := by
  have e : (b * c) ^ 2 + (c * a) ^ 2 + (a * b) ^ 2 =
      a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by ring
  constructor
  · intro hs
    exact ⟨h.derived, e ▸ hs⟩
  · intro hp
    exact e ▸ hp.sq_abc

theorem isSquare_four_mul_iff {n : ℕ} : IsSquare (4 * (n : ℤ)) ↔ IsSquare n := by
  constructor
  · rintro ⟨r, hr⟩
    rcases Int.even_or_odd r with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · refine ⟨s.natAbs, ?_⟩
      zify
      rw [abs_mul_abs_self]
      linarith
    · exfalso
      have e : (2 * s + 1) * (2 * s + 1) = 4 * (s * s + s) + 1 := by ring
      rw [e] at hr
      generalize s * s + s = t at hr
      omega
  · rintro ⟨r, hr⟩
    exact ⟨2 * r, by rw [hr]; push_cast; ring⟩

/-- **Heron ↔ derived.** For an Euler brick with face diagonals `d, e, f`, the triangle with
sides `d, e, f` has square `16·Area²` iff the derived brick `(bc, ca, ab)` is perfect. -/
theorem heron_iff_derived {a b c d e f : ℕ} (h : IsEulerBrick a b c) (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2) :
    IsSquare (2 * ((d : ℤ) ^ 2 * e ^ 2 + e ^ 2 * f ^ 2 + f ^ 2 * d ^ 2) -
      (d ^ 4 + e ^ 4 + f ^ 4)) ↔
      IsPerfectCuboid (b * c) (c * a) (a * b) := by
  rw [← isSquare_sigma2_iff_derived h, ← isSquare_four_mul_iff,
    sixteen_area_sq (a := a) (b := b) (c := c) (by exact_mod_cast hd) (by exact_mod_cast he)
      (by exact_mod_cast hf)]
  push_cast
  rfl

/-- For a perfect cuboid, `(def)² + (abc)² = g² σ₂`. -/
theorem def_sq_add_abc_sq {a b c d e f g : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    (d * e * f) ^ 2 + (a * b * c) ^ 2 =
      g ^ 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  rw [mul_pow, mul_pow, hd, he, hf, hg]; ring

/-- Near miss: for Halcke's brick `σ₂ = 926501904` is not a square, so its derived brick is not
perfect and its face-diagonal triangle `(125, 244, 267)` is not Heronian. -/
theorem not_isSquare_sigma2_44_117_240 :
    ¬ IsSquare (44 ^ 2 * 117 ^ 2 + 117 ^ 2 * 240 ^ 2 + 240 ^ 2 * 44 ^ 2 : ℕ) := by
  rintro ⟨r, hr⟩
  norm_num at hr
  rcases le_or_gt r 30438 with h1 | h1
  · have : r * r ≤ 30438 * 30438 := Nat.mul_le_mul h1 h1
    omega
  · have : 30439 * 30439 ≤ r * r := Nat.mul_le_mul h1 h1
    omega

/-! ### B4: three representations of `g²` -/

/-- **B4.** A perfect cuboid exists iff `g²` has three representations `a² + f² = b² + e² =
c² + d²` with `a² + b² + c² = g²` and `a, b, c > 0`. -/
theorem exists_isPerfectCuboid_iff_three_hyp :
    (∃ a b c, IsPerfectCuboid a b c) ↔
      ∃ g a b c d e f : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + f ^ 2 = g ^ 2 ∧
        b ^ 2 + e ^ 2 = g ^ 2 ∧ c ^ 2 + d ^ 2 = g ^ 2 ∧ a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 := by
  constructor
  · rintro ⟨a, b, c, h⟩
    obtain ⟨d, hd⟩ := h.sq_ab
    obtain ⟨f, hf⟩ := h.sq_bc
    obtain ⟨e, he⟩ := h.sq_ca
    obtain ⟨g, hg⟩ := h.sq_abc
    refine ⟨g, a, b, c, d, e, f, h.pos_a, h.pos_b, h.pos_c, ?_, ?_, ?_, ?_⟩ <;>
      simp only [sq] at * <;> omega
  · rintro ⟨g, a, b, c, d, e, f, ha, hb, hc, h1, h2, h3, h4⟩
    refine ⟨a, b, c, ⟨⟨ha, hb, hc, ⟨d, ?_⟩, ⟨f, ?_⟩, ⟨e, ?_⟩⟩, ⟨g, ?_⟩⟩⟩ <;>
      simp only [sq] at * <;> omega

/-! ### B3: three Pythagorean direction cosines -/

/-- **B3.** A perfect cuboid exists iff there is a rational point `(x₁, x₂, x₃)` on the unit
sphere with positive coordinates and `1 − xⱼ²` a rational square for each `j`. -/
theorem exists_isPerfectCuboid_iff_cosines :
    (∃ a b c, IsPerfectCuboid a b c) ↔
      ∃ x₁ x₂ x₃ : ℚ, 0 < x₁ ∧ 0 < x₂ ∧ 0 < x₃ ∧ IsSquare (1 - x₁ ^ 2) ∧
        IsSquare (1 - x₂ ^ 2) ∧ IsSquare (1 - x₃ ^ 2) ∧ x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 = 1 := by
  constructor
  · rintro ⟨a, b, c, h⟩
    obtain ⟨d, hd⟩ := h.sq_ab
    obtain ⟨f, hf⟩ := h.sq_bc
    obtain ⟨e, he⟩ := h.sq_ca
    obtain ⟨g, hg⟩ := h.sq_abc
    have ha : (0 : ℚ) < a := by exact_mod_cast h.pos_a
    have hb : (0 : ℚ) < b := by exact_mod_cast h.pos_b
    have hc : (0 : ℚ) < c := by exact_mod_cast h.pos_c
    have hd' : (a : ℚ) ^ 2 + b ^ 2 = d * d := by exact_mod_cast hd
    have hf' : (b : ℚ) ^ 2 + c ^ 2 = f * f := by exact_mod_cast hf
    have he' : (c : ℚ) ^ 2 + a ^ 2 = e * e := by exact_mod_cast he
    have hg' : (a : ℚ) ^ 2 + b ^ 2 + c ^ 2 = g * g := by exact_mod_cast hg
    have hg0 : (g : ℚ) ≠ 0 := by
      intro h0; rw [h0] at hg'; nlinarith
    refine ⟨a / g, b / g, c / g, ?_, ?_, ?_, ⟨f / g, ?_⟩, ⟨e / g, ?_⟩, ⟨d / g, ?_⟩, ?_⟩
    · have : (0 : ℚ) < g := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hg0)
      positivity
    · have : (0 : ℚ) < g := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hg0)
      positivity
    · have : (0 : ℚ) < g := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hg0)
      positivity
    all_goals field_simp
    all_goals linarith
  · rintro ⟨x₁, x₂, x₃, h₁, h₂, h₃, ⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩, ⟨s₃, hs₃⟩, hsum⟩
    have p₁ : 0 < |s₁| := abs_pos.mpr (by rintro rfl; nlinarith)
    have p₂ : 0 < |s₂| := abs_pos.mpr (by rintro rfl; nlinarith)
    have p₃ : 0 < |s₃| := abs_pos.mpr (by rintro rfl; nlinarith)
    refine CongruentRank.IsRatCuboid.exists_isPerfectCuboid
      (a := x₁) (b := x₂) (c := x₃) (d := |s₃|) (e := |s₂|) (f := |s₁|) (g := 1)
      ⟨h₁, h₂, h₃, p₃, p₂, p₁, one_pos, ?_, ?_, ?_, ?_⟩
    · rw [sq_abs, sq]; linarith
    · rw [sq_abs, sq]; linarith
    · rw [sq_abs, sq]; linarith
    · linarith

end PerfectCuboid.Bridges
