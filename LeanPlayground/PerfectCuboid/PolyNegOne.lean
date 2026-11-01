module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolyCharP

/-!
# Cuboids over `K[X]` when `−1` is not a square (round 17, brief 3)

Rounds 13–14 proved over `ℚ[X]` that a constant edge is impossible and a linear edge forces
proportional edges. Those proofs use the order of `ℚ` only through "`x² + y² = 0 ⇒ x = y = 0`".
Here they are generalised to an arbitrary field `K` (namespace `PerfectCuboid.PolyNegOne`, on the
`IsCuboid` of `PolyCharP.lean`).

* **No cancellation** (`sq_add_sq_ne_zero`, `sq_add_sq_eq_zero_iff`, `natDegree_sq_add_sq`,
  `natDegree_hyp`, `IsCuboid.natDegree_space`): if `¬ IsSquare (-1 : K)` then
  `deg (x² + y²) = 2 max (deg x, deg y)` and `deg g = max (deg a, deg b, deg c)`.
* **Constant edge** (`IsCuboid.natDegree_eq_zero_of_const`, `IsCuboid.proportional_of_const`):
  for any field with `2 ≠ 0` (no hypothesis on `−1`), a cuboid `(C α, b, c)` has `b, c` constant.
* **Constant cuboids** (`IsConstCuboid`, `isSquare_C_iff`, `isCuboid_C_iff`,
  `Proportional.isConstCuboid`): a proportional cuboid `(α q, β q, γ q)` is the same as a cuboid
  `(α, β, γ)` over `K`.
* **Linear and degree-one edges** (`IsCuboid.proportional_of_linear_edge`,
  `IsCuboid.proportional_of_natDegree_eq_one`): with `¬ IsSquare (-1 : K)` and `2 ≠ 0`, a cuboid
  with an edge of degree one is proportional. Port of the `ℚ[X]` proofs: `isCoprime_sub_add`,
  `monomial_leg`, `quad_disc` (characteristic-free given `2 ≠ 0`), `not_squares_of_monomial`,
  `not_squares_linear_mixed`; the order was used only for "`v² + v'² ≠ 0`", which is
  `sq_add_sq_ne_zero`.
* **`𝔽_p`, `p ≡ 3 (mod 4)`** (`zmod_proportional_of_natDegree_le_one`): an edge of degree `≤ 1`
  forces proportionality. Over `𝔽₃, 𝔽₇, 𝔽₁₁, 𝔽₁₉` there is no constant cuboid
  (`not_isConstCuboid_three`, …, kernel `decide`), hence **every edge of every cuboid over
  `𝔽_p[X]`, `p ∈ {3, 7, 11, 19}`, has degree `≥ 2`** (`no_cuboid_natDegree_le_one_three`, …).
  Over `𝔽₂₃`, `(1, 1, 1)` is a constant cuboid (`isConstCuboid_twentythree`).
* **A nondegenerate non-proportional cuboid over `𝔽₇[X]`** (`isCuboid_seven`,
  `isNondegCuboid_seven`, `not_proportional_seven`, `exists_nondeg_not_proportional_seven`):
  `(X⁶ + 3X⁴ + 2X², X⁸ + 6X⁶ + 4X⁴ + 5X² + 4, X⁷ − X)`, found by the exhaustive search
  `round17/code/b3/cubsearch.c`. So over `𝔽_p`, `p ≡ 3 (mod 4)`, `¬ IsSquare (-1)` does **not**
  force proportionality in general (unlike the degree-`≤ 1` statements); the Frobenius cuboid of
  `PolyCharP.lean` needs `√−1`, this one does not. The search (every edge `a` of degree `≤ D`,
  all partners `b = (a²/t − t)/2`, `t ∣ a²`, of any degree) finds no cuboid over `𝔽₃[X]` with an
  edge of degree `≤ 13`, none over `𝔽₁₁[X]` with an edge of degree `≤ 6`, none over `𝔽₁₉[X]`
  with an edge of degree `≤ 5`, and over `𝔽₇[X]` none with an edge of degree `≤ 5` (search
  results, not formalised).
-/

@[expose] public section

open Polynomial

namespace PerfectCuboid.PolyNegOne

open PolyCharP

variable {K : Type*} [Field K]

/-! ## Sums of two squares do not cancel -/

theorem sq_add_sq_ne_zero (hK : ¬ IsSquare (-1 : K)) {u v : K} (hv : v ≠ 0) :
    u ^ 2 + v ^ 2 ≠ 0 := by
  intro h
  apply hK
  refine ⟨u / v, ?_⟩
  field_simp
  linear_combination -h

theorem sq_add_sq_eq_zero_iff (hK : ¬ IsSquare (-1 : K)) {x y : K[X]} :
    x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    by_cases hy : y = 0
    · subst hy
      refine ⟨?_, rfl⟩
      simpa using h
    · exact absurd (isSquare_neg_one_of_sq_add_sq_eq_zero hy h) hK
  · rintro ⟨rfl, rfl⟩; ring

theorem natDegree_sq_add_sq (hK : ¬ IsSquare (-1 : K)) {x y : K[X]} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x ^ 2 + y ^ 2).natDegree = 2 * max x.natDegree y.natDegree := by
  have hx' := leadingCoeff_ne_zero.2 hx
  have hy' := leadingCoeff_ne_zero.2 hy
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_pow]; omega
    · rw [natDegree_pow]; omega
  · rw [coeff_add]
    rcases lt_trichotomy x.natDegree y.natDegree with hlt | heq | hgt
    · rw [max_eq_right hlt.le, coeff_eq_zero_of_natDegree_lt (by rw [natDegree_pow]; omega),
        zero_add, coeff_pow_mul_natDegree]
      exact pow_ne_zero 2 hy'
    · rw [← heq, max_self, coeff_pow_mul_natDegree, heq, coeff_pow_mul_natDegree]
      exact sq_add_sq_ne_zero hK hy'
    · rw [max_eq_left hgt.le, coeff_eq_zero_of_natDegree_lt (n := 2 * x.natDegree)
        (p := y ^ 2) (by rw [natDegree_pow]; omega), add_zero,
        coeff_pow_mul_natDegree]
      exact pow_ne_zero 2 hx'

theorem natDegree_hyp (hK : ¬ IsSquare (-1 : K)) {x y z : K[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : z.natDegree = max x.natDegree y.natDegree :=
  natDegree_hyp_of_ne hx hy (fun _ => sq_add_sq_ne_zero hK (leadingCoeff_ne_zero.2 hy)) h

theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.natDegree_space (hK : ¬ IsSquare (-1 : K))
    {a b c : K[X]} (h : IsCuboid a b c) {g : K[X]} (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    g.natDegree = max (max a.natDegree b.natDegree) c.natDegree := by
  obtain ⟨d, hd⟩ := h.sq_ab
  rw [← sq] at hd
  have hdne : d ≠ 0 := by
    rintro rfl
    exact h.ne_a ((sq_add_sq_eq_zero_iff hK).1 (by rw [hd]; ring)).1
  rw [natDegree_hyp hK hdne h.ne_c (by rw [← hd]; exact hg), natDegree_hyp hK h.ne_a h.ne_b hd]

/-! ## Constant edges (any field with `2 ≠ 0`) -/

theorem C_half_mul_two (h2 : (2 : K) ≠ 0) : C (1 / 2 : K) * 2 = 1 := by
  rw [← C_1, ← map_ofNat C 2, ← C_mul]
  congr 1
  field_simp

theorem natDegree_eq_zero_of_two_mul (h2 : (2 : K) ≠ 0) {p : K[X]} (h : (2 * p).natDegree = 0) :
    p.natDegree = 0 := by
  rwa [← map_ofNat C 2, natDegree_C_mul h2] at h

/-- A right triangle over `K[X]` with a nonzero constant leg is constant. -/
theorem natDegree_eq_zero_of_leg (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hx : x ≠ 0)
    (hx0 : x.natDegree = 0) (h : x ^ 2 + y ^ 2 = z ^ 2) : y.natDegree = 0 ∧ z.natDegree = 0 := by
  have hu : IsUnit (x ^ 2) := by
    have hxC := eq_C_of_natDegree_eq_zero hx0
    have hc : x.coeff 0 ≠ 0 := by
      intro h0
      rw [h0, C_0] at hxC
      exact hx hxC
    rw [hxC, ← C_pow]
    exact isUnit_C.mpr (Ne.isUnit (pow_ne_zero _ hc))
  have hprod : (z - y) * (z + y) = x ^ 2 := by linear_combination -h
  rw [← hprod] at hu
  have h1 : (z - y).natDegree = 0 := natDegree_eq_zero_of_isUnit (isUnit_of_mul_isUnit_left hu)
  have h2' : (z + y).natDegree = 0 :=
    natDegree_eq_zero_of_isUnit (isUnit_of_mul_isUnit_right hu)
  constructor
  · apply natDegree_eq_zero_of_two_mul h2
    have : 2 * y = (z + y) - (z - y) := by ring
    rw [this]
    exact Nat.eq_zero_of_le_zero ((natDegree_sub_le _ _).trans (by omega))
  · apply natDegree_eq_zero_of_two_mul h2
    have : 2 * z = (z + y) + (z - y) := by ring
    rw [this]
    exact Nat.eq_zero_of_le_zero ((natDegree_add_le _ _).trans (by omega))

/-- **Constant edge ⇒ constant cuboid** (any field with `2 ≠ 0`, no hypothesis on `−1`). -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.natDegree_eq_zero_of_const (h2 : (2 : K) ≠ 0)
    {α : K} {b c : K[X]} (h : IsCuboid (C α) b c) : b.natDegree = 0 ∧ c.natDegree = 0 := by
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  rw [← sq] at hd he
  exact ⟨(natDegree_eq_zero_of_leg h2 h.ne_a (natDegree_C α) hd).1,
    (natDegree_eq_zero_of_leg h2 h.ne_a (natDegree_C α) he).1⟩

theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_const (h2 : (2 : K) ≠ 0)
    {α : K} {b c : K[X]} (h : IsCuboid (C α) b c) : Proportional (C α) b c := by
  obtain ⟨hb, hc⟩ := h.natDegree_eq_zero_of_const h2
  exact ⟨1, α, b.coeff 0, c.coeff 0, by rw [mul_one],
    by rw [mul_one, ← eq_C_of_natDegree_eq_zero hb],
    by rw [mul_one, ← eq_C_of_natDegree_eq_zero hc]⟩

/-! ## Constants and squares -/

theorem isSquare_C_iff {r : K} : IsSquare (C r : K[X]) ↔ IsSquare r := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases hs0 : s = 0
    · subst hs0
      rw [mul_zero, C_eq_zero] at hs
      exact ⟨0, by rw [hs, mul_zero]⟩
    have hdeg := congrArg natDegree hs
    rw [natDegree_C, natDegree_mul hs0 hs0] at hdeg
    have hsC := eq_C_of_natDegree_eq_zero (show s.natDegree = 0 by omega)
    rw [hsC, ← C_mul] at hs
    exact ⟨s.coeff 0, C_injective hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨C s, by rw [hs, C_mul]⟩

/-- If `C r * q² = s²` with `q ≠ 0`, then `r` is a square. -/
theorem isSquare_of_C_mul_sq {r : K} {q s : K[X]} (hq : q ≠ 0) (h : C r * q ^ 2 = s ^ 2) :
    IsSquare r := by
  have h' := congrArg leadingCoeff h
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow, leadingCoeff_pow] at h'
  have hlq : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  refine ⟨s.leadingCoeff / q.leadingCoeff, ?_⟩
  field_simp
  linear_combination h'

/-- A *constant cuboid* over `K`: nonzero `α, β, γ` with the four sums squares in `K`. -/
def IsConstCuboid (α β γ : K) : Prop :=
  α ≠ 0 ∧ β ≠ 0 ∧ γ ≠ 0 ∧ IsSquare (α ^ 2 + β ^ 2) ∧ IsSquare (α ^ 2 + γ ^ 2) ∧
    IsSquare (β ^ 2 + γ ^ 2) ∧ IsSquare (α ^ 2 + β ^ 2 + γ ^ 2)

/-- A proportional cuboid `(α q, β q, γ q)` gives a constant cuboid `(α, β, γ)`. -/
theorem isConstCuboid_of_isCuboid_mul {α β γ : K} {q : K[X]}
    (h : IsCuboid (C α * q) (C β * q) (C γ * q)) : IsConstCuboid α β γ := by
  have hq : q ≠ 0 := by rintro rfl; exact h.ne_a (mul_zero _)
  have hne : ∀ x : K, C x * q ≠ 0 → x ≠ 0 := fun x hx h0 => hx (by rw [h0, C_0, zero_mul])
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  refine ⟨hne _ h.ne_a, hne _ h.ne_b, hne _ h.ne_c, isSquare_of_C_mul_sq (s := d) hq ?_,
    isSquare_of_C_mul_sq (s := e) hq ?_, isSquare_of_C_mul_sq (s := f) hq ?_,
    isSquare_of_C_mul_sq (s := g) hq ?_⟩
  · rw [sq d, ← hd]; simp only [map_add, map_pow]; ring
  · rw [sq e, ← he]; simp only [map_add, map_pow]; ring
  · rw [sq f, ← hf]; simp only [map_add, map_pow]; ring
  · rw [sq g, ← hg]; simp only [map_add, map_pow]; ring

theorem _root_.PerfectCuboid.PolyCharP.Proportional.isConstCuboid {a b c : K[X]}
    (h : IsCuboid a b c) (hp : Proportional a b c) : ∃ α β γ : K, IsConstCuboid α β γ := by
  obtain ⟨q, α, β, γ, rfl, rfl, rfl⟩ := hp
  exact ⟨α, β, γ, isConstCuboid_of_isCuboid_mul h⟩

theorem isCuboid_C_iff {α β γ : K} : IsCuboid (C α) (C β) (C γ) ↔ IsConstCuboid α β γ := by
  constructor
  · intro h
    exact isConstCuboid_of_isCuboid_mul (q := 1) (by simpa only [mul_one] using h)
  · rintro ⟨ha, hb, hc, h1, h2, h3, h4⟩
    refine ⟨C_ne_zero.2 ha, C_ne_zero.2 hb, C_ne_zero.2 hc, ?_, ?_, ?_, ?_⟩
    · rw [← C_pow, ← C_pow, ← C_add, isSquare_C_iff]; exact h1
    · rw [← C_pow, ← C_pow, ← C_add, isSquare_C_iff]; exact h2
    · rw [← C_pow, ← C_pow, ← C_add, isSquare_C_iff]; exact h3
    · rw [← C_pow, ← C_pow, ← C_pow, ← C_add, ← C_add, isSquare_C_iff]; exact h4

/-! ## Pythagorean legs over `K[X]` -/

/-- For a primitive Pythagorean triple, `z - y` and `z + y` are coprime (`2 ≠ 0`). -/
theorem isCoprime_sub_add (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hxy : IsCoprime x y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : IsCoprime (z - y) (z + y) := by
  have hyz : IsCoprime y z := by
    have h1 : IsCoprime y (x ^ 2) := hxy.symm.pow_right
    have h2' : IsCoprime y (z ^ 2) := by
      have := h1.add_mul_left_right y
      rwa [show x ^ 2 + y * y = z ^ 2 by linear_combination h] at this
    exact (IsCoprime.pow_right_iff two_pos).mp h2'
  obtain ⟨u, v, huv⟩ := hyz
  refine ⟨C (1 / 2) * (v - u), C (1 / 2) * (u + v), ?_⟩
  linear_combination (u * y + v * z) * C_half_mul_two h2 + huv

/-- In a coprime factorization `p q = c X ^ m` one of the two factors is a unit. -/
theorem isUnit_or_isUnit_of_mul_eq_C_mul_X_pow {p q : K[X]} {c : K} {m : ℕ} (hc : c ≠ 0)
    (hpq : IsCoprime p q) (h : p * q = C c * X ^ m) : IsUnit p ∨ IsUnit q := by
  have hcu : IsUnit (C c) := isUnit_C.mpr (Ne.isUnit hc)
  have key : ∀ p q : K[X], p * q = C c * X ^ m → ¬ X ∣ p → IsUnit p := by
    intro p q h hX
    have h1 : IsCoprime (X ^ m) p :=
      ((irreducible_X.coprime_iff_not_dvd).mpr hX).pow_left
    have h2 : p ∣ X ^ m * C c := ⟨q, by rw [h, mul_comm]⟩
    exact isUnit_of_dvd_unit (h1.symm.dvd_of_dvd_mul_left h2) hcu
  by_cases hp : X ∣ p
  · by_cases hq : X ∣ q
    · exact absurd (hpq.isUnit_of_dvd' hp hq) (not_isUnit_X)
    · exact Or.inr (key q p (by rw [mul_comm]; exact h) hq)
  · exact Or.inl (key p q h hp)

/-- A face `(α X^k, b, d)` with `b` coprime to the monomial leg: `2b = v X^{2k} − u`,
`u v = α²`. -/
theorem monomial_leg (h2 : (2 : K) ≠ 0) {α : K} {k : ℕ} {b d : K[X]} (hα : α ≠ 0)
    (hab : IsCoprime (C α * X ^ k) b) (h : (C α * X ^ k) ^ 2 + b ^ 2 = d ^ 2) :
    ∃ u v : K, u * v = α ^ 2 ∧ 2 * b = C v * X ^ (2 * k) - C u := by
  have hcop := isCoprime_sub_add h2 hab h
  have hprod : (d - b) * (d + b) = C (α ^ 2) * X ^ (2 * k) := by
    rw [C_pow]; linear_combination -h
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero _ hα
  rcases isUnit_or_isUnit_of_mul_eq_C_mul_X_pow hα2 hcop hprod with hu | hu
  · obtain ⟨u, hu0, hCu⟩ := Polynomial.isUnit_iff.mp hu
    have hu0 := hu0.ne_zero
    have hdb : d + b = C (u⁻¹ * α ^ 2) * X ^ (2 * k) := by
      have : d + b = C u⁻¹ * ((d - b) * (d + b)) := by
        rw [← hCu, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hu0, C_1, one_mul]
      rw [this, hprod, C_mul, mul_assoc]
    refine ⟨u, u⁻¹ * α ^ 2, by field_simp, ?_⟩
    rw [← hdb, hCu]
    ring
  · obtain ⟨w, hw0, hCw⟩ := Polynomial.isUnit_iff.mp hu
    have hw0 := hw0.ne_zero
    have hdb : d - b = C (w⁻¹ * α ^ 2) * X ^ (2 * k) := by
      have : d - b = C w⁻¹ * ((d - b) * (d + b)) := by
        rw [← hCw, mul_comm (d - b), ← mul_assoc, ← C_mul, inv_mul_cancel₀ hw0, C_1, one_mul]
      rw [this, hprod, C_mul, mul_assoc]
    refine ⟨-w, -(w⁻¹ * α ^ 2), by field_simp, ?_⟩
    simp only [map_neg]
    linear_combination -hCw - hdb

/-- **Discriminant lemma** (any field with `2 ≠ 0`): if `A X^{2n} + B X^n + D` (`A ≠ 0`,
`n ≥ 1`) is a square in `K[X]`, then `B² = 4AD`. -/
theorem quad_disc (h2 : (2 : K) ≠ 0) {F : K[X]} {A B D : K} {n : ℕ} (hn : 0 < n) (hA : A ≠ 0)
    (h : F ^ 2 = C A * X ^ (2 * n) + C B * X ^ n + C D) : B ^ 2 = 4 * A * D := by
  have hdeg : (C A * X ^ (2 * n) + C B * X ^ n + C D).natDegree = 2 * n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · refine (natDegree_add_le _ _).trans
        (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
      · exact (natDegree_C_mul_X_pow_le _ _)
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · simp
    · simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
      simp [show 2 * n ≠ n by omega, show 2 * n ≠ 0 by omega, hA]
  have hcoeff : (C A * X ^ (2 * n) + C B * X ^ n + C D).coeff (2 * n) = A := by
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
    simp [show 2 * n ≠ n by omega, show 2 * n ≠ 0 by omega]
  have hF : F.natDegree = n := by
    have := congrArg natDegree h
    rw [natDegree_pow, hdeg] at this
    omega
  have hP : F.leadingCoeff ^ 2 = A := by
    rw [← hcoeff, ← h, ← hF, coeff_pow_mul_natDegree]
  by_contra hne
  have hδ : B ^ 2 - 4 * A * D ≠ 0 := sub_ne_zero.mpr hne
  set s : K[X] := C (2 * A) * X ^ n + C B with hs
  set t : K[X] := C (2 * F.leadingCoeff) * F with ht
  have hPC : C F.leadingCoeff ^ 2 = C A := by rw [← C_pow, hP]
  have hst : (s - t) * (s + t) = C (B ^ 2 - 4 * A * D) := by
    rw [hs, ht]
    simp only [map_mul, map_sub, map_pow, map_ofNat]
    linear_combination (-4 * C A) * h - 4 * F ^ 2 * hPC
  have hne1 : s - t ≠ 0 := by
    intro h0; rw [h0, zero_mul, eq_comm, C_eq_zero] at hst; exact hδ hst
  have hne2 : s + t ≠ 0 := by
    intro h0; rw [h0, mul_zero, eq_comm, C_eq_zero] at hst; exact hδ hst
  have hsum := natDegree_mul hne1 hne2
  rw [hst, natDegree_C] at hsum
  have h2s : (2 * s).natDegree = 0 := by
    have : 2 * s = (s - t) + (s + t) := by ring
    rw [this]
    exact Nat.eq_zero_of_le_zero ((natDegree_add_le _ _).trans (by omega))
  have hs0 := natDegree_eq_zero_of_two_mul h2 h2s
  have hsdeg : s.natDegree = n := by
    rw [hs]
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · refine (natDegree_add_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _) ?_)
      simp
    · simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
      simp [show n ≠ 0 by omega, hA, h2]
  omega

theorem four_ne_zero' (h2 : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2

/-- **Polynomial Korec (coprime case), face-cuboid form**, for `¬ IsSquare (-1)`, `2 ≠ 0`. -/
theorem not_squares_of_monomial (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {α : K} {k : ℕ}
    {b c : K[X]} (hα : α ≠ 0) (hk : 0 < k)
    (hb : IsCoprime (C α * X ^ k) b) (hc : IsCoprime (C α * X ^ k) c)
    (hab : IsSquare ((C α * X ^ k) ^ 2 + b ^ 2)) (hac : IsSquare ((C α * X ^ k) ^ 2 + c ^ 2))
    (habc : IsSquare ((C α * X ^ k) ^ 2 + b ^ 2 + c ^ 2)) : False := by
  obtain ⟨d, hd⟩ := hab
  obtain ⟨e, he⟩ := hac
  obtain ⟨g, hg⟩ := habc
  rw [← sq] at hd he hg
  obtain ⟨u, v, huv, hb2⟩ := monomial_leg h2 hα hb hd
  obtain ⟨u', v', huv', hc2⟩ := monomial_leg h2 hα hc he
  have hv : v ≠ 0 := by rintro rfl; rw [mul_zero] at huv; exact pow_ne_zero 2 hα huv.symm
  have hu : u ≠ 0 := by rintro rfl; rw [zero_mul] at huv; exact pow_ne_zero 2 hα huv.symm
  have hv' : v' ≠ 0 := by rintro rfl; rw [mul_zero] at huv'; exact pow_ne_zero 2 hα huv'.symm
  have hu' : u' ≠ 0 := by rintro rfl; rw [zero_mul] at huv'; exact pow_ne_zero 2 hα huv'.symm
  have hCuv : C u * C v = C α ^ 2 := by rw [← C_mul, huv, C_pow]
  have hCuv' : C u' * C v' = C α ^ 2 := by rw [← C_mul, huv', C_pow]
  have key : (2 * g) ^ 2 = C (v ^ 2 + v' ^ 2) * X ^ (2 * (2 * k)) + C 0 * X ^ (2 * k) +
      C (u ^ 2 + u' ^ 2) := by
    simp only [map_add, map_pow, map_zero, zero_mul, add_zero]
    linear_combination (-4) * hg + (2 * b + (C v * X ^ (2 * k) - C u)) * hb2 +
      (2 * c + (C v' * X ^ (2 * k) - C u')) * hc2 + (-2 * X ^ (2 * k)) * hCuv +
      (-2 * X ^ (2 * k)) * hCuv'
  have hA : v ^ 2 + v' ^ 2 ≠ 0 := sq_add_sq_ne_zero hK hv'
  have hD : u ^ 2 + u' ^ 2 ≠ 0 := sq_add_sq_ne_zero hK hu'
  have := quad_disc h2 (by omega) hA key
  rw [sq, zero_mul, eq_comm] at this
  exact mul_ne_zero (mul_ne_zero (four_ne_zero' h2) hA) hD this

/-! ## Symmetries and translations of `IsCuboid` -/

theorem isCuboid_swap_ab {a b c : K[X]} (h : IsCuboid a b c) : IsCuboid b a c where
  ne_a := h.ne_b
  ne_b := h.ne_a
  ne_c := h.ne_c
  sq_ab := by convert h.sq_ab using 1; ring
  sq_ac := h.sq_bc
  sq_bc := h.sq_ac
  sq_abc := by convert h.sq_abc using 1; ring

theorem isCuboid_swap_bc {a b c : K[X]} (h : IsCuboid a b c) : IsCuboid a c b where
  ne_a := h.ne_a
  ne_b := h.ne_c
  ne_c := h.ne_b
  sq_ab := h.sq_ac
  sq_ac := h.sq_ab
  sq_bc := by convert h.sq_bc using 1; ring
  sq_abc := by convert h.sq_abc using 1; ring

theorem isCuboid_swap_ac {a b c : K[X]} (h : IsCuboid a b c) : IsCuboid c b a where
  ne_a := h.ne_c
  ne_b := h.ne_b
  ne_c := h.ne_a
  sq_ab := by convert h.sq_bc using 1; ring
  sq_ac := by convert h.sq_ac using 1; ring
  sq_bc := by convert h.sq_ab using 1; ring
  sq_abc := by convert h.sq_abc using 1; ring

theorem comp_X_add_C_comp_X_sub_C (p : K[X]) (r : K) :
    (p.comp (X + C r)).comp (X - C r) = p := by
  rw [comp_assoc]
  simp

/-- Translation `X ↦ X + r` maps cuboids to cuboids. -/
theorem isCuboid_comp_X_add_C {a b c : K[X]} (h : IsCuboid a b c) (r : K) :
    IsCuboid (a.comp (X + C r)) (b.comp (X + C r)) (c.comp (X + C r)) := by
  have hne : ∀ p : K[X], p ≠ 0 → p.comp (X + C r) ≠ 0 := by
    intro p hp h0
    apply hp
    rw [← comp_X_add_C_comp_X_sub_C p r, h0, zero_comp]
  have hsq : ∀ p : K[X], IsSquare p → IsSquare (p.comp (X + C r)) := by
    intro p hp
    simpa [coe_compRingHom_apply] using hp.map (compRingHom (X + C r))
  refine ⟨hne a h.ne_a, hne b h.ne_b, hne c h.ne_c, ?_, ?_, ?_, ?_⟩
  · simpa [add_comp, pow_comp] using hsq _ h.sq_ab
  · simpa [add_comp, pow_comp] using hsq _ h.sq_ac
  · simpa [add_comp, pow_comp] using hsq _ h.sq_bc
  · simpa [add_comp, pow_comp] using hsq _ h.sq_abc

/-! ## Linear edges -/

/-- In a face `(α X, b, d)` with `X ∣ b`, the leg `b` is `β X`. -/
theorem linear_leg_of_X_dvd (h2 : (2 : K) ≠ 0) {α : K} {b d : K[X]} (hα : α ≠ 0)
    (h : (C α * X) ^ 2 + b ^ 2 = d ^ 2) (hX : X ∣ b) : ∃ β : K, b = C β * X := by
  obtain ⟨b1, rfl⟩ := hX
  have hXd : X ∣ d := by
    apply prime_X.dvd_of_dvd_pow (n := 2)
    rw [← h]
    exact ⟨(C α) ^ 2 * X + b1 ^ 2 * X, by ring⟩
  obtain ⟨d1, rfl⟩ := hXd
  have h1 : (C α) ^ 2 + b1 ^ 2 = d1 ^ 2 := by
    have : X ^ 2 * ((C α) ^ 2 + b1 ^ 2) = X ^ 2 * d1 ^ 2 := by linear_combination h
    exact mul_left_cancel₀ (pow_ne_zero 2 X_ne_zero) this
  have hCα : C α ≠ 0 := C_ne_zero.mpr hα
  have h0 := (natDegree_eq_zero_of_leg h2 hCα (natDegree_C α) h1).1
  have hb1 := eq_C_of_natDegree_eq_zero h0
  refine ⟨b1.coeff 0, ?_⟩
  rw [mul_comm X b1]
  exact congrArg (· * X) hb1

theorem isCoprime_C_mul_X_of_not_dvd {α : K} {b : K[X]} (hα : α ≠ 0) (hX : ¬ X ∣ b) :
    IsCoprime (C α * X ^ 1) b := by
  have hC : IsCoprime (C α) b := ⟨C α⁻¹, 0, by rw [← C_mul, inv_mul_cancel₀ hα, C_1]; ring⟩
  rw [pow_one]
  exact hC.mul_left ((irreducible_X.coprime_iff_not_dvd).mpr hX)

/-- The mixed case: `α X`, `β X` (`β ≠ 0`) and `c` coprime to `X` never give squares
`(αX)² + c²` and `(αX)² + (βX)² + c²`. -/
theorem not_squares_linear_mixed (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {α β : K}
    {c : K[X]} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hc : IsCoprime (C α * X ^ 1) c) (hac : IsSquare ((C α * X) ^ 2 + c ^ 2))
    (habc : IsSquare ((C α * X) ^ 2 + (C β * X) ^ 2 + c ^ 2)) : False := by
  obtain ⟨e, he⟩ := hac
  obtain ⟨g, hg⟩ := habc
  rw [← sq] at he hg
  obtain ⟨u, v, huv, hc2⟩ := monomial_leg h2 hα hc (by rw [pow_one]; exact he)
  have hv : v ≠ 0 := by rintro rfl; rw [mul_zero] at huv; exact pow_ne_zero 2 hα huv.symm
  have hCuv : C u * C v = C α ^ 2 := by rw [← C_mul, huv, C_pow]
  have key : (2 * g) ^ 2 = C (v ^ 2) * X ^ (2 * 2) + C (2 * α ^ 2 + 4 * β ^ 2) * X ^ 2 +
      C (u ^ 2) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    linear_combination (-4) * hg + (2 * c + (C v * X ^ (2 * 1) - C u)) * hc2 +
      (-2 * X ^ 2) * hCuv
  have hd := quad_disc h2 (by norm_num) (pow_ne_zero 2 hv) key
  have h1 : (u * v) ^ 2 = (α ^ 2) ^ 2 := by rw [huv]
  have h3 : (2 * 2 * 2 * 2) * (β ^ 2 * (α ^ 2 + β ^ 2)) = 0 := by
    linear_combination hd + 4 * h1
  have h4 : β ^ 2 * (α ^ 2 + β ^ 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hβ) (sq_add_sq_ne_zero hK hβ)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2) h4 h3

/-- **Linear edge ⇒ proportional** over any field with `¬ IsSquare (-1)` and `2 ≠ 0`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_linear_edge
    (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {α : K} {b c : K[X]}
    (h : IsCuboid (C α * X) b c) : ∃ β γ : K, b = C β * X ∧ c = C γ * X := by
  have hα : α ≠ 0 := by rintro rfl; exact h.ne_a (by simp)
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  rw [← sq] at hd he
  by_cases hb : X ∣ b <;> by_cases hc : X ∣ c
  · obtain ⟨β, hβ⟩ := linear_leg_of_X_dvd h2 hα hd hb
    obtain ⟨γ, hγ⟩ := linear_leg_of_X_dvd h2 hα he hc
    exact ⟨β, γ, hβ, hγ⟩
  · exfalso
    obtain ⟨β, rfl⟩ := linear_leg_of_X_dvd h2 hα hd hb
    have hβ : β ≠ 0 := by rintro rfl; exact h.ne_b (by simp)
    exact not_squares_linear_mixed hK h2 hα hβ (isCoprime_C_mul_X_of_not_dvd hα hc) h.sq_ac
      h.sq_abc
  · exfalso
    obtain ⟨γ, rfl⟩ := linear_leg_of_X_dvd h2 hα he hc
    have hγ : γ ≠ 0 := by rintro rfl; exact h.ne_c (by simp)
    exact not_squares_linear_mixed hK h2 hα hγ (isCoprime_C_mul_X_of_not_dvd hα hb) h.sq_ab
      (by convert h.sq_abc using 1; ring)
  · exfalso
    have hab := isCoprime_C_mul_X_of_not_dvd hα hb
    have hac := isCoprime_C_mul_X_of_not_dvd hα hc
    exact not_squares_of_monomial hK h2 hα one_pos hab hac (by rw [pow_one]; exact h.sq_ab)
      (by rw [pow_one]; exact h.sq_ac) (by rw [pow_one]; exact h.sq_abc)

/-- A polynomial of degree one becomes `α X` after a translation. -/
theorem exists_comp_eq_C_mul_X {a : K[X]} (ha : a.natDegree = 1) :
    ∃ α r : K, a.comp (X + C r) = C α * X := by
  have hne : a ≠ 0 := by rintro rfl; simp at ha
  have ha1 : a.coeff 1 ≠ 0 := by
    have := leadingCoeff_ne_zero.mpr hne
    rwa [leadingCoeff, ha] at this
  refine ⟨a.coeff 1, -(a.coeff 0) / a.coeff 1, ?_⟩
  have hexp := eq_X_add_C_of_natDegree_le_one ha.le
  have key : a.coeff 1 * (-(a.coeff 0) / a.coeff 1) + a.coeff 0 = 0 := by
    field_simp; ring
  calc a.comp (X + C (-(a.coeff 0) / a.coeff 1))
      = (C (a.coeff 1) * X + C (a.coeff 0)).comp (X + C (-(a.coeff 0) / a.coeff 1)) := by
        rw [← hexp]
    _ = C (a.coeff 1) * X + C (a.coeff 1 * (-(a.coeff 0) / a.coeff 1) + a.coeff 0) := by
        simp only [add_comp, mul_comp, C_comp, X_comp, map_add, map_mul]; ring
    _ = C (a.coeff 1) * X := by rw [key, C_0, add_zero]

/-- **Degree-one edge ⇒ proportional** over any field with `¬ IsSquare (-1)` and `2 ≠ 0`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_natDegree_eq_one
    (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsCuboid a b c)
    (ha : a.natDegree = 1) : Proportional a b c := by
  obtain ⟨α, r, hr⟩ := exists_comp_eq_C_mul_X ha
  have h' := isCuboid_comp_X_add_C h r
  rw [hr] at h'
  obtain ⟨β, γ, hb, hc⟩ := h'.proportional_of_linear_edge hK h2
  refine ⟨X - C r, α, β, γ, ?_, ?_, ?_⟩
  · rw [← comp_X_add_C_comp_X_sub_C a r, hr]; simp
  · rw [← comp_X_add_C_comp_X_sub_C b r, hb]; simp
  · rw [← comp_X_add_C_comp_X_sub_C c r, hc]; simp

/-! ## No constant cuboid ⇒ every edge has degree `≥ 2` -/

/-- If `K` has no constant cuboid (and `2 ≠ 0`), no cuboid over `K[X]` has a constant edge. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.natDegree_ne_zero (h2 : (2 : K) ≠ 0)
    (h0 : ∀ α β γ : K, ¬ IsConstCuboid α β γ) {a b c : K[X]} (h : IsCuboid a b c) :
    a.natDegree ≠ 0 := by
  intro ha
  rw [eq_C_of_natDegree_eq_zero ha] at h
  obtain ⟨α, β, γ, hc⟩ := (h.proportional_of_const h2).isConstCuboid h
  exact h0 _ _ _ hc

/-- If `−1` is not a square, `2 ≠ 0` and `K` has no constant cuboid, every edge of a cuboid
over `K[X]` has degree `≥ 2`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.two_le_natDegree (hK : ¬ IsSquare (-1 : K))
    (h2 : (2 : K) ≠ 0) (h0 : ∀ α β γ : K, ¬ IsConstCuboid α β γ) {a b c : K[X]}
    (h : IsCuboid a b c) : 2 ≤ a.natDegree := by
  have hne := h.natDegree_ne_zero h2 h0
  by_contra hlt
  have h1 : a.natDegree = 1 := by omega
  obtain ⟨α, β, γ, hc⟩ := (h.proportional_of_natDegree_eq_one hK h2 h1).isConstCuboid h
  exact h0 _ _ _ hc

theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.two_le_natDegree_all (hK : ¬ IsSquare (-1 : K))
    (h2 : (2 : K) ≠ 0) (h0 : ∀ α β γ : K, ¬ IsConstCuboid α β γ) {a b c : K[X]}
    (h : IsCuboid a b c) : 2 ≤ a.natDegree ∧ 2 ≤ b.natDegree ∧ 2 ≤ c.natDegree :=
  ⟨h.two_le_natDegree hK h2 h0, (isCuboid_swap_ab h).two_le_natDegree hK h2 h0,
    (isCuboid_swap_ac h).two_le_natDegree hK h2 h0⟩

/-! ## `𝔽_p`, `p ≡ 3 (mod 4)` -/

theorem zmod_not_isSquare_neg_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    ¬ IsSquare (-1 : ZMod p) :=
  fun hs => ZMod.exists_sq_eq_neg_one_iff.1 hs hp

theorem zmod_two_ne_zero {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this
  exact hp2 this

/-- For `p ≡ 3 (mod 4)`, a cuboid over `𝔽_p[X]` with an edge of degree `≤ 1` is proportional. -/
theorem zmod_proportional_of_natDegree_le_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {a b c : (ZMod p)[X]} (h : IsCuboid a b c) (ha : a.natDegree ≤ 1) : Proportional a b c := by
  have h2 := zmod_two_ne_zero (p := p) (by omega)
  rcases (show a.natDegree = 0 ∨ a.natDegree = 1 by omega) with h1 | h1
  · rw [eq_C_of_natDegree_eq_zero h1] at h ⊢
    exact h.proportional_of_const h2
  · exact h.proportional_of_natDegree_eq_one (zmod_not_isSquare_neg_one hp) h2 h1

section Instances
local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance fact_prime_nineteen : Fact (Nat.Prime 19) := ⟨by norm_num⟩
local instance fact_prime_twentythree : Fact (Nat.Prime 23) := ⟨by norm_num⟩

/-- **No constant cuboid over `𝔽₃`, `𝔽₇`, `𝔽₁₁`, `𝔽₁₉`** (kernel `decide`). -/
theorem not_isConstCuboid_three : ∀ α β γ : ZMod 3, ¬ IsConstCuboid α β γ := by
  unfold IsConstCuboid; decide +kernel

theorem not_isConstCuboid_seven : ∀ α β γ : ZMod 7, ¬ IsConstCuboid α β γ := by
  unfold IsConstCuboid; decide +kernel

theorem not_isConstCuboid_eleven : ∀ α β γ : ZMod 11, ¬ IsConstCuboid α β γ := by
  unfold IsConstCuboid; decide +kernel

theorem not_isConstCuboid_nineteen : ∀ α β γ : ZMod 19, ¬ IsConstCuboid α β γ := by
  unfold IsConstCuboid; decide +kernel

/-- Near-miss: over `𝔽₂₃`, `(1, 1, 1)` is a constant cuboid (`2 = 5²`, `3 = 7²`), so the
"no constant cuboid" hypothesis cannot be dropped for every `p ≡ 3 (mod 4)`. -/
theorem isConstCuboid_twentythree : IsConstCuboid (1 : ZMod 23) 1 1 := by
  unfold IsConstCuboid; decide +kernel

theorem no_const_cuboid_three : ∀ α β γ : ZMod 3, ¬ IsCuboid (C α) (C β) (C γ) :=
  fun α β γ h => not_isConstCuboid_three α β γ (isCuboid_C_iff.1 h)

theorem no_const_cuboid_seven : ∀ α β γ : ZMod 7, ¬ IsCuboid (C α) (C β) (C γ) :=
  fun α β γ h => not_isConstCuboid_seven α β γ (isCuboid_C_iff.1 h)

theorem no_const_cuboid_eleven : ∀ α β γ : ZMod 11, ¬ IsCuboid (C α) (C β) (C γ) :=
  fun α β γ h => not_isConstCuboid_eleven α β γ (isCuboid_C_iff.1 h)

theorem no_const_cuboid_nineteen : ∀ α β γ : ZMod 19, ¬ IsCuboid (C α) (C β) (C γ) :=
  fun α β γ h => not_isConstCuboid_nineteen α β γ (isCuboid_C_iff.1 h)


/-- **Every edge of a cuboid over `𝔽₃[X]` has degree `≥ 2`.** -/
theorem no_cuboid_natDegree_le_one_three :
    ∀ a b c : (ZMod 3)[X], IsCuboid a b c → 2 ≤ a.natDegree :=
  fun _ _ _ h => h.two_le_natDegree (zmod_not_isSquare_neg_one (by norm_num)) (by decide)
    not_isConstCuboid_three

theorem no_cuboid_natDegree_le_one_three_all :
    ∀ a b c : (ZMod 3)[X], IsCuboid a b c →
      2 ≤ a.natDegree ∧ 2 ≤ b.natDegree ∧ 2 ≤ c.natDegree :=
  fun _ _ _ h => h.two_le_natDegree_all (zmod_not_isSquare_neg_one (by norm_num)) (by decide)
    not_isConstCuboid_three

theorem no_cuboid_natDegree_le_one_seven :
    ∀ a b c : (ZMod 7)[X], IsCuboid a b c →
      2 ≤ a.natDegree ∧ 2 ≤ b.natDegree ∧ 2 ≤ c.natDegree :=
  fun _ _ _ h => h.two_le_natDegree_all (zmod_not_isSquare_neg_one (by norm_num)) (by decide)
    not_isConstCuboid_seven

theorem no_cuboid_natDegree_le_one_eleven :
    ∀ a b c : (ZMod 11)[X], IsCuboid a b c →
      2 ≤ a.natDegree ∧ 2 ≤ b.natDegree ∧ 2 ≤ c.natDegree :=
  fun _ _ _ h => h.two_le_natDegree_all (zmod_not_isSquare_neg_one (by norm_num)) (by decide)
    not_isConstCuboid_eleven

theorem no_cuboid_natDegree_le_one_nineteen :
    ∀ a b c : (ZMod 19)[X], IsCuboid a b c →
      2 ≤ a.natDegree ∧ 2 ≤ b.natDegree ∧ 2 ≤ c.natDegree :=
  fun _ _ _ h => h.two_le_natDegree_all (zmod_not_isSquare_neg_one (by norm_num)) (by decide)
    not_isConstCuboid_nineteen

/-! ## A nondegenerate non-proportional cuboid over `𝔽₇[X]` -/

theorem seven_eq_zero : (7 : (ZMod 7)[X]) = 0 := by
  have : ((7 : ℕ) : (ZMod 7)[X]) = 0 := CharP.cast_eq_zero _ 7
  exact_mod_cast this

/-- **A cuboid over `𝔽₇[X]`** (found by the round-17 search, `code/b3/cubsearch.c`):
`a = X⁶ + 3X⁴ + 2X² = X²(X² + 1)(X² + 2)`, `b = X⁸ + 6X⁶ + 4X⁴ + 5X² + 4`, `c = X⁷ + 6X = X⁷ − X`,
with `a² + b² = (X⁸ + 6X⁶ + X⁴ + 5X² + 4)²`, `a² + c² = (X⁷ + 4X⁵ + 2X³ + X)²`,
`b² + c² = (X⁸ + 3X⁶ + X² + 3)²`, `a² + b² + c² = (X⁸ + 3X⁶ + 4X⁴ + 6X² + 4)²`. -/
theorem isCuboid_seven :
    IsCuboid (X ^ 6 + 3 * X ^ 4 + 2 * X ^ 2 : (ZMod 7)[X])
      (X ^ 8 + 6 * X ^ 6 + 4 * X ^ 4 + 5 * X ^ 2 + 4) (X ^ 7 + 6 * X) where
  ne_a := by
    have hd : (X ^ 6 + 3 * X ^ 4 + 2 * X ^ 2 : (ZMod 7)[X]).natDegree = 6 := by compute_degree!
    intro h; rw [h, natDegree_zero] at hd; omega
  ne_b := by
    have hd : (X ^ 8 + 6 * X ^ 6 + 4 * X ^ 4 + 5 * X ^ 2 + 4 : (ZMod 7)[X]).natDegree = 8 := by
      compute_degree!
    intro h; rw [h, natDegree_zero] at hd; omega
  ne_c := by
    have hd : (X ^ 7 + 6 * X : (ZMod 7)[X]).natDegree = 7 := by compute_degree!
    intro h; rw [h, natDegree_zero] at hd; omega
  sq_ab := ⟨X ^ 8 + 6 * X ^ 6 + X ^ 4 + 5 * X ^ 2 + 4, by
    linear_combination (4 * X ^ 4 + 6 * X ^ 6 + 4 * X ^ 8 + 6 * X ^ 10 + X ^ 12) * seven_eq_zero⟩
  sq_ac := ⟨X ^ 7 + 4 * X ^ 5 + 2 * X ^ 3 + X, by
    linear_combination (5 * X ^ 2 + X ^ 8 - 2 * X ^ 10 - X ^ 12) * seven_eq_zero⟩
  sq_bc := ⟨X ^ 8 + 3 * X ^ 6 + X ^ 2 + 3, by
    linear_combination (1 + 10 * X ^ 2 + 8 * X ^ 4 + 10 * X ^ 6 + 12 * X ^ 8 + 8 * X ^ 10 +
      5 * X ^ 12 + X ^ 14) * seven_eq_zero⟩
  sq_abc := ⟨X ^ 8 + 3 * X ^ 6 + 4 * X ^ 4 + 6 * X ^ 2 + 4, by
    linear_combination (4 * X ^ 2 - X ^ 4 + 4 * X ^ 6 + 7 * X ^ 8 + 4 * X ^ 10 + 4 * X ^ 12 +
      X ^ 14) * seven_eq_zero⟩

/-- The `𝔽₇` cuboid is nondegenerate (automatic for `p ≡ 3 (mod 4)`). -/
theorem isNondegCuboid_seven :
    IsNondegCuboid (X ^ 6 + 3 * X ^ 4 + 2 * X ^ 2 : (ZMod 7)[X])
      (X ^ 8 + 6 * X ^ 6 + 4 * X ^ 4 + 5 * X ^ 2 + 4) (X ^ 7 + 6 * X) :=
  isCuboid_seven.isNondegCuboid_of_mod_four_eq_three (by norm_num)

/-- The `𝔽₇` cuboid is not proportional (edge degrees `6, 8, 7`). -/
theorem not_proportional_seven :
    ¬ Proportional (X ^ 6 + 3 * X ^ 4 + 2 * X ^ 2 : (ZMod 7)[X])
      (X ^ 8 + 6 * X ^ 6 + 4 * X ^ 4 + 5 * X ^ 2 + 4) (X ^ 7 + 6 * X) := by
  apply not_proportional_of_natDegree_ne isCuboid_seven.ne_a isCuboid_seven.ne_b
  have h1 : (X ^ 6 + 3 * X ^ 4 + 2 * X ^ 2 : (ZMod 7)[X]).natDegree = 6 := by compute_degree!
  have h2 : (X ^ 8 + 6 * X ^ 6 + 4 * X ^ 4 + 5 * X ^ 2 + 4 : (ZMod 7)[X]).natDegree = 8 := by
    compute_degree!
  rw [h1, h2]; omega

/-- **Over `𝔽₇` (where `−1` is not a square) there are nondegenerate non-proportional
cuboids.** So "`¬ IsSquare (-1)` ⇒ proportional" is false in positive characteristic: the
degree-`≤ 1` theorems above are not the start of a general proportionality theorem over `𝔽_p`. -/
theorem exists_nondeg_not_proportional_seven :
    ∃ a b c : (ZMod 7)[X], IsNondegCuboid a b c ∧ ¬ Proportional a b c :=
  ⟨_, _, _, isNondegCuboid_seven, not_proportional_seven⟩

end Instances

/-! ## Near-miss data: an Euler brick over `𝔽₃[X]` with a monomial edge -/

theorem three_eq_zero : (3 : (ZMod 3)[X]) = 0 := by
  have : ((3 : ℕ) : (ZMod 3)[X]) = 0 := CharP.cast_eq_zero _ 3
  exact_mod_cast this

/-- The smallest polynomial Euler brick over `𝔽₃[X]` found by the search: `(X³, X⁶ − 1, X⁵ − X)`
with `a² + b² = (X⁶ + 1)²`, `a² + c² = (X⁵ + X)²`, `b² + c² = (X⁶ − X⁴ + X² − 1)²`. (By the search,
no cuboid over `𝔽₃[X]` has an edge of degree `≤ 13`, so `a² + b² + c²` is not a square.) -/
theorem isBrick_three :
    IsSquare ((X ^ 3 : (ZMod 3)[X]) ^ 2 + (X ^ 6 - 1) ^ 2) ∧
      IsSquare ((X ^ 3 : (ZMod 3)[X]) ^ 2 + (X ^ 5 - X) ^ 2) ∧
      IsSquare ((X ^ 6 - 1 : (ZMod 3)[X]) ^ 2 + (X ^ 5 - X) ^ 2) :=
  ⟨⟨X ^ 6 + 1, by linear_combination (-X ^ 6) * three_eq_zero⟩,
    ⟨X ^ 5 + X, by linear_combination (-X ^ 6) * three_eq_zero⟩,
    ⟨X ^ 6 - X ^ 4 + X ^ 2 - 1, by
      linear_combination (X ^ 2 - X ^ 4 - X ^ 8 + X ^ 10) * three_eq_zero⟩⟩

end PerfectCuboid.PolyNegOne
