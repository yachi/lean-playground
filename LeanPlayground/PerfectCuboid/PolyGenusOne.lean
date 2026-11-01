module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolyCharP

/-!
# Constant genus-one curves have no nonconstant `K(X)`-points

Round 17, brief 2. `K` is any field with `2 ≠ 0`.

* **Theorem T2** (`two_forms_proportional`): if `A ≠ B` are nonzero constants, `v ≠ 0`, and
  `u² + A v²`, `u² + B v²` are both squares in `K[X]`, then `u = λ v` with `λ ∈ K`. Equivalently,
  the constant genus-one curve `y² = (x² + A)(x² + B)` has only constant `K(X)`-points.
  Classical, but proved here by an explicit **Fermat descent on degrees** valid in every
  characteristic `≠ 2` (no Mason–Stothers, no Mordell–Weil):
  - shape `IsTwoSquares A B x y`: `x, y` coprime, `x² − A y²` and `x² − B y²` squares;
  - over an algebraically closed field (`IsTwoSquares.descent`), write `A = α²`, `B = β²`; the
    four pairwise-coprime linear forms `x ± α y`, `x ± β y` are squares, `x − α y = p²`,
    `x + α y = q²`, and `(α ± β) p² + (α ∓ β) q² = 2α (x ∓ β y)` are squares, so `(p, q)` has the
    shape for `A' = −(α − β)/(α + β)`, `B' = −(α + β)/(α − β)` with
    `2 max(deg p, deg q) ≤ max(deg x, deg y)` (`IsTwoSquares.natDegree_eq_zero`: strong
    induction);
  - general `K`: divide by `gcd(u, v)`, map to `AlgebraicClosure K`.
* **Cuboid consequences** (`PolyCharP.IsCuboid` / `IsNondegCuboid`, any `K` with `2 ≠ 0`):
  two proportional edges ⇒ proportional (`IsCuboid.proportional_of_edge_mul`,
  `IsCuboid.proportional_of_two_edges`); an edge proportional to its own face diagonal
  (`IsCuboid.proportional_of_diag_eq_edge`), to the opposite face diagonal
  (`IsNondegCuboid.proportional_of_opp_diag_eq_edge`), to the space diagonal
  (`IsNondegCuboid.proportional_of_space_diag_eq_edge`); two face diagonals proportional
  (`IsNondegCuboid.proportional_of_diag_eq_diag`); a face diagonal proportional to the space
  diagonal (`IsNondegCuboid.proportional_of_space_diag_eq_diag`). Up to relabelling these are all
  21 pairs among the seven lengths (one labelling per type is formalised; the relabelling is not). All are consistent with the Frobenius cuboid (no two of its
  lengths are proportional) and with the degenerate `(2X, X² − 1, i(X² + 1))` (`f = i a`, excluded
  by `a² + b² + c² ≠ 0`).
* **Constant congruent numbers** (`not_congruent_const`): `x² + y² = z²`, `x y = 2N s²`, `N ∈ K*`
  ⇒ `x, y ∈ K · s`; corollary `IsNondegCuboid.proportional_of_mul_opp_diag`.
-/

@[expose] public section

open Polynomial

namespace PerfectCuboid.PolyGenusOne

variable {K : Type*} [Field K]

theorem C_inv_two_mul (h2 : (2 : K) ≠ 0) : C (2⁻¹ : K) * 2 = 1 := by
  rw [show (2 : K[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul, inv_mul_cancel₀ h2, C_1]

/-- `x ± α y` are coprime when `x, y` are, `α ≠ 0` and `2 ≠ 0`. -/
theorem isCoprime_sub_add_C (h2 : (2 : K) ≠ 0) {α : K} (hα : α ≠ 0) {x y : K[X]}
    (h : IsCoprime x y) : IsCoprime (x - C α * y) (x + C α * y) := by
  obtain ⟨u, v, huv⟩ := h
  have e1 := C_inv_two_mul h2
  have e2 : C ((2 * α)⁻¹) * (2 * C α) = 1 := by
    rw [show (2 : K[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul, ← C_mul,
      inv_mul_cancel₀ (mul_ne_zero h2 hα), C_1]
  refine ⟨C (2⁻¹ : K) * u - C ((2 * α)⁻¹) * v, C (2⁻¹ : K) * u + C ((2 * α)⁻¹) * v, ?_⟩
  linear_combination huv + u * x * e1 + v * y * e2

/-- The descent shape: `x, y` coprime, `A ≠ B` nonzero constants, and `x² − A y²`,
`x² − B y²` both squares. Over an algebraically closed field this is the general shape
`a₁ x² + b₁ y² = □`, `a₂ x² + b₂ y² = □` with `a₁ b₂ ≠ a₂ b₁` (divide by `a₁`, `a₂`). -/
structure IsTwoSquares (A B : K) (x y : K[X]) : Prop where
  hA : A ≠ 0
  hB : B ≠ 0
  hAB : A ≠ B
  cop : IsCoprime x y
  sqA : IsSquare (x ^ 2 - C A * y ^ 2)
  sqB : IsSquare (x ^ 2 - C B * y ^ 2)

section AlgClosed

variable [IsAlgClosed K]

/-- Over an algebraically closed field, a nonzero constant times a square is a square. -/
theorem isSquare_C_mul_iff {c : K} (hc : c ≠ 0) {f : K[X]} :
    IsSquare (C c * f) ↔ IsSquare f := by
  obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) two_pos
  have he0 : e ≠ 0 := by rintro rfl; simp at he; exact hc he.symm
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨C e⁻¹ * h, ?_⟩
    have : f = C (c⁻¹) * (C c * f) := by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
    rw [this, hh, ← he, show (e ^ 2)⁻¹ = e⁻¹ * e⁻¹ by ring, C_mul]
    ring
  · rintro ⟨h, rfl⟩
    exact ⟨C e * h, by rw [← he, map_pow]; ring⟩

/-- Over an algebraically closed field, a coprime factor of a square is a square. -/
theorem isSquare_of_isCoprime {f g : K[X]} (hfg : IsCoprime f g) (h : IsSquare (f * g)) :
    IsSquare f := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨d, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hfg (k := 2) (by rw [hm]; ring)
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  rw [← hu, ← hcu, mul_comm]
  exact (isSquare_C_mul_iff hc.ne_zero).mpr ⟨d, sq d⟩

/-- **The descent step.** Write `A = α²`, `B = β²`. The four linear forms `x ± α y`, `x ± β y`
are pairwise-coprime factors of squares, hence squares: `x − α y = p²`, `x + α y = q²`. Then
`(α + β) p² + (α − β) q² = 2α (x − β y)` and `(α − β) p² + (α + β) q² = 2α (x + β y)` are squares,
so `(p, q)` has the shape again with `A' = −(α − β)/(α + β)`, `B' = −(α + β)/(α − β)`
(`A' B' = 1`, `A' ≠ B'`), and `2 deg p, 2 deg q ≤ max (deg x) (deg y)`. -/
theorem IsTwoSquares.descent (h2 : (2 : K) ≠ 0) {A B : K} {x y : K[X]}
    (h : IsTwoSquares A B x y) :
    ∃ (A' B' : K) (p q : K[X]), IsTwoSquares A' B' p q ∧
      2 * p.natDegree ≤ max x.natDegree y.natDegree ∧
      2 * q.natDegree ≤ max x.natDegree y.natDegree ∧
      (p.natDegree = 0 → q.natDegree = 0 → x.natDegree = 0 ∧ y.natDegree = 0) := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq A (n := 2) two_pos
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq B (n := 2) two_pos
  have hα0 : α ≠ 0 := by rintro rfl; exact h.hA (by rw [← hα]; ring)
  have hβ0 : β ≠ 0 := by rintro rfl; exact h.hB (by rw [← hβ]; ring)
  have hab1 : α + β ≠ 0 := by
    intro e; apply h.hAB
    rw [← hα, ← hβ, show β = -α by linear_combination e]; ring
  have hab2 : α - β ≠ 0 := by
    intro e; apply h.hAB
    rw [← hα, ← hβ, show β = α by linear_combination -e]
  have h2α : 2 * α ≠ 0 := mul_ne_zero h2 hα0
  have fA : x ^ 2 - C A * y ^ 2 = (x - C α * y) * (x + C α * y) := by
    rw [← hα, C_pow]; ring
  have fB : x ^ 2 - C B * y ^ 2 = (x - C β * y) * (x + C β * y) := by
    rw [← hβ, C_pow]; ring
  have cA := isCoprime_sub_add_C h2 hα0 h.cop
  have cB := isCoprime_sub_add_C h2 hβ0 h.cop
  obtain ⟨p, hp⟩ := isSquare_of_isCoprime cA (fA ▸ h.sqA)
  obtain ⟨q, hq⟩ := isSquare_of_isCoprime cA.symm (by rw [mul_comm, ← fA]; exact h.sqA)
  have s1 := isSquare_of_isCoprime cB (fB ▸ h.sqB)
  have s2 := isSquare_of_isCoprime cB.symm (by rw [mul_comm, ← fB]; exact h.sqB)
  have hpq : IsCoprime p q := by
    rw [hp, hq] at cA
    exact cA.of_mul_left_left.of_mul_right_left
  set A' : K := -(α - β) / (α + β) with hA'
  set B' : K := -(α + β) / (α - β) with hB'
  have hk1 : (C α + C β) * C A' = -(C α - C β) := by
    rw [← C_add, ← C_mul, hA', mul_div_cancel₀ _ hab1, C_neg, C_sub]
  have hk2 : (C α - C β) * C B' = -(C α + C β) := by
    rw [← C_sub, ← C_mul, hB', mul_div_cancel₀ _ hab2, C_neg, C_add]
  have h2C : C (2 * α) = 2 * C α := by rw [C_mul, map_ofNat]
  have key1 : C (α + β) * (p ^ 2 - C A' * q ^ 2) = C (2 * α) * (x - C β * y) := by
    rw [h2C, C_add]
    linear_combination (-(C α + C β)) * hp - (C α - C β) * hq - q ^ 2 * hk1
  have key2 : C (α - β) * (p ^ 2 - C B' * q ^ 2) = C (2 * α) * (x + C β * y) := by
    rw [h2C, C_sub]
    linear_combination (-(C α - C β)) * hp - (C α + C β) * hq - q ^ 2 * hk2
  have sqA' : IsSquare (p ^ 2 - C A' * q ^ 2) := by
    rw [← isSquare_C_mul_iff hab1, key1, isSquare_C_mul_iff h2α]; exact s1
  have sqB' : IsSquare (p ^ 2 - C B' * q ^ 2) := by
    rw [← isSquare_C_mul_iff hab2, key2, isSquare_C_mul_iff h2α]; exact s2
  have hA'0 : A' ≠ 0 := div_ne_zero (neg_ne_zero.mpr hab2) hab1
  have hB'0 : B' ≠ 0 := div_ne_zero (neg_ne_zero.mpr hab1) hab2
  have hA'B' : A' ≠ B' := by
    intro e
    rw [hA', hB', div_eq_div_iff hab1 hab2] at e
    have : (2 * 2) * (α * β) = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h4 | h4
    · exact mul_ne_zero h2 h2 h4
    · exact mul_ne_zero hα0 hβ0 h4
  have hdeg : ∀ γ : K, (x + C γ * y).natDegree ≤ max x.natDegree y.natDegree :=
    fun γ => (natDegree_add_le _ _).trans (max_le_max le_rfl (natDegree_C_mul_le _ _))
  have hdeg' : (x - C α * y).natDegree ≤ max x.natDegree y.natDegree := by
    rw [sub_eq_add_neg, ← neg_mul, ← C_neg]; exact hdeg _
  refine ⟨A', B', p, q, ⟨hA'0, hB'0, hA'B', hpq, sqA', sqB'⟩, ?_, ?_, ?_⟩
  · rw [← natDegree_pow, sq, ← hp]; exact hdeg'
  · rw [← natDegree_pow, sq, ← hq]; exact hdeg _
  · intro hp0 hq0
    have ex : x = C (2⁻¹ : K) * (p ^ 2 + q ^ 2) := by
      linear_combination (-x) * C_inv_two_mul h2 + C (2⁻¹ : K) * hp + C (2⁻¹ : K) * hq
    have ey : y = C ((2 * α)⁻¹) * (q ^ 2 - p ^ 2) := by
      have e2 : C ((2 * α)⁻¹) * (2 * C α) = 1 := by
        rw [← h2C, ← C_mul, inv_mul_cancel₀ h2α, C_1]
      linear_combination (-y) * e2 - C ((2 * α)⁻¹) * hp + C ((2 * α)⁻¹) * hq
    have hpq0 : ∀ r : K[X], r.natDegree = 0 → (r ^ 2).natDegree = 0 := fun r hr => by
      rw [natDegree_pow, hr]
    constructor
    · rw [ex]
      refine Nat.eq_zero_of_le_zero ((natDegree_C_mul_le _ _).trans ?_)
      exact (natDegree_add_le _ _).trans (by rw [hpq0 p hp0, hpq0 q hq0]; rfl)
    · rw [ey]
      refine Nat.eq_zero_of_le_zero ((natDegree_C_mul_le _ _).trans ?_)
      exact (natDegree_sub_le _ _).trans (by rw [hpq0 p hp0, hpq0 q hq0]; rfl)

/-- **Claim (over `K` algebraically closed, `2 ≠ 0`).** In the shape `IsTwoSquares`, `x` and `y`
are constants. Strong induction on `max (deg x) (deg y)`, which at least halves at each step. -/
theorem IsTwoSquares.natDegree_eq_zero (h2 : (2 : K) ≠ 0) {A B : K} {x y : K[X]}
    (h : IsTwoSquares A B x y) : x.natDegree = 0 ∧ y.natDegree = 0 := by
  suffices H : ∀ n : ℕ, ∀ (A B : K) (x y : K[X]), IsTwoSquares A B x y →
      max x.natDegree y.natDegree ≤ n → x.natDegree = 0 ∧ y.natDegree = 0 from
    H _ A B x y h le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A B x y h hn
    obtain ⟨A', B', p, q, h', hp, hq, hfin⟩ := h.descent h2
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨by omega, by omega⟩
    · have hm : max p.natDegree q.natDegree < n := by omega
      obtain ⟨hp0, hq0⟩ := ih _ hm A' B' p q h' le_rfl
      exact hfin hp0 hq0

end AlgClosed

/-- If `g² w` is a square and `g ≠ 0`, then `w` is a square (`K[X]` is integrally closed). -/
theorem isSquare_of_sq_mul {g w : K[X]} (hg : g ≠ 0) (h : IsSquare (g ^ 2 * w)) : IsSquare w := by
  obtain ⟨m, hm⟩ := h
  have hd : g ^ 2 ∣ m ^ 2 := ⟨w, by rw [sq m, ← hm]⟩
  obtain ⟨m₁, rfl⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp hd
  refine ⟨m₁, ?_⟩
  have : g ^ 2 * (w - m₁ * m₁) = 0 := by linear_combination hm
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h0) hg
  · exact sub_eq_zero.mp h0

/-- **Theorem T2.** Let `K` be a field with `2 ≠ 0`, `A ≠ B` nonzero constants, and `u, v ∈ K[X]`
with `v ≠ 0`. If `u² + A v²` and `u² + B v²` are both squares in `K[X]`, then `u = λ v` for a
constant `λ ∈ K`: the constant genus-one curve `y² = (x² + A)(x² + B)` has no nonconstant
`K(X)`-points. Proof: divide by `gcd(u, v)`, pass to `AlgebraicClosure K` and apply
`IsTwoSquares.natDegree_eq_zero` with `(−A, −B)`. -/
theorem two_forms_proportional (h2 : (2 : K) ≠ 0) {A B : K} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : A ≠ B) {u v : K[X]} (hv : v ≠ 0) (h₁ : IsSquare (u ^ 2 + C A * v ^ 2))
    (h₂ : IsSquare (u ^ 2 + C B * v ^ 2)) : ∃ lam : K, u = C lam * v := by
  classical
  obtain ⟨g, hg⟩ : ∃ g, g = gcd u v := ⟨_, rfl⟩
  have hg0 : g ≠ 0 := fun h0 => hv ((gcd_eq_zero_iff u v).mp (hg ▸ h0)).2
  obtain ⟨u₁, hu₁⟩ : g ∣ u := hg ▸ gcd_dvd_left u v
  obtain ⟨v₁, hv₁⟩ : g ∣ v := hg ▸ gcd_dvd_right u v
  have hcop : IsCoprime u₁ v₁ := by
    have := isCoprime_div_gcd_div_gcd (p := u) hv
    rw [← hg] at this
    have e1 : u / g = u₁ := by rw [hu₁, mul_div_cancel_left₀ _ hg0]
    have e2 : v / g = v₁ := by rw [hv₁, mul_div_cancel_left₀ _ hg0]
    rwa [e1, e2] at this
  clear hg
  have hsq : ∀ D : K, IsSquare (u ^ 2 + C D * v ^ 2) → IsSquare (u₁ ^ 2 + C D * v₁ ^ 2) := by
    intro D hD
    refine isSquare_of_sq_mul hg0 ?_
    convert hD using 1
    rw [hu₁, hv₁]; ring
  let L := AlgebraicClosure K
  let φ : K[X] →+* L[X] := mapRingHom (algebraMap K L)
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hT : IsTwoSquares (algebraMap K L (-A)) (algebraMap K L (-B)) (φ u₁) (φ v₁) := by
    refine ⟨?_, ?_, ?_, hcop.map φ, ?_, ?_⟩
    · exact (map_ne_zero_iff _ hinj).mpr (neg_ne_zero.mpr hA)
    · exact (map_ne_zero_iff _ hinj).mpr (neg_ne_zero.mpr hB)
    · exact fun e => hAB (neg_inj.mp (hinj e))
    · convert (hsq A h₁).map φ using 1
      rw [map_add, map_mul, map_pow, map_pow]
      simp only [φ, coe_mapRingHom, Polynomial.map_C, map_neg]
      ring
    · convert (hsq B h₂).map φ using 1
      rw [map_add, map_mul, map_pow, map_pow]
      simp only [φ, coe_mapRingHom, Polynomial.map_C, map_neg]
      ring
  have h2L : (2 : L) ≠ 0 := by
    rw [show (2 : L) = algebraMap K L 2 from (map_ofNat _ 2).symm]
    exact (map_ne_zero_iff _ hinj).mpr h2
  obtain ⟨d₁, d₂⟩ := hT.natDegree_eq_zero h2L
  simp only [φ, coe_mapRingHom, natDegree_map] at d₁ d₂
  rw [natDegree_eq_zero] at d₁ d₂
  obtain ⟨c₁, rfl⟩ := d₁
  obtain ⟨c₂, rfl⟩ := d₂
  have hc₂ : c₂ ≠ 0 := by rintro rfl; simp [hv₁] at hv
  refine ⟨c₁ / c₂, ?_⟩
  rw [hu₁, hv₁, show C c₁ = C (c₁ / c₂) * C c₂ by rw [← C_mul, div_mul_cancel₀ _ hc₂]]
  ring

/-- Three forms version: if `c² + a²`, `c² + β² a²`, `c² + (1 + β²) a²` are squares, `a ≠ 0`,
`β ≠ 0`, then `c = λ a`. (Use `(1, β²)` unless `1 + β² = 0`... more precisely: use `(1, 1 + β²)`
unless `1 + β² = 0`, in which case `β² = −1 ≠ 1` and `(1, β²)` works.) -/
theorem proportional_of_three_forms (h2 : (2 : K) ≠ 0) {a c : K[X]} {β : K} (ha : a ≠ 0)
    (hβ : β ≠ 0) (s1 : IsSquare (c ^ 2 + C 1 * a ^ 2)) (s2 : IsSquare (c ^ 2 + C (β ^ 2) * a ^ 2))
    (s3 : IsSquare (c ^ 2 + C (1 + β ^ 2) * a ^ 2)) : ∃ lam : K, c = C lam * a := by
  have hβ2 : β ^ 2 ≠ 0 := pow_ne_zero 2 hβ
  by_cases h1 : 1 + β ^ 2 = 0
  · refine two_forms_proportional h2 one_ne_zero hβ2 ?_ ha s1 s2
    intro e
    apply h2
    linear_combination h1 + e
  · refine two_forms_proportional h2 one_ne_zero h1 ?_ ha s1 s3
    intro e
    exact hβ2 (by linear_combination -e)

/-- **Two proportional edges ⇒ proportional cuboid** (any field with `2 ≠ 0`). If
`(a, β a, c)` is a cuboid over `K[X]`, then `c = λ a`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_edge_mul (h2 : (2 : K) ≠ 0)
    {a c : K[X]} {β : K} (h : PolyCharP.IsCuboid a (C β * a) c) :
    PolyCharP.Proportional a (C β * a) c := by
  have ha := h.ne_a
  have hβ : β ≠ 0 := by rintro rfl; exact h.ne_b (by simp)
  obtain ⟨lam, hlam⟩ := proportional_of_three_forms (c := c) h2 ha hβ
    (by convert h.sq_ac using 1; rw [C_1]; ring)
    (by convert h.sq_bc using 1; rw [C_pow]; ring)
    (by convert h.sq_abc using 1; rw [C_add, C_1, C_pow]; ring)
  exact ⟨a, 1, β, lam, by rw [C_1, one_mul], rfl, hlam⟩

theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.swap_bc {a b c : K[X]}
    (h : PolyCharP.IsCuboid a b c) : PolyCharP.IsCuboid a c b :=
  ⟨h.ne_a, h.ne_c, h.ne_b, h.sq_ac, h.sq_ab, by rw [add_comm]; exact h.sq_bc,
    by rw [add_right_comm]; exact h.sq_abc⟩

theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.swap_ab {a b c : K[X]}
    (h : PolyCharP.IsCuboid a b c) : PolyCharP.IsCuboid b a c :=
  ⟨h.ne_b, h.ne_a, h.ne_c, by rw [add_comm]; exact h.sq_ab, h.sq_bc, h.sq_ac,
    by rw [add_comm (b ^ 2)]; exact h.sq_abc⟩

/-- **Any two proportional edges ⇒ proportional.** -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_two_edges (h2 : (2 : K) ≠ 0)
    {a b c : K[X]} (h : PolyCharP.IsCuboid a b c)
    (hpair : (∃ β : K, b = C β * a) ∨ (∃ γ : K, c = C γ * a) ∨ (∃ γ : K, c = C γ * b)) :
    PolyCharP.Proportional a b c := by
  rcases hpair with ⟨β, rfl⟩ | ⟨γ, rfl⟩ | ⟨γ, rfl⟩
  · exact h.proportional_of_edge_mul h2
  · obtain ⟨q, x, y, z, h1, h2', h3⟩ := h.swap_bc.proportional_of_edge_mul h2
    exact ⟨q, x, z, y, h1, h3, h2'⟩
  · obtain ⟨q, x, y, z, h1, h2', h3⟩ := h.swap_ab.swap_bc.proportional_of_edge_mul h2
    exact ⟨q, z, x, y, h3, h1, h2'⟩

/-! ### Stretch S1: two proportional lengths -/

/-- If `b² = κ a²` with `a ≠ 0`, then `b = μ a` for a constant `μ`. -/
theorem exists_C_mul_of_sq_eq {a b : K[X]} (ha : a ≠ 0) {κ : K} (h : b ^ 2 = C κ * a ^ 2) :
    ∃ μ : K, b = C μ * a := by
  obtain ⟨t, rfl⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp
    (⟨C κ, by rw [h, mul_comm]⟩ : a ^ 2 ∣ b ^ 2)
  have ht : a ^ 2 * (t ^ 2 - C κ) = 0 := by linear_combination h
  have ht' : t ^ 2 = C κ := by
    rcases mul_eq_zero.mp ht with h0 | h0
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h0) ha
    · exact sub_eq_zero.mp h0
  have : t.natDegree = 0 := by
    have := congrArg natDegree ht'
    rw [natDegree_pow, natDegree_C] at this
    omega
  rw [natDegree_eq_zero] at this
  obtain ⟨μ, rfl⟩ := this
  exact ⟨μ, mul_comm _ _⟩

/-- Dividing by the square of a nonzero constant preserves squares (any field). -/
theorem isSquare_of_C_sq_mul {μ : K} (hμ : μ ≠ 0) {f : K[X]} (h : IsSquare (C (μ ^ 2) * f)) :
    IsSquare f := by
  obtain ⟨m, hm⟩ := h
  refine ⟨C μ⁻¹ * m, ?_⟩
  have e : C μ⁻¹ * C μ = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hμ, C_1]
  rw [C_pow] at hm
  linear_combination (C μ⁻¹) ^ 2 * hm - f * (C μ⁻¹ * C μ + 1) * e


/-- **Edge ∝ its own face diagonal** (`d = λ a`) ⇒ proportional. No degeneracy hypothesis. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_diag_eq_edge (h2 : (2 : K) ≠ 0)
    {a b c : K[X]} (h : PolyCharP.IsCuboid a b c) {lam : K}
    (hd : a ^ 2 + b ^ 2 = (C lam * a) ^ 2) : PolyCharP.Proportional a b c := by
  obtain ⟨μ, hμ⟩ := exists_C_mul_of_sq_eq (b := b) h.ne_a (κ := lam ^ 2 - 1)
    (by rw [C_sub, C_pow, C_1]; linear_combination hd)
  exact h.proportional_of_two_edges h2 (Or.inl ⟨μ, hμ⟩)

/-- **Edge ∝ the opposite face diagonal** (`f = λ a`, i.e. `b² + c² = λ² a²`) ⇒ proportional,
for nondegenerate cuboids. The forms `c² + b² = (λ a)²` and `c² + (1 + λ²) b² = λ² (a² + b²)`
are squares; `1 + λ² ≠ 0` because `a² + b² + c² = (1 + λ²) a² ≠ 0`, and `λ ≠ 0` because
`b² + c² ≠ 0`. (Both exceptions are genuine: `(2X, X² − 1, i(X² + 1))` has `f = i a`.) -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_opp_diag_eq_edge
    (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : PolyCharP.IsNondegCuboid a b c) {lam : K}
    (hf : b ^ 2 + c ^ 2 = (C lam * a) ^ 2) : PolyCharP.Proportional a b c := by
  have hlam : lam ≠ 0 := by rintro rfl; apply h.ne_bc; rw [hf]; simp
  have hκ : 1 + lam ^ 2 ≠ 0 := by
    intro e; apply h.ne_abc
    have : C (1 + lam ^ 2) = 0 := by rw [e, C_0]
    rw [C_add, C_1, C_pow] at this
    linear_combination hf + a ^ 2 * this
  have hκ1 : (1 : K) ≠ 1 + lam ^ 2 := by
    intro e; exact pow_ne_zero 2 hlam (by linear_combination -e)
  obtain ⟨m, hm⟩ := h.sq_ab
  have s1 : IsSquare (c ^ 2 + C 1 * b ^ 2) := ⟨C lam * a, by rw [C_1]; linear_combination hf⟩
  have s2 : IsSquare (c ^ 2 + C (1 + lam ^ 2) * b ^ 2) :=
    ⟨C lam * m, by rw [C_add, C_1, C_pow]; linear_combination hf + C lam ^ 2 * hm⟩
  obtain ⟨ρ, hρ⟩ := two_forms_proportional h2 one_ne_zero hκ hκ1 h.ne_b s1 s2
  exact h.toIsCuboid.proportional_of_two_edges h2 (Or.inr (Or.inr ⟨ρ, hρ⟩))

/-- **Edge ∝ space diagonal** (`g = λ a`) ⇒ proportional, for nondegenerate cuboids: then
`f² = b² + c² = (λ² − 1) a²`, so `f = ν a` and the previous theorem applies. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_space_diag_eq_edge
    (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : PolyCharP.IsNondegCuboid a b c) {lam : K}
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = (C lam * a) ^ 2) : PolyCharP.Proportional a b c := by
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨ν, hν⟩ := exists_C_mul_of_sq_eq (b := f) h.ne_a (κ := lam ^ 2 - 1)
    (by rw [C_sub, C_pow, C_1]; linear_combination -hf + hg)
  exact h.proportional_of_opp_diag_eq_edge h2 (lam := ν) (by rw [hf, hν]; ring)

/-- **Two face diagonals proportional** (`e = λ d`) ⇒ proportional. Here `c² = λ² d² − a²`;
if `λ² = 1` then `c² = b²`, else `b² + a² = d²` and `b² + ((λ² − 1)/λ²) a² = c²/λ²` are
squares. Needs `λ ≠ 0`, i.e. `a² + c² ≠ 0`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_diag_eq_diag
    (h2 : (2 : K) ≠ 0) {a b c d : K[X]} (h : PolyCharP.IsNondegCuboid a b c) {lam : K}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = (C lam * d) ^ 2) :
    PolyCharP.Proportional a b c := by
  have hlam : lam ≠ 0 := by rintro rfl; apply h.ne_ac; rw [he]; simp
  have hl2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
  by_cases h1 : lam ^ 2 = 1
  · obtain ⟨μ, hμ⟩ := exists_C_mul_of_sq_eq (b := c) h.ne_b (κ := 1) (by
      have : C (lam ^ 2) = 1 := by rw [h1, C_1]
      rw [C_pow] at this
      rw [C_1]; linear_combination he - hd + d ^ 2 * this)
    exact h.toIsCuboid.proportional_of_two_edges h2 (Or.inr (Or.inr ⟨μ, hμ⟩))
  · set κ : K := (lam ^ 2 - 1) / lam ^ 2 with hκdef
    have hk : C (lam ^ 2) * C κ = C (lam ^ 2) - 1 := by
      rw [← C_mul, hκdef, mul_div_cancel₀ _ hl2, C_sub, C_1]
    have hκ0 : κ ≠ 0 := div_ne_zero (sub_ne_zero.mpr h1) hl2
    have hκ1 : (1 : K) ≠ κ := by
      intro e
      rw [hκdef, eq_div_iff hl2] at e
      exact one_ne_zero (by linear_combination e)
    have s1 : IsSquare (b ^ 2 + C 1 * a ^ 2) := ⟨d, by rw [C_1]; linear_combination hd⟩
    have s2 : IsSquare (b ^ 2 + C κ * a ^ 2) := by
      refine isSquare_of_C_sq_mul hlam ⟨c, ?_⟩
      rw [C_pow] at hk ⊢
      linear_combination a ^ 2 * hk - he + C lam ^ 2 * hd
    obtain ⟨ρ, hρ⟩ := two_forms_proportional h2 one_ne_zero hκ0 hκ1 h.ne_a s1 s2
    exact h.toIsCuboid.proportional_of_two_edges h2 (Or.inl ⟨ρ, hρ⟩)

/-- **Face diagonal ∝ space diagonal** (`g = λ d`) ⇒ proportional, for nondegenerate cuboids:
`c² = (λ² − 1) d²` gives `c = μ d`, and then `b² + a² = d²`, `b² + ((1 + μ²)/μ²) a² = (a² + c²)/μ²`
are squares (`1 + μ² ≠ 0` since `a² + b² + c² = (1 + μ²) d² ≠ 0`). -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_space_diag_eq_diag
    (h2 : (2 : K) ≠ 0) {a b c d : K[X]} (h : PolyCharP.IsNondegCuboid a b c) {lam : K}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = (C lam * d) ^ 2) :
    PolyCharP.Proportional a b c := by
  have hd0 : d ≠ 0 := by rintro rfl; apply h.ne_ab; rw [hd]; ring
  obtain ⟨μ, hμ⟩ := exists_C_mul_of_sq_eq (b := c) hd0 (κ := lam ^ 2 - 1)
    (by rw [C_sub, C_pow, C_1]; linear_combination hg - hd)
  have hμ0 : μ ≠ 0 := by rintro rfl; apply h.ne_c; rw [hμ]; simp
  have hμ2 : μ ^ 2 ≠ 0 := pow_ne_zero 2 hμ0
  have h1 : 1 + μ ^ 2 ≠ 0 := by
    intro e; apply h.ne_abc
    have : C (1 + μ ^ 2) = 0 := by rw [e, C_0]
    rw [C_add, C_1, C_pow] at this
    rw [hμ]; linear_combination hd + d ^ 2 * this
  set κ : K := (1 + μ ^ 2) / μ ^ 2 with hκdef
  have hk : C (μ ^ 2) * C κ = 1 + C (μ ^ 2) := by
    rw [← C_mul, hκdef, mul_div_cancel₀ _ hμ2, C_add, C_1]
  have hκ0 : κ ≠ 0 := div_ne_zero h1 hμ2
  have hκ1 : (1 : K) ≠ κ := by
    intro e
    rw [hκdef, eq_div_iff hμ2] at e
    exact one_ne_zero (by linear_combination -e)
  have s1 : IsSquare (b ^ 2 + C 1 * a ^ 2) := ⟨d, by rw [C_1]; linear_combination hd⟩
  obtain ⟨e, he⟩ := h.sq_ac
  have s2 : IsSquare (b ^ 2 + C κ * a ^ 2) := by
    refine isSquare_of_C_sq_mul hμ0 ⟨e, ?_⟩
    rw [C_pow] at hk ⊢
    rw [hμ] at he
    linear_combination a ^ 2 * hk + he + C μ ^ 2 * hd
  obtain ⟨ρ, hρ⟩ := two_forms_proportional h2 one_ne_zero hκ0 hκ1 h.ne_a s1 s2
  exact h.toIsCuboid.proportional_of_two_edges h2 (Or.inl ⟨ρ, hρ⟩)

/-! ### Stretch S2: constant congruent numbers over `K[X]` -/

/-- **No nonconstant polynomial right triangle has constant "congruent number".** If
`x² + y² = z²` and `x y = 2N s²` with `N ∈ K*`, `s ≠ 0`, then `x, y` are constant multiples of
`s`. Proof: `(x ± y)² = z² ± 4N s²`, so T2 with `(4N, −4N)` gives `z = λ s`, and then
`(x ± y)² = (λ² ± 4N) s²` forces `x ± y ∈ K · s`. -/
theorem not_congruent_const (h2 : (2 : K) ≠ 0) {x y z s : K[X]} {N : K} (hN : N ≠ 0)
    (hs : s ≠ 0) (hpy : x ^ 2 + y ^ 2 = z ^ 2) (hxy : x * y = C (2 * N) * s ^ 2) :
    ∃ α β : K, x = C α * s ∧ y = C β * s := by
  have h4 : C (4 * N) = 2 * C (2 * N) := by
    rw [C_mul, C_mul, show (4 : K) = 2 * 2 by norm_num, C_mul, map_ofNat]; ring
  have hA : 4 * N ≠ 0 :=
    mul_ne_zero (by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2) hN
  have s1 : IsSquare (z ^ 2 + C (4 * N) * s ^ 2) :=
    ⟨x + y, by rw [h4]; linear_combination -hpy - 2 * hxy⟩
  have s2 : IsSquare (z ^ 2 + C (-(4 * N)) * s ^ 2) :=
    ⟨x - y, by rw [C_neg, h4]; linear_combination -hpy + 2 * hxy⟩
  have hAB : 4 * N ≠ -(4 * N) := by
    intro e
    have : (2 : K) * (4 * N) = 0 := by linear_combination e
    exact hA ((mul_eq_zero.mp this).resolve_left h2)
  obtain ⟨lam, rfl⟩ := two_forms_proportional h2 hA (neg_ne_zero.mpr hA) hAB hs s1 s2
  obtain ⟨μ, hμ⟩ := exists_C_mul_of_sq_eq (b := x + y) hs (κ := lam ^ 2 + 4 * N) (by
    rw [C_add, C_pow, h4]; linear_combination hpy + 2 * hxy)
  obtain ⟨μ', hμ'⟩ := exists_C_mul_of_sq_eq (b := x - y) hs (κ := lam ^ 2 - 4 * N) (by
    rw [C_sub, C_pow, h4]; linear_combination hpy - 2 * hxy)
  have e1 := C_inv_two_mul h2
  refine ⟨2⁻¹ * (μ + μ'), 2⁻¹ * (μ - μ'), ?_, ?_⟩
  · rw [C_mul, C_add]
    linear_combination C (2⁻¹ : K) * hμ + C (2⁻¹ : K) * hμ' - x * e1
  · rw [C_mul, C_sub]
    linear_combination C (2⁻¹ : K) * hμ - C (2⁻¹ : K) * hμ' - y * e1

/-- **Cuboid corollary of S2.** In a nondegenerate cuboid, if `a · f` (edge times opposite face
diagonal, the legs of the right triangle `a² + f² = g²`) is a nonzero constant times a square,
then the cuboid is proportional. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_mul_opp_diag
    (h2 : (2 : K) ≠ 0) {a b c f s : K[X]} (h : PolyCharP.IsNondegCuboid a b c) {κ : K}
    (hκ : κ ≠ 0) (hf : b ^ 2 + c ^ 2 = f ^ 2) (haf : a * f = C κ * s ^ 2) :
    PolyCharP.Proportional a b c := by
  have hf0 : f ≠ 0 := by rintro rfl; apply h.ne_bc; rw [hf]; ring
  have hs : s ≠ 0 := by
    rintro rfl; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, mul_eq_zero] at haf
    exact haf.elim h.ne_a hf0
  obtain ⟨g, hg⟩ := h.sq_abc
  obtain ⟨α, β, hα, hβ⟩ := not_congruent_const h2 (x := a) (y := f) (N := κ / 2) (z := g)
    (div_ne_zero hκ h2) hs (by linear_combination -hf + hg)
    (by rw [mul_div_cancel₀ _ h2]; exact haf)
  have hα0 : α ≠ 0 := by rintro rfl; apply h.ne_a; rw [hα]; simp
  refine h.proportional_of_opp_diag_eq_edge h2 (lam := β / α) ?_
  rw [hf, hβ, hα, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hα0]

end PerfectCuboid.PolyGenusOne
