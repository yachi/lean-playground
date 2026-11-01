module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolyCharP

/-!
# Pythagorean triples over `K[X]` and pairwise coprime polynomial cuboids

Round 17, brief 4. `K` is any field; the ℚ-only results of `PolynomialCuboid.lean` and
`PolyBrick.lean` are generalised.

* **Squares in a PID** (`exists_sq_of_coprime_mul_eq`): coprime factors of `c · r²` are
  `unit · square`.
* **Pythagorean parametrisation** (`pythagorean_param`, `2 ≠ 0`): coprime `x, y` with
  `x² + y² = z²` give coprime `m, n` and constants `u, v, ν` with `ν² = uv`, `z - y = u m²`,
  `z + y = v n²`, `x = ν m n`, `2y = v n² - u m²`, `2z = v n² + u m²`; degrees
  (`natDegree_param`): `deg x = deg m + deg n`, `max(deg y, deg z) = 2 max(deg m, deg n)`.
  Coprimality transfer: `isCoprime_iff_of_hyp` (`gcd(x, y) = 1 ↔ gcd(y, z) = 1`),
  `isCoprime_sub_add_iff`, `isCoprime_sub_add`.
* **Common-leg structure** (`IsCuboid.common_leg`): for pairwise coprime edges, each edge is
  coprime to the two face diagonals through it, the three face factorisations are coprime, and
  `gcd(g - f, g + f) = 1 ↔ gcd(a, f) = 1 ↔ gcd(a, g) = 1` (and cyclically) — the opposite
  coprimality is *not* automatic (`isNondegCuboid_coprime_five` has `gcd(a, f) = X² - 1`).
* **Mason–Stothers, characteristic `0`** (`two_mul_natDegree_add_one_le`,
  `natDegree_hyp_add_one_le_radical`, `natDegree_pos_of_leg`), and for cuboids with pairwise
  coprime edges (`IsCuboid.radical_bound`): all edges and face diagonals are non-constant once one
  edge is, `deg d + deg e + deg f + 3 ≤ 2 (deg rad a + deg rad b + deg rad c)` (the
  `IsPolyBrick.radical_sum_bound` of `PolyBrick.lean`, over any `K` of characteristic `0`), the
  three face inequalities `2 max(deg a, deg b, deg d) + 1 ≤ deg rad a + deg rad b + deg rad d`,
  and, if `gcd(a, f) = 1`, the space-diagonal inequality (`IsCuboid.radical_bound_space`).
* **Space swap** (`isNondegCuboid_space_swap`): with `i² = -1`, `(a, b, c)` ↦ `(g, ib, ic)`
  preserves (nondegenerate) cuboids — the cuboid surface is symmetric in `(a, b, c, ig)`.
* **A pairwise coprime nondegenerate non-proportional cuboid over `𝔽₅[X]`**
  (`isNondegCuboid_coprime_five`, `isCoprime_coprime_five`, `not_proportional_coprime_five`):
  `(X⁶ - 1, X + X⁵, 2(X⁶ + 1))`, the space swap of the Frobenius cuboid. Exhaustive search
  (round 17, `code/b4/`) shows that up to scaling, signs, permutations, `PGL₂(𝔽₅)` and common
  factors these two are the only nondegenerate cuboids over `𝔽₅[X]` with edge degree `≤ 8`, and
  there is none over `𝔽₁₃[X]` with edge degree `≤ 5`.
* **Euler coordinates** (`four_number`, `exists_euler_param`, `euler_param_identities`,
  `IsCuboid.exists_euler`): `a² + b² + c² = g²` iff `2a = PR + QS`, `2ib = PR - QS`,
  `2c = QR - PS`, `2g = PS + QR`; then `a² + b² = PQRS`, `4(a² + c²) = (P² + Q²)(R² + S²)`,
  `4(b² + c²) = (Q² - P²)(R² - S²)`. So a cuboid over `K[X]` is a pair `t = P/Q`, `s = R/S`
  with `ts`, `(t² + 1)(s² + 1)`, `(t² - 1)(s² - 1)` squares.
-/

@[expose] public section

open Polynomial

namespace PerfectCuboid.PolyPythagoras

variable {K : Type*} [Field K]

/-- `C 2⁻¹ * 2 = 1` in `K[X]` when `2 ≠ 0` in `K`. -/
theorem C_inv_two_mul_two (h2 : (2 : K) ≠ 0) : (C (2⁻¹ : K) : K[X]) * 2 = 1 := by
  rw [show (2 : K[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul, inv_mul_cancel₀ h2, C_1]

/-- **Coprime factors of a unit times a square are units times squares** (`K[X]` is a PID). -/
theorem exists_sq_of_coprime_mul_eq {p q r : K[X]} {c : K} (hc : c ≠ 0) (hpq : IsCoprime p q)
    (h : p * q = C c * r ^ 2) : ∃ (u : K) (m : K[X]), u ≠ 0 ∧ p = C u * m ^ 2 := by
  have hu : IsUnit (C c⁻¹ : K[X]) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hc))
  have hpq' : IsCoprime p (C c⁻¹ * q) := (isCoprime_mul_unit_left_right hu p q).mpr hpq
  have hprod : p * (C c⁻¹ * q) = r ^ 2 := by
    rw [mul_left_comm, h, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
  obtain ⟨m, μ, hμ⟩ := exists_associated_pow_of_mul_eq_pow' hpq' hprod
  obtain ⟨u, hu, hCu⟩ := Polynomial.isUnit_iff.mp μ.isUnit
  exact ⟨u, m, hu.ne_zero, by rw [← hμ, ← hCu, mul_comm]⟩

/-- In a Pythagorean triple, `gcd(x, y) = 1 ↔ gcd(y, z) = 1`. -/
theorem isCoprime_iff_of_hyp {x y z : K[X]} (h : x ^ 2 + y ^ 2 = z ^ 2) :
    IsCoprime x y ↔ IsCoprime y z := by
  constructor
  · intro hxy
    have h1 : IsCoprime y (x ^ 2) := hxy.symm.pow_right
    have h2 : IsCoprime y (z ^ 2) := by
      have := h1.add_mul_left_right y
      rwa [show x ^ 2 + y * y = z ^ 2 by linear_combination h] at this
    exact (IsCoprime.pow_right_iff two_pos).mp h2
  · intro hyz
    have h1 : IsCoprime y (z ^ 2) := hyz.pow_right
    have h2 : IsCoprime y (x ^ 2) := by
      have := h1.add_mul_left_right (-y)
      rwa [show z ^ 2 + y * -y = x ^ 2 by linear_combination -h] at this
    exact ((IsCoprime.pow_right_iff two_pos).mp h2).symm

/-- In a Pythagorean triple with coprime legs, each leg is coprime to the hypotenuse. -/
theorem isCoprime_hyp {x y z : K[X]} (hxy : IsCoprime x y) (h : x ^ 2 + y ^ 2 = z ^ 2) :
    IsCoprime x z ∧ IsCoprime y z :=
  ⟨(isCoprime_iff_of_hyp (by linear_combination h)).mp hxy.symm,
    (isCoprime_iff_of_hyp h).mp hxy⟩

/-- `gcd(z - y, z + y) = 1 ↔ gcd(y, z) = 1` when `2` is invertible. -/
theorem isCoprime_sub_add_iff (h2 : (2 : K) ≠ 0) {y z : K[X]} :
    IsCoprime (z - y) (z + y) ↔ IsCoprime y z := by
  constructor
  · rintro ⟨u, v, huv⟩
    exact ⟨v - u, u + v, by linear_combination huv⟩
  · rintro ⟨u, v, huv⟩
    refine ⟨C 2⁻¹ * (v - u), C 2⁻¹ * (u + v), ?_⟩
    linear_combination (u * y + v * z) * C_inv_two_mul_two h2 + huv

/-- For a primitive Pythagorean triple over `K[X]` (`2 ≠ 0`), `z - y` and `z + y` are coprime. -/
theorem isCoprime_sub_add (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hxy : IsCoprime x y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : IsCoprime (z - y) (z + y) :=
  (isCoprime_sub_add_iff h2).mpr ((isCoprime_iff_of_hyp h).mp hxy)

/-- If `w ^ 2 = C r * s ^ 2` with `s ≠ 0`, then `r = ν²` and `w = C ν * s` for some `ν`. -/
theorem eq_C_mul_of_sq_eq {w s : K[X]} {r : K} (hs : s ≠ 0) (h : w ^ 2 = C r * s ^ 2) :
    ∃ ν : K, ν ^ 2 = r ∧ w = C ν * s := by
  have hl := congrArg leadingCoeff h
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow, leadingCoeff_pow] at hl
  have hls : s.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hs
  set ν₀ := w.leadingCoeff / s.leadingCoeff with hν₀
  have hr : ν₀ ^ 2 = r := by
    rw [hν₀, div_pow, hl]; field_simp
  have hw : (w - C ν₀ * s) * (w + C ν₀ * s) = 0 := by
    rw [← hr, C_pow] at h; linear_combination h
  rcases mul_eq_zero.mp hw with h0 | h0
  · exact ⟨ν₀, hr, by linear_combination h0⟩
  · exact ⟨-ν₀, by rw [neg_sq, hr], by rw [C_neg]; linear_combination h0⟩

/-- **Pythagorean parametrisation over `K[X]`**, any field with `2 ≠ 0`: for coprime `x, y`
with `x² + y² = z²` there are coprime `m, n` and constants `u, v, ν` with `ν² = uv`,
`z - y = u m²`, `z + y = v n²`, `x = ν m n`, `2y = v n² - u m²`, `2z = v n² + u m²`.
No hypothesis on `z` (the degenerate `z = 0` forces `x, y` constant). -/
theorem pythagorean_param (h2 : (2 : K) ≠ 0) {x y z : K[X]} (hx : x ≠ 0)
    (hxy : IsCoprime x y) (h : x ^ 2 + y ^ 2 = z ^ 2) :
    ∃ (m n : K[X]) (u v ν : K), u ≠ 0 ∧ v ≠ 0 ∧ ν ^ 2 = u * v ∧ IsCoprime m n ∧
      z - y = C u * m ^ 2 ∧ z + y = C v * n ^ 2 ∧ x = C ν * (m * n) ∧
      C 2 * y = C v * n ^ 2 - C u * m ^ 2 ∧ C 2 * z = C v * n ^ 2 + C u * m ^ 2 := by
  have hcop := isCoprime_sub_add h2 hxy h
  have hprod : (z - y) * (z + y) = C 1 * x ^ 2 := by rw [C_1]; linear_combination -h
  obtain ⟨u, m, hu, hm⟩ := exists_sq_of_coprime_mul_eq one_ne_zero hcop hprod
  obtain ⟨v, n, hv, hn⟩ := exists_sq_of_coprime_mul_eq one_ne_zero hcop.symm
    (by rw [mul_comm]; exact hprod)
  have hmn : IsCoprime m n := by
    rw [hm, hn] at hcop
    have h1 : IsCoprime (m * (C u * m)) (n * (C v * n)) := by
      convert hcop using 1 <;> ring
    exact h1.of_mul_left_left.of_mul_right_left
  have hx2 : x ^ 2 = C (u * v) * (m * n) ^ 2 := by
    rw [C_1, one_mul] at hprod; rw [← hprod, hm, hn, C_mul]; ring
  have hmn0 : m * n ≠ 0 := by
    rintro h0; rw [h0] at hx2; simp at hx2; exact hx hx2
  obtain ⟨ν, hν, hxν⟩ := eq_C_mul_of_sq_eq hmn0 hx2
  refine ⟨m, n, u, v, ν, hu, hv, hν, hmn, hm, hn, hxν, ?_, ?_⟩
  · rw [← hm, ← hn, show (C 2 : K[X]) = 2 from map_ofNat C 2]; ring
  · rw [← hm, ← hn, show (C 2 : K[X]) = 2 from map_ofNat C 2]; ring

/-- Degrees in the parametrisation: `deg x = deg m + deg n` and
`max (deg y) (deg z) = 2 max (deg m) (deg n)`. -/
theorem natDegree_param (h2 : (2 : K) ≠ 0) {x y z m n : K[X]} {u v ν : K} (hu : u ≠ 0)
    (hv : v ≠ 0) (hν : ν ≠ 0) (hzy : z - y = C u * m ^ 2) (hzy' : z + y = C v * n ^ 2)
    (hx : x = C ν * (m * n)) (hm : m ≠ 0) (hn : n ≠ 0) :
    x.natDegree = m.natDegree + n.natDegree ∧
      max y.natDegree z.natDegree = 2 * max m.natDegree n.natDegree := by
  refine ⟨by rw [hx, natDegree_C_mul hν, natDegree_mul hm hn], ?_⟩
  have e1 : (z - y).natDegree = 2 * m.natDegree := by
    rw [hzy, natDegree_C_mul hu, natDegree_pow]
  have e2 : (z + y).natDegree = 2 * n.natDegree := by
    rw [hzy', natDegree_C_mul hv, natDegree_pow]
  have h2' : (C (2⁻¹ : K)) ≠ 0 := by simpa using h2
  have hz : z = C 2⁻¹ * ((z + y) + (z - y)) := by
    linear_combination (-z) * C_inv_two_mul_two h2
  have hy : y = C 2⁻¹ * ((z + y) - (z - y)) := by
    linear_combination (-y) * C_inv_two_mul_two h2
  have le1 : z.natDegree ≤ max (2 * n.natDegree) (2 * m.natDegree) := by
    rw [hz, natDegree_C_mul (inv_ne_zero h2), ← e1, ← e2]; exact natDegree_add_le _ _
  have le2 : y.natDegree ≤ max (2 * n.natDegree) (2 * m.natDegree) := by
    rw [hy, natDegree_C_mul (inv_ne_zero h2), ← e1, ← e2]; exact natDegree_sub_le _ _
  have le3 : (z - y).natDegree ≤ max z.natDegree y.natDegree := natDegree_sub_le _ _
  have le4 : (z + y).natDegree ≤ max z.natDegree y.natDegree := natDegree_add_le _ _
  omega

/-! ### The common-leg structure of a cuboid with pairwise coprime edges -/

open PolyCharP

/-- **Common-leg structure.** For a cuboid with pairwise coprime edges (any field with
`2 ≠ 0`): each edge is coprime to the two face diagonals through it, the three face
factorisations `a² = (d - b)(d + b)`, `a² = (e - c)(e + c)`, `b² = (f - c)(f + c)` are coprime,
and the space-diagonal factorisations `a² = (g - f)(g + f)`, `b² = (g - e)(g + e)`,
`c² = (g - d)(g + d)` are coprime **iff** the edge is coprime to the opposite face diagonal
(which is *not* automatic: a prime dividing `a` and `f` divides `g` but neither `b` nor `c`);
moreover `gcd(a, f) = 1 ↔ gcd(a, g) = 1` etc. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.common_leg (h2 : (2 : K) ≠ 0) {a b c : K[X]}
    (_h : IsCuboid a b c) (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    {d e f g : K[X]} (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    (a ^ 2 = (d - b) * (d + b) ∧ a ^ 2 = (e - c) * (e + c) ∧ a ^ 2 = (g - f) * (g + f) ∧
      b ^ 2 = (f - c) * (f + c) ∧ b ^ 2 = (g - e) * (g + e) ∧ c ^ 2 = (g - d) * (g + d)) ∧
    IsCoprime (d - b) (d + b) ∧ IsCoprime (e - c) (e + c) ∧ IsCoprime (f - c) (f + c) ∧
    IsCoprime a d ∧ IsCoprime b d ∧ IsCoprime a e ∧ IsCoprime c e ∧ IsCoprime b f ∧
    IsCoprime c f ∧
    (IsCoprime (g - f) (g + f) ↔ IsCoprime a f) ∧ (IsCoprime (g - e) (g + e) ↔ IsCoprime b e) ∧
    (IsCoprime (g - d) (g + d) ↔ IsCoprime c d) ∧
    (IsCoprime a f ↔ IsCoprime a g) ∧ (IsCoprime b e ↔ IsCoprime b g) ∧
    (IsCoprime c d ↔ IsCoprime c g) := by
  have hg1 : a ^ 2 + f ^ 2 = g ^ 2 := by linear_combination hg - hf
  have hg2 : b ^ 2 + e ^ 2 = g ^ 2 := by linear_combination hg - he
  have hg3 : c ^ 2 + d ^ 2 = g ^ 2 := by linear_combination hg - hd
  obtain ⟨had, hbd⟩ := isCoprime_hyp hab hd
  obtain ⟨hae, hce⟩ := isCoprime_hyp hac he
  obtain ⟨hbf, hcf⟩ := isCoprime_hyp hbc hf
  refine ⟨⟨by linear_combination hd, by linear_combination he, by linear_combination hg1,
    by linear_combination hf, by linear_combination hg2, by linear_combination hg3⟩,
    isCoprime_sub_add h2 hab hd, isCoprime_sub_add h2 hac he, isCoprime_sub_add h2 hbc hf,
    had, hbd, hae, hce, hbf, hcf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [isCoprime_sub_add_iff h2, isCoprime_iff_of_hyp hg1]
  · rw [isCoprime_sub_add_iff h2, isCoprime_iff_of_hyp hg2]
  · rw [isCoprime_sub_add_iff h2, isCoprime_iff_of_hyp hg3]
  · rw [isCoprime_comm, isCoprime_iff_of_hyp (by linear_combination hg1 : f ^ 2 + a ^ 2 = g ^ 2)]
  · rw [isCoprime_comm, isCoprime_iff_of_hyp (by linear_combination hg2 : e ^ 2 + b ^ 2 = g ^ 2)]
  · rw [isCoprime_comm, isCoprime_iff_of_hyp (by linear_combination hg3 : d ^ 2 + c ^ 2 = g ^ 2)]

/-! ### Mason–Stothers for Pythagorean triples over `K[X]`, characteristic `0` -/

/-- A coprime Pythagorean triple with a non-constant leg has a nonzero hypotenuse (any field). -/
theorem hyp_ne_zero {x y z : K[X]} (hxy : IsCoprime x y) (h : x ^ 2 + y ^ 2 = z ^ 2)
    (hx : 0 < x.natDegree) : z ≠ 0 := by
  rintro rfl
  have hy : y ^ 2 = -(x ^ 2) := by linear_combination h
  have h1 : IsCoprime (x ^ 2) (y ^ 2) := hxy.pow
  rw [hy, IsCoprime.neg_right_iff, isCoprime_self] at h1
  have := natDegree_eq_zero_of_isUnit (isUnit_pow_iff two_ne_zero |>.mp h1)
  omega

/-! ### The `S₄`-symmetry `a ↔ i g` and a pairwise coprime cuboid over `𝔽₅` -/

/-- **Space swap.** With `i² = -1`, `a² + b² + c² = g²` is `g² + (ib)² + (ic)² = a²`, so
`(g, ib, ic)` is again a cuboid, with face diagonals `e, d, if` and space diagonal `a`
(the cuboid surface is symmetric in `(a, b, c, ig)`, which satisfy `a² + b² + c² + (ig)² = 0`).
Nondegeneracy is preserved. -/
theorem isNondegCuboid_space_swap {i : K} (hi : i ^ 2 = -1) {a b c g : K[X]}
    (h : IsNondegCuboid a b c) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    IsNondegCuboid g (C i * b) (C i * c) := by
  have hCi : (C i : K[X]) ^ 2 = -1 := C_sq_eq_neg_one hi
  have hi0 : (C i : K[X]) ≠ 0 := by
    intro h0; rw [h0] at hCi; exact one_ne_zero (neg_eq_zero.mp (by rw [← hCi]; ring))
  obtain ⟨f, hf⟩ := h.sq_bc
  have e1 : g ^ 2 + (C i * b) ^ 2 = a ^ 2 + c ^ 2 := by
    linear_combination (-1 : K[X]) * hg + b ^ 2 * hCi
  have e2 : g ^ 2 + (C i * c) ^ 2 = a ^ 2 + b ^ 2 := by
    linear_combination (-1 : K[X]) * hg + c ^ 2 * hCi
  have e3 : (C i * b) ^ 2 + (C i * c) ^ 2 = -(b ^ 2 + c ^ 2) := by
    linear_combination (b ^ 2 + c ^ 2) * hCi
  have e4 : g ^ 2 + (C i * b) ^ 2 + (C i * c) ^ 2 = a ^ 2 := by
    linear_combination (-1 : K[X]) * hg + (b ^ 2 + c ^ 2) * hCi
  have hg0 : g ≠ 0 := by
    rintro rfl; exact h.ne_abc (by rw [hg]; ring)
  exact
  { ne_a := hg0
    ne_b := mul_ne_zero hi0 h.ne_b
    ne_c := mul_ne_zero hi0 h.ne_c
    sq_ab := by rw [e1]; exact h.sq_ac
    sq_ac := by rw [e2]; exact h.sq_ab
    sq_bc := ⟨C i * f, by rw [e3, hf]; linear_combination (-(f * f)) * hCi⟩
    sq_abc := ⟨a, by rw [e4]; ring⟩
    ne_ab := by rw [e1]; exact h.ne_ac
    ne_ac := by rw [e2]; exact h.ne_ab
    ne_bc := by rw [e3]; exact neg_ne_zero.mpr h.ne_bc
    ne_abc := by rw [e4]; exact pow_ne_zero 2 h.ne_a }

section FiveExample

local instance fact_prime_five' : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem five_eq_zero' : (5 : (ZMod 5)[X]) = 0 := by
  have : ((5 : ℕ) : (ZMod 5)[X]) = 0 := CharP.cast_eq_zero _ 5
  exact_mod_cast this

theorem ne_zero_of_eval_ne_zero {q : (ZMod 5)[X]} (x : ZMod 5) (h : q.eval x ≠ 0) : q ≠ 0 := by
  rintro rfl; simp at h

/-- **A nondegenerate, non-proportional cuboid over `𝔽₅[X]` with pairwise coprime edges**:
`(X⁶ - 1, X + X⁵, 2 (X⁶ + 1))`, with `a² + b² = ((1 + X²)³)²`, `a² + c² = (X³)²`,
`b² + c² = (2 (1 - X²)³)²`, `a² + b² + c² = (X - X⁵)²`. It is the space swap
(`isNondegCuboid_space_swap`) of the Frobenius cuboid `isNondegCuboid_five` (up to signs).
So "pairwise coprime edges ⇒ no nondegenerate cuboid" is false in characteristic `5`; any
proof in characteristic `0` must use the derivative branch of Mason–Stothers. Here
`gcd(a, f) = X² - 1`, `gcd(b, e) = X`, `gcd(c, d) = X² + 1`: no edge is coprime to the opposite
face diagonal (cf. `IsCuboid.common_leg`). -/
theorem isNondegCuboid_coprime_five :
    IsNondegCuboid (X ^ 6 - 1 : (ZMod 5)[X]) (X + X ^ 5) (2 * (X ^ 6 + 1)) := by
  have hd : (X ^ 6 - 1 : (ZMod 5)[X]) ^ 2 + (X + X ^ 5) ^ 2 = ((1 + X ^ 2) ^ 3) ^ 2 := by
    linear_combination (-1 * X ^ 2 + -3 * X ^ 4 + -4 * X ^ 6 + -3 * X ^ 8 + -1 * X ^ 10) *
      five_eq_zero'
  have he : (X ^ 6 - 1 : (ZMod 5)[X]) ^ 2 + (2 * (X ^ 6 + 1)) ^ 2 = (X ^ 3) ^ 2 := by
    linear_combination (1 + X ^ 6 + X ^ 12) * five_eq_zero'
  have hf : (X + X ^ 5 : (ZMod 5)[X]) ^ 2 + (2 * (X ^ 6 + 1)) ^ 2 = (2 * (1 - X ^ 2) ^ 3) ^ 2 := by
    linear_combination (5 * X ^ 2 + -12 * X ^ 4 + 18 * X ^ 6 + -12 * X ^ 8 + 5 * X ^ 10) *
      five_eq_zero'
  have hg : (X ^ 6 - 1 : (ZMod 5)[X]) ^ 2 + (X + X ^ 5) ^ 2 + (2 * (X ^ 6 + 1)) ^ 2 =
      (X - X ^ 5) ^ 2 := by
    linear_combination (1 + 2 * X ^ 6 + X ^ 12) * five_eq_zero'
  have n1 : ((1 + X ^ 2) ^ 3 : (ZMod 5)[X]) ≠ 0 := ne_zero_of_eval_ne_zero 0 (by simp)
  have n2 : (X ^ 3 : (ZMod 5)[X]) ≠ 0 := pow_ne_zero 3 X_ne_zero
  have n3 : (2 * (1 - X ^ 2) ^ 3 : (ZMod 5)[X]) ≠ 0 :=
    ne_zero_of_eval_ne_zero 0 (by simp; decide)
  have n4 : (X - X ^ 5 : (ZMod 5)[X]) ≠ 0 := by
    intro h; have := congrArg (coeff · 1) h; simp [coeff_X, coeff_X_pow] at this
  exact
  { ne_a := ne_zero_of_eval_ne_zero 0 (by simp)
    ne_b := ne_zero_of_eval_ne_zero 1 (by simp; decide)
    ne_c := ne_zero_of_eval_ne_zero 0 (by simp; decide)
    sq_ab := ⟨(1 + X ^ 2) ^ 3, by rw [hd]; ring⟩
    sq_ac := ⟨X ^ 3, by rw [he]; ring⟩
    sq_bc := ⟨2 * (1 - X ^ 2) ^ 3, by rw [hf]; ring⟩
    sq_abc := ⟨X - X ^ 5, by rw [hg]; ring⟩
    ne_ab := by rw [hd]; exact pow_ne_zero 2 n1
    ne_ac := by rw [he]; exact pow_ne_zero 2 n2
    ne_bc := by rw [hf]; exact pow_ne_zero 2 n3
    ne_abc := by rw [hg]; exact pow_ne_zero 2 n4 }

/-- The edges of `isNondegCuboid_coprime_five` are pairwise coprime (explicit Bézout
certificates). -/
theorem isCoprime_coprime_five :
    IsCoprime (X ^ 6 - 1 : (ZMod 5)[X]) (X + X ^ 5) ∧
    IsCoprime (X ^ 6 - 1 : (ZMod 5)[X]) (2 * (X ^ 6 + 1)) ∧
    IsCoprime (X + X ^ 5 : (ZMod 5)[X]) (2 * (X ^ 6 + 1)) :=
  ⟨⟨4 + 3 * X ^ 2 + 2 * X ^ 4, 3 * X + 2 * X ^ 3 + 3 * X ^ 5, by
      linear_combination (-1 + 2 * X ^ 6 + X ^ 8 + X ^ 10) * five_eq_zero'⟩,
    ⟨2, 4, by linear_combination (1 + 2 * X ^ 6) * five_eq_zero'⟩,
    ⟨2 * X + 2 * X ^ 3 + 2 * X ^ 5, 3 + 4 * X ^ 2 + 4 * X ^ 4, by
      linear_combination (1 + 2 * X ^ 2 + 2 * X ^ 4 + 2 * X ^ 6 + 2 * X ^ 8 + 2 * X ^ 10) *
        five_eq_zero'⟩⟩

theorem not_proportional_coprime_five :
    ¬ Proportional (X ^ 6 - 1 : (ZMod 5)[X]) (X + X ^ 5) (2 * (X ^ 6 + 1)) := by
  apply not_proportional_of_natDegree_ne isNondegCuboid_coprime_five.ne_a
    isNondegCuboid_coprime_five.ne_b
  have h1 : (X ^ 6 - 1 : (ZMod 5)[X]).natDegree = 6 := by compute_degree!
  have h2 : (X + X ^ 5 : (ZMod 5)[X]).natDegree = 5 := by compute_degree!
  rw [h1, h2]; omega

end FiveExample

/-! ### Euler's parametrisation of `a² + b² + c² = g²` and the `(t, s)` form of the cuboid -/

/-- **Four-number lemma** in `K[X]`: `xy = zw ⇒ x = PR, y = QS, z = PS, w = QR`. -/
theorem four_number {x y z w : K[X]} (h : x * y = z * w) :
    ∃ P Q R S : K[X], x = P * R ∧ y = Q * S ∧ z = P * S ∧ w = Q * R := by
  by_cases hx : x = 0
  · subst hx
    have hzw : z * w = 0 := by rw [← h]; ring
    rcases mul_eq_zero.mp hzw with hz | hw
    · exact ⟨0, 1, w, y, by ring, by ring, by rw [hz]; ring, by ring⟩
    · exact ⟨z, y, 0, 1, by ring, by ring, by ring, by rw [hw]; ring⟩
  · obtain ⟨P, R, hP, hR, hPR⟩ := exists_dvd_and_dvd_of_dvd_mul (⟨y, h.symm⟩ : x ∣ z * w)
    obtain ⟨S, hS⟩ := hP
    obtain ⟨Q, hQ⟩ := hR
    refine ⟨P, Q, R, S, hPR, ?_, by rw [hS], by rw [hQ]; ring⟩
    have hPR0 : P * R ≠ 0 := by rw [← hPR]; exact hx
    apply mul_left_cancel₀ hPR0
    calc P * R * y = x * y := by rw [hPR]
      _ = z * w := h
      _ = P * R * (Q * S) := by rw [hS, hQ]; ring

/-- **Euler's parametrisation of the space-diagonal quadric** (`i² = -1`, any field): if
`a² + b² + c² = g²` then there are `P, Q, R, S ∈ K[X]` with
`2a = PR + QS`, `2ib = PR - QS`, `2c = QR - PS`, `2g = PS + QR`, and then
`a² + b² = PQRS`, `4(a² + c²) = (P² + Q²)(R² + S²)`, `4(b² + c²) = (Q² - P²)(R² - S²)`.
So a cuboid over `K[X]` is the same as `(P, Q, R, S)` with `PQRS`, `(P² + Q²)(R² + S²)`,
`(P² - Q²)(R² - S²)` squares; with `t = P/Q`, `s = R/S`: `ts`, `(t² + 1)(s² + 1)`,
`(t² - 1)(s² - 1)` squares in `K(X)`. -/
theorem exists_euler_param {i : K} (hi : i ^ 2 = -1) {a b c g : K[X]}
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    ∃ P Q R S : K[X], C 2 * a = P * R + Q * S ∧ C 2 * (C i * b) = P * R - Q * S ∧
      C 2 * c = Q * R - P * S ∧ C 2 * g = P * S + Q * R ∧
      a ^ 2 + b ^ 2 = P * Q * R * S ∧
      C 4 * (a ^ 2 + c ^ 2) = (P ^ 2 + Q ^ 2) * (R ^ 2 + S ^ 2) ∧
      C 4 * (b ^ 2 + c ^ 2) = (Q ^ 2 - P ^ 2) * (R ^ 2 - S ^ 2) := by
  have hCi : (C i : K[X]) ^ 2 = -1 := C_sq_eq_neg_one hi
  have key : (a + C i * b) * (a - C i * b) = (g - c) * (g + c) := by
    linear_combination (-b ^ 2) * hCi + hg
  obtain ⟨P, Q, R, S, h1, h2', h3, h4⟩ := four_number key
  have h22 : (C 2 : K[X]) = 2 := map_ofNat C 2
  have h44 : (C 4 : K[X]) = 4 := map_ofNat C 4
  have ea : C 2 * a = P * R + Q * S := by rw [h22, ← h1, ← h2']; ring
  have eb : C 2 * (C i * b) = P * R - Q * S := by rw [h22, ← h1, ← h2']; ring
  have ec : C 2 * c = Q * R - P * S := by rw [h22, ← h3, ← h4]; ring
  have eg : C 2 * g = P * S + Q * R := by rw [h22, ← h3, ← h4]; ring
  refine ⟨P, Q, R, S, ea, eb, ec, eg, ?_, ?_, ?_⟩
  · have : a ^ 2 + b ^ 2 = (a + C i * b) * (a - C i * b) := by
      linear_combination b ^ 2 * hCi
    rw [this, h1, h2']; ring
  · rw [h44, show (4 : K[X]) * (a ^ 2 + c ^ 2) = (C 2 * a) ^ 2 + (C 2 * c) ^ 2 by
      rw [h22]; ring, ea, ec]; ring
  · have : (4 : K[X]) * (b ^ 2 + c ^ 2) = -(C 2 * (C i * b)) ^ 2 + (C 2 * c) ^ 2 := by
      rw [h22]; linear_combination (4 * b ^ 2) * hCi
    rw [h44, this, eb, ec]; ring

/-- **Converse of `exists_euler_param`**: any `a, b, c, g` with `2a = PR + QS`,
`2ib = PR - QS`, `2c = QR - PS`, `2g = PS + QR` solve the quadric, with the stated face sums. -/
theorem euler_param_identities (h2 : (2 : K) ≠ 0) {i : K} (hi : i ^ 2 = -1)
    {P Q R S a b c g : K[X]} (ea : C 2 * a = P * R + Q * S)
    (eb : C 2 * (C i * b) = P * R - Q * S) (ec : C 2 * c = Q * R - P * S)
    (eg : C 2 * g = P * S + Q * R) :
    a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 ∧ a ^ 2 + b ^ 2 = P * Q * R * S ∧
      C 4 * (a ^ 2 + c ^ 2) = (P ^ 2 + Q ^ 2) * (R ^ 2 + S ^ 2) ∧
      C 4 * (b ^ 2 + c ^ 2) = (Q ^ 2 - P ^ 2) * (R ^ 2 - S ^ 2) := by
  have hCi : (C i : K[X]) ^ 2 = -1 := C_sq_eq_neg_one hi
  have h22 : (C 2 : K[X]) = 2 := map_ofNat C 2
  have h44 : (C 4 : K[X]) = 4 := map_ofNat C 4
  rw [h22] at ea eb ec eg
  have h4 : (4 : K[X]) ≠ 0 := by
    rw [← h44]; refine C_ne_zero.mpr ?_
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply mul_left_cancel₀ h4
    linear_combination (2 * a + P * R + Q * S) * ea - (2 * (C i * b) + P * R - Q * S) * eb +
      (2 * c + Q * R - P * S) * ec - (2 * g + P * S + Q * R) * eg + 4 * b ^ 2 * hCi
  · apply mul_left_cancel₀ h4
    linear_combination (2 * a + P * R + Q * S) * ea - (2 * (C i * b) + P * R - Q * S) * eb +
      4 * b ^ 2 * hCi
  · rw [h44]
    linear_combination (2 * a + P * R + Q * S) * ea + (2 * c + Q * R - P * S) * ec
  · rw [h44]
    linear_combination -(2 * (C i * b) + P * R - Q * S) * eb + (2 * c + Q * R - P * S) * ec +
      4 * b ^ 2 * hCi

/-- **Cuboids in Euler coordinates**: a cuboid `(a, b, c)` over `K[X]` (`i² = -1`) comes from
`(P, Q, R, S)` as in `exists_euler_param` with `PQRS`, `(P² + Q²)(R² + S²)` and
`(Q² - P²)(R² - S²)` squares. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.exists_euler {i : K} (hi : i ^ 2 = -1)
    {a b c : K[X]} (h : IsCuboid a b c) :
    ∃ P Q R S : K[X], C 2 * a = P * R + Q * S ∧ C 2 * (C i * b) = P * R - Q * S ∧
      C 2 * c = Q * R - P * S ∧ IsSquare (P * Q * R * S) ∧
      IsSquare ((P ^ 2 + Q ^ 2) * (R ^ 2 + S ^ 2)) ∧
      IsSquare ((Q ^ 2 - P ^ 2) * (R ^ 2 - S ^ 2)) := by
  obtain ⟨g, hg⟩ := h.sq_abc
  obtain ⟨P, Q, R, S, ea, eb, ec, -, e1, e2, e3⟩ := exists_euler_param hi (g := g)
    (by rw [hg]; ring)
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨f, hf⟩ := h.sq_bc
  have h22 : (C 4 : K[X]) = C 2 * C 2 := by rw [← C_mul]; norm_num
  refine ⟨P, Q, R, S, ea, eb, ec, ⟨d, by rw [← e1, hd]⟩, ⟨C 2 * e, ?_⟩, ⟨C 2 * f, ?_⟩⟩
  · rw [← e2, he, h22]; ring
  · rw [← e3, hf, h22]; ring

section MasonStothers

variable [DecidableEq K]

open UniqueFactorizationMonoid in
/-- **Mason–Stothers for a Pythagorean triple over `K[X]`, `char K = 0`.** If `x² + y² = z²`
with `x, y` coprime, all nonzero and not all constant, then each of `2 deg x + 1`, `2 deg y + 1`,
`2 deg z + 1` is at most `deg rad x + deg rad y + deg rad z`. (Over `𝔽_p` this fails: the
derivative branch of `Polynomial.abc` is where characteristic `0` enters.) -/
theorem two_mul_natDegree_add_one_le [CharZero K] {x y z : K[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (hxy : IsCoprime x y) (h : x ^ 2 + y ^ 2 = z ^ 2)
    (hnc : 0 < x.natDegree ∨ 0 < y.natDegree ∨ 0 < z.natDegree) :
    2 * x.natDegree + 1 ≤ (radical x).natDegree + (radical y).natDegree + (radical z).natDegree ∧
    2 * y.natDegree + 1 ≤ (radical x).natDegree + (radical y).natDegree + (radical z).natDegree ∧
    2 * z.natDegree + 1 ≤
      (radical x).natDegree + (radical y).natDegree + (radical z).natDegree := by
  have hsum : x ^ 2 + y ^ 2 + (-(z ^ 2)) = 0 := by rw [h]; ring
  rcases Polynomial.abc (pow_ne_zero 2 hx) (pow_ne_zero 2 hy) (neg_ne_zero.mpr (pow_ne_zero 2 hz))
    (hxy.pow) hsum with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hrad : (radical (x ^ 2 * y ^ 2 * -(z ^ 2))).natDegree ≤
        (radical x).natDegree + (radical y).natDegree + (radical z).natDegree := by
      have : x ^ 2 * y ^ 2 * -(z ^ 2) = -((x * y * z) ^ 2) := by ring
      rw [this, UniqueFactorizationDomain.radical_neg, radical_pow _ two_ne_zero]
      have hdvd : radical (x * y * z) ∣ radical x * radical y * radical z :=
        radical_mul_dvd.trans (mul_dvd_mul_right radical_mul_dvd _)
      have hne : radical x * radical y * radical z ≠ 0 :=
        mul_ne_zero (mul_ne_zero radical_ne_zero radical_ne_zero) radical_ne_zero
      refine (natDegree_le_of_dvd hdvd hne).trans ?_
      rw [natDegree_mul (mul_ne_zero radical_ne_zero radical_ne_zero) radical_ne_zero,
        natDegree_mul radical_ne_zero radical_ne_zero]
    rw [natDegree_pow] at h1 h2
    rw [natDegree_neg, natDegree_pow] at h3
    omega
  · rw [derivative_neg, neg_eq_zero] at h3
    have e1 := derivative_eq_zero.mp h1
    have e2 := derivative_eq_zero.mp h2
    have e3 := derivative_eq_zero.mp h3
    rw [natDegree_pow] at e1 e2 e3
    omega

open UniqueFactorizationMonoid in
/-- Radical form for the hypotenuse, `char K = 0`, general `K`:
`deg z + 1 ≤ deg rad x + deg rad y` (port of `natDegree_hyp_add_one_le_radical`, which is over
`ℚ`). -/
theorem natDegree_hyp_add_one_le_radical [CharZero K] {x y z : K[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : IsCoprime x y) (h : x ^ 2 + y ^ 2 = z ^ 2) (hz : 0 < z.natDegree) :
    z.natDegree + 1 ≤ (radical x).natDegree + (radical y).natDegree := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have := (two_mul_natDegree_add_one_le hx hy hz0 hxy h (Or.inr (Or.inr hz))).2.2
  have := natDegree_radical_le (a := z)
  omega

omit [DecidableEq K] in
open UniqueFactorizationMonoid in
/-- **A coprime Pythagorean triple with one non-constant leg has the other leg and the
hypotenuse non-constant** (here via Mason–Stothers, `char K = 0`; the statement itself holds in
every characteristic `≠ 2` by factoring `y² = (z - x)(z + x)`, resp. `z² = (x + iy)(x - iy)`
over `K(i)`, and fails in characteristic `2`, where `x² + 1 = (x + 1)²`). -/
theorem natDegree_pos_of_leg [CharZero K] {x y z : K[X]} (hy : y ≠ 0) (hxy : IsCoprime x y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) (hx : 0 < x.natDegree) :
    0 < y.natDegree ∧ 0 < z.natDegree := by
  classical
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hz0 := hyp_ne_zero hxy h hx
  obtain ⟨h1, h2, h3⟩ := two_mul_natDegree_add_one_le hx0 hy hz0 hxy h (Or.inl hx)
  have rx := natDegree_radical_le (a := x)
  have ry := natDegree_radical_le (a := y)
  have rz := natDegree_radical_le (a := z)
  omega

/-! ### Mason–Stothers for cuboids with pairwise coprime edges, characteristic `0` -/

open UniqueFactorizationMonoid in
/-- **Radical bounds for a cuboid with pairwise coprime edges, `char K = 0`.** If one edge is
non-constant then all three edges and all three face diagonals are non-constant (and nonzero),
the brick bound `deg d + deg e + deg f + 3 ≤ 2 (deg rad a + deg rad b + deg rad c)` holds
(port of `IsPolyBrick.radical_sum_bound` from `ℚ` to any `K` of characteristic `0`, with no
leading-coefficient hypothesis), and each face satisfies the sharper
`2 max(deg a, deg b, deg d) + 1 ≤ deg rad a + deg rad b + deg rad d`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.radical_bound [CharZero K] {a b c : K[X]}
    (h : IsCuboid a b c) (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    (hnc : 0 < a.natDegree ∨ 0 < b.natDegree ∨ 0 < c.natDegree)
    {d e f : K[X]} (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    (0 < a.natDegree ∧ 0 < b.natDegree ∧ 0 < c.natDegree ∧
      0 < d.natDegree ∧ 0 < e.natDegree ∧ 0 < f.natDegree) ∧
    d.natDegree + e.natDegree + f.natDegree + 3 ≤
      2 * ((radical a).natDegree + (radical b).natDegree + (radical c).natDegree) ∧
    2 * max a.natDegree (max b.natDegree d.natDegree) + 1 ≤
      (radical a).natDegree + (radical b).natDegree + (radical d).natDegree ∧
    2 * max a.natDegree (max c.natDegree e.natDegree) + 1 ≤
      (radical a).natDegree + (radical c).natDegree + (radical e).natDegree ∧
    2 * max b.natDegree (max c.natDegree f.natDegree) + 1 ≤
      (radical b).natDegree + (radical c).natDegree + (radical f).natDegree := by
  have hpos : 0 < a.natDegree ∧ 0 < b.natDegree ∧ 0 < c.natDegree := by
    rcases hnc with ha | hb | hc
    · exact ⟨ha, (natDegree_pos_of_leg h.ne_b hab hd ha).1,
        (natDegree_pos_of_leg h.ne_c hac he ha).1⟩
    · exact ⟨(natDegree_pos_of_leg (z := d) h.ne_a hab.symm (by linear_combination hd) hb).1, hb,
        (natDegree_pos_of_leg h.ne_c hbc hf hb).1⟩
    · exact ⟨(natDegree_pos_of_leg (z := e) h.ne_a hac.symm (by linear_combination he) hc).1,
        (natDegree_pos_of_leg (z := f) h.ne_b hbc.symm (by linear_combination hf) hc).1, hc⟩
  obtain ⟨pa, pb, pc⟩ := hpos
  have pd := (natDegree_pos_of_leg h.ne_b hab hd pa).2
  have pe := (natDegree_pos_of_leg h.ne_c hac he pa).2
  have pf := (natDegree_pos_of_leg h.ne_c hbc hf pb).2
  have hd0 : d ≠ 0 := by rintro rfl; simp at pd
  have he0 : e ≠ 0 := by rintro rfl; simp at pe
  have hf0 : f ≠ 0 := by rintro rfl; simp at pf
  obtain ⟨d1, d2, d3⟩ := two_mul_natDegree_add_one_le h.ne_a h.ne_b hd0 hab hd (Or.inl pa)
  obtain ⟨e1, e2, e3⟩ := two_mul_natDegree_add_one_le h.ne_a h.ne_c he0 hac he (Or.inl pa)
  obtain ⟨f1, f2, f3⟩ := two_mul_natDegree_add_one_le h.ne_b h.ne_c hf0 hbc hf (Or.inl pb)
  have rd := natDegree_radical_le (a := d)
  have re := natDegree_radical_le (a := e)
  have rf := natDegree_radical_le (a := f)
  refine ⟨⟨pa, pb, pc, pd, pe, pf⟩, by omega, ?_, ?_, ?_⟩ <;> omega

open UniqueFactorizationMonoid in
/-- **The fourth equation**, `char K = 0`: for a cuboid with pairwise coprime edges, one
non-constant edge, and `gcd(a, f) = 1` (equivalently `gcd(g - f, g + f) = 1`, `common_leg`),
the space diagonal is non-constant and
`2 max(deg a, deg f, deg g) + 1 ≤ deg rad a + deg rad f + deg rad g`; in particular
`deg g + 1 ≤ deg rad a + deg rad f`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.radical_bound_space [CharZero K] {a b c : K[X]}
    (h : IsCuboid a b c) (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    (hnc : 0 < a.natDegree ∨ 0 < b.natDegree ∨ 0 < c.natDegree)
    {d e f g : K[X]} (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (haf : IsCoprime a f) :
    0 < g.natDegree ∧
    2 * max a.natDegree (max f.natDegree g.natDegree) + 1 ≤
      (radical a).natDegree + (radical f).natDegree + (radical g).natDegree ∧
    g.natDegree + 1 ≤ (radical a).natDegree + (radical f).natDegree := by
  obtain ⟨⟨pa, -, -, -, -, pf⟩, -⟩ := h.radical_bound hab hac hbc hnc hd he hf
  have hf0 : f ≠ 0 := by rintro rfl; simp at pf
  have hg1 : a ^ 2 + f ^ 2 = g ^ 2 := by linear_combination hg - hf
  have pg := (natDegree_pos_of_leg hf0 haf hg1 pa).2
  have hg0 : g ≠ 0 := by rintro rfl; simp at pg
  obtain ⟨g1, g2, g3⟩ := two_mul_natDegree_add_one_le h.ne_a hf0 hg0 haf hg1 (Or.inl pa)
  have rg := natDegree_radical_le (a := g)
  refine ⟨pg, by omega, by omega⟩

end MasonStothers

end PerfectCuboid.PolyPythagoras
