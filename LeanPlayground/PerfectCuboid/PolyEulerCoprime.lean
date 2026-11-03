module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolyCharP
public import LeanPlayground.PerfectCuboid.PolyPythagoras
public import LeanPlayground.PerfectCuboid.PolyFermat
public import LeanPlayground.PerfectCuboid.PolyNegOne

/-!
# The Euler–Fermat coprime kill: cuboids over `K[X]` with coprime edges and opposite pairs

Let `K` be **any** field with `2 ≠ 0` (no characteristic hypothesis). For a cuboid
`a, b, c ∈ K[X]` with face diagonals `d² = a² + b²`, `e² = a² + c²`, `f² = b² + c²` and space
diagonal `g² = a² + b² + c²`:

* `IsCuboid.natDegree_eq_zero_of_coprime`: if `a ⊥ b`, `a ⊥ c`, `b ⊥ e`, `c ⊥ d` and
  `a² + b² ≠ 0`, `b² + c² ≠ 0`, then `a`, `b`, `c` are constants
  (`proportional_of_coprime`: hence `Proportional a b c`).
* `IsNondegCuboid.natDegree_eq_zero_of_fully_coprime`: the symmetric form (pairwise coprime edges,
  each edge coprime to its opposite face diagonal).
* `IsNondegCuboid.not_two_opposite_coprime`: in a nondegenerate cuboid with pairwise coprime edges
  and a non-constant edge, at most one of the opposite pairs `(a, f)`, `(b, e)`, `(c, d)` is
  coprime.

**Proof.** Over `L = AlgebraicClosure K` pick `i² = -1`. Euler's four-number factorisation of
`(a + ib)(a - ib) = (g - c)(g + c)` gives `P R = a + ib`, `Q S = a - ib`, `P S = g - c`,
`Q R = g + c` (`exists_euler_factors`). `a ⊥ b` makes `a ± ib` coprime and `c ⊥ d` makes `c ⊥ g`,
hence `g ± c` coprime; so `P, Q, R, S` are pairwise coprime, and `PQRS = d²` makes each a unit
times a square (`four_coprime_sq`). A common prime `π` of `P² + Q²` and `R² + S²` divides
`R²(P² + Q²) - Q²(R² + S²) = 4iab` and `(P² + Q²)(R² + S²) = 4e²`, contradicting `a ⊥ c` or `b ⊥ e`.
So `P² + Q² = κ w²`, i.e. `uP² p⁴ + uQ² q⁴ = κ w²`, and the polynomial Fermat quartic
`PolyFermat.quartic_coprime_gen` (Mathlib's `flt_catalan` with exponents `(4, 4, 2)`) makes
`P, Q` constant. Then `(Q² - P²)(R² - S²) = 4f²` with `Q² - P²` a nonzero constant gives
`uR² r⁴ - uS² s⁴ = κ' f²`, and the quartic again makes `R, S` constant; so are `a, b, c`.

**Sharpness** (`_common.md` §0.3): the 𝔽₅ pairwise-coprime cuboid `(X⁶ - 1, X + X⁵, 2(X⁶ + 1))`
has all three opposite gcds nontrivial; the Frobenius cuboids have `gcd(b, e) = gcd(c, d) = 1` but
`gcd(a, b) = X`; the 𝔽₇ cuboid has `gcd(a, c) = X`; the degenerate `(2X, X² - 1, i(X² + 1))` has
`e = ib` (so `b ⊥ e` fails). No statement here concerns merely pairwise coprime edges (false over
𝔽₅, open over `ℂ`).
-/

@[expose] public section

open Polynomial

namespace PerfectCuboid.PolyEulerCoprime

variable {K : Type*} [Field K]

open PolyCharP

/-- Four pairwise coprime polynomials whose product is a square are units times squares. -/
theorem four_coprime_sq {P Q R S d : K[X]} (hPQ : IsCoprime P Q) (hPR : IsCoprime P R)
    (hPS : IsCoprime P S) (hQR : IsCoprime Q R) (hQS : IsCoprime Q S) (hRS : IsCoprime R S)
    (h : P * Q * R * S = d ^ 2) :
    ∃ (uP uQ uR uS : K) (p q r s : K[X]), uP ≠ 0 ∧ uQ ≠ 0 ∧ uR ≠ 0 ∧ uS ≠ 0 ∧
      P = C uP * p ^ 2 ∧ Q = C uQ * q ^ 2 ∧ R = C uR * r ^ 2 ∧ S = C uS * s ^ 2 := by
  obtain ⟨uP, p, huP, hp⟩ := PolyPythagoras.exists_sq_of_coprime_mul_eq one_ne_zero
    ((hPQ.mul_right hPR).mul_right hPS) (r := d) (by rw [C_1, one_mul, ← h]; ring)
  obtain ⟨uQ, q, huQ, hq⟩ := PolyPythagoras.exists_sq_of_coprime_mul_eq one_ne_zero
    ((hPQ.symm.mul_right hQR).mul_right hQS) (r := d) (by rw [C_1, one_mul, ← h]; ring)
  obtain ⟨uR, r, huR, hr⟩ := PolyPythagoras.exists_sq_of_coprime_mul_eq one_ne_zero
    ((hPR.symm.mul_right hQR.symm).mul_right hRS) (r := d) (by rw [C_1, one_mul, ← h]; ring)
  obtain ⟨uS, s, huS, hs⟩ := PolyPythagoras.exists_sq_of_coprime_mul_eq one_ne_zero
    ((hPS.symm.mul_right hQS.symm).mul_right hRS.symm) (r := d) (by rw [C_1, one_mul, ← h]; ring)
  exact ⟨uP, uQ, uR, uS, p, q, r, s, huP, huQ, huR, huS, hp, hq, hr, hs⟩

/-- Euler's factorisation of `a² + b² + c² = g²` with the four product identities. -/
theorem exists_euler_factors {i : K} (hi : i ^ 2 = -1) {a b c g : K[X]}
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    ∃ P Q R S : K[X], P * R = a + C i * b ∧ Q * S = a - C i * b ∧ P * S = g - c ∧
      Q * R = g + c := by
  have hCi : (C i : K[X]) ^ 2 = -1 := C_sq_eq_neg_one hi
  have key : (a + C i * b) * (a - C i * b) = (g - c) * (g + c) := by
    linear_combination (-b ^ 2) * hCi + hg
  obtain ⟨P, Q, R, S, h1, h2, h3, h4⟩ := PolyPythagoras.four_number key
  exact ⟨P, Q, R, S, h1.symm, h2.symm, h3.symm, h4.symm⟩

/-- `a ⊥ b ⇒ (a + ib) ⊥ (a - ib)` when `2 ≠ 0`. -/
theorem isCoprime_add_sub_mul_I (h2 : (2 : K) ≠ 0) {i : K} (hi : i ^ 2 = -1) {a b : K[X]}
    (hab : IsCoprime a b) : IsCoprime (a + C i * b) (a - C i * b) := by
  have hCi : (C i : K[X]) ^ 2 = -1 := C_sq_eq_neg_one hi
  obtain ⟨u, v, huv⟩ := hab
  refine ⟨C 2⁻¹ * (u - C i * v), C 2⁻¹ * (u + C i * v), ?_⟩
  linear_combination (u * a + v * b) * PolyPythagoras.C_inv_two_mul_two h2 + huv -
    C 2⁻¹ * 2 * v * b * hCi

/-- **Main theorem, `i ∈ K`.** -/
theorem natDegree_eq_zero_of_coprime_aux (h2 : (2 : K) ≠ 0) {i : K} (hi : i ^ 2 = -1)
    {a b c d e g : K[X]}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : IsSquare (b ^ 2 + c ^ 2))
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbe : IsCoprime b e) (hcd : IsCoprime c d)
    (hne_ab : a ^ 2 + b ^ 2 ≠ 0) (hne_bc : b ^ 2 + c ^ 2 ≠ 0) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  have hCi : (C i : K[X]) ^ 2 = -1 := C_sq_eq_neg_one hi
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hi
    exact one_ne_zero (neg_eq_zero.mp hi.symm)
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  obtain ⟨f, hf'⟩ := hf
  have hfsq : b ^ 2 + c ^ 2 = f ^ 2 := by rw [hf', sq]
  obtain ⟨P, Q, R, S, hPR, hQS, hPS, hQR⟩ := exists_euler_factors hi hg
  have h22 : (C 2 : K[X]) = 2 := map_ofNat C 2
  have ea : C 2 * a = P * R + Q * S := by rw [h22, hPR, hQS]; ring
  have eb : C 2 * (C i * b) = P * R - Q * S := by rw [h22, hPR, hQS]; ring
  have ec : C 2 * c = Q * R - P * S := by rw [h22, hPS, hQR]; ring
  have eg : C 2 * g = P * S + Q * R := by rw [h22, hPS, hQR]; ring
  obtain ⟨-, hprod, hAB, hQP⟩ := PolyPythagoras.euler_param_identities h2 hi ea eb ec eg
  -- nonvanishing
  have hPRQS : (a + C i * b) * (a - C i * b) = a ^ 2 + b ^ 2 := by
    linear_combination -b ^ 2 * hCi
  have hPRne : P * R ≠ 0 := by
    rw [hPR]; intro h0; apply hne_ab; rw [← hPRQS, h0, zero_mul]
  have hQSne : Q * S ≠ 0 := by
    rw [hQS]; intro h0; apply hne_ab; rw [← hPRQS, h0, mul_zero]
  have hP0 : P ≠ 0 := left_ne_zero_of_mul hPRne
  have hR0 : R ≠ 0 := right_ne_zero_of_mul hPRne
  have hQ0 : Q ≠ 0 := left_ne_zero_of_mul hQSne
  have hS0 : S ≠ 0 := right_ne_zero_of_mul hQSne
  -- coprimality of `P, Q, R, S`
  have h1 : IsCoprime (P * R) (Q * S) := by
    rw [hPR, hQS]; exact isCoprime_add_sub_mul_I h2 hi hab
  have hdc : d ^ 2 + c ^ 2 = g ^ 2 := by rw [← hd]; exact hg
  have hcg : IsCoprime c g := (PolyPythagoras.isCoprime_iff_of_hyp hdc).mp hcd.symm
  have h1' : IsCoprime (P * S) (Q * R) := by
    rw [hPS, hQR]; exact (PolyPythagoras.isCoprime_sub_add_iff h2).mpr hcg
  have hPQ : IsCoprime P Q := h1.of_mul_left_left.of_mul_right_left
  have hPS' : IsCoprime P S := h1.of_mul_left_left.of_mul_right_right
  have hRQ : IsCoprime R Q := h1.of_mul_left_right.of_mul_right_left
  have hRS : IsCoprime R S := h1.of_mul_left_right.of_mul_right_right
  have hPR' : IsCoprime P R := h1'.of_mul_left_left.of_mul_right_right
  have hSQ : IsCoprime S Q := h1'.of_mul_left_right.of_mul_right_left
  have hd2 : P * Q * R * S = d ^ 2 := by rw [← hprod, hd]
  obtain ⟨uP, uQ, uR, uS, p, q, r, s, huP, huQ, huR, huS, hp, hq, hr, hs⟩ :=
    four_coprime_sq hPQ hPR' hPS' hRQ.symm hSQ.symm hRS hd2
  -- `P² + Q² ⊥ R² + S²`
  have hAB' : (P ^ 2 + Q ^ 2) * (R ^ 2 + S ^ 2) = C 4 * e ^ 2 := by rw [← hAB, he]
  have hcopAB : IsCoprime (P ^ 2 + Q ^ 2) (R ^ 2 + S ^ 2) := by
    have key : ∀ π : K[X], Prime π → π ∣ P ^ 2 + Q ^ 2 → π ∣ R ^ 2 + S ^ 2 → False := by
      intro π hπ hA hB
      have h4u : IsUnit (C (4 * i) : K[X]) :=
        isUnit_C.mpr (isUnit_iff_ne_zero.mpr (mul_ne_zero h4 hi0))
      have hab' : π ∣ C (4 * i) * (a * b) := by
        have e1 : C (4 * i) * (a * b) = (P ^ 2 + Q ^ 2) * R ^ 2 - (R ^ 2 + S ^ 2) * Q ^ 2 := by
          have e2 : (P ^ 2 + Q ^ 2) * R ^ 2 - (R ^ 2 + S ^ 2) * Q ^ 2 =
              (P * R) ^ 2 - (Q * S) ^ 2 := by ring
          rw [e2, hPR, hQS, C_mul, show (C 4 : K[X]) = 4 from map_ofNat C 4]; ring
        rw [e1]; exact dvd_sub (dvd_mul_of_dvd_left hA _) (dvd_mul_of_dvd_left hB _)
      have he' : π ∣ e := by
        have h3 : π ∣ C 4 * e ^ 2 := by rw [← hAB']; exact dvd_mul_of_dvd_left hA _
        rcases hπ.dvd_or_dvd h3 with h | h
        · exact absurd (isUnit_of_dvd_unit h (isUnit_C.mpr (isUnit_iff_ne_zero.mpr h4)))
            hπ.not_isUnit
        · exact hπ.dvd_of_dvd_pow h
      rcases hπ.dvd_or_dvd hab' with h | h
      · exact hπ.not_isUnit (isUnit_of_dvd_unit h h4u)
      rcases hπ.dvd_or_dvd h with h | h
      · have hc' : π ∣ c := by
          refine hπ.dvd_of_dvd_pow (n := 2) ?_
          have e3 : c ^ 2 = e ^ 2 - a ^ 2 := by rw [← he]; ring
          rw [e3]; exact dvd_sub (dvd_pow he' two_ne_zero) (dvd_pow h two_ne_zero)
        exact hπ.not_isUnit (hac.isUnit_of_dvd' h hc')
      · exact hπ.not_isUnit (hbe.isUnit_of_dvd' h he')
    refine isCoprime_of_prime_dvd ?_ (fun π hπ hA hB => key π hπ hA hB)
    rintro ⟨hA0, hB0⟩
    exact key X prime_X (by rw [hA0]; exact dvd_zero _) (by rw [hB0]; exact dvd_zero _)
  -- first Fermat quartic: `P, Q` constant
  obtain ⟨κ, w, hκ0, hκ⟩ := PolyPythagoras.exists_sq_of_coprime_mul_eq h4 hcopAB hAB'
  have hp0 : p ≠ 0 := by rintro rfl; apply hP0; rw [hp]; ring
  have hq0 : q ≠ 0 := by rintro rfl; apply hQ0; rw [hq]; ring
  have hr0 : r ≠ 0 := by rintro rfl; apply hR0; rw [hr]; ring
  have hs0 : s ≠ 0 := by rintro rfl; apply hS0; rw [hs]; ring
  have hcop_sq : ∀ {x y : K[X]} {ux uy : K}, IsCoprime (C ux * x ^ 2) (C uy * y ^ 2) →
      IsCoprime x y := by
    intro x y ux uy hxy
    exact (IsCoprime.pow_iff two_pos two_pos).mp hxy.of_mul_left_right.symm.of_mul_left_right.symm
  have hpq : IsCoprime p q := hcop_sq (by rw [← hp, ← hq]; exact hPQ)
  have hrs : IsCoprime r s := hcop_sq (by rw [← hr, ← hs]; exact hRS)
  have hquart1 : C (uP ^ 2) * p ^ 4 + C (uQ ^ 2) * q ^ 4 = C κ * w ^ 2 := by
    rw [← hκ, hp, hq]; simp only [map_pow]; ring
  obtain ⟨hpd, hqd⟩ := PolyFermat.quartic_coprime_gen h2 (pow_ne_zero 2 huP)
    (pow_ne_zero 2 huQ) hκ0 hp0 hq0 hpq hquart1
  have hdeg : ∀ {x X' : K[X]} {u : K}, u ≠ 0 → X' = C u * x ^ 2 → x.natDegree = 0 →
      X'.natDegree = 0 := by
    intro x X' u hu hX hx
    rw [hX, natDegree_C_mul hu, natDegree_pow, hx, mul_zero]
  obtain ⟨α, hα⟩ := natDegree_eq_zero.mp (hdeg huP hp hpd)
  obtain ⟨β, hβ⟩ := natDegree_eq_zero.mp (hdeg huQ hq hqd)
  subst hα hβ
  -- second Fermat quartic: `R, S` constant
  set θ : K := β ^ 2 - α ^ 2 with hθdef
  have hθ : θ ≠ 0 := by
    intro h0
    apply hne_bc
    have h5 : C 4 * (b ^ 2 + c ^ 2) = 0 := by
      rw [hQP, ← C_pow, ← C_pow, ← C_sub, ← hθdef, h0, C_0, zero_mul]
    rcases mul_eq_zero.mp h5 with h | h
    · exact absurd (C_eq_zero.mp h) h4
    · exact h
  have hquart2 : C (uR ^ 2) * r ^ 4 + C (-uS ^ 2) * s ^ 4 = C (4 / θ) * f ^ 2 := by
    apply mul_left_cancel₀ (C_ne_zero.mpr hθ)
    calc C θ * (C (uR ^ 2) * r ^ 4 + C (-uS ^ 2) * s ^ 4)
        = (C β ^ 2 - C α ^ 2) * (R ^ 2 - S ^ 2) := by
          rw [hθdef, hr, hs]; simp only [map_pow, map_neg, map_sub]; ring
      _ = C 4 * f ^ 2 := by rw [← hQP, hfsq]
      _ = C θ * (C (4 / θ) * f ^ 2) := by rw [← mul_assoc, ← C_mul, mul_div_cancel₀ _ hθ]
  obtain ⟨hrd, hsd⟩ := PolyFermat.quartic_coprime_gen h2 (pow_ne_zero 2 huR)
    (neg_ne_zero.mpr (pow_ne_zero 2 huS)) (div_ne_zero h4 hθ) hr0 hs0 hrs hquart2
  obtain ⟨γ, hγ⟩ := natDegree_eq_zero.mp (hdeg huR hr hrd)
  obtain ⟨δ, hδ⟩ := natDegree_eq_zero.mp (hdeg huS hs hsd)
  subst hγ hδ
  -- conclusion
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg natDegree ea
    rwa [natDegree_C_mul h2, ← C_mul, ← C_mul, ← C_add, natDegree_C] at this
  · have := congrArg natDegree eb
    rwa [natDegree_C_mul h2, natDegree_C_mul hi0, ← C_mul, ← C_mul, ← C_sub, natDegree_C] at this
  · have := congrArg natDegree ec
    rwa [natDegree_C_mul h2, ← C_mul, ← C_mul, ← C_sub, natDegree_C] at this

/-- **Main theorem, any field with `2 ≠ 0`** (via `AlgebraicClosure K`): a cuboid with
`a ⊥ b`, `a ⊥ c`, `b ⊥ e`, `c ⊥ d` (`d² = a² + b²`, `e² = a² + c²`), `a² + b² ≠ 0` and
`b² + c² ≠ 0` has constant edges. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.natDegree_eq_zero_of_coprime (h2 : (2 : K) ≠ 0)
    {a b c : K[X]} (h : IsCuboid a b c) {d e : K[X]} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbe : IsCoprime b e) (hcd : IsCoprime c d)
    (hne_ab : a ^ 2 + b ^ 2 ≠ 0) (hne_bc : b ^ 2 + c ^ 2 ≠ 0) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  have hφ : Function.Injective φ := φ.injective
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : L) two_pos
  have h2L : (2 : L) ≠ 0 := by
    intro h0; apply h2; apply hφ; rw [map_ofNat, h0, map_zero]
  obtain ⟨g, hg'⟩ := h.sq_abc
  have hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 := by rw [hg', sq]
  have mapeq : ∀ {x y z : K[X]}, x ^ 2 + y ^ 2 = z ^ 2 →
      (x.map φ) ^ 2 + (y.map φ) ^ 2 = (z.map φ) ^ 2 := by
    intro x y z hxyz
    have := congrArg (Polynomial.map φ) hxyz
    simpa only [Polynomial.map_add, Polynomial.map_pow] using this
  have mapne : ∀ {x y : K[X]}, x ^ 2 + y ^ 2 ≠ 0 → (x.map φ) ^ 2 + (y.map φ) ^ 2 ≠ 0 := by
    intro x y hxy
    have := (Polynomial.map_ne_zero_iff hφ).mpr hxy
    simpa only [Polynomial.map_add, Polynomial.map_pow] using this
  have hf : IsSquare ((b.map φ) ^ 2 + (c.map φ) ^ 2) := by
    obtain ⟨r, hr⟩ := h.sq_bc
    exact ⟨r.map φ, by rw [← Polynomial.map_mul, ← hr]; simp only [Polynomial.map_add,
      Polynomial.map_pow]⟩
  have hgL : (a.map φ) ^ 2 + (b.map φ) ^ 2 + (c.map φ) ^ 2 = (g.map φ) ^ 2 := by
    have := congrArg (Polynomial.map φ) hg
    simpa only [Polynomial.map_add, Polynomial.map_pow] using this
  obtain ⟨ha', hb', hc'⟩ := natDegree_eq_zero_of_coprime_aux h2L hi (mapeq hd) (mapeq he) hf hgL
    ((isCoprime_map φ).mpr hab) ((isCoprime_map φ).mpr hac) ((isCoprime_map φ).mpr hbe)
    ((isCoprime_map φ).mpr hcd) (mapne hne_ab) (mapne hne_bc)
  rw [natDegree_map] at ha' hb' hc'
  exact ⟨ha', hb', hc'⟩

/-- **Symmetric corollary**: pairwise coprime edges, each coprime to its opposite face
diagonal, nondegenerate ⇒ constant edges. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.natDegree_eq_zero_of_fully_coprime
    (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsNondegCuboid a b c) {d e f : K[X]}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (_hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (_hbc : IsCoprime b c)
    (_haf : IsCoprime a f) (hbe : IsCoprime b e) (hcd : IsCoprime c d) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  h.toIsCuboid.natDegree_eq_zero_of_coprime h2 hd he hab hac hbe hcd h.ne_ab h.ne_bc

/-- In a nondegenerate cuboid with pairwise coprime edges and a non-constant edge, at most one of
the three opposite pairs `(a, f)`, `(b, e)`, `(c, d)` is coprime. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.not_two_opposite_coprime
    (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsNondegCuboid a b c) {d e f : K[X]}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    (hnc : 0 < a.natDegree ∨ 0 < b.natDegree ∨ 0 < c.natDegree) :
    ¬ (IsCoprime b e ∧ IsCoprime c d) ∧ ¬ (IsCoprime a f ∧ IsCoprime c d) ∧
      ¬ (IsCoprime a f ∧ IsCoprime b e) := by
  have hconst : a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 → False := by
    rintro ⟨h1, h2, h3⟩; omega
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hbe, hcd⟩
    exact hconst (h.toIsCuboid.natDegree_eq_zero_of_coprime h2 hd he hab hac hbe hcd
      h.ne_ab h.ne_bc)
  · rintro ⟨haf, hcd⟩
    obtain ⟨hb, ha, hc⟩ := (PolyNegOne.isCuboid_swap_ab h.toIsCuboid).natDegree_eq_zero_of_coprime
      h2 (d := d) (e := f) (by rw [← hd]; ring) hf hab.symm hbc haf hcd
      (by rw [add_comm]; exact h.ne_ab) h.ne_ac
    exact hconst ⟨ha, hb, hc⟩
  · rintro ⟨haf, hbe⟩
    obtain ⟨hc, hb, ha⟩ := (PolyNegOne.isCuboid_swap_ac h.toIsCuboid).natDegree_eq_zero_of_coprime
      h2 (d := f) (e := e) (by rw [← hf]; ring) (by rw [← he]; ring) hbc.symm hac.symm hbe haf
      (by rw [add_comm]; exact h.ne_bc) (by rw [add_comm]; exact h.ne_ab)
    exact hconst ⟨ha, hb, hc⟩

/-- **Proportional form** of `IsCuboid.natDegree_eq_zero_of_coprime`. -/
theorem _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_coprime (h2 : (2 : K) ≠ 0)
    {a b c : K[X]} (h : IsCuboid a b c) {d e : K[X]} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbe : IsCoprime b e) (hcd : IsCoprime c d)
    (hne_ab : a ^ 2 + b ^ 2 ≠ 0) (hne_bc : b ^ 2 + c ^ 2 ≠ 0) :
    Proportional a b c := by
  obtain ⟨ha, hb, hc⟩ :=
    h.natDegree_eq_zero_of_coprime h2 hd he hab hac hbe hcd hne_ab hne_bc
  obtain ⟨α, hα⟩ := natDegree_eq_zero.mp ha
  obtain ⟨β, hβ⟩ := natDegree_eq_zero.mp hb
  obtain ⟨γ, hγ⟩ := natDegree_eq_zero.mp hc
  exact ⟨1, α, β, γ, by rw [mul_one, hα], by rw [mul_one, hβ], by rw [mul_one, hγ]⟩

end PerfectCuboid.PolyEulerCoprime
