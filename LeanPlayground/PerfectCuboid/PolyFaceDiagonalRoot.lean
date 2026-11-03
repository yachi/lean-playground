module

public import Mathlib
public import LeanPlayground.PerfectCuboid.PolyCharP
public import LeanPlayground.PerfectCuboid.PolyNegOne
public import LeanPlayground.PerfectCuboid.PolyGenusOne
public import LeanPlayground.PerfectCuboid.PolyQuadraticEdge
public import LeanPlayground.PerfectCuboid.PolyLinearNondeg

/-! # A face diagonal with a single root forces proportionality (round 19, brief 3)

Cuboids over `K[X]` (`PolyCharP.IsCuboid` / `IsNondegCuboid`). Main results:

* **Lemma BF** (`not_balanced_four_term`, `[CharZero K]`): no polynomial square has exactly the
  shape `A + B X^s + C' X^(N−s) + D X^N` with `A D = B C'`, `A B C' D ≠ 0`, `0 < s`, `2s < N`.
  Proof: Lemma S (sparse square roots, `coeff_eq_zero_of_sq_sparse'`, copied from
  `PolyMonomialEdge` with the order replaced by `CharZero`) forces `s ∣ deg E = N/2 = t s`; for
  `t ≥ 3` the recursion at `(t+1)s` gives `B s (1 − 2t) lc(E) = 0`; for `t = 2`,
  `E = e₀ + e₁ X^s + e₂ X^(2s)` and the balance gives `9 (e₀ e₂)² = 0`. Characteristic `0`
  enters exactly in `(s : K) (1 − 2t) ≠ 0`, `9 ≠ 0`, `(j + 1 : K) ≠ 0` (Lemma S) and `2 ≠ 0`.
* **Headline** (`IsNondegCuboid.proportional_of_single_root_face_diag`, `[CharZero K]`): a
  nondegenerate cuboid whose face diagonal `d` (`d² = a² + b²`) is `α (X − r)^n` is
  proportional; the same for `e` (`…_face_diag_ac`) and `f` (`…_face_diag_bc`).
  Proof (after `X ↦ X + r`): if `i ∈ K` (`core`), `a ± i b` and `g ∓ c` divide `α² X^(2n)`, so
  they are monomials; either `b ∥ a`, or `c ∥ d`, or `4(a² + c²)` is a four-term square
  `u² X^(2m) + w² X^(2k) + v² X^(2m') + z² X^(2k')` with `uw = vz = α²`, `m, m' ≠ n`, which is
  excluded by `quad_disc` (equal exponents) or Lemma BF (`four_term_false`). If `−1 ∉ K²`,
  descent on `n` (`parallel_of_not_isSquare`) gives `b ∥ a`. The uniform statement is assembled
  by `by_cases IsSquare (-1 : K)`; no passage to the algebraic closure is needed.
* **Root count** (`IsNondegCuboid.proportional_of_face_diag_roots_card_le_one`,
  `[IsAlgClosed K] [CharZero K]`): a face diagonal with at most one distinct root.
* **Easy version** (`IsCuboid.proportional_of_single_root_face_diag_of_not_isSquare`): any
  field with `2 ≠ 0` and `−1 ∉ K²` (e.g. `ℚ`, `𝔽_p`, `p ≡ 3 mod 4`), no nondegeneracy.
* **Sharpness** (`isNondegCuboid_face_diag_five`, `not_proportional_face_diag_five`,
  `exists_counterexample_char_five`): over `𝔽₅`, `(3 + 3X⁶, 4 + X⁶, 2X + 3X⁵)` is a nondegenerate,
  non-proportional cuboid with `a² + b² = (X³)²`. Here `a + 2b = 1`, `a − 2b = X⁶`, and
  `4(a² + c²)` is a balanced four-term square with `N = 12`, `s = 4`, `t = 3`, where
  `3s − 2(t+1)s = −5s = 0`: Lemma BF fails in characteristic `5`. The Frobenius cuboid over `𝔽₅`
  (`X − X⁵, 2(X + X⁵), X⁶ + 1`) also has `d = X³`. Nondegeneracy is needed for the char-0
  headline when `i ∈ K`: `(X, iX, c)` has `d = 0`.

Geometric reading over `ℂ`: a nondegenerate rational curve on the Stoll–Testa cuboid surface
has every face diagonal `d` with at least two distinct affine roots; after a Möbius change of
variable sending one zero to `∞` (not formalised here) the hyperplane `{d = 0}` meets the curve
in at least three points of `ℙ¹`. The
degree is unbounded, so this is outside the degree `≤ 6` classification of Stoll–Testa; we know
of no earlier reference. NOT proved: two-root face diagonals, space diagonals with one root. -/

@[expose] public section

open Polynomial

namespace PerfectCuboid.PolyFaceDiagonalRoot

open PolyCharP

variable {K : Type*} [Field K]

/-! ## Lemma S in characteristic zero (copied from `PolyMonomialEdge`, order replaced by
`CharZero`) -/

section SparseSquares

/-- The recursion behind Lemma S (pure algebra, any field). -/
theorem sq_sparse_recursion' {F : K[X]} {c : K} {m N : ℕ} (hm : 0 < m)
    (h : ∀ j < N, (F ^ 2).coeff j = (C (F.coeff 0 ^ 2) + C c * X ^ m).coeff j)
    (j : ℕ) (hj : j + 1 < N) :
    2 * F.coeff 0 ^ 2 * ((j : K) + 1) * F.coeff (j + 1) =
      if m ≤ j + 1 then c * (3 * (m : K) - 2 * ((j : K) + 1)) * F.coeff (j + 1 - m) else 0 := by
  set a := F.coeff 0 ^ 2 with ha
  set Q : K[X] := C a + C c * X ^ m with hQ
  set G : K[X] := F ^ 2 - Q with hG
  have hGd : X ^ N ∣ G := X_pow_dvd_iff.mpr fun d hd => by
    rw [hG, coeff_sub, h d hd, sub_self]
  have hG'd : X ^ (N - 1) ∣ derivative G := pow_sub_one_dvd_derivative_of_pow_dvd hGd
  have hQ' : derivative Q = C (c * m) * X ^ (m - 1) := by
    rw [hQ, derivative_add, derivative_C, zero_add, derivative_C_mul_X_pow]
  have e1 : derivative G = 2 * F * derivative F - derivative Q := by
    rw [hG, derivative_sub, derivative_sq, map_ofNat]
  have key0 : 2 * derivative F * Q - derivative Q * F =
      derivative G * F - 2 * derivative F * G := by
    rw [e1, hG]; ring
  have key : C (2 * a) * derivative F + C (2 * c) * (derivative F * X ^ m) -
      C (c * m) * (F * X ^ (m - 1)) = derivative G * F - 2 * derivative F * G := by
    rw [← key0, hQ', hQ]
    simp only [map_mul, map_ofNat]
    ring
  have hR : (derivative G * F - 2 * derivative F * G).coeff j = 0 := by
    have hd : X ^ (N - 1) ∣ derivative G * F - 2 * derivative F * G :=
      dvd_sub (dvd_mul_of_dvd_left hG'd _)
        (dvd_mul_of_dvd_right ((pow_dvd_pow X (Nat.sub_le N 1)).trans hGd) _)
    exact X_pow_dvd_iff.mp hd j (by omega)
  rw [← key, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_mul_X_pow',
    coeff_mul_X_pow', coeff_derivative] at hR
  rcases lt_trichotomy m (j + 1) with hlt | heq | hgt
  · have h1 : m ≤ j := by omega
    have h2 : m - 1 ≤ j := by omega
    rw [ite_eq_left h1, ite_eq_left h2, coeff_derivative] at hR
    rw [ite_eq_left hlt.le]
    have e2 : j - m + 1 = j + 1 - m := by omega
    have e3 : j - (m - 1) = j + 1 - m := by omega
    rw [e2, e3] at hR
    have e4 : ((j - m : ℕ) : K) = (j : K) - m := by push_cast [Nat.cast_sub h1]; ring
    rw [e4] at hR
    linear_combination hR
  · have h1 : ¬ m ≤ j := by omega
    have h2 : m - 1 ≤ j := by omega
    rw [ite_eq_right h1, ite_eq_left h2] at hR
    rw [ite_eq_left heq.le]
    have e3 : j - (m - 1) = j + 1 - m := by omega
    rw [e3] at hR
    have e5 : (m : K) = j + 1 := by rw [heq]; push_cast; ring
    rw [e5] at hR ⊢
    linear_combination hR
  · have h1 : ¬ m ≤ j := by omega
    have h2 : ¬ m - 1 ≤ j := by omega
    rw [ite_eq_right h1, ite_eq_right h2] at hR
    rw [ite_eq_right (by omega)]
    linear_combination hR

/-- **Lemma S (a), characteristic zero.** If `F² ≡ f₀² + c X^m (mod X^N)` with
`f₀ = F.coeff 0 ≠ 0`, then below `N` the coefficients of `F` vanish off the multiples of `m`. -/
theorem coeff_eq_zero_of_sq_sparse' [CharZero K] {F : K[X]} {c : K} {m N : ℕ} (hm : 0 < m)
    (h0 : F.coeff 0 ≠ 0)
    (h : ∀ j < N, (F ^ 2).coeff j = (C (F.coeff 0 ^ 2) + C c * X ^ m).coeff j) :
    ∀ j < N, ¬ m ∣ j → F.coeff j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjN hmj
    rcases j with _ | j
    · exact absurd (dvd_zero m) hmj
    · have hrec := sq_sparse_recursion' hm h j hjN
      have hne : 2 * F.coeff 0 ^ 2 * ((j : K) + 1) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 h0))
          (by exact_mod_cast Nat.succ_ne_zero j)
      split_ifs at hrec with hmj1
      · have hdv : ¬ m ∣ j + 1 - m := by
          intro hd
          apply hmj
          have : j + 1 = (j + 1 - m) + m := by omega
          rw [this]
          exact dvd_add hd dvd_rfl
        rw [ih (j + 1 - m) (by omega) (by omega) hdv, mul_zero] at hrec
        exact (mul_eq_zero.mp hrec).resolve_left hne
      · exact (mul_eq_zero.mp hrec).resolve_left hne

end SparseSquares

/-! ## Lemma BF: balanced four-term squares -/

theorem coeff_four (A B C' D : K) (s N j : ℕ) :
    (C A + C B * X ^ s + C C' * X ^ (N - s) + C D * X ^ N).coeff j =
      (if j = 0 then A else 0) + (if j = s then B else 0) + (if j = N - s then C' else 0) +
        (if j = N then D else 0) := by
  simp only [coeff_add, coeff_C, coeff_C_mul_X_pow]

/-- **Lemma BF** (balanced four-term squares), characteristic zero: no polynomial square has
exactly the shape `A + B X^s + C' X^(N−s) + D X^N` with `A D = B C'`, all nonzero, `0 < s`,
`2 s < N`. -/
theorem not_balanced_four_term [CharZero K] {A B C' D : K} (hA : A ≠ 0) (hB : B ≠ 0)
    (hC : C' ≠ 0) (hD : D ≠ 0) (hbal : A * D = B * C') {s N : ℕ} (hs : 0 < s)
    (hsN : 2 * s < N) {E : K[X]}
    (hE : E ^ 2 = C A + C B * X ^ s + C C' * X ^ (N - s) + C D * X ^ N) : False := by
  have hc : ∀ j, (E ^ 2).coeff j = (if j = 0 then A else 0) + (if j = s then B else 0) +
      (if j = N - s then C' else 0) + (if j = N then D else 0) := by
    intro j; rw [hE, coeff_four]
  -- step 1
  have he0 : E.coeff 0 ^ 2 = A := by
    have := hc 0
    rw [sq, mul_coeff_zero, ← sq] at this
    rw [this]; simp [show (0 : ℕ) ≠ s by omega, show (0 : ℕ) ≠ N - s by omega,
      show (0 : ℕ) ≠ N by omega]
  have h0 : E.coeff 0 ≠ 0 := by
    intro h0; rw [h0] at he0; exact hA (by rw [← he0]; ring)
  have hE0 : E ≠ 0 := by rintro rfl; simp at h0
  -- step 2
  set nE := E.natDegree with hnE
  have hlc : E.coeff nE ≠ 0 := leadingCoeff_ne_zero.mpr hE0
  have hdeg : 2 * nE = N := by
    have h1 : N ≤ 2 * nE := by
      have : (E ^ 2).coeff N ≠ 0 := by
        rw [hc N]; simp [show N ≠ 0 by omega, show N ≠ s by omega, show N ≠ N - s by omega, hD]
      have := le_natDegree_of_ne_zero this
      rwa [natDegree_pow] at this
    by_contra hne
    have : (E ^ 2).coeff (2 * nE) ≠ 0 := by
      have : (E ^ 2).coeff (2 * nE) = E.leadingCoeff ^ 2 := by
        rw [← leadingCoeff_pow, leadingCoeff, natDegree_pow]
      rw [this]; exact pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hE0)
    apply this
    rw [hc]
    simp [show 2 * nE ≠ 0 by omega, show 2 * nE ≠ s by omega, show 2 * nE ≠ N - s by omega,
      hne]
  -- step 3
  have hsp : ∀ j < N - s, (E ^ 2).coeff j = (C (E.coeff 0 ^ 2) + C B * X ^ s).coeff j := by
    intro j hj
    rw [hc, he0]
    simp only [coeff_add, coeff_C, coeff_C_mul_X_pow]
    simp [show j ≠ N - s by omega, show j ≠ N by omega]
  have hzero := coeff_eq_zero_of_sq_sparse' hs h0 hsp
  -- step 4
  have hsn : s ∣ nE := by
    by_contra hnd
    exact hlc (hzero nE (by omega) hnd)
  obtain ⟨t, ht⟩ := hsn
  have ht2 : 2 ≤ t := by
    by_contra hlt
    have : t ≤ 1 := by omega
    have : s * t ≤ s * 1 := Nat.mul_le_mul_left s this
    omega
  have hsK : (s : K) ≠ 0 := by exact_mod_cast hs.ne'
  rcases Nat.lt_or_ge 2 t with ht3 | ht3
  · -- step 5: t ≥ 3
    have hts : (t + 1) * s < N - s := by
      have : (t + 2) * s < 2 * (s * t) := by nlinarith
      have : (t + 1) * s + s = (t + 2) * s := by ring
      omega
    have hpos : 1 ≤ (t + 1) * s := Nat.one_le_iff_ne_zero.mpr (by positivity)
    obtain ⟨j, hj⟩ : ∃ j, j + 1 = (t + 1) * s := ⟨(t + 1) * s - 1, by omega⟩
    have hrec := sq_sparse_recursion' hs hsp j (by omega)
    have hle : s ≤ j + 1 := by rw [hj]; nlinarith
    rw [ite_eq_left hle] at hrec
    have hjs : j + 1 - s = nE := by rw [hj, ht]; rw [add_mul, one_mul, Nat.add_sub_cancel,
      mul_comm]
    rw [hjs] at hrec
    have hcoef : E.coeff (j + 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [← hnE, hj, ht]; nlinarith
    rw [hcoef, mul_zero] at hrec
    have hjK : (j : K) + 1 = ((t : K) + 1) * s := by
      have := congrArg (Nat.cast : ℕ → K) hj; push_cast at this; exact this
    rw [hjK] at hrec
    have h12 : (1 - 2 * (t : K)) ≠ 0 := by
      intro h12
      have h7 : (2 * (t : K)) = 1 := by linear_combination -h12
      have h6 : (2 * t : ℕ) = 1 := by exact_mod_cast h7
      omega
    have : B * ((s : K) * (1 - 2 * (t : K))) * E.coeff nE = 0 := by
      rw [← hrec.symm]; ring
    exact mul_ne_zero (mul_ne_zero hB (mul_ne_zero hsK h12)) hlc this
  · -- step 6: t = 2
    have ht' : t = 2 := by omega
    subst ht'
    have hN : N = 4 * s := by omega
    have hNs : N - s = 3 * s := by omega
    have hNs4 : 4 * s - s = 3 * s := by omega
    simp only [hN, hNs4] at hc
    set e1 := E.coeff s
    set e2 := E.coeff (2 * s)
    have hEe : E = C (E.coeff 0) + C e1 * X ^ s + C e2 * X ^ (2 * s) := by
      ext j
      simp only [coeff_add, coeff_C, coeff_C_mul_X_pow]
      by_cases hj0 : j = 0
      · subst hj0; simp [show (0 : ℕ) ≠ s by omega, show (0 : ℕ) ≠ 2 * s by omega]
      by_cases hj1 : j = s
      · subst hj1; simp [show j ≠ 0 by omega, show j ≠ 2 * j by omega, e1]
      by_cases hj2 : j = 2 * s
      · subst hj2; simp [hj0, hj1, e2]
      simp only [hj0, hj1, hj2, ite_false, add_zero]
      by_cases hjb : j < 3 * s
      · apply hzero j (by omega)
        rintro ⟨q, rfl⟩
        have : q < 3 := by
          by_contra hq; simp only [not_lt] at hq; have := Nat.mul_le_mul_left s hq; omega
        interval_cases q <;> omega
      · apply coeff_eq_zero_of_natDegree_lt; omega
    have hsq : E ^ 2 = C (E.coeff 0 ^ 2) + C (2 * E.coeff 0 * e1) * X ^ s +
        C (e1 ^ 2 + 2 * E.coeff 0 * e2) * X ^ (2 * s) + C (2 * e1 * e2) * X ^ (3 * s) +
        C (e2 ^ 2) * X ^ (4 * s) := by
      conv_lhs => rw [hEe]
      simp only [map_add, map_mul, map_pow, map_ofNat]
      ring
    have hcE : ∀ j, (E ^ 2).coeff j = (if j = 0 then E.coeff 0 ^ 2 else 0) +
        (if j = s then 2 * E.coeff 0 * e1 else 0) +
        (if j = 2 * s then e1 ^ 2 + 2 * E.coeff 0 * e2 else 0) +
        (if j = 3 * s then 2 * e1 * e2 else 0) + (if j = 4 * s then e2 ^ 2 else 0) := by
      intro j; rw [hsq]; simp only [coeff_add, coeff_C, coeff_C_mul_X_pow]
    have k1 : 2 * E.coeff 0 * e1 = B := by
      have := (hcE s).symm.trans (hc s)
      simpa [show s ≠ 0 by omega, show s ≠ 2 * s by omega, show s ≠ 3 * s by omega,
        show s ≠ 4 * s by omega] using this
    have k2 : e1 ^ 2 + 2 * E.coeff 0 * e2 = 0 := by
      have := (hcE (2 * s)).symm.trans (hc (2 * s))
      simpa [show 2 * s ≠ 0 by omega, show 2 * s ≠ s by omega, show 2 * s ≠ 3 * s by omega,
        show 2 * s ≠ 4 * s by omega] using this
    have k3 : 2 * e1 * e2 = C' := by
      have := (hcE (3 * s)).symm.trans (hc (3 * s))
      simpa [show 3 * s ≠ 0 by omega, show 3 * s ≠ s by omega, show 3 * s ≠ 2 * s by omega,
        show 3 * s ≠ 4 * s by omega] using this
    have k4 : e2 ^ 2 = D := by
      have := (hcE (4 * s)).symm.trans (hc (4 * s))
      simpa [show 4 * s ≠ 0 by omega, show 4 * s ≠ s by omega, show 4 * s ≠ 2 * s by omega,
        show 4 * s ≠ 3 * s by omega] using this
    have he2 : e2 ≠ 0 := by
      have : nE = 2 * s := by rw [ht]; ring
      rw [this] at hlc; exact hlc
    subst he0 k1 k3 k4
    have h9 : (9 : K) * (E.coeff 0 * e2) ^ 2 = 0 := by
      linear_combination hbal + 4 * E.coeff 0 * e2 * k2
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero h0 he2)) h9

/-! ## Splitting a product equal to a monomial -/

theorem split_monomial {x y : K[X]} {κ : K} (hκ : κ ≠ 0) {n : ℕ} (h : x * y = C κ * X ^ n) :
    ∃ m k : ℕ, m + k = n ∧ ∃ u w : K, u * w = κ ∧ x = C u * X ^ m ∧ y = C w * X ^ k := by
  have hdvd : x ∣ X ^ n := ⟨C κ⁻¹ * y, by
    rw [show x * (C κ⁻¹ * y) = C κ⁻¹ * (x * y) by ring, h, ← mul_assoc, ← C_mul,
      inv_mul_cancel₀ hκ, C_1, one_mul]⟩
  obtain ⟨m, hm, u, hu, hx⟩ := PolyQuadraticEdge.exists_C_mul_of_dvd_prime_pow prime_X hdvd
  have hXn : (X : K[X]) ^ n = X ^ m * X ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hy := PolyQuadraticEdge.cofactor hu (pow_ne_zero m X_ne_zero) hx
    (show x * y = X ^ m * (C κ * X ^ (n - m)) by rw [h, hXn]; ring)
  refine ⟨m, n - m, by omega, u, u⁻¹ * κ, by field_simp, hx, ?_⟩
  rw [hy, C_mul]; ring

/-- If `F² = X^(2m) R` then `R` is a square. -/
theorem exists_sq_of_X_pow_mul {F R : K[X]} {m : ℕ} (h : F ^ 2 = X ^ (2 * m) * R) :
    ∃ G : K[X], G ^ 2 = R := by
  have hd : (X ^ m : K[X]) ^ 2 ∣ F ^ 2 := ⟨R, by rw [h, ← pow_mul, mul_comm m 2]⟩
  obtain ⟨G, rfl⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp hd
  refine ⟨G, ?_⟩
  have hX : (X ^ m : K[X]) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ X_ne_zero)
  apply mul_left_cancel₀ hX
  rw [← mul_pow, h, ← pow_mul, mul_comm m 2]

/-! ## The four-term square coming from `a² + c²` -/

/-- The square `4(a² + c²)` produced by the core argument: two "dual pairs" of monomials with
exponents `2m, 2k` (`m + k = 2n`, `m ≠ n`) and coefficients `u², w²` (`u w = α²`), and the same for
`(m', k', v, z)`. In characteristic zero it is never a nonzero square. -/
theorem four_term_false [CharZero K] {α : K} (hα : α ≠ 0) {n m k m' k' : ℕ}
    (hmk : m + k = 2 * n) (hmk' : m' + k' = 2 * n) (hm : m ≠ n) (hm' : m' ≠ n)
    {u w v z : K} (huw : u * w = α ^ 2) (hvz : v * z = α ^ 2) {F : K[X]} (hF : F ≠ 0)
    (h : F ^ 2 = C (u ^ 2) * X ^ (2 * m) + C (w ^ 2) * X ^ (2 * k) + C (v ^ 2) * X ^ (2 * m') +
      C (z ^ 2) * X ^ (2 * k')) : False := by
  wlog hlt : m < n generalizing m k u w
  · exact this (m := k) (k := m) (u := w) (w := u) (by omega) (by omega) (by rwa [mul_comm])
      (by rw [h]; ring) (by omega)
  wlog hlt' : m' < n generalizing m' k' v z
  · exact this (m' := k') (k' := m') (v := z) (z := v) (by omega) (by omega) (by rwa [mul_comm])
      (by rw [h]; ring) (by omega)
  wlog hle : m ≤ m' generalizing m k u w m' k' v z
  · exact this (m := m') (k := k') (u := v) (w := z) (m' := m) (k' := k) (v := u) (z := w)
      hmk' hm' hvz hlt' hmk hm huw (by rw [h]; ring) hlt (by omega)
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα
  have hu : u ≠ 0 := by rintro rfl; apply hα2; rw [← huw, zero_mul]
  have hw : w ≠ 0 := by rintro rfl; apply hα2; rw [← huw, mul_zero]
  have hv : v ≠ 0 := by rintro rfl; apply hα2; rw [← hvz, zero_mul]
  have hz : z ≠ 0 := by rintro rfl; apply hα2; rw [← hvz, mul_zero]
  rcases eq_or_lt_of_le hle with heq | hlt2
  · subst heq
    have hk : k' = k := by omega
    subst hk
    have e1 : 2 * k' = 2 * m + 2 * (2 * n - 2 * m) := by omega
    rw [e1, pow_add] at h
    obtain ⟨G, hG⟩ := exists_sq_of_X_pow_mul (m := m) (F := F)
      (R := C (u ^ 2 + v ^ 2) + C (w ^ 2 + z ^ 2) * X ^ (2 * (2 * n - 2 * m)))
      (by rw [h, C_add, C_add]; ring)
    have hrel : (w ^ 2 + z ^ 2) * (u ^ 2 * v ^ 2) = (α ^ 2) ^ 2 * (u ^ 2 + v ^ 2) := by
      linear_combination (u * w + α ^ 2) * v ^ 2 * huw + (v * z + α ^ 2) * u ^ 2 * hvz
    by_cases h0 : u ^ 2 + v ^ 2 = 0
    · have h0' : w ^ 2 + z ^ 2 = 0 := by
        rw [h0, mul_zero] at hrel
        exact (mul_eq_zero.mp hrel).resolve_right
          (mul_ne_zero (pow_ne_zero 2 hu) (pow_ne_zero 2 hv))
      apply hF
      have : F ^ 2 = 0 := by
        rw [h, show C (u ^ 2) * X ^ (2 * m) + C (w ^ 2) * (X ^ (2 * m) * X ^ (2 * (2 * n - 2 * m)))
          + C (v ^ 2) * X ^ (2 * m) + C (z ^ 2) * (X ^ (2 * m) * X ^ (2 * (2 * n - 2 * m))) =
          C (u ^ 2 + v ^ 2) * X ^ (2 * m) + C (w ^ 2 + z ^ 2) *
            (X ^ (2 * m) * X ^ (2 * (2 * n - 2 * m))) by rw [C_add, C_add]; ring, h0, h0']
        simp
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    · have h0' : w ^ 2 + z ^ 2 ≠ 0 := by
        intro h0'
        rw [h0', zero_mul] at hrel
        exact h0 ((mul_eq_zero.mp hrel.symm).resolve_left (pow_ne_zero 2 hα2))
      have hq := PolyNegOne.quad_disc (two_ne_zero) (n := 2 * n - 2 * m) (A := w ^ 2 + z ^ 2)
        (B := 0) (D := u ^ 2 + v ^ 2) (F := G) (by omega) h0' (by rw [hG]; simp; ring)
      have : (4 : K) * (w ^ 2 + z ^ 2) * (u ^ 2 + v ^ 2) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) h0') h0
      exact this (by rw [← hq]; ring)
  · set s := 2 * m' - 2 * m with hs
    set N := 4 * n - 4 * m with hN
    have e1 : 2 * m' = 2 * m + s := by omega
    have e2 : 2 * k' = 2 * m + (N - s) := by omega
    have e3 : 2 * k = 2 * m + N := by omega
    rw [e1, e2, e3, pow_add, pow_add, pow_add] at h
    obtain ⟨G, hG⟩ := exists_sq_of_X_pow_mul (m := m) (F := F)
      (R := C (u ^ 2) + C (v ^ 2) * X ^ s + C (z ^ 2) * X ^ (N - s) + C (w ^ 2) * X ^ N)
      (by rw [h]; ring)
    exact not_balanced_four_term (pow_ne_zero 2 hu) (pow_ne_zero 2 hv) (pow_ne_zero 2 hz)
      (pow_ne_zero 2 hw) (by linear_combination (u * w + v * z) * (huw - hvz)) (by omega)
      (by omega) hG

/-! ## The core argument over a field containing `i` -/

/-- **Core lemma** (`i² = −1`, characteristic zero): if the face diagonal of `a, b` is
`α X^n`, then `b ∥ a` or `c ∥ d`. -/
theorem core [CharZero K] {i : K} (hi : i ^ 2 = -1) {a b c : K[X]} (h : IsNondegCuboid a b c)
    {α : K} (hα : α ≠ 0) {n : ℕ} (hd : a ^ 2 + b ^ 2 = (C α * X ^ n) ^ 2) :
    (∃ μ : K, b = C μ * a) ∨ (∃ μ : K, c = C μ * (C α * X ^ n)) := by
  have hCi : (C i : K[X]) ^ 2 = -1 := C_sq_eq_neg_one hi
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have h2P : (2 : K[X]) ≠ 0 := PolyQuadraticEdge.two_ne_zero_poly h2
  obtain ⟨m, k, hmk, u, w, huw, hab1, hab2⟩ := split_monomial hα2 (x := a + C i * b)
    (y := a - C i * b) (n := 2 * n) (by rw [C_pow]; linear_combination hd - b ^ 2 * hCi)
  obtain ⟨g, hg⟩ := h.sq_abc
  obtain ⟨m', k', hmk', v, z, hvz, hgc1, hgc2⟩ := split_monomial hα2 (x := g - c)
    (y := g + c) (n := 2 * n) (by rw [C_pow]; linear_combination -hg + hd)
  have h2a : 2 * a = C u * X ^ m + C w * X ^ k := by linear_combination hab1 + hab2
  have h2ib : 2 * (C i * b) = C u * X ^ m - C w * X ^ k := by linear_combination hab1 - hab2
  have h2b : 2 * b = -C i * (C u * X ^ m - C w * X ^ k) := by
    linear_combination 2 * b * hCi - C i * h2ib
  have h2c : 2 * c = C z * X ^ k' - C v * X ^ m' := by linear_combination hgc2 - hgc1
  by_cases hmn : m = n
  · left
    have hkn : k = n := by omega
    rw [hmn, hkn] at h2a h2b
    have huw0 : u + w ≠ 0 := by
      intro h0
      apply h.ne_a
      have : 2 * a = C (u + w) * X ^ n := by rw [h2a, C_add]; ring
      rw [h0, C_0, zero_mul] at this
      exact (mul_eq_zero.mp this).resolve_left h2P
    refine ⟨-i * (u - w) / (u + w), ?_⟩
    have hc0 : (C (2 * (u + w)) : K[X]) ≠ 0 := C_ne_zero.mpr (mul_ne_zero h2 huw0)
    apply mul_left_cancel₀ hc0
    have e : 2 * (u + w) * (-i * (u - w) / (u + w)) = -i * (u - w) * 2 := by
      field_simp
    rw [← mul_assoc, ← C_mul, e]
    simp only [C_mul, C_add, C_sub, C_neg, map_ofNat]
    linear_combination (C u + C w) * h2b + C i * (C u - C w) * h2a
  by_cases hmn' : m' = n
  · right
    have hkn : k' = n := by omega
    subst hmn' hkn
    refine ⟨(z - v) / α / 2, PolyQuadraticEdge.eq_C_mul_of_two_mul h2 ?_⟩
    rw [h2c, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hα, C_sub]; ring
  · exfalso
    obtain ⟨e, he⟩ := h.sq_ac
    have hF : (2 * e : K[X]) ≠ 0 := by
      refine mul_ne_zero h2P ?_
      rintro rfl; apply h.ne_ac; rw [he, mul_zero]
    have hX1 : (X : K[X]) ^ m * X ^ k = X ^ (2 * n) := by rw [← pow_add, hmk]
    have hX2 : (X : K[X]) ^ m' * X ^ k' = X ^ (2 * n) := by rw [← pow_add, hmk']
    have hC1 : C u * C w = C (α ^ 2) := by rw [← C_mul, huw]
    have hC2 : C v * C z = C (α ^ 2) := by rw [← C_mul, hvz]
    refine four_term_false hα hmk hmk' hmn hmn' huw hvz hF ?_
    simp only [C_pow, pow_mul]
    linear_combination -4 * he + (2 * a + C u * X ^ m + C w * X ^ k) * h2a +
      (2 * c + C z * X ^ k' - C v * X ^ m') * h2c + 2 * X ^ m * X ^ k * hC1 +
      2 * C (α ^ 2) * hX1 - 2 * X ^ m' * X ^ k' * hC2 - 2 * C (α ^ 2) * hX2

/-! ## The case `−1 ∉ K²` (any field) -/

/-- If `−1` is not a square, `a² + b² = (α X^n)²` forces `b ∥ a`. -/
theorem parallel_of_not_isSquare (hK : ¬ IsSquare (-1 : K)) {α : K} (n : ℕ) :
    ∀ {a b : K[X]}, a ≠ 0 → a ^ 2 + b ^ 2 = (C α * X ^ n) ^ 2 → ∃ μ : K, b = C μ * a := by
  induction n with
  | zero =>
    intro a b ha hd
    by_cases hb : b = 0
    · exact ⟨0, by rw [hb, C_0, zero_mul]⟩
    have hdeg := PolyNegOne.natDegree_sq_add_sq hK ha hb
    rw [hd, pow_zero, mul_one, ← C_pow, natDegree_C] at hdeg
    have ha0 : a.natDegree = 0 := by omega
    have hb0 : b.natDegree = 0 := by omega
    rw [natDegree_eq_zero] at ha0 hb0
    obtain ⟨x, rfl⟩ := ha0
    obtain ⟨y, rfl⟩ := hb0
    have hx : x ≠ 0 := by rintro rfl; exact ha C_0
    exact ⟨y / x, by rw [← C_mul, div_mul_cancel₀ _ hx]⟩
  | succ n ih =>
    intro a b ha hd
    have h0 : a.eval 0 ^ 2 + b.eval 0 ^ 2 = 0 := by
      have := congrArg (eval 0) hd
      simpa using this
    have hb0 : b.eval 0 = 0 := by
      by_contra hb0
      apply hK
      exact ⟨a.eval 0 / b.eval 0, by field_simp; linear_combination -h0⟩
    have ha0 : a.eval 0 = 0 := by
      rw [hb0] at h0; exact pow_eq_zero_iff two_ne_zero |>.mp (by simpa using h0)
    obtain ⟨a', rfl⟩ : X ∣ a := by rw [X_dvd_iff, coeff_zero_eq_eval_zero]; exact ha0
    obtain ⟨b', rfl⟩ : X ∣ b := by rw [X_dvd_iff, coeff_zero_eq_eval_zero]; exact hb0
    have ha' : a' ≠ 0 := by rintro rfl; exact ha (mul_zero _)
    have hd' : a' ^ 2 + b' ^ 2 = (C α * X ^ n) ^ 2 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero : (X : K[X]) ≠ 0))
      linear_combination hd
    obtain ⟨μ, hμ⟩ := ih ha' hd'
    exact ⟨μ, by rw [hμ]; ring⟩

/-! ## Permutations -/

theorem isNondegCuboid_swap_ab {a b c : K[X]} (h : IsNondegCuboid a b c) :
    IsNondegCuboid b a c :=
  ⟨PolyNegOne.isCuboid_swap_ab h.toIsCuboid, by rw [add_comm]; exact h.ne_ab, h.ne_bc, h.ne_ac,
    by rw [add_comm (b ^ 2)]; exact h.ne_abc⟩

theorem isNondegCuboid_swap_bc {a b c : K[X]} (h : IsNondegCuboid a b c) :
    IsNondegCuboid a c b :=
  ⟨PolyNegOne.isCuboid_swap_bc h.toIsCuboid, h.ne_ac, h.ne_ab, by rw [add_comm]; exact h.ne_bc,
    by rw [add_right_comm]; exact h.ne_abc⟩

/-! ## Headline theorems -/

/-- Over a field of characteristic zero containing `i`, a face diagonal `α X^n` forces
proportionality. -/
theorem proportional_of_monomial_face_diag_of_sq [CharZero K] {i : K} (hi : i ^ 2 = -1)
    {a b c : K[X]} (h : IsNondegCuboid a b c) {α : K} (hα : α ≠ 0) {n : ℕ}
    (hd : a ^ 2 + b ^ 2 = (C α * X ^ n) ^ 2) : Proportional a b c := by
  rcases core hi h hα hd with hb | ⟨μ, hμ⟩
  · exact h.toIsCuboid.proportional_of_two_edges two_ne_zero (Or.inl hb)
  · have hμ0 : μ ≠ 0 := by rintro rfl; apply h.ne_c; rw [hμ, C_0, zero_mul]
    have hd' : a ^ 2 + b ^ 2 = (C μ⁻¹ * c) ^ 2 := by
      rw [hd, hμ, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hμ0, C_1, one_mul]
    obtain ⟨q, x, y, z, h1, h2, h3⟩ :=
      (isNondegCuboid_swap_ab (isNondegCuboid_swap_bc h)).proportional_of_opp_diag_eq_edge
        two_ne_zero hd'
    exact ⟨q, y, z, x, h2, h3, h1⟩

/-- Monomial face diagonal, characteristic zero (no hypothesis on `−1`). -/
theorem proportional_of_monomial_face_diag [CharZero K] {a b c : K[X]} (h : IsNondegCuboid a b c)
    {α : K} (hα : α ≠ 0) {n : ℕ} (hd : a ^ 2 + b ^ 2 = (C α * X ^ n) ^ 2) :
    Proportional a b c := by
  by_cases hK : IsSquare (-1 : K)
  · obtain ⟨i, hi⟩ := hK
    exact proportional_of_monomial_face_diag_of_sq (i := i) (by rw [hi]; ring) h hα hd
  · obtain ⟨μ, hμ⟩ := parallel_of_not_isSquare hK n h.ne_a hd
    exact h.toIsCuboid.proportional_of_two_edges two_ne_zero (Or.inl ⟨μ, hμ⟩)

theorem sq_comp_X_add_C {a b : K[X]} {α r : K} {n : ℕ}
    (hd : a ^ 2 + b ^ 2 = (C α * (X - C r) ^ n) ^ 2) :
    (a.comp (X + C r)) ^ 2 + (b.comp (X + C r)) ^ 2 = (C α * X ^ n) ^ 2 := by
  have := congrArg (fun p => p.comp (X + C r)) hd
  simpa [add_comp, pow_comp, mul_comp, sub_comp] using this

theorem proportional_of_comp {a b c : K[X]} (r : K)
    (h : Proportional (a.comp (X + C r)) (b.comp (X + C r)) (c.comp (X + C r))) :
    Proportional a b c := by
  have := PolyQuadraticEdge.proportional_comp h (X - C r)
  simpa only [PolyNegOne.comp_X_add_C_comp_X_sub_C] using this

/-- **Headline.** A nondegenerate cuboid over a field of characteristic `0` whose face diagonal
`d` (`d² = a² + b²`) is `α (X − r)^n` is proportional. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_single_root_face_diag
    [CharZero K] {a b c : K[X]} (h : IsNondegCuboid a b c) {α r : K} (hα : α ≠ 0) {n : ℕ}
    (hd : a ^ 2 + b ^ 2 = (C α * (X - C r) ^ n) ^ 2) : Proportional a b c :=
  proportional_of_comp r (proportional_of_monomial_face_diag
    (PolyLinearNondeg.isNondegCuboid_comp_X_add_C h r) hα (sq_comp_X_add_C hd))

/-- The same for the face diagonal `e` (`e² = a² + c²`). -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_single_root_face_diag_ac
    [CharZero K] {a b c : K[X]} (h : IsNondegCuboid a b c) {α r : K} (hα : α ≠ 0) {n : ℕ}
    (he : a ^ 2 + c ^ 2 = (C α * (X - C r) ^ n) ^ 2) : Proportional a b c := by
  obtain ⟨q, x, y, z, h1, h2, h3⟩ :=
    (isNondegCuboid_swap_bc h).proportional_of_single_root_face_diag hα he
  exact ⟨q, x, z, y, h1, h3, h2⟩

/-- The same for the face diagonal `f` (`f² = b² + c²`). -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_single_root_face_diag_bc
    [CharZero K] {a b c : K[X]} (h : IsNondegCuboid a b c) {α r : K} (hα : α ≠ 0) {n : ℕ}
    (hf : b ^ 2 + c ^ 2 = (C α * (X - C r) ^ n) ^ 2) : Proportional a b c := by
  obtain ⟨q, x, y, z, h1, h2, h3⟩ :=
    (isNondegCuboid_swap_bc (isNondegCuboid_swap_ab h)).proportional_of_single_root_face_diag
      hα hf
  exact ⟨q, z, x, y, h3, h1, h2⟩

/-- **Easy version**, any field with `2 ≠ 0` in which `−1` is not a square; no nondegeneracy
needed (and `α ≠ 0` is not used: `a ≠ 0` already forces `α ≠ 0`). -/
theorem
    _root_.PerfectCuboid.PolyCharP.IsCuboid.proportional_of_single_root_face_diag_of_not_isSquare
    (hK : ¬ IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {a b c : K[X]} (h : IsCuboid a b c) {α r : K}
    (_hα : α ≠ 0) {n : ℕ} (hd : a ^ 2 + b ^ 2 = (C α * (X - C r) ^ n) ^ 2) :
    Proportional a b c := by
  have h' := PolyNegOne.isCuboid_comp_X_add_C h r
  obtain ⟨μ, hμ⟩ := parallel_of_not_isSquare hK n h'.ne_a (sq_comp_X_add_C hd)
  exact proportional_of_comp r (h'.proportional_of_two_edges h2 (Or.inl ⟨μ, hμ⟩))

/-- Over an algebraically closed field, a nonzero polynomial with at most one distinct root is
`α (X − r)^n`. -/
theorem exists_eq_C_mul_X_sub_C_pow [IsAlgClosed K] [DecidableEq K] {d : K[X]} (hd : d ≠ 0)
    (hroots : d.roots.toFinset.card ≤ 1) :
    ∃ α r : K, α ≠ 0 ∧ ∃ n : ℕ, d = C α * (X - C r) ^ n := by
  have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := d))
  have hlc : d.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd
  rcases Multiset.empty_or_exists_mem d.roots with h0 | ⟨r, hr⟩
  · refine ⟨d.leadingCoeff, 0, hlc, 0, ?_⟩
    rw [h0] at hsplit
    simpa using hsplit.symm
  · have hall : ∀ x ∈ d.roots, x = r := fun x hx =>
      Finset.card_le_one.mp hroots x (Multiset.mem_toFinset.mpr hx) r
        (Multiset.mem_toFinset.mpr hr)
    refine ⟨d.leadingCoeff, r, hlc, Multiset.card d.roots, ?_⟩
    rw [Multiset.eq_replicate_of_mem hall, Multiset.map_replicate, Multiset.prod_replicate]
      at hsplit
    exact hsplit.symm

/-- **Over algebraically closed fields of characteristic 0**: a face diagonal with at most one
distinct root forces proportionality. -/
theorem _root_.PerfectCuboid.PolyCharP.IsNondegCuboid.proportional_of_face_diag_roots_card_le_one
    [IsAlgClosed K] [CharZero K] [DecidableEq K] {a b c d : K[X]} (h : IsNondegCuboid a b c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (hroots : d.roots.toFinset.card ≤ 1) : Proportional a b c := by
  have hd0 : d ≠ 0 := by rintro rfl; apply h.ne_ab; rw [hd]; ring
  obtain ⟨α, r, hα, n, rfl⟩ := exists_eq_C_mul_X_sub_C_pow hd0 hroots
  exact h.proportional_of_single_root_face_diag hα hd

/-! ## Characteristic `0` is necessary: a face diagonal `X³` over `𝔽₅` -/

section FiveExample

local instance fact_prime_five_fd : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem five_eq_zero_fd : (5 : (ZMod 5)[X]) = 0 := by
  have : ((5 : ℕ) : (ZMod 5)[X]) = 0 := CharP.cast_eq_zero _ 5
  exact_mod_cast this

theorem face_diag_five :
    (3 + 3 * X ^ 6 : (ZMod 5)[X]) ^ 2 + (4 + X ^ 6) ^ 2 = (X ^ 3) ^ 2 := by
  linear_combination (5 + 5 * X ^ 6 + 2 * X ^ 12) * five_eq_zero_fd

/-- **The `𝔽₅` face-diagonal cuboid** (planner, round 19): `(3 + 3X⁶, 4 + X⁶, 2X + 3X⁵)` is a
nondegenerate cuboid over `𝔽₅[X]` with face diagonal `d = X³` (one root), `e = 2 + X² + X⁴ + 2X⁶`,
`f = 4 + 3X² + 2X⁴ + X⁶`, `g = 2X + 2X⁵`. -/
theorem isNondegCuboid_face_diag_five :
    IsNondegCuboid (3 + 3 * X ^ 6 : (ZMod 5)[X]) (4 + X ^ 6) (2 * X + 3 * X ^ 5) := by
  have he : (3 + 3 * X ^ 6 : (ZMod 5)[X]) ^ 2 + (2 * X + 3 * X ^ 5) ^ 2 =
      (2 + X ^ 2 + X ^ 4 + 2 * X ^ 6) ^ 2 := by
    linear_combination (1 - X ^ 4 + 4 * X ^ 6 - X ^ 8 + X ^ 10 + X ^ 12) * five_eq_zero_fd
  have hf : (4 + X ^ 6 : (ZMod 5)[X]) ^ 2 + (2 * X + 3 * X ^ 5) ^ 2 =
      (4 + 3 * X ^ 2 + 2 * X ^ 4 + X ^ 6) ^ 2 := by
    linear_combination (-4 * X ^ 2 - 5 * X ^ 4 - 2 * X ^ 8 + X ^ 10) * five_eq_zero_fd
  have hg : (3 + 3 * X ^ 6 : (ZMod 5)[X]) ^ 2 + (4 + X ^ 6) ^ 2 + (2 * X + 3 * X ^ 5) ^ 2 =
      (2 * X + 2 * X ^ 5) ^ 2 := by
    linear_combination (5 + 6 * X ^ 6 + X ^ 10 + 2 * X ^ 12) * five_eq_zero_fd
  have nz : ∀ {q : (ZMod 5)[X]} (x : ZMod 5), q.eval x ≠ 0 → q ≠ 0 := by
    intro q x h; rintro rfl; simp at h
  have n1 : (X ^ 3 : (ZMod 5)[X]) ≠ 0 := pow_ne_zero 3 X_ne_zero
  have n2 : (2 + X ^ 2 + X ^ 4 + 2 * X ^ 6 : (ZMod 5)[X]) ≠ 0 := nz 0 (by simp; decide)
  have n3 : (4 + 3 * X ^ 2 + 2 * X ^ 4 + X ^ 6 : (ZMod 5)[X]) ≠ 0 := nz 0 (by simp; decide)
  have n4 : (2 * X + 2 * X ^ 5 : (ZMod 5)[X]) ≠ 0 := nz 1 (by simp; decide)
  exact
  { ne_a := nz 0 (by simp; decide)
    ne_b := nz 0 (by simp; decide)
    ne_c := by
      intro h; have := congrArg (coeff · 1) h
      simp [coeff_X, coeff_X_pow] at this
      exact absurd this (by decide)
    sq_ab := ⟨X ^ 3, by rw [face_diag_five]; ring⟩
    sq_ac := ⟨2 + X ^ 2 + X ^ 4 + 2 * X ^ 6, by rw [he]; ring⟩
    sq_bc := ⟨4 + 3 * X ^ 2 + 2 * X ^ 4 + X ^ 6, by rw [hf]; ring⟩
    sq_abc := ⟨2 * X + 2 * X ^ 5, by rw [hg]; ring⟩
    ne_ab := by rw [face_diag_five]; exact pow_ne_zero 2 n1
    ne_ac := by rw [he]; exact pow_ne_zero 2 n2
    ne_bc := by rw [hf]; exact pow_ne_zero 2 n3
    ne_abc := by rw [hg]; exact pow_ne_zero 2 n4 }

theorem not_proportional_face_diag_five :
    ¬ Proportional (3 + 3 * X ^ 6 : (ZMod 5)[X]) (4 + X ^ 6) (2 * X + 3 * X ^ 5) := by
  intro hp
  have := hp.natDegree_eq_ac isNondegCuboid_face_diag_five.ne_a isNondegCuboid_face_diag_five.ne_c
  have h1 : (3 + 3 * X ^ 6 : (ZMod 5)[X]).natDegree = 6 := by compute_degree!
  have h2 : (2 * X + 3 * X ^ 5 : (ZMod 5)[X]).natDegree = 5 := by compute_degree!
  rw [h1, h2] at this; omega

/-- **Characteristic `0` cannot be dropped** from
`IsNondegCuboid.proportional_of_single_root_face_diag`: over `𝔽₅` there is a nondegenerate,
non-proportional cuboid whose face diagonal `d` is `X³`. -/
theorem exists_counterexample_char_five :
    ∃ a b c : (ZMod 5)[X], IsNondegCuboid a b c ∧ a ^ 2 + b ^ 2 = (C 1 * (X - C 0) ^ 3) ^ 2 ∧
      ¬ Proportional a b c :=
  ⟨_, _, _, isNondegCuboid_face_diag_five, by rw [face_diag_five]; simp,
    not_proportional_face_diag_five⟩

end FiveExample

end PerfectCuboid.PolyFaceDiagonalRoot
