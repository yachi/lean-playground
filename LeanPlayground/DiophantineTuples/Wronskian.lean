module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public noncomputable section

/-!
# The Wronskian of `m` polynomials

For `g : Fin m → R[X]` let `W(g) = det (g_j^{(i)})_{0 ≤ i, j < m}` (`wronskianN`). Mathlib has the
Wronskian of two polynomials (used for Mason–Stothers); this file treats `m` of them, as needed for
the Vaserstein–Wheland generalization of Mason–Stothers.

* `wronskianN_comb`: replacing `g` by `F`-linear combinations `gP` multiplies `W` by `det P`.
* `wronskianN_ne_zero_of_natDegree_injective`: in characteristic `0`, if the `g j` are nonzero
  with pairwise distinct degrees `d j`, the coefficient of `X^(∑ d j - ∑ i)` in `W(g)` is
  `∏ lc(g j) · ∏_{i < j} (d j - d i) ≠ 0`.
* `wronskianN_ne_zero_of_linearIndependent`: in characteristic `0`, linearly independent
  polynomials have nonzero Wronskian (their span has a basis of distinct degrees).
-/

namespace DiophantineTuples

open Polynomial Matrix Finset

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The Wronskian matrix `(g_j^{(i)})_{i, j}`. -/
def wronskianMatrix (g : Fin m → R[X]) : Matrix (Fin m) (Fin m) R[X] :=
  Matrix.of fun i j => derivative^[i] (g j)

/-- The Wronskian `W(g) = det (g_j^{(i)})` of `m` polynomials. -/
def wronskianN (g : Fin m → R[X]) : R[X] := (wronskianMatrix g).det

lemma wronskianMatrix_comb (g : Fin m → R[X]) (P : Matrix (Fin m) (Fin m) R) :
    wronskianMatrix (fun j => ∑ l, C (P l j) * g l) = wronskianMatrix g * P.map C := by
  refine Matrix.ext fun i j => ?_
  simp only [wronskianMatrix, of_apply, Matrix.mul_apply, map_apply, iterate_derivative_sum,
    iterate_derivative_C_mul]
  exact sum_congr rfl fun l _ => by ring

/-- Linear combinations with constant coefficients multiply the Wronskian by the determinant. -/
theorem wronskianN_comb (g : Fin m → R[X]) (P : Matrix (Fin m) (Fin m) R) :
    wronskianN (fun j => ∑ l, C (P l j) * g l) = wronskianN g * C P.det := by
  rw [wronskianN, wronskianMatrix_comb, det_mul, wronskianN, RingHom.map_det]
  rfl

lemma coeff_mul_of_natDegree_le' {p q : R[X]} {a b : ℕ} (hp : p.natDegree ≤ a)
    (hq : q.natDegree ≤ b) : (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  rw [coeff_mul, Finset.sum_eq_single (a, b)]
  · rintro ⟨i, j⟩ hij hne
    rw [mem_antidiagonal] at hij
    rcases lt_or_ge a i with h | h
    · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt h), zero_mul]
    · have : b < j := by
        by_contra! h'
        exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
      rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt this), mul_zero]
  · intro h; exact absurd (mem_antidiagonal.mpr (rfl : a + b = a + b)) h

lemma coeff_prod_of_natDegree_le' {ι : Type*} (s : Finset ι) (f : ι → R[X]) (n : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ n i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, n i) = ∏ i ∈ s, (f i).coeff (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, prod_insert ha,
      coeff_mul_of_natDegree_le' (h a (mem_insert_self _ _)), ih fun i hi => h i
        (mem_insert_of_mem hi)]
    refine (natDegree_prod_le _ _).trans (sum_le_sum fun i hi => h i (mem_insert_of_mem hi))

lemma coeff_iterate_derivative_natDegree_sub (p : R[X]) (i : ℕ) :
    (derivative^[i] p).coeff (p.natDegree - i) =
      ((p.natDegree.descFactorial i : ℕ) : R) * p.leadingCoeff := by
  by_cases hi : i ≤ p.natDegree
  · rw [coeff_iterate_derivative, Nat.sub_add_cancel hi, nsmul_eq_mul]; rfl
  · rw [iterate_derivative_eq_zero (by omega), Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

lemma natDegree_iterate_derivative_le_sub (p : R[X]) (i : ℕ) :
    (derivative^[i] p).natDegree ≤ p.natDegree - i :=
  natDegree_iterate_derivative p i

section CharZero

variable [IsDomain R] [CharZero R]

/-- In characteristic `0`, nonzero polynomials with pairwise distinct degrees have a nonzero
Wronskian. -/
theorem wronskianN_ne_zero_of_natDegree_injective (g : Fin m → R[X]) (hg : ∀ j, g j ≠ 0)
    (hinj : Function.Injective fun j => (g j).natDegree) : wronskianN g ≠ 0 := by
  classical
  set d : Fin m → ℕ := fun j => (g j).natDegree
  set N : Matrix (Fin m) (Fin m) R :=
    Matrix.of fun i j => (((d j).descFactorial i : ℕ) : R) * (g j).leadingCoeff
  -- the coefficient of `X ^ (∑ d - ∑ i)` in `W(g)` is `det N`
  have key : ∀ σ : Equiv.Perm (Fin m),
      (∏ j, derivative^[σ j] (g j)).coeff (∑ j, d j - ∑ i : Fin m, (i : ℕ)) =
        ∏ j, N (σ j) j := by
    intro σ
    by_cases hle : ∀ j, (σ j : ℕ) ≤ d j
    · have hsum : ∑ j, d j - ∑ i : Fin m, (i : ℕ) = ∑ j, (d j - σ j) := by
        have h1 : ∑ j, ((d j - σ j : ℕ) + σ j) = ∑ j, d j :=
          sum_congr rfl fun j _ => Nat.sub_add_cancel (hle j)
        have h2 : ∑ j : Fin m, ((σ j : Fin m) : ℕ) = ∑ i : Fin m, (i : ℕ) :=
          Equiv.sum_comp σ (fun i => (i : ℕ))
        rw [← h1, sum_add_distrib, h2, Nat.add_sub_cancel]
      rw [hsum, coeff_prod_of_natDegree_le' _ _ _ fun j _ =>
        natDegree_iterate_derivative_le_sub _ _]
      exact prod_congr rfl fun j _ => coeff_iterate_derivative_natDegree_sub _ _
    · push Not at hle
      obtain ⟨j, hj⟩ := hle
      have h0 : derivative^[σ j] (g j) = 0 := iterate_derivative_eq_zero hj
      rw [prod_eq_zero (mem_univ j) h0, coeff_zero]
      refine (prod_eq_zero (mem_univ j) ?_).symm
      simp [N, d, Nat.descFactorial_eq_zero_iff_lt.mpr hj]
  have hcoeff : (wronskianN g).coeff (∑ j, d j - ∑ i : Fin m, (i : ℕ)) = N.det := by
    rw [wronskianN, det_apply, finsetSum_coeff, det_apply]
    refine sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, Units.smul_def, coeff_smul]
    congr 1
    exact key σ
  -- `det N = (∏ lc) · det (descFactorial) ≠ 0`
  have hN : N.det ≠ 0 := by
    have hfac : N = Matrix.of fun (i j : Fin m) => (g j).leadingCoeff *
        (((d j).descFactorial i : ℕ) : R) := by
      ext i j; simp [N, mul_comm]
    have hrow := det_mul_row (fun j => (g j).leadingCoeff)
      (Matrix.of fun i j : Fin m => (((d j).descFactorial i : ℕ) : R))
    simp only [of_apply] at hrow
    rw [hfac, hrow]
    refine mul_ne_zero (prod_ne_zero_iff.mpr fun j _ => leadingCoeff_ne_zero.mpr (hg j)) ?_
    have hV := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun j => ((d j : ℕ) : R)) (fun i => descPochhammer R i)
      (fun i => descPochhammer_natDegree R i) (fun i => monic_descPochhammer R i)
    have hT : (Matrix.of fun i j : Fin m => (((d j).descFactorial i : ℕ) : R)) =
        (Matrix.of fun i j : Fin m => (descPochhammer R j).eval ((d i : ℕ) : R))ᵀ := by
      ext i j; simp [descPochhammer_eval_eq_descFactorial]
    rw [hT, det_transpose, ← hV]
    exact det_vandermonde_ne_zero_iff.mpr fun a b h => hinj (by exact_mod_cast h)
  intro hW
  apply hN
  rw [← hcoeff, hW, coeff_zero]

end CharZero

section Field

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
/-- The span of `m` linearly independent polynomials contains `m` nonzero polynomials of pairwise
distinct degrees. -/
lemma exists_distinct_natDegree_of_linearIndependent {g : Fin m → F[X]}
    (hg : LinearIndependent F g) :
    ∃ f : Fin m → F[X], (∀ j, f j ∈ Submodule.span F (Set.range g)) ∧ (∀ j, f j ≠ 0) ∧
      Function.Injective fun j => (f j).natDegree := by
  classical
  set V := Submodule.span F (Set.range g)
  set B : ℕ := univ.sup fun j => (g j).natDegree
  have hVle : ∀ f ∈ V, f.natDegree ≤ B := by
    intro f hf
    have : V ≤ degreeLE F B := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, mem_degreeLE]
      exact degree_le_of_natDegree_le (le_sup (f := fun j => (g j).natDegree) (mem_univ j))
    exact natDegree_le_iff_degree_le.mpr (mem_degreeLE.mp (this hf))
  set S : Finset ℕ := (range (B + 1)).filter fun e => ∃ f ∈ V, f ≠ 0 ∧ f.natDegree = e
  -- coefficients at the degrees in `S` determine an element of `V`
  let φ : V →ₗ[F] (S → F) := LinearMap.pi fun e => (lcoeff F e.1).comp V.subtype
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro ⟨f, hf⟩ h0
    by_contra hne
    have hf0 : f ≠ 0 := fun h => hne (by simp [h])
    have hS : f.natDegree ∈ S := mem_filter.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le (hVle f hf)), f, hf, hf0, rfl⟩
    have := congrFun (LinearMap.mem_ker.mp h0) ⟨_, hS⟩
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply, lcoeff_apply,
      Pi.zero_apply] at this
    exact leadingCoeff_ne_zero.mpr hf0 this
  have hcard : m ≤ S.card := by
    have h1 := LinearMap.finrank_le_finrank_of_injective hφ
    rw [finrank_span_eq_card hg, Fintype.card_fin, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe] at h1
    exact h1
  -- pick `m` degrees in `S` and witnesses
  let e : Fin m ↪ S := (Fin.castLEEmb hcard).trans S.equivFin.symm.toEmbedding
  have hw : ∀ s : S, ∃ f ∈ V, f ≠ 0 ∧ f.natDegree = s.1 := fun s => (mem_filter.mp s.2).2
  choose f hfV hf0 hfd using hw
  refine ⟨fun j => f (e j), fun j => hfV _, fun j => hf0 _, fun a b h => e.injective ?_⟩
  simp only [hfd] at h
  exact Subtype.ext h

/-- **Linearly independent polynomials have a nonzero Wronskian** (characteristic `0`). -/
theorem wronskianN_ne_zero_of_linearIndependent {g : Fin m → F[X]}
    (hg : LinearIndependent F g) : wronskianN g ≠ 0 := by
  obtain ⟨f, hfV, hf0, hinj⟩ := exists_distinct_natDegree_of_linearIndependent hg
  have hc : ∀ j, ∃ c : Fin m → F, ∑ l, c l • g l = f j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun F).mp (hfV j)
  choose c hc using hc
  have hfeq : f = fun j => ∑ l, C ((Matrix.of fun l j => c j l) l j) * g l := by
    funext j; rw [← hc j]; simp [smul_eq_C_mul]
  have hWf := wronskianN_ne_zero_of_natDegree_injective f hf0 hinj
  rw [hfeq, wronskianN_comb] at hWf
  exact left_ne_zero_of_mul hWf

end Field

end DiophantineTuples
