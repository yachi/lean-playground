module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even

public section

/-!
# The center of a Clifford algebra (characteristic not 2)

Chris Peters and Hans Sterk, *On the center of the Clifford Algebra*, arXiv:2610.23323
(2026-10-16), Proposition 1.1. Let `(V, q)` be a quadratic space over a field `k` of
characteristic not 2 with an orthogonal basis `e₁, …, eₙ` and `q(eᵢ) ≠ 0`, and let
`e = e₁ ⋯ eₙ`. Then

* the centralizer of the even part `C₀(q)` in `C(q)` is `k + k e`: `centralizer_even`;
* the center of `C(q)` is `k` for `n` even (`center_eq_bot`) and `k + k e` for `n` odd
  (`center_eq_span`);
* the center of `C₀(q)` is `k` for `n` odd (`center_even_eq_bot`) and `k + k e` for `n` even
  (`center_even_eq_span`).

## The proof

The paper writes `u = ∑ a_J e_J` and compares `eᵢeⱼ u` with `u eᵢeⱼ`. Here we only use that
the monomials `e_J` span `C(q)` (`span_eJ`), not that they are linearly independent.

Each `e_J` commutes with `eᵢeⱼ` up to a sign `sᵢ(J) sⱼ(J)` (`ι_mul_ι_mul_eJ`), where
`sᵢ(J) = ±1` is the sign that `eᵢ` picks up when it is moved past `e_J`. The averaging map
`Aᵢⱼ x = (x + (eᵢeⱼ) x (eᵢeⱼ)⁻¹) / 2` (`avg`) fixes every `u` that commutes with `eᵢeⱼ`, and it
sends `e_J` to `(1 + sᵢ(J) sⱼ(J))/2 • e_J`, which is `0` when exactly one of `i, j` is in `J`
(`sgn_mul_sgn_of_mem_of_not_mem`). Composing all the `Aᵢⱼ`, `i ≠ j`, gives a map that fixes such
a `u` and kills every `e_J` except `e_∅ = 1` and `e_{1,…,n} = e`: `mem_span_of_commute`.
-/

namespace CliffordCenter

open CliffordAlgebra

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (Q : QuadraticForm k V)
  {n : ℕ} (v : Fin n → V)

/-- The product of the factors `eₐ` for `a ∈ J`, taken in the order of the list `l`. -/
noncomputable def mono (l : List (Fin n)) (J : Finset (Fin n)) : CliffordAlgebra Q :=
  (l.map fun a => if a ∈ J then ι Q (v a) else 1).prod

/-- The monomial `e_J = e_{j₁} ⋯ e_{jᵣ}` for `J = {j₁ < ⋯ < jᵣ}`. -/
noncomputable def eJ (J : Finset (Fin n)) : CliffordAlgebra Q :=
  mono Q v (List.finRange n) J

/-- The "volume element" `e = e₁ ⋯ eₙ`. -/
noncomputable def vol : CliffordAlgebra Q :=
  eJ Q v Finset.univ

/-- The sign that `eᵢ` picks up when it is moved past the factors of `l` that lie in `J`. -/
def sgnL (l : List (Fin n)) (J : Finset (Fin n)) (i : Fin n) : k :=
  (l.map fun a => if a ∈ J ∧ a ≠ i then (-1 : k) else 1).prod

/-- The sign `sᵢ(J)` with `eᵢ e_J = sᵢ(J) e_J eᵢ`. -/
def sgn (J : Finset (Fin n)) (i : Fin n) : k :=
  ∏ a, if a ∈ J ∧ a ≠ i then (-1 : k) else 1

lemma sgnL_finRange (J : Finset (Fin n)) (i : Fin n) :
    sgnL (k := k) (List.finRange n) J i = sgn J i := by
  rw [sgnL, sgn, Fin.prod_univ_def]

lemma mono_congr {l : List (Fin n)} {J K : Finset (Fin n)} (h : ∀ a ∈ l, (a ∈ J ↔ a ∈ K)) :
    mono Q v l J = mono Q v l K := by
  unfold mono
  congr 1
  refine List.map_congr_left fun a ha => ?_
  simp only [h a ha]

@[simp] lemma eJ_empty : eJ Q v ∅ = 1 := by
  simp [eJ, mono]

lemma vol_eq : vol Q v = ((List.finRange n).map fun a => ι Q (v a)).prod := by
  simp [vol, eJ, mono]

/-- The averaging map `x ↦ (x + (eᵢeⱼ) x (eᵢeⱼ)⁻¹) / 2`, using
`(eᵢeⱼ)⁻¹ = -(q(eᵢ) q(eⱼ))⁻¹ eᵢeⱼ`. -/
noncomputable def avg (i j : Fin n) : Module.End k (CliffordAlgebra Q) :=
  (2 : k)⁻¹ • (LinearMap.id + (-(Q (v i) * Q (v j)))⁻¹ •
    (LinearMap.mulLeft k (ι Q (v i) * ι Q (v j)) ∘ₗ LinearMap.mulRight k (ι Q (v i) * ι Q (v j))))

lemma sgn_mul_self (J : Finset (Fin n)) (i : Fin n) : sgn (k := k) J i * sgn J i = 1 := by
  rw [sgn, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun a _ => by split_ifs <;> norm_num

/-- If exactly one of `i, j` lies in `J`, then `eᵢeⱼ` anticommutes with `e_J`. -/
lemma sgn_mul_sgn_of_mem_of_not_mem {J : Finset (Fin n)} {i j : Fin n} (hi : i ∈ J)
    (hj : j ∉ J) : sgn (k := k) J i * sgn J j = -1 := by
  have key : ∀ a, (if a ∈ J ∧ a ≠ j then (-1 : k) else 1) =
      (if a = i then -1 else 1) * (if a ∈ J ∧ a ≠ i then -1 else 1) := by
    intro a
    rcases eq_or_ne a i with rfl | hai
    · have : a ≠ j := fun h => hj (h ▸ hi)
      simp [hi, this]
    · rcases eq_or_ne a j with rfl | haj
      · simp [hj, hai]
      · simp [hai, haj]
  have : sgn (k := k) J j = -sgn J i := by
    rw [sgn, sgn, Finset.prod_congr rfl fun a _ => key a, Finset.prod_mul_distrib]
    simp
  rw [this, mul_neg, sgn_mul_self]

lemma sgn_univ (i : Fin n) : sgn (k := k) Finset.univ i = (-1) ^ (n + 1) := by
  have key : ∀ a, (if a ∈ Finset.univ ∧ a ≠ i then (-1 : k) else 1) =
      (-1) * (if a = i then -1 else 1) := by
    intro a
    rcases eq_or_ne a i with rfl | hai <;> simp [*]
  rw [sgn, Finset.prod_congr rfl fun a _ => key a, Finset.prod_mul_distrib]
  simp [pow_succ]

variable {Q v}
variable (hv : ∀ i j, i ≠ j → Q.IsOrtho (v i) (v j))
include hv

/-- Moving `eᵢ` past a product of basis vectors. -/
theorem ι_mul_mono (i : Fin n) (J : Finset (Fin n)) (l : List (Fin n)) :
    ι Q (v i) * mono Q v l J = sgnL (k := k) l J i • (mono Q v l J * ι Q (v i)) := by
  induction l with
  | nil => simp [mono, sgnL]
  | cons a t ih =>
    simp only [mono, sgnL, List.map_cons, List.prod_cons] at ih ⊢
    by_cases ha : a ∈ J
    · by_cases hai : a = i
      · subst hai
        simp only [ha, ne_eq, not_true_eq_false, and_false, ite_false, ite_true, one_mul]
        conv_lhs => rw [ih]
        rw [mul_smul_comm, ← mul_assoc]
      · simp only [ha, ne_eq, hai, not_false_eq_true, and_self, ite_true]
        rw [← mul_assoc, ι_mul_ι_comm_of_isOrtho (hv i a (Ne.symm hai)), neg_mul, mul_assoc,
          ih, mul_smul_comm, neg_one_mul, neg_smul, ← mul_assoc]
    · simp only [ha, false_and, ite_false, one_mul]
      exact ih

theorem ι_mul_eJ (i : Fin n) (J : Finset (Fin n)) :
    ι Q (v i) * eJ Q v J = sgn (k := k) J i • (eJ Q v J * ι Q (v i)) := by
  rw [eJ, ι_mul_mono hv, sgnL_finRange]

/-- `eᵢeⱼ` commutes with `e_J` up to the sign `sᵢ(J) sⱼ(J)`. -/
theorem ι_mul_ι_mul_eJ (i j : Fin n) (J : Finset (Fin n)) :
    ι Q (v i) * ι Q (v j) * eJ Q v J =
      (sgn (k := k) J i * sgn J j) • (eJ Q v J * (ι Q (v i) * ι Q (v j))) := by
  rw [mul_assoc, ι_mul_eJ hv, mul_smul_comm, ← mul_assoc, ι_mul_eJ hv, smul_mul_assoc, smul_smul,
    mul_assoc, mul_comm (sgn J j)]

/-- Left multiplication by `eᵢ` sends a monomial to a nonzero multiple of a monomial. -/
theorem ι_mul_mono_symmDiff (i : Fin n) (J : Finset (Fin n)) {l : List (Fin n)} (hl : l.Nodup)
    (hi : i ∈ l) : ∃ c : k, ι Q (v i) * mono Q v l J = c • mono Q v l (symmDiff J {i}) := by
  induction l with
  | nil => simp at hi
  | cons a t ih =>
    simp only [List.nodup_cons] at hl
    simp only [mono, List.map_cons, List.prod_cons]
    by_cases hai : a = i
    · subst hai
      have ht : mono Q v t J = mono Q v t (symmDiff J {a}) :=
        mono_congr Q v fun b hb => by
          have : b ≠ a := fun h => hl.1 (h ▸ hb)
          simp [Finset.mem_symmDiff, this]
      simp only [mono] at ht
      rw [ht]
      by_cases ha : a ∈ J
      · refine ⟨Q (v a), ?_⟩
        simp only [ha, ite_true, Finset.mem_symmDiff, Finset.mem_singleton, not_true_eq_false,
          and_false, or_false, ite_false, one_mul]
        rw [← mul_assoc, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      · refine ⟨1, ?_⟩
        simp [ha, Finset.mem_symmDiff]
    · have hit : i ∈ t := by
        rcases List.mem_cons.1 hi with h | h
        · exact absurd h.symm hai
        · exact h
      obtain ⟨c, hc⟩ := ih hl.2 hit
      simp only [mono] at hc
      have hmem : (a ∈ symmDiff J {i}) ↔ a ∈ J := by simp [Finset.mem_symmDiff, hai]
      simp only [hmem]
      by_cases ha : a ∈ J
      · refine ⟨-c, ?_⟩
        simp only [ha, ite_true]
        rw [← mul_assoc, ι_mul_ι_comm_of_isOrtho (hv i a (Ne.symm hai)), neg_mul, mul_assoc, hc,
          mul_smul_comm, neg_smul]
      · refine ⟨c, ?_⟩
        simp only [ha, ite_false, one_mul]
        exact hc

theorem ι_mul_eJ_mem_span (i : Fin n) (J : Finset (Fin n)) :
    ι Q (v i) * eJ Q v J ∈ Submodule.span k (Set.range (eJ Q v)) := by
  obtain ⟨c, hc⟩ := ι_mul_mono_symmDiff hv i J (List.nodup_finRange n) (List.mem_finRange i)
  rw [eJ, hc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

omit hv in
/-- Every element of `C(q)` is a linear combination of the monomials `e_J`. -/
theorem span_eJ (b : Module.Basis (Fin n) k V) (hv : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) :
    Submodule.span k (Set.range (eJ Q b)) = ⊤ := by
  set M := Submodule.span k (Set.range (eJ Q b))
  have hmul : ∀ i, ∀ x ∈ M, ι Q (b i) * x ∈ M := by
    intro i x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨J, rfl⟩ := hx
      exact ι_mul_eJ_mem_span hv i J
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact M.add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact M.smul_mem c hx
  refine eq_top_iff.2 fun x _ => ?_
  clear ‹x ∈ ⊤›
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, ← eJ_empty Q b]
    exact M.smul_mem r (Submodule.subset_span ⟨_, rfl⟩)
  | add x y hx hy => exact M.add_mem hx hy
  | ι_mul x m hx =>
    rw [← b.sum_repr m, map_sum, Finset.sum_mul]
    refine M.sum_mem fun i _ => ?_
    rw [map_smul, smul_mul_assoc]
    exact M.smul_mem _ (hmul i x hx)

/-- `(eᵢeⱼ)² = -q(eᵢ) q(eⱼ)`. -/
theorem pair_mul_self {i j : Fin n} (hij : i ≠ j) :
    ι Q (v i) * ι Q (v j) * (ι Q (v i) * ι Q (v j)) =
      algebraMap k _ (-(Q (v i) * Q (v j))) := by
  calc _ = -(ι Q (v i) * ι Q (v i) * (ι Q (v j) * ι Q (v j))) := by
        rw [mul_assoc, ← mul_assoc (ι Q (v j)), ι_mul_ι_comm_of_isOrtho (hv j i hij.symm)]
        simp only [neg_mul, mul_neg, mul_assoc]
    _ = _ := by rw [ι_sq_scalar, ι_sq_scalar, ← map_mul, ← map_neg]

/-- If `eᵢeⱼ x = t x eᵢeⱼ`, then the averaging map multiplies `x` by `(1 + t)/2`. -/
theorem avg_apply_of (hQ : ∀ i, Q (v i) ≠ 0) {i j : Fin n} (hij : i ≠ j)
    {x : CliffordAlgebra Q} {t : k} (hx : ι Q (v i) * ι Q (v j) * x = t • (x * (ι Q (v i) * ι Q (v j)))) :
    avg Q v i j x = ((1 + t) / 2) • x := by
  simp only [avg, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  rw [← mul_assoc, hx, smul_mul_assoc, mul_assoc, pair_mul_self hv hij, ← Algebra.commutes,
    ← Algebra.smul_def, smul_smul, smul_smul]
  have hq : Q (v i) * Q (v j) ≠ 0 := mul_ne_zero (hQ i) (hQ j)
  have : (-(Q (v i) * Q (v j)))⁻¹ * t * -(Q (v i) * Q (v j)) = t := by
    rw [mul_comm _ t, mul_assoc, inv_mul_cancel₀ (neg_ne_zero.2 hq), mul_one]
  rw [this]
  module

/-- The composite of averaging maps over a list of pairs `(i, j)`, `i ≠ j`. -/
theorem prod_avg_apply_of_commute (hQ : ∀ i, Q (v i) ≠ 0) (h2 : (2 : k) ≠ 0)
    {u : CliffordAlgebra Q}
    (hu : ∀ i j, i ≠ j → ι Q (v i) * ι Q (v j) * u = u * (ι Q (v i) * ι Q (v j)))
    (L : List (Fin n × Fin n)) (hL : ∀ p ∈ L, p.1 ≠ p.2) :
    (L.map fun p => avg Q v p.1 p.2).prod u = u := by
  induction L with
  | nil => simp
  | cons p t ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      ih fun q hq => hL q (List.mem_cons_of_mem _ hq)]
    have hp := hL p List.mem_cons_self
    have hx : ι Q (v p.1) * ι Q (v p.2) * u = (1 : k) • (u * (ι Q (v p.1) * ι Q (v p.2))) := by
      rw [one_smul]; exact hu _ _ hp
    rw [avg_apply_of hv hQ hp hx, one_add_one_eq_two, div_self h2, one_smul]

theorem prod_avg_eJ (hQ : ∀ i, Q (v i) ≠ 0) (J : Finset (Fin n))
    (L : List (Fin n × Fin n)) (hL : ∀ p ∈ L, p.1 ≠ p.2) :
    (L.map fun p => avg Q v p.1 p.2).prod (eJ Q v J) =
      (L.map fun p => (1 + sgn (k := k) J p.1 * sgn J p.2) / 2).prod • eJ Q v J := by
  induction L with
  | nil => simp
  | cons p t ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      ih fun q hq => hL q (List.mem_cons_of_mem _ hq), map_smul,
      avg_apply_of hv hQ (hL p List.mem_cons_self) (ι_mul_ι_mul_eJ hv _ _ J), smul_smul,
      List.map_cons, List.prod_cons, mul_comm]

omit hv in
/-- The heart of Proposition 1.1: an element that commutes with every `eᵢeⱼ` is in `k + k e`. -/
theorem mem_span_of_commute (b : Module.Basis (Fin n) k V)
    (hv : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) (hQ : ∀ i, Q (b i) ≠ 0) (h2 : (2 : k) ≠ 0)
    {u : CliffordAlgebra Q}
    (hu : ∀ i j, i ≠ j → ι Q (b i) * ι Q (b j) * u = u * (ι Q (b i) * ι Q (b j))) :
    u ∈ Submodule.span k {1, vol Q b} := by
  have hu' : u ∈ Submodule.span k (Set.range (eJ Q b)) := span_eJ b hv ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hu'
  set L := (Finset.univ : Finset (Fin n)).offDiag.toList
  have hL : ∀ p ∈ L, p.1 ≠ p.2 := fun p hp => (Finset.mem_offDiag.1 (Finset.mem_toList.1 hp)).2.2
  rw [← prod_avg_apply_of_commute hv hQ h2 hu L hL, ← hc, map_sum]
  refine Submodule.sum_mem _ fun J _ => ?_
  rw [map_smul, prod_avg_eJ hv hQ J L hL]
  by_cases hJ0 : J = ∅
  · subst hJ0
    rw [eJ_empty]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_insert _ _)))
  by_cases hJ1 : J = Finset.univ
  · subst hJ1
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hJ0
  obtain ⟨j, hj⟩ : ∃ j, j ∉ J := by simpa [Finset.eq_univ_iff_forall] using hJ1
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  have h0 : (L.map fun p => (1 + sgn (k := k) J p.1 * sgn J p.2) / 2).prod = 0 := by
    refine List.prod_eq_zero (List.mem_map.2 ⟨(i, j), ?_, ?_⟩)
    · exact Finset.mem_toList.2 (Finset.mem_offDiag.2 ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩)
    · simp [sgn_mul_sgn_of_mem_of_not_mem hi hj]
  rw [h0, zero_smul, smul_zero]
  exact Submodule.zero_mem _

/-! ### The volume element `e` -/

omit hv in
/-- `e ∈ C₀(q)` for `n` even and `e ∈ C₁(q)` for `n` odd. -/
theorem vol_mem_evenOdd : vol Q v ∈ evenOdd Q (n : ZMod 2) := by
  rw [vol_eq]
  convert SetLike.list_prod_map_mem_graded (A := evenOdd Q) (List.finRange n) (fun _ => 1)
    (fun a => ι Q (v a)) fun a _ => ι_mem_evenOdd_one Q (v a)
  simp

omit hv in
theorem involute_vol : involute (vol Q v) = (-1 : k) ^ n • vol Q v := by
  rw [vol_eq, map_list_prod, List.map_map]
  have : (involute ∘ fun a => ι Q (v a)) = Neg.neg ∘ fun a => ι Q (v a) := by
    ext a; simp
  rw [this, ← List.map_map, List.prod_map_neg, List.length_map, List.length_finRange,
    Algebra.smul_def, map_pow, map_neg, map_one]

omit hv in
theorem isUnit_ι (hQ : ∀ i, Q (v i) ≠ 0) (a : Fin n) : IsUnit (ι Q (v a)) := by
  refine ⟨⟨_, (Q (v a))⁻¹ • ι Q (v a), ?_, ?_⟩, rfl⟩ <;>
  simp only [mul_smul_comm, smul_mul_assoc] <;>
  rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_smul,
    inv_mul_cancel₀ (hQ a), one_smul]

omit hv in
theorem isUnit_vol (hQ : ∀ i, Q (v i) ≠ 0) : IsUnit (vol Q v) := by
  rw [vol_eq]
  refine List.prod_isUnit fun x hx => ?_
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  exact isUnit_ι hQ a

theorem ι_mul_vol (i : Fin n) :
    ι Q (v i) * vol Q v = (-1 : k) ^ (n + 1) • (vol Q v * ι Q (v i)) := by
  rw [vol, ι_mul_eJ hv, sgn_univ]

omit hv in
theorem ι_mul_vol' (b : Module.Basis (Fin n) k V) (hv : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j))
    (m : V) : ι Q m * vol Q b = (-1 : k) ^ (n + 1) • (vol Q b * ι Q m) := by
  rw [← b.sum_repr m]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ι_mul_vol hv, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

omit hv in
/-- For `n` odd, `e` is central. -/
theorem mul_vol_of_odd (b : Module.Basis (Fin n) k V)
    (hv : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) (hn : Odd n) (x : CliffordAlgebra Q) :
    x * vol Q b = vol Q b * x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact Algebra.commutes r _
  | ι m => rw [ι_mul_vol' b hv, (hn.add_one).neg_one_pow, one_smul]
  | mul x y hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]

omit hv in
/-- For `n` even, `x e = e α(x)`, with `α` the grade involution. -/
theorem mul_vol_of_even (b : Module.Basis (Fin n) k V)
    (hv : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) (hn : Even n) (x : CliffordAlgebra Q) :
    x * vol Q b = vol Q b * involute x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r _
  | ι m => rw [ι_mul_vol' b hv, (hn.add_one).neg_one_pow, neg_one_smul, involute_ι, mul_neg]
  | mul x y hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc, map_mul]
  | add x y hx hy => rw [add_mul, hx, hy, map_add, mul_add]

omit hv in
theorem mul_vol_of_mem_even (b : Module.Basis (Fin n) k V)
    (hv : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q 0) :
    x * vol Q b = vol Q b * x := by
  rcases Nat.even_or_odd n with hn | hn
  · rw [mul_vol_of_even b hv hn, involute_eq_of_mem_even hx]
  · exact mul_vol_of_odd b hv hn x

/-! ### Proposition 1.1 -/

omit hv in
theorem ι_mul_ι_mem_even (m₁ m₂ : V) : ι Q m₁ * ι Q m₂ ∈ even Q := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
  exact ι_mul_ι_mem_evenOdd_zero Q _ _

omit hv in
/-- If `-(d • w) = d • w` for a unit `w`, then `d = 0`. -/
theorem eq_zero_of_neg_smul_eq {w : CliffordAlgebra Q} (hw : IsUnit w) {d : k}
    (h2 : (2 : k) ≠ 0) (h : -(d • w) = d • w) : d = 0 := by
  have : Invertible (2 : k) := invertibleOfNonzero h2
  have h' : (2 : k) • d • w = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel _
  rcases smul_eq_zero.1 h' with h'' | h''
  · exact absurd h'' h2
  · exact (smul_eq_zero.1 h'').resolve_right hw.ne_zero

variable (b : Module.Basis (Fin n) k V) (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j))
  (hQ : ∀ i, Q (b i) ≠ 0) (h2 : (2 : k) ≠ 0)
include hb hQ h2

omit hv in
/-- The centralizer of the even Clifford algebra `C₀(q)` in `C(q)` is `k + k e`. -/
theorem centralizer_even :
    Subalgebra.toSubmodule (Subalgebra.centralizer k (even Q : Set (CliffordAlgebra Q))) =
      Submodule.span k {1, vol Q b} := by
  ext u
  rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h
    exact mem_span_of_commute b hb hQ h2 fun i j _ => h _ (ι_mul_ι_mem_even _ _)
  · intro h g hg
    have hg' : g ∈ evenOdd Q 0 := by rwa [← even_toSubmodule]
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 h
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul,
      mul_vol_of_mem_even b hb hg']

omit hv in
/-- Proposition 1.1 a), `n` even: the center of `C(q)` is `k`. -/
theorem center_eq_bot (hn : Even n) : Subalgebra.center k (CliffordAlgebra Q) = ⊥ := by
  have : Invertible (2 : k) := invertibleOfNonzero h2
  refine eq_bot_iff.2 fun x hx => ?_
  rw [Subalgebra.mem_center_iff] at hx
  have hx' : x ∈ Subalgebra.toSubmodule (Subalgebra.centralizer k (even Q : Set _)) :=
    (Subalgebra.mem_centralizer_iff k).2 fun g _ => hx g
  rw [centralizer_even b hb hQ h2] at hx'
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hx'
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · refine Algebra.mem_bot.2 ⟨c + d, ?_⟩
    simp [vol_eq, Algebra.algebraMap_eq_smul_one, add_smul]
  have h := hx (ι Q (b ⟨0, hpos⟩))
  rw [mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_one,
    one_mul, ι_mul_vol hb, (hn.add_one).neg_one_pow, neg_one_smul, smul_neg, add_right_inj] at h
  rw [eq_zero_of_neg_smul_eq ((isUnit_vol hQ).mul (isUnit_ι hQ _)) h2 h, zero_smul, add_zero]
  exact Algebra.mem_bot.2 ⟨c, Algebra.algebraMap_eq_smul_one c⟩

omit hv in
/-- Proposition 1.1 a), `n` odd: the center of `C(q)` is `k + k e`. -/
theorem center_eq_span (hn : Odd n) :
    Subalgebra.toSubmodule (Subalgebra.center k (CliffordAlgebra Q)) =
      Submodule.span k {1, vol Q b} := by
  ext x
  rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_center_iff]
  constructor
  · intro hx
    rw [← centralizer_even b hb hQ h2]
    exact (Subalgebra.mem_centralizer_iff k).2 fun g _ => hx g
  · intro h g
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 h
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul,
      mul_vol_of_odd b hb hn]

omit hv in
/-- An element of the center of `C₀(q)` lies in `k + k e`. -/
theorem mem_span_of_mem_center_even {x : even Q} (hx : x ∈ Subalgebra.center k (even Q)) :
    (x : CliffordAlgebra Q) ∈ Submodule.span k {1, vol Q b} := by
  rw [← centralizer_even b hb hQ h2, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
  intro g hg
  exact congrArg Subtype.val (Subalgebra.mem_center_iff.1 hx ⟨g, hg⟩)

omit hv in
/-- Proposition 1.1 b), `n` odd: the center of `C₀(q)` is `k`. -/
theorem center_even_eq_bot (hn : Odd n) : Subalgebra.center k (even Q) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.1 (mem_span_of_mem_center_even b hb hQ h2 hx)
  have hinv : involute (x : CliffordAlgebra Q) = x :=
    involute_eq_of_mem_even (by rw [← even_toSubmodule]; exact x.2)
  rw [← hcd, map_add, map_smul, map_smul, map_one, involute_vol, hn.neg_one_pow, neg_one_smul,
    smul_neg, add_right_inj] at hinv
  rw [eq_zero_of_neg_smul_eq (isUnit_vol hQ) h2 hinv, zero_smul, add_zero] at hcd
  refine Algebra.mem_bot.2 ⟨c, Subtype.ext ?_⟩
  rw [← hcd, Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one]

omit hv hb hQ h2 in
/-- For `n` even, `e ∈ C₀(q)`. -/
theorem vol_mem_even (hn : Even n) : vol Q b ∈ even Q := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
  simpa [hn.natCast_zmod_two] using vol_mem_evenOdd (Q := Q) (v := b)

omit hv in
/-- Proposition 1.1 b), `n` even: the center of `C₀(q)` is `k + k e` (and `e ∈ C₀(q)` by
`vol_mem_even`). The statement holds for every `n`; for `n` odd it says the same as
`center_even_eq_bot`, because then `(k + k e) ∩ C₀(q) = k`. -/
theorem mem_center_even_iff (x : even Q) :
    x ∈ Subalgebra.center k (even Q) ↔ (x : CliffordAlgebra Q) ∈ Submodule.span k {1, vol Q b} := by
  refine ⟨mem_span_of_mem_center_even b hb hQ h2, fun h => ?_⟩
  rw [← centralizer_even b hb hQ h2, Subalgebra.mem_toSubmodule,
    Subalgebra.mem_centralizer_iff] at h
  exact Subalgebra.mem_center_iff.2 fun g => Subtype.ext (h g g.2)

end CliffordCenter
