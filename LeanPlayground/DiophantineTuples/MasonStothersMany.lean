module

public import LeanPlayground.DiophantineTuples.Wronskian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

@[expose] public noncomputable section

/-!
# Mason–Stothers for `m + 1` terms (Wronskian form)

Let `F` be algebraically closed of characteristic `0` and `y₀ + y₁ + ⋯ + y_m = 0` with all
`yⱼ ≠ 0`, no common root, and `y₁, …, y_m` linearly independent over `F`. Then for every `l`
(`natDegree_add_le_mul_card_roots`)

  `deg y_l + m(m-1)/2 ≤ (m - 1) · ∑ⱼ ν(yⱼ)`,

where `ν(y)` is the number of distinct roots of `y`. This is the classical Wronskian proof
(Brownawell–Masser, Voloch; the crude form of Vaserstein–Wheland, Theorem 2.2(a), as used in
Tsang–Yip, arXiv:2607.01165, Lemma 4.1):
* every `m` of the `yⱼ` have Wronskians that are constant multiples of each other;
* at a root `α`, dropping a `yⱼ` with `yⱼ(α) ≠ 0`, the Wronskian vanishes to order at least
  `∑ⱼ (ord_α yⱼ - (m - 1))` (`pow_dvd_wronskianN`);
* `deg W ≤ ∑ deg - m(m-1)/2` (`natDegree_wronskianN_add_le`).
-/

namespace DiophantineTuples

open Polynomial Finset

section CommRing

variable {R : Type*} [CommRing R] {m : ℕ}

/-- If `q ^ v j ∣ g j` then `q ^ ∑ (v j - (m - 1))` divides the Wronskian. -/
lemma pow_dvd_wronskianN {g : Fin m → R[X]} {q : R[X]} {v : Fin m → ℕ}
    (h : ∀ j, q ^ v j ∣ g j) : q ^ (∑ j, (v j - (m - 1))) ∣ wronskianN g := by
  rw [wronskianN, Matrix.det_apply]
  refine dvd_sum fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine dvd_mul_of_dvd_right ?_ _
  rw [← prod_pow_eq_pow_sum]
  refine prod_dvd_prod_of_dvd _ _ fun j _ => ?_
  simp only [wronskianMatrix, Matrix.of_apply]
  have := (σ j).isLt
  exact (pow_dvd_pow q (by omega : v j - (m - 1) ≤ v j - ((σ j : Fin m) : ℕ))).trans
    (pow_sub_dvd_iterate_derivative_of_pow_dvd _ (h j))

/-- `deg W(g) + m(m-1)/2 ≤ ∑ deg gⱼ` when `W(g) ≠ 0`. -/
lemma natDegree_wronskianN_add_le {g : Fin m → R[X]} (hW : wronskianN g ≠ 0) :
    (wronskianN g).natDegree + ∑ i : Fin m, (i : ℕ) ≤ ∑ j, (g j).natDegree := by
  classical
  have hterm : ∀ σ : Equiv.Perm (Fin m), (∏ j, derivative^[σ j] (g j)) ≠ 0 →
      ∀ j, ((σ j : Fin m) : ℕ) ≤ (g j).natDegree := by
    intro σ hσ j
    by_contra! h
    exact hσ (prod_eq_zero (mem_univ j) (iterate_derivative_eq_zero h))
  have hsum : ∀ σ : Equiv.Perm (Fin m), ∑ j, ((σ j : Fin m) : ℕ) = ∑ i : Fin m, (i : ℕ) :=
    fun σ => Equiv.sum_comp σ (fun i : Fin m => (i : ℕ))
  have hbound : ∀ σ : Equiv.Perm (Fin m),
      (Equiv.Perm.sign σ • ∏ j, (wronskianMatrix g) (σ j) j).natDegree ≤
        ∑ j, (g j).natDegree - ∑ i : Fin m, (i : ℕ) := by
    intro σ
    simp only [wronskianMatrix, Matrix.of_apply]
    by_cases h0 : (∏ j, derivative^[σ j] (g j)) = 0
    · simp [h0]
    · have hle := hterm σ h0
      rw [Units.smul_def, zsmul_eq_mul]
      refine natDegree_mul_le.trans ?_
      rw [natDegree_intCast, zero_add]
      refine (natDegree_prod_le _ _).trans ?_
      calc ∑ j, (derivative^[σ j] (g j)).natDegree ≤ ∑ j, ((g j).natDegree - ((σ j : Fin m) : ℕ)) :=
            sum_le_sum fun j _ => natDegree_iterate_derivative _ _
        _ = ∑ j, (g j).natDegree - ∑ i : Fin m, (i : ℕ) := by
          rw [← hsum σ, sum_tsub_distrib _ fun j _ => hle j]
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin m), (∏ j, derivative^[σ j] (g j)) ≠ 0 := by
    by_contra! h
    apply hW
    rw [wronskianN, Matrix.det_apply]
    exact sum_eq_zero fun σ _ => by simp [wronskianMatrix, h σ]
  have hSum0 : ∑ i : Fin m, (i : ℕ) ≤ ∑ j, (g j).natDegree :=
    hsum σ ▸ sum_le_sum fun j _ => hterm σ hσ j
  have := natDegree_sum_le_of_forall_le (s := univ) _ fun σ _ => hbound σ
  rw [wronskianN, Matrix.det_apply]
  omega

end CommRing

lemma sum_count_le_card {α : Type*} [DecidableEq α] (S : Finset α) (M : Multiset α) :
    ∑ a ∈ S, M.count a ≤ Multiset.card M := by
  calc ∑ a ∈ S, M.count a ≤ ∑ a ∈ S ∪ M.toFinset, M.count a :=
        sum_le_sum_of_subset subset_union_left
    _ = ∑ a ∈ M.toFinset, M.count a := by
        refine (sum_subset subset_union_right fun a _ ha => ?_).symm
        exact Multiset.count_eq_zero.mpr (by simpa using ha)
    _ = Multiset.card M := Multiset.toFinset_sum_count_eq M

variable {F : Type*} [Field F]

/-- If the roots of `p ≠ 0` lie in `S` then `∑_{α ∈ S} ord_α p = deg p` (algebraically closed). -/
lemma sum_rootMultiplicity_eq_natDegree [IsAlgClosed F] [DecidableEq F] {p : F[X]} (hp : p ≠ 0)
    {S : Finset F} (hS : p.roots.toFinset ⊆ S) :
    ∑ a ∈ S, rootMultiplicity a p = p.natDegree := by
  rw [(IsAlgClosed.splits p).natDegree_eq_card_roots, ← Multiset.toFinset_sum_count_eq]
  simp_rw [count_roots]
  refine (sum_subset hS fun a _ ha => ?_).symm
  exact rootMultiplicity_eq_zero fun h => ha (Multiset.mem_toFinset.mpr ((mem_roots hp).mpr h))

lemma card_filter_rootMultiplicity_pos [DecidableEq F] {p : F[X]} (hp : p ≠ 0) {S : Finset F}
    (hS : p.roots.toFinset ⊆ S) :
    (S.filter fun a => 0 < rootMultiplicity a p).card = p.roots.toFinset.card := by
  congr 1
  ext a
  simp only [mem_filter, Multiset.mem_toFinset, mem_roots hp, rootMultiplicity_pos hp]
  exact ⟨fun h => h.2, fun h => ⟨hS (Multiset.mem_toFinset.mpr ((mem_roots hp).mpr h)), h⟩⟩

/-- **Mason–Stothers for `m + 1` terms.** If `y₀ + ⋯ + y_m = 0`, all `yⱼ ≠ 0`, the `yⱼ` have no
common root and `y₁, …, y_m` are linearly independent, then
`deg y_l + m(m-1)/2 ≤ (m - 1) ∑ⱼ ν(yⱼ)` for every `l`. -/
theorem natDegree_add_le_mul_card_roots [IsAlgClosed F] [CharZero F] [DecidableEq F] {m : ℕ}
    (y : Fin (m + 1) → F[X]) (hsum : ∑ j, y j = 0) (hy : ∀ j, y j ≠ 0)
    (hli : LinearIndependent F fun j : Fin m => y j.succ)
    (hcop : ∀ α : F, ∃ j, ¬ (y j).IsRoot α) (l : Fin (m + 1)) :
    (y l).natDegree + ∑ i : Fin m, (i : ℕ) ≤ (m - 1) * ∑ j, (y j).roots.toFinset.card := by
  classical
  -- all the `m`-element subfamilies span the same space
  have hspan : ∀ a : Fin (m + 1),
      Submodule.span F (Set.range (y ∘ a.succAbove)) = Submodule.span F (Set.range y) := by
    intro a
    apply le_antisymm
    · exact Submodule.span_mono (Set.range_comp_subset_range _ _)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rcases Fin.eq_self_or_eq_succAbove a j with rfl | ⟨i, rfl⟩
      · have : y j = -∑ i, (y ∘ j.succAbove) i := by
          rw [Fin.sum_univ_succAbove _ j] at hsum
          simp only [Function.comp_apply]
          linear_combination hsum
        rw [SetLike.mem_coe, this]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
          Submodule.subset_span ⟨i, rfl⟩)
      · exact Submodule.subset_span ⟨i, rfl⟩
  have hli' : ∀ a : Fin (m + 1), LinearIndependent F (y ∘ a.succAbove) := by
    intro a
    have h0 : y ∘ (0 : Fin (m + 1)).succAbove = fun j => y j.succ := by
      funext j; simp
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan a, ← hspan 0, h0,
      ← Set.finrank, ← linearIndependent_iff_card_eq_finrank_span]
    exact hli
  set W := wronskianN (y ∘ l.succAbove)
  have hW : W ≠ 0 := wronskianN_ne_zero_of_linearIndependent (hli' l)
  -- order of vanishing of `W` at each `α`
  set e : F → ℕ := fun α => ∑ j, (rootMultiplicity α (y j) - (m - 1))
  have hdvd : ∀ α, (X - C α) ^ e α ∣ W := by
    intro α
    obtain ⟨ex, hex⟩ := hcop α
    have hdW := pow_dvd_wronskianN (g := y ∘ ex.succAbove) (q := X - C α)
      (v := fun j => rootMultiplicity α (y (ex.succAbove j))) fun j => pow_rootMultiplicity_dvd _ _
    have he : e α = ∑ j : Fin m, (rootMultiplicity α (y (ex.succAbove j)) - (m - 1)) := by
      simp only [e]
      rw [Fin.sum_univ_succAbove _ ex, rootMultiplicity_eq_zero hex, Nat.zero_sub, zero_add]
    -- `W` is a constant multiple of the Wronskian of the family without `ex`
    have hmem : ∀ j, (y ∘ l.succAbove) j ∈ Submodule.span F (Set.range (y ∘ ex.succAbove)) := by
      intro j; rw [hspan ex]; exact Submodule.subset_span ⟨_, rfl⟩
    have hc : ∀ j, ∃ c : Fin m → F, ∑ i, c i • (y ∘ ex.succAbove) i = (y ∘ l.succAbove) j :=
      fun j => (Submodule.mem_span_range_iff_exists_fun F).mp (hmem j)
    choose c hc using hc
    have hfeq : (y ∘ l.succAbove) =
        fun j => ∑ i, C ((Matrix.of fun i j => c j i) i j) * (y ∘ ex.succAbove) i := by
      funext j; rw [← hc j]; simp [smul_eq_C_mul]
    have : W = wronskianN (y ∘ ex.succAbove) * C (Matrix.of fun i j => c j i).det := by
      simp only [W]; rw [hfeq, wronskianN_comb]
    rw [this, he]
    exact dvd_mul_of_dvd_left hdW _
  -- sum over the roots
  set S : Finset F := univ.biUnion fun j => (y j).roots.toFinset
  have hSj : ∀ j, (y j).roots.toFinset ⊆ S := fun j =>
    subset_biUnion_of_mem (fun j => (y j).roots.toFinset) (mem_univ j)
  have hlow : ∑ α ∈ S, e α ≤ W.natDegree := by
    calc ∑ α ∈ S, e α ≤ ∑ α ∈ S, W.roots.count α := sum_le_sum fun α _ => by
          rw [count_roots]; exact (le_rootMultiplicity_iff hW).mpr (hdvd α)
      _ ≤ Multiset.card W.roots := sum_count_le_card S W.roots
      _ ≤ W.natDegree := card_roots' W
  have hup : W.natDegree + ∑ i : Fin m, (i : ℕ) ≤ ∑ j, (y (l.succAbove j)).natDegree :=
    natDegree_wronskianN_add_le hW
  have hsplit : ∑ j, (y j).natDegree =
      (y l).natDegree + ∑ j : Fin m, (y (l.succAbove j)).natDegree :=
    Fin.sum_univ_succAbove _ l
  -- `∑ deg ≤ ∑ e + (m - 1) ∑ ν`
  have hpt : ∀ α j, rootMultiplicity α (y j) ≤ (rootMultiplicity α (y j) - (m - 1)) +
      (m - 1) * (if 0 < rootMultiplicity α (y j) then 1 else 0) := by
    intro α j; split_ifs <;> omega
  have hdeg : ∑ j, (y j).natDegree ≤ ∑ α ∈ S, e α +
      (m - 1) * ∑ j, (y j).roots.toFinset.card := by
    calc ∑ j, (y j).natDegree = ∑ j, ∑ α ∈ S, rootMultiplicity α (y j) :=
          sum_congr rfl fun j _ => (sum_rootMultiplicity_eq_natDegree (hy j) (hSj j)).symm
      _ ≤ ∑ j, ∑ α ∈ S, ((rootMultiplicity α (y j) - (m - 1)) +
            (m - 1) * (if 0 < rootMultiplicity α (y j) then 1 else 0)) :=
          sum_le_sum fun j _ => sum_le_sum fun α _ => hpt α j
      _ = ∑ α ∈ S, e α + (m - 1) * ∑ j, (y j).roots.toFinset.card := by
          simp only [sum_add_distrib, e]
          rw [sum_comm]
          congr 1
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [← mul_sum, sum_boole, Nat.cast_id, card_filter_rootMultiplicity_pos (hy j) (hSj j)]
  omega

/-- A minimal spanning subfamily: if `w i0` lies in the span of the other `w i`, then it is a
combination `∑ a x • w (e x)` of a linearly independent subfamily, with all `a x ≠ 0`. -/
lemma exists_minimal_span {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V]
    [Module F V] (w : ι → V) (i0 : ι)
    (h : w i0 ∈ Submodule.span F (w '' ↑(univ.erase i0))) :
    ∃ t, ∃ e : Fin t → ι, Function.Injective e ∧ (∀ x, e x ≠ i0) ∧
      t ≤ Fintype.card ι - 1 ∧ ∃ a : Fin t → F, (∀ x, a x ≠ 0) ∧
      ∑ x, a x • w (e x) = w i0 ∧ LinearIndependent F (w ∘ e) := by
  classical
  obtain ⟨J, hJ, hmin⟩ := exists_min_image
    ((univ.erase i0).powerset.filter fun J : Finset ι => w i0 ∈ Submodule.span F (w '' ↑J)) card
    ⟨_, mem_filter.2 ⟨mem_powerset_self _, h⟩⟩
  rw [mem_filter, mem_powerset] at hJ
  obtain ⟨hJsub, hJspan⟩ := hJ
  let e : Fin J.card → ι := fun x => (J.equivFin.symm x : ι)
  have he : Function.Injective e := Subtype.val_injective.comp J.equivFin.symm.injective
  have heJ : ∀ x, e x ∈ J := fun x => (J.equivFin.symm x).2
  have hrange : w '' ↑J = Set.range (w ∘ e) := by
    ext v; constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨J.equivFin ⟨i, hi⟩, by simp [e]⟩
    · rintro ⟨x, rfl⟩; exact ⟨e x, heJ x, rfl⟩
  have hsmall : ∀ x, w i0 ∉ Submodule.span F (w '' ↑(J.erase (e x))) := by
    intro x hx
    have := hmin (J.erase (e x))
      (mem_filter.2 ⟨mem_powerset.2 ((erase_subset _ _).trans hJsub), hx⟩)
    have := card_erase_lt_of_mem (heJ x)
    omega
  have hkey : ∀ x, w (e x) ∉ Submodule.span F (w '' ↑(J.erase (e x))) := by
    intro x hx
    apply hsmall x
    refine (Submodule.span_le.2 ?_) hJspan
    rintro _ ⟨i, hi, rfl⟩
    by_cases hix : i = e x
    · subst hix; exact hx
    · exact Submodule.subset_span ⟨i, mem_erase.2 ⟨hix, hi⟩, rfl⟩
  rw [hrange] at hJspan
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hJspan
  refine ⟨J.card, e, he, fun x => (mem_erase.1 (hJsub (heJ x))).1, ?_, a, ?_, ha, ?_⟩
  · have := card_le_card hJsub
    rwa [card_erase_of_mem (mem_univ _), card_univ] at this
  · intro x hax
    apply hsmall x
    rw [← ha]
    refine Submodule.sum_mem _ fun x' _ => ?_
    by_cases hx' : x' = x
    · subst hx'; rw [hax, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨e x', mem_erase.2 ⟨he.ne hx', heJ x'⟩, rfl⟩)
  · rw [linearIndependent_iff_notMem_span]
    intro x hx
    apply hkey x
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨x', hx', rfl⟩
    have hx'' : x' ≠ x := by simpa using hx'
    exact ⟨e x', mem_erase.2 ⟨he.ne hx'', heJ x'⟩, rfl⟩

/-- **Vaserstein–Wheland / Tsang–Yip, Corollary 4.2.** Let `F` be algebraically closed of
characteristic `0`, and let `∑ᵢ cᵢ pᵢᵏ = 0` be a relation among `s` nonzero polynomials with
`c_{i₀} ≠ 0`, where `p_{i₀}` is not a constant multiple of any other `pⱼ`. Then `k < s(s-2)`. -/
theorem k_lt_of_relation [IsAlgClosed F] [CharZero F] {s k : ℕ} (hk : 0 < k)
    (p : Fin s → F[X]) (c : Fin s → F) (hp : ∀ i, p i ≠ 0)
    (hrel : ∑ i, C (c i) * p i ^ k = 0) (i0 : Fin s) (hc0 : c i0 ≠ 0)
    (hnp : ∀ j ≠ i0, ∀ a : F, p i0 ≠ C a * p j) : k < s * (s - 2) := by
  classical
  -- `p i0 ^ k` lies in the span of the other `p j ^ k`
  have hspan : p i0 ^ k ∈ Submodule.span F ((fun i => p i ^ k) '' ↑(univ.erase i0)) := by
    rw [← add_sum_erase _ _ (mem_univ i0)] at hrel
    simp only [← smul_eq_C_mul] at hrel
    have h1 : ∑ i ∈ univ.erase i0, c i • p i ^ k = -(c i0 • p i0 ^ k) := by
      linear_combination hrel
    have h2 : p i0 ^ k = (-(c i0)⁻¹) • ∑ i ∈ univ.erase i0, c i • p i ^ k := by
      rw [h1, smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩))
  obtain ⟨t, e, -, hne, hts, a, ha0, ha, hli⟩ := exists_minimal_span (fun i => p i ^ k) i0 hspan
  -- remove the common factor
  let P : Fin (t + 1) → F[X] := Fin.cons (p i0) fun x => p (e x)
  obtain ⟨q, hq, hq1⟩ := extract_gcd P (univ_nonempty (α := Fin (t + 1)))
  set G := univ.gcd P
  have hq0' : p i0 = G * q 0 := by simpa [P] using hq 0 (mem_univ _)
  have hqs : ∀ x, p (e x) = G * q x.succ := fun x => by simpa [P] using hq x.succ (mem_univ _)
  have hG : G ≠ 0 := fun h => hp i0 (by rw [hq0', h, zero_mul])
  have hq0 : ∀ j, q j ≠ 0 := by
    intro j
    induction j using Fin.cases with
    | zero => exact fun h => hp i0 (by rw [hq0', h, mul_zero])
    | succ x => exact fun h => hp (e x) (by rw [hqs, h, mul_zero])
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp only [univ_eq_empty, sum_empty] at ha
      exact absurd ha.symm (pow_ne_zero _ (hp i0))
    · exact h
  -- the reduced relation
  let y : Fin (t + 1) → F[X] := Fin.cons (q 0 ^ k) fun x => -C (a x) * q x.succ ^ k
  have hy : ∀ j, y j ≠ 0 := by
    intro j
    induction j using Fin.cases with
    | zero => simpa [y] using pow_ne_zero k (hq0 0)
    | succ x => simp [y, ha0 x, hq0]
  have hsum : ∑ j, y j = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero k hG)
    rw [mul_zero, mul_sum, Fin.sum_univ_succ]
    simp only [y, Fin.cons_zero, Fin.cons_succ]
    have h := ha
    simp only [hq0', hqs, smul_eq_C_mul, mul_pow] at h
    rw [← h, ← sum_add_distrib]
    exact sum_eq_zero fun x _ => by ring
  have hli' : LinearIndependent F fun x : Fin t => y x.succ := by
    have h1 : LinearIndependent F fun x : Fin t => q x.succ ^ k := by
      apply LinearIndependent.of_comp (LinearMap.mulLeft F (G ^ k))
      convert hli using 1
      funext x
      simp [hqs, mul_pow]
    convert h1.units_smul fun x => Units.mk0 (-a x) (neg_ne_zero.2 (ha0 x)) using 1
    funext x
    simp [y, Units.smul_def, smul_eq_C_mul]
  have hcop : ∀ α : F, ∃ j, ¬ (y j).IsRoot α := by
    intro α
    by_contra! h
    have hdvd : ∀ j, X - C α ∣ q j := by
      intro j
      rw [dvd_iff_isRoot]
      have hj := h j
      induction j using Fin.cases with
      | zero => simpa [y, hk.ne'] using hj
      | succ x => simpa [y, ha0 x, hk.ne'] using hj
    exact not_isUnit_X_sub_C α (isUnit_of_dvd_one (hq1 ▸ dvd_gcd fun j _ => hdvd j))
  have hdeg : ∀ j, (y j).natDegree = k * (q j).natDegree := by
    intro j
    induction j using Fin.cases with
    | zero => simp [y, natDegree_pow]
    | succ x => simp [y, natDegree_pow, natDegree_C_mul (ha0 x)]
  have hν : ∀ j, (y j).roots.toFinset.card = (q j).roots.toFinset.card := by
    intro j
    induction j using Fin.cases with
    | zero => simp [y, roots_pow, Multiset.toFinset_nsmul _ _ hk.ne']
    | succ x => simp [y, roots_C_mul _ (ha0 x), roots_pow, Multiset.toFinset_nsmul _ _ hk.ne']
  obtain ⟨l, -, hl⟩ := exists_max_image univ (fun j => (q j).roots.toFinset.card) univ_nonempty
  have hMS := natDegree_add_le_mul_card_roots y hsum hy hli' hcop l
  rw [hdeg] at hMS
  simp only [hν] at hMS
  set T := (q l).roots.toFinset.card
  have hsumν : ∑ j, (q j).roots.toFinset.card ≤ (t + 1) * T := by
    calc ∑ j, (q j).roots.toFinset.card ≤ ∑ _j : Fin (t + 1), T :=
          sum_le_sum fun j _ => hl j (mem_univ _)
      _ = (t + 1) * T := by simp
  have hTdeg : T ≤ (q l).natDegree := (Multiset.toFinset_card_le _).trans (card_roots' _)
  have hT : 1 ≤ T := by
    by_contra! hT0
    have hc : ∀ j, (q j).natDegree = 0 := by
      intro j
      by_contra hj
      obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (q j)
        (by rw [degree_eq_natDegree (hq0 j)]; exact_mod_cast hj)
      have hpos : 0 < (q j).roots.toFinset.card :=
        card_pos.2 ⟨α, by simpa [mem_roots (hq0 j)] using hα⟩
      have := hl j (mem_univ _)
      omega
    let x0 : Fin t := ⟨0, ht⟩
    obtain ⟨u0, hu0⟩ : ∃ u, q 0 = C u := ⟨_, eq_C_of_natDegree_eq_zero (hc 0)⟩
    obtain ⟨u1, hu1⟩ : ∃ u, q x0.succ = C u := ⟨_, eq_C_of_natDegree_eq_zero (hc x0.succ)⟩
    have hu1' : u1 ≠ 0 := fun h => hq0 x0.succ (by rw [hu1, h, C_0])
    apply hnp (e x0) (hne x0) (u0 / u1)
    rw [hq0', hqs, hu0, hu1, mul_left_comm, ← C_mul, div_mul_cancel₀ _ hu1']
  have hkT : k * T ≤ k * (q l).natDegree := Nat.mul_le_mul_left _ hTdeg
  have h3 : (t - 1) * ∑ j, (q j).roots.toFinset.card ≤ (t - 1) * ((t + 1) * T) :=
    Nat.mul_le_mul_left _ hsumν
  have hTk : T ≤ k * T := Nat.le_mul_of_pos_left _ hk
  have ht2 : 2 ≤ t := by
    by_contra! h
    obtain rfl : t = 1 := by omega
    simp only [Nat.sub_self, zero_mul] at h3
    omega
  have hpos : 1 ≤ ∑ i : Fin t, (i : ℕ) :=
    single_le_sum (f := fun i : Fin t => (i : ℕ)) (fun _ _ => Nat.zero_le _)
      (mem_univ (⟨1, ht2⟩ : Fin t))
  have hk' : k < (t - 1) * (t + 1) := by
    by_contra! H
    have := Nat.mul_le_mul_right T H
    rw [mul_assoc] at this
    omega
  have hts' : t + 1 ≤ s := by
    rw [Fintype.card_fin] at hts
    have := i0.pos
    omega
  calc k < (t - 1) * (t + 1) := hk'
    _ ≤ (s - 2) * s := Nat.mul_le_mul (by omega) hts'
    _ = s * (s - 2) := mul_comm _ _

end DiophantineTuples
