module

public import LeanPlayground.DiophantineTuples.SixTermRigid
public import Mathlib.Algebra.Polynomial.Taylor

@[expose] public noncomputable section

/-!
# Tsang–Yip Proposition 4.4 and six-term rigidity for `k ≥ 18`

Let `F` be algebraically closed of characteristic `0`.

* `pow_dvd_wronskianN_of_injective`: the valuation-gap bound of Vaserstein–Wheland. If
  `(X - α) ^ vⱼ ∣ gⱼ`, the Wronskian `W(g)` vanishes at `α` to order at least
  `min {∑ rⱼ : r injective, r ≥ v} - m(m-1)/2`. The proof expands each `gⱼ` in powers of `X - α`
  (Taylor) and uses multilinearity of the determinant: terms with a repeated exponent vanish.
* `sum_add_le_natDegree_of_dvd`: the Wronskian degree count with prescribed local orders.
* `k_lt_eighteen` (Tsang–Yip, Proposition 4.4): six pairwise nonproportional polynomials with
  `q₁ᵏ + q₂ᵏ + q₃ᵏ = r₁ᵏ + r₂ᵏ + r₃ᵏ` and `q₁q₂q₃ = λ r₁r₂r₃` force `k < 18`. At a root `α` the
  product identity makes `sα = ∑ ord_α` even with no term above `sα/2`; the gap count
  (`gap_bound`, Claim 4.5) gives local loss at most `3 sα`, hence `kT ≤ 18T - 10`.
* `sixTermRigid_of_eighteen_le`: `SixTermRigid F k` for `k ≥ 18` (Claims 4.8–4.9), and so
* `card_le_four_of_eighteen_le`: `|A| ≤ 4` for polynomial `D_k(n)`-tuples, `k ≥ 18`,
  outside the exceptional family, with no extra hypothesis (Tsang–Yip: `|A| ≤ 6`).
-/

namespace DiophantineTuples

open Polynomial Finset

section CommRing

variable {R : Type*} [CommRing R] {m : ℕ}

/-- Per-permutation bound: if `q ^ v j ∣ g j` then `q ^ (∑ v - m(m-1)/2)` divides the Wronskian. -/
lemma pow_sum_sub_dvd_wronskianN {g : Fin m → R[X]} {q : R[X]} {v : Fin m → ℕ}
    (h : ∀ j, q ^ v j ∣ g j) : q ^ (∑ j, v j - ∑ i : Fin m, (i : ℕ)) ∣ wronskianN g := by
  rw [wronskianN, Matrix.det_apply]
  refine dvd_sum fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine dvd_mul_of_dvd_right ?_ _
  have hle : ∑ j, v j - ∑ i : Fin m, (i : ℕ) ≤ ∑ j, (v j - ((σ j : Fin m) : ℕ)) := by
    have h1 : ∑ j, ((σ j : Fin m) : ℕ) = ∑ i : Fin m, (i : ℕ) :=
      Equiv.sum_comp σ (fun i : Fin m => (i : ℕ))
    have h2 : ∑ j, v j ≤ ∑ j, (v j - ((σ j : Fin m) : ℕ)) + ∑ j, ((σ j : Fin m) : ℕ) := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun j _ => le_tsub_add
    omega
  refine (pow_dvd_pow q hle).trans ?_
  rw [← prod_pow_eq_pow_sum]
  refine prod_dvd_prod_of_dvd _ _ fun j _ => ?_
  simp only [wronskianMatrix, Matrix.of_apply]
  exact pow_sub_dvd_iterate_derivative_of_pow_dvd _ (h j)

/-- Taylor coefficients below the order of vanishing are zero. -/
lemma taylor_coeff_eq_zero_of_lt {g : R[X]} {α : R} {v n : ℕ} (h : (X - C α) ^ v ∣ g)
    (hn : n < v) : (taylor α g).coeff n = 0 := by
  obtain ⟨h', rfl⟩ := h
  rw [taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right,
    coeff_X_pow_mul']
  split_ifs with h
  · omega
  · rfl

/-- **Valuation-gap bound for the Wronskian** (Vaserstein–Wheland). If `(X - α) ^ v j ∣ g j`, then
`(X - α) ^ B ∣ W(g)` whenever `B + m(m-1)/2 ≤ ∑ r j` for every *injective* `r ≥ v`. -/
lemma pow_dvd_wronskianN_of_injective {g : Fin m → R[X]} {α : R} {v : Fin m → ℕ}
    (h : ∀ j, (X - C α) ^ v j ∣ g j) (B : ℕ)
    (hB : ∀ r : Fin m → ℕ, Function.Injective r → (∀ j, v j ≤ r j) →
      B + ∑ i : Fin m, (i : ℕ) ≤ ∑ j, r j) :
    (X - C α) ^ B ∣ wronskianN g := by
  classical
  set t : Fin m → ℕ → R := fun j n => (taylor α (g j)).coeff n
  set u : ℕ → Fin m → R[X] := fun n i => derivative^[i] ((X - C α) ^ n)
  set N : Fin m → ℕ := fun j => (g j).natDegree + 1
  have hrow : (wronskianMatrix g).transpose = fun j => ∑ n ∈ range (N j), C (t j n) • u n := by
    funext j i
    simp only [Matrix.transpose_apply, wronskianMatrix, Matrix.of_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, u, t]
    conv_lhs => rw [← sum_taylor_eq (g j) α,
      sum_over_range' _ (fun n => by simp) (N j)
        (by rw [natDegree_taylor]; exact Nat.lt_succ_self _)]
    rw [iterate_derivative_sum]
    exact sum_congr rfl fun n _ => iterate_derivative_C_mul _ _ _
  rw [wronskianN, ← Matrix.det_transpose, hrow]
  change _ ∣ (Matrix.detRowAlternating : (Fin m → R[X]) [⋀^Fin m]→ₗ[R[X]] R[X]).toMultilinearMap
    (fun j => ∑ n ∈ range (N j), C (t j n) • u n)
  rw [MultilinearMap.map_sum_finset]
  refine dvd_sum fun r _ => ?_
  rw [MultilinearMap.map_smul_univ]
  by_cases hrv : ∀ j, v j ≤ r j
  · by_cases hinj : Function.Injective r
    · refine dvd_mul_of_dvd_right ?_ _
      have hdet : (Matrix.detRowAlternating : (Fin m → R[X]) [⋀^Fin m]→ₗ[R[X]] R[X])
          (fun j => u (r j)) = wronskianN fun j => (X - C α) ^ r j := by
        rw [wronskianN, ← Matrix.det_transpose]
        rfl
      rw [AlternatingMap.coe_multilinearMap, hdet]
      refine (pow_dvd_pow _ ?_).trans (pow_sum_sub_dvd_wronskianN (v := r) fun j => dvd_rfl)
      have := hB r hinj hrv
      omega
    · obtain ⟨j₁, j₂, hj, hne⟩ : ∃ j₁ j₂, r j₁ = r j₂ ∧ j₁ ≠ j₂ := by
        by_contra! hcon
        exact hinj fun a b hab => hcon a b hab
      rw [AlternatingMap.coe_multilinearMap,
        AlternatingMap.map_eq_zero_of_eq _ _ (by simp only [hj]) hne, smul_zero]
      exact dvd_zero _
  · push Not at hrv
    obtain ⟨j, hj⟩ := hrv
    have : t j (r j) = 0 := taylor_coeff_eq_zero_of_lt (h j) hj
    rw [prod_eq_zero (mem_univ j) (by rw [this, C_0]), zero_smul]
    exact dvd_zero _

end CommRing

/-- `0 + 1 + ⋯ + (|t| - 1) ≤ ∑ t` for a finite set `t` of naturals. -/
lemma sum_range_card_le (t : Finset ℕ) : ∑ i ∈ range t.card, i ≤ ∑ x ∈ t, x := by
  induction t using Finset.induction_on_max with
  | empty => simp
  | insert a t ha ih =>
    have hat : a ∉ t := fun h => lt_irrefl a (ha a h)
    rw [card_insert_of_notMem hat, sum_range_succ, sum_insert hat]
    have : t.card ≤ a := by
      have hsub : t ⊆ range a := fun x hx => mem_range.2 (ha x hx)
      simpa using card_le_card hsub
    omega

lemma sum_range_card_le_sum_of_injOn {ι : Type*} (S : Finset ι) (r : ι → ℕ)
    (hr : Set.InjOn r S) : ∑ i ∈ range S.card, i ≤ ∑ j ∈ S, r j := by
  classical
  rw [← card_image_of_injOn hr]
  calc ∑ i ∈ range (S.image r).card, i ≤ ∑ x ∈ S.image r, x := sum_range_card_le _
    _ = ∑ j ∈ S, r j := sum_image hr

/-- The valuation count of Tsang–Yip, Claim 4.5: five orders `k wⱼ` with `∑ w` even and no `wⱼ`
above half the total; any injective `r ≥ k w` has `∑ r ≥ (k - 3) ∑ w + 10`. -/
lemma gap_bound {k : ℕ} (w r : Fin 5 → ℕ) (hr : Function.Injective r)
    (hrw : ∀ j, k * w j ≤ r j) (heven : Even (∑ j, w j)) (hmax : ∀ j, 2 * w j ≤ ∑ j, w j) :
    k * ∑ j, w j - 3 * ∑ j, w j + 10 ≤ ∑ j, r j := by
  classical
  have h10 : 10 ≤ ∑ j, r j := by
    have := sum_range_card_le_sum_of_injOn univ r hr.injOn
    simpa [sum_range_succ] using this
  have hks : k * ∑ j, w j ≤ ∑ j, r j := by
    rw [mul_sum]; exact sum_le_sum fun j _ => hrw j
  set s := ∑ j, w j with hs
  obtain ⟨t, ht⟩ := heven
  rcases (by omega : s = 0 ∨ s = 2 ∨ 4 ≤ s) with h | h | h
  · rw [h]; simpa using h10
  · have hw1 : ∀ j, w j ≤ 1 := fun j => by have := hmax j; omega
    set P := univ.filter fun j => w j = 1
    have hsP : s = P.card := by
      rw [hs, card_eq_sum_ones, sum_filter]
      exact sum_congr rfl fun j _ => by have := hw1 j; split_ifs <;> omega
    have hcardZ : (univ.filter fun j => ¬ w j = 1).card = 3 := by
      have := card_filter_add_card_filter_not (s := (univ : Finset (Fin 5)))
        (fun j => w j = 1)
      change P.card + _ = _ at this
      simp only [card_univ, Fintype.card_fin] at this
      omega
    obtain ⟨a, b, hab, hPab⟩ := card_eq_two.1 (by omega : P.card = 2)
    have ha : w a = 1 := (mem_filter.1 (show a ∈ P by rw [hPab]; exact mem_insert_self a {b})).2
    have hb : w b = 1 :=
      (mem_filter.1 (show b ∈ P by rw [hPab]; exact mem_insert_of_mem (mem_singleton_self b))).2
    have hZsum : 3 ≤ ∑ j ∈ univ.filter (fun j => ¬ w j = 1), r j := by
      have := sum_range_card_le_sum_of_injOn (univ.filter fun j => ¬ w j = 1) r hr.injOn
      rw [hcardZ] at this
      simpa [sum_range_succ] using this
    have hsplit := sum_filter_add_sum_filter_not univ (fun j => w j = 1) r
    rw [← show P = univ.filter fun j => w j = 1 from rfl, hPab, sum_pair hab] at hsplit
    have hra := hrw a
    have hrb := hrw b
    rw [ha, mul_one] at hra
    rw [hb, mul_one] at hrb
    have hne : r a ≠ r b := hr.ne hab
    rw [h]
    omega
  · omega

variable {F : Type*} [Field F]

/-- **Wronskian counting with prescribed local bounds.** Let `y₀ + ⋯ + y_m = 0` with some `m` of
the `yⱼ` linearly independent. If at each `α ∈ S` the Wronskian of some `m` of the `yⱼ` is divisible
by `(X - α) ^ e α`, then `∑_{α ∈ S} e α + m(m-1)/2 ≤ ∑_{j ≠ l} deg yⱼ`. -/
theorem sum_add_le_natDegree_of_dvd [CharZero F] {m : ℕ} (y : Fin (m + 1) → F[X])
    (hsum : ∑ j, y j = 0) (a : Fin (m + 1)) (hli : LinearIndependent F (y ∘ a.succAbove))
    (l : Fin (m + 1)) (S : Finset F) (e : F → ℕ)
    (he : ∀ α ∈ S, ∃ ex : Fin (m + 1), (X - C α) ^ e α ∣ wronskianN (y ∘ ex.succAbove)) :
    ∑ α ∈ S, e α + ∑ i : Fin m, (i : ℕ) ≤ ∑ j : Fin m, (y (l.succAbove j)).natDegree := by
  classical
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
  have hli' : ∀ b : Fin (m + 1), LinearIndependent F (y ∘ b.succAbove) := by
    intro b
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan b, ← hspan a,
      ← Set.finrank, ← linearIndependent_iff_card_eq_finrank_span]
    exact hli
  set W := wronskianN (y ∘ l.succAbove)
  have hW : W ≠ 0 := wronskianN_ne_zero_of_linearIndependent (hli' l)
  have hdvd : ∀ α ∈ S, (X - C α) ^ e α ∣ W := by
    intro α hα
    obtain ⟨ex, hex⟩ := he α hα
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
    rw [this]
    exact dvd_mul_of_dvd_left hex _
  have hlow : ∑ α ∈ S, e α ≤ W.natDegree := by
    calc ∑ α ∈ S, e α ≤ ∑ α ∈ S, W.roots.count α := sum_le_sum fun α hα => by
          rw [count_roots]; exact (le_rootMultiplicity_iff hW).mpr (hdvd α hα)
      _ ≤ Multiset.card W.roots := sum_count_le_card S W.roots
      _ ≤ W.natDegree := card_roots' W
  have hup : W.natDegree + ∑ i : Fin m, (i : ℕ) ≤ ∑ j, (y (l.succAbove j)).natDegree :=
    natDegree_wronskianN_add_le hW
  omega

lemma rootMultiplicity_prod_of_ne_zero {ι : Type*} (s : Finset ι) (f : ι → F[X])
    (hf : ∀ i ∈ s, f i ≠ 0) (α : F) :
    rootMultiplicity α (∏ i ∈ s, f i) = ∑ i ∈ s, rootMultiplicity α (f i) := by
  classical
  rw [← count_roots, roots_prod _ _ (prod_ne_zero_iff.2 hf), Multiset.count_bind,
    ← sum_eq_multiset_sum]
  exact sum_congr rfl fun i _ => count_roots _

/-- **Tsang–Yip, Proposition 4.4.** Let `q₁, q₂, q₃, r₁, r₂, r₃ ∈ F[X]` be nonzero and pairwise
nonproportional, with `q₁ᵏ + q₂ᵏ + q₃ᵏ = r₁ᵏ + r₂ᵏ + r₃ᵏ` and `q₁q₂q₃ = λ r₁r₂r₃`. Then `k < 18`. -/
theorem k_lt_eighteen [IsAlgClosed F] [CharZero F] {k : ℕ} (hk : 0 < k) (q r : Fin 3 → F[X])
    (hp : ∀ i, Fin.append q r i ≠ 0)
    (hnp : ∀ i j, i ≠ j → ∀ a : F, Fin.append q r i ≠ C a * Fin.append q r j)
    (hsum : ∑ i, q i ^ k = ∑ j, r j ^ k) (lam : F) (hprod : ∏ i, q i = C lam * ∏ j, r j) :
    k < 18 := by
  classical
  by_contra! hk18
  set p : Fin (3 + 3) → F[X] := Fin.append q r
  set ε : Fin (3 + 3) → F := Fin.append (fun _ => 1) (fun _ => -1)
  have hrel : ∑ i, C (ε i) * p i ^ k = 0 := append_relation hsum
  have hq : ∀ i, q i ≠ 0 := fun i => by
    have h := hp (Fin.castAdd 3 i)
    rwa [show p (Fin.castAdd 3 i) = q i from Fin.append_left q r i] at h
  have hr : ∀ j, r j ≠ 0 := fun j => by
    have h := hp (Fin.natAdd 3 j)
    rwa [show p (Fin.natAdd 3 j) = r j from Fin.append_right q r j] at h
  -- remove the common factor
  obtain ⟨Q, hQ, hQ1⟩ := extract_gcd p (univ_nonempty (α := Fin (3 + 3)))
  set G := univ.gcd p
  have hpQ : ∀ i, p i = G * Q i := fun i => hQ i (mem_univ _)
  have hG : G ≠ 0 := fun h => hp 0 (by rw [hpQ, h, zero_mul])
  have hQ0 : ∀ i, Q i ≠ 0 := fun i h => hp i (by rw [hpQ, h, mul_zero])
  have hnpQ : ∀ i j, i ≠ j → ∀ a : F, Q i ≠ C a * Q j := fun i j hij a h =>
    hnp i j hij a (by rw [hpQ, hpQ, h]; ring)
  have hε : ∀ i, ε i ≠ 0 := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [show ε (Fin.castAdd 3 i) = 1 from Fin.append_left _ _ i]; exact one_ne_zero
    · rw [show ε (Fin.natAdd 3 j) = -1 from Fin.append_right _ _ j]
      exact neg_ne_zero.2 one_ne_zero
  have hrelQ : ∑ i, C (ε i) * Q i ^ k = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero k hG)
    rw [mul_zero, ← hrel, mul_sum]
    exact sum_congr rfl fun i _ => by rw [hpQ, mul_pow]; ring
  have hlam : lam ≠ 0 := by
    rintro rfl
    rw [C_0, zero_mul] at hprod
    exact prod_ne_zero_iff.2 (fun i _ => hq i) hprod
  have hprodQ : ∏ i : Fin 3, Q (Fin.castAdd 3 i) = C lam * ∏ j : Fin 3, Q (Fin.natAdd 3 j) := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hG)
    have h1 : ∏ i, q i = G ^ 3 * ∏ i : Fin 3, Q (Fin.castAdd 3 i) := by
      rw [show ∏ i, q i = ∏ i : Fin 3, (G * Q (Fin.castAdd 3 i)) from prod_congr rfl fun i _ => by
        rw [← hpQ]; exact (Fin.append_left q r i).symm, prod_mul_distrib, prod_const, card_univ,
        Fintype.card_fin]
    have h2 : ∏ j, r j = G ^ 3 * ∏ j : Fin 3, Q (Fin.natAdd 3 j) := by
      rw [show ∏ j, r j = ∏ j : Fin 3, (G * Q (Fin.natAdd 3 j)) from prod_congr rfl fun j _ => by
        rw [← hpQ]; exact (Fin.append_right q r j).symm, prod_mul_distrib, prod_const, card_univ,
        Fintype.card_fin]
    rw [← h1, hprod, h2]
    ring
  -- local data
  set v : F → Fin (3 + 3) → ℕ := fun α i => rootMultiplicity α (Q i)
  set sα : F → ℕ := fun α => ∑ i, v α i
  have hside : ∀ α, ∑ i : Fin 3, v α (Fin.castAdd 3 i) = ∑ j : Fin 3, v α (Fin.natAdd 3 j) := by
    intro α
    have h := congrArg (rootMultiplicity α) hprodQ
    have hne : ∏ j : Fin 3, Q (Fin.natAdd 3 j) ≠ 0 := prod_ne_zero_iff.2 fun j _ => hQ0 _
    rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.2 hlam) hne), rootMultiplicity_C, zero_add,
      rootMultiplicity_prod_of_ne_zero _ _ (fun i _ => hQ0 _),
      rootMultiplicity_prod_of_ne_zero _ _ (fun i _ => hQ0 _)] at h
    exact h
  have hsplit : ∀ α, sα α = ∑ i : Fin 3, v α (Fin.castAdd 3 i) +
      ∑ j : Fin 3, v α (Fin.natAdd 3 j) := fun α => Fin.sum_univ_add _
  have heven : ∀ α, Even (sα α) := fun α => ⟨_, by rw [hsplit, hside]⟩
  have hmax : ∀ α i, 2 * v α i ≤ sα α := by
    intro α i
    rw [hsplit]
    have h := hside α
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · have := single_le_sum (f := fun i : Fin 3 => v α (Fin.castAdd 3 i))
        (fun _ _ => Nat.zero_le _) (mem_univ i)
      beta_reduce at this; omega
    · have := single_le_sum (f := fun j : Fin 3 => v α (Fin.natAdd 3 j))
        (fun _ _ => Nat.zero_le _) (mem_univ j)
      beta_reduce at this; omega
  have hcop : ∀ α, ∃ i, v α i = 0 := by
    intro α
    by_contra! h
    have hdvd : ∀ i, X - C α ∣ Q i := fun i =>
      dvd_iff_isRoot.2 ((rootMultiplicity_pos (hQ0 i)).1 (Nat.pos_of_ne_zero (h i)))
    exact not_isUnit_X_sub_C α (isUnit_of_dvd_one (hQ1 ▸ dvd_gcd fun i _ => hdvd i))
  -- the term of maximal degree
  obtain ⟨i0, -, hi0⟩ := exists_max_image univ (fun i => (Q i).natDegree) univ_nonempty
  set T := (Q i0).natDegree
  have hT : 1 ≤ T := by
    by_contra! h0
    have hc : ∀ i, (Q i).natDegree = 0 := fun i => by have := hi0 i (mem_univ _); omega
    obtain ⟨u0, hu0⟩ : ∃ u, Q 0 = C u := ⟨_, eq_C_of_natDegree_eq_zero (hc 0)⟩
    obtain ⟨u1, hu1⟩ : ∃ u, Q 1 = C u := ⟨_, eq_C_of_natDegree_eq_zero (hc 1)⟩
    have hu1' : u1 ≠ 0 := fun h => hQ0 1 (by rw [hu1, h, C_0])
    exact hnpQ 0 1 (by decide) (u0 / u1) (by rw [hu0, hu1, ← C_mul, div_mul_cancel₀ _ hu1'])
  set y : Fin (3 + 3) → F[X] := fun i => C (ε i) * Q i ^ k
  -- the five terms other than `i0` are linearly independent (else Corollary 4.2 gives `k < 15`)
  have hli : LinearIndependent F (y ∘ i0.succAbove) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j1
    by_contra hj1
    have h15 := k_lt_of_relation (s := 5) hk (fun j => Q (i0.succAbove j))
      (fun j => g j * ε (i0.succAbove j)) (fun j => hQ0 _)
      (by
        rw [← hg]
        exact sum_congr rfl fun j _ => by
          simp only [Function.comp_apply, y, smul_eq_C_mul, C_mul]; ring)
      j1 (mul_ne_zero hj1 (hε _))
      (fun j hj a h => hnpQ _ _ (i0.succAbove_right_injective.ne (Ne.symm hj)) a h)
    norm_num at h15
    omega
  set S : Finset F := univ.biUnion fun i => (Q i).roots.toFinset
  have hMS := sum_add_le_natDegree_of_dvd (m := 5) y hrelQ i0 hli i0 S
    (fun α => k * sα α - 3 * sα α) (fun α _ => by
      obtain ⟨ex, hex⟩ := hcop α
      have hw : ∑ j : Fin 5, v α (ex.succAbove j) = sα α := by
        simp only [sα]
        rw [Fin.sum_univ_succAbove _ ex, hex, zero_add]
      refine ⟨ex, pow_dvd_wronskianN_of_injective
        (v := fun j => k * v α (ex.succAbove j)) (fun j => ?_) _ (fun r hr hrv => ?_)⟩
      · simp only [Function.comp_apply, y]
        refine dvd_mul_of_dvd_right ?_ _
        rw [mul_comm, pow_mul]
        exact pow_dvd_pow_of_dvd (pow_rootMultiplicity_dvd _ _) k
      · have hg := gap_bound (fun j => v α (ex.succAbove j)) r hr hrv (hw ▸ heven α)
          (fun j => hw ▸ hmax α _)
        rw [hw] at hg
        have h10 : ∑ i : Fin 5, (i : ℕ) = 10 := by decide
        rw [h10]
        exact hg)
  -- arithmetic
  set D := ∑ i, (Q i).natDegree
  have hdegy : ∀ i, (y i).natDegree = k * (Q i).natDegree := fun i => by
    simp only [y]; rw [natDegree_C_mul (hε i), natDegree_pow]
  have hRHS : ∑ j : Fin 5, (y (i0.succAbove j)).natDegree + k * T = k * D := by
    rw [mul_sum, Fin.sum_univ_succAbove (fun i => k * (Q i).natDegree) i0]
    simp only [hdegy]
    ring
  have hD : ∑ α ∈ S, sα α = D := by
    simp only [sα, v]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_rootMultiplicity_eq_natDegree (hQ0 i)
      (subset_biUnion_of_mem (fun i => (Q i).roots.toFinset) (mem_univ i))
  have hLHS : ∑ α ∈ S, (k * sα α - 3 * sα α) = (k - 3) * D := by
    rw [← hD, mul_sum]
    exact sum_congr rfl fun α _ => (Nat.sub_mul _ _ _).symm
  have hDT : D ≤ 6 * T := by
    calc D ≤ ∑ _i : Fin (3 + 3), T := sum_le_sum fun i _ => hi0 i (mem_univ _)
      _ = 6 * T := by simp
  have h10 : ∑ i : Fin 5, (i : ℕ) = 10 := by decide
  rw [hLHS, h10] at hMS
  have h1 : (k - 3) * D = k * D - 3 * D := Nat.sub_mul _ _ _
  have h2 : 3 * D ≤ k * D := Nat.mul_le_mul_right _ (by omega)
  have h3 : 18 * T ≤ k * T := Nat.mul_le_mul_right _ hk18
  omega

open scoped Classical in
/-- **Six-term rigidity for `k ≥ 18`** (Tsang–Yip, Claims 4.8–4.9 with Proposition 4.4). -/
theorem sixTermRigid_of_eighteen_le [IsAlgClosed F] [CharZero F] {k : ℕ} (hk : 18 ≤ k) :
    SixTermRigid F k :=
  sixTermRigid_of_classSum (by omega) fun q r hq hr _ hsum hprod g => by
    by_contra hg
    have hlt := lt_of_classSum_ne_zero (by omega) _ _ (append_ne_zero hq hr)
      (append_relation hsum) g hg
    have hcard : (univ.image fun i => monicPart (Fin.append q r i)).card ≤ 6 :=
      card_image_le.trans (by simp)
    rcases (by omega : (univ.image fun i => monicPart (Fin.append q r i)).card ≤ 5 ∨
        (univ.image fun i => monicPart (Fin.append q r i)).card = 6) with h5 | h6
    · have := Nat.mul_le_mul h5 (Nat.sub_le_sub_right h5 2)
      omega
    · have hinj : Set.InjOn (fun i => monicPart (Fin.append q r i))
          ↑(univ : Finset (Fin (3 + 3))) :=
        card_image_iff.1 (h6.trans (by simp))
      refine absurd (k_lt_eighteen (by omega) q r (append_ne_zero hq hr) ?_ hsum 1
        (by rw [C_1, one_mul]; exact hprod)) (by omega)
      intro i j hij a h
      have ha : a ≠ 0 := by
        rintro rfl
        rw [C_0, zero_mul] at h
        exact append_ne_zero hq hr i h
      apply hij
      apply hinj (mem_coe.2 (mem_univ i)) (mem_coe.2 (mem_univ j))
      simp only [h, monicPart_C_mul ha]

/-- **Polynomial `D_k(n)`-tuples have at most four elements for `k ≥ 18`, unconditionally.**
For `F` algebraically closed of characteristic `0`, `n ≠ 0` and `A ⊆ F[X]` with property `D_k(n)`
outside the exceptional family (`n = s²` a `k`-th power, `A ⊆ F s`), `|A| ≤ 4`.
Tsang–Yip (Theorem 1.1) prove `|A| ≤ 6` under the same hypotheses. -/
theorem card_le_four_of_eighteen_le [IsAlgClosed F] [CharZero F] {k : ℕ} (hk : 18 ≤ k)
    {n : F[X]} (hn : n ≠ 0) {A : Finset F[X]} (hA : PolyHasPropertyD k n A)
    (hexc : ¬ ∃ s : F[X], n = s ^ 2 ∧ (∃ f : F[X], n = f ^ k) ∧ ∀ a ∈ A, IsMul a s) :
    A.card ≤ 4 :=
  card_le_four (sixTermRigid_of_eighteen_le hk) (by omega) hn hA hexc

end DiophantineTuples
