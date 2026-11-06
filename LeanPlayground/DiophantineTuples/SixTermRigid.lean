module

public import LeanPlayground.DiophantineTuples.MasonStothersMany
public import LeanPlayground.DiophantineTuples.PolyFive
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

@[expose] public noncomputable section

/-!
# Six-term rigidity for `k ≥ 24` (Tsang–Yip, Claims 4.8–4.9)

Let `F` be algebraically closed of characteristic `0`. If
`q₁ᵏ + q₂ᵏ + q₃ᵏ = r₁ᵏ + r₂ᵏ + r₃ᵏ` with `q₁q₂q₃ = r₁r₂r₃`, all terms nonzero and no `qᵢᵏ`
equal to an `rⱼᵏ`, then for `k ≥ 24` all six `k`-th powers are associated
(`sixTermRigid_of_le`, i.e. `SixTermRigid F k`). Hence the bound `|A| ≤ 4` of `card_le_four`
holds unconditionally for `k ≥ 24` (`card_le_four_of_le`).

The proof follows Tsang–Yip (arXiv:2607.01165, Claims 4.8–4.9):
* group the six terms into proportionality classes (by monic part); if a class had a nonzero
  collapsed coefficient, Corollary 4.2 (`k_lt_of_relation`) with at most `6` classes would give
  `k < 6 · 4 = 24` (`classSum_eq_zero`);
* so every class has zero collapsed coefficient; then no class is a singleton or a
  `{qᵢ, rⱼ}` pair, three classes are impossible by parity, and two classes `R ≠ S` are ruled out
  by the product identity, which forces `Rᵈ = Sᵈ` for some `d ≠ 0`.

Tsang–Yip reach `k ≥ 18` in the six-class case using a sharper valuation count
(their Proposition 4.4); here Corollary 4.2 is used for all cases.
-/

namespace DiophantineTuples

open Polynomial Finset

variable {F : Type*} [Field F]

/-- The monic polynomial proportional to `p` (or `0`). -/
def monicPart (p : F[X]) : F[X] := C (p.leadingCoeff)⁻¹ * p

lemma monicPart_monic {p : F[X]} (hp : p ≠ 0) : (monicPart p).Monic :=
  monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hp))

lemma eq_C_mul_monicPart {p : F[X]} (hp : p ≠ 0) : p = C p.leadingCoeff * monicPart p := by
  rw [monicPart, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (leadingCoeff_ne_zero.2 hp), C_1,
    one_mul]

lemma monicPart_C_mul {a : F} (ha : a ≠ 0) (p : F[X]) : monicPart (C a * p) = monicPart p := by
  rw [monicPart, monicPart, leadingCoeff_mul, leadingCoeff_C, ← mul_assoc, ← C_mul, mul_inv,
    mul_comm a⁻¹, mul_assoc, inv_mul_cancel₀ ha, mul_one]

lemma monicPart_of_monic {p : F[X]} (hp : p.Monic) : monicPart p = p := by
  rw [monicPart, hp.leadingCoeff, inv_one, C_1, one_mul]

lemma associated_monicPart {p : F[X]} (hp : p ≠ 0) : Associated p (monicPart p) := by
  refine associated_of_dvd_dvd ⟨C p.leadingCoeff⁻¹, by rw [monicPart, mul_comm]⟩
    ⟨C p.leadingCoeff, ?_⟩
  conv_lhs => rw [eq_C_mul_monicPart hp]
  exact mul_comm _ _

lemma monic_eq_of_pow_eq {R S : F[X]} (hR : R.Monic) (hS : S.Monic) {d : ℕ} (hd : d ≠ 0)
    (h : R ^ d = S ^ d) : R = S :=
  eq_of_monic_of_associated hR hS (associated_of_dvd_dvd
    ((IsIntegrallyClosed.pow_dvd_pow_iff hd).1 (by rw [h]))
    ((IsIntegrallyClosed.pow_dvd_pow_iff hd).1 (by rw [h])))

/-- From `Rᵃ Sᵇ = Rᵃ' Sᵇ'` with `a + b = a' + b'` and `R, S` monic: `a = a'` or `R = S`. -/
lemma eq_or_eq_of_pow_mul_pow {R S : F[X]} (hR : R.Monic) (hS : S.Monic) {a b a' b' : ℕ}
    (h : R ^ a * S ^ b = R ^ a' * S ^ b') (hab : a + b = a' + b') : a = a' ∨ R = S := by
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · right
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hb : b = b' + (d + 1) := by omega
    subst hb
    have h0 : R ^ a * S ^ b' ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hR.ne_zero) (pow_ne_zero _ hS.ne_zero)
    refine (monic_eq_of_pow_eq hR hS (Nat.succ_ne_zero d) (mul_left_cancel₀ h0 ?_)).symm.symm
    have : R ^ a * S ^ b' * S ^ (d + 1) = R ^ a * S ^ b' * R ^ (d + 1) := by
      calc R ^ a * S ^ b' * S ^ (d + 1) = R ^ a * S ^ (b' + (d + 1)) := by ring
        _ = R ^ (a + d + 1) * S ^ b' := h
        _ = R ^ a * S ^ b' * R ^ (d + 1) := by ring
    exact this.symm
  · exact Or.inl heq
  · right
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have hb : b' = b + (d + 1) := by omega
    subst hb
    have h0 : R ^ a' * S ^ b ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hR.ne_zero) (pow_ne_zero _ hS.ne_zero)
    refine monic_eq_of_pow_eq hR hS (Nat.succ_ne_zero d) (mul_left_cancel₀ h0 ?_)
    calc R ^ a' * S ^ b * R ^ (d + 1) = R ^ (a' + d + 1) * S ^ b := by ring
      _ = R ^ a' * S ^ (b + (d + 1)) := h
      _ = R ^ a' * S ^ b * S ^ (d + 1) := by ring

open scoped Classical in
/-- **Collapsing a relation by proportionality classes.** If `∑ cᵢ pᵢᵏ = 0` with nonzero `pᵢ` and
some class `{pᵢ ∼ g}` has nonzero collapsed coefficient `∑_{pᵢ ∼ g} cᵢ lc(pᵢ)ᵏ`, then
`k < t(t-2)`, where `t` is the number of classes (Corollary 4.2 for the class representatives). -/
theorem lt_of_classSum_ne_zero [IsAlgClosed F] [CharZero F] {s k : ℕ} (hk : 0 < k)
    (p : Fin s → F[X]) (c : Fin s → F) (hp : ∀ i, p i ≠ 0)
    (hrel : ∑ i, C (c i) * p i ^ k = 0) (g : F[X])
    (hg : ∑ i with monicPart (p i) = g, c i * (p i).leadingCoeff ^ k ≠ 0) :
    k < (univ.image fun i => monicPart (p i)).card *
      ((univ.image fun i => monicPart (p i)).card - 2) := by
  classical
  set M := univ.image fun i => monicPart (p i)
  have hgM : g ∈ M := by
    obtain ⟨i, hi, -⟩ := exists_ne_zero_of_sum_ne_zero hg
    exact mem_image.2 ⟨i, mem_univ _, (mem_filter.1 hi).2⟩
  have hmon : ∀ h ∈ M, h.Monic := by
    intro h hh
    obtain ⟨i, -, rfl⟩ := mem_image.1 hh
    exact monicPart_monic (hp i)
  set e := M.equivFin
  set P' : Fin M.card → F[X] := fun x => (e.symm x : F[X])
  set c' : Fin M.card → F :=
    fun x => ∑ i with monicPart (p i) = P' x, c i * (p i).leadingCoeff ^ k
  have hrel' : ∑ x, C (c' x) * P' x ^ k = 0 := by
    have h1 : ∑ x, C (c' x) * P' x ^ k = ∑ h ∈ M,
        C (∑ i with monicPart (p i) = h, c i * (p i).leadingCoeff ^ k) * h ^ k := by
      rw [← sum_coe_sort M]
      exact Equiv.sum_comp e.symm (fun h : M =>
        C (∑ i with monicPart (p i) = (h : F[X]), c i * (p i).leadingCoeff ^ k) * (h : F[X]) ^ k)
    rw [h1, ← hrel]
    simp_rw [map_sum, sum_mul]
    calc ∑ h ∈ M, ∑ i with monicPart (p i) = h, C (c i * (p i).leadingCoeff ^ k) * h ^ k
        = ∑ h ∈ M, ∑ i with monicPart (p i) = h,
            C (c i * (p i).leadingCoeff ^ k) * monicPart (p i) ^ k :=
          sum_congr rfl fun h _ => sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2]
      _ = ∑ i, C (c i * (p i).leadingCoeff ^ k) * monicPart (p i) ^ k :=
          sum_fiberwise_of_maps_to (fun i _ => mem_image_of_mem _ (mem_univ i)) _
      _ = ∑ i, C (c i) * p i ^ k := sum_congr rfl fun i _ => by
          conv_rhs => rw [eq_C_mul_monicPart (hp i)]
          rw [mul_pow, ← C_pow, C_mul]; ring
  set x0 := e ⟨g, hgM⟩
  have hPx0 : P' x0 = g := by simp [P', x0]
  have hlt := k_lt_of_relation hk P' c' (fun x => (hmon _ (e.symm x).2).ne_zero) hrel' x0
    (by simpa [c', hPx0] using hg) (by
      intro j hj a h
      apply hj
      apply e.symm.injective
      apply Subtype.ext
      have h1 := hmon _ (e.symm x0).2
      have h2 := hmon _ (e.symm j).2
      have hlc := congrArg leadingCoeff h
      simp only [P', leadingCoeff_mul, leadingCoeff_C, h1.leadingCoeff, h2.leadingCoeff,
        mul_one] at hlc
      have h' : P' x0 = P' j := by rw [h, ← hlc, C_1, one_mul]
      exact h'.symm)
  exact hlt

open scoped Classical in
/-- **Collapsed coefficients vanish (Tsang–Yip, Claim 4.8).** If `∑ cᵢ pᵢᵏ = 0` with `s` nonzero
terms and `k ≥ s(s-2)`, then for each monic `g` the coefficient `∑_{pᵢ ∼ g} cᵢ lc(pᵢ)ᵏ` of `gᵏ`
vanishes. -/
theorem classSum_eq_zero [IsAlgClosed F] [CharZero F] {s k : ℕ} (hk : 0 < k)
    (hks : s * (s - 2) ≤ k) (p : Fin s → F[X]) (c : Fin s → F) (hp : ∀ i, p i ≠ 0)
    (hrel : ∑ i, C (c i) * p i ^ k = 0) (g : F[X]) :
    ∑ i with monicPart (p i) = g, c i * (p i).leadingCoeff ^ k = 0 := by
  by_contra hg
  have hlt := lt_of_classSum_ne_zero hk p c hp hrel g hg
  have hcard : (univ.image fun i => monicPart (p i)).card ≤ s := card_image_le.trans (by simp)
  have := Nat.mul_le_mul hcard (Nat.sub_le_sub_right hcard 2)
  omega

lemma sum_filter_fin_add {m n : ℕ} {M : Type*} [AddCommMonoid M] (P : Fin (m + n) → Prop)
    [DecidablePred P] (f : Fin (m + n) → M) :
    ∑ i with P i, f i = ∑ i : Fin m with P (Fin.castAdd n i), f (Fin.castAdd n i) +
      ∑ j : Fin n with P (Fin.natAdd m j), f (Fin.natAdd m j) := by
  simp only [sum_filter]
  exact Fin.sum_univ_add _

lemma append_ne_zero {q r : Fin 3 → F[X]} (hq : ∀ i, q i ≠ 0) (hr : ∀ j, r j ≠ 0) :
    ∀ i, Fin.append q r i ≠ 0 := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; exact hq i
  · rw [Fin.append_right]; exact hr j

lemma append_relation {k : ℕ} {q r : Fin 3 → F[X]} (hsum : ∑ i, q i ^ k = ∑ j, r j ^ k) :
    ∑ i, C (Fin.append (fun _ => (1 : F)) (fun _ => -1) i) * Fin.append q r i ^ k = 0 := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, C_1, one_mul, C_neg, neg_mul,
    sum_neg_distrib, hsum, add_neg_cancel]

open scoped Classical in
/-- **Six-term rigidity from vanishing collapsed coefficients** (Tsang–Yip, Claim 4.9). If every
proportionality class of the six terms has zero collapsed coefficient, the six `k`-th powers are
associated. -/
theorem sixTermRigid_of_classSum {k : ℕ} (hk0 : 0 < k)
    (H : ∀ q r : Fin 3 → F[X], (∀ i, q i ≠ 0) → (∀ j, r j ≠ 0) → (∀ i j, q i ^ k ≠ r j ^ k) →
      ∑ i, q i ^ k = ∑ j, r j ^ k → ∏ i, q i = ∏ j, r j → ∀ g : F[X],
      ∑ i with monicPart (Fin.append q r i) = g,
        Fin.append (fun _ => (1 : F)) (fun _ => -1) i * (Fin.append q r i).leadingCoeff ^ k = 0) :
    SixTermRigid F k := by
  classical
  intro q r hq hr hqr hsum hprod
  set p : Fin (3 + 3) → F[X] := Fin.append q r
  set c : Fin (3 + 3) → F := Fin.append (fun _ => 1) (fun _ => -1)
  set mq := fun i => monicPart (q i)
  set mr := fun j => monicPart (r j)
  -- (F1) collapsed coefficients
  have F1 : ∀ g, ∑ i with mq i = g, (q i).leadingCoeff ^ k =
      ∑ j with mr j = g, (r j).leadingCoeff ^ k := by
    intro g
    have h := H q r hq hr hqr hsum hprod g
    rw [sum_filter_fin_add] at h
    simp only [c, Fin.append_left, Fin.append_right, one_mul, neg_one_mul,
      sum_neg_distrib] at h
    linear_combination h
  set nq := fun g => #{i | mq i = g}
  set nr := fun g => #{j | mr j = g}
  -- (F2) no singleton class, no class `{qᵢ, rⱼ}`
  have F2a : ∀ g, nq g = 1 → nr g = 0 → False := by
    intro g h1 h0
    obtain ⟨i, hi⟩ := card_eq_one.1 h1
    have h := F1 g
    rw [hi, card_eq_zero.1 h0, sum_singleton, sum_empty] at h
    exact hq i (leadingCoeff_eq_zero.1 (pow_eq_zero_iff hk0.ne' |>.1 h))
  have F2b : ∀ g, nq g = 0 → nr g = 1 → False := by
    intro g h0 h1
    obtain ⟨j, hj⟩ := card_eq_one.1 h1
    have h := F1 g
    rw [hj, card_eq_zero.1 h0, sum_singleton, sum_empty] at h
    exact hr j (leadingCoeff_eq_zero.1 (pow_eq_zero_iff hk0.ne' |>.1 h.symm))
  have F2c : ∀ g, nq g = 1 → nr g = 1 → False := by
    intro g h1 h1'
    obtain ⟨i, hi⟩ := card_eq_one.1 h1
    obtain ⟨j, hj⟩ := card_eq_one.1 h1'
    have h := F1 g
    rw [hi, hj, sum_singleton, sum_singleton] at h
    have hgi : mq i = g := (mem_filter.1 (hi ▸ mem_singleton_self i : i ∈ _)).2
    have hgj : mr j = g := (mem_filter.1 (hj ▸ mem_singleton_self j : j ∈ _)).2
    apply hqr i j
    rw [eq_C_mul_monicPart (hq i), eq_C_mul_monicPart (hr j), mul_pow, mul_pow, ← C_pow, ← C_pow,
      h]
    simp only [mq, mr] at hgi hgj
    rw [hgi, hgj]
  -- (F3) the monic parts have equal products
  have hprodq : ∏ i, q i = C (∏ i, (q i).leadingCoeff) * ∏ i, mq i := by
    rw [map_prod, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => eq_C_mul_monicPart (hq i)
  have hprodr : ∏ j, r j = C (∏ j, (r j).leadingCoeff) * ∏ j, mr j := by
    rw [map_prod, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ => eq_C_mul_monicPart (hr j)
  have hmq : (∏ i, mq i).Monic := monic_prod_of_monic _ _ fun i _ => monicPart_monic (hq i)
  have hmr : (∏ j, mr j).Monic := monic_prod_of_monic _ _ fun j _ => monicPart_monic (hr j)
  have F3 : ∏ i, mq i = ∏ j, mr j := by
    have h := congrArg monicPart hprod
    rwa [hprodq, hprodr, monicPart_C_mul (prod_ne_zero_iff.2 fun i _ =>
      leadingCoeff_ne_zero.2 (hq i)), monicPart_C_mul (prod_ne_zero_iff.2 fun j _ =>
      leadingCoeff_ne_zero.2 (hr j)), monicPart_of_monic hmq, monicPart_of_monic hmr] at h
  -- the classes
  set M := univ.image mq ∪ univ.image mr
  have hqM : ∀ i, mq i ∈ M := fun i => mem_union_left _ (mem_image_of_mem _ (mem_univ i))
  have hrM : ∀ j, mr j ∈ M := fun j => mem_union_right _ (mem_image_of_mem _ (mem_univ j))
  have hMmon : ∀ g ∈ M, g.Monic := by
    intro g hg
    rcases mem_union.1 hg with hg | hg <;> obtain ⟨i, -, rfl⟩ := mem_image.1 hg
    · exact monicPart_monic (hq i)
    · exact monicPart_monic (hr i)
  have hpos : ∀ g ∈ M, 1 ≤ nq g + nr g := by
    intro g hg
    rcases mem_union.1 hg with hg | hg <;> obtain ⟨i, -, rfl⟩ := mem_image.1 hg
    · have : 0 < nq (mq i) := card_pos.2 ⟨i, mem_filter.2 ⟨mem_univ _, rfl⟩⟩
      omega
    · have : 0 < nr (mr i) := card_pos.2 ⟨i, mem_filter.2 ⟨mem_univ _, rfl⟩⟩
      omega
  have hsq : ∑ g ∈ M, nq g = 3 := by
    rw [← card_eq_sum_card_fiberwise fun i _ => hqM i]; simp
  have hsr : ∑ g ∈ M, nr g = 3 := by
    rw [← card_eq_sum_card_fiberwise fun j _ => hrM j]; simp
  have hprodM : ∏ g ∈ M, g ^ nq g = ∏ g ∈ M, g ^ nr g := by
    have h1 : ∏ i, mq i = ∏ g ∈ M, g ^ nq g := by
      rw [← prod_fiberwise_of_maps_to (fun i _ => hqM i) mq]
      exact prod_congr rfl fun g _ => by
        rw [prod_congr rfl fun i hi => (mem_filter.1 hi).2, prod_const]
    have h2 : ∏ j, mr j = ∏ g ∈ M, g ^ nr g := by
      rw [← prod_fiberwise_of_maps_to (fun j _ => hrM j) mr]
      exact prod_congr rfl fun g _ => by
        rw [prod_congr rfl fun j hj => (mem_filter.1 hj).2, prod_const]
    rw [← h1, ← h2, F3]
  -- at most one class
  have hM1 : M.card ≤ 1 := by
    by_contra! hM
    have h2 : ∀ g ∈ M, 2 ≤ nq g + nr g := by
      intro g hg
      have := hpos g hg
      by_contra! h
      rcases Nat.lt_or_ge (nq g) 1 with h' | h'
      · exact F2b g (by omega) (by omega)
      · exact F2a g (by omega) (by omega)
    have hs6 : ∑ g ∈ M, (nq g + nr g) = 6 := by rw [sum_add_distrib, hsq, hsr]
    have hle : M.card * 2 ≤ 6 := by
      rw [← hs6, ← smul_eq_mul]
      exact card_nsmul_le_sum _ _ _ h2
    rcases (by omega : M.card = 2 ∨ M.card = 3) with hc | hc
    · obtain ⟨R, S, hRS, hMRS⟩ := card_eq_two.1 hc
      have hR : R ∈ M := hMRS ▸ mem_insert_self _ _
      have hS : S ∈ M := hMRS ▸ mem_insert_of_mem (mem_singleton_self _)
      rw [hMRS, sum_pair hRS] at hsq hsr
      rw [hMRS, prod_pair hRS, prod_pair hRS] at hprodM
      rcases eq_or_eq_of_pow_mul_pow (hMmon R hR) (hMmon S hS) hprodM (by omega) with h | h
      · have := h2 R hR
        have := h2 S hS
        have := F2c R
        have := F2c S
        rcases (by omega : nq R = 1 ∨ nq S = 1) with h' | h'
        · exact F2c R h' (by omega)
        · exact F2c S h' (by omega)
      · exact hRS h
    · -- three classes of size two: each has an even number of `q`s
      have hall : ∀ g ∈ M, nq g + nr g = 2 := by
        intro g hg
        by_contra hne
        have h3 : 3 ≤ nq g + nr g := by have := h2 g hg; omega
        have := card_nsmul_le_sum (M.erase g) (fun g => nq g + nr g) 2
          fun g' hg' => h2 g' (mem_of_mem_erase hg')
        rw [card_erase_of_mem hg, hc, smul_eq_mul] at this
        have := add_sum_erase M (fun g => nq g + nr g) hg
        omega
      have heven : ∀ g ∈ M, 2 ∣ nq g := by
        intro g hg
        have := hall g hg
        have := F2c g
        rcases (by omega : nq g = 0 ∨ nq g = 1 ∨ nq g = 2) with h | h | h
        · rw [h]; exact dvd_zero 2
        · exact absurd (this h (by omega)) id
        · rw [h]
      have := dvd_sum heven
      rw [hsq] at this
      omega
  intro i j
  have heq : mq i = mr j := card_le_one.1 hM1 _ (hqM i) _ (hrM j)
  have hi := (associated_monicPart (hq i)).pow_pow (n := k)
  have hj := (associated_monicPart (hr j)).pow_pow (n := k)
  simp only [mq, mr] at heq
  rw [heq] at hi
  exact hi.trans hj.symm

/-- **Six-term rigidity for `k ≥ 24`** (Tsang–Yip, Claims 4.8–4.9, with Corollary 4.2 in place of
their Proposition 4.4). -/
theorem sixTermRigid_of_le [IsAlgClosed F] [CharZero F] {k : ℕ} (hk : 24 ≤ k) :
    SixTermRigid F k :=
  sixTermRigid_of_classSum (by omega) fun q r hq hr _ hsum _ g =>
    classSum_eq_zero (by omega) (by norm_num; omega) _ _ (append_ne_zero hq hr)
      (append_relation hsum) g

/-- **Polynomial `D_k(n)`-tuples have at most four elements for `k ≥ 24`, unconditionally.**
For `F` algebraically closed of characteristic `0`, `n ≠ 0` and `A ⊆ F[X]` with property `D_k(n)`
outside the exceptional family (`n = s²` a `k`-th power, `A ⊆ F s`), `|A| ≤ 4`.
Tsang–Yip (Theorem 1.1) prove `|A| ≤ 6` for `k ≥ 18`. -/
theorem card_le_four_of_le [IsAlgClosed F] [CharZero F] {k : ℕ} (hk : 24 ≤ k) {n : F[X]}
    (hn : n ≠ 0) {A : Finset F[X]} (hA : PolyHasPropertyD k n A)
    (hexc : ¬ ∃ s : F[X], n = s ^ 2 ∧ (∃ f : F[X], n = f ^ k) ∧ ∀ a ∈ A, IsMul a s) :
    A.card ≤ 4 :=
  card_le_four (sixTermRigid_of_le hk) (by omega) hn hA hexc

end DiophantineTuples
