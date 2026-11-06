import Mathlib

/-!
# Dujella unicity: `q`-adic direction of an element of `ℤ[√d]`

Fix a prime `q` and `l : ℤ_[q]` with `l * l = d`. The two ring maps `ℤ√d → ℤ_[q]`
sending `√d ↦ ±l` give valuations `vP`, `vM`; their difference `dir` is the signed
`q`-adic "direction" of an element (the exponent of one prime above `q` minus the other).
-/

namespace DujellaUnicity

open PadicInt

variable {q : ℕ} [hq : Fact q.Prime] {d : ℤ}

/-- `√d ↦ l`. -/
noncomputable def phiP (l : ℤ_[q]) (hl : l * l = d) : ℤ√d →+* ℤ_[q] :=
  Zsqrtd.lift ⟨l, by simpa using hl⟩

/-- `√d ↦ -l`. -/
noncomputable def phiM (l : ℤ_[q]) (hl : l * l = d) : ℤ√d →+* ℤ_[q] :=
  Zsqrtd.lift ⟨-l, by simpa using hl⟩

noncomputable def vP (l : ℤ_[q]) (hl : l * l = d) (γ : ℤ√d) : ℕ := (phiP l hl γ).valuation
noncomputable def vM (l : ℤ_[q]) (hl : l * l = d) (γ : ℤ√d) : ℕ := (phiM l hl γ).valuation
/-- signed direction -/
noncomputable def dir (l : ℤ_[q]) (hl : l * l = d) (γ : ℤ√d) : ℤ :=
  (vP l hl γ : ℤ) - vM l hl γ

variable (l : ℤ_[q]) (hl : l * l = d)

theorem phiP_apply (γ : ℤ√d) : phiP l hl γ = (γ.re : ℤ_[q]) + (γ.im : ℤ_[q]) * l := by
  rfl
theorem phiM_apply (γ : ℤ√d) : phiM l hl γ = (γ.re : ℤ_[q]) - (γ.im : ℤ_[q]) * l := by
  change (γ.re : ℤ_[q]) + (γ.im : ℤ_[q]) * (-l) = _
  ring

theorem phiP_mul_phiM (γ : ℤ√d) : phiP l hl γ * phiM l hl γ = (γ.norm : ℤ_[q]) := by
  rw [phiP_apply, phiM_apply, Zsqrtd.norm_def]
  push_cast
  rw [← hl]
  ring

theorem phiP_ne_zero (hns : ∀ n : ℤ, d ≠ n * n) {γ : ℤ√d} (hγ : γ ≠ 0) : phiP l hl γ ≠ 0 := by
  intro h
  have := phiP_mul_phiM l hl γ
  rw [h, zero_mul, eq_comm, Int.cast_eq_zero, Zsqrtd.norm_eq_zero hns] at this
  exact hγ this
theorem phiM_ne_zero (hns : ∀ n : ℤ, d ≠ n * n) {γ : ℤ√d} (hγ : γ ≠ 0) : phiM l hl γ ≠ 0 := by
  intro h
  have := phiP_mul_phiM l hl γ
  rw [h, mul_zero, eq_comm, Int.cast_eq_zero, Zsqrtd.norm_eq_zero hns] at this
  exact hγ this

theorem phiP_add_phiM (γ : ℤ√d) : phiP l hl γ + phiM l hl γ = 2 * (γ.re : ℤ_[q]) := by
  rw [phiP_apply, phiM_apply]; ring

theorem phiP_sub_phiM (γ : ℤ√d) :
    phiP l hl γ - phiM l hl γ = 2 * ((γ.im : ℤ_[q]) * l) := by
  rw [phiP_apply, phiM_apply]; ring

omit hl in
theorem valuation_intCast_eq_padicValInt (n : ℤ) :
    ((n : ℤ_[q]).valuation : ℤ) = padicValInt q n := by
  have h := valuation_coe (p := q) (n : ℤ_[q])
  rw [coe_intCast, Padic.valuation_intCast] at h
  exact h.symm

omit hl in
theorem valuation_eq_zero_of_isUnit {x : ℤ_[q]} (hx : IsUnit x) : x.valuation = 0 := by
  by_contra h
  have : (q : ℤ_[q]) ^ 1 ∣ x := Ideal.mem_span_singleton.mp
    ((mem_span_pow_iff_le_valuation x hx.ne_zero 1).mpr (Nat.one_le_iff_ne_zero.mpr h))
  rw [pow_one, ← norm_lt_one_iff_dvd, ← not_isUnit_iff] at this
  exact this hx

omit hl in
theorem valuation_neg' (x : ℤ_[q]) : (-x).valuation = x.valuation := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [neg_eq_neg_one_mul, valuation_mul (by simp) hx,
    valuation_eq_zero_of_isUnit isUnit_one.neg, zero_add]

omit hl in
theorem pow_dvd_of_le_valuation {x : ℤ_[q]} {n : ℕ} (h : n ≤ x.valuation) :
    (q : ℤ_[q]) ^ n ∣ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact dvd_zero _
  exact Ideal.mem_span_singleton.mp ((mem_span_pow_iff_le_valuation x hx n).mpr h)

omit hl in
theorem one_le_valuation_of_dvd {x : ℤ_[q]} (hx : x ≠ 0) (h : (q : ℤ_[q]) ∣ x) :
    1 ≤ x.valuation :=
  (mem_span_pow_iff_le_valuation x hx 1).mp (Ideal.mem_span_singleton.mpr (by rwa [pow_one]))

omit hl in
theorem int_dvd_of_dvd {a : ℤ} (h : (q : ℤ_[q]) ∣ (a : ℤ_[q])) : (q : ℤ) ∣ a := by
  have := (pow_p_dvd_int_iff 1 a).mp (by rwa [pow_one])
  simpa using this

omit hl in
theorem isUnit_two_of_ne (hq2 : q ≠ 2) : IsUnit (2 : ℤ_[q]) := by
  by_contra h
  rw [not_isUnit_iff, show (2 : ℤ_[q]) = ((2 : ℤ) : ℤ_[q]) by norm_num,
    norm_int_lt_one_iff_dvd] at h
  have : q ∣ 2 := by exact_mod_cast h
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).mp this)

omit hl in
theorem not_dvd_re_im {γ : ℤ√d} (hprim : Int.gcd γ.re γ.im = 1) (hre : (q : ℤ) ∣ γ.re)
    (him : (q : ℤ) ∣ γ.im) : False := by
  have := Int.dvd_coe_gcd hre him
  rw [hprim] at this
  have : q ∣ 1 := by exact_mod_cast this
  exact hq.out.one_lt.ne' (Nat.dvd_one.mp this)

/-- `vP + vM` is the `q`-adic valuation of the norm. -/
theorem vP_add_vM (hns : ∀ n : ℤ, d ≠ n * n) {γ : ℤ√d} (hγ : γ ≠ 0) :
    vP l hl γ + vM l hl γ = padicValInt q γ.norm := by
  unfold vP vM
  rw [← valuation_mul (phiP_ne_zero l hl hns hγ) (phiM_ne_zero l hl hns hγ), phiP_mul_phiM]
  exact_mod_cast valuation_intCast_eq_padicValInt γ.norm

theorem dir_mul (hns : ∀ n : ℤ, d ≠ n * n) {γ δ : ℤ√d} (hγ : γ ≠ 0) (hδ : δ ≠ 0) :
    dir l hl (γ * δ) = dir l hl γ + dir l hl δ := by
  unfold dir vP vM
  rw [map_mul, map_mul, valuation_mul (phiP_ne_zero l hl hns hγ) (phiP_ne_zero l hl hns hδ),
    valuation_mul (phiM_ne_zero l hl hns hγ) (phiM_ne_zero l hl hns hδ)]
  push_cast; ring

theorem dir_star (γ : ℤ√d) : dir l hl (star γ) = - dir l hl γ := by
  have h1 : phiP l hl (star γ) = phiM l hl γ := by
    rw [phiP_apply, phiM_apply, Zsqrtd.re_star, Zsqrtd.im_star]; push_cast; ring
  have h2 : phiM l hl (star γ) = phiP l hl γ := by
    rw [phiP_apply, phiM_apply, Zsqrtd.re_star, Zsqrtd.im_star]; push_cast; ring
  unfold dir vP vM
  rw [h1, h2]; ring

theorem dir_neg (γ : ℤ√d) : dir l hl (-γ) = dir l hl γ := by
  unfold dir vP vM
  rw [map_neg, map_neg, valuation_neg', valuation_neg']

theorem dir_intCast (c : ℤ) : dir l hl (c : ℤ√d) = 0 := by
  unfold dir vP vM
  rw [map_intCast, map_intCast, sub_self]

/-- `dir` is unchanged by scaling by a nonzero integer. -/
theorem dir_intCast_mul (hns : ∀ n : ℤ, d ≠ n * n) (c : ℤ) (hc : c ≠ 0) {γ : ℤ√d}
    (hγ : γ ≠ 0) : dir l hl ((c : ℤ√d) * γ) = dir l hl γ := by
  have hc' : (c : ℤ√d) ≠ 0 := by
    intro h
    have := congrArg Zsqrtd.re h
    simp at this
    exact hc this
  rw [dir_mul l hl hns hc' hγ, dir_intCast, zero_add]

/-- a unit (norm `±1`) has direction `0`. -/
theorem dir_of_norm_eq_one (hns : ∀ n : ℤ, d ≠ n * n) {γ : ℤ√d} (h : γ.norm = 1 ∨ γ.norm = -1) :
    dir l hl γ = 0 := by
  have hu : IsUnit (phiP l hl γ * phiM l hl γ) := by
    rw [phiP_mul_phiM]; rcases h with h | h <;> rw [h] <;> simp
  unfold dir vP vM
  rw [valuation_eq_zero_of_isUnit (isUnit_of_mul_isUnit_left hu),
    valuation_eq_zero_of_isUnit (isUnit_of_mul_isUnit_right hu)]
  simp

/-- For odd `q` with `l` a unit, a primitive element has `min (vP, vM) = 0`. -/
theorem min_eq_zero_of_primitive (hq2 : q ≠ 2) (hlu : IsUnit l) (hns : ∀ n : ℤ, d ≠ n * n)
    {γ : ℤ√d} (hprim : Int.gcd γ.re γ.im = 1) : vP l hl γ = 0 ∨ vM l hl γ = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have dP : (q : ℤ_[q]) ∣ phiP l hl γ := by
    simpa using pow_dvd_of_le_valuation (n := 1) (Nat.one_le_iff_ne_zero.mpr h1)
  have dM : (q : ℤ_[q]) ∣ phiM l hl γ := by
    simpa using pow_dvd_of_le_valuation (n := 1) (Nat.one_le_iff_ne_zero.mpr h2)
  have h2u := isUnit_two_of_ne hq2
  have hre : (q : ℤ_[q]) ∣ (γ.re : ℤ_[q]) := by
    have := dvd_add dP dM
    rwa [phiP_add_phiM, h2u.dvd_mul_left] at this
  have him : (q : ℤ_[q]) ∣ (γ.im : ℤ_[q]) := by
    have := dvd_sub dP dM
    rwa [phiP_sub_phiM, h2u.dvd_mul_left, hlu.dvd_mul_right] at this
  exact not_dvd_re_im hprim (int_dvd_of_dvd hre) (int_dvd_of_dvd him)

/-- For `q = 2` with `l` a unit, a primitive element has `min (vP, vM) ≤ 1`. -/
theorem min_le_one_of_primitive (hq2 : q = 2) (hlu : IsUnit l) (hns : ∀ n : ℤ, d ≠ n * n)
    {γ : ℤ√d} (hprim : Int.gcd γ.re γ.im = 1) : vP l hl γ ≤ 1 ∨ vM l hl γ ≤ 1 := by
  subst hq2
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have dP : ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ phiP l hl γ := pow_dvd_of_le_valuation h1
  have dM : ((2 : ℕ) : ℤ_[2]) ^ 2 ∣ phiM l hl γ := pow_dvd_of_le_valuation h2
  have h4 : ((2 : ℕ) : ℤ_[2]) ^ 2 = 2 * 2 := by norm_num
  rw [h4] at dP dM
  have h20 : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
  have hre : ((2 : ℕ) : ℤ_[2]) ∣ (γ.re : ℤ_[2]) := by
    have := dvd_add dP dM
    rw [phiP_add_phiM] at this
    rw [Nat.cast_ofNat]; exact (mul_dvd_mul_iff_left h20).mp this
  have him : ((2 : ℕ) : ℤ_[2]) ∣ (γ.im : ℤ_[2]) := by
    have := dvd_sub dP dM
    rw [phiP_sub_phiM] at this
    rw [Nat.cast_ofNat]; exact hlu.dvd_mul_right.mp ((mul_dvd_mul_iff_left h20).mp this)
  exact not_dvd_re_im hprim (int_dvd_of_dvd hre) (int_dvd_of_dvd him)

/-- For `q = 2` with `l` a unit and even norm, both valuations are positive. -/
theorem one_le_min_of_two_dvd_norm (hq2 : q = 2) (hlu : IsUnit l) (hns : ∀ n : ℤ, d ≠ n * n)
    {γ : ℤ√d} (hγ : γ ≠ 0) (h2 : (2 : ℤ) ∣ γ.norm) : 1 ≤ vP l hl γ ∧ 1 ≤ vM l hl γ := by
  subst hq2
  have hP := phiP_ne_zero l hl hns hγ
  have hM := phiM_ne_zero l hl hns hγ
  have hprod : ((2 : ℕ) : ℤ_[2]) ∣ phiP l hl γ * phiM l hl γ := by
    rw [phiP_mul_phiM]
    have := (pow_p_dvd_int_iff (p := 2) 1 γ.norm).mpr (by simpa using h2)
    simpa using this
  have hdiff : ((2 : ℕ) : ℤ_[2]) ∣ phiP l hl γ - phiM l hl γ := by
    rw [phiP_sub_phiM, Nat.cast_ofNat]; exact dvd_mul_right _ _
  unfold vP vM
  rcases prime_p.dvd_or_dvd hprod with h | h
  · have h' : ((2 : ℕ) : ℤ_[2]) ∣ phiM l hl γ := by
      have := dvd_sub h hdiff
      rwa [sub_sub_cancel] at this
    exact ⟨one_le_valuation_of_dvd hP h, one_le_valuation_of_dvd hM h'⟩
  · have h' : ((2 : ℕ) : ℤ_[2]) ∣ phiP l hl γ := by
      have := dvd_add hdiff h
      rwa [sub_add_cancel] at this
    exact ⟨one_le_valuation_of_dvd hP h', one_le_valuation_of_dvd hM h⟩

omit hl in
/-- valuation of `c + l` for odd `q`, when `l ≡ 1 (mod q)` and `q ∤ c + 1`. -/
theorem valuation_intCast_add_odd (hq2 : q ≠ 2) (hl1 : (q : ℤ_[q]) ∣ l - 1) (c : ℤ)
    (hc : ¬ (q : ℤ) ∣ c + 1) : ((c : ℤ_[q]) + l).valuation = 0 := by
  apply valuation_eq_zero_of_isUnit
  by_contra hnu
  rw [not_isUnit_iff, norm_lt_one_iff_dvd] at hnu
  have := dvd_sub hnu hl1
  rw [show (c : ℤ_[q]) + l - (l - 1) = ((c + 1 : ℤ) : ℤ_[q]) by push_cast; ring] at this
  exact hc (int_dvd_of_dvd this)

omit hl in
/-- valuation of `c + l` for `q = 2`, when `l ≡ 1 (mod 4)` and `c ≡ 1 (mod 4)`. -/
theorem valuation_intCast_add_two (hq2 : q = 2) (hl1 : (4 : ℤ_[q]) ∣ l - 1) (c : ℤ)
    (hc : c % 4 = 1) : ((c : ℤ_[q]) + l).valuation = 1 := by
  subst hq2
  obtain ⟨t, ht⟩ := hl1
  have hc' : (4 : ℤ) ∣ c - 1 := by omega
  obtain ⟨s, hs⟩ := hc'
  have hl' : l = 4 * t + 1 := by rw [← ht]; ring
  have hc'' : c = 4 * s + 1 := by omega
  have e : (c : ℤ_[2]) + l = 2 * (1 + 2 * ((s : ℤ_[2]) + t)) := by
    rw [hl', hc'']; push_cast; ring
  have hu : IsUnit (1 + 2 * ((s : ℤ_[2]) + t)) := by
    by_contra hnu
    rw [not_isUnit_iff, norm_lt_one_iff_dvd] at hnu
    have h2 : ((2 : ℕ) : ℤ_[2]) ∣ 2 * ((s : ℤ_[2]) + t) := by
      rw [Nat.cast_ofNat]; exact dvd_mul_right _ _
    have := (dvd_add_left h2).mp hnu
    rw [← norm_lt_one_iff_dvd] at this
    simp at this
  rw [e, valuation_mul two_ne_zero hu.ne_zero, valuation_eq_zero_of_isUnit hu, add_zero]
  simpa using valuation_p (p := 2)

/-- Hensel: a square root of `k^2+1` that is `≡ 1 (mod q)` when `q` is odd and `q ∣ k`. -/
theorem exists_sqrt_odd (hq2 : q ≠ 2) (k : ℤ) (hk : (q : ℤ) ∣ k) :
    ∃ l : ℤ_[q], l * l = ((k ^ 2 + 1 : ℤ) : ℤ_[q]) ∧ (q : ℤ_[q]) ∣ l - 1 := by
  set F : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C (k ^ 2 + 1) with hF
  have hev : ∀ z : ℤ_[q], F.aeval z = z * z - ((k ^ 2 + 1 : ℤ) : ℤ_[q]) := by
    intro z; simp [hF, pow_two]
  have hder : ∀ z : ℤ_[q], F.derivative.aeval z = 2 * z := by
    intro z
    rw [hF, Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.derivative_X_pow]
    rw [sub_zero, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    simp
  have h2 : ‖(2 : ℤ_[q])‖ = 1 := isUnit_iff.mp (isUnit_two_of_ne hq2)
  have hk' : ‖(k : ℤ_[q])‖ < 1 := (norm_int_lt_one_iff_dvd k).mpr hk
  have hnorm : ‖F.aeval (1 : ℤ_[q])‖ < ‖F.derivative.aeval (1 : ℤ_[q])‖ ^ 2 := by
    rw [hev, hder, mul_one, mul_one, h2, one_pow]
    have : (1 : ℤ_[q]) - ((k ^ 2 + 1 : ℤ) : ℤ_[q]) = -((k : ℤ_[q]) * k) := by
      push_cast; ring
    rw [this, norm_neg, norm_mul]
    nlinarith [norm_nonneg (k : ℤ_[q])]
  obtain ⟨z, hz, hz1, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_, ?_⟩
  · rw [hev] at hz; exact sub_eq_zero.mp hz
  · rw [hder, mul_one, h2] at hz1; exact (norm_lt_one_iff_dvd _).mp hz1

/-- Hensel: a square root of `k^2+1` that is `≡ 1 (mod 4)` when `q = 2` and `4 ∣ k`. -/
theorem exists_sqrt_two (hq2 : q = 2) (k : ℤ) (hk : (4 : ℤ) ∣ k) :
    ∃ l : ℤ_[q], l * l = ((k ^ 2 + 1 : ℤ) : ℤ_[q]) ∧ (4 : ℤ_[q]) ∣ l - 1 := by
  subst hq2
  set F : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C (k ^ 2 + 1) with hF
  have hev : ∀ z : ℤ_[2], F.aeval z = z * z - ((k ^ 2 + 1 : ℤ) : ℤ_[2]) := by
    intro z; simp [hF, pow_two]
  have hder : ∀ z : ℤ_[2], F.derivative.aeval z = 2 * z := by
    intro z
    rw [hF, Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.derivative_X_pow]
    rw [sub_zero, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    simp
  have h2 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
    have := norm_p (p := 2); simpa using this
  have hk' : ‖(k : ℤ_[2])‖ ≤ 1 / 4 := by
    have := (norm_int_le_pow_iff_dvd (p := 2) (k := k) (n := 2)).mpr (by simpa using hk)
    norm_num at this ⊢; linarith
  have hnorm : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hev, hder, mul_one, mul_one, h2]
    have : (1 : ℤ_[2]) - ((k ^ 2 + 1 : ℤ) : ℤ_[2]) = -((k : ℤ_[2]) * k) := by
      push_cast; ring
    rw [this, norm_neg, norm_mul]
    nlinarith [norm_nonneg (k : ℤ_[2])]
  obtain ⟨z, hz, hz1, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_, ?_⟩
  · rw [hev] at hz; exact sub_eq_zero.mp hz
  · rw [hder, mul_one, h2] at hz1
    have h3 : ‖z - 1‖ < ((2 : ℕ) : ℝ) ^ (-1 : ℤ) := by norm_num; linarith
    rw [norm_lt_pow_iff_norm_le_pow_sub_one, show (-1 - 1 : ℤ) = -((2 : ℕ) : ℤ) by norm_num,
      norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at h3
    norm_num at h3
    exact h3

end DujellaUnicity
