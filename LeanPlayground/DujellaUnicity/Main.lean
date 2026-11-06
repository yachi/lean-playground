import LeanPlayground.DujellaUnicity.Lattice
import LeanPlayground.DujellaUnicity.SmallNorm
import LeanPlayground.DujellaUnicity.PadicDirection

/-!
# Dujella's unicity conjecture for `k = 2^a p^m`

Main theorem `dujella_unicity`: if `k = 2^a p^m` with `p` an odd prime, `a ≥ 2`, `m ≥ 1`
and `2k` not a perfect square (`a` even or `m` odd), then `x² - (k²+1) y² = k²` has at most one
solution in positive integers with `y < k - 1`.
-/

namespace DujellaUnicity

open PadicInt

section General

/-- `k² + 1` is never a perfect square for `k ≠ 0`. -/
theorem nonsquare (k : ℤ) (hk : 1 ≤ k) : ∀ n : ℤ, k ^ 2 + 1 ≠ n * n := by
  intro n hn
  have h1 : k < |n| := by nlinarith [abs_mul_abs_self n, abs_nonneg n]
  have h2 : |n| < k + 1 := by nlinarith [abs_mul_abs_self n, abs_nonneg n]
  omega

/-- Valuations of `2^i * p^j` at `2` and at `p`. -/
theorem padicValNat_two_pow_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i j : ℕ) :
    padicValNat 2 (2 ^ i * p ^ j) = i := by
  have hpj : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [padicValNat.mul (by positivity) hpj, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd]
  · simp
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h)
  exact hp2 this.symm

theorem padicValNat_p_pow_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i j : ℕ) :
    haveI := Fact.mk hp; padicValNat p (2 ^ i * p ^ j) = j := by
  have := Fact.mk hp
  have hpj : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [padicValNat.mul (by positivity) hpj, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd]
  · simp
  intro h
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
  exact hp2 this

/-- A divisor of `2^i * p^j` has the same shape. -/
theorem dvd_two_pow_mul {p : ℕ} (hp : p.Prime) {x i j : ℕ} (h : x ∣ 2 ^ i * p ^ j) :
    ∃ i' j', i' ≤ i ∧ j' ≤ j ∧ x = 2 ^ i' * p ^ j' := by
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.1 h
  obtain ⟨i', hi', rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hy
  obtain ⟨j', hj', rfl⟩ := (Nat.dvd_prime_pow hp).1 hz
  exact ⟨i', j', hi', hj', rfl⟩

theorem valuation_neg {q : ℕ} [Fact q.Prime] (x : ℤ_[q]) : (-x).valuation = x.valuation := by
  by_cases hx : x = 0
  · simp [hx]
  have hnx : -x ≠ 0 := neg_ne_zero.2 hx
  have h := norm_neg x
  rw [norm_eq_zpow_neg_valuation hnx, norm_eq_zpow_neg_valuation hx] at h
  have hq : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have := zpow_right_injective₀ (by linarith : (0:ℝ) < q) hq.ne' h
  omega

/-- `dir` from `vP` and the norm. -/
theorem dir_eq_of_vP {q : ℕ} [Fact q.Prime] {d : ℤ} (l : ℤ_[q]) (hl : l * l = d)
    (hns : ∀ n : ℤ, d ≠ n * n) {γ : ℤ√d} (hγ : γ ≠ 0) :
    dir l hl γ = 2 * (vP l hl γ : ℤ) - padicValInt q γ.norm := by
  have := vP_add_vM l hl hns hγ
  unfold dir; omega

theorem dir_eq_of_vM {q : ℕ} [Fact q.Prime] {d : ℤ} (l : ℤ_[q]) (hl : l * l = d)
    (hns : ∀ n : ℤ, d ≠ n * n) {γ : ℤ√d} (hγ : γ ≠ 0) :
    dir l hl γ = padicValInt q γ.norm - 2 * (vM l hl γ : ℤ) := by
  have := vP_add_vM l hl hns hγ
  unfold dir; omega

/-- If `d ≡ 1 (mod 8)` and a primitive element has even norm, the norm is divisible by `8`. -/
theorem eight_dvd_norm {d : ℤ} (hd : (8 : ℤ) ∣ d - 1) {γ : ℤ√d} (hprim : Int.gcd γ.re γ.im = 1)
    (h2 : (2 : ℤ) ∣ γ.norm) : (8 : ℤ) ∣ γ.norm := by
  rw [Zsqrtd.norm_def] at h2 ⊢
  obtain ⟨t, ht⟩ := hd
  have hd' : d = 8 * t + 1 := by linarith
  subst hd'
  rcases Int.even_or_odd γ.re with ⟨r, hr⟩ | ⟨r, hr⟩ <;>
    rcases Int.even_or_odd γ.im with ⟨s, hs⟩ | ⟨s, hs⟩
  · exfalso
    have h1 : (2 : ℤ) ∣ γ.re := ⟨r, by omega⟩
    have h2' : (2 : ℤ) ∣ γ.im := ⟨s, by omega⟩
    have := Int.dvd_gcd h1 h2'
    rw [hprim] at this; norm_num at this
  · exfalso; rw [hr, hs] at h2; obtain ⟨c, hc⟩ := h2; ring_nf at hc; omega
  · exfalso; rw [hr, hs] at h2; obtain ⟨c, hc⟩ := h2; ring_nf at hc; omega
  · rw [hr, hs]
    obtain ⟨u, hu⟩ := Int.even_mul_succ_self r
    obtain ⟨w, hw⟩ := Int.even_mul_succ_self s
    exact ⟨u - w - t * (2 * s + 1) ^ 2, by linear_combination 4 * hu - 4 * hw⟩

end General

section Setup

set_option linter.unusedSectionVars false

variable {p : ℕ} [hpF : Fact p.Prime] {k : ℤ}

/-- A nonzero element whose norm is `± 2^i p^j`. -/
def Smooth (p : ℕ) {d : ℤ} (γ : ℤ√d) : Prop :=
  γ ≠ 0 ∧ ∃ i j : ℕ, γ.norm.natAbs = 2 ^ i * p ^ j

variable (l2 : ℤ_[2]) (hl2 : l2 * l2 = ((k ^ 2 + 1 : ℤ) : ℤ_[2]))
  (lp : ℤ_[p]) (hlp : lp * lp = ((k ^ 2 + 1 : ℤ) : ℤ_[p]))

/-- The direction vector: `2`-adic and `p`-adic directions. -/
noncomputable def V (γ : ℤ√(k ^ 2 + 1)) : ℤ × ℤ := (dir l2 hl2 γ, dir lp hlp γ)

theorem smooth_mul {d : ℤ} (hns : ∀ n : ℤ, d ≠ n * n) {γ δ : ℤ√d} (hγ : Smooth p γ)
    (hδ : Smooth p δ) : Smooth p (γ * δ) := by
  obtain ⟨hγ0, i, j, hij⟩ := hγ
  obtain ⟨hδ0, i', j', hij'⟩ := hδ
  refine ⟨?_, i + i', j + j', ?_⟩
  · intro h
    have := congrArg Zsqrtd.norm h
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_zero] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hγ0 ((Zsqrtd.norm_eq_zero hns γ).1 h1)
    · exact hδ0 ((Zsqrtd.norm_eq_zero hns δ).1 h1)
  · rw [Zsqrtd.norm_mul, Int.natAbs_mul, hij, hij']; ring

theorem smooth_star {d : ℤ} {γ : ℤ√d} (hγ : Smooth p γ) : Smooth p (star γ) := by
  obtain ⟨hγ0, i, j, hij⟩ := hγ
  refine ⟨?_, i, j, by rw [Zsqrtd.norm_conj, hij]⟩
  intro h; apply hγ0; simpa using congrArg star h

theorem smooth_one {d : ℤ} : Smooth p (1 : ℤ√d) := ⟨one_ne_zero, 0, 0, by simp⟩

/-- Every nonzero element is an integer multiple of a primitive one. -/
theorem exists_primitive {d : ℤ} {γ : ℤ√d} (hγ : γ ≠ 0) :
    ∃ c : ℤ, ∃ γ0 : ℤ√d, c ≠ 0 ∧ γ = (c : ℤ√d) * γ0 ∧ Int.gcd γ0.re γ0.im = 1 := by
  have hne : γ.re ≠ 0 ∨ γ.im ≠ 0 := by
    by_contra h; push Not at h; exact hγ (Zsqrtd.ext h.1 h.2)
  have hg : 0 < Int.gcd γ.re γ.im := Int.gcd_pos_iff.2 hne
  set g : ℤ := (Int.gcd γ.re γ.im : ℤ) with hgdef
  have hg0 : g ≠ 0 := by positivity
  refine ⟨g, ⟨γ.re / g, γ.im / g⟩, hg0, ?_, ?_⟩
  · ext
    · simp only [Zsqrtd.re_smul]; exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm
    · simp only [Zsqrtd.im_smul]; exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm
  · exact Int.gcd_div_gcd_div_gcd hg

theorem smooth_of_mul {d : ℤ} {c : ℤ} {γ0 : ℤ√d}
    (h : Smooth p ((c : ℤ√d) * γ0)) : Smooth p γ0 := by
  obtain ⟨h0, i, j, hij⟩ := h
  refine ⟨fun h' => h0 (by simp [h']), ?_⟩
  have hdvd : γ0.norm.natAbs ∣ 2 ^ i * p ^ j := by
    rw [← hij, Zsqrtd.norm_mul, Int.natAbs_mul]; exact dvd_mul_left _ _
  obtain ⟨i', j', -, -, h'⟩ := dvd_two_pow_mul hpF.out hdvd
  exact ⟨i', j', h'⟩

end Setup

theorem isUnit_of_dvd_sub_one {q : ℕ} [Fact q.Prime] {l : ℤ_[q]} (h : (q : ℤ_[q]) ∣ l - 1) :
    IsUnit l := by
  by_contra hl
  rw [not_isUnit_iff, norm_lt_one_iff_dvd] at hl
  have h1 : (q : ℤ_[q]) ∣ 1 := by simpa using dvd_sub hl h
  have := (norm_lt_one_iff_dvd (1 : ℤ_[q])).2 h1
  simp at this

section Core

set_option linter.unusedSectionVars false

variable {p : ℕ} [hpF : Fact p.Prime] {k : ℤ} {a m : ℕ}
  (l2 : ℤ_[2]) (hl2 : l2 * l2 = ((k ^ 2 + 1 : ℤ) : ℤ_[2]))
  (lp : ℤ_[p]) (hlp : lp * lp = ((k ^ 2 + 1 : ℤ) : ℤ_[p]))

theorem k_pos (hk : k = 2 ^ a * p ^ m) : 0 < k := by
  have := hpF.out.pos; rw [hk]; positivity

theorem natAbs_two_mul_k (hk : k = 2 ^ a * p ^ m) : (2 * k).natAbs = 2 ^ (a + 1) * p ^ m := by
  rw [hk, Int.natAbs_mul, Int.natAbs_mul]; simp [pow_succ]; ring

theorem natAbs_k_sq (hk : k = 2 ^ a * p ^ m) : (k ^ 2).natAbs = 2 ^ (2 * a) * p ^ (2 * m) := by
  rw [hk, Int.natAbs_pow, Int.natAbs_mul]; simp; ring

theorem pv2 (hp2 : p ≠ 2) {z : ℤ} {i j : ℕ} (h : z.natAbs = 2 ^ i * p ^ j) :
    padicValInt 2 z = i := by
  unfold padicValInt; rw [h]; exact padicValNat_two_pow_mul hpF.out hp2 i j

theorem pvp (hp2 : p ≠ 2) {z : ℤ} {i j : ℕ} (h : z.natAbs = 2 ^ i * p ^ j) :
    padicValInt p z = j := by
  unfold padicValInt; rw [h]; exact padicValNat_p_pow_mul hpF.out hp2 i j

theorem norm_plus : (⟨k + 1, 1⟩ : ℤ√(k ^ 2 + 1)).norm = 2 * k := by
  rw [Zsqrtd.norm_def]; ring
theorem norm_minus : (⟨k - 1, 1⟩ : ℤ√(k ^ 2 + 1)).norm = -(2 * k) := by
  rw [Zsqrtd.norm_def]; ring
theorem norm_E : (⟨-1, 1⟩ : ℤ√(k ^ 2 + 1)).norm = -(k ^ 2) := by
  rw [Zsqrtd.norm_def]; ring
theorem norm_unit : (⟨-k, 1⟩ : ℤ√(k ^ 2 + 1)).norm = -1 := by
  rw [Zsqrtd.norm_def]; ring
theorem norm_unit' : (⟨k, 1⟩ : ℤ√(k ^ 2 + 1)).norm = -1 := by
  rw [Zsqrtd.norm_def]; ring

theorem ne_zero_of_im {d x : ℤ} : (⟨x, 1⟩ : ℤ√d) ≠ 0 := by
  intro h; have := congrArg Zsqrtd.im h; simp at this

theorem vP_mk {q : ℕ} [Fact q.Prime] {d : ℤ} (l : ℤ_[q]) (hl : l * l = d) (x : ℤ) :
    vP l hl ⟨x, 1⟩ = (((x : ℤ) : ℤ_[q]) + l).valuation := by
  unfold vP; rw [phiP_apply]; simp

theorem vM_mk {q : ℕ} [Fact q.Prime] {d : ℤ} (l : ℤ_[q]) (hl : l * l = d) (x : ℤ) :
    vM l hl ⟨x, 1⟩ = (((-x : ℤ) : ℤ_[q]) + l).valuation := by
  unfold vM; rw [phiM_apply, ← valuation_neg]; congr 1; push_cast; ring

theorem p_dvd_k (hk : k = 2 ^ a * p ^ m) (hm : 1 ≤ m) : (p : ℤ) ∣ k := by
  rw [hk]; exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _

theorem four_dvd_k (hk : k = 2 ^ a * p ^ m) (ha : 2 ≤ a) : (4 : ℤ) ∣ k := by
  rw [hk]; exact Dvd.dvd.mul_right (by
    have : (4 : ℤ) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_dvd_pow _ ha) _

theorem not_p_dvd (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m) (hm : 1 ≤ m) (c : ℤ)
    (hc : c = k + 2 ∨ c = 2 - k ∨ c = 2) : ¬ (p : ℤ) ∣ c := by
  intro h
  have hpk := p_dvd_k hk hm
  have h2 : (p : ℤ) ∣ 2 := by
    rcases hc with rfl | rfl | rfl
    · simpa using dvd_sub h hpk
    · simpa using dvd_add h hpk
    · exact h
  have := Int.le_of_dvd (by norm_num) h2
  have := hpF.out.two_le
  omega

theorem dirp_plus (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m) (hm : 1 ≤ m)
    (hp1 : (p : ℤ_[p]) ∣ lp - 1) : dir lp hlp ⟨k + 1, 1⟩ = -(m : ℤ) := by
  have hns := nonsquare k (k_pos hk)
  rw [dir_eq_of_vP lp hlp hns ne_zero_of_im, vP_mk,
    valuation_intCast_add_odd lp hp2 hp1 _ (not_p_dvd hp2 hk hm _ (Or.inl (by ring))),
    norm_plus, pvp hp2 (natAbs_two_mul_k hk)]
  simp

theorem dirp_minus (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m) (hm : 1 ≤ m)
    (hp1 : (p : ℤ_[p]) ∣ lp - 1) : dir lp hlp ⟨k - 1, 1⟩ = (m : ℤ) := by
  have hns := nonsquare k (k_pos hk)
  rw [dir_eq_of_vM lp hlp hns ne_zero_of_im, vM_mk,
    valuation_intCast_add_odd lp hp2 hp1 _ (not_p_dvd hp2 hk hm _ (Or.inr (Or.inl (by ring)))),
    norm_minus, pvp hp2 (by rw [Int.natAbs_neg]; exact natAbs_two_mul_k hk)]
  simp

theorem dirp_E (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m) (hm : 1 ≤ m)
    (hp1 : (p : ℤ_[p]) ∣ lp - 1) : dir lp hlp ⟨-1, 1⟩ = 2 * (m : ℤ) := by
  have hns := nonsquare k (k_pos hk)
  rw [dir_eq_of_vM lp hlp hns ne_zero_of_im, vM_mk,
    valuation_intCast_add_odd lp hp2 hp1 _ (not_p_dvd hp2 hk hm _ (Or.inr (Or.inr (by ring)))),
    norm_E, pvp hp2 (by rw [Int.natAbs_neg]; exact natAbs_k_sq hk)]
  simp

theorem dir2_plus (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m) (ha : 2 ≤ a)
    (h4 : (4 : ℤ_[2]) ∣ l2 - 1) : dir l2 hl2 ⟨k + 1, 1⟩ = 1 - (a : ℤ) := by
  have hns := nonsquare k (k_pos hk)
  have h4k := four_dvd_k hk ha
  rw [dir_eq_of_vP l2 hl2 hns ne_zero_of_im, vP_mk,
    valuation_intCast_add_two l2 rfl h4 _ (by omega),
    norm_plus, pv2 hp2 (natAbs_two_mul_k hk)]
  push_cast; ring

theorem dir2_minus (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m) (ha : 2 ≤ a)
    (h4 : (4 : ℤ_[2]) ∣ l2 - 1) : dir l2 hl2 ⟨k - 1, 1⟩ = (a : ℤ) - 1 := by
  have hns := nonsquare k (k_pos hk)
  have h4k := four_dvd_k hk ha
  rw [dir_eq_of_vM l2 hl2 hns ne_zero_of_im, vM_mk,
    valuation_intCast_add_two l2 rfl h4 _ (by omega),
    norm_minus, pv2 hp2 (by rw [Int.natAbs_neg]; exact natAbs_two_mul_k hk)]
  push_cast; ring

theorem dir2_E (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m)
    (h4 : (4 : ℤ_[2]) ∣ l2 - 1) : dir l2 hl2 ⟨-1, 1⟩ = 2 * (a : ℤ) - 2 := by
  have hns := nonsquare k (k_pos hk)
  rw [dir_eq_of_vM l2 hl2 hns ne_zero_of_im, vM_mk,
    valuation_intCast_add_two l2 rfl h4 _ (by norm_num),
    norm_E, pv2 hp2 (by rw [Int.natAbs_neg]; exact natAbs_k_sq hk)]
  push_cast; ring

theorem two_dvd_l2 (h4 : (4 : ℤ_[2]) ∣ l2 - 1) : ((2 : ℕ) : ℤ_[2]) ∣ l2 - 1 := by
  have : ((2 : ℕ) : ℤ_[2]) ∣ 4 := ⟨2, by norm_num⟩
  exact this.trans h4

theorem norm_shape (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m)
    (h4 : (4 : ℤ_[2]) ∣ l2 - 1) (hp1 : (p : ℤ_[p]) ∣ lp - 1) {γ0 : ℤ√(k ^ 2 + 1)}
    (hprim : Int.gcd γ0.re γ0.im = 1) (hsm : Smooth p γ0) :
    ∃ i, i ≤ (dir l2 hl2 γ0).natAbs + 2 ∧
      γ0.norm.natAbs = 2 ^ i * p ^ (dir lp hlp γ0).natAbs := by
  obtain ⟨h0, I, J, hIJ⟩ := hsm
  have hns := nonsquare k (k_pos hk)
  have e2 := vP_add_vM l2 hl2 hns h0
  rw [pv2 hp2 hIJ] at e2
  have ep := vP_add_vM lp hlp hns h0
  rw [pvp hp2 hIJ] at ep
  have m2 := min_le_one_of_primitive l2 hl2 rfl (isUnit_of_dvd_sub_one (two_dvd_l2 l2 h4))
    hns hprim
  have mp := min_eq_zero_of_primitive lp hlp hp2 (isUnit_of_dvd_sub_one hp1) hns hprim
  refine ⟨I, ?_, ?_⟩
  · unfold dir; omega
  · rw [hIJ]; congr 2; unfold dir; omega

theorem eight_dvd_d_sub_one (hk : k = 2 ^ a * p ^ m) (ha : 2 ≤ a) :
    (8 : ℤ) ∣ (k ^ 2 + 1) - 1 := by
  obtain ⟨t, ht⟩ := four_dvd_k hk ha
  exact ⟨2 * t ^ 2, by rw [ht]; ring⟩

/-- A smooth element of direction `0` is an integer times a unit. -/
theorem content_of_dir_zero (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m) (ha : 2 ≤ a)
    (h4 : (4 : ℤ_[2]) ∣ l2 - 1) (hp1 : (p : ℤ_[p]) ∣ lp - 1) {γ : ℤ√(k ^ 2 + 1)}
    (hsm : Smooth p γ) (hd2 : dir l2 hl2 γ = 0) (hdp : dir lp hlp γ = 0) :
    ∃ c : ℤ, c ∣ γ.re ∧ c ∣ γ.im ∧ c ^ 2 = |γ.norm| := by
  have hns := nonsquare k (k_pos hk)
  obtain ⟨c, γ0, hc, rfl, hprim⟩ := exists_primitive hsm.1
  have hsm0 := smooth_of_mul hsm
  have h00 : γ0 ≠ 0 := hsm0.1
  rw [dir_intCast_mul l2 hl2 hns c hc h00] at hd2
  rw [dir_intCast_mul lp hlp hns c hc h00] at hdp
  obtain ⟨i, hi, hN⟩ := norm_shape l2 hl2 lp hlp hp2 hk h4 hp1 hprim hsm0
  rw [hd2, hdp] at *
  simp only [Int.natAbs_zero, zero_add, pow_zero, mul_one] at hi hN
  have hN1 : γ0.norm.natAbs = 1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simpa using hN
    exfalso
    have h2 : (2 : ℤ) ∣ γ0.norm := by
      rw [← Int.natAbs_dvd_natAbs, hN]; simp; omega
    have h8 := eight_dvd_norm (eight_dvd_d_sub_one hk ha) hprim h2
    rw [← Int.natAbs_dvd_natAbs, hN] at h8
    have := Nat.le_of_dvd (by positivity) h8
    have : 2 ^ i ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hi
    simp at h8; omega
  refine ⟨c, by simp, by simp, ?_⟩
  rw [Zsqrtd.norm_mul, Zsqrtd.norm_intCast, abs_mul, ← Int.natCast_natAbs γ0.norm, hN1]
  simp [sq, abs_mul_abs_self]

theorem dir_zero_elt {q : ℕ} [Fact q.Prime] {d : ℤ} (l : ℤ_[q]) (hl : l * l = d) :
    dir l hl (0 : ℤ√d) = 0 := by
  simpa using dir_intCast l hl 0

theorem key (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m) (ha : 2 ≤ a) (hm : 1 ≤ m)
    (h4 : (4 : ℤ_[2]) ∣ l2 - 1) (hp1 : (p : ℤ_[p]) ∣ lp - 1) {γ : ℤ√(k ^ 2 + 1)}
    (hsm : Smooth p γ) :
    V l2 hl2 lp hlp γ = 0 ∨ V l2 hl2 lp hlp γ = (((a - 1 : ℕ) : ℤ), (m : ℤ)) ∨
      V l2 hl2 lp hlp γ = (-((a - 1 : ℕ) : ℤ), -(m : ℤ)) ∨
      2 ^ (a - 1) * p ^ m < wt p (V l2 hl2 lp hlp γ) := by
  have hns := nonsquare k (k_pos hk)
  have hk0 := k_pos hk
  have hcast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ a)]; ring
  obtain ⟨c, γ0, hc, rfl, hprim⟩ := exists_primitive hsm.1
  have hsm0 := smooth_of_mul hsm
  have h00 : γ0 ≠ 0 := hsm0.1
  have hV : V l2 hl2 lp hlp ((c : ℤ√(k ^ 2 + 1)) * γ0) = V l2 hl2 lp hlp γ0 := by
    unfold V; rw [dir_intCast_mul l2 hl2 hns c hc h00, dir_intCast_mul lp hlp hns c hc h00]
  rw [hV]
  by_contra hcon
  push Not at hcon
  obtain ⟨hn0, hnh, hnmh, hwt⟩ := hcon
  obtain ⟨i, hi, hN⟩ := norm_shape l2 hl2 lp hlp hp2 hk h4 hp1 hprim hsm0
  have hbound : γ0.norm.natAbs ≤ 2 * k.natAbs := by
    rw [hN]
    have h2a : 2 * k.natAbs = 4 * (2 ^ (a - 1) * p ^ m) := by
      rw [hk, Int.natAbs_mul]; simp
      rw [show a = (a - 1) + 1 from by omega, pow_succ]; simp; ring
    rw [h2a]
    unfold wt V at hwt; simp only at hwt
    calc 2 ^ i * p ^ (dir lp hlp γ0).natAbs
        ≤ 2 ^ ((dir l2 hl2 γ0).natAbs + 2) * p ^ (dir lp hlp γ0).natAbs :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hi)
      _ = 4 * (2 ^ (dir l2 hl2 γ0).natAbs * p ^ (dir lp hlp γ0).natAbs) := by ring
      _ ≤ 4 * (2 ^ (a - 1) * p ^ m) := Nat.mul_le_mul_left _ hwt
  have hN' : |γ0.norm| ≤ 2 * k := by
    have := (Int.ofNat_le.2 hbound)
    push_cast at this
    rwa [abs_of_pos hk0] at this
  let S : ℤ√(k ^ 2 + 1) → Prop := fun δ =>
    V l2 hl2 lp hlp δ = 0 ∨ V l2 hl2 lp hlp δ = (((a - 1 : ℕ) : ℤ), (m : ℤ)) ∨
      V l2 hl2 lp hlp δ = (-((a - 1 : ℕ) : ℤ), -(m : ℤ))
  have hk2 : 2 ≤ k := by
    have := four_dvd_k hk ha; omega
  have hS : S γ0 := by
    apply small_norm_classify k hk2 S _ _ _ _ _ _ γ0 hprim hN'
    · left; unfold V; simpa using ⟨dir_intCast l2 hl2 1, dir_intCast lp hlp 1⟩
    · right; right; unfold V
      rw [dir2_plus l2 hl2 hp2 hk ha h4, dirp_plus lp hlp hp2 hk hm hp1, hcast]; ext <;> simp
    · right; left; unfold V
      rw [dir2_minus l2 hl2 hp2 hk ha h4, dirp_minus lp hlp hp2 hk hm hp1, hcast]
    · intro δ hδ; simpa [S, V, dir_neg] using hδ
    · intro δ hδ
      simp only [S, V, dir_star] at hδ ⊢
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, neg_eq_zero, neg_inj] at hδ ⊢
      rcases hδ with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl ⟨by linarith [h.1], by linarith [h.2]⟩)
    · intro δ hδ
      by_cases hδ0 : δ = 0
      · left; unfold V; rw [hδ0, dir_zero_elt, dir_zero_elt]; rfl
      have hu : (⟨-k, 1⟩ : ℤ√(k ^ 2 + 1)) ≠ 0 := ne_zero_of_im
      have h1 : V l2 hl2 lp hlp (δ * ⟨-k, 1⟩) = V l2 hl2 lp hlp δ := by
        unfold V
        rw [dir_mul l2 hl2 hns hδ0 hu, dir_mul lp hlp hns hδ0 hu,
          dir_of_norm_eq_one l2 hl2 hns (Or.inr norm_unit),
          dir_of_norm_eq_one lp hlp hns (Or.inr norm_unit)]
        simp
      simpa [S, h1] using hδ
  rcases hS with h | h | h
  · exact hn0 h
  · exact hnh h
  · exact hnmh h

/-- A solution `(x, y)` written as `g • α` with `α` primitive of norm `s²`, `k = g s`. -/
theorem sol_data {k x y : ℤ} (hk0 : 0 < k) (hy : 0 < y)
    (h : x ^ 2 - (k ^ 2 + 1) * y ^ 2 = k ^ 2) :
    ∃ g s : ℤ, ∃ α : ℤ√(k ^ 2 + 1), 0 < g ∧ 0 < s ∧ k = g * s ∧ x = g * α.re ∧
      y = g * α.im ∧ Int.gcd α.re α.im = 1 ∧ α.norm = s ^ 2 := by
  have hg : 0 < Int.gcd x y := Int.gcd_pos_iff.2 (Or.inr hy.ne')
  set g : ℤ := (Int.gcd x y : ℤ) with hgdef
  have hg0 : 0 < g := by positivity
  have hx : x = g * (x / g) := (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm
  have hy' : y = g * (y / g) := (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm
  set X := x / g
  set Y := y / g
  have hprim : Int.gcd X Y = 1 := Int.gcd_div_gcd_div_gcd hg
  clear_value X Y g
  have hN : g ^ 2 * (X ^ 2 - (k ^ 2 + 1) * Y ^ 2) = k ^ 2 := by
    rw [hx, hy'] at h; linear_combination h
  have hdvd : g ∣ k := (Int.pow_dvd_pow_iff two_ne_zero).1 ⟨_, hN.symm⟩
  obtain ⟨s, hs⟩ := hdvd
  have hs0 : 0 < s := by
    rcases lt_trichotomy s 0 with h1 | h1 | h1
    · nlinarith
    · rw [h1] at hs; omega
    · exact h1
  refine ⟨g, s, ⟨X, Y⟩, hg0, hs0, hs, hx, hy', hprim, ?_⟩
  rw [Zsqrtd.norm_def]
  have : g ^ 2 * (X ^ 2 - (k ^ 2 + 1) * Y ^ 2) = g ^ 2 * s ^ 2 := by rw [hN, hs]; ring
  have := mul_left_cancel₀ (by positivity) this
  simp only; linarith

theorem smooth_of_sq (hk : k = 2 ^ a * p ^ m) {g s : ℤ} (hks : k = g * s) :
    ∃ i j, i ≤ a ∧ j ≤ m ∧ s.natAbs = 2 ^ i * p ^ j := by
  have : s.natAbs ∣ 2 ^ a * p ^ m := by
    have h1 : s.natAbs ∣ k.natAbs := Int.natAbs_dvd_natAbs.2 ⟨g, by rw [hks]; ring⟩
    rwa [hk, Int.natAbs_mul] at h1
  exact dvd_two_pow_mul hpF.out this

theorem smooth_sol (hk : k = 2 ^ a * p ^ m) {α : ℤ√(k ^ 2 + 1)} {g s : ℤ} (hs0 : 0 < s)
    (hks : k = g * s) (hN : α.norm = s ^ 2) :
    Smooth p α ∧ ∃ i j, i ≤ a ∧ j ≤ m ∧ α.norm.natAbs = 2 ^ (2 * i) * p ^ (2 * j) := by
  obtain ⟨i, j, hi, hj, hsij⟩ := smooth_of_sq hk hks
  have hNabs : α.norm.natAbs = 2 ^ (2 * i) * p ^ (2 * j) := by
    rw [hN, Int.natAbs_pow, hsij]; ring
  refine ⟨⟨?_, 2 * i, 2 * j, hNabs⟩, i, j, hi, hj, hNabs⟩
  intro h0; rw [h0, Zsqrtd.norm_zero] at hN; nlinarith

theorem vec_props (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m) (ha : 2 ≤ a)
    (h4 : (4 : ℤ_[2]) ∣ l2 - 1) (hp1 : (p : ℤ_[p]) ∣ lp - 1) {α : ℤ√(k ^ 2 + 1)}
    (hprim : Int.gcd α.re α.im = 1) {g s : ℤ} (hs0 : 0 < s) (hks : k = g * s)
    (hN : α.norm = s ^ 2) :
    Even (dir l2 hl2 α) ∧ Even (dir lp hlp α) ∧ |dir l2 hl2 α| ≤ 2 * ((a - 1 : ℕ) : ℤ) ∧
      |dir lp hlp α| ≤ 2 * (m : ℤ) := by
  have hns := nonsquare k (k_pos hk)
  obtain ⟨hsm, i, j, hi, hj, hNabs⟩ := smooth_sol hk hs0 hks hN
  have e2 := vP_add_vM l2 hl2 hns hsm.1
  rw [pv2 hp2 hNabs] at e2
  have ep := vP_add_vM lp hlp hns hsm.1
  rw [pvp hp2 hNabs] at ep
  have hu2 := isUnit_of_dvd_sub_one (two_dvd_l2 l2 h4)
  have m2 := min_le_one_of_primitive l2 hl2 rfl hu2 hns hprim
  have mp := min_eq_zero_of_primitive lp hlp hp2 (isUnit_of_dvd_sub_one hp1) hns hprim
  have hcast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ a)]; ring
  have h2 : i = 0 ∨ (1 ≤ vP l2 hl2 α ∧ 1 ≤ vM l2 hl2 α) := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact Or.inl h
    · right
      apply one_le_min_of_two_dvd_norm l2 hl2 rfl hu2 hns hsm.1
      rw [← Int.natAbs_dvd_natAbs, hNabs]; simp
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  unfold dir
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Int.even_iff]; omega
  · rw [Int.even_iff]; omega
  · rw [abs_le, hcast]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega

theorem dvd_of_sq_eq {c t : ℤ} (h : c ^ 2 = t ^ 2) {z : ℤ} (hz : c ∣ z) : t ∣ z := by
  have := (sq_eq_sq_iff_abs_eq_abs c t).1 h
  have h1 : |t| ∣ z := by rw [← this]; exact (abs_dvd c z).2 hz
  exact (abs_dvd t z).1 h1

/-- Two solutions whose direction vectors agree up to sign are equal. -/
theorem uniq (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m) (ha : 2 ≤ a)
    (h4 : (4 : ℤ_[2]) ∣ l2 - 1) (hp1 : (p : ℤ_[p]) ∣ lp - 1)
    {x1 y1 x2 y2 g1 g2 s1 s2 : ℤ} {α1 α2 : ℤ√(k ^ 2 + 1)}
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy1' : y1 ≤ k - 1) (hy2' : y2 ≤ k - 1)
    (h1 : x1 ^ 2 - (k ^ 2 + 1) * y1 ^ 2 = k ^ 2) (h2 : x2 ^ 2 - (k ^ 2 + 1) * y2 ^ 2 = k ^ 2)
    (hs1 : 0 < s1) (hks1 : k = g1 * s1) (hx1g : x1 = g1 * α1.re) (hy1g : y1 = g1 * α1.im)
    (hN1 : α1.norm = s1 ^ 2)
    (hs2 : 0 < s2) (hks2 : k = g2 * s2) (hx2g : x2 = g2 * α2.re) (hy2g : y2 = g2 * α2.im)
    (hN2 : α2.norm = s2 ^ 2)
    (hrel : V l2 hl2 lp hlp α1 = V l2 hl2 lp hlp α2 ∨
      V l2 hl2 lp hlp α1 = -V l2 hl2 lp hlp α2) : x1 = x2 ∧ y1 = y2 := by
  have hns := nonsquare k (k_pos hk)
  have hk2 : 2 ≤ k := by have := four_dvd_k hk ha; have := k_pos hk; omega
  obtain ⟨hsm1, -⟩ := smooth_sol hk hs1 hks1 hN1
  obtain ⟨hsm2, -⟩ := smooth_sol hk hs2 hks2 hN2
  have hkk : k ^ 2 = g1 * g2 * (s1 * s2) := by rw [sq]; nth_rewrite 1 [hks1]; rw [hks2]; ring
  simp only [V, Prod.ext_iff, Prod.neg_mk] at hrel
  rcases hrel with ⟨e2, ep⟩ | ⟨e2, ep⟩
  · -- same direction: `α1 * star α2`
    have hsm := smooth_mul hns hsm1 (smooth_star hsm2)
    have hs2' : star α2 ≠ 0 := (smooth_star hsm2).1
    obtain ⟨c, -, hcim, hc2⟩ := content_of_dir_zero l2 hl2 lp hlp hp2 hk ha h4 hp1 hsm
      (by rw [dir_mul l2 hl2 hns hsm1.1 hs2', dir_star, e2]; ring)
      (by rw [dir_mul lp hlp hns hsm1.1 hs2', dir_star, ep]; ring)
    have hc2' : c ^ 2 = (s1 * s2) ^ 2 := by
      rw [hc2, Zsqrtd.norm_mul, Zsqrtd.norm_conj, hN1, hN2]
      rw [abs_of_nonneg (by positivity)]; ring
    have hd := dvd_of_sq_eq hc2' hcim
    apply uniq_same k x1 y1 x2 y2 hk2 hx1 hx2 hy1 hy2 hy1' hy2' h1 h2
    rw [hx1g, hy1g, hx2g, hy2g]
    obtain ⟨t, ht⟩ := hd
    refine ⟨t, ?_⟩
    simp only [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star] at ht
    linear_combination (g1 * g2) * ht - t * hkk
  · -- opposite direction: `α1 * α2`
    have hsm := smooth_mul hns hsm1 hsm2
    obtain ⟨c, hcre, hcim, hc2⟩ := content_of_dir_zero l2 hl2 lp hlp hp2 hk ha h4 hp1 hsm
      (by rw [dir_mul l2 hl2 hns hsm1.1 hsm2.1, e2]; ring)
      (by rw [dir_mul lp hlp hns hsm1.1 hsm2.1, ep]; ring)
    have hc2' : c ^ 2 = (s1 * s2) ^ 2 := by
      rw [hc2, Zsqrtd.norm_mul, hN1, hN2]
      rw [abs_of_nonneg (by positivity)]; ring
    obtain ⟨t, ht⟩ := dvd_of_sq_eq hc2' hcre
    obtain ⟨u, hu⟩ := dvd_of_sq_eq hc2' hcim
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] at ht hu
    exfalso
    apply uniq_opp k x1 y1 x2 y2 hk2 hx1 hx2 hy1 hy2 hy1' hy2' h1 h2
    · refine ⟨t, ?_⟩; rw [hx1g, hy1g, hx2g, hy2g]
      linear_combination (g1 * g2) * ht - t * hkk
    · refine ⟨u, ?_⟩; rw [hx1g, hy1g, hx2g, hy2g]
      linear_combination (g1 * g2) * hu - u * hkk

theorem V_mul (hns : ∀ n : ℤ, k ^ 2 + 1 ≠ n * n) {γ δ : ℤ√(k ^ 2 + 1)} (hγ : γ ≠ 0)
    (hδ : δ ≠ 0) : V l2 hl2 lp hlp (γ * δ) = V l2 hl2 lp hlp γ + V l2 hl2 lp hlp δ := by
  unfold V; rw [dir_mul l2 hl2 hns hγ hδ, dir_mul lp hlp hns hγ hδ]; rfl

theorem V_star (γ : ℤ√(k ^ 2 + 1)) : V l2 hl2 lp hlp (star γ) = -V l2 hl2 lp hlp γ := by
  unfold V; rw [dir_star, dir_star]; rfl

theorem sol_vec (hp2 : p ≠ 2) (hk : k = 2 ^ a * p ^ m) (ha : 2 ≤ a) (hm : 1 ≤ m)
    (h4 : (4 : ℤ_[2]) ∣ l2 - 1) (hp1 : (p : ℤ_[p]) ∣ lp - 1) {x y : ℤ} (hx : 0 < x)
    (hy : 0 < y) (hyk : y < k - 1) (h : x ^ 2 - (k ^ 2 + 1) * y ^ 2 = k ^ 2) :
    ∃ g s : ℤ, ∃ α : ℤ√(k ^ 2 + 1), 0 < s ∧ k = g * s ∧ x = g * α.re ∧ y = g * α.im ∧
      α.norm = s ^ 2 ∧ Smooth p α ∧ IsSolVec (a - 1) m (V l2 hl2 lp hlp α) := by
  have hk0 := k_pos hk
  have hk2 : 2 ≤ k := by have := four_dvd_k hk ha; omega
  have hns := nonsquare k hk0
  have hcast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ a)]; ring
  have hVE : V l2 hl2 lp hlp ⟨-1, 1⟩ = (2 * ((a - 1 : ℕ) : ℤ), 2 * (m : ℤ)) := by
    unfold V; rw [dir2_E l2 hl2 hp2 hk h4, dirp_E lp hlp hp2 hk hm hp1, hcast]
    ext <;> simp; ring
  -- the trivial solution `(k² - k + 1, k - 1)`
  set αt : ℤ√(k ^ 2 + 1) := ⟨-1, 1⟩ * ⟨k, 1⟩ with hαt
  have hαt_re : αt.re = k ^ 2 - k + 1 := by simp [hαt, Zsqrtd.re_mul]; ring
  have hαt_im : αt.im = k - 1 := by simp [hαt, Zsqrtd.im_mul]; ring
  have hαt_N : αt.norm = k ^ 2 := by rw [hαt, Zsqrtd.norm_mul, norm_E, norm_unit']; ring
  have hVt : V l2 hl2 lp hlp αt = (2 * ((a - 1 : ℕ) : ℤ), 2 * (m : ℤ)) := by
    rw [hαt, V_mul l2 hl2 lp hlp hns ne_zero_of_im ne_zero_of_im, hVE]
    have : V l2 hl2 lp hlp (⟨k, 1⟩ : ℤ√(k ^ 2 + 1)) = 0 := by
      unfold V
      rw [dir_of_norm_eq_one l2 hl2 hns (Or.inr norm_unit'),
        dir_of_norm_eq_one lp hlp hns (Or.inr norm_unit')]; rfl
    rw [this, add_zero]
  have htx : 0 < k ^ 2 - k + 1 := by nlinarith
  have hteq : (k ^ 2 - k + 1) ^ 2 - (k ^ 2 + 1) * (k - 1) ^ 2 = k ^ 2 := by ring
  -- a solution gives a solution vector
  obtain ⟨g, s, α, hg, hs, hks, hxg, hyg, hprim, hN⟩ := sol_data hk0 hy h
  obtain ⟨he2, hep, hb2, hbp⟩ := vec_props l2 hl2 lp hlp hp2 hk ha h4 hp1 hprim hs hks hN
  have hsm := (smooth_sol hk hs hks hN).1
  refine ⟨g, s, α, hs, hks, hxg, hyg, hN, hsm, ⟨he2, hep, hb2, hbp, ?_, ?_, ?_⟩⟩
  · intro h0
    simp only [V, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h0
    obtain ⟨c, hcre, hcim, hc2⟩ :=
      content_of_dir_zero l2 hl2 lp hlp hp2 hk ha h4 hp1 hsm h0.1 h0.2
    have hc1 : c.natAbs ∣ 1 := by
      rw [← hprim]
      exact Nat.dvd_gcd (Int.natAbs_dvd_natAbs.2 hcre) (Int.natAbs_dvd_natAbs.2 hcim)
    have hcc : c ^ 2 = 1 := by
      rw [← Int.natAbs_sq, Nat.dvd_one.1 hc1]; norm_num
    rw [hcc, hN, abs_of_nonneg (by positivity)] at hc2
    have hs1 : s = 1 := by nlinarith
    rw [hs1, mul_one] at hks
    have him : 0 < α.im := by
      rcases lt_trichotomy α.im 0 with h' | h' | h'
      · nlinarith
      · rw [h', mul_zero] at hyg; omega
      · exact h'
    nlinarith
  · intro hE'
    have := uniq l2 hl2 lp hlp hp2 hk ha h4 hp1 (x2 := k ^ 2 - k + 1) (y2 := k - 1) (g2 := 1)
      (s2 := k) (α2 := αt) hx htx hy (by omega) hyk.le le_rfl h hteq hs hks hxg hyg hN
      hk0 (by ring) (by rw [hαt_re]; ring) (by rw [hαt_im]; ring) hαt_N
      (Or.inl (by rw [hE', hVt]))
    omega
  · intro hE'
    have := uniq l2 hl2 lp hlp hp2 hk ha h4 hp1 (x2 := k ^ 2 - k + 1) (y2 := k - 1) (g2 := 1)
      (s2 := k) (α2 := αt) hx htx hy (by omega) hyk.le le_rfl h hteq hs hks hxg hyg hN
      hk0 (by ring) (by rw [hαt_re]; ring) (by rw [hαt_im]; ring) hαt_N
      (Or.inr (by rw [hE', hVt]; rfl))
    omega

end Core

/-- **Dujella's unicity conjecture for `k = 2^a p^m`.** Let `p` be an odd prime, `a ≥ 2`,
`m ≥ 1`, and assume `2k` is not a perfect square (`a` even or `m` odd). Then the equation
`x² - (k²+1) y² = k²` has at most one solution in positive integers with `y < k - 1`. -/
theorem dujella_unicity {p a m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 2 ≤ a) (hm : 1 ≤ m)
    (hpar : Even a ∨ Odd m) {k : ℤ} (hk : k = 2 ^ a * p ^ m) {x1 y1 x2 y2 : ℤ}
    (hx1 : 0 < x1) (hy1 : 0 < y1) (hy1k : y1 < k - 1) (h1 : x1 ^ 2 - (k ^ 2 + 1) * y1 ^ 2 = k ^ 2)
    (hx2 : 0 < x2) (hy2 : 0 < y2) (hy2k : y2 < k - 1) (h2 : x2 ^ 2 - (k ^ 2 + 1) * y2 ^ 2 = k ^ 2) :
    x1 = x2 ∧ y1 = y2 := by
  have := Fact.mk hp
  have hk0 := k_pos hk
  have hk2 : 2 ≤ k := by have := four_dvd_k hk ha; omega
  have hns := nonsquare k hk0
  obtain ⟨l2, hl2, h4⟩ := exists_sqrt_two (q := 2) rfl k (four_dvd_k hk ha)
  obtain ⟨lp, hlp, hp1⟩ := exists_sqrt_odd (q := p) hp2 k (p_dvd_k hk hm)
  have hcast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ a)]; ring
  -- the group of direction vectors of smooth elements
  let S : AddSubgroup (ℤ × ℤ) :=
    { carrier := {u | ∃ γ, Smooth p γ ∧ V l2 hl2 lp hlp γ = u}
      zero_mem' := ⟨1, smooth_one, by
        unfold V; simpa using ⟨dir_intCast l2 hl2 1, dir_intCast lp hlp 1⟩⟩
      add_mem' := by
        rintro _ _ ⟨γ, hγ, rfl⟩ ⟨δ, hδ, rfl⟩
        exact ⟨γ * δ, smooth_mul hns hγ hδ, V_mul l2 hl2 lp hlp hns hγ.1 hδ.1⟩
      neg_mem' := by
        rintro _ ⟨γ, hγ, rfl⟩
        exact ⟨star γ, smooth_star hγ, V_star l2 hl2 lp hlp γ⟩ }
  have hVE : V l2 hl2 lp hlp ⟨-1, 1⟩ = (2 * ((a - 1 : ℕ) : ℤ), 2 * (m : ℤ)) := by
    unfold V; rw [dir2_E l2 hl2 hp2 hk h4, dirp_E lp hlp hp2 hk hm hp1, hcast]
    ext <;> simp; ring
  have hsmE : Smooth p (⟨-1, 1⟩ : ℤ√(k ^ 2 + 1)) :=
    ⟨ne_zero_of_im, 2 * a, 2 * m, by rw [norm_E, Int.natAbs_neg, natAbs_k_sq hk]⟩
  have hE : (2 * ((a - 1 : ℕ) : ℤ), 2 * (m : ℤ)) ∈ S := ⟨_, hsmE, hVE⟩
  have hkeyS : ∀ u ∈ S, u = 0 ∨ u = (((a - 1 : ℕ) : ℤ), (m : ℤ)) ∨
      u = (-((a - 1 : ℕ) : ℤ), -(m : ℤ)) ∨ 2 ^ (a - 1) * p ^ m < wt p u := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact key l2 hl2 lp hlp hp2 hk ha hm h4 hp1 hγ
  have hpar' : ¬ (Even (a - 1) ∧ Even m) := by
    rintro ⟨h1', h2'⟩
    rcases hpar with h | h
    · rw [Nat.even_iff] at h h1'; omega
    · exact (Nat.not_even_iff_odd.2 h) h2'
  obtain ⟨g1, s1, α1, hs1, hks1, hx1g, hy1g, hN1, hsm1, hv1⟩ :=
    sol_vec l2 hl2 lp hlp hp2 hk ha hm h4 hp1 hx1 hy1 hy1k h1
  obtain ⟨g2, s2, α2, hs2, hks2, hx2g, hy2g, hN2, hsm2, hv2⟩ :=
    sol_vec l2 hl2 lp hlp hp2 hk ha hm h4 hp1 hx2 hy2 hy2k h2
  have hS1 : V l2 hl2 lp hlp α1 ∈ S := ⟨α1, hsm1, rfl⟩
  have hS2 : V l2 hl2 lp hlp α2 ∈ S := ⟨α2, hsm2, rfl⟩
  have hlat := lattice_main (a - 1) m p (by omega) hm hp.two_le hpar' S
    (by simpa using hE) hkeyS _ _ hS1 hS2 hv1 hv2
  exact uniq l2 hl2 lp hlp hp2 hk ha h4 hp1 hx1 hx2 hy1 hy2 (by omega) (by omega) h1 h2
    hs1 hks1 hx1g hy1g hN1 hs2 hks2 hx2g hy2g hN2 hlat

end DujellaUnicity
