import Mathlib

/-!
# Dujella unicity: elementary facts in `ℤ[√(k²+1)]`

* `small_norm_classify`: a primitive element of norm at most `2k` in absolute value is,
  up to sign, conjugation and the unit `√d - k`, one of `1`, `k+1+√d`, `k-1+√d`.
* `uniq_same`, `uniq_opp`: the size estimates that make two solutions with the same
  (or opposite) direction vector coincide.
-/

namespace DujellaUnicity

/-- Multiplying by the unit `√d - k` preserves primitivity. -/
lemma gcd_mul_unit (k : ℤ) (γ : ℤ√(k ^ 2 + 1)) (hprim : Int.gcd γ.re γ.im = 1) :
    Int.gcd (γ * ⟨-k, 1⟩).re (γ * ⟨-k, 1⟩).im = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one] at hprim ⊢
  obtain ⟨u, v, h⟩ := hprim
  refine ⟨u * k + v, u * (k ^ 2 + 1) + v * k, ?_⟩
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
  linear_combination h

/-- The normalized case `0 ≤ re`, `0 ≤ im` of the descent, given the induction hypothesis. -/
lemma small_norm_nonneg (k : ℤ) (hk : 2 ≤ k) (S : ℤ√(k ^ 2 + 1) → Prop)
    (h1 : S 1) (hplus : S ⟨k + 1, 1⟩) (hminus : S ⟨k - 1, 1⟩)
    (hunit : ∀ γ, S (γ * ⟨-k, 1⟩) → S γ) (γ : ℤ√(k ^ 2 + 1))
    (IH : ∀ γ' : ℤ√(k ^ 2 + 1), γ'.im.natAbs < γ.im.natAbs → Int.gcd γ'.re γ'.im = 1 →
      |γ'.norm| ≤ 2 * k → S γ')
    (hX : 0 ≤ γ.re) (hY : 0 ≤ γ.im)
    (hprim : Int.gcd γ.re γ.im = 1) (hN : |γ.norm| ≤ 2 * k) : S γ := by
  obtain ⟨X, Y⟩ := γ
  simp only [Zsqrtd.norm_def] at hN hX hY hprim IH ⊢
  rcases hY.lt_or_eq with hY | hY
  · obtain ⟨j, rfl⟩ : ∃ j, X = k * Y + j := ⟨X - k * Y, by ring⟩
    have hNe : (k * Y + j) * (k * Y + j) - (k ^ 2 + 1) * Y * Y = j ^ 2 + 2 * k * Y * j - Y ^ 2 := by
      ring
    rw [hNe, abs_le] at hN
    by_cases hj : |j| < Y
    · apply hunit
      apply IH
      · simp only [Zsqrtd.im_mul]
        rw [abs_lt] at hj
        have : (k * Y + j) * 1 + Y * -k = j := by ring
        rw [this]
        omega
      · exact gcd_mul_unit k _ hprim
      · rw [← Zsqrtd.norm_def, Zsqrtd.norm_mul, abs_mul]
        have : (⟨-k, 1⟩ : ℤ√(k ^ 2 + 1)).norm = -1 := by
          rw [Zsqrtd.norm_def]; ring
        rw [this, Zsqrtd.norm_def]
        simp only [abs_neg, abs_one, mul_one]
        rw [hNe, abs_le]
        exact hN
    · rw [abs_lt, not_and_or, not_lt, not_lt] at hj
      rcases hj with hj | hj
      · -- j ≤ -Y
        have hjk : -k * Y ≤ j := by linarith
        have hprod : (j + Y) * (j + (2 * k - 1) * Y) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (by nlinarith)
        have hY1 : Y = 1 := by nlinarith
        subst hY1
        have hj1 : j = -1 := by nlinarith
        subst hj1
        convert hminus using 2; ring
      · -- Y ≤ j
        have e1 : 2 * k * Y * Y ≤ 2 * k * Y * j :=
          mul_le_mul_of_nonneg_left hj (by positivity)
        have e2 : Y * Y ≤ j * j := mul_self_le_mul_self hY.le hj
        have hY1 : Y = 1 := by nlinarith
        subst hY1
        have hj1 : j = 1 := by nlinarith
        subst hj1
        convert hplus using 2; ring
  · subst hY
    have : X = 1 := by
      have := Int.gcd_zero_right X
      omega
    subst this
    exact h1

theorem small_norm_classify (k : ℤ) (hk : 2 ≤ k) (S : ℤ√(k ^ 2 + 1) → Prop)
    (h1 : S 1) (hplus : S ⟨k + 1, 1⟩) (hminus : S ⟨k - 1, 1⟩)
    (hneg : ∀ γ, S γ → S (-γ)) (hstar : ∀ γ, S γ → S (star γ))
    (hunit : ∀ γ, S (γ * ⟨-k, 1⟩) → S γ)
    (γ : ℤ√(k ^ 2 + 1)) (hprim : Int.gcd γ.re γ.im = 1) (hN : |γ.norm| ≤ 2 * k) : S γ := by
  suffices H : ∀ n : ℕ, ∀ γ : ℤ√(k ^ 2 + 1), γ.im.natAbs = n → Int.gcd γ.re γ.im = 1 →
      |γ.norm| ≤ 2 * k → S γ from H _ γ rfl hprim hN
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro γ hn hprim hN
  have IH' : ∀ γ' : ℤ√(k ^ 2 + 1), γ'.im.natAbs < γ.im.natAbs → Int.gcd γ'.re γ'.im = 1 →
      |γ'.norm| ≤ 2 * k → S γ' := fun γ' h => IH _ (hn ▸ h) γ' rfl
  have key : ∀ δ : ℤ√(k ^ 2 + 1), δ.im.natAbs = γ.im.natAbs → 0 ≤ δ.re → 0 ≤ δ.im →
      Int.gcd δ.re δ.im = 1 → |δ.norm| ≤ 2 * k → S δ := by
    intro δ hδ hX hY hp hNδ
    exact small_norm_nonneg k hk S h1 hplus hminus hunit δ (hδ ▸ IH') hX hY hp hNδ
  rcases le_or_gt 0 γ.re with hX | hX <;> rcases le_or_gt 0 γ.im with hY | hY
  · exact key γ rfl hX hY hprim hN
  · have := hstar _ (key (star γ) (by simp [Zsqrtd.im_star]) (by simp [Zsqrtd.re_star]; exact hX)
      (by simp [Zsqrtd.im_star]; linarith) (by simpa [Zsqrtd.re_star, Zsqrtd.im_star] using hprim)
      (by rwa [Zsqrtd.norm_conj]))
    simpa using this
  · have := hneg _ (hstar _ (key (-star γ) (by simp [Zsqrtd.im_star])
      (by simp [Zsqrtd.re_star]; linarith) (by simp [Zsqrtd.im_star]; exact hY)
      (by simpa [Zsqrtd.re_star, Zsqrtd.im_star] using hprim)
      (by rwa [Zsqrtd.norm_neg, Zsqrtd.norm_conj])))
    simpa using this
  · have := hneg _ (key (-γ) (by simp) (by simp; linarith) (by simp; linarith)
      (by simpa using hprim) (by rwa [Zsqrtd.norm_neg]))
    simpa using this

theorem uniq_same (k x1 y1 x2 y2 : ℤ) (hk : 2 ≤ k) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy1' : y1 ≤ k - 1) (hy2' : y2 ≤ k - 1)
    (h1 : x1 ^ 2 - (k ^ 2 + 1) * y1 ^ 2 = k ^ 2) (h2 : x2 ^ 2 - (k ^ 2 + 1) * y2 ^ 2 = k ^ 2)
    (hdvd : k ^ 2 ∣ x2 * y1 - x1 * y2) : x1 = x2 ∧ y1 = y2 := by
  obtain ⟨m, hm⟩ := hdvd
  have hky1 : k * y1 < x1 := by nlinarith
  have hky2 : k * y2 < x2 := by nlinarith
  have hk2 : 0 < k ^ 2 := by positivity
  have hid : (x2 * y1 - x1 * y2) * (x2 * y1 + x1 * y2) = k ^ 2 * (y1 ^ 2 - y2 ^ 2) := by
    linear_combination y1 ^ 2 * h2 - y2 ^ 2 * h1
  rw [hm, mul_assoc] at hid
  have hm' : m * (x2 * y1 + x1 * y2) = y1 ^ 2 - y2 ^ 2 := mul_left_cancel₀ hk2.ne' hid
  have hyx2 : y1 < x2 := by nlinarith
  have hyx1 : y2 < x1 := by nlinarith
  have hP1 : y1 ^ 2 < x2 * y1 := by nlinarith [mul_lt_mul_of_pos_left hyx2 hy1]
  have hP2 : y2 ^ 2 < x1 * y2 := by nlinarith [mul_lt_mul_of_pos_left hyx1 hy2]
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  subst hm0
  have hy : y1 = y2 := by
    have : (y1 - y2) * (y1 + y2) = 0 := by linear_combination -hm'
    rcases mul_eq_zero.mp this with h | h <;> linarith
  subst hy
  refine ⟨?_, rfl⟩
  have : (x1 - x2) * (x1 + x2) = 0 := by linear_combination h1 - h2
  rcases mul_eq_zero.mp this with h | h <;> linarith

theorem uniq_opp (k x1 y1 x2 y2 : ℤ) (hk : 2 ≤ k) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy1' : y1 ≤ k - 1) (hy2' : y2 ≤ k - 1)
    (h1 : x1 ^ 2 - (k ^ 2 + 1) * y1 ^ 2 = k ^ 2) (h2 : x2 ^ 2 - (k ^ 2 + 1) * y2 ^ 2 = k ^ 2)
    (hdvd1 : k ^ 2 ∣ x1 * x2 + (k ^ 2 + 1) * y1 * y2) (hdvd2 : k ^ 2 ∣ x1 * y2 + x2 * y1) :
    False := by
  obtain ⟨a, ha⟩ := hdvd1
  obtain ⟨b, hb⟩ := hdvd2
  have hk2 : 0 < k ^ 2 := by positivity
  have hid : (x1 * x2 + (k ^ 2 + 1) * y1 * y2) ^ 2 - (k ^ 2 + 1) * (x1 * y2 + x2 * y1) ^ 2
      = k ^ 2 * k ^ 2 := by
    linear_combination (x2 ^ 2 - (k ^ 2 + 1) * y2 ^ 2) * h1 + k ^ 2 * h2
  rw [ha, hb] at hid
  have hpell : a ^ 2 - (k ^ 2 + 1) * b ^ 2 = 1 := by
    have h4 : 0 < k ^ 2 * k ^ 2 := by positivity
    have : k ^ 2 * k ^ 2 * (a ^ 2 - (k ^ 2 + 1) * b ^ 2) = k ^ 2 * k ^ 2 * 1 := by
      linear_combination hid
    exact mul_left_cancel₀ h4.ne' this
  have hb0 : 0 < b := by
    have : 0 < k ^ 2 * b := by rw [← hb]; positivity
    exact pos_of_mul_pos_right this hk2.le
  have hb2k : 2 * k ≤ b := by
    by_contra hlt
    push Not at hlt
    have hA : k * b < |a| := by
      have : (k * b) ^ 2 < |a| ^ 2 := by
        rw [sq_abs]; nlinarith [sq_nonneg b]
      exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg a) this
    have hA2 : (k * b + 1) ^ 2 ≤ |a| ^ 2 := by
      have : k * b + 1 ≤ |a| := hA
      have : 0 ≤ k * b + 1 := by positivity
      exact pow_le_pow_left₀ this hA 2
    rw [sq_abs] at hA2
    nlinarith [mul_pos hb0 (sub_pos.mpr hlt)]
  have hxb1 : x1 ≤ k ^ 2 - k + 1 := by
    have hy : y1 ^ 2 ≤ (k - 1) ^ 2 := by nlinarith
    have : x1 ^ 2 ≤ (k ^ 2 - k + 1) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℤ) ≤ k ^ 2 + 1)]
    exact (pow_le_pow_iff_left₀ hx1.le (by nlinarith) two_ne_zero).mp this
  have hxb2 : x2 ≤ k ^ 2 - k + 1 := by
    have hy : y2 ^ 2 ≤ (k - 1) ^ 2 := by nlinarith
    have : x2 ^ 2 ≤ (k ^ 2 - k + 1) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℤ) ≤ k ^ 2 + 1)]
    exact (pow_le_pow_iff_left₀ hx2.le (by nlinarith) two_ne_zero).mp this
  have hB : x1 * y2 + x2 * y1 ≤ 2 * (k ^ 2 - k + 1) * (k - 1) := by
    nlinarith [mul_le_mul hxb1 hy2' hy2.le (by nlinarith),
      mul_le_mul hxb2 hy1' hy1.le (by nlinarith)]
  nlinarith [mul_le_mul_of_nonneg_left hb2k hk2.le]

end DujellaUnicity
