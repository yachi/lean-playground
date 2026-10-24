module

public import LeanPlayground.SimonMarais.Quad

/-!
# The core of the proof: `t ∈ ℚ(√n)` with coprime exponents

Throughout, `t = u + v√n` with `u v : ℚ`, and `t^a + √n`, `t^b + √n` are rational, which means
that the `√n`-coefficients satisfy `B_a = B_b = -1`. The main result is `SimonMarais.core`:
for coprime `1 ≤ a < b` this forces `a = 1`, `b = 2` and `N(t) = u² - nv² < 0`.
-/

@[expose] public section

namespace SimonMarais

open Real Finset

variable {n : ℕ}

/-! ### Two inequalities in `ℝ` (Theorem 9 and the last part of Lemma 10) -/

/-- The ratio argument that replaces the paper's use of Rolle's theorem in Theorem 9: for
`s < p < q`, `((p+s)/(p-s))^β` is not `((q±s)/(q∓s))^α` when `α < β`. -/
theorem ratio_contra {s p q X Y : ℝ} (hs : 0 < s) (hp : s < p) (hpq : p < q) {α β : ℕ}
    (hα : 1 ≤ α) (hαβ : α < β)
    (hXY : (X = q + s ∧ Y = q - s) ∨ (X = q - s ∧ Y = q + s))
    (E1 : (p + s) ^ β = X ^ α) (E2 : (p - s) ^ β = Y ^ α) : False := by
  have hps : 0 < p - s := by linarith
  have hqs : 0 < q - s := by linarith
  have hA : 1 < (p + s) / (p - s) := by rw [one_lt_div hps]; linarith
  have key : ((p + s) / (p - s)) ^ β = (X / Y) ^ α := by rw [div_pow, div_pow, E1, E2]
  rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hB : 1 < (q + s) / (q - s) := by rw [one_lt_div hqs]; linarith
    have hBA : (q + s) / (q - s) < (p + s) / (p - s) := by
      rw [div_lt_div_iff₀ hqs hps]; nlinarith
    have h1 : ((q + s) / (q - s)) ^ β < ((p + s) / (p - s)) ^ β :=
      pow_lt_pow_left₀ hBA (by positivity) (by omega)
    have h2 : ((q + s) / (q - s)) ^ α ≤ ((q + s) / (q - s)) ^ β :=
      pow_le_pow_right₀ hB.le hαβ.le
    linarith
  · have hB : (q - s) / (q + s) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h1 : ((q - s) / (q + s)) ^ α < 1 :=
      pow_lt_one₀ (div_nonneg hqs.le (by linarith)) hB (by omega)
    have h2 : 1 < ((p + s) / (p - s)) ^ β := one_lt_pow₀ hA (by omega)
    linarith

/-- Theorem 9 of the paper, in the form used: `N(t) > 0` is impossible. Here `xa = A_α` and
`xb = A_β`, and `N(t)^c = x_c² - n > 0` means `s² < x_c²`. -/
theorem not_norm_pos {s xa xb : ℝ} (hs : 1 < s) {α β : ℕ} (hα : 1 ≤ α) (hαβ : α < β)
    (h1 : (xa + s) ^ β = (xb + s) ^ α) (h2 : (xa - s) ^ β = (xb - s) ^ α)
    (ha : s ^ 2 < xa ^ 2) (hb : s ^ 2 < xb ^ 2) : False := by
  have E1 : |xa + s| ^ β = |xb + s| ^ α := by rw [← abs_pow, ← abs_pow, h1]
  have E2 : |xa - s| ^ β = |xb - s| ^ α := by rw [← abs_pow, ← abs_pow, h2]
  have hs0 : 0 < s := by linarith
  have hpa : s < |xa| := by simpa [abs_of_pos hs0] using sq_lt_sq.mp ha
  have hpb : s < |xb| := by simpa [abs_of_pos hs0] using sq_lt_sq.mp hb
  -- first, `|xa| < |xb|`
  have hlt : |xa| < |xb| := by
    by_contra hle
    push Not at hle
    have hbig : 1 < |xa| + s := by linarith
    have hgt : (|xa| + s) ^ α < (|xa| + s) ^ β := pow_lt_pow_right₀ hbig hαβ
    rcases le_or_gt 0 xa with hxa | hxa
    · have e : |xa + s| = |xa| + s := by rw [abs_of_nonneg hxa, abs_of_nonneg (by linarith)]
      have : |xb + s| ^ α ≤ (|xa| + s) ^ α :=
        pow_le_pow_left₀ (abs_nonneg _)
          ((abs_add_le _ _).trans (by rw [abs_of_pos hs0]; linarith)) _
      rw [← E1, e] at this; linarith
    · have e : |xa - s| = |xa| + s := by
        rw [abs_of_neg hxa, abs_of_neg (by linarith)]; ring
      have : |xb - s| ^ α ≤ (|xa| + s) ^ α :=
        pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by rw [abs_of_pos hs0]; linarith)) _
      rw [← E2, e] at this; linarith
  set p := |xa|
  set q := |xb|
  have hXY : ∀ y : ℝ, s < |y| →
      (|y + s| = |y| + s ∧ |y - s| = |y| - s) ∨ (|y + s| = |y| - s ∧ |y - s| = |y| + s) := by
    intro y hy
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h] at hy ⊢
      left; exact ⟨abs_of_pos (by linarith), abs_of_pos (by linarith)⟩
    · rw [abs_of_neg h] at hy ⊢
      right; constructor
      · rw [abs_of_neg (by linarith)]; ring
      · rw [abs_of_neg (by linarith)]; ring
  rcases hXY xa hpa with ⟨ea1, ea2⟩ | ⟨ea1, ea2⟩
  · rw [ea1] at E1; rw [ea2] at E2
    refine ratio_contra hs0 hpa hlt hα hαβ ?_ E1 E2
    rcases hXY xb hpb with ⟨eb1, eb2⟩ | ⟨eb1, eb2⟩
    · exact Or.inl ⟨eb1, eb2⟩
    · exact Or.inr ⟨eb1, eb2⟩
  · rw [ea1] at E1; rw [ea2] at E2
    refine ratio_contra hs0 hpa hlt hα hαβ ?_ E2 E1
    rcases hXY xb hpb with ⟨eb1, eb2⟩ | ⟨eb1, eb2⟩
    · exact Or.inr ⟨eb2, eb1⟩
    · exact Or.inl ⟨eb2, eb1⟩

/-- The last part of Lemma 10: `s² < xa²` and `xb² < s²` are incompatible with the equations. -/
theorem not_lt_gt {s xa xb : ℝ} (hs : 1 < s) {α β : ℕ} (hα : 1 ≤ α) (hαβ : α < β)
    (h1 : (xa + s) ^ β = (xb + s) ^ α) (h2 : (xa - s) ^ β = (xb - s) ^ α)
    (ha : s ^ 2 < xa ^ 2) (hb : xb ^ 2 < s ^ 2) : False := by
  have E1 : |xa + s| ^ β = |xb + s| ^ α := by rw [← abs_pow, ← abs_pow, h1]
  have E2 : |xa - s| ^ β = |xb - s| ^ α := by rw [← abs_pow, ← abs_pow, h2]
  have hs0 : 0 < s := by linarith
  have hpa : s < |xa| := by simpa [abs_of_pos hs0] using sq_lt_sq.mp ha
  have hpb : |xb| < s := by simpa [abs_of_pos hs0] using sq_lt_sq.mp hb
  have h2s : 1 ≤ 2 * s := by linarith
  have chain : ∀ z : ℝ, z < 2 * s → |xa| + s = |xa| + s → 0 ≤ z →
      z ^ α < (|xa| + s) ^ β := by
    intro z hz _ hz0
    calc z ^ α < (2 * s) ^ α := pow_lt_pow_left₀ hz hz0 (by omega)
      _ ≤ (2 * s) ^ β := pow_le_pow_right₀ h2s hαβ.le
      _ < (|xa| + s) ^ β := pow_lt_pow_left₀ (by linarith) (by positivity) (by omega)
  rcases le_or_gt 0 xa with hxa | hxa
  · have e : |xa + s| = |xa| + s := by rw [abs_of_nonneg hxa, abs_of_nonneg (by linarith)]
    have := chain |xb + s| (lt_of_le_of_lt (abs_add_le _ _) (by rw [abs_of_pos hs0]; linarith))
      rfl (abs_nonneg _)
    rw [← E1, e] at this; exact lt_irrefl _ this
  · have e : |xa - s| = |xa| + s := by rw [abs_of_neg hxa, abs_of_neg (by linarith)]; ring
    have := chain |xb - s| (lt_of_le_of_lt (abs_sub _ _) (by rw [abs_of_pos hs0]; linarith))
      rfl (abs_nonneg _)
    rw [← E2, e] at this; exact lt_irrefl _ this


theorem lt_two_pow_pred {k : ℕ} (hk : 3 ≤ k) : k < 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have h := Nat.lt_two_pow_self (n := j)
  have : 2 ^ (j + 3 - 1) = 4 * 2 ^ j := by rw [show j + 3 - 1 = j + 2 by omega, pow_add]; ring
  omega

/-! ### Lemma 11: choosing the scaling `M` -/

/-- Lemma 11 of the paper: there is a rational `M ≠ 0` such that `P = M T` and `Q = M² N` are
integers, `P > 0`, and no prime `p` has `p ∣ P` and `p² ∣ Q` (the paper's maximal `λ`). -/
theorem exists_normalized {T N : ℚ} (hT : T ≠ 0) :
    ∃ M : ℚ, M ≠ 0 ∧ ∃ P Q : ℤ, (P : ℚ) = M * T ∧ (Q : ℚ) = M ^ 2 * N ∧ 0 < P ∧
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ P → ¬ (p : ℤ) ^ 2 ∣ Q := by
  have key : ∀ k : ℕ, ∀ M : ℚ, M ≠ 0 → ∀ P Q : ℤ, (P : ℚ) = M * T → (Q : ℚ) = M ^ 2 * N →
      P.natAbs = k → ∃ M : ℚ, M ≠ 0 ∧ ∃ P Q : ℤ, (P : ℚ) = M * T ∧ (Q : ℚ) = M ^ 2 * N ∧
        0 < P ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ P → ¬ (p : ℤ) ^ 2 ∣ Q := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro M hM P Q hP hQ hk
      have hP0 : P ≠ 0 := by
        rintro rfl
        have : M * T = 0 := by rw [← hP]; simp
        rcases mul_eq_zero.mp this with h | h
        · exact hM h
        · exact hT h
      by_cases hgood : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ P → ¬ (p : ℤ) ^ 2 ∣ Q
      · rcases lt_or_gt_of_ne hP0 with hneg | hpos
        · refine ⟨-M, neg_ne_zero.mpr hM, -P, Q, by push_cast; rw [hP]; ring,
            by rw [hQ]; ring, by omega, ?_⟩
          intro p hp hdvd
          exact hgood p hp (by simpa using hdvd)
        · exact ⟨M, hM, P, Q, hP, hQ, hpos, hgood⟩
      · push Not at hgood
        obtain ⟨p, hp, ⟨P', rfl⟩, ⟨Q', rfl⟩⟩ := hgood
        have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hP'0 : P' ≠ 0 := by rintro rfl; simp at hP0
        refine ih P'.natAbs ?_ (M / p) (div_ne_zero hM hp0) P' Q' ?_ ?_ rfl
        · rw [← hk, Int.natAbs_mul, Int.natAbs_natCast]
          have := hp.one_lt
          have : 0 < P'.natAbs := Int.natAbs_pos.mpr hP'0
          nlinarith
        · push_cast at hP
          field_simp
          linarith
        · push_cast at hQ
          field_simp
          linarith
  refine key _ (T.den * N.den : ℚ) (by positivity) (T.num * N.den) (T.den * T.den * N.den * N.num)
    ?_ ?_ rfl
  · push_cast
    rw [← Rat.mul_den_eq_num]; ring
  · push_cast
    rw [← Rat.mul_den_eq_num N]; ring

/-! ### The valuation estimate in Lemma 12 -/

/-- The valuation part of Lemma 12: every prime `p ∣ U_β` has `ν_p(U_β) ≤ ν_p(β)`. -/
theorem val_claim {p : ℕ} [hp : Fact p.Prime] {M u v : ℚ} (hM : M ≠ 0)
    (hu : u ≠ 0) (hv : v ≠ 0) {P Q : ℤ} (hP : (P : ℚ) = M * (2 * u))
    (hQ : (Q : ℚ) = M ^ 2 * (u ^ 2 - n * v ^ 2)) (hQ0 : Q ≠ 0) (hn0 : n ≠ 0)
    (hnorm : (p : ℤ) ∣ P → ¬ (p : ℤ) ^ 2 ∣ Q) {α β : ℕ} (hα3 : 3 ≤ α) (hαo : Odd α)
    (hαβ : α < β) (hcop : α.Coprime β)
    (hUa : ((lucas P Q α : ℤ) : ℚ) = -M ^ (α - 1) / v)
    (hUb : ((lucas P Q β : ℤ) : ℚ) = -M ^ (β - 1) / v)
    (hUb' : ((lucas P Q β : ℤ) : ℚ) = (M * u) ^ (β - 1) * oddSum β (v ^ 2 * n / u ^ 2))
    (hpd : (p : ℤ) ∣ lucas P Q β) :
    padicValRat p ((lucas P Q β : ℤ) : ℚ) ≤ padicValRat p β := by
  have hp1 : 1 < p := hp.out.one_lt
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hn0' : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hvn : (0 : ℤ) ≤ padicValRat p n := by rw [← padicValRat_of_nat]; positivity
  have vint : ∀ z : ℤ, padicValRat p z = padicValInt p z := fun z => padicValRat.of_int
  have hUb0 : ((lucas P Q β : ℤ) : ℚ) ≠ 0 := by
    rw [hUb]; exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hM)) hv
  have hUb0' : lucas P Q β ≠ 0 := by exact_mod_cast hUb0
  have hvb1 : 1 ≤ padicValRat p ((lucas P Q β : ℤ) : ℚ) := by
    rw [vint]
    rcases (padicValInt_dvd_iff (p := p) 1 (lucas P Q β)).mp (by simpa using hpd) with h | h
    · exact absurd h hUb0'
    · exact_mod_cast h
  -- Step 1: `ν_p(U_α) < ν_p(U_β)` and `ν_p(U_α) < α - 1`.
  obtain ⟨s1, s2⟩ : padicValRat p ((lucas P Q α : ℤ) : ℚ) < padicValRat p ((lucas P Q β : ℤ) : ℚ) ∧
      padicValRat p ((lucas P Q α : ℤ) : ℚ) < ((α - 1 : ℕ) : ℤ) := by
    obtain ⟨j, hj⟩ := hαo
    by_cases hs : (p : ℤ) ∣ P ∧ (p : ℤ) ∣ Q
    · obtain ⟨X, hX, hpX⟩ := lucas_special_odd P Q hpZ hs.1 hs.2 (hnorm hs.1) j
      have hX0 : (X : ℚ) ≠ 0 := by
        intro h; apply hpX; rw [show X = 0 by exact_mod_cast h]; exact dvd_zero _
      have hvA : padicValRat p ((lucas P Q α : ℤ) : ℚ) = j := by
        rw [hj, hX]; push_cast
        rw [padicValRat.mul (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hX0,
          padicValRat.pow, padicValRat.self hp1, vint, padicValInt.eq_zero_of_not_dvd hpX]
        simp
      have hdB := lucas_special_dvd P Q hs.1 hs.2 β
      have hvB : ((β / 2 : ℕ) : ℤ) ≤ padicValRat p ((lucas P Q β : ℤ) : ℚ) := by
        rw [vint]
        rcases (padicValInt_dvd_iff (p := p) (β / 2) (lucas P Q β)).mp hdB with h | h
        · exact absurd h hUb0'
        · exact_mod_cast h
      rw [hvA]
      constructor
      · have : j + 1 ≤ β / 2 := by omega
        have h' : (j : ℤ) + 1 ≤ ((β / 2 : ℕ) : ℤ) := by exact_mod_cast this
        linarith
      · have : j < α - 1 := by omega
        exact_mod_cast this
    · have hnd := lucas_not_dvd_both P Q hp.out hs (by omega) (by omega) hcop
      have hna : ¬ (p : ℤ) ∣ lucas P Q α := fun h => hnd ⟨h, hpd⟩
      have hvA : padicValRat p ((lucas P Q α : ℤ) : ℚ) = 0 := by
        rw [vint, padicValInt.eq_zero_of_not_dvd hna]; simp
      rw [hvA]
      constructor
      · linarith
      · have : 0 < α - 1 := by omega
        exact_mod_cast this
  -- Step 2: `ν_p(M) ≥ 1` and `ν_p(v) ≥ 1`.
  have hvUa : padicValRat p ((lucas P Q α : ℤ) : ℚ) = ((α - 1 : ℕ) : ℤ) * padicValRat p M -
      padicValRat p v := by
    rw [hUa, padicValRat.div (neg_ne_zero.mpr (pow_ne_zero _ hM)) hv, padicValRat.neg,
      padicValRat.pow]
  have hvUb : padicValRat p ((lucas P Q β : ℤ) : ℚ) = ((β - 1 : ℕ) : ℤ) * padicValRat p M -
      padicValRat p v := by
    rw [hUb, padicValRat.div (neg_ne_zero.mpr (pow_ne_zero _ hM)) hv, padicValRat.neg,
      padicValRat.pow]
  have hμ : 1 ≤ padicValRat p M := by
    have hlt : ((α - 1 : ℕ) : ℤ) < ((β - 1 : ℕ) : ℤ) := by
      exact_mod_cast (show α - 1 < β - 1 by omega)
    by_contra hc
    push Not at hc
    nlinarith
  have hνv : 1 ≤ padicValRat p v := by
    have : ((α - 1 : ℕ) : ℤ) * 1 ≤ ((α - 1 : ℕ) : ℤ) * padicValRat p M :=
      mul_le_mul_of_nonneg_left hμ (by positivity)
    linarith
  -- Step 3: `ν_p(M u) ≤ 0`, by the normalization of `M`.
  have hMu0 : M * u ≠ 0 := mul_ne_zero hM hu
  have hMv0 : M * v ≠ 0 := mul_ne_zero hM hv
  have hMu : padicValRat p (M * u) ≤ 0 := by
    by_contra hc
    push Not at hc
    apply hnorm
    · have hval : 1 ≤ padicValRat p P := by
        rw [hP, show M * (2 * u) = 2 * (M * u) by ring, padicValRat.mul two_ne_zero hMu0]
        have : (0 : ℤ) ≤ padicValRat p 2 := by
          rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, ← padicValRat_of_nat]
          exact Nat.cast_nonneg _
        linarith
      rw [vint] at hval
      simpa using (padicValInt_dvd_iff (p := p) 1 P).mpr (Or.inr (by exact_mod_cast hval))
    · have hQ' : (Q : ℚ) = (M * u) ^ 2 + -((M * v) ^ 2 * n) := by rw [hQ]; ring
      have hQq : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ0
      have hmin := padicValRat.min_le_padicValRat_add (p := p) (q := (M * u) ^ 2)
        (r := -((M * v) ^ 2 * n)) (by rw [← hQ']; exact hQq)
      rw [← hQ', padicValRat.neg, padicValRat.pow, padicValRat.mul (pow_ne_zero _ hMv0) hn0',
        padicValRat.pow, padicValRat.mul hM hv] at hmin
      have hval : 2 ≤ padicValRat p Q := by
        refine le_trans ?_ hmin
        apply le_min
        · push_cast; linarith
        · push_cast; linarith
      rw [vint] at hval
      exact (padicValInt_dvd_iff (p := p) 2 Q).mpr (Or.inr (by exact_mod_cast hval))
  -- Step 4: `ν_p(v²n/u²) ≥ 2`.
  have hνu : padicValRat p u ≤ -1 := by
    have := padicValRat.mul (p := p) hM hu
    linarith
  have hνρ : 2 ≤ padicValRat p (v ^ 2 * n / u ^ 2) := by
    rw [padicValRat.div (mul_ne_zero (pow_ne_zero _ hv) hn0') (pow_ne_zero _ hu),
      padicValRat.mul (pow_ne_zero _ hv) hn0', padicValRat.pow, padicValRat.pow]
    push_cast
    linarith
  -- Step 5: the binomial sum has valuation exactly `ν_p(β)`.
  have hS := padicValRat_oddSum (p := p) (b := β) (by omega) (Or.inr hνρ)
  have hS0 : oddSum β (v ^ 2 * n / u ^ 2) ≠ 0 := by
    intro h; apply hUb0; rw [hUb', h, mul_zero]
  rw [hUb', padicValRat.mul (pow_ne_zero _ hMu0) hS0, padicValRat.pow, hS]
  have : (0 : ℤ) ≤ ((β - 1 : ℕ) : ℤ) := by positivity
  nlinarith


/-! ### Theorem 13, case `a = 1` -/

/-- Theorem 13 of the paper when `a = 1` (so `t = x_a - √n`, i.e. `v = -1`): then `b = 2`. -/
theorem beta_eq_two (hn : ¬ IsSquare n) {u : ℚ} (hu : u ≠ 0) {β : ℕ} (hβ : 2 ≤ β)
    (hB : coeffB n u (-1) β = -1) : β = 2 := by
  by_contra hne
  have hβ3 : 3 ≤ β := by omega
  have hn0 : (n : ℚ) ≠ 0 := by have := two_le_of_not_isSquare hn; positivity
  have h := coeffB_eq_oddSum hn hu (-1) (b := β) (by omega)
  rw [hB] at h
  have hρ : (-1 : ℚ) ^ 2 * n / u ^ 2 = n / u ^ 2 := by ring
  rw [hρ] at h
  set S := oddSum β (n / u ^ 2) with hSdef
  have hS1 : u ^ (β - 1) * S = 1 := by linear_combination h
  have hSge : (β : ℚ) ≤ S := oddSum_ge (by omega) (by positivity)
  have hβq : (3 : ℚ) ≤ β := by exact_mod_cast hβ3
  -- `|u| < 1`
  have hu1 : |u| < 1 := by
    by_contra hc
    push Not at hc
    have h1 : 1 ≤ |u| ^ (β - 1) := one_le_pow₀ hc
    have h2 : |u ^ (β - 1) * S| = |u| ^ (β - 1) * S := by
      rw [abs_mul, abs_pow, abs_of_pos (by linarith : (0 : ℚ) < S)]
    rw [hS1, abs_one] at h2
    nlinarith
  -- so `u` is not an integer, and some prime `p` divides its denominator
  have hden : u.den ≠ 1 := by
    intro h1
    have e : (u.num : ℚ) = u := by
      rw [← Rat.mul_den_eq_num, h1]; simp
    have hnum : u.num ≠ 0 := Rat.num_ne_zero.mpr hu
    have : (1 : ℚ) ≤ |u| := by
      rw [← e, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs hnum
    linarith
  set p := u.den.minFac
  have hp : p.Prime := Nat.minFac_prime hden
  have := Fact.mk hp
  have hνu : padicValRat p u ≤ -1 := by
    rw [padicValRat_def]
    have h1 : padicValInt p u.num = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro hd
      have h1 : p ∣ u.num.natAbs := Int.natCast_dvd.mp hd
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes u.reduced h1 (Nat.minFac_dvd _))
    have h2 : 1 ≤ padicValNat p u.den := by
      rw [← padicValNat_dvd_iff_le u.den_nz, pow_one]; exact Nat.minFac_dvd _
    rw [h1]
    omega
  have hνρ : 2 ≤ padicValRat p (n / u ^ 2) := by
    rw [padicValRat.div hn0 (pow_ne_zero _ hu), padicValRat.pow]
    have : (0 : ℤ) ≤ padicValRat p n := by rw [← padicValRat_of_nat]; positivity
    push_cast
    linarith
  have hνS := padicValRat_oddSum (p := p) (b := β) (by omega) (Or.inr hνρ)
  have hS0 : S ≠ 0 := by intro h0; rw [h0] at hSge; linarith
  have key := congrArg (padicValRat p) hS1
  rw [padicValRat.mul (pow_ne_zero _ hu) hS0, padicValRat.pow, hSdef, hνS,
    padicValRat.one, ← padicValRat_of_nat] at key
  have hβval : β - 1 ≤ padicValNat p β := by
    have h1 : ((β - 1 : ℕ) : ℤ) * padicValRat p u ≤ -((β - 1 : ℕ) : ℤ) := by
      have : (0 : ℤ) ≤ ((β - 1 : ℕ) : ℤ) := by positivity
      nlinarith
    have : ((β - 1 : ℕ) : ℤ) ≤ (padicValNat p β : ℤ) := by linarith
    exact_mod_cast this
  have hdvd : p ^ (β - 1) ∣ β := (padicValNat_dvd_iff_le (by omega)).mpr hβval
  have h2 : 2 ^ (β - 1) ≤ β :=
    (Nat.pow_le_pow_left hp.two_le _).trans (Nat.le_of_dvd (by omega) hdvd)
  have := lt_two_pow_pred hβ3
  omega

/-! ### Theorem 13, case `a > 1` -/

/-- Theorem 13 of the paper when `a > 1`: impossible. -/
theorem not_three_le (hn : ¬ IsSquare n) {u v : ℚ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hN : u ^ 2 - n * v ^ 2 < 0) {α β : ℕ} (hα3 : 3 ≤ α) (hαo : Odd α) (hαβ : α < β)
    (hcop : α.Coprime β) (hBa : coeffB n u v α = -1) (hBb : coeffB n u v β = -1) : False := by
  have hn0 : n ≠ 0 := by have := two_le_of_not_isSquare hn; omega
  obtain ⟨M, hM, P, Q, hP, hQ, hP0, hnorm⟩ :=
    exists_normalized (T := 2 * u) (N := u ^ 2 - n * v ^ 2) (mul_ne_zero two_ne_zero hu)
  have hQneg : Q < 0 := by
    have : (Q : ℚ) < 0 := by rw [hQ]; exact mul_neg_of_pos_of_neg (by positivity) hN
    exact_mod_cast this
  have hcast : ∀ k, ((lucas P Q k : ℤ) : ℚ) =
      lucas (M * (2 * u)) (M ^ 2 * (u ^ 2 - n * v ^ 2)) k := by
    intro k
    rw [← hP, ← hQ]
    exact map_lucas P Q (Int.castRingHom ℚ) k
  have hU : ∀ c, 1 ≤ c → coeffB n u v c = -1 → ((lucas P Q c : ℤ) : ℚ) = -M ^ (c - 1) / v := by
    intro c hc hB
    have h1 := lucas_scale (2 * u) (u ^ 2 - n * v ^ 2) M c
    rw [← hcast] at h1
    have h2 := coeffB_eq_lucas (n := n) u v c
    rw [hB] at h2
    have hL : lucas (2 * u) (u ^ 2 - n * v ^ 2) c = -1 / v := by
      field_simp; linear_combination -h2
    rw [hL, show M ^ c = M * M ^ (c - 1) by rw [← pow_succ']; congr 1; omega, mul_assoc] at h1
    rw [mul_left_cancel₀ hM h1]
    ring
  have hUa := hU α (by omega) hBa
  have hUb := hU β (by omega) hBb
  have hUb' : ((lucas P Q β : ℤ) : ℚ) = (M * u) ^ (β - 1) * oddSum β (v ^ 2 * n / u ^ 2) := by
    have h := coeffB_eq_oddSum hn hu v (b := β) (by omega)
    rw [hBb] at h
    have hS : u ^ (β - 1) * oddSum β (v ^ 2 * n / u ^ 2) = -1 / v := by
      field_simp; linear_combination -h
    rw [hUb, mul_pow, mul_assoc, hS]
    ring
  -- `U_β ∣ β`
  have hUbpos : 0 < lucas P Q β := lucas_pos hP0 hQneg (by omega)
  have hdvd : (lucas P Q β).natAbs ∣ β := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    have hp' : p.Prime := hp
    have := Fact.mk hp'
    rcases k with _ | k
    · simp
    have hpd : (p : ℤ) ∣ lucas P Q β :=
      Int.natCast_dvd.mpr ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hpk)
    have hval := val_claim (p := p) hM hu hv hP hQ hQneg.ne hn0 (hnorm p hp') hα3 hαo hαβ hcop
      hUa hUb hUb' hpd
    rw [padicValRat.of_int, ← padicValRat_of_nat] at hval
    unfold padicValInt at hval
    have hle : k + 1 ≤ padicValNat p (lucas P Q β).natAbs :=
      (padicValNat_dvd_iff_le (by omega)).mp hpk
    exact (padicValNat_dvd_iff_le (by omega)).mpr
      (by exact_mod_cast hle.trans (by exact_mod_cast hval))
  have hle : lucas P Q β ≤ β := by
    have h1 := Nat.le_of_dvd (by omega) hdvd
    have h2 := Int.natAbs_of_nonneg hUbpos.le
    omega
  -- growth
  by_cases hbig : 5 < β ∨ (3 < β ∧ (1 < P ∨ Q < -1))
  · have := lucas_gt_self hP0 hQneg hbig
    omega
  push Not at hbig
  obtain ⟨hb5, hb3⟩ := hbig
  obtain ⟨hP1, hQ1⟩ := hb3 (by omega)
  obtain rfl : P = 1 := by omega
  obtain rfl : Q = -1 := by omega
  have hb4 : 4 ≤ β := by omega
  interval_cases β
  · have : lucas (1 : ℤ) (-1) 4 = 3 := by decide
    rw [this] at hdvd
    norm_num at hdvd
  · obtain rfl : α = 3 := by obtain ⟨j, rfl⟩ := hαo; omega
    have e5 : lucas (1 : ℤ) (-1) 5 = 5 := by decide
    have e3 : lucas (1 : ℤ) (-1) 3 = 2 := by decide
    rw [e5] at hUb
    rw [e3] at hUa
    push_cast at hUa hUb
    have h5 : (5 : ℚ) = M ^ 2 * 2 := by
      rw [hUb, hUa]; ring
    have : (2 * M) ^ 2 = (10 : ℕ) * 1 ^ 2 := by push_cast; linarith
    have h10 : ¬ IsSquare 10 := by
      rintro ⟨r, hr⟩
      have : r ≤ 4 := by nlinarith
      interval_cases r <;> omega
    exact one_ne_zero (eq_zero_of_sq_eq (n := 10) h10 this)

/-! ### The core theorem -/

/-- The heart of the paper (Lemmas 8, 10 and Theorems 9, 13): if `t = u + v√n` and `t^α + √n`,
`t^β + √n` are rational, with `α < β` coprime, then `α = 1`, `β = 2` and `N(t) < 0`. -/
theorem core (hn : ¬ IsSquare n) {α β : ℕ} (hα : 1 ≤ α) (hαβ : α < β) (hcop : α.Coprime β)
    {u v : ℚ} (hBa : coeffB n u v α = -1) (hBb : coeffB n u v β = -1) :
    α = 1 ∧ β = 2 ∧ u ^ 2 - n * v ^ 2 < 0 := by
  have hs1 := one_lt_sqrt hn
  have hsq : (√(n : ℝ)) ^ 2 = n := sq_sqrt_nat n
  have hr : ∀ c, coeffB n u v c = -1 →
      ((u : ℝ) + v * √(n : ℝ)) ^ c = coeffA n u v c - √(n : ℝ) := by
    intro c h; rw [pow_eq_coeff, h]; push_cast; ring
  have hrb : ∀ c, coeffB n u v c = -1 →
      ((u : ℝ) - v * √(n : ℝ)) ^ c = coeffA n u v c + √(n : ℝ) := by
    intro c h; rw [conj_pow_eq_coeff, h]; push_cast; ring
  have h1 : ((coeffA n u v α : ℝ) + √(n : ℝ)) ^ β = (coeffA n u v β + √(n : ℝ)) ^ α := by
    rw [← hrb α hBa, ← hrb β hBb, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have h2 : ((coeffA n u v α : ℝ) - √(n : ℝ)) ^ β = (coeffA n u v β - √(n : ℝ)) ^ α := by
    rw [← hr α hBa, ← hr β hBb, ← pow_mul, ← pow_mul, Nat.mul_comm]
  -- Lemma 8, item 1: `N^c = x_c² - n`
  have hnorm : ∀ c, coeffB n u v c = -1 →
      (u ^ 2 - n * v ^ 2) ^ c = coeffA n u v c ^ 2 - n := by
    intro c h
    have e : (((u : ℝ) + v * √(n : ℝ)) * (u - v * √(n : ℝ))) ^ c =
        ((coeffA n u v c : ℝ) - √(n : ℝ)) * (coeffA n u v c + √(n : ℝ)) := by
      rw [mul_pow, hr c h, hrb c h]
    have e2 : ((u : ℝ) + v * √(n : ℝ)) * (u - v * √(n : ℝ)) = ((u ^ 2 - n * v ^ 2 : ℚ) : ℝ) := by
      push_cast; linear_combination (-(v : ℝ) ^ 2) * hsq
    have e3 : ((coeffA n u v c : ℝ) - √(n : ℝ)) * (coeffA n u v c + √(n : ℝ)) =
        ((coeffA n u v c ^ 2 - n : ℚ) : ℝ) := by
      push_cast; linear_combination (-1 : ℝ) * hsq
    rw [e2, e3, ← Rat.cast_pow] at e
    exact_mod_cast e
  have hv : v ≠ 0 := by
    rintro rfl
    rw [coeffB_eq_lucas] at hBa
    simp at hBa
  have hN0 : u ^ 2 - n * v ^ 2 ≠ 0 := by
    intro h; exact hv (eq_zero_of_sq_eq hn (u := u) (v := v) (by linarith))
  have hsqlt : ∀ c, coeffB n u v c = -1 → 0 < (u ^ 2 - n * v ^ 2) ^ c →
      (√(n : ℝ)) ^ 2 < (coeffA n u v c : ℝ) ^ 2 := by
    intro c h hpos
    rw [hnorm c h] at hpos
    rw [hsq]; exact_mod_cast (by linarith : (n : ℚ) < coeffA n u v c ^ 2)
  -- Theorem 9 and Lemma 10: `N < 0`
  have hNneg : u ^ 2 - n * v ^ 2 < 0 := by
    by_contra hc
    push Not at hc
    have hpos : 0 < u ^ 2 - n * v ^ 2 := lt_of_le_of_ne hc (Ne.symm hN0)
    exact not_norm_pos hs1 hα hαβ h1 h2 (hsqlt α hBa (pow_pos hpos _))
      (hsqlt β hBb (pow_pos hpos _))
  -- Lemma 10: `u ≠ 0`
  have hu : u ≠ 0 := by
    rintro rfl
    have hB : ∀ c, coeffB n 0 v c = -1 → ∃ j, c = 2 * j + 1 ∧ v * (n * v ^ 2) ^ j = -1 := by
      intro c h
      rw [coeffB_eq_lucas, show (2 : ℚ) * 0 = 0 by ring] at h
      rcases Nat.even_or_odd' c with ⟨j, rfl | rfl⟩
      · rw [(lucas_zero_left _ j).1] at h; simp at h
      · refine ⟨j, rfl, ?_⟩
        rw [(lucas_zero_left _ j).2] at h
        rw [← h]; ring
    obtain ⟨j, rfl, hj⟩ := hB α hBa
    obtain ⟨j', rfl, hj'⟩ := hB β hBb
    have hw : 0 < (n : ℚ) * v ^ 2 := by
      have := two_le_of_not_isSquare hn
      have : (0 : ℚ) < n := by positivity
      positivity
    have hw1 : (n : ℚ) * v ^ 2 ≠ 1 := by
      intro h; exact hv (eq_zero_of_sq_eq hn (u := 1) (by rw [h]; ring))
    have : ((n : ℚ) * v ^ 2) ^ j = ((n : ℚ) * v ^ 2) ^ j' := by
      apply mul_left_cancel₀ hv; rw [hj, hj']
    have := pow_right_injective₀ hw hw1 this
    omega
  -- Lemma 10: `α` is odd
  have hαodd : Odd α := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have hβodd : Odd β := by
      by_contra h
      rw [Nat.not_odd_iff_even] at h
      have := Nat.eq_one_of_dvd_coprimes hcop (even_iff_two_dvd.mp hev) (even_iff_two_dvd.mp h)
      omega
    apply not_lt_gt hs1 hα hαβ h1 h2 (hsqlt α hBa (hev.pow_pos hN0))
    have hneg := hβodd.pow_neg hNneg
    rw [hnorm β hBb] at hneg
    rw [hsq]; exact_mod_cast (by linarith : coeffA n u v β ^ 2 < (n : ℚ))
  rcases Nat.lt_or_ge α 3 with hlt | hge
  · obtain rfl : α = 1 := by obtain ⟨j, rfl⟩ := hαodd; omega
    obtain rfl : v = -1 := by simpa [coeffB_succ] using hBa
    exact ⟨rfl, beta_eq_two hn hu (by omega) hBb, hNneg⟩
  · exact (not_three_le hn hu hv hNneg hge hαodd hαβ hcop hBa hBb).elim

end SimonMarais
