module

public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Lucas sequences

The Lucas sequence `U_k(P, Q)`: `U_0 = 0`, `U_1 = 1`, `U_{k+2} = P U_{k+1} - Q U_k`.

We prove the special cases of the results from Ballot–Williams, *The Lucas Sequences* (2023),
that the Simon Marais paper cites, with elementary proofs:

* `SimonMarais.lucas_not_dvd_both` — a prime `p ∤ gcd(P, Q)` cannot divide both `U_a` and `U_b`
  when `gcd(a, b) = 1`. This is the case of the paper's Theorem 3 (Ballot–Williams, Theorem 6)
  that the proof uses.
* `SimonMarais.lucas_special_dvd`, `SimonMarais.lucas_special_odd` — if `p ∣ P` and `p ∥ Q`,
  then `p^⌊k/2⌋ ∣ U_k`, with exact valuation for odd `k`. This is the paper's Corollary 5 (from its
  Theorem 4, Ballot–Williams Theorem 46).
* `SimonMarais.lucas_gt_self` — growth when `P > 0 > Q` (Lemma 6).
-/

@[expose] public section

namespace SimonMarais

/-- The Lucas sequence `U_k(P, Q)`. -/
def lucas {R : Type*} [CommRing R] (P Q : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | k + 2 => P * lucas P Q (k + 1) - Q * lucas P Q k

section Ring

variable {R S : Type*} [CommRing R] [CommRing S] (P Q : R)

@[simp] theorem lucas_zero : lucas P Q 0 = 0 := rfl
@[simp] theorem lucas_one : lucas P Q 1 = 1 := rfl
theorem lucas_add_two (k : ℕ) :
    lucas P Q (k + 2) = P * lucas P Q (k + 1) - Q * lucas P Q k := rfl

theorem map_lucas (f : R →+* S) (k : ℕ) : f (lucas P Q k) = lucas (f P) (f Q) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simp
    | k + 2 => simp [lucas_add_two, ih k (by omega), ih (k + 1) (by omega)]

/-- `U_{m+n+1} = U_{m+1} U_{n+1} - Q U_m U_n`. -/
theorem lucas_add (m n : ℕ) :
    lucas P Q (m + n + 1) =
      lucas P Q (m + 1) * lucas P Q (n + 1) - Q * lucas P Q m * lucas P Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp [lucas_add_two]; ring
    | n + 2 =>
      have h1 := ih n (by omega)
      have h2 := ih (n + 1) (by omega)
      rw [show m + (n + 2) + 1 = (m + n + 1) + 2 by omega, lucas_add_two,
        show m + n + 1 + 1 = m + (n + 1) + 1 by omega, h2, h1, lucas_add_two P Q (n + 1),
        lucas_add_two P Q n]
      ring

/-- Lucas sequences are divisibility sequences. -/
theorem lucas_dvd_lucas_mul (m k : ℕ) : lucas P Q m ∣ lucas P Q (k * m) := by
  rcases m with _ | m
  · simp
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * (m + 1) = k * (m + 1) + m + 1 by ring, lucas_add]
    exact dvd_sub (dvd_mul_left _ _) (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ih _) _)

/-- With `P = 0`: `U_{2j} = 0` and `U_{2j+1} = (-Q)^j`. -/
theorem lucas_zero_left (j : ℕ) :
    lucas 0 Q (2 * j) = 0 ∧ lucas 0 Q (2 * j + 1) = (-Q) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    refine ⟨?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring, lucas_add_two, ih.1]; ring
    · rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, lucas_add_two, ih.2]; ring

end Ring

section Field

variable {K : Type*} [Field K]

/-- Rescaling: `M · U_k(MP, M²Q) = M^k · U_k(P, Q)`. -/
theorem lucas_scale (P Q M : K) (k : ℕ) :
    M * lucas (M * P) (M ^ 2 * Q) k = M ^ k * lucas P Q k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      have h1 := ih k (by omega)
      have h2 := ih (k + 1) (by omega)
      rw [lucas_add_two, lucas_add_two]
      linear_combination (M * P) * h2 - (M ^ 2 * Q) * h1

end Field

section Int

variable (P Q : ℤ)

/-- If `p ∤ Q`, then `p` never divides two consecutive terms. -/
theorem lucas_not_dvd_consecutive {p : ℤ} (hp : Prime p) (hQ : ¬ p ∣ Q) (k : ℕ) :
    ¬ (p ∣ lucas P Q k ∧ p ∣ lucas P Q (k + 1)) := by
  induction k with
  | zero => simpa using hp.not_dvd_one
  | succ k ih =>
    rintro ⟨h1, h2⟩
    apply ih
    refine ⟨?_, h1⟩
    rw [lucas_add_two] at h2
    have : p ∣ Q * lucas P Q k := by
      have := dvd_sub (dvd_mul_of_dvd_right h1 P) h2
      simpa using this
    exact (hp.dvd_or_dvd this).resolve_left hQ

/-- If `p ∣ Q`, then `U_{k+1} ≡ P^k (mod p)`. -/
theorem lucas_modEq_of_dvd_Q {p : ℤ} (hQ : p ∣ Q) (k : ℕ) : p ∣ lucas P Q (k + 1) - P ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | k + 1 =>
      have h := ih k (by omega)
      rw [show k + 1 + 1 = k + 2 by omega, lucas_add_two,
        show P * lucas P Q (k + 1) - Q * lucas P Q k - P ^ (k + 1) =
          P * (lucas P Q (k + 1) - P ^ k) - Q * lucas P Q k by ring]
      exact dvd_sub (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_left hQ _)

/-- Strong divisibility, in the form the paper uses: a prime `p` that does not divide both `P`
and `Q` cannot divide both `U_a` and `U_b` when `a` and `b` are coprime. -/
theorem lucas_not_dvd_both {p : ℕ} (hp : p.Prime) (hPQ : ¬ ((p : ℤ) ∣ P ∧ (p : ℤ) ∣ Q))
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    ¬ ((p : ℤ) ∣ lucas P Q a ∧ (p : ℤ) ∣ lucas P Q b) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rintro ⟨hA, hB⟩
  by_cases hQ : (p : ℤ) ∣ Q
  · have hP : ¬ (p : ℤ) ∣ P := fun h => hPQ ⟨h, hQ⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have := lucas_modEq_of_dvd_Q P Q hQ a'
    have hpow : (p : ℤ) ∣ P ^ a' := by simpa using dvd_sub hA this
    exact hP (hpZ.dvd_of_dvd_pow hpow)
  · rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · obtain rfl : b = 1 := by omega
      exact hpZ.not_dvd_one (by simpa using hB)
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hab (by omega)
    have h1 : (p : ℤ) ∣ lucas P Q (m * a) := hA.trans (lucas_dvd_lucas_mul P Q a m)
    have h2 : (p : ℤ) ∣ lucas P Q (a * m / b * b) := hB.trans (lucas_dvd_lucas_mul P Q b _)
    have he : m * a = a * m / b * b + 1 := by
      have := Nat.div_add_mod (a * m) b
      rw [hm] at this
      rw [mul_comm m a]; linarith [Nat.mul_comm b (a * m / b)]
    rw [he] at h1
    exact lucas_not_dvd_consecutive P Q hpZ hQ _ ⟨h2, h1⟩

/-- The special-prime case with `p ∥ Q`: writing `P = p P₁` and `Q = p Q₁` with `p ∤ Q₁`,
`U_{2j+1} = p^j X` and `U_{2j+2} = p^{j+1} Y` with `X ≡ (-Q₁)^j (mod p)`. -/
theorem lucas_special_aux {p P₁ Q₁ : ℤ} (j : ℕ) :
    ∃ X Y : ℤ, lucas (p * P₁) (p * Q₁) (2 * j + 1) = p ^ j * X ∧
      lucas (p * P₁) (p * Q₁) (2 * j + 2) = p ^ (j + 1) * Y ∧ p ∣ X - (-Q₁) ^ j := by
  induction j with
  | zero => exact ⟨1, P₁, by simp, by simp [lucas_add_two], by simp⟩
  | succ j ih =>
    obtain ⟨X, Y, hX, hY, hXm⟩ := ih
    set X' := p * P₁ * Y - Q₁ * X
    have hX' : lucas (p * P₁) (p * Q₁) (2 * (j + 1) + 1) = p ^ (j + 1) * X' := by
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, lucas_add_two,
        show 2 * j + 1 + 1 = 2 * j + 2 by ring, hY, hX]
      ring
    refine ⟨X', P₁ * X' - Q₁ * Y, hX', ?_, ?_⟩
    · rw [show 2 * (j + 1) + 2 = (2 * j + 2) + 2 by ring, lucas_add_two,
        show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by ring, hX', hY]
      ring
    · have : X' - (-Q₁) ^ (j + 1) = p * (P₁ * Y) + (-Q₁) * (X - (-Q₁) ^ j) := by ring
      rw [this]
      exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right hXm _)

/-- If `p ∣ P`, `p ∣ Q` and `p² ∤ Q`, then `p^⌊k/2⌋ ∣ U_k` for every `k`. -/
theorem lucas_special_dvd {p : ℤ} (hP : p ∣ P) (hQ : p ∣ Q) (k : ℕ) :
    p ^ (k / 2) ∣ lucas P Q k := by
  obtain ⟨P₁, rfl⟩ := hP
  obtain ⟨Q₁, rfl⟩ := hQ
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rcases j with _ | j
    · simp
    obtain ⟨X, Y, -, hY, -⟩ := lucas_special_aux (p := p) (P₁ := P₁) (Q₁ := Q₁) j
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, hY, show (2 * j + 2) / 2 = j + 1 by omega]
    exact dvd_mul_right _ _
  · obtain ⟨X, Y, hX, -, -⟩ := lucas_special_aux (p := p) (P₁ := P₁) (Q₁ := Q₁) j
    rw [hX, show (2 * j + 1) / 2 = j by omega]
    exact dvd_mul_right _ _

/-- If `p ∣ P`, `p ∣ Q` and `p² ∤ Q`, then for odd `k = 2j + 1`, `U_k = p^j X` with `p ∤ X`. -/
theorem lucas_special_odd {p : ℤ} (hp : Prime p) (hP : p ∣ P) (hQ : p ∣ Q) (hQ2 : ¬ p ^ 2 ∣ Q)
    (j : ℕ) : ∃ X, lucas P Q (2 * j + 1) = p ^ j * X ∧ ¬ p ∣ X := by
  obtain ⟨P₁, rfl⟩ := hP
  obtain ⟨Q₁, rfl⟩ := hQ
  obtain ⟨X, Y, hX, -, hXm⟩ := lucas_special_aux (p := p) (P₁ := P₁) (Q₁ := Q₁) j
  refine ⟨X, hX, fun h => ?_⟩
  have hQ₁ : ¬ p ∣ Q₁ := fun h' => hQ2 (by rw [pow_two]; exact mul_dvd_mul_left p h')
  have : p ∣ (-Q₁) ^ j := by simpa using dvd_sub h hXm
  exact hQ₁ (by simpa using hp.dvd_of_dvd_pow this)

/-! ### Growth when `P > 0 > Q` -/

variable {P Q}

theorem lucas_growth (hP : 0 < P) (hQ : Q < 0) (k : ℕ) :
    0 ≤ lucas P Q k ∧ lucas P Q (k + 1) + lucas P Q k ≤ lucas P Q (k + 2) ∧
      0 < lucas P Q (k + 1) := by
  induction k with
  | zero => simp [lucas_add_two]; omega
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have h3 : 0 < lucas P Q (k + 2) := by linarith
    refine ⟨h2.le, ?_, h3⟩
    rw [lucas_add_two P Q (k + 1)]
    nlinarith

theorem lucas_pos (hP : 0 < P) (hQ : Q < 0) {k : ℕ} (hk : 0 < k) : 0 < lucas P Q k := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact (lucas_growth hP hQ k).2.2

theorem lucas_gt_of_two {m : ℕ} (hP : 0 < P) (hQ : Q < 0) (h1 : (m : ℤ) < lucas P Q m)
    (h2 : (m + 1 : ℤ) < lucas P Q (m + 1)) (k : ℕ) : (m + k : ℤ) < lucas P Q (m + k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simpa using h1
    | 1 => simpa using h2
    | k + 2 =>
      have a := ih k (by omega)
      have b := ih (k + 1) (by omega)
      have c := (lucas_growth hP hQ (m + k)).2.1
      have d : (0 : ℤ) ≤ m := by positivity
      push_cast at a b ⊢
      rw [show m + (k + 2) = m + k + 2 by ring]
      rw [show m + (k + 1) = m + k + 1 by ring] at b
      linarith

/-- Lemma 6 of the paper: `U_k > k` for `k > 5`, and for `k > 3` if `P > 1` or `Q < -1`. -/
theorem lucas_gt_self (hP : 0 < P) (hQ : Q < 0) {k : ℕ} (hk : 5 < k ∨ (3 < k ∧ (1 < P ∨ Q < -1))) :
    (k : ℤ) < lucas P Q k := by
  have g := lucas_growth hP hQ
  have u2 : lucas P Q 2 = P := by simp [lucas_add_two]
  have u3 : lucas P Q 3 = P ^ 2 - Q := by simp [lucas_add_two]; ring
  have u4 : lucas P Q 4 = P * (P ^ 2 - Q) - Q * P := by rw [lucas_add_two, u3, u2]
  have u5 : lucas P Q 5 = P * lucas P Q 4 - Q * (P ^ 2 - Q) := by rw [lucas_add_two, u3]
  rcases hk with hk | ⟨hk, hPQ⟩
  · have u6 := (g 4).2.1
    have u7 := (g 5).2.1
    have h6 : (6 : ℤ) < lucas P Q 6 := by
      have : (1 : ℤ) ≤ P := hP
      have : (1 : ℤ) ≤ -Q := by omega
      nlinarith
    have h7 : (7 : ℤ) < lucas P Q 7 := by
      have : (1 : ℤ) ≤ P := hP
      have : (1 : ℤ) ≤ -Q := by omega
      nlinarith
    have := lucas_gt_of_two (m := 6) hP hQ (by simpa using h6) (by simpa using h7) (k - 6)
    rw [show 6 + (k - 6) = k by omega] at this
    have e : ((k : ℕ) : ℤ) = 6 + ((k - 6 : ℕ) : ℤ) := by omega
    push_cast at this; linarith
  · have h4 : (4 : ℤ) < lucas P Q 4 := by
      rw [u4]; rcases hPQ with h | h <;> nlinarith
    have h5 : (5 : ℤ) < lucas P Q 5 := by
      rw [u5, u4]; rcases hPQ with h | h <;> nlinarith
    have := lucas_gt_of_two (m := 4) hP hQ (by simpa using h4) (by simpa using h5) (k - 4)
    rw [show 4 + (k - 4) = k by omega] at this
    have e : ((k : ℕ) : ℤ) = 4 + ((k - 4 : ℕ) : ℤ) := by omega
    push_cast at this; linarith

end Int

end SimonMarais
