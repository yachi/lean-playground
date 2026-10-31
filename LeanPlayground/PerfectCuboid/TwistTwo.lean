module

public import LeanPlayground.PerfectCuboid.TwistRigidity

/-!
# Three equal face twists force `k ∈ {1, 2}`

`TwistRigidity.twist_rigidity` shows that if three of the four sums
`S₁ = a² + b²`, `S₂ = a² + c²`, `S₃ = b² + c²`, `S₄ = a² + b² + c²` lie in one square class `k`
and the fourth lies in `1` or `k`, then `k = 1`. Without any condition on `S₄` this is false:
`(1, 1, 1)` has `S₁ = S₂ = S₃ = 2·1²`. The correct statement is:

**Theorem** (`three_twists`). If `s` is squarefree, `A, B, C` are not all zero and
`s D² = A² + B²`, `s E² = A² + C²`, `s F² = B² + C²`, then `s = 1` or `s = 2`.
Rational version `three_twists_rat`: three face sums of a positive rational box in one square
class `k` force `k ∈ ℚ*² ∪ 2·ℚ*²`.

*Proof.* Let `p` be an odd prime dividing `s`. Then `p` divides `S₁ + S₂ − S₃ = 2A²`,
`S₁ + S₃ − S₂ = 2B²` and `S₂ + S₃ − S₁ = 2C²`, hence `A, B, C`; then `p² ∣ s D²` with `s`
squarefree gives `p ∣ D` (`TwistRigidity.dvd_of_sq_dvd_mul`), likewise `p ∣ E, F`
(`descent_three`), and dividing by `p` gives a smaller solution. By infinite descent no odd
prime divides `s`, so the squarefree `s` is `1` or `2`. No congruence modulo `8` is used, and
the prime `2` is never descended on.

Both values occur: `s = 1` for every Euler brick, e.g. `(44, 117, 240)`, and `s = 2` for
`(1, 1, 1)` (`two_twist_example`) and the primitive box `(23, 289, 527)` with
`23² + 289² = 2·205²`, `23² + 527² = 2·373²`, `289² + 527² = 2·425²` (`two_twist_example'`).
(The primitive examples with `A < B < C ≤ 3000` are `(17, 697, 1127)`, `(23, 289, 527)`,
`(89, 191, 329)`, `(97, 553, 833)`, `(119, 833, 1081)`.)

**`n`-dimensional rigidity** (`rigidity_fin`). For `a : Fin n → ℕ`, `n ≥ 3`, not identically
zero, if every sum `∑_{i ∈ S} aᵢ²` with `|S| ≥ 2` is `s` times a square (`s` squarefree), then
`s = 1`: a prime `p ∣ s` divides every `aᵢ` by `TwistRigidity.local_three_faces` applied to three
coordinates (for `p = 2` the triple sum, odd if all three are odd, is what excludes `s = 2`),
and one descends on `∑ aᵢ`.
-/

@[expose] public section

namespace PerfectCuboid.TwistTwo

open TwistRigidity

/-- **Local step at an odd prime.** If an odd prime `p` divides the squarefree `s`, every
solution of the three twisted face equations is divisible by `p`. -/
theorem descent_three {p s A B C D E F : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hs : Squarefree s)
    (hps : p ∣ s) (hD : s * D ^ 2 = A ^ 2 + B ^ 2) (hE : s * E ^ 2 = A ^ 2 + C ^ 2)
    (hF : s * F ^ 2 = B ^ 2 + C ^ 2) :
    p ∣ A ∧ p ∣ B ∧ p ∣ C ∧ p ∣ D ∧ p ∣ E ∧ p ∣ F := by
  have hodd : ¬ p ∣ 2 := by
    intro h
    have := Nat.le_of_dvd two_pos h
    have := hp.two_le
    omega
  have pd {X S : ℕ} (h : s * X ^ 2 = S) : p ∣ S := by
    rw [← h]; exact dvd_mul_of_dvd_left hps _
  have h₁ := pd hD; have h₂ := pd hE; have h₃ := pd hF
  have h2A : p ∣ 2 * A ^ 2 := by
    have : p ∣ 2 * A ^ 2 + (B ^ 2 + C ^ 2) := by
      have := dvd_add h₁ h₂
      convert this using 1; ring
    exact (Nat.dvd_add_left h₃).mp this
  have hA : p ∣ A := hp.dvd_of_dvd_pow ((hp.dvd_mul.mp h2A).resolve_left hodd)
  have hB : p ∣ B := hp.dvd_of_dvd_pow ((Nat.dvd_add_right (dvd_pow hA two_ne_zero)).mp h₁)
  have hC : p ∣ C := hp.dvd_of_dvd_pow ((Nat.dvd_add_right (dvd_pow hA two_ne_zero)).mp h₂)
  have sq2 {X Y Z : ℕ} (hX : p ∣ X) (hY : p ∣ Y) (h : s * Z ^ 2 = X ^ 2 + Y ^ 2) : p ∣ Z := by
    obtain ⟨X', rfl⟩ := hX
    obtain ⟨Y', rfl⟩ := hY
    exact dvd_of_sq_dvd_mul hp hs ⟨X' ^ 2 + Y' ^ 2, by rw [h]; ring⟩
  exact ⟨hA, hB, hC, sq2 hA hB hD, sq2 hA hC hE, sq2 hB hC hF⟩

/-- **Descent.** If an odd prime divides the squarefree `s`, the three twisted face equations
have only the solution `A = B = C = 0`. -/
theorem eq_zero_of_odd_prime_dvd {p s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hs : Squarefree s)
    (hps : p ∣ s) {A B C D E F : ℕ} (hD : s * D ^ 2 = A ^ 2 + B ^ 2)
    (hE : s * E ^ 2 = A ^ 2 + C ^ 2) (hF : s * F ^ 2 = B ^ 2 + C ^ 2) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  suffices key : ∀ n, ∀ A B C D E F : ℕ, A + B + C = n → s * D ^ 2 = A ^ 2 + B ^ 2 →
      s * E ^ 2 = A ^ 2 + C ^ 2 → s * F ^ 2 = B ^ 2 + C ^ 2 → A = 0 ∧ B = 0 ∧ C = 0 from
    key _ A B C D E F rfl hD hE hF
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A B C D E F hn hD hE hF
  obtain ⟨⟨A', rfl⟩, ⟨B', rfl⟩, ⟨C', rfl⟩, ⟨D', rfl⟩, ⟨E', rfl⟩, ⟨F', rfl⟩⟩ :=
    descent_three hp hp2 hs hps hD hE hF
  have hp0 : 0 < p ^ 2 := by have := hp.pos; positivity
  have cancel {X Y Z : ℕ} (h : s * (p * Z) ^ 2 = (p * X) ^ 2 + (p * Y) ^ 2) :
      s * Z ^ 2 = X ^ 2 + Y ^ 2 :=
    Nat.eq_of_mul_eq_mul_left hp0 (by linear_combination h)
  rcases Nat.eq_zero_or_pos (A' + B' + C') with h0 | h0
  · have : A' = 0 ∧ B' = 0 ∧ C' = 0 := by omega
    obtain ⟨rfl, rfl, rfl⟩ := this
    simp
  · have hlt : A' + B' + C' < n := by
      have : p * A' + p * B' + p * C' = p * (A' + B' + C') := by ring
      rw [← hn, this]
      have := hp.two_le
      nlinarith
    obtain ⟨rfl, rfl, rfl⟩ := ih _ hlt A' B' C' D' E' F' rfl (cancel hD) (cancel hE) (cancel hF)
    simp

/-- A squarefree natural number without odd prime factors is `1` or `2`. -/
theorem eq_one_or_two_of_squarefree {s : ℕ} (hs : Squarefree s)
    (h : ∀ p : ℕ, p.Prime → p ∣ s → p = 2) : s = 1 ∨ s = 2 := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hs.ne_zero
  have hm1 : m = 1 := by
    by_contra hm1
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    have := h q hq (dvd_mul_of_dvd_right hqm _)
    subst this
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hqm)
  subst hm1
  have hk : k < 2 := by
    by_contra hk
    have : 2 * 2 ∣ 2 ^ k * 1 := by
      rw [mul_one, ← pow_two]; exact Nat.pow_dvd_pow 2 (by omega)
    exact Nat.prime_two.not_isUnit (hs 2 this)
  interval_cases k <;> simp

/-- **Three equal face twists force `s ∈ {1, 2}`.** If `s` is squarefree, `A, B, C` are not all
zero and `A² + B²`, `A² + C²`, `B² + C²` are all `s` times a square, then `s = 1` or `s = 2`. -/
theorem three_twists {s A B C D E F : ℕ} (hs : Squarefree s) (h0 : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0)
    (hD : s * D ^ 2 = A ^ 2 + B ^ 2) (hE : s * E ^ 2 = A ^ 2 + C ^ 2)
    (hF : s * F ^ 2 = B ^ 2 + C ^ 2) : s = 1 ∨ s = 2 := by
  refine eq_one_or_two_of_squarefree hs fun p hp hps ↦ ?_
  by_contra hp2
  obtain ⟨rfl, rfl, rfl⟩ := eq_zero_of_odd_prime_dvd hp hp2 hs hps hD hE hF
  simp at h0

/-- **Rational version.** For positive rationals `a, b, c` with `a² + b² = k x²`,
`a² + c² = k y²`, `b² + c² = k z²` (`k > 0`), `k` is a square or twice a square. -/
theorem three_twists_rat {k a b c x y z : ℚ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : a ^ 2 + b ^ 2 = k * x ^ 2) (hy : a ^ 2 + c ^ 2 = k * y ^ 2)
    (hz : b ^ 2 + c ^ 2 = k * z ^ 2) : IsSquare k ∨ IsSquare (k / 2) := by
  obtain ⟨s, q, hs, hq, rfl⟩ := exists_squarefree_mul_sq hk
  obtain ⟨s₄, q₄, -, -, h₄⟩ := exists_squarefree_mul_sq (k := a ^ 2 + b ^ 2 + c ^ 2)
    (by positivity)
  obtain ⟨A, B, C, D, E, F, G, h0, hD, hE, hF, -⟩ :=
    exists_nat_of_rat (u₁ := s) (u₂ := s) (u₃ := s) (u₄ := s₄) (d := q * x) (e := q * y)
      (f := q * z) (g := q₄) (Or.inl ha.ne') (by rw [hx]; ring) (by rw [hy]; ring)
      (by rw [hz]; ring) h₄.symm
  rcases three_twists hs h0 hD hE hF with rfl | rfl
  · exact Or.inl ⟨q, by push_cast; ring⟩
  · exact Or.inr ⟨q, by push_cast; ring⟩

/-- Sharpness: `(1, 1, 1)` has all three face sums equal to `2·1²`. -/
theorem two_twist_example :
    2 * 1 ^ 2 = 1 ^ 2 + 1 ^ 2 ∧ 2 * 1 ^ 2 = 1 ^ 2 + 1 ^ 2 ∧ 2 * 1 ^ 2 = 1 ^ 2 + 1 ^ 2 := by
  norm_num

/-- Sharpness with distinct edges: the primitive box `(23, 289, 527)` has
`23² + 289² = 2·205²`, `23² + 527² = 2·373²`, `289² + 527² = 2·425²`. -/
theorem two_twist_example' :
    2 * 205 ^ 2 = 23 ^ 2 + 289 ^ 2 ∧ 2 * 373 ^ 2 = 23 ^ 2 + 527 ^ 2 ∧
      2 * 425 ^ 2 = 289 ^ 2 + 527 ^ 2 ∧ Nat.gcd (Nat.gcd 23 289) 527 = 1 := by
  norm_num

/-! ### `n`-dimensional rigidity -/

/-- Local step for three distinct coordinates of an `n`-dimensional box all of whose sub-sums
of at least two squares are `s` times a square: a prime `p ∣ s` divides `a i`. -/
theorem dvd_of_three {n p s : ℕ} (hp : p.Prime) (hps : p ∣ s) (a : Fin n → ℕ)
    (h : ∀ S : Finset (Fin n), 2 ≤ S.card → ∃ D, s * D ^ 2 = ∑ i ∈ S, a i ^ 2)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : p ∣ a i := by
  have pd {S : Finset (Fin n)} (hS : 2 ≤ S.card) : p ∣ ∑ i ∈ S, a i ^ 2 := by
    obtain ⟨D, hD⟩ := h S hS
    rw [← hD]; exact dvd_mul_of_dvd_left hps _
  have c2 {x y : Fin n} (hxy : x ≠ y) : 2 ≤ ({x, y} : Finset (Fin n)).card :=
    (Finset.card_pair hxy).ge
  have h₁ := pd (c2 hij); have h₂ := pd (c2 hik); have h₃ := pd (c2 hjk)
  rw [Finset.sum_pair hij] at h₁
  rw [Finset.sum_pair hik] at h₂
  rw [Finset.sum_pair hjk] at h₃
  have hmem : i ∉ ({j, k} : Finset (Fin n)) := by simp [hij, hik]
  have c3 : 2 ≤ (insert i {j, k} : Finset (Fin n)).card := by
    rw [Finset.card_insert_of_notMem hmem, Finset.card_pair hjk]; omega
  obtain ⟨G, hG⟩ := h _ c3
  rw [Finset.sum_insert hmem, Finset.sum_pair hjk, ← add_assoc] at hG
  exact (local_three_faces hp h₁ h₂ h₃ (Or.inr hps) hG).1

/-- **`n`-dimensional twist rigidity** (`n ≥ 3`). If `a : Fin n → ℕ` is not identically zero,
`s` is squarefree, and every sum `∑_{i ∈ S} aᵢ²` over a set `S` of at least two indices is `s`
times a square, then `s = 1`. (For `n = 3` this is `twist_rigidity` with all four sums twisted;
the triple sum is what excludes `s = 2`.) -/
theorem rigidity_fin {n s : ℕ} (hn : 3 ≤ n) (hs : Squarefree s) (a : Fin n → ℕ)
    (h0 : ∃ i, a i ≠ 0)
    (h : ∀ S : Finset (Fin n), 2 ≤ S.card → ∃ D, s * D ^ 2 = ∑ i ∈ S, a i ^ 2) : s = 1 := by
  by_contra hs1
  obtain ⟨p, hp, hps⟩ := Nat.exists_prime_and_dvd hs1
  have i0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  have i1 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp
  have i2 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp
  have loc : ∀ a : Fin n → ℕ,
      (∀ S : Finset (Fin n), 2 ≤ S.card → ∃ D, s * D ^ 2 = ∑ i ∈ S, a i ^ 2) →
      ∀ i, p ∣ a i := by
    intro a h i
    by_cases e0 : i = ⟨0, by omega⟩
    · subst e0; exact dvd_of_three hp hps a h i0 i1 i2
    by_cases e1 : i = ⟨1, by omega⟩
    · subst e1; exact dvd_of_three hp hps a h i0.symm i2 i1
    · exact dvd_of_three hp hps a h e0 e1 i0
  suffices key : ∀ m, ∀ a : Fin n → ℕ, ∑ i, a i = m → (∃ i, a i ≠ 0) →
      (∀ S : Finset (Fin n), 2 ≤ S.card → ∃ D, s * D ^ 2 = ∑ i ∈ S, a i ^ 2) → False from
    key _ a rfl h0 h
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a hm h0 h
  have hdv := loc a h
  set b : Fin n → ℕ := fun i ↦ a i / p with hb
  have hab : ∀ i, a i = p * b i := fun i ↦ (Nat.mul_div_cancel' (hdv i)).symm
  have hp0 : 0 < p ^ 2 := by have := hp.pos; positivity
  have hsum : ∀ S : Finset (Fin n), ∑ i ∈ S, a i ^ 2 = p ^ 2 * ∑ i ∈ S, b i ^ 2 := by
    intro S
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hab i]; ring
  have hb' : ∀ S : Finset (Fin n), 2 ≤ S.card → ∃ D, s * D ^ 2 = ∑ i ∈ S, b i ^ 2 := by
    intro S hS
    obtain ⟨D, hD⟩ := h S hS
    rw [hsum] at hD
    obtain ⟨D', rfl⟩ := dvd_of_sq_dvd_mul hp hs ⟨_, hD⟩
    exact ⟨D', Nat.eq_of_mul_eq_mul_left hp0 (by rw [← hD]; ring)⟩
  obtain ⟨i, hi⟩ := h0
  have hbi : b i ≠ 0 := by intro h'; apply hi; rw [hab i, h', mul_zero]
  have hlt : ∑ i, b i < m := by
    rw [← hm]
    have : ∑ i, a i = p * ∑ i, b i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ hab i
    rw [this]
    have hpos : 0 < ∑ i, b i :=
      lt_of_lt_of_le (Nat.pos_of_ne_zero hbi) (Finset.single_le_sum (by simp) (Finset.mem_univ i))
    have := hp.two_le
    nlinarith
  exact ih _ hlt b rfl ⟨i, hbi⟩ hb'

end PerfectCuboid.TwistTwo
