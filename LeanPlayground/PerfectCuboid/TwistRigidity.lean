module

public import LeanPlayground.PerfectCuboid.TwistClass

/-!
# Twist rigidity: every twisted perfect cuboid is a perfect cuboid

For a box with edges `a, b, c` consider the four sums
`S₁ = a² + b²`, `S₂ = a² + c²`, `S₃ = b² + c²`, `S₄ = a² + b² + c²`
and their *twists*, the classes of the `Sᵢ` in `ℚ*/ℚ*²`.

**Theorem (twist rigidity).** If at least three of the four sums lie in one square class `k`, and
the fourth lies in the class `1` or `k`, then `k = 1`. (`twist_rigidity`, `twist_rigidity_rat`;
the two shapes `{S₁, S₂, S₃}` and `{S₁, S₂, S₄}` are `squarefree_eq_one_of_three_faces`,
`squarefree_eq_one_of_two_faces_space`, `isSquare_of_three_faces`,
`isSquare_of_two_faces_space`.) For the shapes containing `S₄` the fourth sum plays no role at all
in the argument; for `{S₁, S₂, S₃}` some condition on `S₄` is needed, since `(1, 1, 1)` has
`S₁ = S₂ = S₃ = 2`, `S₄ = 3`.

*Proof idea.* Scale to natural numbers and take `k = s` squarefree. If a prime `p ∣ s` then
`p ∣ A, B, C`: for odd `p` because `S₁ + S₂ − S₃ = 2A²` (resp. `S₄ − S₁ = C²`); for `p = 2`
because otherwise `A, B, C` are all odd and `S₄ ≡ 3 (mod 8)` is neither a square nor even.
Then `p²` divides each `uᵢ·Xᵢ²`, so `p ∣ Xᵢ` (as `uᵢ` is squarefree), and dividing everything by
`p` gives a smaller solution (`descent`). Infinite descent forces `A = B = C = 0`.

**Consequences** (namespace `PerfectCuboid.CongruentRank`).
* `IsTwistedCuboid.isSquare_twist`, `IsTwistedCuboid.exists_isRatCuboid`,
  `not_exists_isTwistedCuboid_of_not_isSquare`: a `k`-twisted perfect cuboid has `k ∈ ℚ²` and is
  a rational perfect cuboid. This answers the question left open in `TwistedCuboid.lean`.
* `IsConfigPts.isSquare_twist`, `IsConfigPts.isSquare_neg_prod`, `IsConfigPts.exists_isRatCuboid`:
  for every positive cuboid configuration on `E_N`, `U₁² + U₂²` and `−X₁X₂X₃` are rational squares,
  and the box `|U₁|, |U₂|, |U₃|` is a rational perfect cuboid. So the square condition in
  `exists_isPerfectCuboid_iff` (and in `exists_isPerfectCuboid_iff'`) is automatic.
* `exists_isPerfectCuboid_iff_exists_isConfigPts`: **a perfect cuboid exists if and only if some
  `E_N` has a positive cuboid configuration**, with no extra hypothesis;
  `exists_isPerfectCuboid_iff_exists_isTwistedCuboid`: iff some twisted perfect cuboid exists.
* `fiber_twist`: on a Pythagorean fiber `U² + V² = W²`, if `t² + U²`, `t² + V²`, `t² + W²` all lie
  in the class `k` (with `t ≠ 0`) then `k ∈ ℚ²` (the second shape).
* `two_equal_twists_example`: `(4, 7, 32; 33)` has `S₁ = 65`, `S₂ = 65·4²`, so two equal twists
  `≠ 1` do occur: the bound "three" is sharp.

Literature. Asiryan (arXiv:2610.10643, Definition 1) imposes no square condition on a
configuration, and attributes the converse correspondence (configuration to cuboid) to
Paulsen–West (Houston J. Math. 48 (2022), Proposition 3.1). The theorem here shows by an
elementary descent that this converse needs no extra hypothesis. The notion of a twisted cuboid
is this repository's; we found no statement of the rigidity theorem in print.

Near-miss remark. Positivity is never used in the integer core; only "not all of `A, B, C` are
zero". Degenerate boxes `(a, b, 0)` and `(0, 0, c)` satisfy the conclusion (their twists are `1`),
so the theorem is consistent with them.
-/

@[expose] public section

namespace PerfectCuboid.TwistRigidity

/-- If `u` is squarefree and `p² ∣ u·D²` for a prime `p`, then `p ∣ D`. -/
theorem dvd_of_sq_dvd_mul {p u D : ℕ} (hp : p.Prime) (hu : Squarefree u) (h : p ^ 2 ∣ u * D ^ 2) :
    p ∣ D := by
  apply hp.dvd_of_dvd_pow (n := 2)
  by_cases hpu : p ∣ u
  · obtain ⟨u', rfl⟩ := hpu
    have hu' : ¬ p ∣ u' := by
      rintro ⟨v, rfl⟩
      have := hu p ⟨v, by ring⟩
      exact hp.not_isUnit this
    have h' : p * p ∣ p * (u' * D ^ 2) := by
      rw [← sq, ← mul_assoc]; exact h
    have := (mul_dvd_mul_iff_left hp.ne_zero).mp h'
    exact (hp.dvd_mul.mp this).resolve_left hu'
  · have : p ∣ u * D ^ 2 := (dvd_pow_self p two_ne_zero).trans h
    exact (hp.dvd_mul.mp this).resolve_left hpu

/-- `x² ≡ x (mod 2)`. -/
theorem sq_mod_two (x : ℕ) : x ^ 2 % 2 = x % 2 := by
  rw [Nat.pow_mod]
  have := Nat.mod_lt x (show 0 < 2 by norm_num)
  interval_cases h : x % 2 <;> simp

/-- An odd square is `1 (mod 8)`. -/
theorem sq_mod_eight_of_odd {x : ℕ} (hx : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  rw [Nat.pow_mod]
  have := Nat.mod_lt x (show 0 < 8 by norm_num)
  have h2 : x % 8 % 2 = 1 := by omega
  interval_cases h : x % 8 <;> simp_all

/-- A square is `0, 1` or `4 (mod 8)`. -/
theorem sq_mod_eight (x : ℕ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  rw [Nat.pow_mod]
  have := Nat.mod_lt x (show 0 < 8 by norm_num)
  interval_cases h : x % 8 <;> simp

/-- **The descent step.** Let `u₁, …, u₄` be squarefree and `p` a prime such that every solution
of `u₁D² = A² + B²`, `u₂E² = A² + C²`, `u₃F² = B² + C²`, `u₄G² = A² + B² + C²` has
`p ∣ A, B, C`. Then every solution has `A = B = C = 0`. -/
theorem descent {p u₁ u₂ u₃ u₄ : ℕ} (hp : p.Prime) (h₁ : Squarefree u₁) (h₂ : Squarefree u₂)
    (h₃ : Squarefree u₃) (h₄ : Squarefree u₄)
    (hloc : ∀ A B C D E F G : ℕ, u₁ * D ^ 2 = A ^ 2 + B ^ 2 → u₂ * E ^ 2 = A ^ 2 + C ^ 2 →
      u₃ * F ^ 2 = B ^ 2 + C ^ 2 → u₄ * G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2 → p ∣ A ∧ p ∣ B ∧ p ∣ C)
    {A B C D E F G : ℕ} (hD : u₁ * D ^ 2 = A ^ 2 + B ^ 2) (hE : u₂ * E ^ 2 = A ^ 2 + C ^ 2)
    (hF : u₃ * F ^ 2 = B ^ 2 + C ^ 2) (hG : u₄ * G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  suffices key : ∀ n, ∀ A B C D E F G : ℕ, A + B + C = n → u₁ * D ^ 2 = A ^ 2 + B ^ 2 →
      u₂ * E ^ 2 = A ^ 2 + C ^ 2 → u₃ * F ^ 2 = B ^ 2 + C ^ 2 →
      u₄ * G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2 → A = 0 ∧ B = 0 ∧ C = 0 from
    key _ A B C D E F G rfl hD hE hF hG
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A B C D E F G hn hD hE hF hG
  obtain ⟨⟨A', rfl⟩, ⟨B', rfl⟩, ⟨C', rfl⟩⟩ := hloc A B C D E F G hD hE hF hG
  have hp2 : 0 < p ^ 2 := by have := hp.pos; positivity
  have dv {u X S : ℕ} (hu : Squarefree u) (hX : u * X ^ 2 = p ^ 2 * S) :
      ∃ X', X = p * X' ∧ u * X' ^ 2 = S := by
    obtain ⟨X', rfl⟩ := dvd_of_sq_dvd_mul hp hu ⟨S, hX⟩
    refine ⟨X', rfl, Nat.eq_of_mul_eq_mul_left hp2 ?_⟩
    calc p ^ 2 * (u * X' ^ 2) = u * (p * X') ^ 2 := by ring
      _ = p ^ 2 * S := hX
  obtain ⟨D', rfl, hD'⟩ := dv h₁ (S := A' ^ 2 + B' ^ 2) (by rw [hD]; ring)
  obtain ⟨E', rfl, hE'⟩ := dv h₂ (S := A' ^ 2 + C' ^ 2) (by rw [hE]; ring)
  obtain ⟨F', rfl, hF'⟩ := dv h₃ (S := B' ^ 2 + C' ^ 2) (by rw [hF]; ring)
  obtain ⟨G', rfl, hG'⟩ := dv h₄ (S := A' ^ 2 + B' ^ 2 + C' ^ 2) (by rw [hG]; ring)
  have hsum : p * A' + p * B' + p * C' = p * (A' + B' + C') := by ring
  rcases Nat.eq_zero_or_pos (A' + B' + C') with h0 | h0
  · have : A' = 0 ∧ B' = 0 ∧ C' = 0 := by omega
    obtain ⟨rfl, rfl, rfl⟩ := this
    simp
  · have hlt : A' + B' + C' < n := by
      rw [← hn, hsum]
      have := hp.two_le
      nlinarith
    obtain ⟨rfl, rfl, rfl⟩ := ih _ hlt A' B' C' D' E' F' G' rfl hD' hE' hF' hG'
    simp

/-- The `2`-adic local step: if `A² + B²`, `A² + C²`, `B² + C²` are even and `A² + B² + C²` is
`uG²` with `u = 1` or `u` even, then `A, B, C` are even. -/
theorem local_three_faces_two {u A B C G : ℕ} (h₁ : 2 ∣ A ^ 2 + B ^ 2)
    (h₂ : 2 ∣ A ^ 2 + C ^ 2) (hu : u = 1 ∨ 2 ∣ u)
    (hG : u * G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2) : 2 ∣ A ∧ 2 ∣ B ∧ 2 ∣ C := by
  have a2 := sq_mod_two A; have b2 := sq_mod_two B; have c2 := sq_mod_two C
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod] at h₁ h₂
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  have hB : B % 2 = A % 2 := by omega
  have hC : C % 2 = A % 2 := by omega
  clear h₁ h₂ a2 b2 c2
  by_cases hA : A % 2 = 0
  · exact ⟨hA, hB ▸ hA, hC ▸ hA⟩
  · exfalso
    have a8 := sq_mod_eight_of_odd (x := A) (by omega)
    have b8 := sq_mod_eight_of_odd (x := B) (by omega)
    have c8 := sq_mod_eight_of_odd (x := C) (by omega)
    have hS : (A ^ 2 + B ^ 2 + C ^ 2) % 8 = 3 := by
      rw [Nat.add_mod, Nat.add_mod (A ^ 2), a8, b8, c8]
    rw [← hG] at hS
    clear a8 b8 c8 hG hA hB hC
    rcases hu with rfl | ⟨v, rfl⟩
    · rw [one_mul] at hS
      rcases sq_mod_eight G with h | h | h <;> rw [h] at hS <;> exact absurd hS (by decide)
    · have h8 : (2 * v * G ^ 2) % 2 = 0 := by
        rw [mul_assoc]; exact Nat.mul_mod_right _ _
      have := Nat.mod_mod_of_dvd (2 * v * G ^ 2) (show 2 ∣ 8 by norm_num)
      rw [hS, h8] at this
      exact absurd this (by decide)

/-- **Local step, first shape.** If a prime `p` divides `A² + B²`, `A² + C²`, `B² + C²`, and
`A² + B² + C² = uG²` with `u = 1` or `p ∣ u`, then `p ∣ A, B, C`. -/
theorem local_three_faces {p u A B C G : ℕ} (hp : p.Prime) (h₁ : p ∣ A ^ 2 + B ^ 2)
    (h₂ : p ∣ A ^ 2 + C ^ 2) (h₃ : p ∣ B ^ 2 + C ^ 2) (hu : u = 1 ∨ p ∣ u)
    (hG : u * G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2) : p ∣ A ∧ p ∣ B ∧ p ∣ C := by
  by_cases hp2 : p = 2
  · subst hp2
    exact local_three_faces_two h₁ h₂ hu hG
  · have hodd : ¬ p ∣ 2 := by
      intro h
      have := Nat.le_of_dvd two_pos h
      have := hp.two_le
      omega
    have h2A : p ∣ 2 * A ^ 2 := by
      have : p ∣ 2 * A ^ 2 + (B ^ 2 + C ^ 2) := by
        have := dvd_add h₁ h₂
        convert this using 1; ring
      exact (Nat.dvd_add_left h₃).mp this
    have hA2 : p ∣ A ^ 2 := (hp.dvd_mul.mp h2A).resolve_left hodd
    have hA : p ∣ A := hp.dvd_of_dvd_pow hA2
    have hB : p ∣ B := hp.dvd_of_dvd_pow ((Nat.dvd_add_right (dvd_pow hA two_ne_zero)).mp h₁)
    have hC : p ∣ C := hp.dvd_of_dvd_pow ((Nat.dvd_add_right (dvd_pow hA two_ne_zero)).mp h₂)
    exact ⟨hA, hB, hC⟩

/-- **Local step, second shape.** If a prime `p` divides `A² + B²`, `A² + C²` and
`A² + B² + C²`, then `p ∣ A, B, C`. -/
theorem local_two_faces_space {p A B C : ℕ} (hp : p.Prime) (h₁ : p ∣ A ^ 2 + B ^ 2)
    (h₂ : p ∣ A ^ 2 + C ^ 2) (h₄ : p ∣ A ^ 2 + B ^ 2 + C ^ 2) : p ∣ A ∧ p ∣ B ∧ p ∣ C := by
  have hC : p ∣ C := hp.dvd_of_dvd_pow ((Nat.dvd_add_right h₁).mp h₄)
  have hA : p ∣ A := hp.dvd_of_dvd_pow ((Nat.dvd_add_left (dvd_pow hC two_ne_zero)).mp h₂)
  have hB : p ∣ B := hp.dvd_of_dvd_pow ((Nat.dvd_add_right (dvd_pow hA two_ne_zero)).mp h₁)
  exact ⟨hA, hB, hC⟩

/-- **Twist rigidity over `ℕ`.** Let `s` be squarefree and let each of the four sums
`A² + B²`, `A² + C²`, `B² + C²`, `A² + B² + C²` be `uᵢ·(square)` with `uᵢ ∈ {1, s}`, where at least
three of the `uᵢ` equal `s`. If `A, B, C` are not all zero, then `s = 1`. -/
theorem twist_rigidity {s u₁ u₂ u₃ u₄ A B C D E F G : ℕ} (hs : Squarefree s)
    (hu₁ : u₁ = 1 ∨ u₁ = s) (hu₂ : u₂ = 1 ∨ u₂ = s) (hu₃ : u₃ = 1 ∨ u₃ = s)
    (hu₄ : u₄ = 1 ∨ u₄ = s)
    (h3 : (u₁ = s ∧ u₂ = s ∧ u₃ = s) ∨ (u₁ = s ∧ u₂ = s ∧ u₄ = s) ∨
      (u₁ = s ∧ u₃ = s ∧ u₄ = s) ∨ (u₂ = s ∧ u₃ = s ∧ u₄ = s))
    (h0 : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) (hD : u₁ * D ^ 2 = A ^ 2 + B ^ 2)
    (hE : u₂ * E ^ 2 = A ^ 2 + C ^ 2) (hF : u₃ * F ^ 2 = B ^ 2 + C ^ 2)
    (hG : u₄ * G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2) : s = 1 := by
  by_contra hs1
  obtain ⟨p, hp, hps⟩ := Nat.exists_prime_and_dvd hs1
  have sqf {u : ℕ} (hu : u = 1 ∨ u = s) : Squarefree u := by
    rcases hu with rfl | rfl
    · exact squarefree_one
    · exact hs
  have pd {u X S : ℕ} (hu : u = s) (h : u * X ^ 2 = S) : p ∣ S := by
    rw [← h, hu]; exact dvd_mul_of_dvd_left hps _
  have hloc : ∀ A B C D E F G : ℕ, u₁ * D ^ 2 = A ^ 2 + B ^ 2 → u₂ * E ^ 2 = A ^ 2 + C ^ 2 →
      u₃ * F ^ 2 = B ^ 2 + C ^ 2 → u₄ * G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2 →
      p ∣ A ∧ p ∣ B ∧ p ∣ C := by
    intro A B C D E F G hD hE hF hG
    rcases h3 with ⟨e₁, e₂, e₃⟩ | ⟨e₁, e₂, e₄⟩ | ⟨e₁, e₃, e₄⟩ | ⟨e₂, e₃, e₄⟩
    · refine local_three_faces hp (pd e₁ hD) (pd e₂ hE) (pd e₃ hF) ?_ hG
      rcases hu₄ with h | h
      · exact Or.inl h
      · exact Or.inr (h ▸ hps)
    · exact local_two_faces_space hp (pd e₁ hD) (pd e₂ hE) (pd e₄ hG)
    · obtain ⟨hB, hA, hC⟩ := local_two_faces_space (A := B) (B := A) (C := C) hp
        (pd e₁ (hD.trans (add_comm _ _))) (pd e₃ hF) (pd e₄ (by rw [hG]; ring))
      exact ⟨hA, hB, hC⟩
    · obtain ⟨hC, hA, hB⟩ := local_two_faces_space (A := C) (B := A) (C := B) hp
        (pd e₂ (hE.trans (add_comm _ _))) (pd e₃ (hF.trans (add_comm _ _)))
        (pd e₄ (by rw [hG]; ring))
      exact ⟨hA, hB, hC⟩
  obtain ⟨rfl, rfl, rfl⟩ :=
    descent hp (sqf hu₁) (sqf hu₂) (sqf hu₃) (sqf hu₄) hloc hD hE hF hG
  simp at h0

/-- **Integer core, first shape:** three twisted faces and a square space diagonal force a
trivial twist. -/
theorem squarefree_eq_one_of_three_faces {s A B C D E F G : ℕ} (hs : Squarefree s)
    (h0 : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) (hD : s * D ^ 2 = A ^ 2 + B ^ 2) (hE : s * E ^ 2 = A ^ 2 + C ^ 2)
    (hF : s * F ^ 2 = B ^ 2 + C ^ 2) (hG : G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2) : s = 1 :=
  twist_rigidity hs (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl ⟨rfl, rfl, rfl⟩)
    h0 hD hE hF (by rw [one_mul]; exact hG)

/-- **Integer core, second shape:** two twisted faces and a twisted space diagonal force a
trivial twist (the third face plays no role). -/
theorem squarefree_eq_one_of_two_faces_space {s A B C D E F G : ℕ} (hs : Squarefree s)
    (h0 : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) (hD : s * D ^ 2 = A ^ 2 + B ^ 2) (hE : s * E ^ 2 = A ^ 2 + C ^ 2)
    (hF : F ^ 2 = B ^ 2 + C ^ 2) (hG : s * G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2) : s = 1 :=
  twist_rigidity hs (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) h0 hD hE (by rw [one_mul]; exact hF) hG

/-! ### From rationals to integers -/

/-- A positive rational is a squarefree natural number times a nonzero rational square. -/
theorem exists_squarefree_mul_sq {k : ℚ} (hk : 0 < k) :
    ∃ (s : ℕ) (q : ℚ), Squarefree s ∧ q ≠ 0 ∧ k = s * q ^ 2 := by
  have hn : 0 < k.num := Rat.num_pos.mpr hk
  have hnm : 0 < k.num.toNat * k.den := Nat.mul_pos (by omega) k.den_pos
  obtain ⟨s, r, -, hr, hrs, hsq⟩ := Nat.sq_mul_squarefree_of_pos hnm
  refine ⟨s, r / k.den, hsq, by positivity, ?_⟩
  have h1 : ((k.num.toNat : ℕ) : ℚ) = k.num := by exact_mod_cast Int.toNat_of_nonneg hn.le
  have h2 : (r : ℚ) ^ 2 * s = k.num * k.den := by rw [← h1]; exact_mod_cast hrs
  have hd : (k.den : ℚ) ≠ 0 := by positivity
  rw [div_pow, ← mul_div_assoc, mul_comm (s : ℚ), h2]
  field_simp
  rw [← Rat.mul_den_eq_num]

/-- A rational `q` times a multiple `M` of its denominator is, up to sign, a natural number. -/
theorem exists_nat_sq_eq {q : ℚ} {M : ℕ} (hM : q.den ∣ M) :
    ∃ n : ℕ, (n : ℚ) ^ 2 = (M * q) ^ 2 := by
  obtain ⟨t, rfl⟩ := hM
  refine ⟨(t * q.num).natAbs, ?_⟩
  simp only [Nat.cast_natAbs, Int.cast_abs, sq_abs, Int.cast_mul, Int.cast_natCast,
    Nat.cast_mul, ← Rat.mul_den_eq_num]
  ring

/-- **Clearing denominators.** A rational solution of the four twisted equations, with
coefficients `uᵢ ∈ ℕ`, gives a natural-number solution with the same coefficients. -/
theorem exists_nat_of_rat {u₁ u₂ u₃ u₄ : ℕ} {a b c d e f g : ℚ} (h0 : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (hD : (u₁ : ℚ) * d ^ 2 = a ^ 2 + b ^ 2) (hE : (u₂ : ℚ) * e ^ 2 = a ^ 2 + c ^ 2)
    (hF : (u₃ : ℚ) * f ^ 2 = b ^ 2 + c ^ 2) (hG : (u₄ : ℚ) * g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    ∃ A B C D E F G : ℕ, (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧ u₁ * D ^ 2 = A ^ 2 + B ^ 2 ∧
      u₂ * E ^ 2 = A ^ 2 + C ^ 2 ∧ u₃ * F ^ 2 = B ^ 2 + C ^ 2 ∧
      u₄ * G ^ 2 = A ^ 2 + B ^ 2 + C ^ 2 := by
  set M : ℕ := a.den * b.den * c.den * d.den * e.den * f.den * g.den with hMdef
  have hM : (M : ℚ) ≠ 0 := by positivity
  obtain ⟨A, hA⟩ := exists_nat_sq_eq (q := a) (M := M)
     ⟨b.den * c.den * d.den * e.den * f.den * g.den, by rw [hMdef]; ring⟩
  obtain ⟨B, hB⟩ := exists_nat_sq_eq (q := b) (M := M)
     ⟨a.den * c.den * d.den * e.den * f.den * g.den, by rw [hMdef]; ring⟩
  obtain ⟨C, hC⟩ := exists_nat_sq_eq (q := c) (M := M)
     ⟨a.den * b.den * d.den * e.den * f.den * g.den, by rw [hMdef]; ring⟩
  obtain ⟨D, hD'⟩ := exists_nat_sq_eq (q := d) (M := M)
     ⟨a.den * b.den * c.den * e.den * f.den * g.den, by rw [hMdef]; ring⟩
  obtain ⟨E, hE'⟩ := exists_nat_sq_eq (q := e) (M := M)
     ⟨a.den * b.den * c.den * d.den * f.den * g.den, by rw [hMdef]; ring⟩
  obtain ⟨F, hF'⟩ := exists_nat_sq_eq (q := f) (M := M)
     ⟨a.den * b.den * c.den * d.den * e.den * g.den, by rw [hMdef]; ring⟩
  obtain ⟨G, hG'⟩ := exists_nat_sq_eq (q := g) (M := M)
     ⟨a.den * b.den * c.den * d.den * e.den * f.den, by rw [hMdef]; ring⟩
  clear_value M
  have nz {n : ℕ} {q : ℚ} (h : (n : ℚ) ^ 2 = (M * q) ^ 2) (hq : q ≠ 0) : n ≠ 0 := by
    rintro rfl
    have : (M * q) ^ 2 ≠ 0 := by positivity
    simp [← h] at this
  refine ⟨A, B, C, D, E, F, G, ?_, ?_, ?_, ?_, ?_⟩
  · rcases h0 with h | h | h
    · exact Or.inl (nz hA h)
    · exact Or.inr (Or.inl (nz hB h))
    · exact Or.inr (Or.inr (nz hC h))
  · exact_mod_cast (show (u₁ : ℚ) * (D : ℚ) ^ 2 = (A : ℚ) ^ 2 + (B : ℚ) ^ 2 by
      rw [hA, hB, hD']; linear_combination (M : ℚ) ^ 2 * hD)
  · exact_mod_cast (show (u₂ : ℚ) * (E : ℚ) ^ 2 = (A : ℚ) ^ 2 + (C : ℚ) ^ 2 by
      rw [hA, hC, hE']; linear_combination (M : ℚ) ^ 2 * hE)
  · exact_mod_cast (show (u₃ : ℚ) * (F : ℚ) ^ 2 = (B : ℚ) ^ 2 + (C : ℚ) ^ 2 by
      rw [hB, hC, hF']; linear_combination (M : ℚ) ^ 2 * hF)
  · exact_mod_cast (show (u₄ : ℚ) * (G : ℚ) ^ 2 = (A : ℚ) ^ 2 + (B : ℚ) ^ 2 + (C : ℚ) ^ 2 by
      rw [hA, hB, hC, hG']; linear_combination (M : ℚ) ^ 2 * hG)

/-- **Twist rigidity over `ℚ`.** Let `k > 0` and let each of the four sums `a² + b²`, `a² + c²`,
`b² + c²`, `a² + b² + c²` be `κᵢ·(rational square)` with `κᵢ ∈ {1, k}`, where at least three of
the `κᵢ` equal `k`. If `a, b, c` are not all zero, then `k` is a square. -/
theorem twist_rigidity_rat {k κ₁ κ₂ κ₃ κ₄ a b c d e f g : ℚ} (hk : 0 < k)
    (hκ₁ : κ₁ = 1 ∨ κ₁ = k) (hκ₂ : κ₂ = 1 ∨ κ₂ = k) (hκ₃ : κ₃ = 1 ∨ κ₃ = k)
    (hκ₄ : κ₄ = 1 ∨ κ₄ = k)
    (h3 : (κ₁ = k ∧ κ₂ = k ∧ κ₃ = k) ∨ (κ₁ = k ∧ κ₂ = k ∧ κ₄ = k) ∨
      (κ₁ = k ∧ κ₃ = k ∧ κ₄ = k) ∨ (κ₂ = k ∧ κ₃ = k ∧ κ₄ = k))
    (h0 : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) (hD : κ₁ * d ^ 2 = a ^ 2 + b ^ 2)
    (hE : κ₂ * e ^ 2 = a ^ 2 + c ^ 2) (hF : κ₃ * f ^ 2 = b ^ 2 + c ^ 2)
    (hG : κ₄ * g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) : IsSquare k := by
  obtain ⟨s, q, hs, hq, rfl⟩ := exists_squarefree_mul_sq hk
  -- each `κᵢ x²` is `uᵢ x'²` with `uᵢ ∈ {1, s}`, and `uᵢ = s` when `κᵢ = k`
  have red {κ x S : ℚ} (hκ : κ = 1 ∨ κ = s * q ^ 2) (h : κ * x ^ 2 = S) :
      ∃ (u : ℕ) (x' : ℚ), (u = 1 ∨ u = s) ∧ (κ = s * q ^ 2 → u = s) ∧ (u : ℚ) * x' ^ 2 = S := by
    by_cases hκk : κ = s * q ^ 2
    · exact ⟨s, q * x, Or.inr rfl, fun _ => rfl, by rw [← h, hκk]; ring⟩
    · rcases hκ with rfl | h'
      · exact ⟨1, x, Or.inl rfl, fun h' => absurd h' hκk, by rw [← h]; push_cast; ring⟩
      · exact absurd h' hκk
  obtain ⟨u₁, d', hu₁, hk₁, hD'⟩ := red hκ₁ hD
  obtain ⟨u₂, e', hu₂, hk₂, hE'⟩ := red hκ₂ hE
  obtain ⟨u₃, f', hu₃, hk₃, hF'⟩ := red hκ₃ hF
  obtain ⟨u₄, g', hu₄, hk₄, hG'⟩ := red hκ₄ hG
  obtain ⟨A, B, C, D, E, F, G, h0', hD₀, hE₀, hF₀, hG₀⟩ := exists_nat_of_rat h0 hD' hE' hF' hG'
  have h3' : (u₁ = s ∧ u₂ = s ∧ u₃ = s) ∨ (u₁ = s ∧ u₂ = s ∧ u₄ = s) ∨
      (u₁ = s ∧ u₃ = s ∧ u₄ = s) ∨ (u₂ = s ∧ u₃ = s ∧ u₄ = s) := by
    rcases h3 with ⟨e₁, e₂, e₃⟩ | ⟨e₁, e₂, e₃⟩ | ⟨e₁, e₂, e₃⟩ | ⟨e₁, e₂, e₃⟩
    · exact Or.inl ⟨hk₁ e₁, hk₂ e₂, hk₃ e₃⟩
    · exact Or.inr (Or.inl ⟨hk₁ e₁, hk₂ e₂, hk₄ e₃⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hk₁ e₁, hk₃ e₂, hk₄ e₃⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hk₂ e₁, hk₃ e₂, hk₄ e₃⟩))
  have hs1 := twist_rigidity hs hu₁ hu₂ hu₃ hu₄ h3' h0' hD₀ hE₀ hF₀ hG₀
  exact ⟨q, by rw [hs1]; push_cast; ring⟩

/-- **Rational version, first shape** (`IsSquare k` in `ℚ`): three faces twisted by `k` and a
rational space diagonal force `k ∈ ℚ²`. -/
theorem isSquare_of_three_faces {k a b c d e f g : ℚ} (hk : 0 < k) (ha : 0 < a) (_hb : 0 < b)
    (_hc : 0 < c) (hD : k * d ^ 2 = a ^ 2 + b ^ 2) (hE : k * e ^ 2 = a ^ 2 + c ^ 2)
    (hF : k * f ^ 2 = b ^ 2 + c ^ 2) (hG : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) : IsSquare k :=
  twist_rigidity_rat hk (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
    (Or.inl ⟨rfl, rfl, rfl⟩) (Or.inl ha.ne') hD hE hF (by rw [one_mul]; exact hG)

/-- **Rational version, second shape:** two faces and the space diagonal twisted by `k`, and a
rational third face, force `k ∈ ℚ²`. -/
theorem isSquare_of_two_faces_space {k a b c d e f g : ℚ} (hk : 0 < k) (ha : 0 < a)
    (hD : k * d ^ 2 = a ^ 2 + b ^ 2) (hE : k * e ^ 2 = a ^ 2 + c ^ 2)
    (hF : f ^ 2 = b ^ 2 + c ^ 2) (hG : k * g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) : IsSquare k :=
  twist_rigidity_rat hk (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (Or.inl ha.ne') hD hE (by rw [one_mul]; exact hF) hG

/-- **Fiber formulation.** On a Pythagorean fiber `U² + V² = W²`, if `t² + U²`, `t² + V²` and
`t² + W²` all lie in the square class of `k > 0` and `t ≠ 0`, then `k` is a square. -/
theorem fiber_twist {k t U V W x y z : ℚ} (hk : 0 < k) (ht : t ≠ 0) (hW : U ^ 2 + V ^ 2 = W ^ 2)
    (hx : k * x ^ 2 = t ^ 2 + U ^ 2) (hy : k * y ^ 2 = t ^ 2 + V ^ 2)
    (hz : k * z ^ 2 = t ^ 2 + W ^ 2) : IsSquare k :=
  twist_rigidity_rat (f := W) hk (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (Or.inl ht) hx hy (by rw [hW]; ring)
    (by rw [hz, ← hW]; ring)

/-! ### Sharpness: two equal twists are not rigid -/

/-- `(4, 7, 32)` has square space diagonal `33` and `a² + b² = 65`, `a² + c² = 1040 = 65·4²`
lie in the same nontrivial square class (`(a² + b²)(a² + c²) = 260²`), while `b² + c² = 1073` is
not a square: two equal twists `≠ 1` do occur. -/
theorem two_equal_twists_example :
    (4 : ℕ) ^ 2 + 7 ^ 2 + 32 ^ 2 = 33 ^ 2 ∧ (4 ^ 2 + 7 ^ 2) * (4 ^ 2 + 32 ^ 2) = (260 : ℕ) ^ 2 ∧
      65 * 1 ^ 2 = (4 : ℕ) ^ 2 + 7 ^ 2 ∧ 65 * 4 ^ 2 = (4 : ℕ) ^ 2 + 32 ^ 2 ∧
      Squarefree (65 : ℕ) ∧ ¬ IsSquare ((4 : ℕ) ^ 2 + 7 ^ 2) ∧
      ¬ IsSquare ((7 : ℕ) ^ 2 + 32 ^ 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, by decide +kernel,
    by decide +kernel⟩
  rw [show (65 : ℕ) = 5 * 13 by norm_num]
  exact (Nat.squarefree_mul_iff.mpr ⟨by norm_num, Nat.prime_five.squarefree,
    (by norm_num : Nat.Prime 13).squarefree⟩)

end PerfectCuboid.TwistRigidity

namespace PerfectCuboid.CongruentRank

open TwistRigidity

section Twisted

variable {k a b c d e f g : ℚ}

/-- **Every twisted perfect cuboid is untwisted:** the twist `k` of a `k`-twisted perfect cuboid
is a rational square. -/
theorem IsTwistedCuboid.isSquare_twist (h : IsTwistedCuboid k a b c d e f g) : IsSquare k :=
  isSquare_of_three_faces h.pos_k h.pos_a h.pos_b h.pos_c h.hd h.he h.hf h.hg

/-- A `k`-twisted perfect cuboid is a rational perfect cuboid with the same edges and space
diagonal (face diagonals `√k·d`, `√k·e`, `√k·f`). -/
theorem IsTwistedCuboid.exists_isRatCuboid (h : IsTwistedCuboid k a b c d e f g) :
    ∃ d' e' f', IsRatCuboid a b c d' e' f' g := by
  obtain ⟨r, hr⟩ := h.isSquare_twist
  have hr0 : r ≠ 0 := by
    rintro rfl
    have := h.pos_k
    rw [hr] at this
    simp at this
  have h' : IsTwistedCuboid (1 * r ^ 2) a b c d e f g := by rw [one_mul, sq, ← hr]; exact h
  exact ⟨_, _, _, isTwistedCuboid_one_iff.mp (h'.of_mul_sq hr0)⟩

/-- There is no `k`-twisted perfect cuboid with `k ∉ ℚ²`. -/
theorem not_exists_isTwistedCuboid_of_not_isSquare (hk : ¬ IsSquare k) :
    ¬ ∃ a b c d e f g : ℚ, IsTwistedCuboid k a b c d e f g := by
  rintro ⟨a, b, c, d, e, f, g, h⟩
  exact hk h.isSquare_twist

end Twisted

section Config

variable {N x₁ x₂ x₃ y₁ y₂ y₃ : ℚ}

/-- **The square condition is automatic:** for every positive configuration, `U₁² + U₂²` is a
rational square. -/
theorem IsConfigPts.isSquare_twist (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) :
    IsSquare (edge N x₁ y₁ ^ 2 + edge N x₂ y₂ ^ 2) :=
  hc.isTwistedCuboid.isSquare_twist

/-- For every positive configuration, `−X₁X₂X₃` is a rational square. -/
theorem IsConfigPts.isSquare_neg_prod (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) :
    IsSquare (-(x₁ * x₂ * x₃)) :=
  hc.isRatCuboid_iff_isSquare.mp (hc.isRatCuboid_iff.mpr hc.isSquare_twist)

/-- **Every positive configuration is a rational perfect cuboid:** the box with edges
`|U₁|, |U₂|, |U₃|`. -/
theorem IsConfigPts.exists_isRatCuboid (hc : IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃) :
    ∃ d e f g, IsRatCuboid |edge N x₁ y₁| |edge N x₂ y₂| |edge N x₃ y₃| d e f g :=
  hc.isRatCuboid_iff.mpr hc.isSquare_twist

end Config

/-- **Perfect cuboids are exactly positive configurations** (no square condition): a perfect
cuboid exists if and only if some `E_N` has a positive cuboid configuration. -/
theorem exists_isPerfectCuboid_iff_exists_isConfigPts :
    (∃ a b c : ℕ, IsPerfectCuboid a b c) ↔
      ∃ N x₁ x₂ x₃ y₁ y₂ y₃ : ℚ, IsConfigPts N x₁ x₂ x₃ y₁ y₂ y₃ := by
  rw [exists_isPerfectCuboid_iff]
  constructor
  · rintro ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc, -⟩
    exact ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc⟩
  · rintro ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc⟩
    exact ⟨N, x₁, x₂, x₃, y₁, y₂, y₃, hc, hc.isSquare_twist⟩

/-- A perfect cuboid exists if and only if a `k`-twisted perfect cuboid exists for some `k`. -/
theorem exists_isPerfectCuboid_iff_exists_isTwistedCuboid :
    (∃ a b c : ℕ, IsPerfectCuboid a b c) ↔
      ∃ k a b c d e f g : ℚ, IsTwistedCuboid k a b c d e f g := by
  rw [exists_isPerfectCuboid_iff_exists_isConfigPts, exists_config_iff]

end PerfectCuboid.CongruentRank
