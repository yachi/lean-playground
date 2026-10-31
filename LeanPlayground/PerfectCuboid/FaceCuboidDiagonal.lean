module

public import Mathlib
public import LeanPlayground.PerfectCuboid.FaceCuboid
public import LeanPlayground.PerfectCuboid.Korec
public import LeanPlayground.PerfectCuboid.DiagonalPrimePower
public import LeanPlayground.PerfectCuboid.LeechEdge
public import LeanPlayground.PerfectCuboid.FermatTriangle

/-!
# Prime-power diagonals of a face cuboid (partial)

A face cuboid `(a, b, c)` (`IsFaceCuboid`) has `e² = a² + c²`, `f² = b² + c²`,
`g² = a² + b² + c²` integral, while `√(a² + b²)` may be irrational.

## Main results

* `FaceDiagonal.eq_zero_of_sq_add_sq_eq_prime_pow`: for `p = 2` or `p ≡ 3 (mod 4)`, the only
  representations `x² + y² = (p^k)²` are the trivial ones.
* `IsFaceCuboid.space_diagonal_prime_pow_structure`: if `g = p^k` and `p` does not divide all of
  `a, b, c`, then `p ≡ 1 (mod 4)`, `k ≥ 1`, `p` divides exactly one of `a, b`, and `p ∤ c`.
  The case `p ∤ a, p ∤ b` is excluded by the uniqueness of the primitive representation of
  `p^(2k)` (`Korec.sq_add_sq_unique`): it forces `a = b`, `e = f`, and then
  `e⁴ − a⁴ = (c g)²` contradicts Fermat (`fermat_sub`).
* `IsFaceCuboid.space_diagonal_prime_pow_descent`: the same after dividing out `p^j`.
* `IsFaceCuboid.space_diagonal_ne_prime_pow_of_eq`: a face cuboid with `a = b` has no
  prime-power space diagonal.
* `IsFaceCuboid.face_diagonal_prime_pow_structure`: if `e = p^k`, then `p ≡ 1 (mod 4)` and,
  writing the leg `b` of `(p^k, b, g)` as `2b = p^i (p^(2(k−i)) − 1)`, we have `i ≥ 1` and
  `p^i ∤ c`. (If `p^i ∣ c`, then `f = p^i F` with `F² = B² + C²`, `2B + 1 = p^(2(k−i))` and
  `C < p^(k−i)`, so `C² ≥ 2B + 1 > C²`.) In particular `p ∣ b`
  (`IsFaceCuboid.prime_dvd_of_face_diagonal_eq_prime_pow`).

The remaining open cases (not proved here) are: for `g = p^k`, the case `p ∣ a`, `p ∤ b`
(equivalently a product of two Lucas-sequence terms being `±□`), and for `e = p^k`, the case
`0 < v_p(c) < v_p(b)`, equivalently the norm `N(π^(2(n+m)) ± π̄^(2j))` being `4□`.
-/

@[expose] public section

namespace PerfectCuboid.FaceDiagonal

/-- For `p = 2` or `p ≡ 3 (mod 4)`, `x² + y² = (p^k)²` forces `x = 0` or `y = 0`. -/
theorem eq_zero_of_sq_add_sq_eq_prime_pow {p : ℕ} (hp : p.Prime) (hp4 : p % 4 ≠ 1) :
    ∀ (k : ℕ) {x y : ℕ}, x ^ 2 + y ^ 2 = (p ^ k) ^ 2 → x = 0 ∨ y = 0 := by
  intro k
  induction k with
  | zero =>
    intro x y h
    by_contra hc
    push Not at hc
    have : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hc.1)
    have : 1 ≤ y ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hc.2)
    simp at h
    omega
  | succ k ih =>
    intro x y h
    have hdiv : p ∣ x ∧ p ∣ y := by
      rcases hp.eq_two_or_odd with rfl | hodd
      · apply DiagonalPrimePower.two_dvd_of_four_dvd_sq_add_sq
        rw [h]
        exact ⟨(2 ^ k) ^ 2, by ring⟩
      · have hp3 : p % 4 = 3 := by omega
        have := Fact.mk hp
        have hpd : p ∣ x ^ 2 + y ^ 2 := by
          rw [h]; exact dvd_pow (dvd_pow_self p (Nat.succ_ne_zero k)) two_ne_zero
        have hz : ((x : ZMod p)) ^ 2 + (y : ZMod p) ^ 2 = 0 := by
          have := (ZMod.natCast_eq_zero_iff _ p).mpr hpd
          push_cast at this
          exact this
        have hy : (y : ZMod p) = 0 := by
          by_contra hy
          exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hy (eq_neg_of_add_eq_zero_left hz) hp3
        have hy' : p ∣ y := (ZMod.natCast_eq_zero_iff _ p).mp hy
        refine ⟨?_, hy'⟩
        apply hp.dvd_of_dvd_pow (n := 2)
        exact (Nat.dvd_add_left (dvd_pow hy' two_ne_zero)).mp hpd
    obtain ⟨⟨x', rfl⟩, ⟨y', rfl⟩⟩ := hdiv
    have h' : x' ^ 2 + y' ^ 2 = (p ^ k) ^ 2 := by
      have : p ^ 2 * (x' ^ 2 + y' ^ 2) = p ^ 2 * (p ^ k) ^ 2 := by
        calc p ^ 2 * (x' ^ 2 + y' ^ 2) = (p * x') ^ 2 + (p * y') ^ 2 := by ring
          _ = (p ^ (k + 1)) ^ 2 := h
          _ = p ^ 2 * (p ^ k) ^ 2 := by ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) this
    rcases ih h' with h0 | h0 <;> simp [h0]

/-- A prime that is neither `2` nor `≡ 3 (mod 4)` is `≡ 1 (mod 4)`; contrapositive form. -/
theorem mod_four_eq_one_of {p : ℕ} (hp : p.Prime) {k x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 2 + y ^ 2 = (p ^ k) ^ 2) : p % 4 = 1 := by
  by_contra h4
  rcases eq_zero_of_sq_add_sq_eq_prime_pow hp h4 k h with h0 | h0 <;> omega

/-- Dividing a sum of three squares by a common prime factor. -/
theorem div_of_dvd₃ {p x y z G : ℕ} (hp : p.Prime) (hx : p ∣ x) (hy : p ∣ y) (hz : p ∣ z)
    (hG : x ^ 2 + y ^ 2 + z ^ 2 = G ^ 2) :
    p ∣ G ∧ (x / p) ^ 2 + (y / p) ^ 2 + (z / p) ^ 2 = (G / p) ^ 2 := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  obtain ⟨z', rfl⟩ := hz
  have hG' : p ∣ G := hp.dvd_of_dvd_pow (n := 2)
    ⟨p * (x' ^ 2 + y' ^ 2 + z' ^ 2), by rw [← hG]; ring⟩
  obtain ⟨G', rfl⟩ := hG'
  refine ⟨dvd_mul_right _ _, ?_⟩
  simp only [Nat.mul_div_cancel_left _ hp.pos]
  have : p ^ 2 * (x' ^ 2 + y' ^ 2 + z' ^ 2) = p ^ 2 * G' ^ 2 := by rw [← mul_pow, ← hG]; ring
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) this

/-- Dividing a face cuboid by a common prime factor of its edges. -/
theorem isFaceCuboid_div {a b c p : ℕ} (h : IsFaceCuboid a b c) (hp : p.Prime) (ha : p ∣ a)
    (hb : p ∣ b) (hc : p ∣ c) : IsFaceCuboid (a / p) (b / p) (c / p) := by
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  have pos {w : ℕ} (hw : 0 < w) (hpw : p ∣ w) : 0 < w / p :=
    Nat.div_pos (Nat.le_of_dvd hw hpw) hp.pos
  refine ⟨pos h.pos_a ha, pos h.pos_b hb, pos h.pos_c hc, ?_, ?_, ?_⟩
  · exact ⟨e / p, by rw [← sq, (DiagonalPrimePower.div_of_dvd hp ha hc (by rw [he, sq])).2]⟩
  · exact ⟨f / p, by rw [← sq, (DiagonalPrimePower.div_of_dvd hp hb hc (by rw [hf, sq])).2]⟩
  · exact ⟨g / p, by rw [← sq, (div_of_dvd₃ hp ha hb hc (by rw [hg, sq])).2]⟩

end PerfectCuboid.FaceDiagonal

namespace PerfectCuboid

open FaceDiagonal

/-- **Space diagonal `g = p^k` of a face cuboid: structure.** If `a² + b² + c² = (p^k)²` with `p`
prime and `p` does not divide all three edges, then `p ≡ 1 (mod 4)`, `k ≥ 1`, `p` divides exactly
one of the two edges `a, b` adjacent to the irrational face diagonal, and `p ∤ c`. -/
theorem IsFaceCuboid.space_diagonal_prime_pow_structure {a b c p k : ℕ} (h : IsFaceCuboid a b c)
    (hp : p.Prime) (hg : a ^ 2 + b ^ 2 + c ^ 2 = (p ^ k) ^ 2)
    (hprim : ¬ (p ∣ a ∧ p ∣ b ∧ p ∣ c)) :
    p % 4 = 1 ∧ 1 ≤ k ∧ ((p ∣ a ∧ ¬ p ∣ b) ∨ (¬ p ∣ a ∧ p ∣ b)) ∧ ¬ p ∣ c := by
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨f, hf⟩ := h.sq_bc
  have ha0 := h.pos_a
  have hb0 := h.pos_b
  have hc0 := h.pos_c
  have heb : e ^ 2 + b ^ 2 = (p ^ k) ^ 2 := by rw [← hg, sq e, ← he]; ring
  have hfa : f ^ 2 + a ^ 2 = (p ^ k) ^ 2 := by rw [← hg, sq f, ← hf]; ring
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · subst h0; nlinarith
    · exact h0
  have hp4 : p % 4 = 1 := mod_four_eq_one_of hp he0 hb0 heb
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hg; nlinarith
    · exact hk
  have hpk : p ∣ (p ^ k) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) two_ne_zero
  have hpsum : p ∣ (a ^ 2 + c ^ 2) + b ^ 2 := by rw [← hg] at hpk; rwa [add_right_comm] at hpk
  have hpsum' : p ∣ (b ^ 2 + c ^ 2) + a ^ 2 := by
    rw [show b ^ 2 + c ^ 2 + a ^ 2 = a ^ 2 + c ^ 2 + b ^ 2 by ring]; exact hpsum
  refine ⟨hp4, hk, ?_⟩
  by_cases ha : p ∣ a <;> by_cases hb : p ∣ b
  · -- (β) both: then `p ∣ c`
    exfalso
    apply hprim
    refine ⟨ha, hb, hp.dvd_of_dvd_pow (n := 2) ?_⟩
    have h1 : p ∣ a ^ 2 + c ^ 2 := (Nat.dvd_add_left (dvd_pow hb two_ne_zero)).mp hpsum
    exact (Nat.dvd_add_right (dvd_pow ha two_ne_zero)).mp h1
  · refine ⟨Or.inl ⟨ha, hb⟩, fun hc => hb ?_⟩
    apply hp.dvd_of_dvd_pow (n := 2)
    exact (Nat.dvd_add_right (dvd_add (dvd_pow ha two_ne_zero) (dvd_pow hc two_ne_zero))).mp
      hpsum
  · refine ⟨Or.inr ⟨ha, hb⟩, fun hc => ha ?_⟩
    apply hp.dvd_of_dvd_pow (n := 2)
    exact (Nat.dvd_add_right (dvd_add (dvd_pow hb two_ne_zero) (dvd_pow hc two_ne_zero))).mp
      hpsum'
  · -- (α) neither: both representations are primitive
    exfalso
    have hp2 : p ≠ 2 := by omega
    have hpe : ¬ p ∣ e := by
      intro hpe
      apply hb
      apply hp.dvd_of_dvd_pow (n := 2)
      have : p ∣ e ^ 2 + b ^ 2 := by rw [heb]; exact hpk
      exact (Nat.dvd_add_right (dvd_pow hpe two_ne_zero)).mp this
    have hpf : ¬ p ∣ f := by
      intro hpf
      apply ha
      apply hp.dvd_of_dvd_pow (n := 2)
      have : p ∣ f ^ 2 + a ^ 2 := by rw [hfa]; exact hpk
      exact (Nat.dvd_add_right (dvd_pow hpf two_ne_zero)).mp this
    have hZ : ∀ x : ℕ, ¬ p ∣ x → ¬ (p : ℤ) ∣ (x : ℤ) := fun x hx h' =>
      hx (Int.natCast_dvd_natCast.mp h')
    have h1 : (e : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ) ^ (2 * k) := by
      have : ((e ^ 2 + b ^ 2 : ℕ) : ℤ) = ((p ^ k) ^ 2 : ℕ) := by rw [heb]
      push_cast at this; rw [this]; ring
    have h2 : (f : ℤ) ^ 2 + (a : ℤ) ^ 2 = (p : ℤ) ^ (2 * k) := by
      have : ((f ^ 2 + a ^ 2 : ℕ) : ℤ) = ((p ^ k) ^ 2 : ℕ) := by rw [hfa]
      push_cast at this; rw [this]; ring
    rcases Korec.sq_add_sq_unique hp hp2 (by omega) h1 h2 (hZ e hpe) (hZ f hpf) with
      ⟨hef, hba⟩ | ⟨hea, hbf⟩
    · -- `e = f`, `a = b`: then `e⁴ − a⁴ = (c p^k)²`
      have hea' : (e : ℤ) ^ 2 = (a : ℤ) ^ 2 + (c : ℤ) ^ 2 := by
        have : ((e * e : ℕ) : ℤ) = ((a ^ 2 + c ^ 2 : ℕ) : ℤ) := by rw [he]
        push_cast at this; linear_combination this
      have key : (e : ℤ) ^ 4 - (a : ℤ) ^ 4 = ((c : ℤ) * (p : ℤ) ^ k) ^ 2 := by
        have h1' : (e : ℤ) ^ 2 + (a : ℤ) ^ 2 = (p : ℤ) ^ (2 * k) := by rw [← hba]; exact h1
        linear_combination ((e : ℤ) ^ 2 + (a : ℤ) ^ 2) * hea' + (c : ℤ) ^ 2 * h1'
      rcases fermat_sub key with h0 | h0 | h0
      · omega
      · omega
      · rcases mul_eq_zero.mp h0 with h0 | h0
        · omega
        · exact absurd h0 (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
    · -- `e = a`: then `c = 0`
      have : (e : ℤ) ^ 2 = (a : ℤ) ^ 2 + (c : ℤ) ^ 2 := by
        have : ((e * e : ℕ) : ℤ) = ((a ^ 2 + c ^ 2 : ℕ) : ℤ) := by rw [he]
        push_cast at this; linear_combination this
      have hc2 : (c : ℤ) ^ 2 = 0 := by linear_combination hea - this
      have : (c : ℤ) = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hc2
      omega

/-- **Space diagonal `g = p^k`, general form.** For any face cuboid with `g = p^k`, after dividing
out the largest power `p^j` common to the three edges, the structure of
`space_diagonal_prime_pow_structure` holds. -/
theorem IsFaceCuboid.space_diagonal_prime_pow_descent {p : ℕ} (hp : p.Prime) :
    ∀ (k : ℕ) {a b c : ℕ}, IsFaceCuboid a b c → a ^ 2 + b ^ 2 + c ^ 2 = (p ^ k) ^ 2 →
    ∃ j < k, ∃ a' b' c', a = p ^ j * a' ∧ b = p ^ j * b' ∧ c = p ^ j * c' ∧
      IsFaceCuboid a' b' c' ∧ a' ^ 2 + b' ^ 2 + c' ^ 2 = (p ^ (k - j)) ^ 2 ∧
      p % 4 = 1 ∧ ((p ∣ a' ∧ ¬ p ∣ b') ∨ (¬ p ∣ a' ∧ p ∣ b')) ∧ ¬ p ∣ c' := by
  intro k
  induction k with
  | zero =>
    intro a b c h hg
    have := h.pos_a; have := h.pos_b; have := h.pos_c
    simp at hg; nlinarith
  | succ k ih =>
    intro a b c h hg
    by_cases hprim : p ∣ a ∧ p ∣ b ∧ p ∣ c
    · obtain ⟨ha, hb, hc⟩ := hprim
      have h' := isFaceCuboid_div h hp ha hb hc
      obtain ⟨-, hg'⟩ := div_of_dvd₃ hp ha hb hc hg
      rw [show p ^ (k + 1) / p = p ^ k by rw [pow_succ, Nat.mul_div_cancel _ hp.pos]] at hg'
      obtain ⟨j, hj, a', b', c', ha', hb', hc', hF, hg'', rest⟩ := ih h' hg'
      refine ⟨j + 1, by omega, a', b', c', ?_, ?_, ?_, hF, ?_, rest⟩
      · rw [pow_succ', mul_assoc, ← ha', Nat.mul_div_cancel' ha]
      · rw [pow_succ', mul_assoc, ← hb', Nat.mul_div_cancel' hb]
      · rw [pow_succ', mul_assoc, ← hc', Nat.mul_div_cancel' hc]
      · rw [hg'', Nat.add_sub_add_right]
    · obtain ⟨h4, -, hab, hc⟩ := h.space_diagonal_prime_pow_structure hp hg hprim
      exact ⟨0, by omega, a, b, c, by simp, by simp, by simp, h, by simpa using hg, h4, hab, hc⟩

/-- A face cuboid with two equal edges `a = b` next to the irrational face diagonal has no
prime-power space diagonal. -/
theorem IsFaceCuboid.space_diagonal_ne_prime_pow_of_eq {a c : ℕ} (h : IsFaceCuboid a a c)
    {g p k : ℕ} (hp : p.Prime) (hg : a ^ 2 + a ^ 2 + c ^ 2 = g ^ 2) : g ≠ p ^ k := by
  rintro rfl
  obtain ⟨j, -, a', b', c', ha, hb, -, -, -, -, hab, -⟩ :=
    IsFaceCuboid.space_diagonal_prime_pow_descent hp k h hg
  have : a' = b' := by
    rw [ha] at hb
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos j) hb
  subst this
  tauto

/-- **Face diagonal `e = p^k` of a face cuboid: structure.** If `a² + c² = (p^k)²` with `p` prime,
then `p ≡ 1 (mod 4)` and the leg `b` of the right triangle `(p^k, b, g)` has the form
`2b = p^i B`, `B + 1 = p^(2(k−i))` with `1 ≤ i < k` and `p^i ∤ c`. -/
theorem IsFaceCuboid.face_diagonal_prime_pow_structure {a b c p k : ℕ} (h : IsFaceCuboid a b c)
    (hp : p.Prime) (he : a ^ 2 + c ^ 2 = (p ^ k) ^ 2) :
    p % 4 = 1 ∧ ∃ i < k, 1 ≤ i ∧ ∃ B, 2 * b = p ^ i * B ∧ B + 1 = p ^ (2 * (k - i)) ∧
      ¬ p ^ i ∣ c := by
  obtain ⟨g, hg⟩ := h.sq_abc
  obtain ⟨f, hf⟩ := h.sq_bc
  have ha0 := h.pos_a
  have hb0 := h.pos_b
  have hc0 := h.pos_c
  have hp4 : p % 4 = 1 := mod_four_eq_one_of hp ha0 hc0 he
  have hleg : (p ^ k) ^ 2 + b ^ 2 = g ^ 2 := by rw [← he, sq g, ← hg]; ring
  obtain ⟨i, hik, B, hB, hB1⟩ := leg_of_prime_pow hp hb0 hleg
  have key : ¬ p ^ i ∣ c := by
    rintro ⟨C, rfl⟩
    set m := k - i with hm
    have hkm : k = i + m := by omega
    have hpi : 0 < p ^ i := pow_pos hp.pos i
    -- `B` is even since `B + 1 = p^(2m)` is odd
    have hodd : Odd (p ^ (2 * m)) := (hp.odd_of_ne_two (by omega)).pow
    obtain ⟨B', rfl⟩ : 2 ∣ B := by
      rcases Nat.even_or_odd B with ⟨r, hr⟩ | hBo
      · exact ⟨r, by omega⟩
      · exfalso
        have : Even (p ^ (2 * m)) := by rw [← hB1]; exact hBo.add_one
        exact (Nat.not_even_iff_odd.mpr hodd) this
    have hb : b = p ^ i * B' := by nlinarith
    subst hb
    have hfdvd : p ^ i ∣ f := by
      rw [← Nat.pow_dvd_pow_iff two_ne_zero]
      exact ⟨B' ^ 2 + C ^ 2, by rw [sq f, ← hf]; ring⟩
    obtain ⟨F, rfl⟩ := hfdvd
    have hF : F ^ 2 = B' ^ 2 + C ^ 2 := by
      have : (p ^ i) ^ 2 * F ^ 2 = (p ^ i) ^ 2 * (B' ^ 2 + C ^ 2) := by
        rw [← mul_pow, sq (p ^ i * F), ← hf]; ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hpi 2) this
    have hC0 : 0 < C := by
      rcases Nat.eq_zero_or_pos C with h0 | h0
      · subst h0; simp at hc0
      · exact h0
    -- `C < p^m` since `c < p^k`
    have hCm : C ^ 2 < p ^ (2 * m) := by
      have h1 : (p ^ i * C) ^ 2 < (p ^ k) ^ 2 := by rw [← he]; have := pow_pos ha0 2; omega
      rw [hkm, pow_add, mul_pow, mul_pow] at h1
      have h2 : C ^ 2 < (p ^ m) ^ 2 := Nat.lt_of_mul_lt_mul_left h1
      rwa [← pow_mul, mul_comm m 2] at h2
    -- `F > B'`, hence `C² = F² − B'² ≥ 2B' + 1 = p^(2m)`
    have hFB : B' < F := by
      have : B' ^ 2 < F ^ 2 := by rw [hF]; have := pow_pos hC0 2; omega
      exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
    nlinarith
  refine ⟨hp4, i, hik, ?_, B, hB, hB1, key⟩
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; simp at key
  · exact h0

/-- If the face diagonal `e = √(a² + c²)` of a face cuboid is a prime power `p^k`, then `p`
divides the opposite edge `b`. -/
theorem IsFaceCuboid.prime_dvd_of_face_diagonal_eq_prime_pow {a b c p k : ℕ}
    (h : IsFaceCuboid a b c) (hp : p.Prime) (he : a ^ 2 + c ^ 2 = (p ^ k) ^ 2) : p ∣ b := by
  obtain ⟨hp4, i, -, hi, B, hB, -, -⟩ := h.face_diagonal_prime_pow_structure hp he
  have : p ∣ 2 * b := hB ▸ (dvd_pow_self p (by omega)).mul_right B
  rcases (Nat.Prime.dvd_mul hp).mp this with h2 | h2
  · exfalso
    have := Nat.le_of_dvd two_pos h2
    have := hp.two_le
    have : p = 2 := by omega
    omega
  · exact h2

/-- The same for the other integral face diagonal `f = √(b² + c²)`. -/
theorem IsFaceCuboid.face_diagonal_prime_pow_structure_f {a b c p k : ℕ}
    (h : IsFaceCuboid a b c) (hp : p.Prime) (hf : b ^ 2 + c ^ 2 = (p ^ k) ^ 2) :
    p % 4 = 1 ∧ ∃ i < k, 1 ≤ i ∧ ∃ A, 2 * a = p ^ i * A ∧ A + 1 = p ^ (2 * (k - i)) ∧
      ¬ p ^ i ∣ c :=
  h.swap.face_diagonal_prime_pow_structure hp hf

end PerfectCuboid
