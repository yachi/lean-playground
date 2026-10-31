module

public import Mathlib
public import LeanPlayground.PerfectCuboid.DiagonalTwoPrimes

/-!
# Even face diagonals `2 ^ s p ^ k`: the family F2 (types II/III) (partial)

Let `a, b, c` be the edges of a perfect cuboid with no prime dividing all three, `a` odd,
`f² = b² + c²`, `g² = a² + b² + c²`, and suppose `f = 2 ^ s p ^ k` with `p` an odd prime.

* `exists_type` (Euclid form of the triangle `(a, f, g)`): `g − a = 2 p ^ j E²`,
  `g + a = 2 p ^ j D²`, `j ≤ k`, `E < D`, with `(D, E)` of type
  **I** `(2^(s-1) p^(k-j), 1)`, **II** `(p^(k-j), 2^(s-1))` or
  **III** `(2^(s-1), p^(k-j))`, `j < k`.
  This uses only that `a` is odd and `a² + f² = g²`.
* `f2_reduction`: type I is the family F1, empty by round 11
  (`DiagonalTwoPrimes.face_diagonal_ne_two_pow_mul_prime_pow_of_F1`); so only II/III remain.
* `IsPerfectCuboid.face_diagonal_two_pow_mul_prime_pow_structure`: if `p ∣ a` (i.e. `j ≥ 1`)
  then `p ∤ b, c`, `p ≡ 1 (mod 4)` and `{b, c} = {2^s (X² − Y²), 2^(s+1) X Y}` with
  `X² + Y² = p ^ k` (2-adic descent `two_pow_descent` + Euclid's parametrisation of the
  primitive triple `b₀² + c₀² = (p^k)²`).
* `IsPerfectCuboid.face_diagonal_two_pow_mul_prime_pow_param`: the combination; the whole cuboid
  is determined by `(p, s, k, j, type)` and only `a² + b² = □`, `a² + c² = □` remain.
* `sq_mul_sq_eq`: the identity `d² e² = a² g² + b² c²` (every box with `g² = a² + b² + c²`).
* `f2_small`: the sub-family `D² − E² < p ^ j`, `(D + E)² < 2 p ^ j` (`j ≥ 1`) is empty
  (`DiagonalTwoPrimes.key_lemma` with `n = 2j`).

The full statement `f ≠ 2 ^ s p ^ k` remains open (types II/III with `j ≥ 1` outside `f2_small`,
and types II/III with `j = 0`).

Near-miss check: `exists_type`, `rep_of_not_dvd` and the structure theorem never use `c > 0`
(they hold for Euler bricks and degenerate boxes alike, e.g. the brick `(693, 140, 480)` with
`f = 500 = 2²·5³`, where `p ∤ a`). `c > 0` and `g` enter only through `f2_reduction` and
`f2_small` (Lemma A / key lemma of round 11). The degenerate `(3, 4, 0)`
(`f = 4`, `g = 5`, `k = 0`) is type I with `j = 0`.
-/

@[expose] public section

namespace PerfectCuboid.FaceDiagonalF2

/-- 2-adic descent: `b² + c² = (2 ^ s N)²` forces `2 ^ s ∣ b, c`. -/
theorem two_pow_descent (N : ℕ) : ∀ (s b c : ℕ), b ^ 2 + c ^ 2 = (2 ^ s * N) ^ 2 →
    ∃ b₀ c₀, b = 2 ^ s * b₀ ∧ c = 2 ^ s * c₀ ∧ b₀ ^ 2 + c₀ ^ 2 = N ^ 2 := by
  intro s
  induction s with
  | zero => intro b c h; exact ⟨b, c, by simp, by simp, by simpa using h⟩
  | succ s ih =>
    intro b c h
    obtain ⟨⟨b', rfl⟩, ⟨c', rfl⟩⟩ := DiagonalPrimePower.two_dvd_of_four_dvd_sq_add_sq
      (y := b) (z := c) ⟨(2 ^ s * N) ^ 2, by rw [h]; ring⟩
    have h' : b' ^ 2 + c' ^ 2 = (2 ^ s * N) ^ 2 := by
      have : 4 * (b' ^ 2 + c' ^ 2) = 4 * (2 ^ s * N) ^ 2 := by
        calc 4 * (b' ^ 2 + c' ^ 2) = (2 * b') ^ 2 + (2 * c') ^ 2 := by ring
          _ = (2 ^ (s + 1) * N) ^ 2 := h
          _ = 4 * (2 ^ s * N) ^ 2 := by ring
      omega
    obtain ⟨b₀, c₀, rfl, rfl, h₀⟩ := ih b' c' h'
    exact ⟨b₀, c₀, by ring, by ring, h₀⟩

/-- Euclid's parametrisation of a coprime triple `b² + c² = z²` with `b` odd, in `ℕ`. -/
theorem euclid_nat {b c z : ℕ} (h : b ^ 2 + c ^ 2 = z ^ 2) (hcop : Nat.Coprime b c)
    (hb : b % 2 = 1) (hc : 0 < c) :
    ∃ X Y : ℕ, Y < X ∧ X ^ 2 + Y ^ 2 = z ∧ Nat.Coprime X Y ∧ X % 2 ≠ Y % 2 ∧
      b = X ^ 2 - Y ^ 2 ∧ c = 2 * X * Y := by
  have hz : 0 < z := by
    rcases Nat.eq_zero_or_pos z with h0 | h0
    · subst h0; nlinarith
    · exact h0
  have hT : PythagoreanTriple (b : ℤ) c z := by
    unfold PythagoreanTriple; nlinarith [h]
  obtain ⟨m, n, hbm, hcm, hzm, hmn, hpar, hm0⟩ := PythagoreanTriple.coprime_classification' hT
    (by rw [Int.gcd_natCast_natCast]; exact hcop) (by omega) (by exact_mod_cast hz)
  have hc' : (0 : ℤ) < 2 * m * n := by rw [← hcm]; exact_mod_cast hc
  have hm : 0 < m := by
    rcases lt_or_eq_of_le hm0 with h' | h'
    · exact h'
    · rw [← h'] at hc'; simp at hc'
  have hn : 0 < n := by
    by_contra hn; push Not at hn; nlinarith
  have hb' : (0 : ℤ) < m ^ 2 - n ^ 2 := by rw [← hbm]; exact_mod_cast (by omega : 0 < b)
  have hnm : n < m := by nlinarith
  lift m to ℕ using hm0
  lift n to ℕ using hn.le
  have hnm' : n < m := by exact_mod_cast hnm
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm'.le 2
  refine ⟨m, n, hnm', by exact_mod_cast hzm.symm, ?_, by omega, ?_, by exact_mod_cast hcm⟩
  · rw [Int.gcd_natCast_natCast] at hmn; exact hmn
  · zify [hle]; exact hbm

/-- Primitive representations of `(p ^ k)²` (Euclid). -/
theorem prim_rep {p k b c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (h : b ^ 2 + c ^ 2 = (p ^ k) ^ 2) (hpb : ¬ p ∣ b) :
    p % 4 = 1 ∧ ∃ X Y : ℕ, Y < X ∧ X ^ 2 + Y ^ 2 = p ^ k ∧ Nat.Coprime X Y ∧
      X % 2 ≠ Y % 2 ∧
      (b = X ^ 2 - Y ^ 2 ∧ c = 2 * X * Y ∨ c = X ^ 2 - Y ^ 2 ∧ b = 2 * X * Y) := by
  have hpk : p ∣ p ^ k := dvd_pow_self p (by omega)
  have hpc : ¬ p ∣ c := by
    intro hc
    apply hpb
    refine hp.dvd_of_dvd_pow (n := 2) ?_
    have : b ^ 2 = (p ^ k) ^ 2 - c ^ 2 := by omega
    rw [this]
    exact Nat.dvd_sub (dvd_pow hpk two_ne_zero) (dvd_pow hc two_ne_zero)
  have hcop : Nat.Coprime b c := by
    apply Nat.coprime_of_dvd
    intro q hq hqb hqc
    have hq2 : q ∣ (p ^ k) ^ 2 := by
      rw [← h]; exact dvd_add (dvd_pow hqb two_ne_zero) (dvd_pow hqc two_ne_zero)
    have hqp : q ∣ p := hq.dvd_of_dvd_pow (hq.dvd_of_dvd_pow hq2)
    rw [(Nat.prime_dvd_prime_iff_eq hq hp).mp hqp] at hqb
    exact hpb hqb
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · exact absurd h2 hp2
    · exact h2
  have hpkodd : (p ^ k) % 2 = 1 := by rw [Nat.pow_mod, hpodd]; simp
  have hb0 : b ≠ 0 := by rintro rfl; exact hpb (dvd_zero p)
  have hc0 : c ≠ 0 := by rintro rfl; exact hpc (dvd_zero p)
  -- the representation
  obtain ⟨X, Y, hYX, hXY, hco, hpar, hbc⟩ : ∃ X Y : ℕ, Y < X ∧ X ^ 2 + Y ^ 2 = p ^ k ∧
      Nat.Coprime X Y ∧ X % 2 ≠ Y % 2 ∧
      (b = X ^ 2 - Y ^ 2 ∧ c = 2 * X * Y ∨ c = X ^ 2 - Y ^ 2 ∧ b = 2 * X * Y) := by
    rcases Nat.even_or_odd b with hbe | hbo
    · have hco : c % 2 = 1 := by
        rcases Nat.even_or_odd c with hce | hco
        · exfalso
          obtain ⟨u, rfl⟩ := hbe; obtain ⟨v, rfl⟩ := hce
          have : (p ^ k) ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hpkodd]
          rw [← h] at this; ring_nf at this; omega
        · exact Nat.odd_iff.mp hco
      obtain ⟨X, Y, h1, h2, h3, h4, h5, h6⟩ :=
        euclid_nat (by rw [← h]; ring) hcop.symm hco (Nat.pos_of_ne_zero hb0)
      exact ⟨X, Y, h1, h2, h3, h4, Or.inr ⟨h5, h6⟩⟩
    · obtain ⟨X, Y, h1, h2, h3, h4, h5, h6⟩ :=
        euclid_nat h hcop (Nat.odd_iff.mp hbo) (Nat.pos_of_ne_zero hc0)
      exact ⟨X, Y, h1, h2, h3, h4, Or.inl ⟨h5, h6⟩⟩
  refine ⟨?_, X, Y, hYX, hXY, hco, hpar, hbc⟩
  -- `p ≡ 1 (mod 4)`
  have hpY : ¬ p ∣ Y := by
    intro hY
    have hX : p ∣ X := hp.dvd_of_dvd_pow (n := 2) (by
      have : X ^ 2 = p ^ k - Y ^ 2 := by omega
      rw [this]; exact Nat.dvd_sub hpk (dvd_pow hY two_ne_zero))
    have h1 : p ∣ 1 := hco ▸ Nat.dvd_gcd hX hY
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have := Fact.mk hp
  have hY0 : (Y : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpY
  have hsq : (X : ZMod p) ^ 2 = -(Y : ZMod p) ^ 2 := by
    have : ((X ^ 2 + Y ^ 2 : ℕ) : ZMod p) = 0 := by
      rw [hXY, ZMod.natCast_eq_zero_iff]; exact hpk
    push_cast at this
    linear_combination this
  have := ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hY0 hsq
  omega

/-- **Euclid types.** Let `a` be odd and `a² + f² = g²` with `f = 2 ^ s p ^ k`, `s ≥ 1`, `p` an odd
prime. Then `g − a = 2 p ^ j E²`, `g + a = 2 p ^ j D²` (equivalently `a = p ^ j (D² − E²)`,
`g = p ^ j (D² + E²)`, `f = 2 p ^ j D E`) with `j ≤ k`, `E < D`, and `(D, E)` of one of the three
types **I** `(2 ^ (s-1) p ^ (k-j), 1)`, **II** `(p ^ (k-j), 2 ^ (s-1))`,
**III** `(2 ^ (s-1), p ^ (k-j))` with `j < k`. -/
theorem exists_type {a f g p s k : ℕ} (hp : p.Prime) (ha : a % 2 = 1)
    (hs : 1 ≤ s) (hag : a ^ 2 + f ^ 2 = g ^ 2) (hf : f = 2 ^ s * p ^ k) :
    ∃ j D E : ℕ, j ≤ k ∧ E < D ∧ g = a + 2 * p ^ j * E ^ 2 ∧ a + p ^ j * E ^ 2 = p ^ j * D ^ 2 ∧
      (D = 2 ^ (s - 1) * p ^ (k - j) ∧ E = 1 ∨ D = p ^ (k - j) ∧ E = 2 ^ (s - 1) ∨
        j < k ∧ D = 2 ^ (s - 1) ∧ E = p ^ (k - j)) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hp0 : 0 < p := hp.pos
  -- `g` is odd and `g > a`
  have hf2 : f % 2 = 0 := by
    have : f = 2 * (2 ^ t * p ^ k) := by rw [hf, pow_succ]; ring
    omega
  have hgo : g % 2 = 1 := by
    have h1 : (a ^ 2 + f ^ 2) % 2 = 1 := by simp [Nat.add_mod, Nat.pow_mod, ha, hf2]
    rw [hag] at h1
    rcases Nat.mod_two_eq_zero_or_one g with h | h
    · simp [Nat.pow_mod, h] at h1
    · exact h
  have hf0 : 0 < f := by rw [hf]; positivity
  have hag' : a < g := by
    have : a ^ 2 < g ^ 2 := by rw [← hag]; have := pow_pos hf0 2; omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  obtain ⟨u, rfl⟩ : ∃ u, g = a + 2 * u := ⟨(g - a) / 2, by omega⟩
  have hu0 : 0 < u := by omega
  -- `u (a + u) = 2 ^ (2t) p ^ (2k)`
  have key : u * (a + u) = 2 ^ (2 * t) * p ^ (2 * k) := by
    have : a ^ 2 + 4 * (u * (a + u)) = a ^ 2 + 4 * (2 ^ (2 * t) * p ^ (2 * k)) := by
      rw [show a ^ 2 + 4 * (u * (a + u)) = (a + 2 * u) ^ 2 by ring,
        show 4 * (2 ^ (2 * t) * p ^ (2 * k)) = (2 ^ (t + 1) * p ^ k) ^ 2 by ring, ← hf, hag]
    omega
  obtain ⟨y, z, hy, hz, hyz⟩ := (dvd_mul (k := u)).mp ⟨a + u, key.symm⟩
  obtain ⟨α, hα, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
  obtain ⟨β, hβ, rfl⟩ := (Nat.dvd_prime_pow hp).mp hz
  subst hyz
  have hw : a + 2 ^ α * p ^ β = 2 ^ (2 * t - α) * p ^ (2 * k - β) := by
    have h1 : 2 ^ (2 * t) * p ^ (2 * k) =
        2 ^ α * p ^ β * (2 ^ (2 * t - α) * p ^ (2 * k - β)) := by
      rw [show 2 ^ (2 * t) = 2 ^ α * 2 ^ (2 * t - α) by rw [← pow_add, Nat.add_sub_cancel' hα],
        show p ^ (2 * k) = p ^ β * p ^ (2 * k - β) by rw [← pow_add, Nat.add_sub_cancel' hβ]]
      ring
    rw [h1] at key
    exact Nat.eq_of_mul_eq_mul_left (by positivity) key
  -- parity: `α = 0` or `α = 2t`
  have hα' : α = 0 ∨ α = 2 * t := by
    by_contra hne
    push Not at hne
    have h2u : 2 ∣ 2 ^ α * p ^ β :=
      Dvd.dvd.mul_right (dvd_pow_self 2 hne.1) _
    have h2w : 2 ∣ 2 ^ (2 * t - α) * p ^ (2 * k - β) :=
      Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    rw [← hw] at h2w
    omega
  -- the generic conclusion `E < D`
  have fin : ∀ j D E : ℕ, j ≤ k → 2 ^ α * p ^ β = p ^ j * E ^ 2 →
      a + p ^ j * E ^ 2 = p ^ j * D ^ 2 →
      (D = 2 ^ t * p ^ (k - j) ∧ E = 1 ∨ D = p ^ (k - j) ∧ E = 2 ^ t ∨
        j < k ∧ D = 2 ^ t ∧ E = p ^ (k - j)) →
      ∃ j D E : ℕ, j ≤ k ∧ E < D ∧ a + 2 * (2 ^ α * p ^ β) = a + 2 * p ^ j * E ^ 2 ∧
        a + p ^ j * E ^ 2 = p ^ j * D ^ 2 ∧
        (D = 2 ^ t * p ^ (k - j) ∧ E = 1 ∨ D = p ^ (k - j) ∧ E = 2 ^ t ∨
          j < k ∧ D = 2 ^ t ∧ E = p ^ (k - j)) := by
    intro j D E hj hu hw' hty
    refine ⟨j, D, E, hj, ?_, by rw [hu]; ring, hw', hty⟩
    have hpj : 0 < p ^ j := pow_pos hp0 j
    have : p ^ j * E ^ 2 < p ^ j * D ^ 2 := by omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (Nat.lt_of_mul_lt_mul_left this)
  rcases le_or_gt β k with hβk | hβk
  · rcases hα' with rfl | rfl
    · rw [Nat.sub_zero] at hw
      have e1 : 2 ^ 0 * p ^ β = p ^ β * 1 ^ 2 := by ring
      refine fin β (2 ^ t * p ^ (k - β)) 1 hβk e1 ?_ (Or.inl ⟨rfl, rfl⟩)
      rw [← e1, hw, show 2 * k - β = β + 2 * (k - β) by omega]; ring
    · rw [Nat.sub_self] at hw
      have e1 : 2 ^ (2 * t) * p ^ β = p ^ β * (2 ^ t) ^ 2 := by ring
      refine fin β (p ^ (k - β)) (2 ^ t) hβk e1 ?_ (Or.inr (Or.inl ⟨rfl, rfl⟩))
      rw [← e1, hw, show 2 * k - β = β + 2 * (k - β) by omega]; ring
  · rcases hα' with rfl | rfl
    · rw [Nat.sub_zero] at hw
      have e1 : 2 ^ 0 * p ^ β = p ^ (2 * k - β) * (p ^ (k - (2 * k - β))) ^ 2 := by
        rw [show β = (2 * k - β) + 2 * (k - (2 * k - β)) by omega]
        rw [show 2 * k - (2 * k - β + 2 * (k - (2 * k - β))) = 2 * k - β by omega]; ring
      refine fin (2 * k - β) (2 ^ t) (p ^ (k - (2 * k - β))) (by omega) e1 ?_
        (Or.inr (Or.inr ⟨by omega, rfl, rfl⟩))
      rw [← e1, hw]; ring
    · exfalso
      have h1 : p ^ (2 * k - β) < p ^ β := Nat.pow_lt_pow_right hp.one_lt (by omega)
      have h2 : p ^ β ≤ 2 ^ (2 * t) * p ^ β := Nat.le_mul_of_pos_left _ (by positivity)
      rw [Nat.sub_self, pow_zero, one_mul] at hw
      omega

/-- **The product identity.** For every box (no integrality needed),
`(a² + b²)(a² + c²) = a² (a² + b² + c²) + b² c²`; so in an Euler brick `(ag, bc, de)` is a
Pythagorean triple whenever `g² = a² + b² + c²` is a square. -/
theorem sq_mul_sq_eq {a b c d e g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : d ^ 2 * e ^ 2 = a ^ 2 * g ^ 2 + b ^ 2 * c ^ 2 := by
  rw [← hd, ← he, ← hg]; ring

/-- **Representation core.** If `b² + c² = (2 ^ s p ^ k)²` with `p` an odd prime, `k ≥ 1` and
`p ∤ b`, then `p ≡ 1 (mod 4)` and `{b, c} = {2 ^ s (X² − Y²), 2 ^ (s+1) X Y}` with
`X² + Y² = p ^ k`, `Y < X`, `gcd(X, Y) = 1`, `X ≢ Y (mod 2)`. -/
theorem rep_of_not_dvd {b c p s k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (h : b ^ 2 + c ^ 2 = (2 ^ s * p ^ k) ^ 2) (hpb : ¬ p ∣ b) :
    p % 4 = 1 ∧ ∃ X Y : ℕ, Y < X ∧ X ^ 2 + Y ^ 2 = p ^ k ∧ Nat.Coprime X Y ∧
      X % 2 ≠ Y % 2 ∧
      (b = 2 ^ s * (X ^ 2 - Y ^ 2) ∧ c = 2 ^ (s + 1) * X * Y ∨
        c = 2 ^ s * (X ^ 2 - Y ^ 2) ∧ b = 2 ^ (s + 1) * X * Y) := by
  obtain ⟨b₀, c₀, rfl, rfl, h₀⟩ := two_pow_descent (p ^ k) s b c h
  have hpb₀ : ¬ p ∣ b₀ := fun hd => hpb (Dvd.dvd.mul_left hd _)
  obtain ⟨h4, X, Y, h1, h2, h3, h5, h6⟩ := prim_rep hp hp2 hk h₀ hpb₀
  refine ⟨h4, X, Y, h1, h2, h3, h5, ?_⟩
  rcases h6 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, by ring⟩
  · exact Or.inr ⟨rfl, by ring⟩

/-- **Structure theorem (guaranteed deliverable of round 12, brief 5).** In a perfect cuboid
with no prime dividing all three edges, if the diagonal of the face `(b, c)` is
`2 ^ s p ^ k` with `p` an odd prime, `k ≥ 1` and `p ∣ a`, then `p ∤ b`, `p ∤ c`,
`p ≡ 1 (mod 4)` and `{b, c} = {2 ^ s (X² − Y²), 2 ^ (s+1) X Y}` where `X + iY` is a Gaussian
integer of norm `p ^ k` (`X² + Y² = p ^ k`, `0 ≤ Y < X`, coprime, of opposite parity). In
particular `b, c` are determined by `(p, s, k)` up to order (uniqueness of `X, Y`:
`Korec.sq_add_sq_unique`). -/
theorem _root_.PerfectCuboid.IsPerfectCuboid.face_diagonal_two_pow_mul_prime_pow_structure
    {a b c : ℕ} (_h : IsPerfectCuboid a b c)
    (hprim : ∀ q : ℕ, q.Prime → q ∣ a → q ∣ b → q ∣ c → False)
    {p s k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (hf : b ^ 2 + c ^ 2 = (2 ^ s * p ^ k) ^ 2) (hpa : p ∣ a) :
    ¬ p ∣ b ∧ ¬ p ∣ c ∧ p % 4 = 1 ∧ ∃ X Y : ℕ, Y < X ∧ X ^ 2 + Y ^ 2 = p ^ k ∧
      Nat.Coprime X Y ∧ X % 2 ≠ Y % 2 ∧
      (b = 2 ^ s * (X ^ 2 - Y ^ 2) ∧ c = 2 ^ (s + 1) * X * Y ∨
        c = 2 ^ s * (X ^ 2 - Y ^ 2) ∧ b = 2 ^ (s + 1) * X * Y) := by
  have hpf : p ∣ (2 ^ s * p ^ k) ^ 2 :=
    Dvd.dvd.mul_left (dvd_pow_self p (by omega)) _ |>.trans (dvd_pow_self _ two_ne_zero)
  have other {y z : ℕ} (hyz : y ^ 2 + z ^ 2 = (2 ^ s * p ^ k) ^ 2) (hy : p ∣ y) : p ∣ z := by
    refine hp.dvd_of_dvd_pow (n := 2) ?_
    have : z ^ 2 = (2 ^ s * p ^ k) ^ 2 - y ^ 2 := by omega
    rw [this]; exact Nat.dvd_sub hpf (dvd_pow hy two_ne_zero)
  have hpb : ¬ p ∣ b := fun hb => hprim p hp hpa hb (other hf hb)
  have hpc : ¬ p ∣ c := fun hc => hprim p hp hpa (other (by rw [← hf]; ring) hc) hc
  exact ⟨hpb, hpc, rep_of_not_dvd hp hp2 hk hf hpb⟩

/-- **Reduction to the family F2.** Let `a, b, c > 0` be the edges of a perfect cuboid with `a`
odd and `p` not dividing all three edges, `d, e, f, g` its diagonals, and
`f = 2 ^ s p ^ k` (`s ≥ 1`, `p` an odd prime). Then, in the Euclid form
`g − a = 2 p ^ j E²`, `g + a = 2 p ^ j D²` of `exists_type`, the pair `(D, E)` is of type II
`(p ^ (k-j), 2 ^ (s-1))` or III `(2 ^ (s-1), p ^ (k-j))` with `j < k`: type I is the family F1,
which is empty (`DiagonalTwoPrimes.face_diagonal_ne_two_pow_mul_prime_pow_of_F1`). -/
theorem f2_reduction {a b c d e f g p s k : ℕ} (ha0 : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (prim : p ∣ a → p ∣ b → p ∣ c → False) (ha : a % 2 = 1) (hs : 1 ≤ s)
    (hfk : f = 2 ^ s * p ^ k) :
    ∃ j D E : ℕ, j ≤ k ∧ E < D ∧ g = a + 2 * p ^ j * E ^ 2 ∧ a + p ^ j * E ^ 2 = p ^ j * D ^ 2 ∧
      (D = p ^ (k - j) ∧ E = 2 ^ (s - 1) ∨ j < k ∧ D = 2 ^ (s - 1) ∧ E = p ^ (k - j)) := by
  obtain ⟨j, D, E, hj, hED, hgE, haD, hty⟩ :=
    exists_type (f := f) (g := g) hp ha hs (by rw [← hf, ← hg]; ring) hfk
  refine ⟨j, D, E, hj, hED, hgE, haD, ?_⟩
  rcases hty with ⟨-, rfl⟩ | hty | hty
  · exact absurd (DiagonalTwoPrimes.face_diagonal_ne_two_pow_mul_prime_pow_of_F1 ha0 hb hc hd he
      hf hg hp hp2 prim hfk (by rw [hgE]; ring) hj) id
  · exact Or.inl hty
  · exact Or.inr hty

/-- **Full parametrisation of the open family F2.** Let `a, b, c` be the edges of a perfect cuboid
with no prime dividing all three, `a` odd, and let the diagonal of the face `(b, c)` be
`f = 2 ^ s p ^ k` (`s ≥ 1`, `p` an odd prime). Then there are `j ≤ k` and `D > E` with
`a = p ^ j (D² − E²)`, `g = a + 2 p ^ j E²` (so `g = p ^ j (D² + E²)`) and
`(D, E) = (p ^ (k-j), 2 ^ (s-1))` (type II) or `(2 ^ (s-1), p ^ (k-j))`, `j < k` (type III).
If moreover `j ≥ 1`, then `p ≡ 1 (mod 4)` and `{b, c} = {2 ^ s (X² − Y²), 2 ^ (s+1) X Y}` with
`X² + Y² = p ^ k`. So the whole cuboid is determined by `(p, s, k, j, type)`, and only the two
conditions `a² + b² = □`, `a² + c² = □` remain. -/
theorem _root_.PerfectCuboid.IsPerfectCuboid.face_diagonal_two_pow_mul_prime_pow_param
    {a b c : ℕ} (h : IsPerfectCuboid a b c)
    (hprim : ∀ q : ℕ, q.Prime → q ∣ a → q ∣ b → q ∣ c → False)
    {f p s k : ℕ} (hf : b ^ 2 + c ^ 2 = f ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : a % 2 = 1) (hs : 1 ≤ s) (hfk : f = 2 ^ s * p ^ k) {g : ℕ}
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    ∃ j D E : ℕ, j ≤ k ∧ E < D ∧ g = a + 2 * p ^ j * E ^ 2 ∧ a + p ^ j * E ^ 2 = p ^ j * D ^ 2 ∧
      (D = p ^ (k - j) ∧ E = 2 ^ (s - 1) ∨ j < k ∧ D = 2 ^ (s - 1) ∧ E = p ^ (k - j)) ∧
      (1 ≤ j → p % 4 = 1 ∧ ∃ X Y : ℕ, Y < X ∧ X ^ 2 + Y ^ 2 = p ^ k ∧
        (b = 2 ^ s * (X ^ 2 - Y ^ 2) ∧ c = 2 ^ (s + 1) * X * Y ∨
          c = 2 ^ s * (X ^ 2 - Y ^ 2) ∧ b = 2 ^ (s + 1) * X * Y)) := by
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ca
  obtain ⟨j, D, E, hj, hED, hgE, haD, hty⟩ :=
    f2_reduction h.pos_a h.pos_b h.pos_c (d := d) (e := e) (by rw [hd]; ring)
      (by rw [add_comm, he]; ring) hf hg hp hp2 (hprim p hp) ha hs hfk
  refine ⟨j, D, E, hj, hED, hgE, haD, hty, fun hj1 => ?_⟩
  have hpa : p ∣ a := by
    have h1 : p ∣ p ^ j * D ^ 2 :=
      Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
    have h2 : p ∣ p ^ j * E ^ 2 :=
      Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
    rw [← haD] at h1
    exact (Nat.dvd_add_right h2).mp (by rwa [add_comm] at h1)
  obtain ⟨-, -, h4, X, Y, h1, h2, -, -, h6⟩ :=
    h.face_diagonal_two_pow_mul_prime_pow_structure hprim (s := s) (k := k) hp hp2 (by omega)
      (by rw [hf, hfk]) hpa
  exact ⟨h4, X, Y, h1, h2, h6⟩

/-- **A proved sub-family of F2 (key lemma of round 11).** In a perfect cuboid whose odd edge
`a` has Euclid form `g = a + 2 p ^ j E²`, `a + p ^ j E² = p ^ j D²` with respect to the face
diagonal `f` (`a² + f² = g²`), with `p` an odd prime not dividing all three edges and `j ≥ 1`,
the "small" configurations `D² − E² < p ^ j` and `(D + E)² < 2 p ^ j` are impossible.
(Then `a < p ^ (2j)` and `g + f = p ^ j (D + E)² < 2 p ^ (2j)`, and
`DiagonalTwoPrimes.key_lemma` applies with `n = 2j`.) Numerically this covers 31943 of the
67392 lemma-A-admissible F2 configurations with `1 ≤ j < k`, `p < 3000`, `s ≤ 20`, `k ≤ 8`. -/
theorem f2_small {a b c d e f g p j D E : ℕ} (ha0 : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (prim : p ∣ a → p ∣ b → p ∣ c → False) (hj : 1 ≤ j)
    (hgE : g = a + 2 * p ^ j * E ^ 2) (haD : a + p ^ j * E ^ 2 = p ^ j * D ^ 2)
    (hsmall1 : D ^ 2 < p ^ j + E ^ 2) (hsmall2 : (D + E) ^ 2 < 2 * p ^ j) : False := by
  set P := p ^ j with hP
  have hP0 : 0 < P := pow_pos hp.pos j
  -- `f = 2 P D E`
  have hfsq : (f : ℤ) ^ 2 = (2 * P * D * E) ^ 2 := by
    have e1 : (a : ℤ) ^ 2 + f ^ 2 = g ^ 2 := by
      have : a ^ 2 + f ^ 2 = g ^ 2 := by rw [← hf, ← hg]; ring
      exact_mod_cast this
    have e2 : (g : ℤ) = a + 2 * P * E ^ 2 := by exact_mod_cast hgE
    have e3 : (a : ℤ) + P * E ^ 2 = P * D ^ 2 := by exact_mod_cast haD
    linear_combination e1 + (g + a + 2 * P * E ^ 2) * e2 + 4 * P * E ^ 2 * e3
  have hfP : f = 2 * P * D * E := by
    have : f ^ 2 = (2 * P * D * E) ^ 2 := by exact_mod_cast hfsq
    exact Nat.pow_left_injective two_ne_zero this
  -- `D > E`
  have hED : E < D := by
    have : P * E ^ 2 < P * D ^ 2 := by omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (Nat.lt_of_mul_lt_mul_left this)
  have hD0 : 0 < D := by omega
  -- divisibility
  have hpP : p ∣ P := dvd_pow_self p (by omega)
  have hPa : P ∣ a := by
    have : a = P * (D ^ 2 - E ^ 2) := by
      rw [Nat.mul_sub]; omega
    exact ⟨_, this⟩
  have hpa : p ∣ a := hpP.trans hPa
  have hpf : p ∣ f := by rw [hfP]; exact (hpP.mul_left 2).mul_right _ |>.mul_right _
  have hpf2 : p ∣ f ^ 2 := dvd_pow hpf two_ne_zero
  have other {y z : ℕ} (hyz : y ^ 2 + z ^ 2 = f ^ 2) (hy : p ∣ y) : p ∣ z := by
    refine hp.dvd_of_dvd_pow (n := 2) ?_
    have : z ^ 2 = f ^ 2 - y ^ 2 := by omega
    rw [this]; exact Nat.dvd_sub hpf2 (dvd_pow hy two_ne_zero)
  have hp2' : ¬ p ∣ 2 := fun h2 =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have not2 {w : ℕ} (hw : ¬ p ∣ w) : ¬ p ∣ 2 * w := fun h2 =>
    (hp.dvd_mul.mp h2).elim hp2' hw
  have hpb : ¬ p ∣ b := fun hb' => prim hpa hb' (other hf hb')
  have hpc : ¬ p ∣ c := fun hc' => prim hpa (other (by rw [← hf]; ring) hc') hc'
  -- sizes
  have hdvd : p ^ (2 * j) ∣ a ^ 2 := by
    rw [pow_mul', ← hP]; exact pow_dvd_pow_of_dvd hPa 2
  have hxlt : a < p ^ (2 * j) := by
    rw [pow_mul', ← hP]
    have : a + P * E ^ 2 < P * (P + E ^ 2) := by
      rw [haD]; exact Nat.mul_lt_mul_of_pos_left hsmall1 hP0
    nlinarith
  have hlt : g + f < 2 * p ^ (2 * j) := by
    rw [pow_mul', ← hP]
    have h1 : g + f = P * (D + E) ^ 2 := by
      rw [hgE, hfP]
      have : a = P * D ^ 2 - P * E ^ 2 := by omega
      have hle : P * E ^ 2 ≤ P * D ^ 2 := by omega
      rw [this]; zify [hle]; ring
    rw [h1]
    have := Nat.mul_lt_mul_of_pos_left hsmall2 hP0
    nlinarith
  exact DiagonalTwoPrimes.key_lemma hp ha0 hb hc hd he hf hg (not2 hpb) (not2 hpc) hdvd hxlt hlt

end PerfectCuboid.FaceDiagonalF2
