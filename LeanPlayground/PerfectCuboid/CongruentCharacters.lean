module

public import LeanPlayground.PerfectCuboid.BeauvilleLambda
public import LeanPlayground.PerfectCuboid.Genocchi

/-!
# Three congruent numbers of a perfect cuboid

A *body cuboid* is a box with edges `x, y, z` in which the two face diagonals `u, v` through the
edge `x` and the space diagonal `g` are integers:

  `u² = x² + y²`,  `v² = x² + z²`,  `g² = x² + y² + z²`.

(Infinitely many exist; the face diagonal `√(y² + z²)` is not required to be an integer.) With
`s = g + u` and `t = x + v` there is the identity

  `(s − t)(g + v)(x + u) = y² (s + t)`,

so the right triangle `(s² − t², 2st, s² + t²)` has area `s t (s² − t²) = D · (s t y (s + t) / D)²`
with `D = (x + u)(x + v)(g + u)(g + v)`. Hence `D` is a congruent number (`isCongruent_body`).

A perfect cuboid is a body cuboid in three ways, once for each edge, so it gives three congruent
numbers. These are the three `j = 1728` twist classes `μ₂μ₃`, `μ₁μ₃`, `μ₁μ₂` of
`BeauvilleCharacters.lean`, now over `ℚ` instead of `ℚ(i)`. Genocchi's theorems (`Genocchi.lean`)
then exclude whole square classes:

* `IsPerfectCuboid.diag_prod_{ed,fd,fe}_ne_prime_mul_sq`: `(a+d)(a+e)(g+d)(g+e)`,
  `(b+d)(b+f)(g+d)(g+f)` and `(c+e)(c+f)(g+e)(g+f)` are never `p m²` with `p ≡ 3 (mod 8)` prime.
* `IsPerfectCuboid.diag_prod_{ed,fd,fe}_ne_two_mul_prime_mul_sq`: nor `2p m²` with
  `p ≡ 5 (mod 8)` prime.
* `IsPerfectCuboid.gcd_prod_ed_ne_prime_mul_sq`: if `a` is the odd edge,
  `(a,c)(b,e)(a,b)(c,d) ≠ p m²` for `p ≡ 3 (mod 8)`, because then
  `(a+d)(a+e)(g+d)(g+e) · (a,c)(b,e)(a,b)(c,d) = 16 N²`.
* `IsPerfectCuboid.squarefree_part_ne`: the squarefree part `N` of `abcg/2`
  (`IsPerfectCuboid.isCongruent`) is not such a `p` or `2p`.

These are theorems about body cuboids, which exist, so like `μᵢ ≠ μⱼ` and `λ ≠ 1` they remove
square classes of perfect cuboids rather than all of them. Degenerate boxes `(m² − n², 2mn, 0)`
give honest congruent numbers (`(3, 4, 0)` gives `D = 3840`, class `15`), consistent with the
theorems. See `fable-new-frameworks-round7.md` (round 7, Brief 4).
-/

@[expose] public section

namespace PerfectCuboid

open CongruentRank

/-- **A body cuboid gives a congruent number.** If `u² = x² + y²`, `v² = x² + z²` and
`g² = x² + y² + z²` with `x, y > 0`, then `(x + u)(x + v)(g + u)(g + v)` is a congruent number.
`z = 0` is allowed. -/
theorem isCongruent_body {x y z u v g : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hu : u ^ 2 = x ^ 2 + y ^ 2) (hv : v ^ 2 = x ^ 2 + z ^ 2)
    (hg : g ^ 2 = x ^ 2 + y ^ 2 + z ^ 2) :
    IsCongruent (((x + u) * (x + v) * (g + u) * (g + v) : ℕ) : ℚ) := by
  have hu' : (u : ℚ) ^ 2 = x ^ 2 + y ^ 2 := by exact_mod_cast hu
  have hv' : (v : ℚ) ^ 2 = x ^ 2 + z ^ 2 := by exact_mod_cast hv
  have hg' : (g : ℚ) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by exact_mod_cast hg
  have hx0 : (0 : ℚ) < x := by exact_mod_cast hx
  have hy0 : (0 : ℚ) < y := by exact_mod_cast hy
  have hu0 : (0 : ℚ) ≤ u := by positivity
  have hv0 : (0 : ℚ) ≤ v := by positivity
  have hg0 : (0 : ℚ) ≤ g := by positivity
  -- `u > x` and `g > v`, so `s > t > 0`
  have hux : (x : ℚ) < u := by nlinarith
  have hgv : (v : ℚ) < g := by nlinarith
  set s : ℚ := g + u with hs
  set t : ℚ := x + v with ht
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < s := by linarith
  have hts : t < s := by linarith
  have key : (s - t) * (g + v) * (x + u) = y ^ 2 * (s + t) := by
    rw [hs, ht]; linear_combination (g + v) * hu' - (u + x) * hv' + (u + x) * hg'
  push_cast
  set D : ℚ := (x + u) * (x + v) * (g + u) * (g + v) with hD
  have hD0 : 0 < D :=
    mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by linarith)
  set q : ℚ := s * t * y * (s + t) / D with hq
  have hq0 : 0 < q := div_pos (mul_pos (mul_pos (mul_pos hs0 ht0) hy0) (by linarith)) hD0
  refine ⟨(s ^ 2 - t ^ 2) / q, 2 * s * t / q, (s ^ 2 + t ^ 2) / q, ?_, by positivity, ?_, ?_⟩
  · have : 0 < s ^ 2 - t ^ 2 := by nlinarith
    positivity
  · field_simp; ring
  · rw [hq]
    field_simp
    rw [hD]
    rw [hs, ht] at key ⊢
    linear_combination (g + u + (x + v)) * (g + u) * (x + v) * key

/-! ### Genocchi's square classes -/

/-- A congruent number is never `p m²` with `p ≡ 3 (mod 8)` prime. -/
theorem ne_prime_mul_sq_of_isCongruent {D p : ℕ} (hD : IsCongruent (D : ℚ)) (hp : p.Prime)
    (h8 : p % 8 = 3) (m : ℕ) : D ≠ p * m ^ 2 := by
  rintro rfl
  have hm : (m : ℚ) ≠ 0 := by
    rintro h0
    have := hD.pos
    push_cast [h0] at this
    simp at this
  push_cast at hD
  rw [mul_comm, isCongruent_mul_sq_iff hm] at hD
  exact FermatTriangle.not_isCongruent_prime_three_mod_eight hp h8 hD

/-- A congruent number is never `2 p m²` with `p ≡ 5 (mod 8)` prime. -/
theorem ne_two_mul_prime_mul_sq_of_isCongruent {D p : ℕ} (hD : IsCongruent (D : ℚ))
    (hp : p.Prime) (h8 : p % 8 = 5) (m : ℕ) : D ≠ 2 * p * m ^ 2 := by
  rintro rfl
  have hm : (m : ℚ) ≠ 0 := by
    rintro h0
    have := hD.pos
    push_cast [h0] at this
    simp at this
  push_cast at hD
  rw [mul_comm, isCongruent_mul_sq_iff hm] at hD
  exact FermatTriangle.not_isCongruent_two_mul_prime_five_mod_eight hp h8 hD

/-! ### The three congruent numbers of a perfect cuboid -/

variable {a b c : ℕ}

/-- The congruent number of the edge `a` (diagonals `d`, `e`; class `μ₂μ₃`). -/
theorem IsPerfectCuboid.isCongruent_ed (h : IsPerfectCuboid a b c) {d e g : ℕ}
    (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    IsCongruent (((a + d) * (a + e) * (g + d) * (g + e) : ℕ) : ℚ) :=
  isCongruent_body h.pos_a h.pos_b hd he hg

/-- The congruent number of the edge `b` (diagonals `d`, `f`; class `μ₁μ₃` up to `2`). -/
theorem IsPerfectCuboid.isCongruent_fd (h : IsPerfectCuboid a b c) {d f g : ℕ}
    (hd : d ^ 2 = a ^ 2 + b ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    IsCongruent (((b + d) * (b + f) * (g + d) * (g + f) : ℕ) : ℚ) :=
  isCongruent_body (x := b) (y := a) (z := c) h.pos_b h.pos_a (by rw [hd]; ring) hf
    (by rw [hg]; ring)

/-- The congruent number of the edge `c` (diagonals `e`, `f`; class `μ₁μ₂` up to `2`). -/
theorem IsPerfectCuboid.isCongruent_fe (h : IsPerfectCuboid a b c) {e f g : ℕ}
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    IsCongruent (((c + e) * (c + f) * (g + e) * (g + f) : ℕ) : ℚ) :=
  isCongruent_body (x := c) (y := a) (z := b) h.pos_c h.pos_a (by rw [he]; ring)
    (by rw [hf]; ring) (by rw [hg]; ring)

/-- **`(a+d)(a+e)(g+d)(g+e)` is never `p m²` with `p ≡ 3 (mod 8)` prime.** -/
theorem IsPerfectCuboid.diag_prod_ed_ne_prime_mul_sq (h : IsPerfectCuboid a b c) {d e g : ℕ}
    (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3) (m : ℕ) :
    (a + d) * (a + e) * (g + d) * (g + e) ≠ p * m ^ 2 :=
  ne_prime_mul_sq_of_isCongruent (h.isCongruent_ed hd he hg) hp h8 m

/-- **`(b+d)(b+f)(g+d)(g+f)` is never `p m²` with `p ≡ 3 (mod 8)` prime.** -/
theorem IsPerfectCuboid.diag_prod_fd_ne_prime_mul_sq (h : IsPerfectCuboid a b c) {d f g : ℕ}
    (hd : d ^ 2 = a ^ 2 + b ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3) (m : ℕ) :
    (b + d) * (b + f) * (g + d) * (g + f) ≠ p * m ^ 2 :=
  ne_prime_mul_sq_of_isCongruent (h.isCongruent_fd hd hf hg) hp h8 m

/-- **`(c+e)(c+f)(g+e)(g+f)` is never `p m²` with `p ≡ 3 (mod 8)` prime.** -/
theorem IsPerfectCuboid.diag_prod_fe_ne_prime_mul_sq (h : IsPerfectCuboid a b c) {e f g : ℕ}
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3) (m : ℕ) :
    (c + e) * (c + f) * (g + e) * (g + f) ≠ p * m ^ 2 :=
  ne_prime_mul_sq_of_isCongruent (h.isCongruent_fe he hf hg) hp h8 m

/-- **`(a+d)(a+e)(g+d)(g+e)` is never `2p m²` with `p ≡ 5 (mod 8)` prime.** -/
theorem IsPerfectCuboid.diag_prod_ed_ne_two_mul_prime_mul_sq (h : IsPerfectCuboid a b c)
    {d e g : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 5) (m : ℕ) :
    (a + d) * (a + e) * (g + d) * (g + e) ≠ 2 * p * m ^ 2 :=
  ne_two_mul_prime_mul_sq_of_isCongruent (h.isCongruent_ed hd he hg) hp h8 m

/-- **`(b+d)(b+f)(g+d)(g+f)` is never `2p m²` with `p ≡ 5 (mod 8)` prime.** -/
theorem IsPerfectCuboid.diag_prod_fd_ne_two_mul_prime_mul_sq (h : IsPerfectCuboid a b c)
    {d f g : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 5) (m : ℕ) :
    (b + d) * (b + f) * (g + d) * (g + f) ≠ 2 * p * m ^ 2 :=
  ne_two_mul_prime_mul_sq_of_isCongruent (h.isCongruent_fd hd hf hg) hp h8 m

/-- **`(c+e)(c+f)(g+e)(g+f)` is never `2p m²` with `p ≡ 5 (mod 8)` prime.** -/
theorem IsPerfectCuboid.diag_prod_fe_ne_two_mul_prime_mul_sq (h : IsPerfectCuboid a b c)
    {e f g : ℕ} (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 5) (m : ℕ) :
    (c + e) * (c + f) * (g + e) * (g + f) ≠ 2 * p * m ^ 2 :=
  ne_two_mul_prime_mul_sq_of_isCongruent (h.isCongruent_fe he hf hg) hp h8 m

/-! ### The gcd form -/

/-- For a Pythagorean triple `p² + q² = r²` with `q` odd, `(r + q) · gcd(p, q) = 2 n²`. -/
theorem pyth_rule_odd {p q r : ℕ} (hp : 0 < p) (hq : Odd q) (h : p ^ 2 + q ^ 2 = r ^ 2) :
    ∃ n : ℕ, (r + q) * Nat.gcd p q = 2 * n ^ 2 := by
  have ht0 : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left q hp
  obtain ⟨p', q', hco, hp', hq'⟩ := Nat.exists_coprime p q
  generalize Nat.gcd p q = t at *
  subst hp' hq'
  have htr : t ∣ r := by
    rw [← Nat.pow_dvd_pow_iff two_ne_zero, ← h]
    exact ⟨p' ^ 2 + q' ^ 2, by ring⟩
  obtain ⟨r', rfl⟩ := htr
  have h' : p' ^ 2 + q' ^ 2 = r' ^ 2 := by
    have : t ^ 2 * (p' ^ 2 + q' ^ 2) = t ^ 2 * r' ^ 2 := by linear_combination h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hp0 : 0 < p' := Nat.pos_of_mul_pos_right hp
  have hr0 : (0 : ℤ) < r' := by
    have : 0 < r' := by
      rcases Nat.eq_zero_or_pos r' with h0 | h0
      · rw [h0] at h'; nlinarith
      · exact h0
    exact_mod_cast this
  have hpt : PythagoreanTriple (p' : ℤ) q' r' := by
    unfold PythagoreanTriple; exact_mod_cast (by nlinarith [h'] : p' * p' + q' * q' = r' * r')
  have hg : Int.gcd (p' : ℤ) q' = 1 := by rw [Int.gcd_natCast_natCast]; exact hco
  have hqo : (q' : ℤ) % 2 = 1 := by
    have : Odd q' := (Nat.odd_mul.mp hq).1
    rw [← Int.odd_iff]; exact_mod_cast this
  obtain ⟨m, n, hq, -, hr, -⟩ := hpt.symm.coprime_classification' (by rwa [Int.gcd_comm]) hqo hr0
  refine ⟨t * m.natAbs, ?_⟩
  zify
  rw [mul_pow, sq_abs]
  linear_combination t ^ 2 * hr + t ^ 2 * hq

/-- **If `a` is the odd edge, `(a,c)(b,e)(a,b)(c,d)` is never `p m²` with `p ≡ 3 (mod 8)`.**
The four triples through `a`, `d`, `e` have odd second leg, so `pyth_rule_odd` gives
`(a+d)(a+e)(g+d)(g+e) · (a,c)(b,e)(a,b)(c,d) = 16 N²`. -/
theorem IsPerfectCuboid.gcd_prod_ed_ne_prime_mul_sq (h : IsPerfectCuboid a b c) (ha : Odd a)
    {d e g : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3) (m : ℕ) :
    a.gcd c * b.gcd e * a.gcd b * c.gcd d ≠ p * m ^ 2 := by
  intro H
  have ha0 := h.pos_a
  have hb0 := h.pos_b
  have hc0 := h.pos_c
  -- `d` and `e` are odd: an odd square plus an odd square is not a square
  have hodd : ∀ {x y z : ℕ}, Odd x → z ^ 2 = x ^ 2 + y ^ 2 → Odd z := by
    intro x y z hx hz
    rcases Nat.even_or_odd z with hze | hzo
    · exfalso
      have hx8 := FermatTriangle.sq_emod_eight_of_odd (by exact_mod_cast hx : Odd (x : ℤ))
      have hz4 := FermatTriangle.sq_emod_four (z : ℤ)
      have hy4 := FermatTriangle.sq_emod_four (y : ℤ)
      have hz' : (z : ℤ) ^ 2 = x ^ 2 + y ^ 2 := by exact_mod_cast hz
      have hze' : (z : ℤ) ^ 2 % 4 = 0 := by
        obtain ⟨k, rfl⟩ := hze
        push_cast; ring_nf; omega
      omega
    · exact hzo
  have hdo : Odd d := hodd ha hd
  have heo : Odd e := hodd ha he
  have hd0 : 0 < d := hdo.pos
  obtain ⟨n₁, h₁⟩ := pyth_rule_odd hb0 ha (by rw [hd]; ring : b ^ 2 + a ^ 2 = d ^ 2)
  obtain ⟨n₂, h₂⟩ := pyth_rule_odd hc0 ha (by rw [he]; ring : c ^ 2 + a ^ 2 = e ^ 2)
  obtain ⟨n₃, h₃⟩ := pyth_rule_odd hc0 hdo (by rw [hd, hg]; ring : c ^ 2 + d ^ 2 = g ^ 2)
  obtain ⟨n₄, h₄⟩ := pyth_rule_odd hb0 heo (by rw [he, hg]; ring : b ^ 2 + e ^ 2 = g ^ 2)
  -- `D · p m² = (4 N)²`
  have key : ((a + d) * (a + e) * (g + d) * (g + e)) * (p * m ^ 2) =
      (4 * (n₁ * n₂ * n₃ * n₄)) ^ 2 := by
    rw [← H, Nat.gcd_comm a c, Nat.gcd_comm a b]
    calc _ = ((d + a) * b.gcd a) * ((e + a) * c.gcd a) * ((g + d) * c.gcd d) *
          ((g + e) * b.gcd e) := by ring
      _ = _ := by rw [h₁, h₂, h₃, h₄]; ring
  have hm : m ≠ 0 := by
    rintro rfl
    have : 0 < a.gcd c * b.gcd e * a.gcd b * c.gcd d := by
      have := Nat.gcd_pos_of_pos_left c ha0; have := Nat.gcd_pos_of_pos_left e hb0
      have := Nat.gcd_pos_of_pos_left b ha0; have := Nat.gcd_pos_of_pos_left d hc0
      positivity
    simp [H] at this
  have hC := h.isCongruent_ed hd he hg
  have hpm : ((p * m : ℕ) : ℚ) ≠ 0 := by
    have := hp.pos
    positivity
  have hN : ((4 * (n₁ * n₂ * n₃ * n₄) : ℕ) : ℚ) ≠ 0 := by
    intro h0
    have hD : (0 : ℚ) < ((a + d) * (a + e) * (g + d) * (g + e) : ℕ) := hC.pos
    have : (((a + d) * (a + e) * (g + d) * (g + e)) * (p * m ^ 2) : ℕ) = (0 : ℚ) := by
      rw [key]; push_cast at h0 ⊢; rw [h0]; ring
    push_cast at this hD
    have : (0 : ℚ) < p * m ^ 2 := by
      have := hp.pos
      positivity
    nlinarith
  have := hC.mul_sq hpm
  rw [show ((p * m : ℕ) : ℚ) ^ 2 * (((a + d) * (a + e) * (g + d) * (g + e) : ℕ) : ℚ) =
      ((4 * (n₁ * n₂ * n₃ * n₄) : ℕ) : ℚ) ^ 2 * p by
    rw [← Nat.cast_pow, ← Nat.cast_pow, ← key]; push_cast; ring,
    isCongruent_mul_sq_iff hN] at this
  exact FermatTriangle.not_isCongruent_prime_three_mod_eight hp h8 this

/-! ### The squarefree part `N` of `abcg/2` -/

/-- The squarefree part `N` of `abcg/2` of a perfect cuboid is neither a prime `p ≡ 3 (mod 8)`
nor `2p` with `p ≡ 5 (mod 8)` prime. -/
theorem IsPerfectCuboid.squarefree_part_ne (h : IsPerfectCuboid a b c) :
    ∃ N : ℕ, Squarefree N ∧ (∃ (g : ℕ) (s : ℚ), g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 ∧
      (a * b * c * g : ℚ) / 2 = N * s ^ 2) ∧
      (∀ p : ℕ, p.Prime → p % 8 = 3 → N ≠ p) ∧
      (∀ p : ℕ, p.Prime → p % 8 = 5 → N ≠ 2 * p) := by
  obtain ⟨N, hsq, g, s, hg, hs, hN, -⟩ := h.isCongruent
  refine ⟨N, hsq, ⟨g, s, hg, hs⟩, fun p hp h8 hNp ↦ ?_, fun p hp h8 hNp ↦ ?_⟩
  · subst hNp
    exact FermatTriangle.not_isCongruent_prime_three_mod_eight hp h8 hN
  · subst hNp
    exact FermatTriangle.not_isCongruent_two_mul_prime_five_mod_eight hp h8 (by exact_mod_cast hN)

end PerfectCuboid
