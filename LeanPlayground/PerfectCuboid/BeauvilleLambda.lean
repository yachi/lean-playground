module

public import LeanPlayground.PerfectCuboid.Basic
public import LeanPlayground.PerfectCuboid.GaussianQuartic
public import Mathlib.NumberTheory.PythagoreanTriples

/-!
# No perfect cuboid has trivial Beauville invariant

Let `a, b, c` be the edges of a perfect cuboid, with face diagonals `d² = a² + b²`,
`e² = a² + c²`, `f² = b² + c²` and space diagonal `g² = a² + b² + c²`. In `ℤ[i]` put `p = a + g`
and `q = b − i c`. Then (`cuboid_identity`)

  `p q (p⁴ − q⁴) · 8 (a+g)(f+b)(e+a)(g+e)(d+a)(g+d) = W²`

for an explicit `W`. It comes from three smaller identities: `q · 2(f+b) = (b + f − ic)²`,
`(p² − q²) · 2(e+a)(g+e) = 2β₂²` and `(p² + q²) · 2(d+a)(g+d) = 2β₃²`. So the point
`ξ = p/q` lies on the twist `B_D : D y² = x⁵ − x` of the genus-two curve `B : y² = x⁵ − x`, where
`D = 8 (a+g)(f+b)(e+a)(g+e)(d+a)(g+d)`.

If `D` is `2^k` times a square, then `p q (p⁴ − q⁴) = V²` or `i V²` (since `2 = −i(1 + i)²`), and
`GaussianQuartic.genus_two` says this forces `p = 0`, `q = 0` or `p⁴ = q⁴`. All three are
impossible for a cuboid: the last one gives `(a + g)² = b² + c² < g²`.

* `IsPerfectCuboid.diag_prod_ne_two_pow_mul_sq`: `(a+g)(f+b)(e+a)(g+e)(d+a)(g+d)` is never
  `2^k m²`.
* `IsPerfectCuboid.gcd_prod_ne_two_pow_mul_sq`: the product of the gcds of the six Pythagorean
  triples, `(a,b)(a,c)(b,c)(a,f)(b,e)(c,d)`, is never `2^k m²`. This is the statement
  "the Beauville invariant `λ` (the odd squarefree part of that product) is never `1`". It
  follows from the first via `pyth_rule`: for a Pythagorean triple `p² + q² = r²`,
  `(r + q) · gcd(p, q)` is `2^j n²`.

Leech's divisibility facts do not rule out `λ = 1` (see the round-5 report), so this is a genuine
new restriction. It removes one square class of perfect cuboids, not all of them.
-/

@[expose] public section

namespace PerfectCuboid

open GaussianQuartic

local notation "G" => GaussianInt

/-- For a Pythagorean triple `p² + q² = r²`, `(r + q) · gcd(p, q)` is `2^j n²`: with
`t = gcd(p, q)` the primitive triple has `r/t + q/t = 2m²` (`q/t` odd) or `(m + n)²`
(`q/t` even). -/
theorem pyth_rule {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (h : p ^ 2 + q ^ 2 = r ^ 2) :
    ∃ j n : ℕ, (r + q) * Nat.gcd p q = 2 ^ j * n ^ 2 := by
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
  rcases hpt.even_odd_of_coprime hg with ⟨-, hqo⟩ | ⟨hpo, -⟩
  · obtain ⟨m, n, hq, -, hr, -⟩ := hpt.symm.coprime_classification' (by rwa [Int.gcd_comm]) hqo hr0
    refine ⟨1, t * m.natAbs, ?_⟩
    zify
    rw [mul_pow, sq_abs]
    linear_combination t ^ 2 * hr + t ^ 2 * hq
  · obtain ⟨m, n, -, hq, hr, -⟩ := hpt.coprime_classification' hg hpo hr0
    refine ⟨0, t * (m + n).natAbs, ?_⟩
    zify
    rw [mul_pow, sq_abs]
    linear_combination t ^ 2 * hr + t ^ 2 * hq

/-- If `P · 2ⁿ N² = W²` in `ℤ[i]` then `P` is a square or `i` times a square (`2 = −i(1 + i)²`). -/
theorem sq_or_ι_sq {P W N : G} {n : ℕ} (hN : N ≠ 0) (h : P * (2 ^ n * N ^ 2) = W ^ 2) :
    ∃ V, P = 1 * V ^ 2 ∨ P = ι * V ^ 2 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hne : (2 : G) ^ j * N ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hN
    obtain ⟨V, hV⟩ := exists_sq_of_mul hne (by linear_combination h : (2 ^ j * N) ^ 2 * P = W ^ 2)
    exact ⟨V, Or.inl (by rw [hV, one_mul])⟩
  · have hne : (2 : G) ^ j * N ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hN
    obtain ⟨V₀, hV₀⟩ := exists_sq_of_mul hne
      (by linear_combination h : (2 ^ j * N) ^ 2 * (2 * P) = W ^ 2)
    obtain ⟨V, rfl⟩ : ω ∣ V₀ := prime_ω.dvd_of_dvd_pow (n := 2)
      ⟨-ι * ω * P, by linear_combination -hV₀ + P * two_eq⟩
    refine ⟨V, Or.inr (mul_left_cancel₀ (pow_ne_zero 2 ω_ne_zero) ?_)⟩
    linear_combination P * ω_sq + ι * hV₀

/-- The triple `(b, c, f)`: `q · 2(f+b) = (b + f − ic)²` with `q = b − ic`. -/
theorem hypleg_f {b c f : G} (hf : f ^ 2 = b ^ 2 + c ^ 2) :
    (b - ι * c) * (2 * (f + b)) = (b + f - ι * c) ^ 2 := by
  linear_combination (-1) * hf + (-c ^ 2) * ι_sq

/-- The triples `(a, c, e)` and `(b, e, g)`: `(p² − q²) · 2(e+a)(g+e)` is twice a square. -/
theorem hypleg_e {a b c e g : G} (he : e ^ 2 = a ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    ((a + g) ^ 2 - (b - ι * c) ^ 2) * (2 * (e + a) * (g + e)) =
      2 * (a ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e) ^ 2 := by
  linear_combination (-2 * (b - c * ι) ^ 2) * he + (2 * (a + e) * (a + g)) * hg +
    (-2 * c ^ 2 * (a ^ 2 + a * e + a * g + b ^ 2 + c ^ 2 + e * g)) * ι_sq

/-- The triples `(a, b, d)` and `(c, d, g)`: `(p² + q²) · 2(d+a)(g+d)` is twice a square. -/
theorem hypleg_d {a b c d g : G} (hd : d ^ 2 = a ^ 2 + b ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    ((a + g) ^ 2 + (b - ι * c) ^ 2) * (2 * (d + a) * (g + d)) =
      2 * (a ^ 2 + a * g + b ^ 2 - ι * b * c + (a + g) * d) ^ 2 := by
  linear_combination (2 * (b - c * ι) ^ 2) * hd + (2 * (a + d) * (a + g)) * hg +
    (2 * c ^ 2 * (a + d) * (a + g)) * ι_sq

/-- The key identity: with `p = a + g`, `q = b - i c`,
`p q (p⁴ - q⁴) · 8 (g+a)(f+b)(e+a)(g+e)(d+a)(g+d)` is a square in `ℤ[i]`. -/
theorem cuboid_identity {a b c d e f g : G} (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    (a + g) * (b - ι * c) * ((a + g) ^ 4 - (b - ι * c) ^ 4) *
        (8 * ((a + g) * (f + b) * (e + a) * (g + e) * (d + a) * (g + d))) =
      (2 * (a + g) * (b + f - ι * c) * (a ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e) *
        (a ^ 2 + a * g + b ^ 2 - ι * b * c + (a + g) * d)) ^ 2 := by
  have J1 := hypleg_f (c := c) hf
  have J2 := hypleg_e (b := b) he hg
  have J3 := hypleg_d (c := c) hd hg
  calc _ = ((a + g) * (a + g)) * ((b - ι * c) * (2 * (f + b))) *
        ((((a + g) ^ 2 - (b - ι * c) ^ 2) * (2 * (e + a) * (g + e)))) *
        ((((a + g) ^ 2 + (b - ι * c) ^ 2) * (2 * (d + a) * (g + d)))) := by
        generalize a + g = p; generalize b - ι * c = q; ring
    _ = _ := by
        rw [J1, J2, J3]
        generalize a + g = p
        generalize b + f - ι * c = r
        generalize a ^ 2 + a * g + c ^ 2 + ι * b * c + p * e = s
        generalize a ^ 2 + a * g + b ^ 2 - ι * b * c + p * d = t
        ring

/-- `N(x⁴) = N(x)⁴`. -/
theorem norm_pow_four (x : G) : (x ^ 4).norm = x.norm ^ 4 := by
  simp only [pow_succ, pow_zero, one_mul, Zsqrtd.norm_mul]

/-- For a cuboid, `p = a + g` and `q = b − i c` are nonzero and `p⁴ ≠ q⁴`. -/
theorem cuboid_contra {a b c g : ℕ} (ha : 0 < a) (hb : 0 < b) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2)
    (h : (a + g : G) = 0 ∨ (b - ι * c : G) = 0 ∨ (a + g : G) ^ 4 = (b - ι * c : G) ^ 4) :
    False := by
  rcases h with h | h | h
  · have := congrArg Zsqrtd.re h
    simp at this; omega
  · have := congrArg Zsqrtd.re h
    simp [ι] at this; omega
  · have := congrArg Zsqrtd.norm h
    rw [norm_pow_four, norm_pow_four] at this
    have hp : (a + g : G).norm = ((a : ℤ) + g) ^ 2 := by simp [Zsqrtd.norm]; ring
    have hq : (b - ι * c : G).norm = (b : ℤ) ^ 2 + (c : ℤ) ^ 2 := by simp [Zsqrtd.norm, ι]; ring
    rw [hp, hq] at this
    have e := (pow_left_inj₀ (by positivity) (by positivity) four_ne_zero).1 this
    have hg' : (g : ℤ) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by exact_mod_cast hg
    have : (0 : ℤ) < a := by exact_mod_cast ha
    nlinarith [(Nat.cast_nonneg g : (0 : ℤ) ≤ g)]

/-- **No perfect cuboid has trivial Beauville invariant** (core form): for a perfect cuboid with
face diagonals `d, e, f` and space diagonal `g`, the product
`(a+g)(f+b)(e+a)(g+e)(d+a)(g+d)` times `2^k m²` is never `2^J N²`. -/
theorem perfectCuboid_core {a b c d e f g : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) {k J m N : ℕ} (hm : m ≠ 0)
    (H : (a + g) * (f + b) * (e + a) * (g + e) * (d + a) * (g + d) * (2 ^ k * m ^ 2) =
      2 ^ J * N ^ 2) : False := by
  have hg0 : 0 < g := by rcases Nat.eq_zero_or_pos g with rfl | h; · nlinarith
                         exact h
  have he0 : 0 < e := by rcases Nat.eq_zero_or_pos e with rfl | h; · nlinarith
                         exact h
  have hd0 : 0 < d := by rcases Nat.eq_zero_or_pos d with rfl | h; · nlinarith
                         exact h
  have hN : N ≠ 0 := by
    rintro rfl
    have : 0 < (a + g) * (f + b) * (e + a) * (g + e) * (d + a) * (g + d) * (2 ^ k * m ^ 2) := by
      positivity
    simp [H] at this
  have HG : ((a : G) + g) * (f + b) * (e + a) * (g + e) * (d + a) * (g + d) *
      (2 ^ k * (m : G) ^ 2) =
      2 ^ J * (N : G) ^ 2 := by exact_mod_cast H
  have I := cuboid_identity (a := (a : G)) (b := b) (c := c) (d := d) (e := e) (f := f) (g := g)
    (by exact_mod_cast hd) (by exact_mod_cast he) (by exact_mod_cast hf) (by exact_mod_cast hg)
  generalize hP : ((a : G) + g) * (b - ι * c) * ((a + g) ^ 4 - (b - ι * c) ^ 4) = P at I
  generalize 2 * ((a : G) + g) * (b + f - ι * c) *
    (a ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e) *
    (a ^ 2 + a * g + b ^ 2 - ι * b * c + (a + g) * d) = W at I
  generalize ((a : G) + g) * (f + b) * (e + a) * (g + e) * (d + a) * (g + d) = Q at I HG
  have key : P * (2 ^ (J + k + 3) * (N : G) ^ 2) = (W * 2 ^ k * m) ^ 2 := by
    linear_combination (2 ^ k * (m : G)) ^ 2 * I - (P * 8 * 2 ^ k) * HG
  have hNG : (N : G) ≠ 0 := by exact_mod_cast hN
  obtain ⟨V, hV | hV⟩ := sq_or_ι_sq hNG key
  · rw [← hP] at hV; exact cuboid_contra ha hb hg (genus_two isUnit_one hV)
  · rw [← hP] at hV; exact cuboid_contra ha hb hg (genus_two isUnit_ι hV)

/-- `(a+g)(f+b)(e+a)(g+e)(d+a)(g+d)` is never `2^k m²` for a perfect cuboid. -/
theorem IsPerfectCuboid.diag_prod_ne_two_pow_mul_sq {a b c : ℕ} (h : IsPerfectCuboid a b c)
    {d e f g : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hf : f ^ 2 = b ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) (k m : ℕ) :
    (a + g) * (f + b) * (e + a) * (g + e) * (d + a) * (g + d) ≠ 2 ^ k * m ^ 2 := by
  intro H
  exact perfectCuboid_core h.pos_a h.pos_b hd he hf hg (k := 0) (m := 1) (J := k) (N := m)
    one_ne_zero
    (by rw [H]; ring)

/-- **No perfect cuboid has `λ = 1`.** The product of the gcds of the six Pythagorean triples
`(a, b, d)`, `(a, c, e)`, `(b, c, f)`, `(a, f, g)`, `(b, e, g)`, `(c, d, g)` of a perfect cuboid is
never `2^k m²`. -/
theorem IsPerfectCuboid.gcd_prod_ne_two_pow_mul_sq {a b c : ℕ} (h : IsPerfectCuboid a b c)
    {d e f g : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hf : f ^ 2 = b ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) (k m : ℕ) :
    a.gcd b * a.gcd c * b.gcd c * a.gcd f * b.gcd e * c.gcd d ≠ 2 ^ k * m ^ 2 := by
  intro H
  have ha := h.pos_a
  have hb := h.pos_b
  have hc := h.pos_c
  have hd0 : 0 < d := by rcases Nat.eq_zero_or_pos d with rfl | h; · nlinarith
                         exact h
  have he0 : 0 < e := by rcases Nat.eq_zero_or_pos e with rfl | h; · nlinarith
                         exact h
  have hf0 : 0 < f := by rcases Nat.eq_zero_or_pos f with rfl | h; · nlinarith
                         exact h
  have hm : m ≠ 0 := by
    rintro rfl
    have : 0 < a.gcd b * a.gcd c * b.gcd c * a.gcd f * b.gcd e * c.gcd d := by
      have := Nat.gcd_pos_of_pos_left b ha; have := Nat.gcd_pos_of_pos_left c ha
      have := Nat.gcd_pos_of_pos_left c hb; have := Nat.gcd_pos_of_pos_left f ha
      have := Nat.gcd_pos_of_pos_left e hb; have := Nat.gcd_pos_of_pos_left d hc
      positivity
    simp [H] at this
  obtain ⟨j₁, n₁, h₁⟩ := pyth_rule hf0 ha (by rw [hf, hg]; ring : f ^ 2 + a ^ 2 = g ^ 2)
  obtain ⟨j₂, n₂, h₂⟩ := pyth_rule hc hb (by rw [hf]; ring : c ^ 2 + b ^ 2 = f ^ 2)
  obtain ⟨j₃, n₃, h₃⟩ := pyth_rule hc ha (by rw [he]; ring : c ^ 2 + a ^ 2 = e ^ 2)
  obtain ⟨j₄, n₄, h₄⟩ := pyth_rule hb he0 (by rw [he, hg]; ring : b ^ 2 + e ^ 2 = g ^ 2)
  obtain ⟨j₅, n₅, h₅⟩ := pyth_rule hb ha (by rw [hd]; ring : b ^ 2 + a ^ 2 = d ^ 2)
  obtain ⟨j₆, n₆, h₆⟩ := pyth_rule hc hd0 (by rw [hd, hg]; ring : c ^ 2 + d ^ 2 = g ^ 2)
  refine perfectCuboid_core ha hb hd he hf hg (k := k) (m := m)
    (J := j₁ + j₂ + j₃ + j₄ + j₅ + j₆) (N := n₁ * n₂ * n₃ * n₄ * n₅ * n₆) hm ?_
  rw [← H, Nat.gcd_comm a f, Nat.gcd_comm b c, Nat.gcd_comm a c, Nat.gcd_comm a b]
  calc _ = ((g + a) * f.gcd a) * ((f + b) * c.gcd b) * ((e + a) * c.gcd a) *
        ((g + e) * b.gcd e) * ((d + a) * b.gcd a) * ((g + d) * c.gcd d) := by ring
    _ = _ := by rw [h₁, h₂, h₃, h₄, h₅, h₆]; ring

end PerfectCuboid
