module

public import LeanPlayground.PerfectCuboid.BeauvilleLambda

/-!
# Three more square classes of perfect cuboids

For a perfect cuboid put `ξ = p/q` with `p = a + g`, `q = b − i c` in `ℤ[i]` (as in
`BeauvilleLambda.lean`). The three hyp+leg identities `hypleg_f`, `hypleg_e`, `hypleg_d` give the
square classes of `2ξ`, `ξ² − 1` and `ξ² + 1` in `ℚ(i)*/ℚ(i)*²`:

  `2ξ ≡ (a+g)(f+b)`,  `ξ² − 1 ≡ (e+a)(g+e)`,  `ξ² + 1 ≡ (d+a)(g+d)`.

These are the twist classes `(d₁, d₂, d₃)` of the curve `X(8)` that the cuboid lies on (Stoll–Testa,
arXiv:1009.0388, §4). Its Jacobian splits into three `j = 1728` curves, twisted by `d₁d₂`, `d₁d₃`
and `d₂d₃`, and the genus-two Jacobian twisted by `d₁d₂d₃` (`BeauvilleLambda.lean` handles that
one). This file handles the other three: if one of the twists is trivial, the corresponding
`ℚ(i)`-point lives on an untwisted curve that has only torsion points, and those come from
degenerate cuboids.

* `GaussianQuartic.quartic_plus`: `X⁴ + Y⁴ = u w²` (`u` a unit) forces `X = 0`, `Y = 0`, `w = 0`
  or `X⁴ = Y⁴`. The case `u = ±i` has the solution `(1, 1, 1 − i)`, so `X⁴ = Y⁴` cannot be
  dropped. Proof: `(X⁴ − Y⁴)⁴ − (2XYw)⁴ = (X⁸ + 6X⁴Y⁴ + Y⁸)²` reduces it to `quartic_one`.
* `GaussianQuartic.cn_gauss`: `p q (p² − q²) = u V²` forces `p = 0`, `q = 0` or `p⁴ = q⁴`. That
  is, `1` and `i` are not congruent numbers over `ℚ(i)`: `y² = x³ − x` and its twist by `i`,
  `y² = x³ + x`, have only torsion points over `ℚ(i)`.

Writing `μ₁, μ₂, μ₃` for the odd squarefree parts of the gcd products of the two Pythagorean
triples through `f`, `e`, `d`, the cuboid theorems say `μ₁, μ₂, μ₃` are pairwise distinct:

* `IsPerfectCuboid.gcd_prod_ed_ne_two_pow_mul_sq`: `(a,c)(b,e)(a,b)(c,d)` is never `2^k m²`
  (`μ₂ ≠ μ₃`; twist `ξ⁴ − 1`). This is the global, fiber-free form of Cipollini's
  "infinity class" (arXiv:2609.14526, §2).
* `IsPerfectCuboid.gcd_prod_fe_ne_two_pow_mul_sq`: `(a,f)(b,c)(a,c)(b,e)` is never `2^k m²`
  (`μ₁ ≠ μ₂`; twist `ξ(ξ² − 1)`).
* `IsPerfectCuboid.gcd_prod_fd_ne_two_pow_mul_sq`: `(a,f)(b,c)(a,b)(c,d)` is never `2^k m²`
  (`μ₁ ≠ μ₃`; twist `ξ(ξ² + 1)`).

Like `λ ≠ 1`, each removes one square class of perfect cuboids, not all of them. See
`fable-new-frameworks-round6.md` (round 6, framework F2).

Scope: each of the three proofs uses only positivity and three of the four diagonal equations
(`identity_ed` needs `d, e, g`; `identity_fe` needs `e, f, g`; `identity_fd` needs `d, f, g`). So
each inequality holds for every *body cuboid* with the corresponding two face diagonals and the
space diagonal integral, and body cuboids exist in infinite families. The same holds for the
congruent-number form in `CongruentCharacters.lean`.
-/

@[expose] public section

namespace PerfectCuboid

open GaussianQuartic

local notation "G" => GaussianInt

namespace GaussianQuartic

/-- `X⁴ + Y⁴ = i w²` forces `X = 0`, `Y = 0`, `w = 0` or `X⁴ = Y⁴`. -/
theorem quartic_plus_i {X Y w : G} (hX : X ≠ 0) (hY : Y ≠ 0) (hw : w ≠ 0) (hXY : X ^ 4 ≠ Y ^ 4)
    (h : X ^ 4 + Y ^ 4 = ι * w ^ 2) : False := by
  have hw4 : w ^ 4 = -(X ^ 4 + Y ^ 4) ^ 2 := by
    linear_combination (X ^ 4 + Y ^ 4 + ι * w ^ 2) * h + w ^ 4 * ι_sq
  have e : (X ^ 4 - Y ^ 4) ^ 4 + -1 * (2 * X * Y * w) ^ 4 =
      ((X ^ 4) ^ 2 + 6 * X ^ 4 * Y ^ 4 + (Y ^ 4) ^ 2) ^ 2 := by
    linear_combination (-16 * X ^ 4 * Y ^ 4) * hw4
  have hz : (X ^ 4) ^ 2 + 6 * X ^ 4 * Y ^ 4 + (Y ^ 4) ^ 2 ≠ 0 := by
    intro h0
    -- `(X⁴ + 3Y⁴)² = 8 Y⁸ = −i (2ωY⁴)²`, and `−i` is not a square
    rcases unit_sq_of_sq (u := -ι) (W := 2 * ω * Y ^ 4) (Y := X ^ 4 + 3 * Y ^ 4) isUnit_ι.neg
      (mul_ne_zero (mul_ne_zero two_ne_zero ω_ne_zero) (pow_ne_zero 4 hY))
      (by linear_combination -h0 - 4 * ι * (Y ^ 4) ^ 2 * ω_sq - 8 * (Y ^ 4) ^ 2 * ι_sq)
      with h1 | h1 <;> simp [ι, Zsqrtd.ext_iff] at h1
  exact quartic_one (-1) (Or.inr rfl) (sub_ne_zero.2 hXY)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hX) hY) hw) hz e

/-- `X⁴ + Y⁴ = u w²` (`u` a unit) forces `X = 0`, `Y = 0`, `w = 0` or `X⁴ = Y⁴`. The last case
occurs: `1 + 1 = i (1 − i)²`. -/
theorem quartic_plus {u X Y w : G} (hu : IsUnit u) (h : X ^ 4 + Y ^ 4 = u * w ^ 2) :
    X = 0 ∨ Y = 0 ∨ w = 0 ∨ X ^ 4 = Y ^ 4 := by
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hX, hY, hw, hXY⟩ := hne
  have hιw : ι * w ≠ 0 := mul_ne_zero isUnit_ι.ne_zero hw
  rcases (isUnit_iff u).1 hu with rfl | rfl | rfl | rfl
  · exact quartic_one 1 (Or.inl rfl) hX hY hw (by linear_combination h)
  · exact quartic_one 1 (Or.inl rfl) hX hY hιw (by linear_combination h - w ^ 2 * ι_sq)
  · exact quartic_plus_i hX hY hw hXY h
  · exact quartic_plus_i hX hY hιw hXY (by linear_combination h - ι * w ^ 2 * ι_sq)

/-- `p q (p² − q²) = u V²` (`u` a unit) forces `p = 0`, `q = 0` or `p⁴ = q⁴`: the congruent-number
curves `y² = x³ − x` and `y² = x³ + x` have only their torsion points over `ℚ(i)`. -/
theorem cn_gauss {u p q V : G} (hu : IsUnit u) (h : p * q * (p ^ 2 - q ^ 2) = u * V ^ 2) :
    p = 0 ∨ q = 0 ∨ p ^ 4 = q ^ 4 := by
  by_cases hq : q = 0
  · exact Or.inr (Or.inl hq)
  obtain ⟨g, p, q, hg, rfl, rfl, hc⟩ := exists_coprime p q hq
  suffices H : p = 0 ∨ q = 0 ∨ p ^ 4 = q ^ 4 by
    rcases H with H | H | H
    · left; rw [H, mul_zero]
    · right; left; rw [H, mul_zero]
    · right; right; rw [mul_pow, mul_pow, H]
  have hd : (g ^ 2) ^ 2 ∣ V ^ 2 := by
    rw [← hu.dvd_mul_left]
    exact ⟨p * q * (p ^ 2 - q ^ 2), by rw [← h]; ring⟩
  obtain ⟨V, rfl⟩ := dvd_of_sq_dvd_sq hd
  have h' : p * (q * (p ^ 2 - q ^ 2)) = u * V ^ 2 :=
    mul_left_cancel₀ (pow_ne_zero 4 hg) (by linear_combination h)
  have hpr : IsCoprime p (p ^ 2 - q ^ 2) := by
    have := ((hc.pow_right (n := 2)).neg_right).add_mul_left_right p
    convert this using 1; ring
  have hqr : IsCoprime q (p ^ 2 - q ^ 2) := by
    have := (hc.symm.pow_right (n := 2)).add_mul_left_right (-q)
    convert this using 1; ring
  obtain ⟨η₁, s, hη₁, hp⟩ := pow_split (hc.mul_right hpr) hu h'
  obtain ⟨η₂, t, hη₂, hq⟩ := pow_split (hc.symm.mul_right hqr) hu
    (by linear_combination h' : q * (p * (p ^ 2 - q ^ 2)) = u * V ^ 2)
  obtain ⟨η₃, w, hη₃, hr⟩ := pow_split (hpr.symm.mul_right hqr.symm) hu
    (by linear_combination h' : (p ^ 2 - q ^ 2) * (p * q) = u * V ^ 2)
  have hp4 : p ^ 4 = (s ^ 4) ^ 2 := by rw [hp, mul_pow, unit_pow_four hη₁]; ring
  have hq4 : q ^ 4 = (t ^ 4) ^ 2 := by rw [hq, mul_pow, unit_pow_four hη₂]; ring
  have hp0 : s = 0 → p = 0 := fun h0 => by rw [hp, h0]; ring
  have hq0 : t = 0 → q = 0 := fun h0 => by rw [hq, h0]; ring
  have hw0 : w = 0 → p ^ 4 = q ^ 4 := fun h0 => by
    have e : p ^ 2 = q ^ 2 := by linear_combination hr + η₃ * (w + 0) * h0
    rw [show p ^ 4 = (p ^ 2) ^ 2 by ring, e]; ring
  -- `η₁² s⁴ − η₂² t⁴ = η₃ w²` with `η₁², η₂² = ±1`
  have hr' : η₁ ^ 2 * s ^ 4 - η₂ ^ 2 * t ^ 4 = η₃ * w ^ 2 := by
    rw [← hr, hp, hq]; ring
  rcases unit_sq hη₁ with e₁ | e₁ <;> rcases unit_sq hη₂ with e₂ | e₂ <;> rw [e₁, e₂] at hr'
  · rcases quartic (X := s) (Y := t) (w := w) hη₃ (by linear_combination hr') with h0 | h0 | h0
    exacts [Or.inl (hp0 h0), Or.inr (Or.inl (hq0 h0)), Or.inr (Or.inr (hw0 h0))]
  · rcases quartic_plus (X := s) (Y := t) (w := w) hη₃ (by linear_combination hr')
      with h0 | h0 | h0 | h0
    exacts [Or.inl (hp0 h0), Or.inr (Or.inl (hq0 h0)), Or.inr (Or.inr (hw0 h0)),
      Or.inr (Or.inr (by rw [hp4, hq4, h0]))]
  · rcases quartic_plus (X := s) (Y := t) (w := w) hη₃.neg (by linear_combination -hr')
      with h0 | h0 | h0 | h0
    exacts [Or.inl (hp0 h0), Or.inr (Or.inl (hq0 h0)), Or.inr (Or.inr (hw0 h0)),
      Or.inr (Or.inr (by rw [hp4, hq4, h0]))]
  · rcases quartic (X := t) (Y := s) (w := w) hη₃ (by linear_combination hr')
      with h0 | h0 | h0
    exacts [Or.inr (Or.inl (hq0 h0)), Or.inl (hp0 h0), Or.inr (Or.inr (hw0 h0))]

end GaussianQuartic

/-! ### The three character identities -/

section Identities

variable {a b c d e f g : G}

/-- `{v, w}`: `(p⁴ − q⁴) · 4 (e+a)(g+e)(d+a)(g+d)` is a square. -/
theorem identity_ed (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    ((a + g) ^ 4 - (b - ι * c) ^ 4) * (2 ^ 2 * ((e + a) * (g + e) * (d + a) * (g + d))) =
      (2 * (a ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e) *
        (a ^ 2 + a * g + b ^ 2 - ι * b * c + (a + g) * d)) ^ 2 := by
  calc _ = (((a + g) ^ 2 - (b - ι * c) ^ 2) * (2 * (e + a) * (g + e))) *
        (((a + g) ^ 2 + (b - ι * c) ^ 2) * (2 * (d + a) * (g + d))) := by
        generalize a + g = p; generalize b - ι * c = q; ring
    _ = _ := by
        rw [hypleg_e he hg, hypleg_d hd hg]
        generalize a ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e = s
        generalize a ^ 2 + a * g + b ^ 2 - ι * b * c + (a + g) * d = t
        ring

/-- `{u, v}`: `p q (p² − q²) · 8 (a+g)(f+b)(e+a)(g+e)` is a square. -/
theorem identity_fe (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    (a + g) * (b - ι * c) * ((a + g) ^ 2 - (b - ι * c) ^ 2) *
        (2 ^ 3 * ((a + g) * (f + b) * (e + a) * (g + e))) =
      (2 * (a + g) * (b + f - ι * c) * (a ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e)) ^ 2 := by
  calc _ = 2 * ((a + g) * (a + g)) * ((b - ι * c) * (2 * (f + b))) *
        (((a + g) ^ 2 - (b - ι * c) ^ 2) * (2 * (e + a) * (g + e))) := by
        generalize a + g = p; generalize b - ι * c = q; ring
    _ = _ := by
        rw [hypleg_f hf, hypleg_e he hg]
        generalize a + g = p
        generalize b + f - ι * c = r
        generalize a ^ 2 + a * g + c ^ 2 + ι * b * c + p * e = s
        ring

/-- `{u, w}`: `p q (p² + q²) · 8 (a+g)(f+b)(d+a)(g+d)` is a square. -/
theorem identity_fd (hd : d ^ 2 = a ^ 2 + b ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    (a + g) * (b - ι * c) * ((a + g) ^ 2 + (b - ι * c) ^ 2) *
        (2 ^ 3 * ((a + g) * (f + b) * (d + a) * (g + d))) =
      (2 * (a + g) * (b + f - ι * c) * (a ^ 2 + a * g + b ^ 2 - ι * b * c + (a + g) * d)) ^ 2 := by
  calc _ = 2 * ((a + g) * (a + g)) * ((b - ι * c) * (2 * (f + b))) *
        (((a + g) ^ 2 + (b - ι * c) ^ 2) * (2 * (d + a) * (g + d))) := by
        generalize a + g = p; generalize b - ι * c = q; ring
    _ = _ := by
        rw [hypleg_f hf, hypleg_d hd hg]
        generalize a + g = p
        generalize b + f - ι * c = r
        generalize a ^ 2 + a * g + b ^ 2 - ι * b * c + p * d = t
        ring

end Identities

/-- If `P · 2^c Q` is a square and `Q · 2^k m²` is `2^J N²`, then `P` is a unit times a square. -/
theorem unit_mul_sq_of {P Q W m N : G} {c k J : ℕ} (hN : N ≠ 0) (I : P * (2 ^ c * Q) = W ^ 2)
    (HG : Q * (2 ^ k * m ^ 2) = 2 ^ J * N ^ 2) : ∃ u V, IsUnit u ∧ P = u * V ^ 2 := by
  have key : P * (2 ^ (J + k + c) * N ^ 2) = (W * 2 ^ k * m) ^ 2 := by
    linear_combination (2 ^ k * m) ^ 2 * I - (P * 2 ^ c * 2 ^ k) * HG
  obtain ⟨V, hV | hV⟩ := sq_or_ι_sq hN key
  exacts [⟨1, V, isUnit_one, hV⟩, ⟨ι, V, isUnit_ι, hV⟩]

/-! ### The three square classes -/

/-- `{v, w}` core form: `(e+a)(g+e)(d+a)(g+d) · 2^k m²` is never `2^J N²`. -/
theorem core_ed {a b c d e g : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) {k J m N : ℕ}
    (H : (e + a) * (g + e) * (d + a) * (g + d) * (2 ^ k * m ^ 2) = 2 ^ J * N ^ 2)
    (hm : m ≠ 0) : False := by
  have hg0 : 0 < g := by rcases Nat.eq_zero_or_pos g with rfl | h; · nlinarith
                         exact h
  have hN : N ≠ 0 := by
    rintro rfl
    have : 0 < (e + a) * (g + e) * (d + a) * (g + d) * (2 ^ k * m ^ 2) := by positivity
    simp [H] at this
  have HG : ((e : G) + a) * (g + e) * (d + a) * (g + d) * (2 ^ k * (m : G) ^ 2) =
      2 ^ J * (N : G) ^ 2 := by exact_mod_cast H
  have I := identity_ed (a := (a : G)) (b := b) (c := c) (d := d) (e := e) (g := g)
    (by exact_mod_cast hd) (by exact_mod_cast he) (by exact_mod_cast hg)
  obtain ⟨u, V, hu, hV⟩ := unit_mul_sq_of (by exact_mod_cast hN) I HG
  rcases quartic hu hV with h0 | h0 | h0
  · exact cuboid_contra ha hb hg (Or.inl h0)
  · exact cuboid_contra ha hb hg (Or.inr (Or.inl h0))
  · rw [h0, sq, zero_mul, mul_zero, sub_eq_zero] at hV
    exact cuboid_contra ha hb hg (Or.inr (Or.inr hV))

/-- `{u, v}` core form: `(a+g)(f+b)(e+a)(g+e) · 2^k m²` is never `2^J N²`. -/
theorem core_fe {a b c e f g : ℕ} (ha : 0 < a) (hb : 0 < b) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hf : f ^ 2 = b ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) {k J m N : ℕ}
    (H : (a + g) * (f + b) * (e + a) * (g + e) * (2 ^ k * m ^ 2) = 2 ^ J * N ^ 2)
    (hm : m ≠ 0) : False := by
  have hg0 : 0 < g := by rcases Nat.eq_zero_or_pos g with rfl | h; · nlinarith
                         exact h
  have hN : N ≠ 0 := by
    rintro rfl
    have : 0 < (a + g) * (f + b) * (e + a) * (g + e) * (2 ^ k * m ^ 2) := by positivity
    simp [H] at this
  have HG : ((a : G) + g) * (f + b) * (e + a) * (g + e) * (2 ^ k * (m : G) ^ 2) =
      2 ^ J * (N : G) ^ 2 := by exact_mod_cast H
  have I := identity_fe (a := (a : G)) (b := b) (c := c) (e := e) (f := f) (g := g)
    (by exact_mod_cast he) (by exact_mod_cast hf) (by exact_mod_cast hg)
  obtain ⟨u, V, hu, hV⟩ := unit_mul_sq_of (by exact_mod_cast hN) I HG
  exact cuboid_contra ha hb hg (cn_gauss hu hV)

/-- `{u, w}` core form: `(a+g)(f+b)(d+a)(g+d) · 2^k m²` is never `2^J N²`. -/
theorem core_fd {a b c d f g : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (hf : f ^ 2 = b ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) {k J m N : ℕ}
    (H : (a + g) * (f + b) * (d + a) * (g + d) * (2 ^ k * m ^ 2) = 2 ^ J * N ^ 2)
    (hm : m ≠ 0) : False := by
  have hg0 : 0 < g := by rcases Nat.eq_zero_or_pos g with rfl | h; · nlinarith
                         exact h
  have hN : N ≠ 0 := by
    rintro rfl
    have : 0 < (a + g) * (f + b) * (d + a) * (g + d) * (2 ^ k * m ^ 2) := by positivity
    simp [H] at this
  have HG : ((a : G) + g) * (f + b) * (d + a) * (g + d) * (2 ^ k * (m : G) ^ 2) =
      2 ^ J * (N : G) ^ 2 := by exact_mod_cast H
  have I := identity_fd (a := (a : G)) (b := b) (c := c) (d := d) (f := f) (g := g)
    (by exact_mod_cast hd) (by exact_mod_cast hf) (by exact_mod_cast hg)
  obtain ⟨u, V, hu, hV⟩ := unit_mul_sq_of (by exact_mod_cast hN) I HG
  -- with `q' = i q`: `p q' (p² − q'²) = i · p q (p² + q²)`
  have hV' : ((a : G) + g) * (ι * (b - ι * c)) * ((a + g) ^ 2 - (ι * (b - ι * c)) ^ 2) =
      (ι * u) * V ^ 2 := by
    linear_combination ι * hV - ((a : G) + g) * ι * (b - ι * c) ^ 3 * ι_sq
  rcases cn_gauss (isUnit_ι.mul hu) hV' with h0 | h0 | h0
  · exact cuboid_contra ha hb hg (Or.inl h0)
  · exact cuboid_contra ha hb hg
      (Or.inr (Or.inl ((mul_eq_zero.1 h0).resolve_left isUnit_ι.ne_zero)))
  · refine cuboid_contra ha hb hg (Or.inr (Or.inr ?_))
    rw [h0, mul_pow, unit_pow_four isUnit_ι, one_mul]

/-- **`μ₂ ≠ μ₃`.** For a perfect cuboid, `(a,c)(b,e)(a,b)(c,d)` — the gcds of the triples
`(a, c, e)`, `(b, e, g)`, `(a, b, d)`, `(c, d, g)` — is never `2^k m²`. This is the global form
of Cipollini's infinity class: the point `ξ` would lie on `y² = x³ − x` over `ℚ(i)`.
The proof uses only two face diagonals and `g`, so it holds for every body cuboid. -/
theorem IsPerfectCuboid.gcd_prod_ed_ne_two_pow_mul_sq {a b c : ℕ} (h : IsPerfectCuboid a b c)
    {d e g : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) (k m : ℕ) :
    a.gcd c * b.gcd e * a.gcd b * c.gcd d ≠ 2 ^ k * m ^ 2 := by
  intro H
  have ha := h.pos_a
  have hb := h.pos_b
  have hc := h.pos_c
  have hd0 : 0 < d := by rcases Nat.eq_zero_or_pos d with rfl | h; · nlinarith
                         exact h
  have he0 : 0 < e := by rcases Nat.eq_zero_or_pos e with rfl | h; · nlinarith
                         exact h
  have hm : m ≠ 0 := by
    rintro rfl
    have : 0 < a.gcd c * b.gcd e * a.gcd b * c.gcd d := by
      have := Nat.gcd_pos_of_pos_left c ha; have := Nat.gcd_pos_of_pos_left e hb
      have := Nat.gcd_pos_of_pos_left b ha; have := Nat.gcd_pos_of_pos_left d hc
      positivity
    simp [H] at this
  obtain ⟨j₃, n₃, h₃⟩ := pyth_rule hc ha (by rw [he]; ring : c ^ 2 + a ^ 2 = e ^ 2)
  obtain ⟨j₄, n₄, h₄⟩ := pyth_rule hb he0 (by rw [he, hg]; ring : b ^ 2 + e ^ 2 = g ^ 2)
  obtain ⟨j₅, n₅, h₅⟩ := pyth_rule hb ha (by rw [hd]; ring : b ^ 2 + a ^ 2 = d ^ 2)
  obtain ⟨j₆, n₆, h₆⟩ := pyth_rule hc hd0 (by rw [hd, hg]; ring : c ^ 2 + d ^ 2 = g ^ 2)
  refine core_ed ha hb hd he hg (k := k) (m := m) (J := j₃ + j₄ + j₅ + j₆)
    (N := n₃ * n₄ * n₅ * n₆) ?_ hm
  rw [← H, Nat.gcd_comm a c, Nat.gcd_comm a b]
  calc _ = ((e + a) * c.gcd a) * ((g + e) * b.gcd e) * ((d + a) * b.gcd a) *
        ((g + d) * c.gcd d) := by ring
    _ = _ := by rw [h₃, h₄, h₅, h₆]; ring

/-- **`μ₁ ≠ μ₂`.** For a perfect cuboid, `(a,f)(b,c)(a,c)(b,e)` — the gcds of the triples
`(a, f, g)`, `(b, c, f)`, `(a, c, e)`, `(b, e, g)` — is never `2^k m²`.
The proof uses only two face diagonals and `g`, so it holds for every body cuboid. -/
theorem IsPerfectCuboid.gcd_prod_fe_ne_two_pow_mul_sq {a b c : ℕ} (h : IsPerfectCuboid a b c)
    {e f g : ℕ} (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) (k m : ℕ) :
    a.gcd f * b.gcd c * a.gcd c * b.gcd e ≠ 2 ^ k * m ^ 2 := by
  intro H
  have ha := h.pos_a
  have hb := h.pos_b
  have hc := h.pos_c
  have he0 : 0 < e := by rcases Nat.eq_zero_or_pos e with rfl | h; · nlinarith
                         exact h
  have hf0 : 0 < f := by rcases Nat.eq_zero_or_pos f with rfl | h; · nlinarith
                         exact h
  have hm : m ≠ 0 := by
    rintro rfl
    have : 0 < a.gcd f * b.gcd c * a.gcd c * b.gcd e := by
      have := Nat.gcd_pos_of_pos_left f ha; have := Nat.gcd_pos_of_pos_left c hb
      have := Nat.gcd_pos_of_pos_left c ha; have := Nat.gcd_pos_of_pos_left e hb
      positivity
    simp [H] at this
  obtain ⟨j₁, n₁, h₁⟩ := pyth_rule hf0 ha (by rw [hf, hg]; ring : f ^ 2 + a ^ 2 = g ^ 2)
  obtain ⟨j₂, n₂, h₂⟩ := pyth_rule hc hb (by rw [hf]; ring : c ^ 2 + b ^ 2 = f ^ 2)
  obtain ⟨j₃, n₃, h₃⟩ := pyth_rule hc ha (by rw [he]; ring : c ^ 2 + a ^ 2 = e ^ 2)
  obtain ⟨j₄, n₄, h₄⟩ := pyth_rule hb he0 (by rw [he, hg]; ring : b ^ 2 + e ^ 2 = g ^ 2)
  refine core_fe ha hb he hf hg (k := k) (m := m) (J := j₁ + j₂ + j₃ + j₄)
    (N := n₁ * n₂ * n₃ * n₄) ?_ hm
  rw [← H, Nat.gcd_comm a f, Nat.gcd_comm b c, Nat.gcd_comm a c]
  calc _ = ((g + a) * f.gcd a) * ((f + b) * c.gcd b) * ((e + a) * c.gcd a) *
        ((g + e) * b.gcd e) := by ring
    _ = _ := by rw [h₁, h₂, h₃, h₄]; ring

/-- **`μ₁ ≠ μ₃`.** For a perfect cuboid, `(a,f)(b,c)(a,b)(c,d)` — the gcds of the triples
`(a, f, g)`, `(b, c, f)`, `(a, b, d)`, `(c, d, g)` — is never `2^k m²`.
The proof uses only two face diagonals and `g`, so it holds for every body cuboid. -/
theorem IsPerfectCuboid.gcd_prod_fd_ne_two_pow_mul_sq {a b c : ℕ} (h : IsPerfectCuboid a b c)
    {d f g : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) (k m : ℕ) :
    a.gcd f * b.gcd c * a.gcd b * c.gcd d ≠ 2 ^ k * m ^ 2 := by
  intro H
  have ha := h.pos_a
  have hb := h.pos_b
  have hc := h.pos_c
  have hd0 : 0 < d := by rcases Nat.eq_zero_or_pos d with rfl | h; · nlinarith
                         exact h
  have hf0 : 0 < f := by rcases Nat.eq_zero_or_pos f with rfl | h; · nlinarith
                         exact h
  have hm : m ≠ 0 := by
    rintro rfl
    have : 0 < a.gcd f * b.gcd c * a.gcd b * c.gcd d := by
      have := Nat.gcd_pos_of_pos_left f ha; have := Nat.gcd_pos_of_pos_left c hb
      have := Nat.gcd_pos_of_pos_left b ha; have := Nat.gcd_pos_of_pos_left d hc
      positivity
    simp [H] at this
  obtain ⟨j₁, n₁, h₁⟩ := pyth_rule hf0 ha (by rw [hf, hg]; ring : f ^ 2 + a ^ 2 = g ^ 2)
  obtain ⟨j₂, n₂, h₂⟩ := pyth_rule hc hb (by rw [hf]; ring : c ^ 2 + b ^ 2 = f ^ 2)
  obtain ⟨j₅, n₅, h₅⟩ := pyth_rule hb ha (by rw [hd]; ring : b ^ 2 + a ^ 2 = d ^ 2)
  obtain ⟨j₆, n₆, h₆⟩ := pyth_rule hc hd0 (by rw [hd, hg]; ring : c ^ 2 + d ^ 2 = g ^ 2)
  refine core_fd ha hb hd hf hg (k := k) (m := m) (J := j₁ + j₂ + j₅ + j₆)
    (N := n₁ * n₂ * n₅ * n₆) ?_ hm
  rw [← H, Nat.gcd_comm a f, Nat.gcd_comm b c, Nat.gcd_comm a b]
  calc _ = ((g + a) * f.gcd a) * ((f + b) * c.gcd b) * ((d + a) * b.gcd a) *
        ((g + d) * c.gcd d) := by ring
    _ = _ := by rw [h₁, h₂, h₅, h₆]; ring

end PerfectCuboid
