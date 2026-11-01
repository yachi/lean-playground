module

public import LeanPlayground.PerfectCuboid.BeauvilleCharacters

/-!
# The derived triangle in `ℤ[i]`: the gcd class and the quarter condition

Let `a, b, c` be the edges of a box with integer face diagonals `d² = a² + b²`, `e² = a² + c²`
and integer space diagonal `g² = a² + b² + c²` (a *body cuboid*; `f` is not needed). In `ℤ[i]`
put `p = a + g`, `q = b − ιc`. The derived triangle `T₁ = (ag, bc, de)`
(`(ag)² + (bc)² = (de)²`) enters the Stoll–Testa identities of `BeauvilleLambda.lean` through

* `gauss_ag`: `(p² − q²)(p² + q̄²) = 4p²(ag + ιbc)` (modulo `g² = a² + b² + c²`);
* `p_sq_sub_q_sq`: `p² − q² = 2(e² + ag + ιbc)`;
* `triple_product`: `(ag + ιbc)(bg + ιac)(cg + ιab) = ι(def)²`;
* `two_mul_hyp_add`: `2(z + x)(z + y) = (x + y + z)²` for every right triangle.

Multiplying `hypleg_e` with the conjugate of `hypleg_d` and using `gauss_ag` gives
(`gauss_key`) `(ag + ιbc) · W · (2p)² = (β₂ β̄₃)²` with `W = (e+a)(g+e)(d+a)(g+d)`,
`β₂ = a² + ag + c² + ιbc + (a+g)e`, `β̄₃ = a² + ag + b² + ιbc + (a+g)d`.

**C1 (the gcd class).** Let `k = gcd(ag, bc)`. If `ag/k` is odd then `k · W` is a perfect square
(`gcd_class_odd`); if `ag/k` is even then `2k · W` is a perfect square (`gcd_class_even`).
*Proof.* The primitive triangle `(ag/k, bc/k, de/k)` is `(m² − n², 2mn, m² + n²)` (odd case)
or `(2mn, m² − n², m² + n²)` (even case), so `ag + ιbc = k(m + ιn)²` resp. `ιk(m − ιn)²`.
Then `gauss_key` reads `kW · z² = (β₂β̄₃)²` resp. `ιkW · z² = (β₂β̄₃)²` with `z ≠ 0`, so `kW`
resp. `ιkW` is a square `V²` in `ℤ[i]`; comparing real and imaginary parts, `kW = V.re²`
(`V.re · V.im = 0` and `kW > 0`) resp. `kW = 2 V.re²`. Both cases occur (75 odd and 51 even
cases among the 126 known face cuboids, relabelled as body cuboids). The degenerate box
`(a, b, 0)` is allowed (only `0 < a` is assumed), so C1 is a local square-class identity, not an
obstruction. In Stoll–Testa terms the square class of the gcd of the derived triangle is `d₂d₃`
(odd case) resp. `2d₂d₃` (even case), with `d₂ ≡ (e+a)(g+e)`, `d₃ ≡ (d+a)(g+d)`.
`IsPerfectCuboid.gcd_class` states it for the three derived triangles `(ag, bc, de)`,
`(bg, ac, df)`, `(cg, ab, ef)` of a perfect cuboid.

**C2/C3 (the quarter condition).** If `ag = k(m² − n²)`, `bc = 2kmn`, `m + n = σ²`,
`m − n = δ²` then `2(ag + ιbc) = ιk(σ² − ιδ²)²` (`quarter_gauss`) and, with `w² = kW`,
`β₂β̄₃ = ±(1 + ι) · w · (a + g) · (σ² − ιδ²)` (`quarter_factorisation`;
natural-number form with `w` supplied by C1: `quarter_factorisation_nat`).
-/

@[expose] public section

namespace PerfectCuboid.QuarterChar

open GaussianQuartic

local notation "G" => GaussianInt

/-! ### Ring identities in `ℤ[i]` -/

section Identities

variable {a b c d e f g : G}

/-- **I1.** `(p² − q²)(p² + q̄²) = 4p²(ag + ιbc)` modulo the space-diagonal equation. -/
theorem gauss_ag (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    ((a + g) ^ 2 - (b - ι * c) ^ 2) * ((a + g) ^ 2 + (b + ι * c) ^ 2) =
      4 * (a + g) ^ 2 * (a * g + ι * b * c) := by
  linear_combination (2 * b ^ 2 * c ^ 2 - c ^ 4 * ι ^ 2 + c ^ 4) * ι_sq +
    (-a ^ 2 + b ^ 2 + c ^ 2 + g ^ 2) * hg

/-- `p² − q² = 2(e² + ag + ιbc)` modulo `e² = a² + c²`, `g² = a² + b² + c²`. -/
theorem p_sq_sub_q_sq (he : e ^ 2 = a ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    (a + g) ^ 2 - (b - ι * c) ^ 2 = 2 * (e ^ 2 + a * g + ι * b * c) := by
  linear_combination (-c ^ 2) * ι_sq + hg - 2 * he

/-- `p² + q̄² = 2(d² + ag + ιbc)` modulo `d² = a² + b²`, `g² = a² + b² + c²`. -/
theorem p_sq_add_qbar_sq (hd : d ^ 2 = a ^ 2 + b ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    (a + g) ^ 2 + (b + ι * c) ^ 2 = 2 * (d ^ 2 + a * g + ι * b * c) := by
  linear_combination c ^ 2 * ι_sq + hg - 2 * hd

/-- **I2.** `(ag + ιbc)(bg + ιac)(cg + ιab) = ι(def)²` modulo the four cuboid equations. -/
theorem triple_product (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hf : f ^ 2 = b ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    (a * g + ι * b * c) * (b * g + ι * a * c) * (c * g + ι * a * b) = ι * (d * e * f) ^ 2 := by
  linear_combination (a ^ 3 * b * c * g + a ^ 2 * b ^ 2 * c ^ 2 * ι + a * b ^ 3 * c * g +
      a * b * c ^ 3 * g) * ι_sq +
    (a ^ 2 * b ^ 2 * ι + a ^ 2 * c ^ 2 * ι + a * b * c * g + b ^ 2 * c ^ 2 * ι) * hg +
    (-d ^ 2 * e ^ 2 * ι) * hf + (-b ^ 2 * d ^ 2 * ι - c ^ 2 * d ^ 2 * ι) * he +
    (-a ^ 2 * b ^ 2 * ι - a ^ 2 * c ^ 2 * ι - b ^ 2 * c ^ 2 * ι - c ^ 4 * ι) * hd

/-- For any right triangle `x² + y² = z²` (any commutative ring): `2(z+x)(z+y) = (x+y+z)²`. -/
theorem two_mul_hyp_add {R : Type*} [CommRing R] {x y z : R} (h : z ^ 2 = x ^ 2 + y ^ 2) :
    2 * ((z + x) * (z + y)) = (x + y + z) ^ 2 := by
  linear_combination h

/-- The complex conjugate of `hypleg_d` (`ι ↦ −ι`, the variables being real):
`(p² + q̄²) · 2(d+a)(g+d) = 2β̄₃²`. -/
theorem hypleg_d_conj (hd : d ^ 2 = a ^ 2 + b ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    ((a + g) ^ 2 + (b + ι * c) ^ 2) * (2 * (d + a) * (g + d)) =
      2 * (a ^ 2 + a * g + b ^ 2 + ι * b * c + (a + g) * d) ^ 2 := by
  linear_combination (2 * (b + c * ι) ^ 2) * hd + (2 * (a + d) * (a + g)) * hg +
    (2 * c ^ 2 * (a + d) * (a + g)) * ι_sq

/-- **The key identity.** `(ag + ιbc) · (e+a)(g+e)(d+a)(g+d) · (2p)² = (β₂ β̄₃)²`. -/
theorem gauss_key (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    (a * g + ι * b * c) * ((e + a) * (g + e) * (d + a) * (g + d)) * (2 * (a + g)) ^ 2 =
      ((a ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e) *
        (a ^ 2 + a * g + b ^ 2 + ι * b * c + (a + g) * d)) ^ 2 := by
  have h1 := PerfectCuboid.hypleg_e he hg
  have h2 := hypleg_d_conj hd hg
  have h3 := gauss_ag hg
  refine mul_left_cancel₀ (show (4 : G) ≠ 0 by decide) ?_
  linear_combination (-4 * ((e + a) * (g + e)) * ((d + a) * (g + d))) * h3 +
    (((a + g) ^ 2 + (b + ι * c) ^ 2) * (2 * (d + a) * (g + d))) * h1 +
    (2 * (a ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e) ^ 2) * h2

end Identities

/-! ### Squares of natural numbers detected in `ℤ[i]` -/

/-- A positive natural number that is a square in `ℤ[i]` is a square in `ℕ`. -/
theorem isSquare_of_gauss_sq {n : ℕ} (hn : 0 < n) {V : G} (h : (n : G) = V ^ 2) :
    IsSquare n := by
  have hre := congrArg Zsqrtd.re h
  have him := congrArg Zsqrtd.im h
  simp only [Zsqrtd.re_natCast, Zsqrtd.im_natCast, sq_re, sq_im] at hre him
  have hmul : V.re * V.im = 0 := by linarith
  rcases mul_eq_zero.1 hmul with h0 | h0
  · rw [h0] at hre
    have : (0 : ℤ) < n := by exact_mod_cast hn
    nlinarith [sq_nonneg V.im]
  · rw [h0] at hre
    refine ⟨V.re.natAbs, ?_⟩
    have : (n : ℤ) = (V.re.natAbs : ℤ) * V.re.natAbs := by
      rw [Int.natCast_natAbs, ← sq, sq_abs]; linarith
    exact_mod_cast this

/-- If `ι · n` is a square in `ℤ[i]` for a positive natural number `n`, then `2n` is a square. -/
theorem isSquare_two_mul_of_gauss_sq {n : ℕ} (hn : 0 < n) {V : G} (h : ι * (n : G) = V ^ 2) :
    IsSquare (2 * n) := by
  have hre : (0 : ℤ) = V.re ^ 2 - V.im ^ 2 := by
    have := congrArg Zsqrtd.re h
    simpa [ι, sq_re] using this
  have him : (n : ℤ) = 2 * V.re * V.im := by
    have := congrArg Zsqrtd.im h
    simpa [ι, sq_im] using this
  have hsq : (V.re - V.im) * (V.re + V.im) = 0 := by linear_combination -hre
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  rcases mul_eq_zero.1 hsq with h0 | h0
  · have : V.im = V.re := by linarith
    refine ⟨2 * V.re.natAbs, ?_⟩
    have : ((2 * n : ℕ) : ℤ) = ((2 * V.re.natAbs : ℕ) : ℤ) * ((2 * V.re.natAbs : ℕ) : ℤ) := by
      push_cast
      rw [this] at him
      nlinarith [sq_abs V.re]
    exact_mod_cast this
  · have : V.im = -V.re := by linarith
    rw [this] at him
    nlinarith [sq_nonneg V.re]

/-! ### C1: the gcd class of the derived triangle -/

/-- The derived triangle `(ag, bc, de)` of a body cuboid is Pythagorean. -/
theorem derived_pyth {a b c d e g : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) : (a * g) ^ 2 + (b * c) ^ 2 = (d * e) ^ 2 := by
  calc (a * g) ^ 2 + (b * c) ^ 2 = a ^ 2 * g ^ 2 + b ^ 2 * c ^ 2 := by ring
    _ = (a ^ 2 + b ^ 2) * (a ^ 2 + c ^ 2) := by rw [hg]; ring
    _ = (d * e) ^ 2 := by rw [← hd, ← he]; ring

/-- The common set-up of C1: the primitive derived triangle `(A, B, C)` with
`ag = kA`, `bc = kB`, `de = kC`, `A² + B² = C²`, `gcd(A, B) = 1`, `0 < C`. -/
theorem primitive_setup {a b c d e g : ℕ} (ha : 0 < a) (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    0 < Nat.gcd (a * g) (b * c) ∧
    a * g = Nat.gcd (a * g) (b * c) * ((a * g) / Nat.gcd (a * g) (b * c)) ∧
    b * c = Nat.gcd (a * g) (b * c) * ((b * c) / Nat.gcd (a * g) (b * c)) ∧
    Nat.Coprime ((a * g) / Nat.gcd (a * g) (b * c)) ((b * c) / Nat.gcd (a * g) (b * c)) ∧
    ∃ C : ℕ, 0 < C ∧ ((a * g) / Nat.gcd (a * g) (b * c)) ^ 2 +
      ((b * c) / Nat.gcd (a * g) (b * c)) ^ 2 = C ^ 2 := by
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0] at hg; nlinarith
    · exact h0
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0] at hd; nlinarith
    · exact h0
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0] at he; nlinarith
    · exact h0
  set k := Nat.gcd (a * g) (b * c) with hk
  set A := (a * g) / k
  set B := (b * c) / k
  have hk0 : 0 < k := Nat.gcd_pos_of_pos_left _ (Nat.mul_pos ha hg0)
  have hA : a * g = k * A := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have hB : b * c = k * B := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  have hcop : Nat.Coprime A B := Nat.coprime_div_gcd_div_gcd hk0
  have hP := derived_pyth hd he hg
  have hkde : k ∣ d * e := by
    rw [← Nat.pow_dvd_pow_iff two_ne_zero, ← hP, hA, hB]
    exact ⟨A ^ 2 + B ^ 2, by ring⟩
  obtain ⟨C, hC⟩ := hkde
  refine ⟨hk0, hA, hB, hcop, C, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos C with h0 | h0
    · rw [h0, mul_zero] at hC
      exact absurd hC (Nat.mul_pos hd0 he0).ne'
    · exact h0
  · have : k ^ 2 * (A ^ 2 + B ^ 2) = k ^ 2 * C ^ 2 := by
      have := hP; rw [hA, hB, hC] at this; linear_combination this
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this

/-- Positivity of `W = (e+a)(g+e)(d+a)(g+d)`. -/
theorem W_pos {a d e g : ℕ} (ha : 0 < a) (hg : 0 < g) :
    0 < (e + a) * (g + e) * (d + a) * (g + d) := by
  positivity

/-- Casting the body-cuboid equations into `ℤ[i]`. -/
theorem cast_eqs {a b c d e g : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    (d : G) ^ 2 = (a : G) ^ 2 + (b : G) ^ 2 ∧ (e : G) ^ 2 = (a : G) ^ 2 + (c : G) ^ 2 ∧
      (g : G) ^ 2 = (a : G) ^ 2 + (b : G) ^ 2 + (c : G) ^ 2 :=
  ⟨by exact_mod_cast hd, by exact_mod_cast he, by exact_mod_cast hg⟩

/-- `ag + ιbc ≠ 0` in `ℤ[i]` when `a, g > 0`. -/
theorem ag_add_ne_zero {a b c g : ℕ} (ha : 0 < a) (hg : 0 < g) :
    (a : G) * g + ι * b * c ≠ 0 := by
  intro h
  have := congrArg Zsqrtd.re h
  simp [ι] at this
  omega

/-- **C1, odd case.** For a body cuboid (`0 < a`, `d, e, g` integral) with `k = gcd(ag, bc)`:
if `ag/k` is odd then `k · (e+a)(g+e)(d+a)(g+d)` is a perfect square. -/
theorem gcd_class_odd {a b c d e g : ℕ} (ha : 0 < a) (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2)
    (hodd : Odd ((a * g) / Nat.gcd (a * g) (b * c))) :
    IsSquare (Nat.gcd (a * g) (b * c) * ((e + a) * (g + e) * (d + a) * (g + d))) := by
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0] at hg; nlinarith
    · exact h0
  obtain ⟨hk0, hA, hB, hcop, C, hC0, hP⟩ := primitive_setup ha hd he hg
  set k := Nat.gcd (a * g) (b * c)
  set A := (a * g) / k
  set B := (b * c) / k
  have hpt : PythagoreanTriple (A : ℤ) B C := by
    unfold PythagoreanTriple
    have : A * A + B * B = C * C := by nlinarith [hP]
    exact_mod_cast this
  have hgcd : Int.gcd (A : ℤ) (B : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact hcop
  have hpar : (A : ℤ) % 2 = 1 := by
    obtain ⟨r, hr⟩ := hodd
    rw [hr]; push_cast; omega
  obtain ⟨m, n, hm, hn, -, -, -, -⟩ :=
    hpt.coprime_classification' hgcd hpar (by exact_mod_cast hC0)
  obtain ⟨hdG, heG, hgG⟩ := cast_eqs (a := a) (b := b) (c := c) hd he hg
  have hX : (a : G) * g + ι * b * c = (k : G) * ((m : G) + ι * (n : G)) ^ 2 := by
    have h1 : (a : G) * g = (k : G) * (A : G) := by exact_mod_cast hA
    have h2 : (b : G) * c = (k : G) * (B : G) := by exact_mod_cast hB
    have h3 : (A : G) = (m : G) ^ 2 - (n : G) ^ 2 := by
      have := congrArg (fun z : ℤ => (z : G)) hm; push_cast at this; exact this
    have h4 : (B : G) = 2 * (m : G) * (n : G) := by
      have := congrArg (fun z : ℤ => (z : G)) hn; push_cast at this; exact this
    linear_combination h1 + ι * h2 + (k : G) * h3 + (ι * k : G) * h4 +
      (-(k : G) * (n : G) ^ 2) * ι_sq
  have key := gauss_key hdG heG hgG
  rw [hX] at key
  have hz : 2 * ((a : G) + g) * ((m : G) + ι * n) ≠ 0 := by
    intro h0
    apply ag_add_ne_zero (b := b) (c := c) ha hg0
    rw [hX]
    have : (k : G) * ((m : G) + ι * n) ^ 2 * (2 * ((a : G) + g)) ^ 2 =
        (k : G) * (2 * ((a : G) + g) * ((m : G) + ι * n)) ^ 2 := by ring
    rw [h0] at this
    have h2p : (2 * ((a : G) + g)) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      apply mul_ne_zero two_ne_zero
      exact_mod_cast (Nat.add_pos_left ha g).ne'
    have := this.trans (by ring : (k : G) * (0 : G) ^ 2 = 0)
    exact (mul_eq_zero.1 this).resolve_right h2p
  obtain ⟨V, hV⟩ := exists_sq_of_mul hz
    (by linear_combination key : (2 * ((a : G) + g) * ((m : G) + ι * n)) ^ 2 *
      ((k : G) * (((e : G) + a) * ((g : G) + e) * ((d : G) + a) * ((g : G) + d))) =
      (((a : G) ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e) *
        ((a : G) ^ 2 + a * g + b ^ 2 + ι * b * c + (a + g) * d)) ^ 2)
  apply isSquare_of_gauss_sq (Nat.mul_pos hk0 (W_pos ha hg0)) (V := V)
  rw [← hV]; push_cast; ring

/-- **C1, even case.** For a body cuboid with `k = gcd(ag, bc)`: if `ag/k` is even then
`2k · (e+a)(g+e)(d+a)(g+d)` is a perfect square. -/
theorem gcd_class_even {a b c d e g : ℕ} (ha : 0 < a) (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2)
    (heven : Even ((a * g) / Nat.gcd (a * g) (b * c))) :
    IsSquare (2 * (Nat.gcd (a * g) (b * c) * ((e + a) * (g + e) * (d + a) * (g + d)))) := by
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0] at hg; nlinarith
    · exact h0
  obtain ⟨hk0, hA, hB, hcop, C, hC0, hP⟩ := primitive_setup ha hd he hg
  set k := Nat.gcd (a * g) (b * c)
  set A := (a * g) / k
  set B := (b * c) / k
  have hpt : PythagoreanTriple (B : ℤ) A C := by
    unfold PythagoreanTriple
    have : B * B + A * A = C * C := by nlinarith [hP]
    exact_mod_cast this
  have hgcd : Int.gcd (B : ℤ) (A : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact hcop.symm
  have hBodd : Odd B := by
    rcases Nat.even_or_odd B with hBe | hBo
    · exfalso
      have h2 : 2 ∣ Nat.gcd A B := Nat.dvd_gcd (even_iff_two_dvd.1 heven) (even_iff_two_dvd.1 hBe)
      rw [hcop] at h2; omega
    · exact hBo
  have hpar : (B : ℤ) % 2 = 1 := by
    obtain ⟨r, hr⟩ := hBodd
    rw [hr]; push_cast; omega
  obtain ⟨m, n, hm, hn, -, -, -, -⟩ :=
    hpt.coprime_classification' hgcd hpar (by exact_mod_cast hC0)
  obtain ⟨hdG, heG, hgG⟩ := cast_eqs (a := a) (b := b) (c := c) hd he hg
  have hX : (a : G) * g + ι * b * c = ι * (k : G) * ((m : G) - ι * (n : G)) ^ 2 := by
    have h1 : (a : G) * g = (k : G) * (A : G) := by exact_mod_cast hA
    have h2 : (b : G) * c = (k : G) * (B : G) := by exact_mod_cast hB
    have h3 : (B : G) = (m : G) ^ 2 - (n : G) ^ 2 := by
      have := congrArg (fun z : ℤ => (z : G)) hm; push_cast at this; exact this
    have h4 : (A : G) = 2 * (m : G) * (n : G) := by
      have := congrArg (fun z : ℤ => (z : G)) hn; push_cast at this; exact this
    linear_combination h1 + ι * h2 + (ι * k : G) * h3 + (k : G) * h4 +
      (2 * (k : G) * m * n - ι * k * n ^ 2) * ι_sq
  have key := gauss_key hdG heG hgG
  rw [hX] at key
  have hz : 2 * ((a : G) + g) * ((m : G) - ι * n) ≠ 0 := by
    intro h0
    apply ag_add_ne_zero (b := b) (c := c) ha hg0
    rw [hX]
    have : ι * (k : G) * ((m : G) - ι * n) ^ 2 * (2 * ((a : G) + g)) ^ 2 =
        ι * (k : G) * (2 * ((a : G) + g) * ((m : G) - ι * n)) ^ 2 := by ring
    rw [h0] at this
    have h2p : (2 * ((a : G) + g)) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      apply mul_ne_zero two_ne_zero
      exact_mod_cast (Nat.add_pos_left ha g).ne'
    have := this.trans (by ring : ι * (k : G) * (0 : G) ^ 2 = 0)
    exact (mul_eq_zero.1 this).resolve_right h2p
  obtain ⟨V, hV⟩ := exists_sq_of_mul hz
    (by linear_combination key : (2 * ((a : G) + g) * ((m : G) - ι * n)) ^ 2 *
      (ι * ((k : G) * (((e : G) + a) * ((g : G) + e) * ((d : G) + a) * ((g : G) + d)))) =
      (((a : G) ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e) *
        ((a : G) ^ 2 + a * g + b ^ 2 + ι * b * c + (a + g) * d)) ^ 2)
  apply isSquare_two_mul_of_gauss_sq (Nat.mul_pos hk0 (W_pos ha hg0)) (V := V)
  rw [← hV]; push_cast; ring

/-- C1 in one statement: `kW` or `2kW` is a perfect square. -/
theorem gcd_class {a b c d e g : ℕ} (ha : 0 < a) (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    IsSquare (Nat.gcd (a * g) (b * c) * ((e + a) * (g + e) * (d + a) * (g + d))) ∨
      IsSquare (2 * (Nat.gcd (a * g) (b * c) * ((e + a) * (g + e) * (d + a) * (g + d)))) := by
  rcases Nat.even_or_odd ((a * g) / Nat.gcd (a * g) (b * c)) with h | h
  · exact Or.inr (gcd_class_even ha hd he hg h)
  · exact Or.inl (gcd_class_odd ha hd he hg h)

/-- If `ag` is odd (e.g. `a` the odd edge of a primitive perfect cuboid), the odd case applies. -/
theorem gcd_class_of_odd {a b c d e g : ℕ} (ha : 0 < a) (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) (hodd : Odd (a * g)) :
    IsSquare (Nat.gcd (a * g) (b * c) * ((e + a) * (g + e) * (d + a) * (g + d))) :=
  gcd_class_odd ha hd he hg (hodd.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)))

/-- **C1 for the three derived triangles of a perfect cuboid** `T₁ = (ag, bc, de)`,
`T₂ = (bg, ac, df)`, `T₃ = (cg, ab, ef)`: for each, `gcd · W` or `2 · gcd · W` is a square. -/
theorem _root_.PerfectCuboid.IsPerfectCuboid.gcd_class {a b c d e f g : ℕ}
    (h : IsPerfectCuboid a b c) (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2)
    (hf : f ^ 2 = b ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) :
    (IsSquare (Nat.gcd (a * g) (b * c) * ((e + a) * (g + e) * (d + a) * (g + d))) ∨
      IsSquare (2 * (Nat.gcd (a * g) (b * c) * ((e + a) * (g + e) * (d + a) * (g + d))))) ∧
    (IsSquare (Nat.gcd (b * g) (a * c) * ((f + b) * (g + f) * (d + b) * (g + d))) ∨
      IsSquare (2 * (Nat.gcd (b * g) (a * c) * ((f + b) * (g + f) * (d + b) * (g + d))))) ∧
    (IsSquare (Nat.gcd (c * g) (a * b) * ((f + c) * (g + f) * (e + c) * (g + e))) ∨
      IsSquare (2 * (Nat.gcd (c * g) (a * b) * ((f + c) * (g + f) * (e + c) * (g + e))))) := by
  refine ⟨QuarterChar.gcd_class h.pos_a hd he hg,
    QuarterChar.gcd_class (a := b) (b := a) (c := c) (d := d) (e := f) (g := g) h.pos_b
      (by rw [hd]; ring) (by rw [hf]) (by rw [hg]; ring),
    QuarterChar.gcd_class (a := c) (b := a) (c := b) (d := e) (e := f) (g := g) h.pos_c
      (by rw [he]; ring) (by rw [hf]; ring) (by rw [hg]; ring)⟩

/-! ### C2, C3: the quarter condition as a Gaussian factorisation -/

/-- **C2.** If `ag = k(m² − n²)`, `bc = 2kmn`, `m + n = σ²`, `m − n = δ²` then
`2(ag + ιbc) = ιk(σ² − ιδ²)²`. -/
theorem quarter_gauss {a b c g k m n σ δ : G} (h1 : a * g = k * (m ^ 2 - n ^ 2))
    (h2 : b * c = 2 * k * m * n) (hσ : m + n = σ ^ 2) (hδ : m - n = δ ^ 2) :
    2 * (a * g + ι * b * c) = ι * k * (σ ^ 2 - ι * δ ^ 2) ^ 2 := by
  rw [← hσ, ← hδ]
  linear_combination 2 * h1 + 2 * ι * h2 + (-k * (m - n) ^ 2 * ι + 2 * k * (m ^ 2 - n ^ 2)) * ι_sq

/-- **C3 (the factorisation).** Under the quarter condition for `T₁` and `w² = kW`,
`β₂ β̄₃ = ±(1 + ι) · w · (a + g) · (σ² − ιδ²)`. -/
theorem quarter_factorisation {a b c d e g k m n σ δ w : G} (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2)
    (h1 : a * g = k * (m ^ 2 - n ^ 2)) (h2 : b * c = 2 * k * m * n) (hσ : m + n = σ ^ 2)
    (hδ : m - n = δ ^ 2) (hw : k * ((e + a) * (g + e) * (d + a) * (g + d)) = w ^ 2) :
    (a ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e) *
        (a ^ 2 + a * g + b ^ 2 + ι * b * c + (a + g) * d) =
          (1 + ι) * w * (a + g) * (σ ^ 2 - ι * δ ^ 2) ∨
      (a ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e) *
        (a ^ 2 + a * g + b ^ 2 + ι * b * c + (a + g) * d) =
          -((1 + ι) * w * (a + g) * (σ ^ 2 - ι * δ ^ 2)) := by
  have key := gauss_key hd he hg
  have q := quarter_gauss h1 h2 hσ hδ
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  linear_combination (-1) * key +
    (2 * (a + g) ^ 2 * ((e + a) * (g + e) * (d + a) * (g + d))) * q +
    (2 * ι * (a + g) ^ 2 * (σ ^ 2 - ι * δ ^ 2) ^ 2) * hw -
    (w ^ 2 * (a + g) ^ 2 * (σ ^ 2 - ι * δ ^ 2) ^ 2) * ι_sq

/-- **C3, natural-number form.** For a body cuboid (`0 < a`) with `k = gcd(ag, bc)`, if the
primitive derived triangle is a quarter triangle — `ag + kn² = km²`, `bc = 2kmn`, `m + n = σ²`,
`m = n + δ²` — then `kW = w²` for a natural number `w` (C1; the odd case is forced since `bc/k`
is even) and `β₂ β̄₃ = ±(1 + ι) w (a + g)(σ² − ιδ²)` in `ℤ[i]`. -/
theorem quarter_factorisation_nat {a b c d e g m n σ δ : ℕ} (ha : 0 < a)
    (hd : d ^ 2 = a ^ 2 + b ^ 2) (he : e ^ 2 = a ^ 2 + c ^ 2) (hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2)
    (h1 : a * g + Nat.gcd (a * g) (b * c) * n ^ 2 = Nat.gcd (a * g) (b * c) * m ^ 2)
    (h2 : b * c = 2 * Nat.gcd (a * g) (b * c) * m * n) (hσ : m + n = σ ^ 2)
    (hδ : m = n + δ ^ 2) :
    ∃ w : ℕ, w ^ 2 = Nat.gcd (a * g) (b * c) * ((e + a) * (g + e) * (d + a) * (g + d)) ∧
      (((a : G) ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e) *
          ((a : G) ^ 2 + a * g + b ^ 2 + ι * b * c + (a + g) * d) =
            (1 + ι) * w * (a + g) * ((σ : G) ^ 2 - ι * δ ^ 2) ∨
        ((a : G) ^ 2 + a * g + c ^ 2 + ι * b * c + (a + g) * e) *
          ((a : G) ^ 2 + a * g + b ^ 2 + ι * b * c + (a + g) * d) =
            -((1 + ι) * w * (a + g) * ((σ : G) ^ 2 - ι * δ ^ 2))) := by
  obtain ⟨hk0, hA, hB, hcop, -⟩ := primitive_setup ha hd he hg
  set k := Nat.gcd (a * g) (b * c)
  have hBe : (b * c) / k = 2 * (m * n) := by
    rw [h2, show 2 * k * m * n = k * (2 * (m * n)) by ring, Nat.mul_div_cancel_left _ hk0]
  have hodd : Odd ((a * g) / k) := by
    rcases Nat.even_or_odd ((a * g) / k) with he' | ho
    · exfalso
      have h2' : 2 ∣ Nat.gcd ((a * g) / k) ((b * c) / k) :=
        Nat.dvd_gcd (even_iff_two_dvd.1 he') ⟨m * n, hBe⟩
      rw [hcop] at h2'; omega
    · exact ho
  obtain ⟨w, hw⟩ := gcd_class_odd ha hd he hg hodd
  refine ⟨w, by rw [hw]; ring, ?_⟩
  obtain ⟨hdG, heG, hgG⟩ := cast_eqs (a := a) (b := b) (c := c) hd he hg
  apply quarter_factorisation (k := (k : G)) (m := (m : G)) (n := (n : G)) (δ := (δ : G))
    hdG heG hgG
  · have : ((a * g + k * n ^ 2 : ℕ) : G) = ((k * m ^ 2 : ℕ) : G) := by rw [h1]
    push_cast at this; linear_combination this
  · exact_mod_cast h2
  · exact_mod_cast hσ
  · have : (m : G) = n + δ ^ 2 := by exact_mod_cast hδ
    linear_combination this
  · have : ((w * w : ℕ) : G) = ((k * ((e + a) * (g + e) * (d + a) * (g + d)) : ℕ) : G) := by
      rw [hw]
    push_cast at this; linear_combination -this

/-! ### Examples -/

/-- The face cuboid `(153, 672, 104)` relabelled as a body cuboid `(104, 153, 672)`
(`d = 185`, `e = 680`, `g = 697`): `gcd(104·697, 153·672) = 136`, `104·697/136 = 533` is odd,
and `136 · (680+104)(697+680)(185+104)(697+185)` is a square. -/
example : IsSquare (Nat.gcd (104 * 697) (153 * 672) *
    ((680 + 104) * (697 + 680) * (185 + 104) * (697 + 185))) :=
  gcd_class_odd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

/-- The degenerate box `(3, 4, 0)` (`d = g = 5`, `e = 3`) is allowed: `k = gcd(15, 0) = 15`,
`15 · (3+3)(5+3)(5+3)(5+5) = 240²`. -/
example : IsSquare (Nat.gcd (3 * 5) (4 * 0) * ((3 + 3) * (5 + 3) * (5 + 3) * (5 + 5))) :=
  gcd_class_odd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

/-- An even case: the body cuboid `(448, 264, 975)` (`d = 520`, `e = 1073`, `g = 1105`) has
`k = gcd(448·1105, 264·975) = 520` and `448·1105/520 = 952` even, so `2k · W` is a square. -/
example : IsSquare (2 * (Nat.gcd (448 * 1105) (264 * 975) *
    ((1073 + 448) * (1105 + 1073) * (520 + 448) * (1105 + 520)))) :=
  gcd_class_even (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)


end PerfectCuboid.QuarterChar
