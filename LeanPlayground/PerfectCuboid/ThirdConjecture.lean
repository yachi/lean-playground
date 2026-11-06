module

public import Mathlib
public import LeanPlayground.PerfectCuboid.ConfigCuboid

/-!
# The third cuboid conjecture: even quadratic factors

Sharipov's **third cuboid conjecture** (arXiv:1108.5348, arXiv:1203.2567; stated in Lean as
`EulerBrick.Cuboid.cuboidThree` in google-deepmind/formal-conjectures) says that for positive
coprime integers `a, b, c`, pairwise distinct, with `b c ≠ a²` and `a c ≠ b²`, the degree-12
polynomial `cuboidThreePoly a b c` below is irreducible in `ℤ[X]`. The polynomial is even:
`cuboidThreePoly a b c = f(X²)` for the sextic `f = sextic a b c`. A rational root `t` of it gives
a rational perfect cuboid (Sharipov), so the conjecture implies that the parameters `a, b, c` of
Sharipov's cuboid equation give no perfect cuboid.

**Main theorem (new).** For rationals `a, b, c` with `c ≠ 0`, every nonzero rational root `y` of
the sextic `f_{a,b,c}` is a square or minus a square (`isSquare_or_isSquare_neg_of_sextic_eq_zero`).

So if `X² − r` divides `cuboidThreePoly a b c` (for integers with `c ≠ 0`), then `r = m²` or
`r = −m²` (`isSquare_or_isSquare_neg_of_dvd`). Positive non-square `r` never occurs: an even
quadratic factor `X² − r` with `r > 0` always splits as `(X − m)(X + m)`.

*Proof idea.* Write `y = t²` with `t = √y`. Sharipov's parametrization turns a root into a box
over `ℚ(√y)` with unit space diagonal, in which one edge and the two face diagonals through it lie
in `√y·ℚ` while the other lengths are rational. Multiplying by `√y` gives rationals with
`u² + y v² = D²`, `u² + y w² = E²`, `u² + y (v² + w²) = y G²` and `u ≠ 0`
(`sextic_identity_one`, `sextic_identity_two`, `sextic_identity_three`; the first two hold modulo
`f`, the third identically). Scale to integers and write `y = s r²` with `s` squarefree. If a prime
`p` divides `s`, the third equation gives `p ∣ u`, the first two give `p ∣ D, E` and then
`p ∣ v, w` (as `p² ∤ s`), and finally `p ∣ G` (`dvd_of_descent`). Infinite descent
(`eq_zero_of_descent`) forces `u = 0`, a contradiction, so `s = ±1`.
The degenerate cases, where the parametrization has a zero denominator, are exactly those where
`y` is `±` a square already (`y ∈ {−c², b², −a²}`).

**Consequence for cuboids.** Combined with Sharipov's parametrization this gives
`exists_isRatCuboid_of_dvd`: if `X² − r` with `r > 0` divides `cuboidThreePoly a b c` and the
triple is not exceptional (`excPoly a b c ≠ 0`, which for positive `a, b, c` is exactly the
hypothesis of the conjecture apart from coprimality), then a rational perfect cuboid exists. The
root-to-cuboid step (`exists_isRatCuboid_of_root`) is Sharipov's Theorem 1.1 (one direction);
the nondegeneracy of the box is checked here by explicit resultant certificates
(`nn_sub_dd_ne_zero`, `nn_add_dd_ne_zero`).

What remains open for even quadratic factors is `X² + m²`: a root `y = −m²` gives the same
system with `s = −1`, where the descent says nothing.

Literature. We found no prior proof that `f_{a,b,c}` has no positive non-square rational root.
Sharipov (arXiv:1203.2567) proves a structural theorem for integer roots `t` of the degree-12
polynomial; Asiryan's work (arXiv:2510.11768, arXiv:2610.25319) treats the first and second
conjectures, not the third.
-/

@[expose] public section

namespace PerfectCuboid.ThirdConjecture

open Polynomial

/-! ### The polynomials -/

/-- Sharipov's third cuboid polynomial, exactly as in formal-conjectures
(`EulerBrick.Cuboid.CuboidThreeFor`). -/
noncomputable def cuboidThreePoly (a b c : ℤ) : ℤ[X] :=
  X ^ 12 + C (6 * c ^ 2 - 2 * a ^ 2 - 2 * b ^ 2) * X ^ 10
    + C (c ^ 4 + b ^ 4 + a ^ 4 + 4 * a ^ 2 * c ^ 2 + 4 * b ^ 2 * c ^ 2 - 12 * b ^ 2 * a ^ 2)
    * X ^ 8 + C (6 * a ^ 4 * c ^ 2 + 6 * c ^ 2 * b ^ 4 - 8 * a ^ 2 * b ^ 2 * c ^ 2
    - 2 * c ^ 4 * a ^ 2 - 2 * c ^ 4 * b ^ 2 - 2 * a ^ 4 * b ^ 2 - 2 * b ^ 4 * a ^ 2)
    * X ^ 6 + C (4 * c ^ 2 * b ^ 4 * a ^ 2 + 4 * a ^ 4 * c ^ 2 * b ^ 2
    - 12 * c ^ 4 * a ^ 2 * b ^ 2 + c ^ 4 * a ^ 4 + c ^ 4 * b ^ 4 + a ^ 4 * b ^ 4) * X ^ 4
    + C (6 * a ^ 4 * c ^ 2 * b ^ 4 - 2 * c ^ 4 * a ^ 4 * b ^ 2 - 2 * c ^ 4 * a ^ 2 * b ^ 4)
    * X ^ 2 + C (c ^ 4 * a ^ 4 * b ^ 4)

/-- The sextic `f_{a,b,c}` with `cuboidThreePoly a b c = f_{a,b,c}(X²)`. -/
def sextic (a b c y : ℚ) : ℚ :=
  y ^ 6 + (6 * c ^ 2 - 2 * a ^ 2 - 2 * b ^ 2) * y ^ 5
    + (c ^ 4 + b ^ 4 + a ^ 4 + 4 * a ^ 2 * c ^ 2 + 4 * b ^ 2 * c ^ 2 - 12 * b ^ 2 * a ^ 2) * y ^ 4
    + (6 * a ^ 4 * c ^ 2 + 6 * c ^ 2 * b ^ 4 - 8 * a ^ 2 * b ^ 2 * c ^ 2 - 2 * c ^ 4 * a ^ 2
      - 2 * c ^ 4 * b ^ 2 - 2 * a ^ 4 * b ^ 2 - 2 * b ^ 4 * a ^ 2) * y ^ 3
    + (4 * c ^ 2 * b ^ 4 * a ^ 2 + 4 * a ^ 4 * c ^ 2 * b ^ 2 - 12 * c ^ 4 * a ^ 2 * b ^ 2
      + c ^ 4 * a ^ 4 + c ^ 4 * b ^ 4 + a ^ 4 * b ^ 4) * y ^ 2
    + (6 * a ^ 4 * c ^ 2 * b ^ 4 - 2 * c ^ 4 * a ^ 4 * b ^ 2 - 2 * c ^ 4 * a ^ 2 * b ^ 4) * y
    + c ^ 4 * a ^ 4 * b ^ 4

/-- Numerator of Sharipov's auxiliary parameter `z = nn / dd` (in terms of `y = t²`). -/
def nn (a b c y : ℚ) : ℚ := (y + c ^ 2) * (y - b ^ 2) * (y + a ^ 2)

/-- Denominator of Sharipov's auxiliary parameter `z = nn / dd`. -/
def dd (a b c y : ℚ) : ℚ := 2 * (y + b ^ 2) * (y ^ 2 - a ^ 2 * c ^ 2)

/-! ### The descent -/

/-- **Local step.** If a prime `p` divides the squarefree `s`, every integer solution of
`U² + sV² = D²`, `U² + sW² = E²`, `U² + s(V² + W²) = sG²` is divisible by `p`. -/
theorem dvd_of_descent {p s U V W D E G : ℤ} (hp : Prime p) (hs : Squarefree s) (hps : p ∣ s)
    (h1 : U ^ 2 + s * V ^ 2 = D ^ 2) (h2 : U ^ 2 + s * W ^ 2 = E ^ 2)
    (h3 : U ^ 2 + s * (V ^ 2 + W ^ 2) = s * G ^ 2) :
    p ∣ U ∧ p ∣ V ∧ p ∣ W ∧ p ∣ D ∧ p ∣ E ∧ p ∣ G := by
  obtain ⟨s', rfl⟩ := hps
  have hs' : ¬ p ∣ s' := by
    rintro ⟨k, rfl⟩
    exact hp.not_isUnit (hs p ⟨k, by ring⟩)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hU : p ∣ U :=
    hp.dvd_of_dvd_pow (n := 2) ⟨s' * (G ^ 2 - V ^ 2 - W ^ 2), by linear_combination h3⟩
  obtain ⟨U', rfl⟩ := hU
  have hD : p ∣ D :=
    hp.dvd_of_dvd_pow (n := 2) ⟨p * U' ^ 2 + s' * V ^ 2, by linear_combination -h1⟩
  have hE : p ∣ E :=
    hp.dvd_of_dvd_pow (n := 2) ⟨p * U' ^ 2 + s' * W ^ 2, by linear_combination -h2⟩
  obtain ⟨D', rfl⟩ := hD
  obtain ⟨E', rfl⟩ := hE
  have hV : p ∣ V := by
    have h : s' * V ^ 2 = p * (D' ^ 2 - U' ^ 2) :=
      mul_left_cancel₀ hp0 (by linear_combination h1)
    exact hp.dvd_of_dvd_pow (n := 2) ((hp.dvd_or_dvd ⟨_, h⟩).resolve_left hs')
  have hW : p ∣ W := by
    have h : s' * W ^ 2 = p * (E' ^ 2 - U' ^ 2) :=
      mul_left_cancel₀ hp0 (by linear_combination h2)
    exact hp.dvd_of_dvd_pow (n := 2) ((hp.dvd_or_dvd ⟨_, h⟩).resolve_left hs')
  obtain ⟨V', rfl⟩ := hV
  obtain ⟨W', rfl⟩ := hW
  have hG : p ∣ G := by
    have h : s' * G ^ 2 = p * (U' ^ 2 + s' * p * (V' ^ 2 + W' ^ 2)) :=
      mul_left_cancel₀ hp0 (by linear_combination -h3)
    exact hp.dvd_of_dvd_pow (n := 2) ((hp.dvd_or_dvd ⟨_, h⟩).resolve_left hs')
  exact ⟨dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_right _ _,
    dvd_mul_right _ _, hG⟩

/-- **Infinite descent.** If a prime divides the squarefree `s`, the system of `dvd_of_descent`
has only solutions with `U = 0`. -/
theorem eq_zero_of_descent {p s : ℤ} (hp : Prime p) (hs : Squarefree s) (hps : p ∣ s) :
    ∀ (n : ℕ) (U V W D E G : ℤ), U.natAbs = n → U ^ 2 + s * V ^ 2 = D ^ 2 →
      U ^ 2 + s * W ^ 2 = E ^ 2 → U ^ 2 + s * (V ^ 2 + W ^ 2) = s * G ^ 2 → U = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U V W D E G hn h1 h2 h3
    by_contra hU0
    obtain ⟨⟨U', rfl⟩, ⟨V', rfl⟩, ⟨W', rfl⟩, ⟨D', rfl⟩, ⟨E', rfl⟩, ⟨G', rfl⟩⟩ :=
      dvd_of_descent hp hs hps h1 h2 h3
    have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
    have h1' : U' ^ 2 + s * V' ^ 2 = D' ^ 2 := mul_left_cancel₀ hp2 (by linear_combination h1)
    have h2' : U' ^ 2 + s * W' ^ 2 = E' ^ 2 := mul_left_cancel₀ hp2 (by linear_combination h2)
    have h3' : U' ^ 2 + s * (V' ^ 2 + W' ^ 2) = s * G' ^ 2 :=
      mul_left_cancel₀ hp2 (by linear_combination h3)
    have hU' : U' ≠ 0 := by rintro rfl; simp at hU0
    have hlt : U'.natAbs < n := by
      rw [← hn, Int.natAbs_mul]
      have h2 : 2 ≤ p.natAbs := by
        have h0 : p.natAbs ≠ 0 := by simpa using hp.ne_zero
        have h1 : p.natAbs ≠ 1 := by
          intro h; exact hp.not_isUnit (Int.isUnit_iff_natAbs_eq.mpr h)
        omega
      have : 0 < U'.natAbs := Int.natAbs_pos.mpr hU'
      nlinarith
    exact hU' (ih _ hlt U' V' W' D' E' G' rfl h1' h2' h3')

/-- Multiplying a rational by a multiple of its denominator gives an integer. -/
theorem exists_int_mul {x : ℚ} {M : ℤ} (h : (x.den : ℤ) ∣ M) : ∃ z : ℤ, (z : ℚ) = M * x := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k * x.num, ?_⟩
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

/-- **Rational descent.** If `u ≠ 0` and `u² + y v² = D²`, `u² + y w² = E²`,
`u² + y (v² + w²) = y G²` over `ℚ`, then `y` or `−y` is a square. -/
theorem isSquare_or_isSquare_neg_of_descent {y u v w D E G : ℚ} (hu : u ≠ 0)
    (h1 : u ^ 2 + y * v ^ 2 = D ^ 2) (h2 : u ^ 2 + y * w ^ 2 = E ^ 2)
    (h3 : u ^ 2 + y * (v ^ 2 + w ^ 2) = y * G ^ 2) : IsSquare y ∨ IsSquare (-y) := by
  -- write `y = s r²` with `s` squarefree
  obtain ⟨e, s, hes, hsq⟩ := exists_sq_mul_squarefree (y.num * y.den)
  set r : ℚ := (e : ℚ) / y.den with hr
  have hden : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_ne_zero
  have hys : y = s * r ^ 2 := by
    have hmy : ((y.num * y.den : ℤ) : ℚ) = y * (y.den : ℚ) ^ 2 := by
      push_cast; rw [← Rat.mul_den_eq_num]; ring
    have : ((e ^ 2 * s : ℤ) : ℚ) = y * (y.den : ℚ) ^ 2 := by rw [hes]; exact hmy
    rw [hr]; field_simp; push_cast at this; linear_combination -this
  -- clear denominators
  set v₁ := r * v
  set w₁ := r * w
  set G₁ := r * G
  set M : ℤ := u.den * v₁.den * w₁.den * D.den * E.den * G₁.den with hM
  have hM0 : M ≠ 0 := by
    rw [hM]; simp [Rat.den_ne_zero]
  obtain ⟨U, hU⟩ := exists_int_mul (x := u) (M := M)
    ⟨v₁.den * w₁.den * D.den * E.den * G₁.den, by rw [hM]; ring⟩
  obtain ⟨V, hV⟩ := exists_int_mul (x := v₁) (M := M)
    ⟨u.den * w₁.den * D.den * E.den * G₁.den, by rw [hM]; ring⟩
  obtain ⟨W, hW⟩ := exists_int_mul (x := w₁) (M := M)
    ⟨u.den * v₁.den * D.den * E.den * G₁.den, by rw [hM]; ring⟩
  obtain ⟨D', hD⟩ := exists_int_mul (x := D) (M := M)
    ⟨u.den * v₁.den * w₁.den * E.den * G₁.den, by rw [hM]; ring⟩
  obtain ⟨E', hE⟩ := exists_int_mul (x := E) (M := M)
    ⟨u.den * v₁.den * w₁.den * D.den * G₁.den, by rw [hM]; ring⟩
  obtain ⟨G', hG⟩ := exists_int_mul (x := G₁) (M := M)
    ⟨u.den * v₁.den * w₁.den * D.den * E.den, by rw [hM]; ring⟩
  have e1 : U ^ 2 + s * V ^ 2 = D' ^ 2 := by
    have : (U : ℚ) ^ 2 + s * (V : ℚ) ^ 2 = (D' : ℚ) ^ 2 := by
      rw [hU, hV, hD]; rw [hys] at h1; linear_combination (M : ℚ) ^ 2 * h1
    exact_mod_cast this
  have e2 : U ^ 2 + s * W ^ 2 = E' ^ 2 := by
    have : (U : ℚ) ^ 2 + s * (W : ℚ) ^ 2 = (E' : ℚ) ^ 2 := by
      rw [hU, hW, hE]; rw [hys] at h2; linear_combination (M : ℚ) ^ 2 * h2
    exact_mod_cast this
  have e3 : U ^ 2 + s * (V ^ 2 + W ^ 2) = s * G' ^ 2 := by
    have : (U : ℚ) ^ 2 + s * ((V : ℚ) ^ 2 + (W : ℚ) ^ 2) = s * (G' : ℚ) ^ 2 := by
      rw [hU, hV, hW, hG]; rw [hys] at h3; linear_combination (M : ℚ) ^ 2 * h3
    exact_mod_cast this
  have hU0 : U ≠ 0 := by
    intro h
    have : (M : ℚ) * u = 0 := by rw [← hU, h]; simp
    rcases mul_eq_zero.mp this with h' | h'
    · exact hM0 (by exact_mod_cast h')
    · exact hu h'
  have hs1 : s.natAbs = 1 := by
    by_contra hne
    obtain ⟨p, hp, hps⟩ := Int.exists_prime_and_dvd hne
    exact hU0 (eq_zero_of_descent hp hsq hps _ U V W D' E' G' rfl e1 e2 e3)
  rcases Int.natAbs_eq_iff.mp hs1 with h | h
  · left; exact ⟨r, by rw [hys, h]; push_cast; ring⟩
  · right; exact ⟨r, by rw [hys, h]; push_cast; ring⟩

/-! ### Sharipov's parametrization, multiplied by `√y`

With `z = nn/dd`, Sharipov's box over `ℚ(√y)` with unit space diagonal has edges
`√y·u/(y Δ)`, `v/Δ`, `w/Δ` where `Δ = (y + c²)(dd² + nn²)` and `u, v, w` are below. The three
identities say that the two face diagonals through the first edge, and the space diagonal, have the
predicted form. The first two need `f_{a,b,c}(y) = 0`; the cofactors were computed with PARI/GP. -/

/-- The scaled edge `u` (Sharipov's `x₁`, times `√y·(y + c²)(dd² + nn²)`). -/
def uu (a b c y : ℚ) : ℚ := 2 * c * y * (dd a b c y ^ 2 + nn a b c y ^ 2)

/-- The scaled edge `v` (Sharipov's `x₂`). -/
def vv (a b c y : ℚ) : ℚ := 2 * nn a b c y * dd a b c y * (y - c ^ 2)

/-- The scaled edge `w` (Sharipov's `x₃`). -/
def ww (a b c y : ℚ) : ℚ := (y - c ^ 2) * (dd a b c y ^ 2 - nn a b c y ^ 2)

/-- The scaled face diagonal over the edges `u, v` (Sharipov's `d₃`). -/
def diagD (a b c y : ℚ) : ℚ := 2 * a * (c ^ 2 * nn a b c y ^ 2 + y * dd a b c y ^ 2)

/-- The scaled face diagonal over the edges `u, w` (Sharipov's `d₂`). -/
def diagE (a b c y : ℚ) : ℚ :=
  b * ((y + c ^ 2) * (dd a b c y ^ 2 + nn a b c y ^ 2) + 2 * nn a b c y * dd a b c y * (y - c ^ 2))

/-- The scaled space diagonal. -/
def diagG (a b c y : ℚ) : ℚ := (y + c ^ 2) * (dd a b c y ^ 2 + nn a b c y ^ 2)

set_option maxHeartbeats 4000000 in
-- `linear_combination` normalises a degree-28 identity in four variables
/-- First face: `u² + y v² = D²` modulo `f_{a,b,c}(y) = 0`. -/
theorem sextic_identity_one {a b c y : ℚ} (hf : sextic a b c y = 0) :
    uu a b c y ^ 2 + y * vv a b c y ^ 2 = diagD a b c y ^ 2 := by
  unfold sextic at hf
  unfold uu vv diagD nn dd
  linear_combination (
      16*y^9 + (32*b^2 + 4*c^2)*y^8 + (-40*c^2*a^2 + (16*b^4 - 8*c^2*b^2 + 8*c^4))*y^7
      + (4*c^2*a^4 + (-112*c^2*b^2 + 12*c^4)*a^2 + (4*c^2*b^4 - 16*c^4*b^2 + 4*c^6))*y^6
      + ((-8*c^2*b^2 + 48*c^4)*a^4 + (-40*c^2*b^4 - 24*c^4*b^2)*a^2 + (8*c^4*b^4
      - 8*c^6*b^2))*y^5 + (-4*c^4*a^6 + (4*c^2*b^4 + 96*c^4*b^2 - 12*c^6)*a^4
      + (12*c^4*b^4 - 4*c^8)*a^2 + 4*c^6*b^4)*y^4 + ((8*c^4*b^2 - 24*c^6)*a^6
      + (48*c^4*b^4 + 24*c^6*b^2 - 8*c^8)*a^4 + 8*c^8*b^2*a^2)*y^3 + ((-4*c^4*b^4
      - 16*c^6*b^2 - 4*c^8)*a^6 + (-12*c^6*b^4 + 16*c^8*b^2)*a^4 - 4*c^8*b^4*a^2)*y^2
      + ((-24*c^6*b^4 + 8*c^8*b^2)*a^6 - 8*c^8*b^4*a^4)*y - 4*c^8*b^4*a^6) * hf

set_option maxHeartbeats 4000000 in
-- `linear_combination` normalises a degree-28 identity in four variables
/-- Second face: `u² + y w² = E²` modulo `f_{a,b,c}(y) = 0`. -/
theorem sextic_identity_two {a b c y : ℚ} (hf : sextic a b c y = 0) :
    uu a b c y ^ 2 + y * ww a b c y ^ 2 = diagE a b c y ^ 2 := by
  unfold sextic at hf
  unfold uu ww diagE nn dd
  linear_combination (
      9*y^9 + (6*a^2 + (-3*b^2 + 16*c^2))*y^8 + (a^4 - 10*b^2*a^2 + (-5*b^4 - 8*c^2*b^2
      + 6*c^4))*y^7 + (-3*b^2*a^4 + (2*b^4 - 32*c^2*b^2 - 12*c^4)*a^2 + (-b^6
      - 10*c^4*b^2))*y^6 + ((3*b^4 - 8*c^2*b^2 + 6*c^4)*a^4 + (2*b^6 + 32*c^2*b^4
      - 44*c^4*b^2)*a^2 + (-8*c^2*b^6 + 18*c^4*b^4 - 8*c^6*b^2 + c^8))*y^5 + ((-b^6
      + 16*c^2*b^4 - 10*c^4*b^2 + 16*c^6)*a^4 + (60*c^4*b^4 - 32*c^6*b^2 + 6*c^8)*a^2
      + (-14*c^4*b^6 + 16*c^6*b^4 - 3*c^8*b^2))*y^4 + ((-8*c^2*b^6 + 18*c^4*b^4
      - 8*c^6*b^2 + 9*c^8)*a^4 + (-4*c^4*b^6 + 32*c^6*b^4 - 10*c^8*b^2)*a^2
      + (-8*c^6*b^6 + 3*c^8*b^4))*y^3 + ((-14*c^4*b^6 - 3*c^8*b^2)*a^4 + 2*c^8*b^4*a^2
      - c^8*b^6)*y^2 + ((-8*c^6*b^6 - 5*c^8*b^4)*a^4 + 2*c^8*b^6*a^2)*y - c^8*b^6*a^4) * hf

/-- Space diagonal: `u² + y (v² + w²) = y G²`, an identity. -/
theorem sextic_identity_three (a b c y : ℚ) :
    uu a b c y ^ 2 + y * (vv a b c y ^ 2 + ww a b c y ^ 2) = y * diagG a b c y ^ 2 := by
  unfold uu vv ww diagG
  ring

/-- Third face: `v² + w² = ((y − c²)(dd² + nn²))²`, an identity. -/
theorem sextic_identity_four (a b c y : ℚ) :
    vv a b c y ^ 2 + ww a b c y ^ 2 = ((y - c ^ 2) * (dd a b c y ^ 2 + nn a b c y ^ 2)) ^ 2 := by
  unfold vv ww
  ring

/-! ### The main theorem -/

/-- **Main theorem.** For rationals `a, b, c` with `c ≠ 0`, every nonzero rational root of the
third cuboid sextic `f_{a,b,c}` is a square or minus a square. -/
theorem isSquare_or_isSquare_neg_of_sextic_eq_zero {a b c y : ℚ} (hc : c ≠ 0) (hy : y ≠ 0)
    (hf : sextic a b c y = 0) : IsSquare y ∨ IsSquare (-y) := by
  by_cases h : dd a b c y ^ 2 + nn a b c y ^ 2 = 0
  · -- degenerate parametrization: `nn = 0`, so `y ∈ {−c², b², −a²}`
    have hn : nn a b c y = 0 := by nlinarith [sq_nonneg (dd a b c y), sq_nonneg (nn a b c y)]
    unfold nn at hn
    rcases mul_eq_zero.mp hn with hn | hn
    · rcases mul_eq_zero.mp hn with hn | hn
      · right; exact ⟨c, by linear_combination -hn⟩
      · left; exact ⟨b, by linear_combination hn⟩
    · right; exact ⟨a, by linear_combination -hn⟩
  · refine isSquare_or_isSquare_neg_of_descent ?_ (sextic_identity_one hf)
      (sextic_identity_two hf) (sextic_identity_three a b c y)
    unfold uu
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hc) hy) h

/-- The value of `cuboidThreePoly a b c` at a complex `z` with `z² = r` is `f_{a,b,c}(r)`. -/
theorem aeval_cuboidThreePoly {a b c r : ℤ} {z : ℂ} (hz : z ^ 2 = r) :
    aeval z (cuboidThreePoly a b c) = ((sextic a b c r : ℚ) : ℂ) := by
  simp only [cuboidThreePoly, map_add, map_sub, map_mul, map_pow, map_intCast, map_ofNat,
    aeval_X, eq_intCast]
  rw [show z ^ 12 = (z ^ 2) ^ 6 by ring, show z ^ 10 = (z ^ 2) ^ 5 by ring,
    show z ^ 8 = (z ^ 2) ^ 4 by ring, show z ^ 6 = (z ^ 2) ^ 3 by ring,
    show z ^ 4 = (z ^ 2) ^ 2 by ring, hz]
  simp only [sextic]
  push_cast
  ring

/-- If `X² − r` divides the third cuboid polynomial then `f_{a,b,c}(r) = 0`. -/
theorem sextic_eq_zero_of_dvd {a b c r : ℤ} (h : X ^ 2 - C r ∣ cuboidThreePoly a b c) :
    sextic a b c r = 0 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((r : ℂ)) two_pos
  obtain ⟨Q, hQ⟩ := h
  have h0 : aeval z (cuboidThreePoly a b c) = 0 := by
    rw [hQ, map_mul]
    simp [hz]
  rw [aeval_cuboidThreePoly hz] at h0
  exact_mod_cast h0

/-- **Corollary (even quadratic factors).** If `X² − r` divides the third cuboid polynomial in
`ℤ[X]` and `c ≠ 0`, then `r` or `−r` is a perfect square. -/
theorem isSquare_or_isSquare_neg_of_dvd {a b c r : ℤ} (hc : c ≠ 0)
    (h : X ^ 2 - C r ∣ cuboidThreePoly a b c) : IsSquare r ∨ IsSquare (-r) := by
  rcases eq_or_ne r 0 with rfl | hr
  · exact Or.inl ⟨0, by simp⟩
  have := isSquare_or_isSquare_neg_of_sextic_eq_zero (a := a) (b := b) (c := c) (y := r)
    (by exact_mod_cast hc) (by exact_mod_cast hr) (sextic_eq_zero_of_dvd h)
  rcases this with h' | h'
  · exact Or.inl (Rat.isSquare_intCast_iff.mp h')
  · exact Or.inr (Rat.isSquare_intCast_iff.mp (by push_cast; exact h'))

/-- In particular a positive non-square `r` never gives a factor `X² − r`. -/
theorem not_dvd_of_not_isSquare {a b c r : ℤ} (hc : c ≠ 0) (hr : 0 < r) (hsq : ¬ IsSquare r) :
    ¬ X ^ 2 - C r ∣ cuboidThreePoly a b c := by
  intro h
  rcases isSquare_or_isSquare_neg_of_dvd hc h with h' | ⟨m, hm⟩
  · exact hsq h'
  · nlinarith [mul_self_nonneg m]

/-! ### From a rational root to a perfect cuboid (Sharipov's Theorem 1.1, one direction) -/

/-- The exceptional triples of the conjecture, as one polynomial: `excPoly a b c = 0` iff one of
`a, b, c` is `0`, two of `a², b², c²` agree, `a c = ±b²` or `b c = ±a²`. For positive `a, b, c`,
`excPoly a b c ≠ 0` is exactly the conjecture's hypothesis apart from coprimality. -/
def excPoly (a b c : ℚ) : ℚ :=
  a * b * c * (a ^ 2 - b ^ 2) * (a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) * (a * c - b ^ 2) *
    (a * c + b ^ 2) * (b * c - a ^ 2) * (b * c + a ^ 2)

/-- The nonzero factors of a non-exceptional triple. -/
theorem factors_ne_zero {a b c : ℚ} (hE : excPoly a b c ≠ 0) :
    a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a - b ≠ 0 ∧ a + b ≠ 0 ∧ a - c ≠ 0 ∧ a + c ≠ 0 ∧ b - c ≠ 0 ∧
      b + c ≠ 0 ∧ a * c - b ^ 2 ≠ 0 ∧ a * c + b ^ 2 ≠ 0 ∧ b * c - a ^ 2 ≠ 0 ∧
      b * c + a ^ 2 ≠ 0 := by
  unfold excPoly at hE
  simp only [ne_eq, mul_eq_zero, not_or] at hE
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hac⟩, hbc⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hE
  refine ⟨ha, hb, hc, ?_, ?_, ?_, ?_, ?_, ?_, h1, h2, h3, h4⟩ <;> intro h
  · exact hab (by linear_combination (a + b) * h)
  · exact hab (by linear_combination (a - b) * h)
  · exact hac (by linear_combination (a + c) * h)
  · exact hac (by linear_combination (a - c) * h)
  · exact hbc (by linear_combination (b + c) * h)
  · exact hbc (by linear_combination (b - c) * h)

set_option maxHeartbeats 4000000 in
-- `linear_combination` normalises a large resultant certificate
/-- Resultant certificate: on a root, `nn ≠ dd` unless the triple is exceptional. -/
theorem nn_sub_dd_ne_zero {a b c y : ℚ} (hE : excPoly a b c ≠ 0) (hf : sextic a b c y = 0) :
    nn a b c y - dd a b c y ≠ 0 := by
  intro h
  obtain ⟨ha, hb, hc, hab, hab', hac, hac', hbc, hbc', h1, h2, -, -⟩ := factors_ne_zero hE
  have hR : -2048 * c ^ 4 * b ^ 4 * (b - c) ^ 4 * (b + c) ^ 4 * a ^ 6 * (a - b) ^ 2 * (a + b) ^ 2 *
      (a - c) ^ 3 * (a + c) ^ 3 * (c * a - b ^ 2) * (c * a + b ^ 2) = 0 := by
    unfold sextic at hf
    unfold nn dd at h
    linear_combination (
      ((-256*c^2*b^6 + 896*c^4*b^4 - 1024*c^6*b^2 + 384*c^8)*a^12 + (256*b^10
      - 256*c^2*b^8 - 1408*c^6*b^4 + 2560*c^8*b^2 - 1152*c^10)*a^10 + (-512*b^12
      - 256*c^2*b^10 + 2304*c^4*b^8 - 1024*c^6*b^6 - 128*c^8*b^4 - 1536*c^10*b^2
      + 1152*c^12)*a^8 + (256*b^14 + 2304*c^2*b^12 - 7168*c^4*b^10 + 6656*c^6*b^8
      - 3584*c^8*b^6 + 2432*c^10*b^4 - 512*c^12*b^2 - 384*c^14)*a^6 + (-1536*c^2*b^14
      + 3584*c^4*b^12 - 2432*c^6*b^10 + 640*c^8*b^8 - 128*c^10*b^6 - 640*c^12*b^4
      + 512*c^14*b^2)*a^4 + (384*c^4*b^14 - 640*c^6*b^12 - 256*c^8*b^10 + 768*c^10*b^8
      - 128*c^12*b^6 - 128*c^14*b^4)*a^2 + (-128*c^6*b^14 + 384*c^8*b^12 - 384*c^10*b^10
      + 128*c^12*b^8))*y^2 + ((256*c^2*b^6 - 896*c^4*b^4 + 1024*c^6*b^2 - 384*c^8)*a^14
      + (-256*b^10 - 512*c^2*b^8 + 2816*c^4*b^6 - 2304*c^6*b^4 - 512*c^8*b^2
      + 768*c^10)*a^12 + (1280*b^12 - 512*c^2*b^10 - 2816*c^4*b^8 - 2048*c^6*b^6
      + 8192*c^8*b^4 - 4096*c^10*b^2)*a^10 + (-1792*b^14 - 3072*c^2*b^12
      + 16640*c^4*b^10 - 15872*c^6*b^8 + 6656*c^8*b^6 - 6912*c^10*b^4 + 5120*c^12*b^2
      - 768*c^14)*a^8 + (768*b^16 + 8448*c^2*b^14 - 29696*c^4*b^12 + 34816*c^6*b^10
      - 22528*c^8*b^8 + 12288*c^10*b^6 - 3456*c^12*b^4 - 1024*c^14*b^2 + 384*c^16)*a^6
      + (-4608*c^2*b^16 + 12800*c^4*b^14 - 12928*c^6*b^12 + 7424*c^8*b^10
      - 3072*c^10*b^8 - 1280*c^12*b^6 + 2176*c^14*b^4 - 512*c^16*b^2)*a^4
      + (1152*c^4*b^16 - 2304*c^6*b^14 - 128*c^8*b^12 + 2560*c^10*b^10 - 1152*c^12*b^8
      - 256*c^14*b^6 + 128*c^16*b^4)*a^2 + (-384*c^6*b^16 + 1280*c^8*b^14
      - 1536*c^10*b^12 + 768*c^12*b^10 - 128*c^14*b^8))*y + ((-256*c^2*b^8
      + 1792*c^4*b^6 - 3968*c^6*b^4 + 3584*c^8*b^2 - 1152*c^10)*a^14 + (256*b^12
      - 1280*c^2*b^10 + 1024*c^4*b^8 - 1024*c^6*b^6 + 6272*c^8*b^4 - 8704*c^10*b^2
      + 3456*c^12)*a^12 + (-512*b^14 + 2816*c^2*b^12 - 2816*c^4*b^10 + 2048*c^6*b^8
      - 6656*c^8*b^6 + 3968*c^10*b^4 + 4608*c^12*b^2 - 3456*c^14)*a^10 + (256*b^16
      - 768*c^2*b^14 - 3072*c^4*b^12 + 6656*c^6*b^10 - 3584*c^8*b^8 + 6656*c^10*b^6
      - 9856*c^12*b^4 + 2560*c^14*b^2 + 1152*c^16)*a^8 + (-512*c^2*b^16 + 1536*c^4*b^14
      + 3584*c^6*b^12 - 11264*c^8*b^10 + 6656*c^10*b^8 - 512*c^12*b^6 + 2560*c^14*b^4
      - 2048*c^16*b^2)*a^6 + (1536*c^4*b^16 - 7168*c^6*b^14 + 10368*c^8*b^12
      - 4480*c^10*b^10 - 128*c^12*b^8 - 1152*c^14*b^6 + 1024*c^16*b^4)*a^4
      + (-128*c^6*b^16 + 1408*c^8*b^14 - 3328*c^10*b^12 + 2816*c^12*b^10 - 640*c^14*b^8
      - 128*c^16*b^6)*a^2 + (-128*c^8*b^16 + 384*c^10*b^14 - 384*c^12*b^12
      + 128*c^14*b^10))) * hf + (
      ((-256*c^2*b^6 + 896*c^4*b^4 - 1024*c^6*b^2 + 384*c^8)*a^12 + (256*b^10
      - 256*c^2*b^8 - 1408*c^6*b^4 + 2560*c^8*b^2 - 1152*c^10)*a^10 + (-512*b^12
      - 256*c^2*b^10 + 2304*c^4*b^8 - 1024*c^6*b^6 - 128*c^8*b^4 - 1536*c^10*b^2
      + 1152*c^12)*a^8 + (256*b^14 + 2304*c^2*b^12 - 7168*c^4*b^10 + 6656*c^6*b^8
      - 3584*c^8*b^6 + 2432*c^10*b^4 - 512*c^12*b^2 - 384*c^14)*a^6 + (-1536*c^2*b^14
      + 3584*c^4*b^12 - 2432*c^6*b^10 + 640*c^8*b^8 - 128*c^10*b^6 - 640*c^12*b^4
      + 512*c^14*b^2)*a^4 + (384*c^4*b^14 - 640*c^6*b^12 - 256*c^8*b^10 + 768*c^10*b^8
      - 128*c^12*b^6 - 128*c^14*b^4)*a^2 + (-128*c^6*b^14 + 384*c^8*b^12 - 384*c^10*b^10
      + 128*c^12*b^8))*y^5 + ((512*c^2*b^6 - 1792*c^4*b^4 + 2048*c^6*b^2 - 768*c^8)*a^14
      + (-512*b^10 + 1024*c^2*b^8 - 3456*c^4*b^6 + 10496*c^6*b^4 - 12160*c^8*b^2
      + 4608*c^10)*a^12 + (512*b^12 + 2816*c^2*b^10 - 6912*c^4*b^8 + 6016*c^6*b^6
      - 14336*c^8*b^4 + 21120*c^10*b^2 - 9216*c^12)*a^10 + (512*b^14 - 7680*c^2*b^12
      + 10496*c^4*b^10 - 1280*c^6*b^8 + 3712*c^8*b^6 - 2560*c^10*b^4 - 10880*c^12*b^2
      + 7680*c^14)*a^8 + (-512*b^16 + 256*c^2*b^14 + 18688*c^4*b^12 - 46208*c^6*b^10
      + 41344*c^8*b^8 - 24832*c^10*b^6 + 16768*c^12*b^4 - 3200*c^14*b^2 - 2304*c^16)*a^6
      + (3072*c^2*b^16 - 16256*c^4*b^14 + 24960*c^6*b^12 - 12544*c^8*b^10
      + 1280*c^10*b^8 + 1152*c^12*b^6 - 4736*c^14*b^4 + 3072*c^16*b^2)*a^4
      + (-768*c^4*b^16 + 3712*c^6*b^14 - 3712*c^8*b^12 - 2688*c^10*b^10 + 4736*c^12*b^8
      - 512*c^14*b^6 - 768*c^16*b^4)*a^2 + (256*c^6*b^16 - 1536*c^8*b^14
      + 3072*c^10*b^12 - 2560*c^12*b^10 + 768*c^14*b^8))*y^4 + ((-256*c^2*b^6
      + 896*c^4*b^4 - 1024*c^6*b^2 + 384*c^8)*a^16 + (256*b^10 + 2816*c^2*b^8
      - 11520*c^4*b^6 + 13952*c^6*b^4 - 5888*c^8*b^2 + 384*c^10)*a^14 + (-3584*b^12
      + 3072*c^2*b^10 + 3072*c^4*b^8 + 14336*c^6*b^6 - 35328*c^8*b^4 + 21504*c^10*b^2
      - 3072*c^12)*a^12 + (6656*b^14 + 4608*c^2*b^12 - 38912*c^4*b^10 + 29184*c^6*b^8
      - 6656*c^8*b^6 + 21504*c^10*b^4 - 19456*c^12*b^2 + 3072*c^14)*a^10 + (-3584*b^16
      - 29952*c^2*b^14 + 98048*c^4*b^12 - 96768*c^6*b^10 + 54784*c^8*b^8
      - 37376*c^10*b^6 + 11648*c^12*b^4 + 3584*c^14*b^2 - 384*c^16)*a^8 + (256*b^18
      + 21248*c^2*b^16 - 43008*c^4*b^14 + 7424*c^6*b^12 + 28672*c^8*b^10
      - 24576*c^10*b^8 + 19200*c^12*b^6 - 9600*c^14*b^4 + 768*c^16*b^2 - 384*c^18)*a^6
      + (-1536*c^2*b^18 - 8960*c^4*b^16 + 30336*c^6*b^14 - 26752*c^8*b^12
      + 9216*c^10*b^10 - 4352*c^12*b^8 + 1408*c^14*b^6 + 128*c^16*b^4
      + 512*c^18*b^2)*a^4 + (384*c^4*b^18 + 2688*c^6*b^16 - 9088*c^8*b^14
      + 8320*c^10*b^12 - 2944*c^12*b^10 + 1408*c^14*b^8 - 640*c^16*b^6
      - 128*c^18*b^4)*a^2 + (-128*c^6*b^18 - 128*c^8*b^16 + 1024*c^10*b^14
      - 1024*c^12*b^12 + 128*c^14*b^10 + 128*c^16*b^8))*y^3 + ((512*c^2*b^8
      - 3456*c^4*b^6 + 7680*c^6*b^4 - 7040*c^8*b^2 + 2304*c^10)*a^16 + (-512*b^12
      + 2816*c^2*b^10 - 768*c^4*b^8 - 3712*c^6*b^6 - 6656*c^8*b^4 + 16512*c^10*b^2
      - 7680*c^12)*a^14 + (512*b^14 - 7680*c^2*b^12 + 7680*c^4*b^10 + 1024*c^6*b^8
      + 14336*c^8*b^6 - 17920*c^10*b^4 - 7168*c^12*b^2 + 9216*c^14)*a^12 + (512*b^16
      + 9728*c^2*b^14 - 9216*c^4*b^12 - 9216*c^6*b^10 - 4096*c^8*b^8 + 4608*c^10*b^6
      + 19456*c^12*b^4 - 7168*c^14*b^2 - 4608*c^16)*a^10 + (-512*b^18 - 10240*c^2*b^16
      + 7424*c^4*b^14 + 19712*c^6*b^12 - 16384*c^8*b^10 + 14848*c^10*b^8
      - 24960*c^12*b^6 + 4352*c^14*b^4 + 4992*c^16*b^2 + 768*c^18)*a^8 + (4864*c^2*b^18
      + 7424*c^4*b^16 - 43648*c^6*b^14 + 57216*c^8*b^12 - 51712*c^10*b^10
      + 34816*c^12*b^8 - 3840*c^14*b^6 - 4992*c^16*b^4 - 128*c^18*b^2)*a^6
      + (-9088*c^4*b^18 + 25728*c^6*b^16 - 32128*c^8*b^14 + 30080*c^10*b^12
      - 17536*c^12*b^10 - 1664*c^14*b^8 + 5504*c^16*b^6 - 896*c^18*b^4)*a^4
      + (2432*c^6*b^18 - 4480*c^8*b^16 - 1280*c^10*b^14 + 6144*c^12*b^12
      - 2432*c^14*b^10 - 640*c^16*b^8 + 256*c^18*b^6)*a^2 + (-768*c^8*b^18
      + 2560*c^10*b^16 - 3072*c^12*b^14 + 1536*c^14*b^12 - 256*c^16*b^10))*y^2
      + ((-256*c^2*b^10 + 256*c^4*b^8 + 768*c^6*b^6 - 896*c^8*b^4 - 256*c^10*b^2
      + 384*c^12)*a^16 + (256*b^14 + 256*c^2*b^12 - 1024*c^4*b^10 + 5120*c^6*b^8
      - 15872*c^8*b^6 + 16512*c^10*b^4 - 4096*c^12*b^2 - 1152*c^14)*a^14 + (-512*b^16
      - 768*c^2*b^14 + 256*c^4*b^12 - 1536*c^8*b^8 + 25088*c^10*b^6 - 37504*c^12*b^4
      + 13824*c^14*b^2 + 1152*c^16)*a^12 + (256*b^18 + 1792*c^2*b^16 - 5120*c^4*b^14
      + 16896*c^6*b^12 - 19968*c^8*b^10 - 8192*c^10*b^8 + 6656*c^12*b^6 + 22400*c^14*b^4
      - 14336*c^16*b^2 - 384*c^18)*a^10 + (-1024*c^2*b^18 + 12288*c^4*b^16
      - 48128*c^6*b^14 + 64512*c^8*b^12 - 32768*c^10*b^10 + 25088*c^12*b^8
      - 30976*c^14*b^6 + 6144*c^16*b^4 + 4864*c^18*b^2)*a^8 + (-6656*c^4*b^18
      + 19968*c^6*b^16 - 3840*c^8*b^14 - 31744*c^10*b^12 + 25088*c^12*b^10
      - 6144*c^14*b^8 + 9984*c^16*b^6 - 6656*c^18*b^4)*a^6 + (5376*c^6*b^18
      - 21504*c^8*b^16 + 26496*c^10*b^14 - 6528*c^12*b^12 - 4992*c^14*b^10
      - 1152*c^16*b^8 + 2304*c^18*b^6)*a^4 + (-896*c^8*b^18 + 4992*c^10*b^16
      - 9472*c^12*b^14 + 7424*c^14*b^12 - 1920*c^16*b^10 - 128*c^18*b^8)*a^2
      + (-128*c^10*b^18 + 384*c^12*b^16 - 384*c^14*b^14 + 128*c^16*b^12))*y
      + ((-1792*c^4*b^10 + 6400*c^6*b^8 - 8320*c^8*b^6 + 4608*c^10*b^4
      - 896*c^12*b^2)*a^16 + (1792*c^2*b^14 - 2816*c^4*b^12 + 1024*c^6*b^10
      - 7168*c^8*b^8 + 16256*c^10*b^6 - 11776*c^12*b^4 + 2688*c^14*b^2)*a^14
      + (-3584*c^2*b^16 + 5376*c^4*b^14 - 1280*c^6*b^12 + 8192*c^8*b^10 - 13824*c^10*b^8
      + 128*c^12*b^6 + 7680*c^14*b^4 - 2688*c^16*b^2)*a^12 + (1792*c^2*b^18
      + 4864*c^4*b^16 - 21504*c^6*b^14 + 22016*c^8*b^12 - 16896*c^10*b^10
      + 22016*c^12*b^8 - 14720*c^14*b^6 + 1536*c^16*b^4 + 896*c^18*b^2)*a^10
      + (-5632*c^4*b^18 + 10752*c^6*b^16 + 512*c^8*b^14 - 9216*c^10*b^12
      + 3584*c^12*b^10 - 3584*c^14*b^8 + 5632*c^16*b^6 - 2048*c^18*b^4)*a^8
      + (4608*c^6*b^18 - 13312*c^8*b^16 + 12160*c^10*b^14 - 3712*c^12*b^12
      + 2176*c^14*b^10 - 2944*c^16*b^8 + 1024*c^18*b^6)*a^6 + (-1920*c^8*b^18
      + 6784*c^10*b^16 - 8960*c^12*b^14 + 5376*c^14*b^12 - 1408*c^16*b^10
      + 128*c^18*b^8)*a^4 + (128*c^10*b^18 - 384*c^12*b^16 + 384*c^14*b^14
      - 128*c^16*b^12)*a^2)) * h
  have h1' : c * a - b ^ 2 ≠ 0 := by rw [mul_comm]; exact h1
  have h2' : c * a + b ^ 2 ≠ 0 := by rw [mul_comm]; exact h2
  revert hR
  repeat' apply mul_ne_zero
  all_goals first | assumption | exact pow_ne_zero _ ‹_› | norm_num

set_option maxHeartbeats 4000000 in
-- `linear_combination` normalises a large resultant certificate
/-- Resultant certificate: on a root, `nn ≠ −dd` unless the triple is exceptional. -/
theorem nn_add_dd_ne_zero {a b c y : ℚ} (hE : excPoly a b c ≠ 0) (hf : sextic a b c y = 0) :
    nn a b c y + dd a b c y ≠ 0 := by
  intro h
  obtain ⟨ha, hb, hc, hab, hab', hac, hac', hbc, hbc', h1, h2, h3, h4⟩ := factors_ne_zero hE
  have hR : -2048 * c ^ 4 * b ^ 4 * (b - c) ^ 3 * (b + c) ^ 3 * a ^ 4 * (a - b) ^ 2 * (a + b) ^ 2 *
      (a - c) ^ 3 * (a + c) ^ 3 * (c * a - b ^ 2) * (c * a + b ^ 2) * (a ^ 2 - c * b) *
      (a ^ 2 + c * b) = 0 := by
    unfold sextic at hf
    unfold nn dd at h
    linear_combination (
      ((-768*c^2*b^4 - 1920*c^4*b^2 - 384*c^6)*a^14 + (768*b^8 + 3072*c^2*b^6
      + 4608*c^4*b^4 + 5760*c^6*b^2 + 1152*c^8)*a^12 + (-1536*b^10 - 2304*c^2*b^8
      - 11520*c^4*b^6 - 8832*c^6*b^4 - 5376*c^8*b^2 - 1152*c^10)*a^10 + (768*b^12
      - 2304*c^2*b^10 + 18432*c^4*b^8 + 1536*c^6*b^6 + 11136*c^8*b^4 + 768*c^10*b^2
      + 384*c^12)*a^8 + (3072*c^2*b^12 - 11520*c^4*b^10 + 1536*c^6*b^8 - 6144*c^8*b^6
      - 3456*c^10*b^4 + 1152*c^12*b^2)*a^6 + (-768*c^2*b^14 + 4608*c^4*b^12
      - 8832*c^6*b^10 + 11136*c^8*b^8 - 3456*c^10*b^6 + 768*c^12*b^4 - 384*c^14*b^2)*a^4
      + (-1920*c^4*b^14 + 5760*c^6*b^12 - 5376*c^8*b^10 + 768*c^10*b^8 + 1152*c^12*b^6
      - 384*c^14*b^4)*a^2 + (-384*c^6*b^14 + 1152*c^8*b^12 - 1152*c^10*b^10
      + 384*c^12*b^8))*y^2 + ((-256*c^2*b^4 - 640*c^4*b^2 - 128*c^6)*a^16 + (256*b^8
      + 768*c^2*b^6 + 2560*c^4*b^4 + 2304*c^6*b^2 + 256*c^8)*a^14 + (-256*b^10
      - 1792*c^2*b^8 - 4352*c^4*b^6 - 6016*c^6*b^4 - 2944*c^8*b^2)*a^12 + (-256*b^12
      + 2560*c^2*b^10 + 2304*c^4*b^8 + 10240*c^6*b^6 + 4352*c^8*b^4 + 1536*c^10*b^2
      - 256*c^12)*a^10 + (256*b^14 - 1792*c^2*b^12 + 2304*c^4*b^10 - 11264*c^6*b^8
      - 3584*c^8*b^6 - 1024*c^10*b^4 - 384*c^12*b^2 + 128*c^14)*a^8 + (768*c^2*b^14
      - 4352*c^4*b^12 + 10240*c^6*b^10 - 3584*c^8*b^8 + 4096*c^10*b^6 - 1280*c^12*b^4
      + 256*c^14*b^2)*a^6 + (-256*c^2*b^16 + 2560*c^4*b^14 - 6016*c^6*b^12
      + 4352*c^8*b^10 - 1024*c^10*b^8 - 1280*c^12*b^6 + 768*c^14*b^4 - 128*c^16*b^2)*a^4
      + (-640*c^4*b^16 + 2304*c^6*b^14 - 2944*c^8*b^12 + 1536*c^10*b^10 - 384*c^12*b^8
      + 256*c^14*b^6 - 128*c^16*b^4)*a^2 + (-128*c^6*b^16 + 256*c^8*b^14 - 256*c^12*b^10
      + 128*c^14*b^8))*y + ((256*c^2*b^6 + 1536*c^4*b^4 + 1152*c^6*b^2 + 128*c^8)*a^16
      + (-256*b^10 - 2048*c^2*b^8 - 3072*c^4*b^6 - 6656*c^6*b^4 - 2944*c^8*b^2
      - 384*c^10)*a^14 + (512*b^12 + 1792*c^2*b^10 + 7424*c^4*b^8 + 8704*c^6*b^6
      + 10112*c^8*b^4 + 1792*c^10*b^2 + 384*c^12)*a^12 + (-256*b^14 + 1792*c^2*b^12
      - 11776*c^4*b^10 - 3584*c^6*b^8 - 11264*c^8*b^6 - 6272*c^10*b^4 + 768*c^12*b^2
      - 128*c^14)*a^10 + (-2048*c^2*b^14 + 7424*c^4*b^12 - 3584*c^6*b^10 + 11776*c^8*b^8
      + 1024*c^10*b^6 + 1664*c^12*b^4 - 896*c^14*b^2)*a^8 + (256*c^2*b^16
      - 3072*c^4*b^14 + 8704*c^6*b^12 - 11264*c^8*b^10 + 1024*c^10*b^8 + 2048*c^12*b^6
      - 896*c^14*b^4 + 128*c^16*b^2)*a^6 + (1536*c^4*b^16 - 6656*c^6*b^14
      + 10112*c^8*b^12 - 6272*c^10*b^10 + 1664*c^12*b^8 - 896*c^14*b^6
      + 512*c^16*b^4)*a^4 + (1152*c^6*b^16 - 2944*c^8*b^14 + 1792*c^10*b^12
      + 768*c^12*b^10 - 896*c^14*b^8 + 128*c^16*b^6)*a^2 + (128*c^8*b^16 - 384*c^10*b^14
      + 384*c^12*b^12 - 128*c^14*b^10))) * hf + (
      ((256*c^2*b^4 + 640*c^4*b^2 + 128*c^6)*a^14 + (-256*b^8 - 1024*c^2*b^6
      - 1536*c^4*b^4 - 1920*c^6*b^2 - 384*c^8)*a^12 + (512*b^10 + 768*c^2*b^8
      + 3840*c^4*b^6 + 2944*c^6*b^4 + 1792*c^8*b^2 + 384*c^10)*a^10 + (-256*b^12
      + 768*c^2*b^10 - 6144*c^4*b^8 - 512*c^6*b^6 - 3712*c^8*b^4 - 256*c^10*b^2
      - 128*c^12)*a^8 + (-1024*c^2*b^12 + 3840*c^4*b^10 - 512*c^6*b^8 + 2048*c^8*b^6
      + 1152*c^10*b^4 - 384*c^12*b^2)*a^6 + (256*c^2*b^14 - 1536*c^4*b^12
      + 2944*c^6*b^10 - 3712*c^8*b^8 + 1152*c^10*b^6 - 256*c^12*b^4 + 128*c^14*b^2)*a^4
      + (640*c^4*b^14 - 1920*c^6*b^12 + 1792*c^8*b^10 - 256*c^10*b^8 - 384*c^12*b^6
      + 128*c^14*b^4)*a^2 + (128*c^6*b^14 - 384*c^8*b^12 + 384*c^10*b^10
      - 128*c^12*b^8))*y^5 + ((-512*c^2*b^4 - 1280*c^4*b^2 - 256*c^6)*a^16 + (512*b^8
      + 1536*c^2*b^6 + 2688*c^4*b^4 + 7040*c^6*b^2 + 1536*c^8)*a^14 + (-512*b^10
      - 256*c^2*b^8 - 9728*c^4*b^6 - 9088*c^6*b^4 - 13184*c^8*b^2 - 3072*c^10)*a^12
      + (-512*b^12 - 1536*c^2*b^10 + 8960*c^4*b^8 + 12672*c^6*b^6 + 19712*c^8*b^4
      + 9344*c^10*b^2 + 2560*c^12)*a^10 + (512*b^14 - 256*c^2*b^12 + 8960*c^4*b^10
      - 28672*c^6*b^8 + 2176*c^8*b^6 - 22784*c^10*b^4 - 128*c^12*b^2 - 768*c^14)*a^8
      + (1536*c^2*b^14 - 9728*c^4*b^12 + 12672*c^6*b^10 + 2176*c^8*b^8 + 4864*c^10*b^6
      + 8448*c^12*b^4 - 2560*c^14*b^2)*a^6 + (-512*c^2*b^16 + 2688*c^4*b^14
      - 9088*c^6*b^12 + 19712*c^8*b^10 - 22784*c^10*b^8 + 8448*c^12*b^6 - 2304*c^14*b^4
      + 768*c^16*b^2)*a^4 + (-1280*c^4*b^16 + 7040*c^6*b^14 - 13184*c^8*b^12
      + 9344*c^10*b^10 - 128*c^12*b^8 - 2560*c^14*b^6 + 768*c^16*b^4)*a^2
      + (-256*c^6*b^16 + 1536*c^8*b^14 - 3072*c^10*b^12 + 2560*c^12*b^10
      - 768*c^14*b^8))*y^4 + ((256*c^2*b^4 + 640*c^4*b^2 + 128*c^6)*a^18 + (-256*b^8
      - 4096*c^2*b^6 - 6912*c^4*b^4 - 128*c^6*b^2 + 128*c^8)*a^16 + (3584*b^10
      + 10752*c^2*b^8 + 19200*c^4*b^6 + 16256*c^6*b^4 - 4736*c^8*b^2 - 1024*c^10)*a^14
      + (-6656*b^12 - 6912*c^2*b^10 - 53760*c^4*b^8 - 17152*c^6*b^6 - 11648*c^8*b^4
      + 8064*c^10*b^2 + 1024*c^12)*a^12 + (3584*b^14 - 6912*c^2*b^12 + 82944*c^4*b^10
      - 2560*c^6*b^8 + 33792*c^8*b^6 - 9216*c^10*b^4 - 4224*c^12*b^2 - 128*c^14)*a^10
      + (-256*b^16 + 10752*c^2*b^14 - 53760*c^4*b^12 - 2560*c^6*b^10 - 19968*c^8*b^8
      - 6144*c^10*b^6 + 9472*c^12*b^4 + 128*c^14*b^2 - 128*c^16)*a^8 + (-4096*c^2*b^16
      + 19200*c^4*b^14 - 17152*c^6*b^12 + 33792*c^8*b^10 - 6144*c^10*b^8 - 3584*c^12*b^6
      - 640*c^14*b^4 + 128*c^16*b^2)*a^6 + (256*c^2*b^18 - 6912*c^4*b^16
      + 16256*c^6*b^14 - 11648*c^8*b^12 - 9216*c^10*b^10 + 9472*c^12*b^8 - 640*c^14*b^6
      - 768*c^16*b^4 + 128*c^18*b^2)*a^4 + (640*c^4*b^18 - 128*c^6*b^16 - 4736*c^8*b^14
      + 8064*c^10*b^12 - 4224*c^12*b^10 + 128*c^14*b^8 + 128*c^16*b^6
      + 128*c^18*b^4)*a^2 + (128*c^6*b^18 + 128*c^8*b^16 - 1024*c^10*b^14
      + 1024*c^12*b^12 - 128*c^14*b^10 - 128*c^16*b^8))*y^3 + ((-512*c^2*b^6
      - 384*c^4*b^4 + 3200*c^6*b^2 + 768*c^8)*a^18 + (512*b^10 + 768*c^2*b^8
      + 2048*c^4*b^6 - 8832*c^6*b^4 - 13440*c^8*b^2 - 2560*c^10)*a^16 + (-512*b^12
      - 5120*c^2*b^10 + 3584*c^4*b^8 + 7040*c^6*b^6 + 34688*c^8*b^4 + 19712*c^10*b^2
      + 3072*c^12)*a^14 + (-512*b^14 + 9728*c^2*b^12 - 5376*c^4*b^10 - 10240*c^6*b^8
      - 32640*c^8*b^6 - 46464*c^10*b^4 - 10240*c^12*b^2 - 1536*c^14)*a^12 + (512*b^16
      - 5120*c^2*b^14 - 5376*c^4*b^12 + 18432*c^6*b^10 + 11264*c^8*b^8 + 44544*c^10*b^6
      + 23680*c^12*b^4 - 1152*c^14*b^2 + 256*c^16)*a^10 + (768*c^2*b^16 + 3584*c^4*b^14
      - 10240*c^6*b^12 + 11264*c^8*b^10 - 39424*c^10*b^8 - 8192*c^12*b^6 - 3968*c^14*b^4
      + 2176*c^16*b^2)*a^8 + (-512*c^2*b^18 + 2048*c^4*b^16 + 7040*c^6*b^14
      - 32640*c^8*b^12 + 44544*c^10*b^10 - 8192*c^12*b^8 - 1792*c^14*b^6 + 1024*c^16*b^4
      - 256*c^18*b^2)*a^6 + (-384*c^4*b^18 - 8832*c^6*b^16 + 34688*c^8*b^14
      - 46464*c^10*b^12 + 23680*c^12*b^10 - 3968*c^14*b^8 + 1024*c^16*b^6
      - 768*c^18*b^4)*a^4 + (3200*c^6*b^18 - 13440*c^8*b^16 + 19712*c^10*b^14
      - 10240*c^12*b^12 - 1152*c^14*b^10 + 2176*c^16*b^8 - 256*c^18*b^6)*a^2
      + (768*c^8*b^18 - 2560*c^10*b^16 + 3072*c^12*b^14 - 1536*c^14*b^12
      + 256*c^16*b^10))*y^2 + ((256*c^2*b^8 + 3072*c^4*b^6 + 768*c^6*b^4 - 1152*c^8*b^2
      + 128*c^10)*a^18 + (-256*b^12 - 3584*c^2*b^10 - 4608*c^4*b^8 - 10752*c^6*b^6
      - 512*c^8*b^4 + 2688*c^10*b^2 - 384*c^12)*a^16 + (512*b^14 + 3328*c^2*b^12
      + 14080*c^4*b^10 + 12288*c^6*b^8 + 14592*c^8*b^6 - 2944*c^10*b^4 - 1280*c^12*b^2
      + 384*c^14)*a^14 + (-256*b^16 + 3328*c^2*b^14 - 25088*c^4*b^12 - 3072*c^6*b^10
      - 20480*c^8*b^8 - 9728*c^10*b^6 + 4992*c^12*b^4 - 768*c^14*b^2 - 128*c^16)*a^12
      + (-3584*c^2*b^16 + 14080*c^4*b^14 - 3072*c^6*b^12 + 24064*c^8*b^10
      - 1024*c^10*b^8 + 8704*c^12*b^6 - 3712*c^14*b^4 + 384*c^16*b^2)*a^10
      + (256*c^2*b^18 - 4608*c^4*b^16 + 12288*c^6*b^14 - 20480*c^8*b^12 - 1024*c^10*b^10
      + 4096*c^12*b^8 - 6144*c^14*b^6 + 2176*c^16*b^4 + 128*c^18*b^2)*a^8
      + (3072*c^4*b^18 - 10752*c^6*b^16 + 14592*c^8*b^14 - 9728*c^10*b^12
      + 8704*c^12*b^10 - 6144*c^14*b^8 + 3072*c^16*b^6 - 768*c^18*b^4)*a^6
      + (768*c^6*b^18 - 512*c^8*b^16 - 2944*c^10*b^14 + 4992*c^12*b^12 - 3712*c^14*b^10
      + 2176*c^16*b^8 - 768*c^18*b^6)*a^4 + (-1152*c^8*b^18 + 2688*c^10*b^16
      - 1280*c^12*b^14 - 768*c^14*b^12 + 384*c^16*b^10 + 128*c^18*b^8)*a^2
      + (128*c^10*b^18 - 384*c^12*b^16 + 384*c^14*b^14 - 128*c^16*b^12))*y
      + ((768*c^4*b^8 - 1536*c^6*b^6 + 2432*c^8*b^4 - 640*c^10*b^2)*a^18
      + (-768*c^2*b^12 - 1024*c^6*b^8 + 512*c^8*b^6 - 5760*c^10*b^4
      + 1920*c^12*b^2)*a^16 + (1536*c^2*b^14 - 768*c^4*b^12 + 1792*c^6*b^10
      + 1536*c^8*b^8 + 4736*c^10*b^6 + 3328*c^12*b^4 - 1920*c^14*b^2)*a^14
      + (-768*c^2*b^16 - 768*c^4*b^14 + 1536*c^6*b^12 - 4608*c^8*b^10 - 3072*c^10*b^8
      - 3456*c^12*b^6 + 256*c^14*b^4 + 640*c^16*b^2)*a^12 + (1792*c^6*b^14
      - 4608*c^8*b^12 + 10752*c^10*b^10 - 3072*c^12*b^8 - 128*c^14*b^6
      + 384*c^16*b^4)*a^10 + (768*c^4*b^18 - 1024*c^6*b^16 + 1536*c^8*b^14
      - 3072*c^10*b^12 - 3072*c^12*b^10 + 6144*c^14*b^8 - 1664*c^16*b^6
      - 640*c^18*b^4)*a^8 + (-1536*c^6*b^18 + 512*c^8*b^16 + 4736*c^10*b^14
      - 3456*c^12*b^12 - 128*c^14*b^10 - 1664*c^16*b^8 + 1536*c^18*b^6)*a^6
      + (2432*c^8*b^18 - 5760*c^10*b^16 + 3328*c^12*b^14 + 256*c^14*b^12 + 384*c^16*b^10
      - 640*c^18*b^8)*a^4 + (-640*c^10*b^18 + 1920*c^12*b^16 - 1920*c^14*b^14
      + 640*c^16*b^12)*a^2)) * h
  have h1' : c * a - b ^ 2 ≠ 0 := by rw [mul_comm]; exact h1
  have h2' : c * a + b ^ 2 ≠ 0 := by rw [mul_comm]; exact h2
  have h3' : a ^ 2 - c * b ≠ 0 := fun h => h3 (by linear_combination -h)
  have h4' : a ^ 2 + c * b ≠ 0 := fun h => h4 (by linear_combination h)
  revert hR
  repeat' apply mul_ne_zero
  all_goals first | assumption | exact pow_ne_zero _ ‹_› | norm_num

/-- On a positive root of a non-exceptional triple, Sharipov's box is nondegenerate:
`u, v, w ≠ 0`. -/
theorem edges_ne_zero {a b c y : ℚ} (hE : excPoly a b c ≠ 0) (hy : 0 < y)
    (hf : sextic a b c y = 0) :
    uu a b c y ≠ 0 ∧ vv a b c y ≠ 0 ∧ ww a b c y ≠ 0 := by
  obtain ⟨ha, hb, hc, hab, hab', hac, hac', hbc, hbc', h1, h2, -, -⟩ := factors_ne_zero hE
  -- `nn ≠ 0`
  have hnn : nn a b c y ≠ 0 := by
    unfold nn
    refine mul_ne_zero (mul_ne_zero (by positivity) ?_) (by positivity)
    intro hyb
    have hy' : y = b ^ 2 := by linear_combination hyb
    have : 16 * b ^ 6 * (a - c) * (a + c) * (a * c - b ^ 2) * (a * c + b ^ 2) = 0 := by
      rw [← hf, hy']; unfold sextic; ring
    revert this
    repeat' apply mul_ne_zero
    all_goals first | assumption | exact pow_ne_zero _ ‹_› | norm_num
  -- `dd ≠ 0`
  have hdd : dd a b c y ≠ 0 := by
    unfold dd
    refine mul_ne_zero (mul_ne_zero two_ne_zero (by positivity)) ?_
    intro hyac
    have hfac : (y - a * c) * (y + a * c) = 0 := by linear_combination hyac
    rcases mul_eq_zero.mp hfac with h | h
    · have hy' : y = a * c := by linear_combination h
      have : c ^ 2 * a ^ 2 * (a + c) ^ 4 * (c * a - b ^ 2) ^ 2 = 0 := by
        rw [← hf, hy']; unfold sextic; ring
      have h1' : c * a - b ^ 2 ≠ 0 := by rw [mul_comm]; exact h1
      revert this
      repeat' apply mul_ne_zero
      all_goals exact pow_ne_zero _ ‹_›
    · have hy' : y = -(a * c) := by linear_combination h
      have : c ^ 2 * a ^ 2 * (a - c) ^ 4 * (c * a + b ^ 2) ^ 2 = 0 := by
        rw [← hf, hy']; unfold sextic; ring
      have h2' : c * a + b ^ 2 ≠ 0 := by rw [mul_comm]; exact h2
      revert this
      repeat' apply mul_ne_zero
      all_goals exact pow_ne_zero _ ‹_›
  -- `y ≠ c²`
  have hyc : y - c ^ 2 ≠ 0 := by
    intro hyc
    have hy' : y = c ^ 2 := by linear_combination hyc
    have key : (b ^ 4 + c ^ 4) * sextic a b c y = 8 * c ^ 4 *
        (((b ^ 4 + c ^ 4) * a ^ 2 - 2 * c ^ 4 * b ^ 2) ^ 2 + c ^ 4 * (b ^ 4 - c ^ 4) ^ 2) := by
      rw [hy']; unfold sextic; ring
    rw [hf, mul_zero] at key
    have hc4 : 0 < c ^ 4 := by positivity
    have hsq : c ^ 4 * (b ^ 4 - c ^ 4) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((b ^ 4 + c ^ 4) * a ^ 2 - 2 * c ^ 4 * b ^ 2),
        sq_nonneg (b ^ 4 - c ^ 4), mul_nonneg hc4.le (sq_nonneg (b ^ 4 - c ^ 4))]
    have : (b - c) * (b + c) * (b ^ 2 + c ^ 2) = 0 := by
      have h0 : b ^ 4 - c ^ 4 = 0 := by
        rcases mul_eq_zero.mp hsq with h | h
        · exact absurd h hc4.ne'
        · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
      linear_combination h0
    revert this
    exact mul_ne_zero (mul_ne_zero hbc hbc') (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · unfold uu
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hc) hy.ne') ?_
    positivity
  · unfold vv
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hnn) hdd) hyc
  · unfold ww
    refine mul_ne_zero hyc ?_
    have : dd a b c y ^ 2 - nn a b c y ^ 2 =
        -((nn a b c y - dd a b c y) * (nn a b c y + dd a b c y)) := by ring
    rw [this, neg_ne_zero]
    exact mul_ne_zero (nn_sub_dd_ne_zero hE hf) (nn_add_dd_ne_zero hE hf)

/-- **Sharipov's Theorem 1.1 (root ⇒ cuboid).** A nonzero rational root `t` of the third cuboid
polynomial, for a non-exceptional triple, gives a rational perfect cuboid: the box
`|u/t|, |v|, |w|` of Sharipov's parametrization. -/
theorem exists_isRatCuboid_of_root {a b c t : ℚ} (hE : excPoly a b c ≠ 0) (ht : t ≠ 0)
    (hf : sextic a b c (t ^ 2) = 0) :
    ∃ p q r d e f g : ℚ, PerfectCuboid.CongruentRank.IsRatCuboid p q r d e f g := by
  have hy : 0 < t ^ 2 := by positivity
  obtain ⟨hu, hv, hw⟩ := edges_ne_zero hE hy hf
  set y := t ^ 2 with hydef
  have i1 := sextic_identity_one hf
  have i2 := sextic_identity_two hf
  have i3 := sextic_identity_three a b c y
  have i4 := sextic_identity_four a b c y
  have hp : 0 < |uu a b c y / t| := abs_pos.mpr (div_ne_zero hu ht)
  have hq : 0 < |vv a b c y| := abs_pos.mpr hv
  have hr : 0 < |ww a b c y| := abs_pos.mpr hw
  refine ⟨|uu a b c y / t|, |vv a b c y|, |ww a b c y|, |diagD a b c y / t|,
    |diagE a b c y / t|, |(y - c ^ 2) * (dd a b c y ^ 2 + nn a b c y ^ 2)|, |diagG a b c y|,
    { pos_a := hp, pos_b := hq, pos_c := hr, pos_d := ?_, pos_e := ?_, pos_f := ?_, pos_g := ?_,
      hd := ?_, he := ?_, hf := ?_, hg := ?_ }⟩
  all_goals try simp only [sq_abs, div_pow]
  · refine abs_pos.mpr fun h => ?_
    have : (diagD a b c y / t) ^ 2 = 0 := by rw [h]; ring
    rw [div_pow, ← i1, hydef] at this
    field_simp at this
    nlinarith [sq_pos_of_ne_zero hu, sq_nonneg (t * vv a b c y)]
  · refine abs_pos.mpr fun h => ?_
    have : (diagE a b c y / t) ^ 2 = 0 := by rw [h]; ring
    rw [div_pow, ← i2, hydef] at this
    field_simp at this
    nlinarith [sq_pos_of_ne_zero hu, sq_nonneg (t * ww a b c y)]
  · refine abs_pos.mpr fun h => ?_
    have : ((y - c ^ 2) * (dd a b c y ^ 2 + nn a b c y ^ 2)) ^ 2 = 0 := by rw [h]; ring
    rw [← i4] at this
    nlinarith [sq_pos_of_ne_zero hv, sq_nonneg (ww a b c y)]
  · refine abs_pos.mpr fun h => ?_
    have : y * diagG a b c y ^ 2 = 0 := by rw [h]; ring
    rw [← i3] at this
    nlinarith [sq_pos_of_ne_zero hu, sq_nonneg (vv a b c y), sq_nonneg (ww a b c y), hy]
  · rw [← i1, hydef]; field_simp
  · rw [← i2, hydef]; field_simp
  · rw [i4]
  · have h3 : diagG a b c y ^ 2 = uu a b c y ^ 2 / y + (vv a b c y ^ 2 + ww a b c y ^ 2) := by
      field_simp
      linear_combination -i3
    rw [h3, hydef]; field_simp; ring

/-- **Corollary.** For a non-exceptional integer triple, a factor `X² − r` of the third cuboid
polynomial with `r > 0` forces `r = m²` and a rational perfect cuboid. So for such triples the
factor types with an even quadratic factor `X² − r`, `r > 0`, occur only if a perfect cuboid
exists. -/
theorem exists_isRatCuboid_of_dvd {a b c r : ℤ} (hE : excPoly a b c ≠ 0) (hr : 0 < r)
    (h : X ^ 2 - C r ∣ cuboidThreePoly a b c) :
    ∃ p q r d e f g : ℚ, PerfectCuboid.CongruentRank.IsRatCuboid p q r d e f g := by
  have hc : (c : ℚ) ≠ 0 := (factors_ne_zero hE).2.2.1
  have hc' : c ≠ 0 := by exact_mod_cast hc
  rcases isSquare_or_isSquare_neg_of_dvd hc' h with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm0 : (m : ℚ) ≠ 0 := by
      rintro h0; have : m = 0 := by exact_mod_cast h0
      subst this; simp at hm; omega
    refine exists_isRatCuboid_of_root hE hm0 ?_
    have := sextic_eq_zero_of_dvd h
    rw [hm] at this; push_cast at this; rwa [sq]
  · nlinarith [mul_self_nonneg m]

end PerfectCuboid.ThirdConjecture
