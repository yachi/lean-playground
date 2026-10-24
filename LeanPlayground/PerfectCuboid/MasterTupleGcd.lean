module

public import LeanPlayground.PerfectCuboid.MasterTuple

/-!
# The arithmetic of a master tuple

Section 2 of René Peschmann, *A torsion-intersection proof of perfect-cuboid nonexistence on
1,072 explicit master-tuple fibers*, <https://arxiv.org/abs/2604.28072> (2026), proves two
structural facts about a master tuple `(a, b, m, n)`. Write

  `U₁ = a² − b²`, `V₁ = 2ab`, `W₁ = a² + b²`,  `U₂ = m² − n²`, `V₂ = 2mn`, `W₂ = m² + n²`.

The brick of the tuple has edges `U₁U₂ / g`, `V₁U₂ / g`, `U₁V₂ / g` with `g = gcd(U₁, U₂)`, so
its space diagonal is `√f₁ / g`, where `f₁ = (W₁U₂)² + (U₁V₂)²`.

## Main results

* `sq_add_sq_add_sq` — `(U₁U₂)² + (V₁U₂)² + (U₁V₂)² = f₁`, so the brick is perfect exactly
  when `f₁` is a square.
* `f₁_eq` — Theorem 2.2: `f₁ = L · R` with `L = W₁W₂ − V₁V₂ = (am − bn)² + (an − bm)²` and
  `R = W₁W₂ + V₁V₂ = (am + bn)² + (an + bm)²`.
* `gcd_mul_gcd` — Theorem 2.1: with `g₊ = gcd(am + bn, an + bm)` and
  `g₋ = gcd(am − bn, an − bm)`, if `gcd(a, b) = gcd(m, n) = 1` and `a − b`, `m − n` are odd, then
  `g₊ · g₋ = gcd(U₁, U₂)`, and `g₊`, `g₋` are coprime (`coprime_gPlus_gMinus`).
* `gPlus_sq_dvd`, `gMinus_sq_dvd` — Corollary 2.3: `g₊² ∣ R` and `g₋² ∣ L`.
* `IsPerfectCuboid.mul`, `IsPerfectCuboid.of_mul` — Lemma 2.5 (scaling).

The proof of `gPlus ⬝ gMinus ∣ gcd(U₁, U₂)` is the paper's. For the other direction the paper
works one prime power at a time; here we use instead that `gcd(U₁, U₂)` divides the four
products `AC, AD, BC, BD` of `A = am + bn`, `B = an + bm`, `C = am − bn`, `D = an − bm`
(each is an integer combination of `U₁` and `U₂`), and `gcd(A, B) · gcd(C, D)` is a
combination of those four products by Bézout.
-/

@[expose] public section

namespace PerfectCuboid

namespace MasterTupleGcd

variable (a b m n : ℤ)

/-- `U₁ = a² − b²` -/
def U₁ : ℤ := a ^ 2 - b ^ 2
/-- `V₁ = 2ab` -/
def V₁ : ℤ := 2 * a * b
/-- `W₁ = a² + b²` -/
def W₁ : ℤ := a ^ 2 + b ^ 2
/-- `U₂ = m² − n²` -/
def U₂ : ℤ := m ^ 2 - n ^ 2
/-- `V₂ = 2mn` -/
def V₂ : ℤ := 2 * m * n
/-- `W₂ = m² + n²` -/
def W₂ : ℤ := m ^ 2 + n ^ 2

/-- Peschmann's `f₁ = (W₁U₂)² + (U₁V₂)²`: `g²` times the squared space diagonal. -/
def f₁ : ℤ := (W₁ a b * U₂ m n) ^ 2 + (U₁ a b * V₂ m n) ^ 2

/-- `L = W₁W₂ − V₁V₂` -/
def L : ℤ := W₁ a b * W₂ m n - V₁ a b * V₂ m n
/-- `R = W₁W₂ + V₁V₂` -/
def R : ℤ := W₁ a b * W₂ m n + V₁ a b * V₂ m n

/-- `g₊ = gcd(am + bn, an + bm)` -/
def gPlus : ℕ := Int.gcd (a * m + b * n) (a * n + b * m)
/-- `g₋ = gcd(am − bn, an − bm)` -/
def gMinus : ℕ := Int.gcd (a * m - b * n) (a * n - b * m)

/-- The squared space diagonal of the (unreduced) brick `(U₁U₂, V₁U₂, U₁V₂)` is `f₁`. -/
theorem sq_add_sq_add_sq :
    (U₁ a b * U₂ m n) ^ 2 + (V₁ a b * U₂ m n) ^ 2 + (U₁ a b * V₂ m n) ^ 2 = f₁ a b m n := by
  simp only [U₁, V₁, W₁, U₂, V₂, f₁]
  ring

/-- **Theorem 2.2.** `f₁ = L · R`. -/
theorem f₁_eq : f₁ a b m n = L a b m n * R a b m n := by
  simp only [U₁, V₁, W₁, U₂, V₂, W₂, f₁, L, R]
  ring

/-- `L` is a sum of two squares (Brahmagupta). -/
theorem L_eq : L a b m n = (a * m - b * n) ^ 2 + (a * n - b * m) ^ 2 := by
  simp only [V₁, W₁, V₂, W₂, L]
  ring

/-- `R` is a sum of two squares (Brahmagupta). -/
theorem R_eq : R a b m n = (a * m + b * n) ^ 2 + (a * n + b * m) ^ 2 := by
  simp only [V₁, W₁, V₂, W₂, R]
  ring

variable {a b m n}

/-- If `x, y` are coprime and `d` divides `x z` and `y z`, then `d ∣ z`. -/
theorem dvd_of_dvd_mul_of_dvd_mul {x y z d : ℤ} (hxy : IsCoprime x y) (hx : d ∣ x * z)
    (hy : d ∣ y * z) : d ∣ z := by
  obtain ⟨u, v, huv⟩ := hxy
  have : z = u * (x * z) + v * (y * z) := by linear_combination -z * huv
  rw [this]
  exact dvd_add (hx.mul_left u) (hy.mul_left v)

/-- If `d` divides `x C` and `x D`, then `d` divides `x · gcd(C, D)` (Bézout). -/
theorem dvd_mul_gcd {x C D d : ℤ} (hC : d ∣ x * C) (hD : d ∣ x * D) :
    d ∣ x * (Int.gcd C D : ℤ) := by
  rw [Int.gcd_eq_gcd_ab, mul_add, ← mul_assoc, ← mul_assoc]
  exact dvd_add (hC.mul_right _) (hD.mul_right _)

theorem gPlus_dvd_U₂ (hab : IsCoprime a b) : (gPlus a b m n : ℤ) ∣ U₂ m n := by
  have hA : (gPlus a b m n : ℤ) ∣ a * m + b * n := Int.gcd_dvd_left ..
  have hB : (gPlus a b m n : ℤ) ∣ a * n + b * m := Int.gcd_dvd_right ..
  apply dvd_of_dvd_mul_of_dvd_mul hab
  · have : a * U₂ m n = m * (a * m + b * n) - n * (a * n + b * m) := by simp only [U₂]; ring
    rw [this]
    exact dvd_sub (hA.mul_left _) (hB.mul_left _)
  · have : b * U₂ m n = m * (a * n + b * m) - n * (a * m + b * n) := by simp only [U₂]; ring
    rw [this]
    exact dvd_sub (hB.mul_left _) (hA.mul_left _)

theorem gPlus_dvd_U₁ (hmn : IsCoprime m n) : (gPlus a b m n : ℤ) ∣ U₁ a b := by
  have hA : (gPlus a b m n : ℤ) ∣ a * m + b * n := Int.gcd_dvd_left ..
  have hB : (gPlus a b m n : ℤ) ∣ a * n + b * m := Int.gcd_dvd_right ..
  apply dvd_of_dvd_mul_of_dvd_mul hmn
  · have : m * U₁ a b = a * (a * m + b * n) - b * (a * n + b * m) := by simp only [U₁]; ring
    rw [this]
    exact dvd_sub (hA.mul_left _) (hB.mul_left _)
  · have : n * U₁ a b = a * (a * n + b * m) - b * (a * m + b * n) := by simp only [U₁]; ring
    rw [this]
    exact dvd_sub (hB.mul_left _) (hA.mul_left _)

theorem gMinus_dvd_U₂ (hab : IsCoprime a b) : (gMinus a b m n : ℤ) ∣ U₂ m n := by
  have hC : (gMinus a b m n : ℤ) ∣ a * m - b * n := Int.gcd_dvd_left ..
  have hD : (gMinus a b m n : ℤ) ∣ a * n - b * m := Int.gcd_dvd_right ..
  apply dvd_of_dvd_mul_of_dvd_mul hab
  · have : a * U₂ m n = m * (a * m - b * n) - n * (a * n - b * m) := by simp only [U₂]; ring
    rw [this]
    exact dvd_sub (hC.mul_left _) (hD.mul_left _)
  · have : b * U₂ m n = n * (a * m - b * n) - m * (a * n - b * m) := by simp only [U₂]; ring
    rw [this]
    exact dvd_sub (hC.mul_left _) (hD.mul_left _)

theorem gMinus_dvd_U₁ (hmn : IsCoprime m n) : (gMinus a b m n : ℤ) ∣ U₁ a b := by
  have hC : (gMinus a b m n : ℤ) ∣ a * m - b * n := Int.gcd_dvd_left ..
  have hD : (gMinus a b m n : ℤ) ∣ a * n - b * m := Int.gcd_dvd_right ..
  apply dvd_of_dvd_mul_of_dvd_mul hmn
  · have : m * U₁ a b = a * (a * m - b * n) + b * (a * n - b * m) := by simp only [U₁]; ring
    rw [this]
    exact dvd_add (hC.mul_left _) (hD.mul_left _)
  · have : n * U₁ a b = b * (a * m - b * n) + a * (a * n - b * m) := by simp only [U₁]; ring
    rw [this]
    exact dvd_add (hC.mul_left _) (hD.mul_left _)

/-- `g₊` and `g₋` are coprime: a common divisor divides `2am, 2an, 2bm, 2bn`, hence `2`, and
it also divides the odd number `(am + bn) + (an + bm) = (a + b)(m + n)`. -/
theorem coprime_gPlus_gMinus (hab : IsCoprime a b) (hmn : IsCoprime m n) (hab2 : Odd (a - b))
    (hmn2 : Odd (m - n)) : Nat.Coprime (gPlus a b m n) (gMinus a b m n) := by
  set d : ℤ := ((Nat.gcd (gPlus a b m n) (gMinus a b m n) : ℕ) : ℤ)
  have hdP : d ∣ (gPlus a b m n : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left ..)
  have hdM : d ∣ (gMinus a b m n : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right ..)
  have hA : d ∣ a * m + b * n := hdP.trans (Int.gcd_dvd_left ..)
  have hB : d ∣ a * n + b * m := hdP.trans (Int.gcd_dvd_right ..)
  have hC : d ∣ a * m - b * n := hdM.trans (Int.gcd_dvd_left ..)
  have hD : d ∣ a * n - b * m := hdM.trans (Int.gcd_dvd_right ..)
  -- `d ∣ 2a` and `d ∣ 2b`, so `d ∣ 2`
  have h2a : d ∣ 2 * a := by
    apply dvd_of_dvd_mul_of_dvd_mul hmn
    · have : m * (2 * a) = (a * m + b * n) + (a * m - b * n) := by ring
      rw [this]
      exact dvd_add hA hC
    · have : n * (2 * a) = (a * n + b * m) + (a * n - b * m) := by ring
      rw [this]
      exact dvd_add hB hD
  have h2b : d ∣ 2 * b := by
    apply dvd_of_dvd_mul_of_dvd_mul hmn
    · have : m * (2 * b) = (a * n + b * m) - (a * n - b * m) := by ring
      rw [this]
      exact dvd_sub hB hD
    · have : n * (2 * b) = (a * m + b * n) - (a * m - b * n) := by ring
      rw [this]
      exact dvd_sub hA hC
  have h2 : d ∣ 2 := by
    obtain ⟨u, v, huv⟩ := hab
    have : (2 : ℤ) = u * (2 * a) + v * (2 * b) := by linear_combination -2 * huv
    rw [this]
    exact dvd_add (h2a.mul_left u) (h2b.mul_left v)
  -- `(am + bn) + (an + bm) = (a + b)(m + n)` is odd
  obtain ⟨k, hk⟩ : Odd ((a * m + b * n) + (a * n + b * m)) := by
    have : (a * m + b * n) + (a * n + b * m) = (a - b + 2 * b) * (m - n + 2 * n) := by ring
    rw [this]
    exact (hab2.add_even (even_two_mul b)).mul (hmn2.add_even (even_two_mul n))
  have h1 : d ∣ 1 := by
    have : (1 : ℤ) = ((a * m + b * n) + (a * n + b * m)) - k * 2 := by rw [hk]; ring
    rw [this]
    exact dvd_sub (dvd_add hA hB) (h2.mul_left k)
  exact Int.natCast_dvd_natCast.mp (by simpa using h1) |> Nat.dvd_one.mp

/-- `gcd(U₁, U₂)` divides `g₊ · g₋`. -/
theorem gcd_dvd_gPlus_mul_gMinus :
    Int.gcd (U₁ a b) (U₂ m n) ∣ gPlus a b m n * gMinus a b m n := by
  set G : ℤ := ((Int.gcd (U₁ a b) (U₂ m n) : ℕ) : ℤ)
  have h₁ : G ∣ U₁ a b := Int.gcd_dvd_left ..
  have h₂ : G ∣ U₂ m n := Int.gcd_dvd_right ..
  have comb : ∀ x y : ℤ, G ∣ x * U₁ a b + y * U₂ m n := fun x y ↦
    dvd_add (h₁.mul_left x) (h₂.mul_left y)
  have hAC : G ∣ (a * m + b * n) * (a * m - b * n) := by
    have := comb (m ^ 2) (b ^ 2)
    convert this using 1
    simp only [U₁, U₂]
    ring
  have hAD : G ∣ (a * m + b * n) * (a * n - b * m) := by
    have := comb (m * n) (-(a * b))
    convert this using 1
    simp only [U₁, U₂]
    ring
  have hBC : G ∣ (a * n + b * m) * (a * m - b * n) := by
    have := comb (m * n) (a * b)
    convert this using 1
    simp only [U₁, U₂]
    ring
  have hBD : G ∣ (a * n + b * m) * (a * n - b * m) := by
    have := comb (n ^ 2) (-(b ^ 2))
    convert this using 1
    simp only [U₁, U₂]
    ring
  have hA := dvd_mul_gcd hAC hAD
  have hB := dvd_mul_gcd hBC hBD
  have : G ∣ (gMinus a b m n : ℤ) * (gPlus a b m n : ℤ) := by
    rw [mul_comm] at hA hB
    exact dvd_mul_gcd hA hB
  rw [mul_comm] at this
  exact Int.natCast_dvd_natCast.mp (by push_cast; exact this)

/-- **Theorem 2.1** (`g₊ · g₋` structure). For coprime `a, b` and coprime `m, n` with `a − b`
and `m − n` odd, `g₊ · g₋ = gcd(U₁, U₂)`. -/
theorem gcd_mul_gcd (hab : IsCoprime a b) (hmn : IsCoprime m n) (hab2 : Odd (a - b))
    (hmn2 : Odd (m - n)) : gPlus a b m n * gMinus a b m n = Int.gcd (U₁ a b) (U₂ m n) := by
  apply Nat.dvd_antisymm _ gcd_dvd_gPlus_mul_gMinus
  apply (coprime_gPlus_gMinus hab hmn hab2 hmn2).mul_dvd_of_dvd_of_dvd
  · exact Int.dvd_gcd (gPlus_dvd_U₁ hmn) (gPlus_dvd_U₂ hab)
  · exact Int.dvd_gcd (gMinus_dvd_U₁ hmn) (gMinus_dvd_U₂ hab)

/-- **Corollary 2.3.** `g₊² ∣ R`. -/
theorem gPlus_sq_dvd : (gPlus a b m n : ℤ) ^ 2 ∣ R a b m n := by
  rw [R_eq, sq, sq, sq]
  exact dvd_add (mul_dvd_mul (Int.gcd_dvd_left ..) (Int.gcd_dvd_left ..))
    (mul_dvd_mul (Int.gcd_dvd_right ..) (Int.gcd_dvd_right ..))

/-- **Corollary 2.3.** `g₋² ∣ L`. -/
theorem gMinus_sq_dvd : (gMinus a b m n : ℤ) ^ 2 ∣ L a b m n := by
  rw [L_eq, sq, sq, sq]
  exact dvd_add (mul_dvd_mul (Int.gcd_dvd_left ..) (Int.gcd_dvd_left ..))
    (mul_dvd_mul (Int.gcd_dvd_right ..) (Int.gcd_dvd_right ..))

end MasterTupleGcd

/-! ### Lemma 2.5: scaling -/

namespace IsPerfectCuboid

/-- Scaling a perfect cuboid by `k > 0` gives a perfect cuboid. -/
theorem mul {a b c k : ℕ} (h : IsPerfectCuboid a b c) (hk : 0 < k) :
    IsPerfectCuboid (k * a) (k * b) (k * c) := by
  have sq_mul {n : ℕ} (hn : IsSquare n) : IsSquare (k ^ 2 * n) := by
    obtain ⟨r, rfl⟩ := hn
    exact ⟨k * r, by ring⟩
  obtain ⟨⟨ha, hb, hc, hab, hbc, hca⟩, habc⟩ := h
  refine ⟨⟨Nat.mul_pos hk ha, Nat.mul_pos hk hb, Nat.mul_pos hk hc, ?_, ?_, ?_⟩, ?_⟩
  · convert sq_mul hab using 1; ring
  · convert sq_mul hbc using 1; ring
  · convert sq_mul hca using 1; ring
  · convert sq_mul habc using 1; ring

/-- Conversely, if `k · (a, b, c)` is a perfect cuboid, so is `(a, b, c)`. -/
theorem of_mul {a b c k : ℕ} (h : IsPerfectCuboid (k * a) (k * b) (k * c)) :
    IsPerfectCuboid a b c := by
  obtain ⟨⟨ha, hb, hc, hab, hbc, hca⟩, habc⟩ := h
  have hk : 0 < k := Nat.pos_of_mul_pos_right ha
  have unscale {n : ℕ} (e : IsSquare (k ^ 2 * n)) : IsSquare n := isSquare_of_sq_mul hk e
  refine ⟨⟨Nat.pos_of_mul_pos_left ha, Nat.pos_of_mul_pos_left hb, Nat.pos_of_mul_pos_left hc,
    unscale ?_, unscale ?_, unscale ?_⟩, unscale ?_⟩
  · convert hab using 1; ring
  · convert hbc using 1; ring
  · convert hca using 1; ring
  · convert habc using 1; ring

end IsPerfectCuboid

end PerfectCuboid
