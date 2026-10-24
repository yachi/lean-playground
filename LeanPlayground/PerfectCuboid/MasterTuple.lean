module

public import LeanPlayground.PerfectCuboid.Contradiction
public import Mathlib.NumberTheory.PythagoreanTriples

/-!
# Master tuples: every primitive Euler brick comes from two Pythagorean pairs

The recent fiber-by-fiber attacks on the perfect cuboid problem

* René Peschmann, *A torsion-intersection proof of perfect-cuboid nonexistence on 1,072
  explicit master-tuple fibers*, <https://arxiv.org/abs/2604.28072> (2026), Theorem (i);
* Marco Cipollini, *Elimination of René Peschmann's 968 remaining hard fibers*,
  <https://arxiv.org/abs/2609.14526> (2026), §1,

rest on one elementary classification: a primitive Euler brick `(X, Y, Z)` is determined by two
primitive Pythagorean triples that share the edge `X`. Writing their legs in Euclid's form,
`(u₁, v₁)` from the pair `(a, b)` and `(u, v)` from the pair `(m, n)`, and `g = gcd(u, u₁)`,

  `g · X = u · u₁`,  `g · Y = u · v₁`,  `g · Z = u₁ · v`.

The quadruple `(a, b, m, n)` is the *master tuple* of the brick. Fixing `(m, n)` and letting
`(a, b)` vary gives the *fiber* on which both papers work. Conversely every such quadruple gives
a brick as soon as the third face closes, i.e. `(u v₁)² + (u₁ v)²` is a square.

## Main results

* `EuclidLegs` — the legs of a primitive Pythagorean triple in Euclid's form.
* `exists_euclidLegs` — Euclid's parametrization, from Mathlib's
  `PythagoreanTriple.coprime_classification'`, for positive coprime legs.
* `IsEulerBrick.exists_masterTuple` — the classification above (Peschmann's Theorem (i)).
* `isEulerBrick_of_euclidLegs` — the converse construction.

The proof of the classification is the one in Cipollini's paper: with `d = gcd(X, Y)` and
`e = gcd(X, Z)`, `X = d u₁ = e u`; any common divisor of `d, e` divides `X, Y, Z`, so `d, e` are
coprime, hence `u = d k`, `u₁ = e k` with `k = gcd(u, u₁)`.
-/

@[expose] public section

namespace PerfectCuboid

/-- The legs `(u, v)` of a primitive Pythagorean triple in Euclid's form: `u = a² − b²` and
`v = 2ab` (or the other way round), where `a > b > 0` are coprime and of opposite parity. -/
def EuclidLegs (a b u v : ℕ) : Prop :=
  0 < b ∧ b < a ∧ Nat.Coprime a b ∧ (a + b) % 2 = 1 ∧
    ((u = a ^ 2 - b ^ 2 ∧ v = 2 * a * b) ∨ (u = 2 * a * b ∧ v = a ^ 2 - b ^ 2))

namespace EuclidLegs

variable {a b u v : ℕ}

theorem swap (h : EuclidLegs a b u v) : EuclidLegs a b v u := by
  obtain ⟨hb, hba, hab, hpar, h | h⟩ := h
  · exact ⟨hb, hba, hab, hpar, Or.inr ⟨h.2, h.1⟩⟩
  · exact ⟨hb, hba, hab, hpar, Or.inl ⟨h.2, h.1⟩⟩

/-- Euclid's legs form a Pythagorean triple with hypotenuse `a² + b²`. -/
theorem sq_add_sq (h : EuclidLegs a b u v) : u ^ 2 + v ^ 2 = (a ^ 2 + b ^ 2) ^ 2 := by
  obtain ⟨-, hba, -, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h <;>
  · have hle : b ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hba.le 2
    zify [hle]
    ring

theorem isSquare (h : EuclidLegs a b u v) : IsSquare (u ^ 2 + v ^ 2) :=
  ⟨a ^ 2 + b ^ 2, by rw [h.sq_add_sq, sq]⟩

theorem pos_left (h : EuclidLegs a b u v) : 0 < u := by
  obtain ⟨hb, hba, -, -, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := h
  · exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hba two_ne_zero)
  · exact Nat.mul_pos (Nat.mul_pos two_pos (by omega)) hb

theorem pos_right (h : EuclidLegs a b u v) : 0 < v := h.swap.pos_left

end EuclidLegs

/-- **Euclid's parametrization.** Positive coprime legs of a Pythagorean triple are Euclid's legs
of some pair `(a, b)`. -/
theorem exists_euclidLegs {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (huv : Nat.Coprime u v)
    (hsq : IsSquare (u ^ 2 + v ^ 2)) : ∃ a b, EuclidLegs a b u v := by
  suffices key : ∀ {u v : ℕ}, 0 < u → 0 < v → Nat.Coprime u v → IsSquare (u ^ 2 + v ^ 2) →
      u % 2 = 1 → ∃ a b, EuclidLegs a b u v by
    rcases Nat.even_or_odd u with heu | hou
    · have hov : v % 2 = 1 := by
        by_contra hv2
        have h2u : 2 ∣ u := even_iff_two_dvd.mp heu
        have h2v : 2 ∣ v := Nat.dvd_of_mod_eq_zero (by omega)
        have := Nat.dvd_gcd h2u h2v
        rw [huv.gcd_eq_one] at this
        omega
      obtain ⟨a, b, h⟩ := key hv hu huv.symm (by rw [add_comm]; exact hsq) hov
      exact ⟨a, b, h.swap⟩
    · exact key hu hv huv hsq (Nat.odd_iff.mp hou)
  intro u v hu hv huv hsq hodd
  obtain ⟨w, hw⟩ := hsq
  have hw0 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with rfl | hw0
    · nlinarith
    · exact hw0
  have hpt : PythagoreanTriple (u : ℤ) v w := by
    unfold PythagoreanTriple
    exact_mod_cast (by simpa only [sq] using hw : u * u + v * v = w * w)
  obtain ⟨m, n, hu', hv', -, hmn, hpar, hm0⟩ := hpt.coprime_classification'
    (by rw [Int.gcd_natCast_natCast]; exact huv) (by omega) (by exact_mod_cast hw0)
  have hm : 0 < m := by
    rcases hm0.lt_or_eq with hm | rfl
    · exact hm
    · simp at hv'
      omega
  have hn : 0 < n := by
    have : (0 : ℤ) < v := by exact_mod_cast hv
    by_contra hn
    rw [not_lt] at hn
    nlinarith
  have hnm : n < m := by
    have : (0 : ℤ) < u := by exact_mod_cast hu
    by_contra hnm
    rw [not_lt] at hnm
    nlinarith
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, (M : ℤ) = m := ⟨m.toNat, Int.toNat_of_nonneg hm0⟩
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, (N : ℤ) = n := ⟨n.toNat, Int.toNat_of_nonneg hn.le⟩
  have hNM : N < M := by exact_mod_cast hnm
  refine ⟨M, N, by exact_mod_cast hn, hNM, ?_, by omega, Or.inl ⟨?_, by exact_mod_cast hv'⟩⟩
  · change Nat.gcd M N = 1
    rw [← Int.gcd_natCast_natCast]
    exact hmn
  · have : (u : ℤ) = ((M ^ 2 - N ^ 2 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.pow_le_pow_left hNM.le 2)]
      push_cast
      exact hu'
    exact_mod_cast this

/-- **Every primitive Euler brick has a master tuple** (Peschmann, arXiv:2604.28072,
Theorem (i)). If `(X, Y, Z)` is an Euler brick with `gcd(X, Y, Z) = 1`, then there are Euclid
legs `(u₁, v₁)` of a pair `(a, b)` and `(u, v)` of a pair `(m, n)` such that, with
`g = gcd(u, u₁)`,
`g X = u u₁`, `g Y = u v₁` and `g Z = u₁ v`. -/
theorem IsEulerBrick.exists_masterTuple {X Y Z : ℕ} (h : IsEulerBrick X Y Z)
    (hp : Nat.gcd X (Nat.gcd Y Z) = 1) :
    ∃ a b m n u v u₁ v₁ : ℕ, EuclidLegs a b u₁ v₁ ∧ EuclidLegs m n u v ∧
      Nat.gcd u u₁ * X = u * u₁ ∧ Nat.gcd u u₁ * Y = u * v₁ ∧ Nat.gcd u u₁ * Z = u₁ * v := by
  obtain ⟨hX, hY, hZ, hXY, hYZ, hZX⟩ := h
  -- the face `X, Y` is `d = gcd(X, Y)` times a primitive triple, and likewise the face `X, Z`
  obtain ⟨u₁, v₁, hcop₁, hXd, hYd⟩ := Nat.exists_coprime X Y
  obtain ⟨u, v, hcop, hXe, hZe⟩ := Nat.exists_coprime X Z
  obtain ⟨d, hd⟩ : ∃ d, Nat.gcd X Y = d := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, Nat.gcd X Z = e := ⟨_, rfl⟩
  have hdX : d ∣ X := hd ▸ Nat.gcd_dvd_left X Y
  have hdY : d ∣ Y := hd ▸ Nat.gcd_dvd_right X Y
  have heZ : e ∣ Z := he ▸ Nat.gcd_dvd_right X Z
  rw [hd] at hXd hYd
  rw [he] at hXe hZe
  have hd0 : 0 < d := hd ▸ Nat.gcd_pos_of_pos_left _ hX
  have he0 : 0 < e := he ▸ Nat.gcd_pos_of_pos_left _ hX
  have pos {x y g : ℕ} (hxy : x = y * g) (hx : 0 < x) : 0 < y :=
    Nat.pos_of_ne_zero (by rintro rfl; simp at hxy; omega)
  have hu₁ := pos hXd hX
  have hv₁ := pos hYd hY
  have hu := pos hXe hX
  have hv := pos hZe hZ
  have hsq₁ : IsSquare (u₁ ^ 2 + v₁ ^ 2) := by
    apply isSquare_of_sq_mul hd0
    have : d ^ 2 * (u₁ ^ 2 + v₁ ^ 2) = X ^ 2 + Y ^ 2 := by rw [hXd, hYd]; ring
    rw [this]
    exact hXY
  have hsq : IsSquare (u ^ 2 + v ^ 2) := by
    apply isSquare_of_sq_mul he0
    have : e ^ 2 * (u ^ 2 + v ^ 2) = Z ^ 2 + X ^ 2 := by rw [hXe, hZe]; ring
    rw [this]
    exact hZX
  -- `d` and `e` are coprime, since a common divisor divides `X, Y, Z`
  have hde : Nat.Coprime d e := by
    change Nat.gcd d e = 1
    have : Nat.gcd d e ∣ Nat.gcd X (Nat.gcd Y Z) :=
      Nat.dvd_gcd ((Nat.gcd_dvd_left d e).trans hdX)
        (Nat.dvd_gcd ((Nat.gcd_dvd_left d e).trans hdY) ((Nat.gcd_dvd_right d e).trans heZ))
    rw [hp] at this
    exact Nat.dvd_one.mp this
  -- `d u₁ = e u = X` with `d, e` coprime forces `u = d k`, `u₁ = e k`
  have hX2 : u₁ * d = u * e := by rw [← hXd, ← hXe]
  obtain ⟨k, hk⟩ : d ∣ u := hde.dvd_of_dvd_mul_right ⟨u₁, by rw [← hX2]; ring⟩
  have hu₁k : u₁ = e * k := by
    have : u₁ * d = (e * k) * d := by rw [hX2, hk]; ring
    exact Nat.eq_of_mul_eq_mul_right hd0 this
  have hg : Nat.gcd u u₁ = k := by
    rw [hk, hu₁k, Nat.gcd_mul_right, hde.gcd_eq_one, one_mul]
  obtain ⟨a, b, hab⟩ := exists_euclidLegs hu₁ hv₁ hcop₁ hsq₁
  obtain ⟨m, n, hmn⟩ := exists_euclidLegs hu hv hcop hsq
  refine ⟨a, b, m, n, u, v, u₁, v₁, hab, hmn, ?_, ?_, ?_⟩
  · rw [hg, hXd, hk, hu₁k]; ring
  · rw [hg, hYd, hk]; ring
  · rw [hg, hZe, hu₁k]; ring

/-- **The converse.** Euclid legs `(u₁, v₁)` and `(u, v)` give an Euler brick with
`g X = u u₁`, `g Y = u v₁`, `g Z = u₁ v` (where `g = gcd(u, u₁)`) as soon as the third face
closes: `(u v₁)² + (u₁ v)²` is a square. -/
theorem isEulerBrick_of_euclidLegs {a b m n u v u₁ v₁ : ℕ} (h₁ : EuclidLegs a b u₁ v₁)
    (h : EuclidLegs m n u v) (hM : IsSquare ((u * v₁) ^ 2 + (u₁ * v) ^ 2)) :
    IsEulerBrick (u * u₁ / Nat.gcd u u₁) (u * v₁ / Nat.gcd u u₁) (u₁ * v / Nat.gcd u u₁) := by
  have hu0 := h.pos_left
  have hu₁0 := h₁.pos_left
  have hg0 : 0 < Nat.gcd u u₁ := Nat.gcd_pos_of_pos_left _ hu0
  obtain ⟨u', u₁', hcop, hu, hu₁⟩ := Nat.exists_coprime u u₁
  set g := Nat.gcd u u₁ with hg
  have hu' : 0 < u' := Nat.pos_of_ne_zero (by rintro rfl; simp at hu; omega)
  have hu₁' : 0 < u₁' := Nat.pos_of_ne_zero (by rintro rfl; simp at hu₁; omega)
  have eX : u * u₁ / g = u' * u₁' * g := by
    rw [hu, hu₁, show u' * g * (u₁' * g) = u' * u₁' * g * g by ring, Nat.mul_div_cancel _ hg0]
  have eY : u * v₁ / g = u' * v₁ := by
    rw [hu, show u' * g * v₁ = u' * v₁ * g by ring, Nat.mul_div_cancel _ hg0]
  have eZ : u₁ * v / g = u₁' * v := by
    rw [hu₁, show u₁' * g * v = u₁' * v * g by ring, Nat.mul_div_cancel _ hg0]
  rw [eX, eY, eZ]
  refine ⟨by positivity, Nat.mul_pos hu' h₁.pos_right, Nat.mul_pos hu₁' h.pos_right, ?_, ?_, ?_⟩
  · refine ⟨u' * (a ^ 2 + b ^ 2), ?_⟩
    have := h₁.sq_add_sq
    rw [hu₁] at this
    linear_combination u' ^ 2 * this
  · apply isSquare_of_sq_mul hg0
    obtain ⟨r, hr⟩ := hM
    refine ⟨r, ?_⟩
    rw [hu, hu₁] at hr
    linear_combination hr
  · refine ⟨u₁' * (m ^ 2 + n ^ 2), ?_⟩
    have := h.sq_add_sq
    rw [hu] at this
    linear_combination u₁' ^ 2 * this

end PerfectCuboid
