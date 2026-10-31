module

public import LeanPlayground.PerfectCuboid.Basic
public import LeanPlayground.PerfectCuboid.Leech
public import LeanPlayground.PerfectCuboid.EdgeCuboid
public import LeanPlayground.PerfectCuboid.FaceCuboid

/-!
# A Leech table for face cuboids, and their 2-adic shape

A *face cuboid* (`IsFaceCuboid a b c`) has integer edges `a, b, c` with
`a² + c² = e²`, `b² + c² = f²`, `a² + b² + c² = g²`; the face diagonal `√(a² + b²)` may be
irrational. Example: `(153, 672, 104)` with `(e, f, g) = (185, 680, 697)`.

## Main results

* `FaceLeech.face_leech_dvd`, `IsFaceCuboid.leech_dvd`:
  `2⁴ · 3² · 5² · 7 · 13 · 17 ∣ a · b · c · e · f · g`.
  Each exponent is attained by a primitive face cuboid (`FaceLeech.sharp_two`, …), so the table
  is best possible: `2⁴` exactly for `(468, 4180, 399; 615, 4199, 4225)`, `3²` and `17¹` for
  `(264, 975, 448; 520, 1073, 1105)`, `5²`, `7¹`, `13¹` for `(153, 672, 104; 185, 680, 697)`.
  The local computation modulo `2⁸, 3⁴, 5³, 7², 11², 13², 17²` and `p < 60` gives the same
  exponents, and the gcd of `abcefg` over the 107 primitive face cuboids with common leg
  `< 30000` is exactly `2⁴·3²·5²·7·13·17 = 5569200`.
* **11 escapes.** `not_eleven_dvd_153_672_104`, `IsFaceCuboid.not_eleven_dvd_example`: the face
  cuboid `(153, 672, 104)` has no factor `11` in any of its six lengths, although `11` divides an
  edge of every Euler brick (`IsEulerBrick.eleven_dvd`) and `11 ∣ abcdefg` for perfect cuboids
  (`Leech.leech_dvd`). Likewise `19, 29` (same example) and `37`
  (`(468, 4180, 399)`) are not forced (`FaceLeech.not_forced_19_29_37`).
* `FaceLeech.face_two_adic`, `IsFaceCuboid.two_adic`: if `a, b, c` are not all even, exactly one
  of them is odd and the other two are divisible by `4`; if the odd edge is `a` (or `b`), one of
  the two even edges is divisible by `16` (as for perfect cuboids, Leech 1977; here it follows
  from `sixteen_dvd_of_four_dvd` applied to the square `b² + c²` resp. `a² + c²`); if the odd
  edge is the shared edge `c`, no more is forced: `v₂(a) = v₂(b) = 2` occurs, e.g.
  `(1092, 1540, 1881)`. Moreover `g` is odd.
* `IsFaceCuboid.one_odd`: a primitive face cuboid has exactly one odd edge.
* `IsFaceCuboid.three_dvd_two_edges`: `3` divides at least two edges;
  `IsFaceCuboid.seven_dvd_edge`: `7` divides an edge. (`5, 13, 17` may sit in the diagonals only.)

## The method

As in `EdgeCuboid.lean` (`EdgeLeech`): modulo `m = pʲ` we run over the *profiles*
`(x² mod m, min(v_p x, j))` of `a, b, c` (`completeE` checks the list of profiles). The descent
`(a, b, c) ↦ (a/p, b/p, c/p)` multiplies `abcefg` by `p⁶`, so we may assume `p ∤ a` or `p ∤ b`
or `p ∤ c`. `checkF` checks that whenever the three sums are squares mod `m`, the capped valuations
of `a, b, c` and the forced valuations of `e, f, g` add up to at least `k`. `shapeF` checks a
Boolean property of the profiles instead (used for the 2-adic shape, modulo `2⁴`).
-/

@[expose] public section

namespace PerfectCuboid.FaceLeech

open PerfectCuboid.Leech PerfectCuboid.EdgeLeech

/-- The check for the profiles `a`, `b`, `c` of the three edges: unless all three are divisible by
`p` or one of the three sums is a non-square mod `pʲ`, the capped valuations of `a, b, c, e, f, g`
add up to at least `k`. -/
def okF (p j k : ℕ) (L : List (ℕ × ℕ)) (a b c : ℕ × ℕ) : Bool :=
  let m := p ^ j
  let s₂ := (a.1 + c.1) % m
  let s₃ := (b.1 + c.1) % m
  let s₄ := (a.1 + b.1 + c.1) % m
  (decide (0 < a.2) && decide (0 < b.2) && decide (0 < c.2)) ||
    !(isSq L s₃ && isSq L s₄) ||
    decide (k ≤ a.2 + b.2 + c.2 + hv p j s₂ + hv p j s₃ + hv p j s₄)

/-- Run `okF` over all profiles `a, c` with `a² + c²` a square mod `pʲ`, and all profiles `b`. -/
def checkF (p j k : ℕ) (L : List (ℕ × ℕ)) : Bool :=
  L.all fun a => L.all fun c => !isSq L ((a.1 + c.1) % p ^ j) ||
    L.all fun b => okF p j k L a b c

/-- Check a property `P` of the profiles of `(a, b, c)` whenever the three sums are squares. -/
def shapeF (p j : ℕ) (L : List (ℕ × ℕ)) (P : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → Bool) : Bool :=
  L.all fun a => L.all fun c => !isSq L ((a.1 + c.1) % p ^ j) ||
    L.all fun b => !(isSq L ((b.1 + c.1) % p ^ j) && isSq L ((a.1 + b.1 + c.1) % p ^ j)) ||
      P a b c

section Check

variable {p j k : ℕ} {L : List (ℕ × ℕ)}

theorem pow_dvd_of_le_ev {x : ℕ} (h : k ≤ ev p j (x % p ^ j)) : p ^ k ∣ x :=
  (pow_dvd_pow p h).trans (pow_ev_dvd_of_mod p j x)

theorem ev_pos_of_dvd (hj : 0 < j) {x : ℕ} (h : p ∣ x) : 0 < ev p j (x % p ^ j) := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h0 : x % p ^ (j + 1) % p = 0 := by
    rw [Nat.mod_mod_of_dvd x (dvd_pow_self p (Nat.succ_ne_zero j))]
    exact Nat.mod_eq_zero_of_dvd h
  simp [ev, h0]

/-- The congruence check gives `pᵏ ∣ abcefg` for a reduced face cuboid. -/
theorem dvd_of_checkF (hp : p.Prime) (hU : checkF p j k L = true)
    (hc : completeE p j L = true) {a b c e f g : ℕ}
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    (hn : ¬ (p ∣ a ∧ p ∣ b ∧ p ∣ c)) :
    p ^ k ∣ a * b * c * e * f * g := by
  set m := p ^ j with hm
  have hm0 : 0 < m := pow_pos hp.pos j
  have md (x : ℕ) : Nat.ModEq m (x % m) x := Nat.mod_modEq x m
  have e₂ : (a ^ 2 % m + c ^ 2 % m) % m = e ^ 2 % m := by rw [← he]; exact (md _).add (md _)
  have e₃ : (b ^ 2 % m + c ^ 2 % m) % m = f ^ 2 % m := by rw [← hf]; exact (md _).add (md _)
  have e₄ : (a ^ 2 % m + b ^ 2 % m + c ^ 2 % m) % m = g ^ 2 % m := by
    rw [← hg]; exact ((md _).add (md _)).add (md _)
  have hac := List.all_eq_true.mp (List.all_eq_true.mp hU _ (mem_LE hc hm0 a)) _
    (mem_LE hc hm0 c)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hac
  rcases hac with h | h
  · rw [e₂, isSq_of_eqE hc hm0 rfl] at h
    exact absurd h (by simp)
  have hok := List.all_eq_true.mp h _ (mem_LE hc hm0 b)
  simp only [okF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hok
  rw [e₂, e₃, e₄] at hok
  have sq (x : ℕ) : isSq L (x ^ 2 % m) = true := isSq_of_eqE hc hm0 rfl
  rcases hok with (h | h) | h
  · exact absurd ⟨dvd_of_ev_pos h.1.1, dvd_of_ev_pos h.1.2, dvd_of_ev_pos h.2⟩ hn
  · simp [sq] at h
  have hdiv : p ^ (ev p j (a % m) + ev p j (b % m) + ev p j (c % m) + hv p j (e ^ 2 % m) +
      hv p j (f ^ 2 % m) + hv p j (g ^ 2 % m)) ∣ a * b * c * e * f * g := by
    simp only [pow_add]
    exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul
      (pow_ev_dvd_of_mod p j a) (pow_ev_dvd_of_mod p j b)) (pow_ev_dvd_of_mod p j c))
      (pow_hv_dvd hp)) (pow_hv_dvd hp)) (pow_hv_dvd hp)
  exact (pow_dvd_pow p h).trans hdiv

/-- Divide out `(p, p, p)` from `(a, b, c)` as often as possible. -/
theorem dvd_prodF (hp : p.Prime) (hU : checkF p j k L = true)
    (hc : completeE p j L = true) {a b c e f g : ℕ}
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    p ^ k ∣ a * b * c * e * f * g := by
  induction h : a + b + c using Nat.strong_induction_on generalizing a b c e f g with
  | _ n ih =>
  by_cases hn : p ∣ a ∧ p ∣ b ∧ p ∣ c
  swap
  · exact dvd_of_checkF hp hU hc he hf hg hn
  obtain ⟨ha, hb, hc'⟩ := hn
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : a = 0 := by omega
    simp [this]
  have sq {x y z : ℕ} (hx : p ∣ x) (hy : p ∣ y) (h : x ^ 2 + y ^ 2 = z ^ 2) : p ∣ z :=
    hp.dvd_of_dvd_pow (h ▸ dvd_add (dvd_pow hx two_ne_zero) (dvd_pow hy two_ne_zero))
  have he' := sq ha hc' he
  have hf' := sq hb hc' hf
  have hg' : p ∣ g := hp.dvd_of_dvd_pow (hg ▸ dvd_add (dvd_add (dvd_pow ha two_ne_zero)
    (dvd_pow hb two_ne_zero)) (dvd_pow hc' two_ne_zero))
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc'
  obtain ⟨e, rfl⟩ := he'
  obtain ⟨f, rfl⟩ := hf'
  obtain ⟨g, rfl⟩ := hg'
  have p2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  have cancel {x y z : ℕ} (h : (p * x) ^ 2 + (p * y) ^ 2 = (p * z) ^ 2) : x ^ 2 + y ^ 2 = z ^ 2 :=
    mul_left_cancel₀ p2 (by rw [mul_add, ← mul_pow, ← mul_pow, ← mul_pow]; exact h)
  have hg₀ : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 :=
    mul_left_cancel₀ p2 (by rw [mul_add, mul_add, ← mul_pow, ← mul_pow, ← mul_pow, ← mul_pow]
                            exact hg)
  have hlt : a + b + c < n := by
    have := hp.two_le
    rw [← h] at hn ⊢
    nlinarith
  have := ih _ hlt (cancel he) (cancel hf) hg₀ rfl
  have := this.mul_left (p ^ 6)
  rwa [show p ^ 6 * (a * b * c * e * f * g) =
    p * a * (p * b) * (p * c) * (p * e) * (p * f) * (p * g) by ring] at this

/-- The shape check: the profiles of the edges of any solution satisfy `P`. -/
theorem shape_of_shapeF (hp : 0 < p) {P : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → Bool}
    (hS : shapeF p j L P = true) (hc : completeE p j L = true) {a b c e f g : ℕ}
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    P (a ^ 2 % p ^ j, ev p j (a % p ^ j)) (b ^ 2 % p ^ j, ev p j (b % p ^ j))
      (c ^ 2 % p ^ j, ev p j (c % p ^ j)) = true := by
  set m := p ^ j with hm
  have hm0 : 0 < m := pow_pos hp j
  have md (x : ℕ) : Nat.ModEq m (x % m) x := Nat.mod_modEq x m
  have e₂ : (a ^ 2 % m + c ^ 2 % m) % m = e ^ 2 % m := by rw [← he]; exact (md _).add (md _)
  have e₃ : (b ^ 2 % m + c ^ 2 % m) % m = f ^ 2 % m := by rw [← hf]; exact (md _).add (md _)
  have e₄ : (a ^ 2 % m + b ^ 2 % m + c ^ 2 % m) % m = g ^ 2 % m := by
    rw [← hg]; exact ((md _).add (md _)).add (md _)
  have hac := List.all_eq_true.mp (List.all_eq_true.mp hS _ (mem_LE hc hm0 a)) _
    (mem_LE hc hm0 c)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hac
  rcases hac with h | h
  · rw [e₂, isSq_of_eqE hc hm0 rfl] at h
    exact absurd h (by simp)
  have hok := List.all_eq_true.mp h _ (mem_LE hc hm0 b)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hok
  rw [e₃, e₄, isSq_of_eqE hc hm0 rfl, isSq_of_eqE hc hm0 rfl] at hok
  simpa using hok

end Check

/-! ### The tables -/

/-- Profiles `(x² mod 8, min(v₂(x), 3))`. -/
def L_eight : List (ℕ × ℕ) := [(0, 2), (0, 3), (1, 0), (4, 1)]

/-- Profiles `(x² mod 3, min(v₃(x), 1))`. -/
def L_three' : List (ℕ × ℕ) := [(0, 1), (1, 0)]

theorem two_pow_dvd_F {a b c e f g : ℕ} (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    2 ^ 4 ∣ a * b * c * e * f * g :=
  dvd_prodF (j := 3) (L := L_eight) (by norm_num) (by decide +kernel) (by decide +kernel) he hf hg

theorem three_pow_dvd_F {a b c e f g : ℕ} (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    3 ^ 2 ∣ a * b * c * e * f * g :=
  dvd_prodF (j := 1) (L := L_three') (by norm_num) (by decide +kernel) (by decide +kernel) he hf hg

theorem five_pow_dvd_F {a b c e f g : ℕ} (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    5 ^ 2 ∣ a * b * c * e * f * g :=
  dvd_prodF (j := 1) (L := Leech.L_five) (by norm_num) (by decide +kernel) (by decide +kernel)
    he hf hg

theorem seven_dvd_F {a b c e f g : ℕ} (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    7 ^ 1 ∣ a * b * c * e * f * g :=
  dvd_prodF (j := 1) (L := L_seven) (by norm_num) (by decide +kernel) (by decide +kernel) he hf hg

theorem thirteen_dvd_F {a b c e f g : ℕ} (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    13 ^ 1 ∣ a * b * c * e * f * g :=
  dvd_prodF (j := 1) (L := L_thirteen) (by norm_num) (by decide +kernel) (by decide +kernel)
    he hf hg

theorem seventeen_dvd_F {a b c e f g : ℕ} (he : a ^ 2 + c ^ 2 = e ^ 2)
    (hf : b ^ 2 + c ^ 2 = f ^ 2) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    17 ^ 1 ∣ a * b * c * e * f * g :=
  dvd_prodF (j := 1) (L := L_seventeen) (by norm_num) (by decide +kernel) (by decide +kernel)
    he hf hg

/-- **Leech's divisibility for face cuboids.** If `a² + c² = e²`, `b² + c² = f²` and
`a² + b² + c² = g²`, then `2⁴ · 3² · 5² · 7 · 13 · 17 ∣ a · b · c · e · f · g`. Every exponent is
best possible (`sharp_two`, …), and no other prime is forced (`not_eleven_dvd_153_672_104`,
`not_forced_19_29_37`; locally, no prime `19 ≤ p < 60` is forced either). -/
theorem face_leech_dvd {a b c e f g : ℕ} (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    2 ^ 4 * 3 ^ 2 * 5 ^ 2 * 7 * 13 * 17 ∣ a * b * c * e * f * g := by
  have h2 := two_pow_dvd_F he hf hg
  have h3 := three_pow_dvd_F he hf hg
  have h5 := five_pow_dvd_F he hf hg
  have h7 := seven_dvd_F he hf hg
  have h13 := thirteen_dvd_F he hf hg
  have h17 := seventeen_dvd_F he hf hg
  simp only [pow_one] at *
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h5
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h7
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h13
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h17

/-! ### The 2-adic shape -/

/-- Profiles `(x² mod 16, min(v₂(x), 4))`. -/
def L_16 : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 4), (1, 0), (4, 1), (9, 0)]

/-- The 2-adic shape as a property of the capped valuations `x, y, z` of `a, b, c` and of
`s = (a² + b² + c²) mod 16`. -/
def twoShape (x y z s : ℕ) : Bool :=
  (decide (0 < x) && decide (0 < y) && decide (0 < z)) ||
  (decide (s % 8 = 1) &&
    ((x == 0 && decide (2 ≤ y) && decide (2 ≤ z)) ||
     (y == 0 && decide (2 ≤ x) && decide (2 ≤ z)) ||
     (z == 0 && decide (2 ≤ x) && decide (2 ≤ y))))

theorem twoShape_check : shapeF 2 4 L_16
    (fun a b c => twoShape a.2 b.2 c.2 ((a.1 + b.1 + c.1) % 16)) = true := by
  decide +kernel

theorem odd_of_sq_mod {g : ℕ} (h : g ^ 2 % 8 = 1) : g % 2 = 1 := by
  rw [Nat.pow_mod] at h
  have : g % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h2 : g % 2 = g % 8 % 2 := (Nat.mod_mod_of_dvd g (by norm_num)).symm
  interval_cases hg : g % 8 <;> simp_all

/-- **The 2-adic shape of a face cuboid.** If `a² + c² = e²`, `b² + c² = f²`,
`a² + b² + c² = g²` and `a, b, c` are not all even, then exactly one edge is odd, the other two
are divisible by `4`, and if the odd edge is `a` or `b` then `16` divides one of the even edges.
The space diagonal `g` is odd. This holds for `c = 0` too (Pythagorean triples `(a, b, g)`). -/
theorem face_two_adic {a b c e f g : ℕ} (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (hn : ¬ (2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c)) :
    ((a % 2 = 1 ∧ 4 ∣ b ∧ 4 ∣ c ∧ (16 ∣ b ∨ 16 ∣ c)) ∨
      (b % 2 = 1 ∧ 4 ∣ a ∧ 4 ∣ c ∧ (16 ∣ a ∨ 16 ∣ c)) ∨
      (c % 2 = 1 ∧ 4 ∣ a ∧ 4 ∣ b)) ∧ g % 2 = 1 := by
  have h := shape_of_shapeF (by norm_num) twoShape_check (by decide +kernel) he hf hg
  have hs : (a ^ 2 % 2 ^ 4 + b ^ 2 % 2 ^ 4 + c ^ 2 % 2 ^ 4) % 16 % 8 = g ^ 2 % 8 := by
    rw [← hg]; omega
  simp only [twoShape, hs, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  have fact (x : ℕ) : (ev 2 4 (x % 2 ^ 4) = 0 ↔ x % 2 = 1) ∧
      (2 ≤ ev 2 4 (x % 2 ^ 4) → 4 ∣ x) := by
    refine ⟨⟨fun h0 => ?_, fun h1 => ?_⟩, fun h2 => ?_⟩
    · by_contra hx
      have := ev_pos_of_dvd (p := 2) (j := 4) (by norm_num) (x := x) (by omega)
      omega
    · by_contra hx
      have := dvd_of_ev_pos (p := 2) (j := 4) (x := x) (by omega)
      omega
    · exact pow_dvd_of_le_ev (k := 2) h2
  obtain ⟨a0, a2⟩ := fact a
  obtain ⟨b0, b2⟩ := fact b
  obtain ⟨c0, c2⟩ := fact c
  have pos_two (x : ℕ) (hx : 0 < ev 2 4 (x % 2 ^ 4)) : 2 ∣ x := dvd_of_ev_pos hx
  rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨hs8, h⟩
  · exact absurd ⟨pos_two a h1, pos_two b h2, pos_two c h3⟩ hn
  refine ⟨?_, odd_of_sq_mod hs8⟩
  rcases h with (⟨⟨hx, hy⟩, hz⟩ | ⟨⟨hx, hy⟩, hz⟩) | ⟨⟨hx, hy⟩, hz⟩
  · exact Or.inl ⟨a0.mp hx, b2 hy, c2 hz,
      sixteen_dvd_of_four_dvd ⟨f, by rw [hf, sq]⟩ (b2 hy) (c2 hz)⟩
  · exact Or.inr (Or.inl ⟨b0.mp hx, a2 hy, c2 hz,
      sixteen_dvd_of_four_dvd ⟨e, by rw [he, sq]⟩ (a2 hy) (c2 hz)⟩)
  · exact Or.inr (Or.inr ⟨c0.mp hx, a2 hy, b2 hz⟩)

end PerfectCuboid.FaceLeech

namespace PerfectCuboid

open FaceLeech

/-- The three diagonals of a face cuboid. -/
theorem FaceLeech.diagonals {a b c : ℕ} (h : IsFaceCuboid a b c) :
    ∃ e f g : ℕ, a ^ 2 + c ^ 2 = e ^ 2 ∧ b ^ 2 + c ^ 2 = f ^ 2 ∧ a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 := by
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  exact ⟨e, f, g, by rw [he, sq], by rw [hf, sq], by rw [hg, sq]⟩

/-- The residues of a face cuboid's edges modulo `m` pass the three square tests. -/
theorem IsFaceCuboid.residues {a b c m : ℕ} (h : IsFaceCuboid a b c) (hm : 0 < m)
    {P : ℕ → ℕ → ℕ → Bool}
    (hP : allRes m (fun x y z ↦ !(IsSqMod m (x ^ 2 + z ^ 2) && IsSqMod m (y ^ 2 + z ^ 2) &&
      IsSqMod m (x ^ 2 + y ^ 2 + z ^ 2)) || P x y z) = true) :
    P (a % m) (b % m) (c % m) = true := by
  have := allRes_spec hP (Nat.mod_lt a hm) (Nat.mod_lt b hm) (Nat.mod_lt c hm)
  have h3 : IsSqMod m ((a % m) ^ 2 + (b % m) ^ 2 + (c % m) ^ 2) = true := by
    rw [← isSqMod_mod, mod_sq_add_sq_add_sq, isSqMod_mod]
    exact isSqMod_of_isSquare hm h.sq_abc
  simpa [isSqMod_res hm h.sq_ac, isSqMod_res hm h.sq_bc, h3] using this

/-- **Leech's divisibility for a face cuboid and its diagonals.** -/
theorem IsFaceCuboid.leech_dvd {a b c : ℕ} (h : IsFaceCuboid a b c) :
    ∃ e f g : ℕ, a ^ 2 + c ^ 2 = e ^ 2 ∧ b ^ 2 + c ^ 2 = f ^ 2 ∧ a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 ∧
      2 ^ 4 * 3 ^ 2 * 5 ^ 2 * 7 * 13 * 17 ∣ a * b * c * e * f * g := by
  obtain ⟨e, f, g, he, hf, hg⟩ := FaceLeech.diagonals h
  exact ⟨e, f, g, he, hf, hg, face_leech_dvd he hf hg⟩

/-- **The 2-adic shape of a face cuboid** whose edges are not all even. -/
theorem IsFaceCuboid.two_adic {a b c : ℕ} (h : IsFaceCuboid a b c)
    (hn : ¬ (2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c)) :
    (a % 2 = 1 ∧ 4 ∣ b ∧ 4 ∣ c ∧ (16 ∣ b ∨ 16 ∣ c)) ∨
      (b % 2 = 1 ∧ 4 ∣ a ∧ 4 ∣ c ∧ (16 ∣ a ∨ 16 ∣ c)) ∨
      (c % 2 = 1 ∧ 4 ∣ a ∧ 4 ∣ b) := by
  obtain ⟨e, f, g, he, hf, hg⟩ := FaceLeech.diagonals h
  exact (face_two_adic he hf hg hn).1

/-- A primitive face cuboid has exactly one odd edge. -/
theorem IsFaceCuboid.one_odd {a b c : ℕ} (h : IsFaceCuboid a b c)
    (hp : Nat.gcd (Nat.gcd a b) c = 1) :
    (a % 2 = 1 ∧ b % 2 = 0 ∧ c % 2 = 0) ∨ (a % 2 = 0 ∧ b % 2 = 1 ∧ c % 2 = 0) ∨
      (a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 1) := by
  have hn : ¬ (2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c) := by
    rintro ⟨ha, hb, hc⟩
    have := Nat.dvd_gcd (Nat.dvd_gcd ha hb) hc
    rw [hp] at this
    omega
  rcases h.two_adic hn with ⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3⟩ <;> omega

/-- The space diagonal of a primitive face cuboid is odd. -/
theorem IsFaceCuboid.space_diagonal_odd {a b c g : ℕ} (h : IsFaceCuboid a b c)
    (hp : Nat.gcd (Nat.gcd a b) c = 1) (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : g % 2 = 1 := by
  obtain ⟨e, f, -, he, hf, -⟩ := FaceLeech.diagonals h
  have hn : ¬ (2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c) := by
    rintro ⟨ha, hb, hc⟩
    have := Nat.dvd_gcd (Nat.dvd_gcd ha hb) hc
    rw [hp] at this
    omega
  exact (face_two_adic he hf hg hn).2

/-- At least two edges of a face cuboid are divisible by `3` (so `9 ∣ abc`). -/
theorem IsFaceCuboid.three_dvd_two_edges {a b c : ℕ} (h : IsFaceCuboid a b c) :
    (3 ∣ a ∧ 3 ∣ b) ∨ (3 ∣ b ∧ 3 ∣ c) ∨ (3 ∣ c ∧ 3 ∣ a) := by
  have := h.residues (m := 3) (by norm_num)
    (P := fun x y z ↦ (x % 3 == 0 && y % 3 == 0) || (y % 3 == 0 && z % 3 == 0) ||
      (z % 3 == 0 && x % 3 == 0)) (by decide +kernel)
  simpa [mod_mod_eq_zero_iff (dvd_refl 3), or_assoc, Nat.dvd_iff_mod_eq_zero] using this

/-- Some edge of a face cuboid is divisible by `7`. -/
theorem IsFaceCuboid.seven_dvd_edge {a b c : ℕ} (h : IsFaceCuboid a b c) :
    7 ∣ a ∨ 7 ∣ b ∨ 7 ∣ c := by
  have := h.residues (m := 7) (by norm_num)
    (P := fun x y z ↦ x % 7 == 0 || y % 7 == 0 || z % 7 == 0) (by decide +kernel)
  simpa [mod_mod_eq_zero_iff (dvd_refl 7), or_assoc, Nat.dvd_iff_mod_eq_zero] using this

/-! ### Sharpness, and the primes that escape -/

/-- **11 escapes.** The face cuboid `(153, 672, 104)` (diagonals `185, 680, 697`) has no factor
`11` in any of its six lengths. By contrast `11` divides an edge of every Euler brick
(`IsEulerBrick.eleven_dvd`, Kraitchik) and `11 ∣ abcdefg` for every perfect cuboid
(`Leech.leech_dvd`). -/
theorem not_eleven_dvd_153_672_104 : ¬ 11 ∣ 153 * 672 * 104 * 185 * 680 * 697 := by
  norm_num

theorem FaceLeech.sq_eq_sq_nat {x y : ℕ} (h : x ^ 2 = y ^ 2) : x = y :=
  Nat.pow_left_injective two_ne_zero h

/-- There is a face cuboid none of whose lengths is divisible by `11`. -/
theorem IsFaceCuboid.not_eleven_dvd_example :
    ∃ a b c : ℕ, IsFaceCuboid a b c ∧ ∀ e f g : ℕ, a ^ 2 + c ^ 2 = e ^ 2 →
      b ^ 2 + c ^ 2 = f ^ 2 → a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 → ¬ 11 ∣ a * b * c * e * f * g := by
  refine ⟨153, 672, 104, isFaceCuboid_153_672_104, fun e f g he hf hg => ?_⟩
  obtain rfl : e = 185 := (FaceLeech.sq_eq_sq_nat (by rw [← he]; norm_num)).symm
  obtain rfl : f = 680 := (FaceLeech.sq_eq_sq_nat (by rw [← hf]; norm_num)).symm
  obtain rfl : g = 697 := (FaceLeech.sq_eq_sq_nat (by rw [← hg]; norm_num)).symm
  exact not_eleven_dvd_153_672_104

namespace FaceLeech

/-- `(468, 4180, 399)` is a face cuboid (diagonals `615, 4199, 4225`; `468² + 4180²` is not a
square). -/
theorem isFaceCuboid_468_4180_399 : IsFaceCuboid 468 4180 399 where
  pos_a := by norm_num
  pos_b := by norm_num
  pos_c := by norm_num
  sq_ac := ⟨615, by norm_num⟩
  sq_bc := ⟨4199, by norm_num⟩
  sq_abc := ⟨4225, by norm_num⟩

theorem not_isSquare_468_4180 : ¬ IsSquare (468 ^ 2 + 4180 ^ 2) := by
  rintro ⟨r, hr⟩
  rcases le_or_gt r 4206 with h | h <;> nlinarith

/-- `(264, 975, 448)` is a face cuboid (diagonals `520, 1073, 1105`; `264² + 975²` is not a
square). -/
theorem isFaceCuboid_264_975_448 : IsFaceCuboid 264 975 448 where
  pos_a := by norm_num
  pos_b := by norm_num
  pos_c := by norm_num
  sq_ac := ⟨520, by norm_num⟩
  sq_bc := ⟨1073, by norm_num⟩
  sq_abc := ⟨1105, by norm_num⟩

theorem not_isSquare_264_975 : ¬ IsSquare (264 ^ 2 + 975 ^ 2) := by
  rintro ⟨r, hr⟩
  rcases le_or_gt r 1010 with h | h <;> nlinarith

/-- `2⁴` is attained exactly: `(468, 4180, 399; 615, 4199, 4225)`. -/
theorem sharp_two : ¬ 2 ^ 5 ∣ 468 * 4180 * 399 * 615 * 4199 * 4225 := by norm_num

/-- `3²` and `17` are attained exactly: `(264, 975, 448; 520, 1073, 1105)`. -/
theorem sharp_three_seventeen : ¬ 3 ^ 3 ∣ 264 * 975 * 448 * 520 * 1073 * 1105 ∧
    ¬ 17 ^ 2 ∣ 264 * 975 * 448 * 520 * 1073 * 1105 := by norm_num

/-- `5²`, `7` and `13` are attained exactly: `(153, 672, 104; 185, 680, 697)`. -/
theorem sharp_five_seven_thirteen : ¬ 5 ^ 3 ∣ 153 * 672 * 104 * 185 * 680 * 697 ∧
    ¬ 7 ^ 2 ∣ 153 * 672 * 104 * 185 * 680 * 697 ∧
    ¬ 13 ^ 2 ∣ 153 * 672 * 104 * 185 * 680 * 697 := by norm_num

/-- `19` and `29` are not forced (`(153, 672, 104)`), nor is `37` (`(468, 4180, 399)`); all
three divide `abcdefg` for every perfect cuboid. -/
theorem not_forced_19_29_37 : ¬ 19 ∣ 153 * 672 * 104 * 185 * 680 * 697 ∧
    ¬ 29 ∣ 153 * 672 * 104 * 185 * 680 * 697 ∧
    ¬ 37 ∣ 468 * 4180 * 399 * 615 * 4199 * 4225 := by norm_num


/-! ### Stretch: a Leech table for Euler bricks

For an Euler brick (`a² + b² = d²`, `a² + c² = e²`, `b² + c² = f²`, no condition on the space
diagonal) the same method gives `2⁸ · 3⁴ · 5² · 11 ∣ a · b · c · d · e · f`; the exponents are
best possible (the gcd over the 87 primitive Euler bricks with edges `≤ 2·10⁵` is exactly
`2⁸ · 3⁴ · 5² · 11 = 5702400`; `(44, 117, 240; 125, 244, 267)` attains `2⁸, 3⁴, 11`,
`(187, 1020, 1584; 1037, 1595, 1884)` attains `5²`). The edge-only statements of `Basic.lean`
(`two_dvd_four`, `sixteen_dvd`, `two_dvd_three`, `nine_dvd`, `five_dvd`, `eleven_dvd`) give only
`2⁶ · 3³ · 5 · 11 ∣ abc`. -/

open PerfectCuboid.Leech PerfectCuboid.EdgeLeech

/-- The check for the profiles `a, b, c` of an Euler brick. -/
def okB (p j k : ℕ) (L : List (ℕ × ℕ)) (a b c : ℕ × ℕ) : Bool :=
  let m := p ^ j
  let s₁ := (a.1 + b.1) % m
  let s₂ := (a.1 + c.1) % m
  let s₃ := (b.1 + c.1) % m
  (decide (0 < a.2) && decide (0 < b.2) && decide (0 < c.2)) ||
    !(isSq L s₂ && isSq L s₃) ||
    decide (k ≤ a.2 + b.2 + c.2 + hv p j s₁ + hv p j s₂ + hv p j s₃)

/-- Run `okB` over all profiles `a, b` with `a² + b²` a square mod `pʲ`, and all profiles `c`. -/
def checkB (p j k : ℕ) (L : List (ℕ × ℕ)) : Bool :=
  L.all fun a => L.all fun b => !isSq L ((a.1 + b.1) % p ^ j) ||
    L.all fun c => okB p j k L a b c

section CheckB

variable {p j k : ℕ} {L : List (ℕ × ℕ)}

theorem dvd_of_checkB (hp : p.Prime) (hU : checkB p j k L = true)
    (hc : completeE p j L = true) {a b c d e f : ℕ}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hn : ¬ (p ∣ a ∧ p ∣ b ∧ p ∣ c)) :
    p ^ k ∣ a * b * c * d * e * f := by
  set m := p ^ j with hm
  have hm0 : 0 < m := pow_pos hp.pos j
  have md (x : ℕ) : Nat.ModEq m (x % m) x := Nat.mod_modEq x m
  have e₁ : (a ^ 2 % m + b ^ 2 % m) % m = d ^ 2 % m := by rw [← hd]; exact (md _).add (md _)
  have e₂ : (a ^ 2 % m + c ^ 2 % m) % m = e ^ 2 % m := by rw [← he]; exact (md _).add (md _)
  have e₃ : (b ^ 2 % m + c ^ 2 % m) % m = f ^ 2 % m := by rw [← hf]; exact (md _).add (md _)
  have hab := List.all_eq_true.mp (List.all_eq_true.mp hU _ (mem_LE hc hm0 a)) _
    (mem_LE hc hm0 b)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hab
  rcases hab with h | h
  · rw [e₁, isSq_of_eqE hc hm0 rfl] at h
    exact absurd h (by simp)
  have hok := List.all_eq_true.mp h _ (mem_LE hc hm0 c)
  simp only [okB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hok
  rw [e₁, e₂, e₃] at hok
  have sq (x : ℕ) : isSq L (x ^ 2 % m) = true := isSq_of_eqE hc hm0 rfl
  rcases hok with (h | h) | h
  · exact absurd ⟨dvd_of_ev_pos h.1.1, dvd_of_ev_pos h.1.2, dvd_of_ev_pos h.2⟩ hn
  · simp [sq] at h
  have hdiv : p ^ (ev p j (a % m) + ev p j (b % m) + ev p j (c % m) + hv p j (d ^ 2 % m) +
      hv p j (e ^ 2 % m) + hv p j (f ^ 2 % m)) ∣ a * b * c * d * e * f := by
    simp only [pow_add]
    exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul
      (pow_ev_dvd_of_mod p j a) (pow_ev_dvd_of_mod p j b)) (pow_ev_dvd_of_mod p j c))
      (pow_hv_dvd hp)) (pow_hv_dvd hp)) (pow_hv_dvd hp)
  exact (pow_dvd_pow p h).trans hdiv

theorem dvd_prodB (hp : p.Prime) (hU : checkB p j k L = true)
    (hc : completeE p j L = true) {a b c d e f : ℕ}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    p ^ k ∣ a * b * c * d * e * f := by
  induction h : a + b + c using Nat.strong_induction_on generalizing a b c d e f with
  | _ n ih =>
  by_cases hn : p ∣ a ∧ p ∣ b ∧ p ∣ c
  swap
  · exact dvd_of_checkB hp hU hc hd he hf hn
  obtain ⟨ha, hb, hc'⟩ := hn
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : a = 0 := by omega
    simp [this]
  have sq {x y z : ℕ} (hx : p ∣ x) (hy : p ∣ y) (h : x ^ 2 + y ^ 2 = z ^ 2) : p ∣ z :=
    hp.dvd_of_dvd_pow (h ▸ dvd_add (dvd_pow hx two_ne_zero) (dvd_pow hy two_ne_zero))
  have hd' := sq ha hb hd
  have he' := sq ha hc' he
  have hf' := sq hb hc' hf
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc'
  obtain ⟨d, rfl⟩ := hd'
  obtain ⟨e, rfl⟩ := he'
  obtain ⟨f, rfl⟩ := hf'
  have p2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  have cancel {x y z : ℕ} (h : (p * x) ^ 2 + (p * y) ^ 2 = (p * z) ^ 2) : x ^ 2 + y ^ 2 = z ^ 2 :=
    mul_left_cancel₀ p2 (by rw [mul_add, ← mul_pow, ← mul_pow, ← mul_pow]; exact h)
  have hlt : a + b + c < n := by
    have := hp.two_le
    rw [← h] at hn ⊢
    nlinarith
  have := ih _ hlt (cancel hd) (cancel he) (cancel hf) rfl
  have := this.mul_left (p ^ 6)
  rwa [show p ^ 6 * (a * b * c * d * e * f) =
    p * a * (p * b) * (p * c) * (p * d) * (p * e) * (p * f) by ring] at this

end CheckB

theorem two_pow_dvd_B {a b c d e f : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    2 ^ 8 ∣ a * b * c * d * e * f :=
  dvd_prodB (j := 7) (L := L_two) (by norm_num) (by decide +kernel) (by decide +kernel) hd he hf

theorem three_pow_dvd_B {a b c d e f : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    3 ^ 4 ∣ a * b * c * d * e * f :=
  dvd_prodB (j := 3) (L := L_three) (by norm_num) (by decide +kernel) (by decide +kernel) hd he hf

theorem five_pow_dvd_B {a b c d e f : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    5 ^ 2 ∣ a * b * c * d * e * f :=
  dvd_prodB (j := 1) (L := Leech.L_five) (by norm_num) (by decide +kernel) (by decide +kernel)
    hd he hf

theorem eleven_dvd_B {a b c d e f : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    11 ^ 1 ∣ a * b * c * d * e * f :=
  dvd_prodB (j := 1) (L := L_eleven) (by norm_num) (by decide +kernel) (by decide +kernel)
    hd he hf

/-- **Leech-type divisibility for Euler bricks.** If `a² + b² = d²`, `a² + c² = e²` and
`b² + c² = f²`, then `2⁸ · 3⁴ · 5² · 11 ∣ a · b · c · d · e · f`. -/
theorem brick_leech_dvd {a b c d e f : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2) :
    2 ^ 8 * 3 ^ 4 * 5 ^ 2 * 11 ∣ a * b * c * d * e * f := by
  have h2 := two_pow_dvd_B hd he hf
  have h3 := three_pow_dvd_B hd he hf
  have h5 := five_pow_dvd_B hd he hf
  have h11 := eleven_dvd_B hd he hf
  simp only [pow_one] at *
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h5
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h11

/-- `2⁸`, `3⁴` and `11` are attained exactly by `(44, 117, 240; 125, 244, 267)`, and `5²` by
`(187, 1020, 1584; 1037, 1595, 1884)`. -/
theorem brick_sharp : ¬ 2 ^ 9 ∣ 44 * 117 * 240 * 125 * 244 * 267 ∧
    ¬ 3 ^ 5 ∣ 44 * 117 * 240 * 125 * 244 * 267 ∧ ¬ 11 ^ 2 ∣ 44 * 117 * 240 * 125 * 244 * 267 ∧
    ¬ 5 ^ 3 ∣ 187 * 1020 * 1584 * 1037 * 1595 * 1884 := by norm_num

end FaceLeech

/-- Leech-type divisibility for an Euler brick and its face diagonals. -/
theorem IsEulerBrick.leech_dvd {a b c : ℕ} (h : IsEulerBrick a b c) :
    ∃ d e f : ℕ, a ^ 2 + b ^ 2 = d ^ 2 ∧ a ^ 2 + c ^ 2 = e ^ 2 ∧ b ^ 2 + c ^ 2 = f ^ 2 ∧
      2 ^ 8 * 3 ^ 4 * 5 ^ 2 * 11 ∣ a * b * c * d * e * f := by
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ca
  obtain ⟨f, hf⟩ := h.sq_bc
  have hd' : a ^ 2 + b ^ 2 = d ^ 2 := by rw [hd, sq]
  have he' : a ^ 2 + c ^ 2 = e ^ 2 := by rw [add_comm, he, sq]
  have hf' : b ^ 2 + c ^ 2 = f ^ 2 := by rw [hf, sq]
  exact ⟨d, e, f, hd', he', hf', FaceLeech.brick_leech_dvd hd' he' hf'⟩

end PerfectCuboid
