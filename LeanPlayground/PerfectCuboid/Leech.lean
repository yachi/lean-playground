module

public import LeanPlayground.PerfectCuboid.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Prime

/-!
# Leech's divisibility of the seven lengths of a perfect cuboid

Leech (as reported in Guy, *Unsolved Problems in Number Theory*, problem D18) observed that the
product of the three edges, three face diagonals and space diagonal of a perfect cuboid is
divisible by
`2⁸ · 3⁴ · 5³ · 7 · 11 · 13 · 17 · 19 · 29 · 37`. This file proves it:

* `leech_dvd`: if `a² + b² = d²`, `a² + c² = e²`, `b² + c² = f²` and `a² + b² + c² = g²` in `ℕ`,
  then `2⁸ · 3⁴ · 5³ · 7 · 11 · 13 · 17 · 19 · 29 · 37 ∣ abcdefg`;
* `IsPerfectCuboid.leech_dvd`: the same for a perfect cuboid and its diagonals.

`Basic.lean` already shows that each of the primes divides an edge or a diagonal. The new part is
the exponents `2⁸`, `3⁴` and `5³` of the whole product.

## How it is proved

Every prime power `pᵏ` is a congruence check modulo `m = pʲ`, with `(p, j, k)` one of `(2, 7, 8)`,
`(3, 3, 4)`, `(5, 1, 3)` and `(q, 1, 1)` for `q = 7, …, 37`.

* `ev p j r = min(v_p(r), j)` is the `p`-adic valuation of a residue, capped at `j`, and
  `p ^ ev p j (x % pʲ) ∣ x` (`pow_ev_dvd_of_mod`).
* A diagonal only enters through its square: if `pᵗ ∣ d²` then `p ^ ⌈t/2⌉ ∣ d`
  (`pow_half_dvd`).
* After dividing by `p` as often as possible, some edge, say `a`, is prime to `p` (`dvd_prod`,
  by strong induction and the symmetry of the problem). Then the bound depends only on
  `a² mod m`, which is a unit square, and on the *profiles* `(x² mod m, ev p j (x mod m))` of `b`
  and `c`.
* `check` runs over all these profiles. Whenever the four sums of squares are squares mod `m`,
  it checks that the capped valuations add up to at least `k`. The lists of unit squares `U` and
  of profiles `L` are written out, and `complete` checks that they cover every residue. Both
  are `Bool` computations that the kernel runs (`decide +kernel`); the largest, modulo `128`,
  has `16 · 26² = 10816` cases.
-/

@[expose] public section

namespace PerfectCuboid.Leech

/-- `ev p j r = min (v_p r) j`, where `v_p 0 = ∞`. -/
def ev (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, r => if r % p = 0 then ev p j (r / p) + 1 else 0

theorem ev_le (p j r : ℕ) : ev p j r ≤ j := by
  induction j generalizing r with
  | zero => simp [ev]
  | succ j ih =>
    simp only [ev]
    split_ifs
    · exact Nat.succ_le_succ (ih _)
    · exact Nat.zero_le _

theorem pow_ev_dvd (p j r : ℕ) : p ^ ev p j r ∣ r := by
  induction j generalizing r with
  | zero => simp [ev]
  | succ j ih =>
    simp only [ev]
    split_ifs with h
    · rw [pow_succ]
      conv_rhs => rw [← Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)]
      exact mul_dvd_mul_right (ih _) p
    · simp

theorem pow_ev_dvd_of_mod (p j x : ℕ) : p ^ ev p j (x % p ^ j) ∣ x :=
  (Nat.dvd_mod_iff (pow_dvd_pow p (ev_le p j _))).mp (pow_ev_dvd p j _)

theorem pow_half_dvd {p t d : ℕ} (hp : p.Prime) (h : p ^ t ∣ d ^ 2) : p ^ ((t + 1) / 2) ∣ d := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  rw [hp.pow_dvd_iff_le_factorization hd]
  rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hd), Nat.factorization_pow] at h
  simp only [Finsupp.smul_apply, smul_eq_mul] at h
  omega

/-- The exponent of `p` that a diagonal `d` with `d² ≡ s (mod pʲ)` must carry. -/
def hv (p j s : ℕ) : ℕ := (ev p j s + 1) / 2

theorem pow_hv_dvd {p j d : ℕ} (hp : p.Prime) : p ^ hv p j (d ^ 2 % p ^ j) ∣ d :=
  pow_half_dvd hp (pow_ev_dvd_of_mod p j _)

/-- Whether `s` is a square modulo `pʲ`, read off the list of profiles. -/
def isSq (L : List (ℕ × ℕ)) (s : ℕ) : Bool := L.any fun x => x.1 == s

/-- The check for `a² ≡ A` and the profiles `b`, `c`: if all four sums of squares are squares,
the capped valuations of `b, c, d, e, f, g` add up to at least `k`. -/
def ok (p j k : ℕ) (L : List (ℕ × ℕ)) (A : ℕ) (b c : ℕ × ℕ) : Bool :=
  let m := p ^ j
  let s₁ := (A + b.1) % m
  let s₂ := (A + c.1) % m
  let s₃ := (b.1 + c.1) % m
  let s₄ := (A + b.1 + c.1) % m
  !(isSq L s₁ && isSq L s₂ && isSq L s₃ && isSq L s₄) ||
    decide (k ≤ b.2 + c.2 + hv p j s₁ + hv p j s₂ + hv p j s₃ + hv p j s₄)

/-- Run `ok` over all unit squares `A ∈ U` and profiles `b, c ∈ L`. -/
def check (p j k : ℕ) (U : List ℕ) (L : List (ℕ × ℕ)) : Bool :=
  U.all fun A => L.all fun b => L.all fun c => ok p j k L A b c

/-- `U` contains the square of every unit and `L` the profile of every residue modulo `pʲ`. -/
def complete (p j : ℕ) (U : List ℕ) (L : List (ℕ × ℕ)) : Bool :=
  (List.range (p ^ j)).all fun r =>
    L.contains (r ^ 2 % p ^ j, ev p j r) && (r % p == 0 || U.contains (r ^ 2 % p ^ j))

section Check

variable {p j k : ℕ} {U : List ℕ} {L : List (ℕ × ℕ)}

theorem mem_L (hc : complete p j U L = true) (hj : 0 < p ^ j) (x : ℕ) :
    (x ^ 2 % p ^ j, ev p j (x % p ^ j)) ∈ L := by
  have := List.all_eq_true.mp hc (x % p ^ j) (List.mem_range.mpr (Nat.mod_lt _ hj))
  simp only [Bool.and_eq_true, List.contains_iff_mem] at this
  rw [Nat.pow_mod]
  exact this.1

theorem mem_U (hc : complete p j U L = true) (hj : 0 < j) (hp : 0 < p) {x : ℕ} (hx : ¬ p ∣ x) :
    x ^ 2 % p ^ j ∈ U := by
  have hpj : 0 < p ^ j := pow_pos hp j
  have := List.all_eq_true.mp hc (x % p ^ j) (List.mem_range.mpr (Nat.mod_lt _ hpj))
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at this
  rw [Nat.mod_mod_of_dvd _ (dvd_pow_self p hj.ne')] at this
  rw [Nat.pow_mod]
  exact this.2.resolve_left (fun h => hx (Nat.dvd_of_mod_eq_zero h))

theorem isSq_of_eq (hc : complete p j U L = true) (hj : 0 < p ^ j) {s d : ℕ}
    (h : s = d ^ 2 % p ^ j) : isSq L s = true := by
  rw [isSq, List.any_eq_true, h]
  exact ⟨_, mem_L hc hj d, by simp⟩

/-- The congruence check gives `pᵏ ∣ abcdefg` when `p ∤ a`. -/
theorem dvd_of_check (hp : p.Prime) (hj : 0 < j) (hU : check p j k U L = true)
    (hc : complete p j U L = true) {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) (ha : ¬ p ∣ a) :
    p ^ k ∣ a * b * c * d * e * f * g := by
  set m := p ^ j with hm
  have hm0 : 0 < m := pow_pos hp.pos j
  have hok := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hU _
    (mem_U hc hj hp.pos ha)) _ (mem_L hc hm0 b)) _ (mem_L hc hm0 c)
  have md (x : ℕ) : Nat.ModEq m (x % m) x := Nat.mod_modEq x m
  have e₁ : (a ^ 2 % m + b ^ 2 % m) % m = d ^ 2 % m := by rw [← hd]; exact (md _).add (md _)
  have e₂ : (a ^ 2 % m + c ^ 2 % m) % m = e ^ 2 % m := by rw [← he]; exact (md _).add (md _)
  have e₃ : (b ^ 2 % m + c ^ 2 % m) % m = f ^ 2 % m := by rw [← hf]; exact (md _).add (md _)
  have e₄ : (a ^ 2 % m + b ^ 2 % m + c ^ 2 % m) % m = g ^ 2 % m := by
    rw [← hg]; exact ((md _).add (md _)).add (md _)
  simp only [ok, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hok
  rw [e₁, e₂, e₃, e₄] at hok
  rcases hok with h | h
  · have sq (x : ℕ) : isSq L (x ^ 2 % m) = true := isSq_of_eq hc hm0 rfl
    simp [sq] at h
  have hdiv : p ^ (ev p j (b % m) + ev p j (c % m) + hv p j (d ^ 2 % m) + hv p j (e ^ 2 % m) +
      hv p j (f ^ 2 % m) + hv p j (g ^ 2 % m)) ∣ b * c * d * e * f * g := by
    simp only [pow_add]
    exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul
      (pow_ev_dvd_of_mod p j b) (pow_ev_dvd_of_mod p j c)) (pow_hv_dvd hp)) (pow_hv_dvd hp))
      (pow_hv_dvd hp)) (pow_hv_dvd hp)
  have := ((pow_dvd_pow p h).trans hdiv).mul_left a
  rwa [show a * (b * c * d * e * f * g) = a * b * c * d * e * f * g by ring] at this

/-- Divide out common factors of `p`, and use the symmetry of the problem to make `p ∤ a`. -/
theorem dvd_prod (hp : p.Prime) (hj : 0 < j) (hU : check p j k U L = true)
    (hc : complete p j U L = true) {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : p ^ k ∣ a * b * c * d * e * f * g := by
  induction h : a + b + c using Nat.strong_induction_on generalizing a b c d e f g with
  | _ n ih =>
  by_cases ha : p ∣ a
  swap
  · exact dvd_of_check hp hj hU hc hd he hf hg ha
  by_cases hb : p ∣ b
  swap
  · have := dvd_of_check hp hj hU hc (a := b) (b := a) (c := c) (d := d) (e := f) (f := e)
      (by rw [← hd]; ring) hf he (by rw [← hg]; ring) hb
    rwa [show b * a * c * d * f * e * g = a * b * c * d * e * f * g by ring] at this
  by_cases hc' : p ∣ c
  swap
  · have := dvd_of_check hp hj hU hc (a := c) (b := a) (c := b) (d := e) (e := f) (f := d)
      (by rw [← he]; ring) (by rw [← hf]; ring) hd (by rw [← hg]; ring) hc'
    rwa [show c * a * b * e * f * d * g = a * b * c * d * e * f * g by ring] at this
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : a = 0 := by omega
    simp [this]
  have sq {x y z : ℕ} (hx : p ∣ x) (hy : p ∣ y) (h : x ^ 2 + y ^ 2 = z ^ 2) : p ∣ z :=
    hp.dvd_of_dvd_pow (h ▸ dvd_add (dvd_pow hx two_ne_zero) (dvd_pow hy two_ne_zero))
  have hd' := sq ha hb hd
  have he' := sq ha hc' he
  have hf' := sq hb hc' hf
  have hg' := sq hd' hc' (hd ▸ hg)
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc'
  obtain ⟨d, rfl⟩ := hd'
  obtain ⟨e, rfl⟩ := he'
  obtain ⟨f, rfl⟩ := hf'
  obtain ⟨g, rfl⟩ := hg'
  have p2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  have cancel {x y z : ℕ} (h : (p * x) ^ 2 + (p * y) ^ 2 = (p * z) ^ 2) : x ^ 2 + y ^ 2 = z ^ 2 :=
    mul_left_cancel₀ p2 (by rw [mul_add, ← mul_pow, ← mul_pow, ← mul_pow]; exact h)
  have hg₀ : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
    refine (mul_left_cancel₀ p2 ?_).symm
    rw [mul_add, mul_add, ← mul_pow, ← mul_pow, ← mul_pow, ← mul_pow]
    exact hg
  have hlt : a + b + c < n := by
    have := hp.two_le
    rw [← h] at hn ⊢
    nlinarith
  have := ih _ hlt (cancel hd) (cancel he) (cancel hf) hg₀.symm rfl
  have := this.mul_left (p ^ 7)
  rwa [show p ^ 7 * (a * b * c * d * e * f * g) =
    p * a * (p * b) * (p * c) * (p * d) * (p * e) * (p * f) * (p * g) by ring] at this

end Check

/-! ### The tables -/

/-- Unit squares modulo `128`. -/
def U_two : List ℕ := [1, 9, 17, 25, 33, 41, 49, 57, 65, 73, 81, 89, 97, 105, 113, 121]

/-- Profiles `(x² mod 128, min(v_2(x), 7))`. -/
def L_two : List (ℕ × ℕ) := [(0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (4, 1), (9, 0), (16, 2),
  (17, 0), (25, 0), (33, 0), (36, 1), (41, 0), (49, 0), (57, 0), (64, 3), (65, 0), (68, 1), (73, 0),
  (81, 0), (89, 0), (97, 0), (100, 1), (105, 0), (113, 0), (121, 0)]

theorem two_pow_dvd {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : 2 ^ 8 ∣ a * b * c * d * e * f * g :=
  dvd_prod (j := 7) (U := U_two) (L := L_two) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

/-- Unit squares modulo `27`. -/
def U_three : List ℕ := [1, 4, 7, 10, 13, 16, 19, 22, 25]

/-- Profiles `(x² mod 27, min(v_3(x), 3))`. -/
def L_three : List (ℕ × ℕ) := [(0, 2), (0, 3), (1, 0), (4, 0), (7, 0), (9, 1), (10, 0), (13, 0),
  (16, 0), (19, 0), (22, 0), (25, 0)]

theorem three_pow_dvd {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : 3 ^ 4 ∣ a * b * c * d * e * f * g :=
  dvd_prod (j := 3) (U := U_three) (L := L_three) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

/-- Unit squares modulo `5`. -/
def U_five : List ℕ := [1, 4]

/-- Profiles `(x² mod 5, min(v_5(x), 1))`. -/
def L_five : List (ℕ × ℕ) := [(0, 1), (1, 0), (4, 0)]

theorem five_pow_dvd {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : 5 ^ 3 ∣ a * b * c * d * e * f * g :=
  dvd_prod (j := 1) (U := U_five) (L := L_five) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

/-- Unit squares modulo `7`. -/
def U_seven : List ℕ := [1, 2, 4]

/-- Profiles `(x² mod 7, min(v_7(x), 1))`. -/
def L_seven : List (ℕ × ℕ) := [(0, 1), (1, 0), (2, 0), (4, 0)]

theorem seven_pow_dvd {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : 7 ^ 1 ∣ a * b * c * d * e * f * g :=
  dvd_prod (j := 1) (U := U_seven) (L := L_seven) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

/-- Unit squares modulo `11`. -/
def U_eleven : List ℕ := [1, 3, 4, 5, 9]

/-- Profiles `(x² mod 11, min(v_11(x), 1))`. -/
def L_eleven : List (ℕ × ℕ) := [(0, 1), (1, 0), (3, 0), (4, 0), (5, 0), (9, 0)]

theorem eleven_pow_dvd {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : 11 ^ 1 ∣ a * b * c * d * e * f * g :=
  dvd_prod (j := 1) (U := U_eleven) (L := L_eleven) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

/-- Unit squares modulo `13`. -/
def U_thirteen : List ℕ := [1, 3, 4, 9, 10, 12]

/-- Profiles `(x² mod 13, min(v_13(x), 1))`. -/
def L_thirteen : List (ℕ × ℕ) := [(0, 1), (1, 0), (3, 0), (4, 0), (9, 0), (10, 0), (12, 0)]

theorem thirteen_pow_dvd {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : 13 ^ 1 ∣ a * b * c * d * e * f * g :=
  dvd_prod (j := 1) (U := U_thirteen) (L := L_thirteen) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

/-- Unit squares modulo `17`. -/
def U_seventeen : List ℕ := [1, 2, 4, 8, 9, 13, 15, 16]

/-- Profiles `(x² mod 17, min(v_17(x), 1))`. -/
def L_seventeen : List (ℕ × ℕ) := [(0, 1), (1, 0), (2, 0), (4, 0), (8, 0), (9, 0), (13, 0), (15, 0),
  (16, 0)]

theorem seventeen_pow_dvd {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : 17 ^ 1 ∣ a * b * c * d * e * f * g :=
  dvd_prod (j := 1) (U := U_seventeen) (L := L_seventeen) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

/-- Unit squares modulo `19`. -/
def U_nineteen : List ℕ := [1, 4, 5, 6, 7, 9, 11, 16, 17]

/-- Profiles `(x² mod 19, min(v_19(x), 1))`. -/
def L_nineteen : List (ℕ × ℕ) := [(0, 1), (1, 0), (4, 0), (5, 0), (6, 0), (7, 0), (9, 0), (11, 0),
  (16, 0), (17, 0)]

theorem nineteen_pow_dvd {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : 19 ^ 1 ∣ a * b * c * d * e * f * g :=
  dvd_prod (j := 1) (U := U_nineteen) (L := L_nineteen) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

/-- Unit squares modulo `29`. -/
def U_twentynine : List ℕ := [1, 4, 5, 6, 7, 9, 13, 16, 20, 22, 23, 24, 25, 28]

/-- Profiles `(x² mod 29, min(v_29(x), 1))`. -/
def L_twentynine : List (ℕ × ℕ) := [(0, 1), (1, 0), (4, 0), (5, 0), (6, 0), (7, 0), (9, 0), (13, 0),
  (16, 0), (20, 0), (22, 0), (23, 0), (24, 0), (25, 0), (28, 0)]

theorem twentynine_pow_dvd {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : 29 ^ 1 ∣ a * b * c * d * e * f * g :=
  dvd_prod (j := 1) (U := U_twentynine) (L := L_twentynine) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

/-- Unit squares modulo `37`. -/
def U_thirtyseven : List ℕ := [1, 3, 4, 7, 9, 10, 11, 12, 16, 21, 25, 26, 27, 28, 30, 33, 34, 36]

/-- Profiles `(x² mod 37, min(v_37(x), 1))`. -/
def L_thirtyseven : List (ℕ × ℕ) := [(0, 1), (1, 0), (3, 0), (4, 0), (7, 0), (9, 0), (10, 0),
  (11, 0), (12, 0), (16, 0), (21, 0), (25, 0), (26, 0), (27, 0), (28, 0), (30, 0), (33, 0), (34, 0),
  (36, 0)]

theorem thirtyseven_pow_dvd {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : 37 ^ 1 ∣ a * b * c * d * e * f * g :=
  dvd_prod (j := 1) (U := U_thirtyseven) (L := L_thirtyseven) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) hd he hf hg

/-! ### Leech's theorem -/

/-- **Leech.** The product of the edges, face diagonals and space diagonal of a perfect cuboid
is divisible by `2⁸ · 3⁴ · 5³ · 7 · 11 · 13 · 17 · 19 · 29 · 37`. -/
theorem leech_dvd {a b c d e f g : ℕ} (hd : a ^ 2 + b ^ 2 = d ^ 2)
    (he : a ^ 2 + c ^ 2 = e ^ 2) (hf : b ^ 2 + c ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    2 ^ 8 * 3 ^ 4 * 5 ^ 3 * 7 * 11 * 13 * 17 * 19 * 29 * 37 ∣ a * b * c * d * e * f * g := by
  have h_two := two_pow_dvd hd he hf hg
  have h_three := three_pow_dvd hd he hf hg
  have h_five := five_pow_dvd hd he hf hg
  have h_seven := seven_pow_dvd hd he hf hg
  have h_eleven := eleven_pow_dvd hd he hf hg
  have h_thirteen := thirteen_pow_dvd hd he hf hg
  have h_seventeen := seventeen_pow_dvd hd he hf hg
  have h_nineteen := nineteen_pow_dvd hd he hf hg
  have h_twentynine := twentynine_pow_dvd hd he hf hg
  have h_thirtyseven := thirtyseven_pow_dvd hd he hf hg
  simp only [pow_one] at *
  have := h_two
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h_three
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h_five
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h_seven
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h_eleven
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h_thirteen
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h_seventeen
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h_nineteen
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h_twentynine
  replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this h_thirtyseven
  exact this

/-- Leech's divisibility for a perfect cuboid, with its diagonals `d, e, f, g`. -/
theorem _root_.PerfectCuboid.IsPerfectCuboid.leech_dvd {a b c : ℕ} (h : IsPerfectCuboid a b c) :
    ∃ d e f g : ℕ, a ^ 2 + b ^ 2 = d ^ 2 ∧ a ^ 2 + c ^ 2 = e ^ 2 ∧ b ^ 2 + c ^ 2 = f ^ 2 ∧
      a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 ∧
      2 ^ 8 * 3 ^ 4 * 5 ^ 3 * 7 * 11 * 13 * 17 * 19 * 29 * 37 ∣ a * b * c * d * e * f * g := by
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ca
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  rw [← sq] at hd he hf hg
  have he' : a ^ 2 + c ^ 2 = e ^ 2 := by rw [← he]; ring
  exact ⟨d, e, f, g, hd, he', hf, hg, PerfectCuboid.Leech.leech_dvd hd he' hf hg⟩

end PerfectCuboid.Leech
