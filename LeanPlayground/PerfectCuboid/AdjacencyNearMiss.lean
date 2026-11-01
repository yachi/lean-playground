module

public import LeanPlayground.PerfectCuboid.NearMissTwist
public import LeanPlayground.PerfectCuboid.LeechEdge

/-!
# The two adjacency near-miss boxes (types A and B)

Both objects are face cuboids (`IsFaceCuboid x y c`: `x² + c²`, `y² + c²`, `x² + y² + c²` are
squares, `c` is the edge shared by the two square faces, `x² + y²` is the possibly non-square
face) with one extra square condition:

* **Type A** (`IsBoxA x y c`): `x² + y² + 2c² = h²`, i.e. the space diagonal `g` and the common
  edge `c` are the legs of a right triangle `(c, g, h)` (equivalently `e² + f² = h²` for the two
  integer face diagonals `e, f`).
* **Type B** (`IsBoxB u r p`): `r < u` and `u² − r² = q²`, i.e. the two edges `u, r` next to the
  common edge `p` are a leg–hypotenuse pair `(q, r, u)`.

`IsBoxA x y c` has the same conditions as `Adjacency.IsTypeA x y c`, and `IsBoxB u r p` the same as
`Adjacency.IsTypeB u r p` (this file does not import `Adjacency.lean`, so the two are stated
separately); by `Adjacency.IsTypeA.not_isSquare_face` and `IsTypeB.not_isSquare_face` (Fermat)
neither type is ever a perfect cuboid, so the results below concern genuine face cuboids.

Write `k s² = x² + y²` (resp. `u² + r²`) with `k` squarefree, the *twist* of the missing face.

## Main results

* `twist_prime_mod_four`: an odd prime dividing the squarefree part of a sum of two squares is
  `≡ 1 (mod 4)` (from `Nat.eq_sq_add_sq_iff`).
* `IsBoxA.prime_dvd_twist` (**S1**): in a type-A box an odd prime `p ∣ k` with `p ∤ c` is
  `≡ 1 (mod 8)`: `h² ≡ 2c² (mod p)` makes `2` a square mod `p`, and `p ≡ 1 (mod 4)`.
  (No primitivity is used.) If `p ∣ c` then `p ∣ g` and only `p ≡ 1 (mod 4)` is known.
* `IsBoxB.prime_dvd_twist` (**S2**): in a type-B box an odd prime `p ∣ k` with `p ∤ u` is
  `≡ 1 (mod 8)`: `q² = 2u² − (u² + r²) ≡ 2u² (mod p)`. (If `p ∣ u` then also `p ∣ r`.)
* `IsBoxA.c_even`, `IsBoxA.two_adic`, `IsBoxA.diagonals_odd`, `IsBoxA.twist_mod_eight`
  (**S3**, primitive type A): `c` is even (else `h² = g² + c² ≡ 2 (mod 8)`), hence `4 ∣ c`, exactly
  one of `x, y` is odd, the other is `≡ 0 (mod 4)`, `16` divides it or `c`; `g` and `h` are odd;
  and the twist satisfies `k ≡ 1 (mod 8)` (the exception of `IsFaceCuboid.twist_mod_eight`
  needs `c` odd).
* `IsBoxB.two_adic` (**S3**, primitive type B): `r` is even (an odd `r` with `4 ∣ u` would give
  `q² ≡ 7 (mod 8)`): either `u` is odd, `4 ∣ r`, `4 ∣ p`, `16 ∣ r` or `16 ∣ p`; or `p` is odd and
  `4 ∣ u`, `4 ∣ r`.
* `IsBoxA.three_dvd_c`, `IsBoxA.eleven_dvd_edge`, `IsBoxB.three_dvd_r` (**S4**, residue checks
  modulo `3` and `11`): `3 ∣ c` and `11 ∣ x y c` for type A; `3 ∣ r` for type B. Neither is true
  for face cuboids in general: `(153, 672, 104)` has `3 ∤ 104` and no factor `11`.
  Consequently `(153, 672, 104)` is not of type A (`not_isBoxA_153_672_104`).
* `IsBoxA.dvd_seven`, `IsBoxB.dvd_seven` (residue check modulo a prime `m`, the seven lengths
  `x, y, c, e, f, g, h` resp. `u, r, p, e, f, g, q`), instantiated at `29` and `37`
  (`IsBoxA.twentynine_dvd`, `IsBoxA.thirtyseven_dvd`, `IsBoxB.twentynine_dvd`,
  `IsBoxB.thirtyseven_dvd`); neither prime is forced for face cuboids
  (`FaceLeech.not_forced_19_29_37`).
* `IsBoxA.leech_dvd`: `2⁴·3²·5²·7·11·13·17·29·37 ∣ xycefgh`; `IsBoxB.leech_dvd`:
  `2⁴·3²·5²·7·13·17·29·37 ∣ urpefgq` (the face-cuboid table times the new primes; locally no
  other prime `p < 60` is forced, and `11` is not forced for type B).
* `isBoxA_degenerate`, `isBoxB_degenerate`, `boxB_p_zero` (near-miss protocol): the equations
  of type A hold for `(x, y, 0)` with `x² + y² = z²`; those of type B hold for `(u, 0, p)` with
  `u² + p² = □`; with `p = 0` they force `r = 0` (Fermat, `fermat_sub`). All results above hold
  for these degenerate solutions (`c = 0`, `r = 0` are divisible by everything), so they fail on
  them only through the positivity hypotheses.

## Search

No type-A or type-B box (primitive or not) has common edge `≤ 10⁷` (C search over all face
cuboids by common edge, round 15, brief 5).
-/

@[expose] public section

namespace PerfectCuboid.AdjacencyNearMiss

open PerfectCuboid PerfectCuboid.NearMissTwist

/-- **Type A**: a face cuboid `(x, y, c)` with `x² + y² + 2c²` a square (`g² + c² = h²`). -/
def IsBoxA (x y c : ℕ) : Prop :=
  IsFaceCuboid x y c ∧ ∃ h : ℕ, h ^ 2 = x ^ 2 + y ^ 2 + 2 * c ^ 2

/-- **Type B**: a face cuboid `(u, r, p)` with `r < u` and `u² − r²` a square. -/
def IsBoxB (u r p : ℕ) : Prop :=
  IsFaceCuboid u r p ∧ r < u ∧ ∃ q : ℕ, q ^ 2 = u ^ 2 - r ^ 2

/-! ### Elementary facts -/

theorem sq_mod_eight (n : ℕ) : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  have h := Nat.mod_lt n (show 8 > 0 by norm_num)
  rw [Nat.pow_mod]
  interval_cases n % 8 <;> simp

theorem not_all_even {x y c : ℕ} (hp : Nat.gcd (Nat.gcd x y) c = 1) :
    ¬ (2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ c) := by
  rintro ⟨hx, hy, hc⟩
  have := Nat.dvd_gcd (Nat.dvd_gcd hx hy) hc
  rw [hp] at this
  omega

/-- In type B, `q² + r² = u²`. -/
theorem IsBoxB.pyth {u r p : ℕ} (H : IsBoxB u r p) :
    ∃ q : ℕ, q ^ 2 + r ^ 2 = u ^ 2 := by
  obtain ⟨-, hru, q, hq⟩ := H
  have : r ^ 2 < u ^ 2 := Nat.pow_lt_pow_left hru (by norm_num)
  exact ⟨q, by omega⟩

/-- An odd prime dividing the squarefree part `k` of a sum of two squares `k s² = x² + y²`
(`s ≠ 0`) is not `≡ 3 (mod 4)`. -/
theorem twist_prime_mod_four {x y k s p : ℕ} (hk : Squarefree k) (hs : s ≠ 0)
    (hks : k * s ^ 2 = x ^ 2 + y ^ 2) (hp : p.Prime) (hpk : p ∣ k) : p % 4 ≠ 3 := by
  intro h3
  have := Fact.mk hp
  have hk0 : k ≠ 0 := hk.ne_zero
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hn0 : k * s ^ 2 ≠ 0 := mul_ne_zero hk0 hs2
  have hmem : p ∈ (k * s ^ 2).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_of_dvd_left hpk _, hn0⟩
  have hev := (Nat.eq_sq_add_sq_iff.mp ⟨x, y, hks⟩) p hmem h3
  rw [padicValNat.mul hk0 hs2, padicValNat.pow s 2] at hev
  have h1 : padicValNat p k = 1 := by
    have hle : 1 ≤ padicValNat p k := one_le_padicValNat_of_dvd hk0 hpk
    have hlt : ¬ 2 ≤ padicValNat p k := by
      intro h2
      have h' : p ^ 2 ∣ k := (padicValNat_dvd_iff_le hk0).mpr h2
      have := hk p (by simpa [sq] using h')
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
    omega
  rw [h1] at hev
  obtain ⟨m, hm⟩ := hev
  omega

/-! ### S1 and S2: primes in the twist -/

/-- **S1.** In a type-A box, an odd prime dividing the twist `k` of `x² + y²` but not the common
edge `c` is `≡ 1 (mod 8)`. -/
theorem IsBoxA.prime_dvd_twist {x y c k s p : ℕ} (H : IsBoxA x y c) (hk : Squarefree k)
    (hks : k * s ^ 2 = x ^ 2 + y ^ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p ∣ k)
    (hpc : ¬ p ∣ c) : p % 8 = 1 := by
  obtain ⟨hF, h, hh⟩ := H
  have := Fact.mk hp
  have hs : s ≠ 0 := by
    rintro rfl
    have := hF.pos_a
    have : 0 < x ^ 2 := by positivity
    rw [zero_pow two_ne_zero, mul_zero] at hks
    omega
  have h4 := twist_prime_mod_four hk hs hks hp hpk
  have h2 : IsSquare (2 : ZMod p) := by
    have hc : (c : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have hk0 : (k : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff k p).mpr hpk
    have e1 := congrArg (Nat.cast : ℕ → ZMod p) hh
    have e2 := congrArg (Nat.cast : ℕ → ZMod p) hks
    push_cast at e1 e2
    rw [hk0, zero_mul] at e2
    have e3 : (h : ZMod p) ^ 2 = 2 * (c : ZMod p) ^ 2 := by linear_combination e1 - e2
    refine ⟨h * (c : ZMod p)⁻¹, ?_⟩
    have : (h : ZMod p) * (c : ZMod p)⁻¹ * (h * (c : ZMod p)⁻¹) =
        (h : ZMod p) ^ 2 * ((c : ZMod p)⁻¹) ^ 2 := by ring
    rw [this, e3, mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow, mul_one]
  have := (ZMod.exists_sq_eq_two_iff hp2).mp h2
  omega

/-- **S2.** In a type-B box, an odd prime dividing the twist `k` of `u² + r²` but not `u` is
`≡ 1 (mod 8)`. -/
theorem IsBoxB.prime_dvd_twist {u r p' k s p : ℕ} (H : IsBoxB u r p') (hk : Squarefree k)
    (hks : k * s ^ 2 = u ^ 2 + r ^ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p ∣ k)
    (hpu : ¬ p ∣ u) : p % 8 = 1 := by
  obtain ⟨q, hq⟩ := H.pyth
  have hF := H.1
  have := Fact.mk hp
  have hs : s ≠ 0 := by
    rintro rfl
    have := hF.pos_a
    have : 0 < u ^ 2 := by positivity
    rw [zero_pow two_ne_zero, mul_zero] at hks
    omega
  have h4 := twist_prime_mod_four hk hs hks hp hpk
  have h2 : IsSquare (2 : ZMod p) := by
    have hu : (u : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have hk0 : (k : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff k p).mpr hpk
    have e1 := congrArg (Nat.cast : ℕ → ZMod p) hq
    have e2 := congrArg (Nat.cast : ℕ → ZMod p) hks
    push_cast at e1 e2
    rw [hk0, zero_mul] at e2
    have e3 : (q : ZMod p) ^ 2 = 2 * (u : ZMod p) ^ 2 := by linear_combination e1 + e2
    refine ⟨q * (u : ZMod p)⁻¹, ?_⟩
    have : (q : ZMod p) * (u : ZMod p)⁻¹ * (q * (u : ZMod p)⁻¹) =
        (q : ZMod p) ^ 2 * ((u : ZMod p)⁻¹) ^ 2 := by ring
    rw [this, e3, mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, mul_one]
  have := (ZMod.exists_sq_eq_two_iff hp2).mp h2
  omega

/-- In S2 the excluded case is symmetric: a prime dividing the twist and `u` divides `r`. -/
theorem IsBoxB.dvd_r_of_dvd_u {u r k s p : ℕ} (hks : k * s ^ 2 = u ^ 2 + r ^ 2)
    (hp : p.Prime) (hpk : p ∣ k) (hpu : p ∣ u) : p ∣ r := by
  have h1 : p ∣ u ^ 2 + r ^ 2 := hks ▸ dvd_mul_of_dvd_left hpk _
  have h2 : p ∣ u ^ 2 := dvd_pow hpu two_ne_zero
  exact hp.dvd_of_dvd_pow ((Nat.dvd_add_right h2).mp h1)

/-! ### S3: the 2-adic shape -/

/-- **S3 (type A).** In a primitive type-A box the common edge `c` is even. -/
theorem IsBoxA.c_even {x y c : ℕ} (H : IsBoxA x y c) (hp : Nat.gcd (Nat.gcd x y) c = 1) :
    c % 2 = 0 := by
  obtain ⟨hF, h, hh⟩ := H
  obtain ⟨g, hg⟩ := hF.sq_abc
  have hg' : x ^ 2 + y ^ 2 + c ^ 2 = g ^ 2 := by rw [hg, sq]
  have hgo := hF.space_diagonal_odd hp hg'
  by_contra hc
  have h1 := sq_mod_eight_of_odd hgo
  have h2 := sq_mod_eight_of_odd (show c % 2 = 1 by omega)
  have h3 := sq_mod_eight h
  omega

/-- **S3 (type A).** The 2-adic shape of a primitive type-A box: `4 ∣ c`, and exactly one of
`x, y` is odd; the other is divisible by `4`, and `16` divides it or `c`. -/
theorem IsBoxA.two_adic {x y c : ℕ} (H : IsBoxA x y c) (hp : Nat.gcd (Nat.gcd x y) c = 1) :
    4 ∣ c ∧ ((x % 2 = 1 ∧ 4 ∣ y ∧ (16 ∣ y ∨ 16 ∣ c)) ∨
      (y % 2 = 1 ∧ 4 ∣ x ∧ (16 ∣ x ∨ 16 ∣ c))) := by
  have hc := H.c_even hp
  rcases H.1.two_adic (not_all_even hp) with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, -, -⟩
  · exact ⟨h3, Or.inl ⟨h1, h2, h4⟩⟩
  · exact ⟨h3, Or.inr ⟨h1, h2, h4⟩⟩
  · omega

/-- **S3 (type A).** In a primitive type-A box the space diagonal `g` and the extra hypotenuse
`h` are odd. -/
theorem IsBoxA.diagonals_odd {x y c g h : ℕ} (H : IsBoxA x y c)
    (hp : Nat.gcd (Nat.gcd x y) c = 1) (hg : x ^ 2 + y ^ 2 + c ^ 2 = g ^ 2)
    (hh : h ^ 2 = x ^ 2 + y ^ 2 + 2 * c ^ 2) : g % 2 = 1 ∧ h % 2 = 1 := by
  have hgo := H.1.space_diagonal_odd hp hg
  refine ⟨hgo, FaceLeech.odd_of_sq_mod ?_⟩
  have h1 := sq_mod_eight_of_odd hgo
  have h2 := sq_mod_eight_of_four_dvd (H.two_adic hp).1
  omega

/-- **S3 (type A).** The twist of the missing face of a primitive type-A box is `≡ 1 (mod 8)`. -/
theorem IsBoxA.twist_mod_eight {x y c k s : ℕ} (H : IsBoxA x y c)
    (hp : Nat.gcd (Nat.gcd x y) c = 1) (hk : Squarefree k) (hks : k * s ^ 2 = x ^ 2 + y ^ 2) :
    k % 8 = 1 := by
  have hc := H.c_even hp
  rcases H.1.twist_mod_eight hp hk hks with h | ⟨h, -, -⟩
  · exact h
  · omega

/-- **S3 (type B).** The 2-adic shape of a primitive type-B box: `r` is even, and either `u` is
odd, `4 ∣ r`, `4 ∣ p`, `16 ∣ r ∨ 16 ∣ p`, or `p` is odd and `4 ∣ u`, `4 ∣ r`. -/
theorem IsBoxB.two_adic {u r p : ℕ} (H : IsBoxB u r p) (hp : Nat.gcd (Nat.gcd u r) p = 1) :
    (u % 2 = 1 ∧ 4 ∣ r ∧ 4 ∣ p ∧ (16 ∣ r ∨ 16 ∣ p)) ∨ (p % 2 = 1 ∧ 4 ∣ u ∧ 4 ∣ r) := by
  obtain ⟨q, hq⟩ := H.pyth
  rcases H.1.two_adic (not_all_even hp) with h | ⟨h1, h2, -, -⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · have := sq_mod_eight_of_odd h1
    have := sq_mod_eight_of_four_dvd h2
    have := sq_mod_eight q
    omega
  · exact Or.inr ⟨h1, h2, h3⟩

/-- **S3 (type B).** In a primitive type-B box the edge `r` is even. -/
theorem IsBoxB.r_even {u r p : ℕ} (H : IsBoxB u r p) (hp : Nat.gcd (Nat.gcd u r) p = 1) :
    r % 2 = 0 := by
  rcases H.two_adic hp with ⟨-, h, -⟩ | ⟨-, -, h⟩ <;> omega

/-! ### S4: residue checks -/

/-- `b² + t² ≡ a² (mod m)` for some `t`, i.e. `a² − b²` is a square mod `m`. -/
def IsDiffSqMod (m a b : ℕ) : Bool := (List.range m).any fun t ↦ (t * t + b * b) % m == a * a % m

theorem isDiffSqMod_of_pyth {m q r u : ℕ} (hm : 0 < m) (h : q ^ 2 + r ^ 2 = u ^ 2) :
    IsDiffSqMod m (u % m) (r % m) = true := by
  simp only [IsDiffSqMod, List.any_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨q % m, Nat.mod_lt _ hm, ?_⟩
  have := congrArg (· % m) h
  simp only [sq] at this
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] at this ⊢
  exact this

theorem mod_sq_add_sq_add_two_sq (m a b c : ℕ) :
    ((a % m) ^ 2 + (b % m) ^ 2 + 2 * (c % m) ^ 2) % m = (a ^ 2 + b ^ 2 + 2 * c ^ 2) % m := by
  simp [Nat.add_mod, Nat.pow_mod, Nat.mul_mod]

/-- Residues of a type-A box modulo `m` pass the four square tests. -/
theorem IsBoxA.residues {x y c m : ℕ} (H : IsBoxA x y c) (hm : 0 < m) {P : ℕ → ℕ → ℕ → Bool}
    (hP : allRes m (fun a b z ↦ !(IsSqMod m (a ^ 2 + z ^ 2) && IsSqMod m (b ^ 2 + z ^ 2) &&
      IsSqMod m (a ^ 2 + b ^ 2 + z ^ 2) && IsSqMod m (a ^ 2 + b ^ 2 + 2 * z ^ 2)) || P a b z) =
      true) :
    P (x % m) (y % m) (c % m) = true := by
  obtain ⟨hF, h, hh⟩ := H
  have := allRes_spec hP (Nat.mod_lt x hm) (Nat.mod_lt y hm) (Nat.mod_lt c hm)
  have h3 : IsSqMod m ((x % m) ^ 2 + (y % m) ^ 2 + (c % m) ^ 2) = true := by
    rw [← isSqMod_mod, mod_sq_add_sq_add_sq, isSqMod_mod]
    exact isSqMod_of_isSquare hm hF.sq_abc
  have h4 : IsSqMod m ((x % m) ^ 2 + (y % m) ^ 2 + 2 * (c % m) ^ 2) = true := by
    rw [← isSqMod_mod, mod_sq_add_sq_add_two_sq, isSqMod_mod]
    exact isSqMod_of_isSquare hm ⟨h, by rw [← hh, sq]⟩
  simpa [isSqMod_res hm hF.sq_ac, isSqMod_res hm hF.sq_bc, h3, h4] using this

/-- Residues of a type-B box modulo `m` pass the four square tests. -/
theorem IsBoxB.residues {u r p m : ℕ} (H : IsBoxB u r p) (hm : 0 < m) {P : ℕ → ℕ → ℕ → Bool}
    (hP : allRes m (fun a b z ↦ !(IsSqMod m (a ^ 2 + z ^ 2) && IsSqMod m (b ^ 2 + z ^ 2) &&
      IsSqMod m (a ^ 2 + b ^ 2 + z ^ 2) && IsDiffSqMod m a b) || P a b z) = true) :
    P (u % m) (r % m) (p % m) = true := by
  obtain ⟨q, hq⟩ := H.pyth
  have hF := H.1
  have := allRes_spec hP (Nat.mod_lt u hm) (Nat.mod_lt r hm) (Nat.mod_lt p hm)
  have h3 : IsSqMod m ((u % m) ^ 2 + (r % m) ^ 2 + (p % m) ^ 2) = true := by
    rw [← isSqMod_mod, mod_sq_add_sq_add_sq, isSqMod_mod]
    exact isSqMod_of_isSquare hm hF.sq_abc
  simpa [isSqMod_res hm hF.sq_ac, isSqMod_res hm hF.sq_bc, h3, isDiffSqMod_of_pyth hm hq]
    using this

/-- **S4.** The common edge of a type-A box is divisible by `3`. (For face cuboids in general
this fails: `(153, 672, 104)`.) -/
theorem IsBoxA.three_dvd_c {x y c : ℕ} (H : IsBoxA x y c) : 3 ∣ c := by
  have := H.residues (m := 3) (by norm_num) (P := fun _ _ z ↦ z == 0) (by decide +kernel)
  simp only [beq_iff_eq] at this
  omega

/-- **S4.** `11` divides an edge of every type-A box. (For face cuboids `11` is not forced:
`(153, 672, 104)`, `FaceLeech.not_eleven_dvd_153_672_104`.) -/
theorem IsBoxA.eleven_dvd_edge {x y c : ℕ} (H : IsBoxA x y c) : 11 ∣ x ∨ 11 ∣ y ∨ 11 ∣ c := by
  have := H.residues (m := 11) (by norm_num) (P := fun a b z ↦ a == 0 || b == 0 || z == 0)
    (by decide +kernel)
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  omega

/-- **S4.** The shorter edge `r` of a type-B box is divisible by `3`. -/
theorem IsBoxB.three_dvd_r {u r p : ℕ} (H : IsBoxB u r p) : 3 ∣ r := by
  have := H.residues (m := 3) (by norm_num) (P := fun _ b _ ↦ b == 0) (by decide +kernel)
  simp only [beq_iff_eq] at this
  omega

/-- **S4 (generic).** If the residue check modulo a prime `m` passes, `m` divides the product of
the seven lengths `x, y, c, e, f, g, h` of a type-A box. -/
theorem IsBoxA.dvd_seven {x y c e f g h m : ℕ} (H : IsBoxA x y c) (hm : m.Prime)
    (he : x ^ 2 + c ^ 2 = e ^ 2) (hf : y ^ 2 + c ^ 2 = f ^ 2) (hg : x ^ 2 + y ^ 2 + c ^ 2 = g ^ 2)
    (hh : h ^ 2 = x ^ 2 + y ^ 2 + 2 * c ^ 2)
    (hP : allRes m (fun a b z ↦ !(IsSqMod m (a ^ 2 + z ^ 2) && IsSqMod m (b ^ 2 + z ^ 2) &&
      IsSqMod m (a ^ 2 + b ^ 2 + z ^ 2) && IsSqMod m (a ^ 2 + b ^ 2 + 2 * z ^ 2)) ||
      a * b * z * (a ^ 2 + z ^ 2) * (b ^ 2 + z ^ 2) * (a ^ 2 + b ^ 2 + z ^ 2) *
        (a ^ 2 + b ^ 2 + 2 * z ^ 2) % m == 0) = true) :
    m ∣ x * y * c * e * f * g * h := by
  have h0 := H.residues hm.pos hP
  simp only [beq_iff_eq] at h0
  have hx := Nat.mod_modEq x m
  have hy := Nat.mod_modEq y m
  have hc := Nat.mod_modEq c m
  have key : x % m * (y % m) * (c % m) * ((x % m) ^ 2 + (c % m) ^ 2) *
      ((y % m) ^ 2 + (c % m) ^ 2) * ((x % m) ^ 2 + (y % m) ^ 2 + (c % m) ^ 2) *
      ((x % m) ^ 2 + (y % m) ^ 2 + 2 * (c % m) ^ 2) ≡
      x * y * c * (x ^ 2 + c ^ 2) * (y ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + c ^ 2) *
      (x ^ 2 + y ^ 2 + 2 * c ^ 2) [MOD m] := by gcongr
  rw [he, hf, hg, ← hh] at key
  have hd : m ∣ x * y * c * e ^ 2 * f ^ 2 * g ^ 2 * h ^ 2 :=
    (Nat.modEq_zero_iff_dvd).mp (key.symm.trans h0)
  have hd2 : m ∣ (x * y * c * e * f * g * h) ^ 2 := hd.trans ⟨x * y * c, by ring⟩
  exact hm.dvd_of_dvd_pow hd2

/-- **S4 (generic).** If the residue check modulo a prime `m` passes, `m` divides the product of
the seven lengths `u, r, p, e, f, g, q` of a type-B box. -/
theorem IsBoxB.dvd_seven {u r p e f g q m : ℕ} (H : IsBoxB u r p) (hm : m.Prime)
    (he : u ^ 2 + p ^ 2 = e ^ 2) (hf : r ^ 2 + p ^ 2 = f ^ 2) (hg : u ^ 2 + r ^ 2 + p ^ 2 = g ^ 2)
    (hq : q ^ 2 + r ^ 2 = u ^ 2)
    (hP : allRes m (fun a b z ↦ !(IsSqMod m (a ^ 2 + z ^ 2) && IsSqMod m (b ^ 2 + z ^ 2) &&
      IsSqMod m (a ^ 2 + b ^ 2 + z ^ 2) && IsDiffSqMod m a b) ||
      (a * b * z * (a ^ 2 + z ^ 2) * (b ^ 2 + z ^ 2) * (a ^ 2 + b ^ 2 + z ^ 2) % m == 0 ||
        a * a % m == b * b % m)) = true) :
    m ∣ u * r * p * e * f * g * q := by
  have h0 := H.residues hm.pos hP
  simp only [Bool.or_eq_true, beq_iff_eq] at h0
  have hx := Nat.mod_modEq u m
  have hy := Nat.mod_modEq r m
  have hc := Nat.mod_modEq p m
  rcases h0 with h0 | h0
  · have key : u % m * (r % m) * (p % m) * ((u % m) ^ 2 + (p % m) ^ 2) *
        ((r % m) ^ 2 + (p % m) ^ 2) * ((u % m) ^ 2 + (r % m) ^ 2 + (p % m) ^ 2) ≡
        u * r * p * (u ^ 2 + p ^ 2) * (r ^ 2 + p ^ 2) * (u ^ 2 + r ^ 2 + p ^ 2) [MOD m] := by
      gcongr
    rw [he, hf, hg] at key
    have hd : m ∣ u * r * p * e ^ 2 * f ^ 2 * g ^ 2 :=
      (Nat.modEq_zero_iff_dvd).mp (key.symm.trans h0)
    have hd2 : m ∣ (u * r * p * e * f * g * q) ^ 2 := hd.trans ⟨u * r * p * q ^ 2, by ring⟩
    exact hm.dvd_of_dvd_pow hd2
  · have h1 : u * u ≡ r * r [MOD m] := by
      have a1 : u % m * (u % m) ≡ u * u [MOD m] := by gcongr
      have a2 : r % m * (r % m) ≡ r * r [MOD m] := by gcongr
      exact a1.symm.trans ((show _ ≡ _ [MOD m] from h0).trans a2)
    have h2 : q ^ 2 + r ^ 2 ≡ 0 + r ^ 2 [MOD m] := by
      rw [hq, zero_add, sq, sq]; exact h1
    have h3 : m ∣ q ^ 2 := (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_right_cancel' _ h2)
    exact (hm.dvd_of_dvd_pow h3).trans (Dvd.intro_left _ rfl)

/-- **S4.** `29` divides the product of the seven lengths of a type-A box. (For face cuboids `29`
is not forced: `FaceLeech.not_forced_19_29_37`.) -/
theorem IsBoxA.twentynine_dvd {x y c e f g h : ℕ} (H : IsBoxA x y c)
    (he : x ^ 2 + c ^ 2 = e ^ 2) (hf : y ^ 2 + c ^ 2 = f ^ 2) (hg : x ^ 2 + y ^ 2 + c ^ 2 = g ^ 2)
    (hh : h ^ 2 = x ^ 2 + y ^ 2 + 2 * c ^ 2) : 29 ∣ x * y * c * e * f * g * h :=
  H.dvd_seven (by norm_num) he hf hg hh (by decide +kernel)

/-- **S4.** `37` divides the product of the seven lengths of a type-A box. -/
theorem IsBoxA.thirtyseven_dvd {x y c e f g h : ℕ} (H : IsBoxA x y c)
    (he : x ^ 2 + c ^ 2 = e ^ 2) (hf : y ^ 2 + c ^ 2 = f ^ 2) (hg : x ^ 2 + y ^ 2 + c ^ 2 = g ^ 2)
    (hh : h ^ 2 = x ^ 2 + y ^ 2 + 2 * c ^ 2) : 37 ∣ x * y * c * e * f * g * h :=
  H.dvd_seven (by norm_num) he hf hg hh (by decide +kernel)

/-- **S4.** `29` divides the product of the seven lengths of a type-B box. -/
theorem IsBoxB.twentynine_dvd {u r p e f g q : ℕ} (H : IsBoxB u r p)
    (he : u ^ 2 + p ^ 2 = e ^ 2) (hf : r ^ 2 + p ^ 2 = f ^ 2) (hg : u ^ 2 + r ^ 2 + p ^ 2 = g ^ 2)
    (hq : q ^ 2 + r ^ 2 = u ^ 2) : 29 ∣ u * r * p * e * f * g * q :=
  H.dvd_seven (by norm_num) he hf hg hq (by decide +kernel)

/-- **S4.** `37` divides the product of the seven lengths of a type-B box. -/
theorem IsBoxB.thirtyseven_dvd {u r p e f g q : ℕ} (H : IsBoxB u r p)
    (he : u ^ 2 + p ^ 2 = e ^ 2) (hf : r ^ 2 + p ^ 2 = f ^ 2) (hg : u ^ 2 + r ^ 2 + p ^ 2 = g ^ 2)
    (hq : q ^ 2 + r ^ 2 = u ^ 2) : 37 ∣ u * r * p * e * f * g * q :=
  H.dvd_seven (by norm_num) he hf hg hq (by decide +kernel)

/-- **S4 (Leech table for type A).** `2⁴·3²·5²·7·11·13·17·29·37` divides the product of the seven
lengths of a type-A box: the face-cuboid table `2⁴·3²·5²·7·13·17` (`FaceLeech.face_leech_dvd`)
together with `11 ∣ xyc`, `29 ∣ xycefgh`, `37 ∣ xycefgh`. -/
theorem IsBoxA.leech_dvd {x y c e f g h : ℕ} (H : IsBoxA x y c)
    (he : x ^ 2 + c ^ 2 = e ^ 2) (hf : y ^ 2 + c ^ 2 = f ^ 2) (hg : x ^ 2 + y ^ 2 + c ^ 2 = g ^ 2)
    (hh : h ^ 2 = x ^ 2 + y ^ 2 + 2 * c ^ 2) :
    2 ^ 4 * 3 ^ 2 * 5 ^ 2 * 7 * 13 * 17 * 11 * 29 * 37 ∣ x * y * c * e * f * g * h := by
  have h1 : 2 ^ 4 * 3 ^ 2 * 5 ^ 2 * 7 * 13 * 17 ∣ x * y * c * e * f * g * h :=
    (FaceLeech.face_leech_dvd he hf hg).trans (Dvd.intro _ rfl)
  have h11 : 11 ∣ x * y * c * e * f * g * h := by
    have : 11 ∣ x * y * c := by
      rcases H.eleven_dvd_edge with h | h | h
      · exact (h.mul_right _).mul_right _
      · exact (h.mul_left _).mul_right _
      · exact h.mul_left _
    exact this.trans ⟨e * f * g * h, by ring⟩
  have h29 := H.twentynine_dvd he hf hg hh
  have h37 := H.thirtyseven_dvd he hf hg hh
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h11) h29) h37

/-- **S4 (Leech table for type B).** `2⁴·3²·5²·7·13·17·29·37` divides the product of the seven
lengths of a type-B box. -/
theorem IsBoxB.leech_dvd {u r p e f g q : ℕ} (H : IsBoxB u r p)
    (he : u ^ 2 + p ^ 2 = e ^ 2) (hf : r ^ 2 + p ^ 2 = f ^ 2) (hg : u ^ 2 + r ^ 2 + p ^ 2 = g ^ 2)
    (hq : q ^ 2 + r ^ 2 = u ^ 2) :
    2 ^ 4 * 3 ^ 2 * 5 ^ 2 * 7 * 13 * 17 * 29 * 37 ∣ u * r * p * e * f * g * q := by
  have h1 : 2 ^ 4 * 3 ^ 2 * 5 ^ 2 * 7 * 13 * 17 ∣ u * r * p * e * f * g * q :=
    (FaceLeech.face_leech_dvd he hf hg).trans (Dvd.intro _ rfl)
  have h29 := H.twentynine_dvd he hf hg hq
  have h37 := H.thirtyseven_dvd he hf hg hq
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h29) h37

/-- The face cuboid `(153, 672, 104)` is not of type A, since `3 ∤ 104`. -/
theorem not_isBoxA_153_672_104 : ¬ IsBoxA 153 672 104 := fun H ↦ by
  have := H.three_dvd_c
  omega

/-- The face cuboid `(672, 153, 104)` is not of type B: `672² − 153² = 428175` lies strictly
between `654²` and `655²`. -/
theorem not_isBoxB_672_153_104 : ¬ IsBoxB 672 153 104 := by
  rintro ⟨-, -, q, hq⟩
  exact Nat.not_exists_sq' (m := 654) (n := 672 ^ 2 - 153 ^ 2) (by norm_num) (by norm_num)
    ⟨q, by rw [hq]⟩

/-! ### Degenerate solutions (near-miss protocol) -/

/-- The equations of type A hold for `(x, y, 0)` with `x² + y² = z²`. -/
theorem isBoxA_degenerate {x y z : ℕ} (h : x ^ 2 + y ^ 2 = z ^ 2) :
    IsSquare (x ^ 2 + 0 ^ 2) ∧ IsSquare (y ^ 2 + 0 ^ 2) ∧ IsSquare (x ^ 2 + y ^ 2 + 0 ^ 2) ∧
      ∃ h : ℕ, h ^ 2 = x ^ 2 + y ^ 2 + 2 * 0 ^ 2 :=
  ⟨⟨x, by ring⟩, ⟨y, by ring⟩, ⟨z, by rw [← sq]; simp [h]⟩, ⟨z, by simp [h]⟩⟩

/-- The equations of type B hold for `(u, 0, p)` with `u² + p² = w²`. -/
theorem isBoxB_degenerate {u p w : ℕ} (h : u ^ 2 + p ^ 2 = w ^ 2) :
    IsSquare (u ^ 2 + p ^ 2) ∧ IsSquare (0 ^ 2 + p ^ 2) ∧ IsSquare (u ^ 2 + 0 ^ 2 + p ^ 2) ∧
      ∃ q : ℕ, q ^ 2 = u ^ 2 - 0 ^ 2 :=
  ⟨⟨w, by rw [← sq, h]⟩, ⟨p, by ring⟩, ⟨w, by rw [← sq]; simp [h]⟩, ⟨u, by simp⟩⟩

/-- With `p = 0` the equations of type B force `r = 0` (Fermat: `u⁴ − r⁴ = □`). -/
theorem boxB_p_zero {u r w q : ℕ} (hru : r < u) (hw : u ^ 2 + r ^ 2 = w ^ 2)
    (hq : q ^ 2 + r ^ 2 = u ^ 2) : r = 0 := by
  have hF : (u : ℤ) ^ 4 - (r : ℤ) ^ 4 = ((w : ℤ) * q) ^ 2 := by
    have e1 : (u : ℤ) ^ 2 + r ^ 2 = w ^ 2 := by exact_mod_cast hw
    have e2 : (q : ℤ) ^ 2 + r ^ 2 = u ^ 2 := by exact_mod_cast hq
    have : ((w : ℤ) * q) ^ 2 = (u ^ 2 + r ^ 2) * (u ^ 2 - r ^ 2) := by
      rw [mul_pow, ← e1]; congr 1; linarith
    rw [this]; ring
  rcases fermat_sub hF with h | h | h
  · omega
  · exact_mod_cast h
  · rcases mul_eq_zero.mp h with h | h
    · have : w = 0 := by exact_mod_cast h
      subst this
      have : u ^ 2 = 0 := by omega
      have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp this
      omega
    · have : q = 0 := by exact_mod_cast h
      subst this
      have : r ^ 2 < u ^ 2 := Nat.pow_lt_pow_left hru (by norm_num)
      omega

end PerfectCuboid.AdjacencyNearMiss

