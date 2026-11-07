module

public import LeanPlayground.PerfectCuboid.ThirdConjectureModP

/-!
# Certificates for the third cuboid polynomial modulo many primes

Infrastructure for `LeanPlayground.PerfectCuboid.ThirdConjectureMulti`, which extends the
two-prime criterion of `LeanPlayground.PerfectCuboid.ThirdConjectureModP` to many primes.

**Precomputed certificates** (`irreducible_of_certB`). As in `irredB`, a monic `h` of degree `n`
over `ZMod p` is irreducible if `gcd (h, X ^ (p ^ k) − X) = 1` for `1 ≤ k ≤ n / 2`. Here the rows
`mᵢ = X ^ (p i) mod h` of the Berlekamp matrix come with their quotients, and each coprimality
with Bézout coefficients `s h + t (X ^ (p ^ k) − X) = 1`, all computed outside Lean. The kernel
only multiplies and compares, which is several times faster than running Euclid's algorithm.

**Scaling** (`cuboidThreePoly_comp_C_mul_X`, `cuboidThreePoly_swap`). The polynomial is
homogeneous, `P_{ta,tb,tc}(t X) = t¹² P_{a,b,c}(X)`, and symmetric in `a, b`. So the degrees of
the divisors of the reduction modulo `p` depend only on the class of `(a², b², c²)` up to
multiplication by a nonzero square and swapping `a, b`.

**Table entries** (`entryOK`, `natDegree_mem_of_matchT`). An entry stores a representative
`(r₁, r₂, r₃)` of such a class and the certified factorization of `cuboidThreePoly r₁ r₂ r₃`
modulo `p`. If `(a², b², c²) ≡ t² (r₁², r₂², r₃²)` (possibly after swapping `a, b`) with
`t ≢ 0`, every divisor of the reduction of `cuboidThreePoly a b c` has as degree a subset sum of
the degrees of the factors.
-/

@[expose] public section

namespace PerfectCuboid.ThirdConjecture.ModP

open Polynomial

/-! ### Certified irreducibility from precomputed data -/

theorem dvd_sub_of_eqb {p : ℕ} {a b h q r : List ℕ}
    (e : eqb p (mulL p a b) (addL p (mulL p h q) r) = true) :
    toPoly p h ∣ toPoly p a * toPoly p b - toPoly p r := by
  have := toPoly_eq_of_eqb p _ _ e
  rw [toPoly_mulL, toPoly_addL, toPoly_mulL] at this
  exact ⟨toPoly p q, by rw [this]; ring⟩

/-- Rows `m₂, m₃, …` of the Berlekamp matrix with their quotients
`m · m₁ = h q + m'`, read from the certificate. Ends with `k ms rest`. -/
def rowsK (p : ℕ) (h m₁ : List ℕ) (k : List (List ℕ) → List (List ℕ) → Bool) :
    ℕ → List ℕ → List (List ℕ) → List (List ℕ) → Bool
  | 0, _, acc, rest => k acc rest
  | n + 1, m, acc, m' :: q :: rest =>
    eqb p (mulL p m m₁) (addL p (mulL p h q) m') && rowsK p h m₁ k n m' (acc ++ [m']) rest
  | _ + 1, _, _, _ => false

theorem exists_of_rowsK {p : ℕ} {h m₁ : List ℕ} {k : List (List ℕ) → List (List ℕ) → Bool}
    (h₁ : toPoly p h ∣ X ^ p - toPoly p m₁) :
    ∀ n m acc rest, rowsK p h m₁ k n m acc rest = true → QM p (toPoly p h) 0 acc →
      0 < acc.length → toPoly p h ∣ X ^ (p * (acc.length - 1)) - toPoly p m →
      ∃ ms rest', QM p (toPoly p h) 0 ms ∧ acc.length ≤ ms.length ∧ k ms rest' = true
  | 0, _, acc, rest, hk, hq, _, _ => ⟨acc, rest, hq, le_rfl, hk⟩
  | n + 1, m, acc, m' :: q :: rest, hk, hq, hl, hm => by
    rw [rowsK, Bool.and_eq_true] at hk
    have hm' := dvd_sub_of_eqb hk.1
    have hm'' : toPoly p h ∣ X ^ (p * acc.length) - toPoly p m' := by
      have e : X ^ (p * acc.length) - toPoly p m' =
          X ^ (p * (acc.length - 1)) * (X ^ p - toPoly p m₁)
          + toPoly p m₁ * (X ^ (p * (acc.length - 1)) - toPoly p m)
          + (toPoly p m * toPoly p m₁ - toPoly p m') := by
        rw [show p * acc.length = p * (acc.length - 1) + p by
          rw [← Nat.mul_succ]; congr 1; omega, pow_add]
        ring
      rw [e]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_right h₁ _) (dvd_mul_of_dvd_right hm _)) hm'
    obtain ⟨ms, rest', hms, hlen, hk⟩ := exists_of_rowsK h₁ n m' (acc ++ [m']) rest hk.2
      ((QM_append m' acc 0).2 ⟨hq, by simpa using hm''⟩) (by simp) (by simpa using hm'')
    exact ⟨ms, rest', hms, by simp at hlen; omega, hk⟩
  | _ + 1, _, _, [], hk, _, _, _ => by simp [rowsK] at hk
  | _ + 1, _, _, [_], hk, _, _, _ => by simp [rowsK] at hk

/-- Steps `k + 1, …, k + n` of the Frobenius chain (as in `frobLoop`), with coprimality checked
by Bézout coefficients `s h + t (r' − X) = 1` read from the certificate. -/
def bezLoop (p : ℕ) (h : List ℕ) (ms : List (List ℕ)) : ℕ → List ℕ → List (List ℕ) → Bool
  | 0, _, _ => true
  | n + 1, r, s :: t :: rest => decide (r.length ≤ ms.length) && forceL (combL p r ms) fun r' ↦
      eqb p (addL p (mulL p s h) (mulL p t (subL p r' [0, 1]))) [1] && bezLoop p h ms n r' rest
  | _ + 1, _, _ => false

theorem isCoprime_of_bezLoop {p : ℕ} [Fact p.Prime] {h : List ℕ} {ms : List (List ℕ)}
    (hQ : QM p (toPoly p h) 0 ms) :
    ∀ n k r rest, bezLoop p h ms n r rest = true → toPoly p h ∣ X ^ p ^ k - toPoly p r →
      ∀ j, 0 < j → j ≤ n → IsCoprime (toPoly p h) (X ^ p ^ (k + j) - X)
  | 0, _, _, _, _, _, j, hj, hjn => absurd hjn (by omega)
  | n + 1, k, r, s :: t :: rest, hl, hr, j, hj, hjn => by
    have hp : 0 < p := (Fact.out : p.Prime).pos
    rw [bezLoop, forceL_eq] at hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
    obtain ⟨hlen, hc, hl⟩ := hl
    set r' := combL p r ms
    have hr' : toPoly p h ∣ X ^ p ^ (k + 1) - toPoly p r' := by
      have h1 := hr.trans (sub_dvd_pow_sub_pow (X ^ p ^ k) (toPoly p r) p)
      rw [← pow_mul, ← pow_succ, ← ZMod.expand_card] at h1
      have h2 := dvd_combL r ms 0 hlen hQ
      rw [mul_zero, pow_zero, one_mul] at h2
      simpa using dvd_add h1 h2
    rcases Nat.lt_or_ge 1 j with hj1 | hj1
    · have := isCoprime_of_bezLoop hQ n (k + 1) r' rest hl hr' (j - 1) (by omega) (by omega)
      rwa [show k + 1 + (j - 1) = k + j by omega] at this
    · obtain rfl : j = 1 := by omega
      have hc' := toPoly_eq_of_eqb p _ _ hc
      rw [toPoly_addL, toPoly_mulL, toPoly_mulL, toPoly_subL hp] at hc'
      have hc : IsCoprime (toPoly p h) (toPoly p r' - toPoly p [0, 1]) :=
        ⟨toPoly p s, toPoly p t, by rw [hc']; simp⟩
      obtain ⟨m, hm⟩ := hr'
      have : X ^ p ^ (k + 1) - X = (toPoly p r' - toPoly p [0, 1]) + toPoly p h * m := by
        rw [← hm]; simp
      rw [this]
      exact hc.add_mul_left_right m
  | _ + 1, _, _, [], hl, _, _, _, _ => by simp [bezLoop] at hl
  | _ + 1, _, _, [_], hl, _, _, _, _ => by simp [bezLoop] at hl

/-- A certificate `h :: rest` for the irreducibility of the monic `h`: nothing for degree `1`;
otherwise `rest = m₁ :: q₀ :: m₂ :: q₂ :: … :: s₁ :: t₁ :: …` with `X ^ p = h q₀ + m₁`,
`mᵢ₋₁ m₁ = h qᵢ + mᵢ` (rows of the Berlekamp matrix), and Bézout coefficients for
`gcd (h, X ^ (p ^ k) − X) = 1`, `1 ≤ k ≤ deg h / 2`. -/
def certB (p : ℕ) : List (List ℕ) → Bool
  | [h] => lastIsOne h && h.length == 2
  | h :: m₁ :: q₀ :: rest => lastIsOne h && decide (3 ≤ h.length) &&
      eqb p (mulL p h q₀) (subL p (xpowL p) m₁) &&
      rowsK p h m₁ (fun ms rest' ↦ bezLoop p h ms ((h.length - 1) / 2) [0, 1] rest')
        (h.length - 3) m₁ [[1], m₁] rest
  | _ => false

theorem irreducible_of_certB {p : ℕ} [Fact p.Prime] {l : List (List ℕ)} (hb : certB p l = true) :
    Irreducible (toPoly p (l.headD [])) ∧ lastIsOne (l.headD []) = true := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  match l, hb with
  | [h], hb =>
    change Irreducible (toPoly p h) ∧ lastIsOne h = true
    simp only [certB, Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨hm, hd⟩ := monic_toPoly (p := p) h hb.1
    refine ⟨Polynomial.irreducible_of_degree_eq_one ?_, hb.1⟩
    rw [degree_eq_natDegree hm.ne_zero, hd, hb.2]; rfl
  | h :: m₁ :: q₀ :: rest, hb =>
    change Irreducible (toPoly p h) ∧ lastIsOne h = true
    simp only [certB, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨hl, hlen⟩, hx⟩, hf⟩ := hb
    have h₁ : toPoly p h ∣ X ^ p - toPoly p m₁ := by
      have := toPoly_eq_of_eqb p _ _ hx
      rw [toPoly_mulL, toPoly_subL hp, toPoly_xpowL] at this
      exact ⟨toPoly p q₀, this.symm⟩
    obtain ⟨ms, rest', hQ, hmsl, hf⟩ := exists_of_rowsK h₁ _ _ _ _ hf
      ⟨by simp, by simpa using h₁, trivial⟩ (by simp) (by simpa using h₁)
    obtain ⟨hm, hd⟩ := monic_toPoly (p := p) h hl
    refine ⟨irreducible_of_isCoprime hm (fun h1 ↦ ?_) fun k hk hkn ↦ ?_, hl⟩
    · rw [h1, natDegree_one] at hd; omega
    · have := isCoprime_of_bezLoop hQ _ 0 _ _ hf (by simp) k hk (by rw [← hd]; exact hkn)
      simpa using this

/-! ### Homogeneity and symmetry of the cuboid polynomial -/

theorem cuboidThreePoly_comp_C_mul_X (t a b c : ℤ) :
    (cuboidThreePoly (t * a) (t * b) (t * c)).comp (C t * X) =
      C (t ^ 12) * cuboidThreePoly a b c := by
  simp only [cuboidThreePoly, add_comp, mul_comp, C_comp, X_pow_comp, mul_pow,
    ← C_pow]
  simp only [C_pow, C_mul, C_add, C_sub, C_ofNat]
  ring

theorem cuboidThreePoly_swap (a b c : ℤ) : cuboidThreePoly b a c = cuboidThreePoly a b c := by
  simp only [cuboidThreePoly]
  ring_nf

/-! ### Table entries -/

/-- A table entry: a key (the normal form of the class), a representative `(r₁, r₂, r₃)`, and
certificates `h :: rest` for the factors `h` of the polynomial modulo `p` at `(r₁, r₂, r₃)`. -/
abbrev Entry := (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × List (List (List ℕ))

/-- The factors of an entry. -/
def Entry.facs (e : Entry) : List (List ℕ) := e.2.2.map (·.headD [])

/-- An entry is correct: the product of its factors is the polynomial modulo `p` at its
representative, and each factor is certified irreducible. -/
def entryOK (p : ℕ) (e : Entry) : Bool :=
  eqb p (cuboidCoeffs p (e.2.1.1 * e.2.1.1 % p) (e.2.1.2.1 * e.2.1.2.1 % p)
      (e.2.1.2.2 * e.2.1.2.2 % p)) (prodL p e.facs) && e.2.2.all (certB p)

theorem natDegree_mem_of_entryOK {p : ℕ} [Fact p.Prime] {e : Entry} (he : entryOK p e = true)
    (u : (ZMod p)[X])
    (hu : u ∣ (cuboidThreePoly e.2.1.1 e.2.1.2.1 e.2.1.2.2).map (Int.castRingHom (ZMod p))) :
    u.natDegree ∈ sums (degs e.facs) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simp only [entryOK, Bool.and_eq_true, List.all_eq_true] at he
  have hsq : ∀ r : ℕ, ((r * r % p : ℕ) : ZMod p) = ((r : ℤ) : ZMod p) ^ 2 := fun r ↦ by
    rw [ZMod.natCast_mod]; push_cast; ring
  rw [map_cuboidThreePoly hp (hsq _) (hsq _) (hsq _), toPoly_eq_of_eqb _ _ _ he.1,
    toPoly_prodL] at hu
  have hc : ∀ f ∈ e.2.2, Irreducible (toPoly p (f.headD [])) ∧ lastIsOne (f.headD []) = true :=
    fun f hf ↦ irreducible_of_certB (he.2 f hf)
  have hd : (e.facs.map (toPoly p)).map natDegree = degs e.facs := by
    rw [degs, List.map_map]
    refine List.map_congr_left fun f hf ↦ ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact (monic_toPoly (p := p) _ (hc g hg).2).2
  rw [← hd]
  refine natDegree_mem_sums _ ?_ u hu
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hf
  exact (hc f' hf').1

/-- The class of `(a, b, c)` matches the entry with scale `t`: `(a², b², c²) ≡ t² (r₁², r₂², r₃²)`,
possibly after swapping `a, b`, and `t ≢ 0 (mod p)`. -/
def matchT (p : ℕ) (a b c t : ℤ) (e : Entry) : Bool :=
  t % (p : ℤ) != 0 &&
    let k := (sqMod p (t * e.2.1.1), sqMod p (t * e.2.1.2.1), sqMod p (t * e.2.1.2.2))
    ((sqMod p a, sqMod p b, sqMod p c) == k || (sqMod p b, sqMod p a, sqMod p c) == k)

/-- Some `t ∈ {a, b, c}` scales the entry to the class of `(a, b, c)`. -/
def matchB (p : ℕ) (a b c : ℤ) (e : Entry) : Bool :=
  matchT p a b c a e || matchT p a b c b e || matchT p a b c c e

theorem map_eq_of_sqMod {p : ℕ} (hp : 0 < p) {a b c a' b' c' : ℤ}
    (h : (sqMod p a, sqMod p b, sqMod p c) = (sqMod p a', sqMod p b', sqMod p c')) :
    (cuboidThreePoly a b c).map (Int.castRingHom (ZMod p)) =
      (cuboidThreePoly a' b' c').map (Int.castRingHom (ZMod p)) := by
  simp only [Prod.mk.injEq] at h
  rw [map_cuboidThreePoly hp (cast_sqMod hp a) (cast_sqMod hp b) (cast_sqMod hp c),
    map_cuboidThreePoly hp (h.1 ▸ cast_sqMod hp a') (h.2.1 ▸ cast_sqMod hp b')
      (h.2.2 ▸ cast_sqMod hp c')]

theorem natDegree_mem_of_matchT {p : ℕ} [Fact p.Prime] {e : Entry} (he : entryOK p e = true)
    {a b c t : ℤ} (hm : matchT p a b c t e = true) (u : (ZMod p)[X])
    (hu : u ∣ (cuboidThreePoly a b c).map (Int.castRingHom (ZMod p))) :
    u.natDegree ∈ sums (degs e.facs) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simp only [matchT, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at hm
  obtain ⟨ht, hm⟩ := hm
  set r₁ : ℤ := (e.2.1.1 : ℤ)
  set r₂ : ℤ := (e.2.1.2.1 : ℤ)
  set r₃ : ℤ := (e.2.1.2.2 : ℤ)
  have hmap : (cuboidThreePoly a b c).map (Int.castRingHom (ZMod p)) =
      (cuboidThreePoly (t * r₁) (t * r₂) (t * r₃)).map (Int.castRingHom (ZMod p)) := by
    rcases hm with hm | hm
    · exact map_eq_of_sqMod hp hm
    · rw [← cuboidThreePoly_swap a b c]; exact map_eq_of_sqMod hp hm
  have ht' : (t : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun hd ↦ ht (Int.emod_eq_zero_of_dvd hd)
  rw [hmap] at hu
  obtain ⟨w, hw⟩ := hu
  have key : (u.comp (C (t : ZMod p) * X)) * w.comp (C (t : ZMod p) * X) =
      C ((t : ZMod p) ^ 12) * (cuboidThreePoly r₁ r₂ r₃).map (Int.castRingHom (ZMod p)) := by
    rw [← mul_comp, ← hw, ← Polynomial.map_X (Int.castRingHom (ZMod p)), ← eq_intCast
      (Int.castRingHom (ZMod p)) t, ← Polynomial.map_C, ← Polynomial.map_mul, ← map_comp,
      cuboidThreePoly_comp_C_mul_X, Polynomial.map_mul, Polynomial.map_C, map_pow]
  have hunit : IsUnit (C ((t : ZMod p) ^ 12)) := isUnit_C.2 (pow_ne_zero _ ht').isUnit
  have hdvd : u.comp (C (t : ZMod p) * X) ∣
      (cuboidThreePoly r₁ r₂ r₃).map (Int.castRingHom (ZMod p)) :=
    (hunit.dvd_mul_left).1 ⟨_, key.symm⟩
  have := natDegree_mem_of_entryOK he _ hdvd
  rwa [natDegree_comp, natDegree_C_mul_X _ ht', mul_one] at this

end PerfectCuboid.ThirdConjecture.ModP
