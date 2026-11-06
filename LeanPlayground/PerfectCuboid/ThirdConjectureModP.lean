module

public import Mathlib
public import LeanPlayground.PerfectCuboid.ThirdConjecture

/-!
# Irreducibility of the third cuboid polynomial from two primes

Sharipov's third cuboid conjecture (see `LeanPlayground.PerfectCuboid.ThirdConjecture`) says that
`cuboidThreePoly a b c` is irreducible in `ℤ[X]`. This file gives a kernel-checked criterion that
proves this on explicit congruence classes of `(a, b, c)`.

**Two-prime criterion** (`irreducible_of_two_primes`). A monic `g ∈ ℤ[X]` is irreducible if the
degrees of the divisors of its reductions modulo two primes `p, q` have only `0` and `deg g` in
common: a factorization `g = u v` with `u, v` monic would give divisors of degree `deg u` modulo
both primes. One prime is never enough for `cuboidThreePoly`, whose reduction is never
irreducible, so this is the shape a congruence proof has to take.

**Degrees of divisors** (`natDegree_mem_sums`). Over a field, every divisor of a product of
irreducible polynomials has as degree a subset sum of their degrees.

**Certified irreducibility over `ZMod p`** (`irreducible_of_irredB`). A monic `h` of degree `n`
is irreducible if `gcd (h, X ^ (p ^ k) − X) = 1` for `1 ≤ k ≤ n / 2`, because an irreducible `q`
divides `X ^ (p ^ deg q) − X` (`dvd_X_pow_sub_X`, from Mathlib). The test `irredB` computes
`X ^ (p ^ k) mod h` with the Berlekamp matrix `mᵢ = X ^ (p i) mod h` (using `r ^ p = r (X ^ p)`
over `ZMod p`, `ZMod.expand_card`), and checks each coprimality by a Bézout identity.

Polynomials over `ZMod p` are lists of natural numbers (`toPoly`) with computable arithmetic
(`addL`, `mulL`, …) and correctness lemmas (`toPoly_addL`, `toPoly_mulL`, …). Divisions and
Euclid's algorithm (`divModK`, `xgcdK`) are not verified: their results are checked afterwards
(`eqb`), so only the checks enter the proofs. The checks run in the kernel (`decide +kernel`);
they are written in continuation-passing style with every intermediate list evaluated to numerals
(`forceL`), since the kernel does not share the results of repeated subterms.

**The cuboid polynomial modulo `p`** (`map_cuboidThreePoly`). The reduction depends only on
`(a², b², c²) mod p` (`cuboidCoeffs`). `classOK p ((A, B, C), fs)` checks that the reduction for
the class `(A, B, C)` is the product of the factors `fs`, each irreducible. The main criterion
`irreducible_of_tables` combines two certified tables whose degree patterns are compatible
(`compatB`). It is applied to `p = 13`, `q = 17` in
`LeanPlayground.PerfectCuboid.ThirdConjecture1317`.
-/

@[expose] public section

namespace PerfectCuboid.ThirdConjecture.ModP

open Polynomial

/-! ### Polynomials over `ZMod p` as lists of natural numbers -/

/-- The polynomial `∑ lᵢ Xⁱ` over `ZMod p` (coefficients listed from the constant term up). -/
noncomputable def toPoly (p : ℕ) (l : List ℕ) : (ZMod p)[X] :=
  l.foldr (fun a q ↦ C (a : ZMod p) + X * q) 0

@[simp] theorem toPoly_nil (p : ℕ) : toPoly p [] = 0 := rfl

@[simp] theorem toPoly_cons (p a : ℕ) (l : List ℕ) :
    toPoly p (a :: l) = C (a : ZMod p) + X * toPoly p l := rfl

/-- Sum of coefficient lists. -/
def addL (p : ℕ) : List ℕ → List ℕ → List ℕ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) % p :: addL p l m

theorem toPoly_addL (p : ℕ) : ∀ l m, toPoly p (addL p l m) = toPoly p l + toPoly p m
  | [], m => by simp [addL]
  | a :: l, [] => by simp [addL]
  | a :: l, b :: m => by
    simp only [addL, toPoly_cons, toPoly_addL p l m, ZMod.natCast_mod, Nat.cast_add, C_add]
    ring

/-- Scalar multiple `c • l`. -/
def smulL (p c : ℕ) (l : List ℕ) : List ℕ := l.map fun a ↦ c * a % p

theorem toPoly_smulL (p c : ℕ) : ∀ l, toPoly p (smulL p c l) = C (c : ZMod p) * toPoly p l
  | [] => by simp [smulL]
  | a :: l => by
    have := toPoly_smulL p c l
    simp only [smulL, List.map_cons, toPoly_cons, ZMod.natCast_mod, Nat.cast_mul, C_mul] at this ⊢
    rw [this]; ring

/-- Product of coefficient lists. -/
def mulL (p : ℕ) (l m : List ℕ) : List ℕ :=
  l.foldr (fun a acc ↦ addL p (smulL p a m) (0 :: acc)) []

theorem toPoly_mulL (p : ℕ) (m : List ℕ) : ∀ l, toPoly p (mulL p l m) = toPoly p l * toPoly p m
  | [] => by simp [mulL]
  | a :: l => by
    have := toPoly_mulL p m l
    simp only [mulL, List.foldr_cons] at this ⊢
    rw [toPoly_addL, toPoly_smulL, toPoly_cons, this, toPoly_cons]
    simp only [Nat.cast_zero, C_0]
    ring

/-- `l ^ n`. -/
def powL (p : ℕ) (l : List ℕ) : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => mulL p (powL p l n) l

theorem toPoly_powL (p : ℕ) (l : List ℕ) : ∀ n, toPoly p (powL p l n) = toPoly p l ^ n
  | 0 => by simp [powL]
  | n + 1 => by rw [powL, toPoly_mulL, toPoly_powL p l n, pow_succ]

/-- Negation. -/
def negL (p : ℕ) (l : List ℕ) : List ℕ := l.map fun a ↦ (p - a % p) % p

theorem toPoly_negL {p : ℕ} (hp : 0 < p) : ∀ l, toPoly p (negL p l) = -toPoly p l
  | [] => by simp [negL]
  | a :: l => by
    have := toPoly_negL hp l
    simp only [negL, List.map_cons, toPoly_cons] at this ⊢
    rw [this]
    have : (((p - a % p) % p : ℕ) : ZMod p) = -(a : ZMod p) := by
      rw [ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt a hp).le, ZMod.natCast_self,
        ZMod.natCast_mod, zero_sub]
    rw [this, C_neg]; ring

/-- Difference. -/
def subL (p : ℕ) (l m : List ℕ) : List ℕ := addL p l (negL p m)

theorem toPoly_subL {p : ℕ} (hp : 0 < p) (l m : List ℕ) :
    toPoly p (subL p l m) = toPoly p l - toPoly p m := by
  rw [subL, toPoly_addL, toPoly_negL hp, sub_eq_add_neg]

/-- All coefficients vanish modulo `p`. -/
def zeroB (p : ℕ) : List ℕ → Bool
  | [] => true
  | a :: l => a % p == 0 && zeroB p l

theorem toPoly_eq_zero_of_zeroB (p : ℕ) : ∀ l, zeroB p l = true → toPoly p l = 0
  | [] => fun _ ↦ rfl
  | a :: l => by
    intro h
    simp only [zeroB, Bool.and_eq_true, beq_iff_eq] at h
    have h2 : (a : ZMod p) = 0 := by rw [← ZMod.natCast_mod, h.1, Nat.cast_zero]
    simp [toPoly_eq_zero_of_zeroB p l h.2, h2]

/-- Equality of coefficient lists modulo `p` (missing coefficients are zero). -/
def eqb (p : ℕ) : List ℕ → List ℕ → Bool
  | [], m => zeroB p m
  | a :: l, [] => zeroB p (a :: l)
  | a :: l, b :: m => a % p == b % p && eqb p l m

theorem toPoly_eq_of_eqb (p : ℕ) : ∀ l m, eqb p l m = true → toPoly p l = toPoly p m
  | [], m => fun h ↦ (toPoly_eq_zero_of_zeroB p m h).symm
  | a :: l, [] => fun h ↦ toPoly_eq_zero_of_zeroB p _ h
  | a :: l, b :: m => by
    intro h
    simp only [eqb, Bool.and_eq_true, beq_iff_eq] at h
    have h1 := toPoly_eq_of_eqb p l m h.2
    have h2 : (a : ZMod p) = b := (ZMod.natCast_eq_natCast_iff' a b p).2 h.1
    simp [h1, h2]

/-! ### Forcing evaluation in the kernel -/

/-- `f n`, with `n` evaluated to a numeral first (see `PerfectCuboid.Descent.withNat`). -/
def withN (n : ℕ) (f : ℕ → Bool) : Bool :=
  match n with
  | 0 => f 0
  | k + 1 => f (k + 1)

theorem withN_eq (n : ℕ) (f : ℕ → Bool) : withN n f = f n := by cases n <;> rfl

/-- `f l`, with every entry of `l` evaluated to a numeral first. -/
def forceL : List ℕ → (List ℕ → Bool) → Bool
  | [], f => f []
  | a :: t, f => withN a fun a' ↦ forceL t fun t' ↦ f (a' :: t')

theorem forceL_eq : ∀ (l : List ℕ) (f : List ℕ → Bool), forceL l f = f l
  | [], _ => rfl
  | a :: t, f => by rw [forceL, withN_eq, forceL_eq t]

/-! ### Unverified division and Euclid (their output is checked afterwards) -/

/-- Strip leading (top) zero coefficients. -/
def trimL (p : ℕ) (l : List ℕ) : List ℕ := (l.reverse.dropWhile fun a ↦ a % p == 0).reverse

/-- `r − c · h` at the top of `r` (lists written from the top coefficient down). -/
def subTop (p c : ℕ) : List ℕ → List ℕ → List ℕ
  | r :: rt, h :: ht => (r + (p - c * h % p)) % p :: subTop p c rt ht
  | rt, [] => rt
  | [], _ :: _ => []

/-- Long division by a monic polynomial with top-down tail `ht` (lists top-down), in
continuation-passing style: ends with `k q r`. -/
def divRevK (p : ℕ) (ht : List ℕ) (k : List ℕ → List ℕ → Bool) :
    ℕ → List ℕ → List ℕ → Bool
  | 0, r, q => k q r
  | _ + 1, [], q => k q []
  | n + 1, c :: rt, q =>
    if rt.length < ht.length then k q (c :: rt)
    else withN (c % p) fun c' ↦ forceL (subTop p c' rt ht) fun r ↦ divRevK p ht k n r (c' :: q)

theorem exists_of_divRevK (p : ℕ) (ht : List ℕ) (k : List ℕ → List ℕ → Bool) :
    ∀ n r q, divRevK p ht k n r q = true → ∃ q r, k q r = true
  | 0, r, q, h => ⟨q, r, h⟩
  | _ + 1, [], q, h => ⟨q, [], h⟩
  | n + 1, c :: rt, q, h => by
    rw [divRevK] at h
    split at h
    · exact ⟨_, _, h⟩
    · rw [withN_eq, forceL_eq] at h
      exact exists_of_divRevK p ht k n _ _ h

/-- Quotient `q` and remainder `r` of `l` by the monic `h` (bottom-up lists): ends with
`k q r`. -/
def divModK (p : ℕ) (l h : List ℕ) (k : List ℕ → List ℕ → Bool) : Bool :=
  divRevK p h.reverse.tail (fun q r ↦ k q r.reverse) (l.length + 1) l.reverse []

theorem exists_of_divModK {p : ℕ} {l h : List ℕ} {k : List ℕ → List ℕ → Bool}
    (hk : divModK p l h k = true) : ∃ q r, k q r = true := by
  obtain ⟨q, r, h⟩ := exists_of_divRevK _ _ _ _ _ _ hk
  exact ⟨q, _, h⟩

/-- `k (l ^ n)`, with every intermediate power evaluated. -/
def powK (p : ℕ) (l : List ℕ) : (List ℕ → Bool) → ℕ → Bool
  | k, 0 => k [1]
  | k, n + 1 => powK p l (fun s ↦ forceL (mulL p s l) k) n

theorem powK_eq (p : ℕ) (l : List ℕ) : ∀ k n, powK p l k n = k (powL p l n)
  | _, 0 => rfl
  | k, n + 1 => by rw [powK, powK_eq, forceL_eq, powL]

/-- Inverse modulo the prime `p`. -/
def invP (p a : ℕ) : ℕ := a ^ (p - 2) % p

/-- Leading coefficient. -/
def leadL (l : List ℕ) : ℕ := l.getLast?.getD 0

/-- Extended Euclid in continuation-passing style: calls `k s t` with `s a + t b = 1` when
`gcd (a, b) = 1` (`r₀ = s₀ a + t₀ b`, `r₁ = s₁ a + t₁ b` along the way). -/
def xgcdK (p : ℕ) (k : List ℕ → List ℕ → Bool) :
    ℕ → List ℕ → List ℕ → List ℕ → List ℕ → List ℕ → List ℕ → Bool
  | 0, _, s₀, t₀, _, _, _ => k s₀ t₀
  | n + 1, r₀, s₀, t₀, r₁, s₁, t₁ =>
    forceL (trimL p r₁) fun r₁ ↦
      match r₁ with
      | [] => let c := invP p (leadL r₀); k (smulL p c s₀) (smulL p c t₀)
      | _ :: _ =>
        withN (invP p (leadL r₁)) fun c ↦
          divModK p r₀ (smulL p c r₁) fun q r ↦ forceL (smulL p c q) fun q ↦
            forceL r fun r ↦ forceL (subL p s₀ (mulL p q s₁)) fun s ↦
              forceL (subL p t₀ (mulL p q t₁)) fun t ↦ xgcdK p k n r₁ s₁ t₁ r s t

theorem exists_of_xgcdK (p : ℕ) (k : List ℕ → List ℕ → Bool) :
    ∀ n r₀ s₀ t₀ r₁ s₁ t₁, xgcdK p k n r₀ s₀ t₀ r₁ s₁ t₁ = true → ∃ s t, k s t = true
  | 0, _, s₀, t₀, _, _, _, h => ⟨s₀, t₀, h⟩
  | n + 1, r₀, s₀, t₀, r₁, s₁, t₁, h => by
    rw [xgcdK, forceL_eq] at h
    split at h
    · exact ⟨_, _, h⟩
    · rw [withN_eq] at h
      obtain ⟨q, r, h⟩ := exists_of_divModK h
      rw [forceL_eq, forceL_eq, forceL_eq, forceL_eq] at h
      exact exists_of_xgcdK p k n _ _ _ _ _ _ h

/-! ### Checked facts -/

/-- `h ∣ d`, checked by dividing. -/
def dvdB (p : ℕ) (h d : List ℕ) : Bool := divModK p d h fun q _ ↦ eqb p d (mulL p h q)

theorem dvd_of_dvdB {p : ℕ} {h d : List ℕ} (hd : dvdB p h d = true) :
    toPoly p h ∣ toPoly p d := by
  obtain ⟨q, _, hq⟩ := exists_of_divModK hd
  exact ⟨_, (toPoly_eq_of_eqb p _ _ hq).trans (toPoly_mulL _ _ _)⟩

/-- `a` and `b` are coprime, checked by a Bézout identity. -/
def coprimeB (p : ℕ) (a b : List ℕ) : Bool :=
  xgcdK p (fun s t ↦ eqb p (addL p (mulL p s a) (mulL p t b)) [1])
    (a.length + b.length + 2) a [1] [] b [] [1]

theorem isCoprime_of_coprimeB {p : ℕ} {a b : List ℕ} (h : coprimeB p a b = true) :
    IsCoprime (toPoly p a) (toPoly p b) := by
  obtain ⟨s, t, hst⟩ := exists_of_xgcdK p _ _ _ _ _ _ _ _ h
  refine ⟨toPoly p s, toPoly p t, ?_⟩
  have := toPoly_eq_of_eqb p _ _ hst
  rw [toPoly_addL, toPoly_mulL, toPoly_mulL] at this
  simpa using this

/-! ### Irreducibility over `ZMod p` -/

/-- The last coefficient is `1`. -/
def lastIsOne : List ℕ → Bool
  | [] => false
  | [a] => a == 1
  | _ :: b :: t => lastIsOne (b :: t)

theorem monic_toPoly {p : ℕ} [Fact p.Prime] :
    ∀ l, lastIsOne l = true → (toPoly p l).Monic ∧ (toPoly p l).natDegree = l.length - 1
  | [], h => by simp [lastIsOne] at h
  | [a], h => by
    simp only [lastIsOne, beq_iff_eq] at h
    subst h
    simp
  | a :: b :: t, h => by
    obtain ⟨hm, hd⟩ := monic_toPoly (p := p) (b :: t) h
    have hX : (X * toPoly p (b :: t)).Monic := monic_X.mul hm
    have hXd : (X * toPoly p (b :: t)).natDegree = t.length + 1 := by
      rw [(monic_X).natDegree_mul hm, hd, natDegree_X]; simp; omega
    have hlt : (C (a : ZMod p)).degree < (X * toPoly p (b :: t)).degree := by
      rw [degree_eq_natDegree hX.ne_zero, hXd]
      exact (degree_C_le).trans_lt (by exact_mod_cast Nat.succ_pos _)
    rw [toPoly_cons]
    refine ⟨hX.add_of_right hlt, ?_⟩
    rw [natDegree_add_eq_right_of_degree_lt hlt, hXd]
    simp

theorem dvd_X_pow_sub_X {p : ℕ} [Fact p.Prime] {q : (ZMod p)[X]} (hq : Irreducible q) :
    q ∣ X ^ p ^ q.natDegree - X := by
  have := (hq.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := q.natDegree)).1 dvd_rfl
  rwa [Nat.card_zmod] at this

/-- A monic `h` of degree `n` is irreducible if it is coprime to `X ^ (p ^ k) − X` for
`1 ≤ k ≤ n / 2`. -/
theorem irreducible_of_isCoprime {p : ℕ} [Fact p.Prime] {h : (ZMod p)[X]} (hm : h.Monic)
    (h1 : h ≠ 1) (hc : ∀ k, 0 < k → k ≤ h.natDegree / 2 → IsCoprime h (X ^ p ^ k - X)) :
    Irreducible h := by
  rw [hm.irreducible_iff_lt_natDegree_lt h1]
  intro g hg hdg hgh
  rw [Finset.mem_Ioc] at hdg
  have hgu : ¬ IsUnit g := fun hu ↦ by
    rw [natDegree_eq_zero_of_isUnit hu] at hdg; exact lt_irrefl _ hdg.1
  obtain ⟨q, hq, hqg⟩ := WfDvdMonoid.exists_irreducible_factor hgu hg.ne_zero
  have hqd : q.natDegree ≤ g.natDegree := natDegree_le_of_dvd hqg hg.ne_zero
  exact hq.not_isUnit ((hc _ hq.natDegree_pos (hqd.trans hdg.2)).isUnit_of_dvd'
    (hqg.trans hgh) (dvd_X_pow_sub_X hq))

/-! ### The Frobenius chain via the Berlekamp matrix -/

/-- The remainder `r` of `a` modulo the monic `h`, with `a = h q + r` checked; ends with
`k r`. -/
def modK (p : ℕ) (h a : List ℕ) (k : List ℕ → Bool) : Bool :=
  divModK p a h fun q r ↦ eqb p a (addL p (mulL p h q) r) && forceL r k

theorem exists_of_modK {p : ℕ} {h a : List ℕ} {k : List ℕ → Bool} (hk : modK p h a k = true) :
    ∃ r, toPoly p h ∣ toPoly p a - toPoly p r ∧ k r = true := by
  obtain ⟨q, r, hk⟩ := exists_of_divModK hk
  rw [Bool.and_eq_true, forceL_eq] at hk
  refine ⟨r, ⟨toPoly p q, ?_⟩, hk.2⟩
  rw [toPoly_eq_of_eqb p _ _ hk.1, toPoly_addL, toPoly_mulL]
  ring

/-- `ms = [mⱼ, mⱼ₊₁, …]` with `mᵢ ≡ X ^ (p i) (mod h)`: rows of the Berlekamp matrix. -/
def QM (p : ℕ) (h : (ZMod p)[X]) : ℕ → List (List ℕ) → Prop
  | _, [] => True
  | j, m :: ms => h ∣ X ^ (p * j) - toPoly p m ∧ QM p h (j + 1) ms

theorem QM_append {p : ℕ} {h : (ZMod p)[X]} (m : List ℕ) :
    ∀ (ms : List (List ℕ)) (j : ℕ),
      QM p h j (ms ++ [m]) ↔ QM p h j ms ∧ h ∣ X ^ (p * (j + ms.length)) - toPoly p m
  | [], j => by simp [QM]
  | m' :: ms, j => by
    simp only [List.cons_append, QM, QM_append m ms (j + 1), List.length_cons]
    rw [show j + 1 + ms.length = j + (ms.length + 1) by omega, and_assoc]

/-- `∑ rᵢ mᵢ`, the image of `r ^ p` under the Berlekamp matrix. -/
def combL (p : ℕ) : List ℕ → List (List ℕ) → List ℕ
  | [], _ => []
  | _ :: _, [] => []
  | a :: r, m :: ms => addL p (smulL p a m) (combL p r ms)

theorem toPoly_expand_cons (p a : ℕ) (l : List ℕ) :
    expand (ZMod p) p (toPoly p (a :: l)) =
      C (a : ZMod p) + X ^ p * expand (ZMod p) p (toPoly p l) := by
  simp

theorem dvd_combL {p : ℕ} {h : (ZMod p)[X]} :
    ∀ (r : List ℕ) (ms : List (List ℕ)) (j : ℕ), r.length ≤ ms.length → QM p h j ms →
      h ∣ X ^ (p * j) * expand (ZMod p) p (toPoly p r) - toPoly p (combL p r ms)
  | [], _, j, _, _ => by simp [combL]
  | a :: r, [], j, hl, _ => by simp at hl
  | a :: r, m :: ms, j, hl, hq => by
    obtain ⟨hm, hms⟩ := hq
    have ih := dvd_combL r ms (j + 1) (by simpa using hl) hms
    rw [combL, toPoly_addL, toPoly_smulL, toPoly_expand_cons]
    have : X ^ (p * j) * (C (a : ZMod p) + X ^ p * expand (ZMod p) p (toPoly p r))
        - (C (a : ZMod p) * toPoly p m + toPoly p (combL p r ms))
        = C (a : ZMod p) * (X ^ (p * j) - toPoly p m)
          + (X ^ (p * (j + 1)) * expand (ZMod p) p (toPoly p r) - toPoly p (combL p r ms)) := by
      ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right hm _) ih

/-- Rows `m₂, m₃, …` of the Berlekamp matrix: `mᵢ₊₁ = mᵢ m₁ mod h`. Ends with `k ms`. -/
def qmatK (p : ℕ) (h m₁ : List ℕ) (k : List (List ℕ) → Bool) :
    ℕ → List ℕ → List (List ℕ) → Bool
  | 0, _, acc => k acc
  | n + 1, m, acc => modK p h (mulL p m m₁) fun m' ↦ qmatK p h m₁ k n m' (acc ++ [m'])

theorem exists_of_qmatK {p : ℕ} {h m₁ : List ℕ} {k : List (List ℕ) → Bool}
    (h₁ : toPoly p h ∣ X ^ p - toPoly p m₁) :
    ∀ n m acc, qmatK p h m₁ k n m acc = true → QM p (toPoly p h) 0 acc → 0 < acc.length →
      toPoly p h ∣ X ^ (p * (acc.length - 1)) - toPoly p m →
      ∃ ms, QM p (toPoly p h) 0 ms ∧ acc.length ≤ ms.length ∧ k ms = true
  | 0, _, acc, hk, hq, _, _ => ⟨acc, hq, le_rfl, hk⟩
  | n + 1, m, acc, hk, hq, hl, hm => by
    rw [qmatK] at hk
    obtain ⟨m', hm', hk⟩ := exists_of_modK hk
    rw [toPoly_mulL] at hm'
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
    obtain ⟨ms, hms, hlen, hk⟩ := exists_of_qmatK h₁ n m' (acc ++ [m']) hk
      ((QM_append m' acc 0).2 ⟨hq, by simpa using hm''⟩) (by simp) (by simpa using hm'')
    exact ⟨ms, hms, by simp at hlen; omega, hk⟩

/-- Steps `k + 1, …, k + n` of the Frobenius chain: `r ≡ X ^ (p ^ k) (mod h)` on entry; each
step computes `r' ≡ r ^ p (mod h)` with the Berlekamp matrix `ms` and checks
`gcd (h, r' − X) = 1`. -/
def frobLoop (p : ℕ) (h : List ℕ) (ms : List (List ℕ)) : ℕ → List ℕ → Bool
  | 0, _ => true
  | n + 1, r => decide (r.length ≤ ms.length) && forceL (combL p r ms) fun r' ↦
      coprimeB p h (subL p r' [0, 1]) && frobLoop p h ms n r'

theorem isCoprime_of_frobLoop {p : ℕ} [Fact p.Prime] {h : List ℕ} {ms : List (List ℕ)}
    (hQ : QM p (toPoly p h) 0 ms) :
    ∀ n k r, frobLoop p h ms n r = true → toPoly p h ∣ X ^ p ^ k - toPoly p r →
      ∀ j, 0 < j → j ≤ n → IsCoprime (toPoly p h) (X ^ p ^ (k + j) - X)
  | 0, _, _, _, _, j, hj, hjn => absurd hjn (by omega)
  | n + 1, k, r, hl, hr, j, hj, hjn => by
    have hp : 0 < p := (Fact.out : p.Prime).pos
    rw [frobLoop, forceL_eq] at hl
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
    · have := isCoprime_of_frobLoop hQ n (k + 1) r' hl hr' (j - 1) (by omega) (by omega)
      rwa [show k + 1 + (j - 1) = k + j by omega] at this
    · obtain rfl : j = 1 := by omega
      have hc := isCoprime_of_coprimeB hc
      rw [toPoly_subL hp] at hc
      obtain ⟨m, hm⟩ := hr'
      have : X ^ p ^ (k + 1) - X = (toPoly p r' - toPoly p [0, 1]) + toPoly p h * m := by
        rw [← hm]; simp
      rw [this]
      exact hc.add_mul_left_right m

/-- The list of `X ^ p`. -/
def xpowL (p : ℕ) : List ℕ := List.replicate p 0 ++ [1]

theorem toPoly_replicate_append (p : ℕ) (l : List ℕ) :
    ∀ n, toPoly p (List.replicate n 0 ++ l) = X ^ n * toPoly p l
  | 0 => by simp
  | n + 1 => by
    rw [List.replicate_succ, List.cons_append, toPoly_cons, toPoly_replicate_append p l n]
    simp [pow_succ']; ring

theorem toPoly_xpowL (p : ℕ) : toPoly p (xpowL p) = X ^ p := by
  rw [xpowL, toPoly_replicate_append]; simp

/-- Irreducibility test: the Frobenius chain up to half the degree. -/
def irredB (p : ℕ) (h : List ℕ) : Bool :=
  lastIsOne h && 2 ≤ h.length && modK p h (xpowL p) fun m₁ ↦
    qmatK p h m₁ (fun ms ↦ frobLoop p h ms ((h.length - 1) / 2) [0, 1]) (h.length - 2) m₁ [[1], m₁]

theorem irreducible_of_irredB {p : ℕ} [Fact p.Prime] {h : List ℕ} (hb : irredB p h = true) :
    Irreducible (toPoly p h) := by
  simp only [irredB, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hl, hlen⟩, hf⟩ := hb
  obtain ⟨m₁, h₁, hf⟩ := exists_of_modK hf
  rw [toPoly_xpowL] at h₁
  obtain ⟨ms, hQ, hmsl, hf⟩ := exists_of_qmatK h₁ _ _ _ hf
    ⟨by simp, by simpa using h₁, trivial⟩ (by simp) (by simpa using h₁)
  obtain ⟨hm, hd⟩ := monic_toPoly (p := p) h hl
  refine irreducible_of_isCoprime hm (fun h1 ↦ ?_) fun k hk hkn ↦ ?_
  · rw [h1, natDegree_one] at hd; omega
  · have := isCoprime_of_frobLoop hQ _ 0 _ hf (by simp) k hk (by rw [← hd]; exact hkn)
    simpa using this

/-! ### Degrees of divisors of a product of irreducibles -/

/-- All subset sums of a list (with repetitions). -/
def sums : List ℕ → List ℕ
  | [] => [0]
  | d :: ds => sums ds ++ (sums ds).map (d + ·)

/-- Every divisor of a product of irreducible polynomials has as degree a subset sum of their
degrees. -/
theorem natDegree_mem_sums {K : Type*} [Field K] :
    ∀ fs : List K[X], (∀ f ∈ fs, Irreducible f) →
      ∀ u, u ∣ fs.prod → u.natDegree ∈ sums (fs.map natDegree)
  | [], _, u, hu => by
    simp [sums, natDegree_eq_zero_of_isUnit (isUnit_of_dvd_one hu)]
  | f :: fs, hirr, u, ⟨w, hw⟩ => by
    have hf := hirr f (by simp)
    have hfs : ∀ g ∈ fs, Irreducible g := fun g hg ↦ hirr g (by simp [hg])
    have hR : fs.prod ≠ 0 := by
      rw [Ne, List.prod_eq_zero_iff]
      exact fun h0 ↦ (hfs 0 h0).ne_zero rfl
    rw [List.prod_cons] at hw
    simp only [List.map_cons, sums, List.mem_append, List.mem_map]
    rcases hf.prime.dvd_or_dvd (⟨fs.prod, hw.symm⟩ : f ∣ u * w) with ⟨u', rfl⟩ | ⟨w', rfl⟩
    · have h' : u' * w = fs.prod := mul_left_cancel₀ hf.ne_zero (by rw [hw]; ring)
      have hu' : u' ≠ 0 := by
        rintro rfl
        exact hR (by rw [← h', zero_mul])
      exact Or.inr ⟨u'.natDegree, natDegree_mem_sums fs hfs u' ⟨w, h'.symm⟩, by
        rw [natDegree_mul hf.ne_zero hu']⟩
    · have h' : u * w' = fs.prod := mul_left_cancel₀ hf.ne_zero (by rw [hw]; ring)
      exact Or.inl (natDegree_mem_sums fs hfs u ⟨w', h'.symm⟩)

/-- **Two-prime criterion.** A monic integer polynomial `g` is irreducible if the degrees of the
divisors of its reductions modulo two primes have no common value other than `0` and
`deg g`. -/
theorem irreducible_of_two_primes {g : ℤ[X]} (hg : g.Monic) (hg1 : g ≠ 1) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] {Sp Sq : List ℕ}
    (hp : ∀ u : (ZMod p)[X], u ∣ g.map (Int.castRingHom _) → u.natDegree ∈ Sp)
    (hq : ∀ u : (ZMod q)[X], u ∣ g.map (Int.castRingHom _) → u.natDegree ∈ Sq)
    (hS : ∀ d ∈ Sp, d ∈ Sq → d = 0 ∨ d = g.natDegree) : Irreducible g := by
  rw [hg.irreducible_iff_natDegree]
  refine ⟨hg1, fun f h hf hh hfh ↦ ?_⟩
  have key : ∀ (r : ℕ) [Fact r.Prime],
      f.map (Int.castRingHom (ZMod r)) ∣ g.map (Int.castRingHom (ZMod r)) :=
    fun r _ ↦ ⟨h.map _, by rw [← hfh, Polynomial.map_mul]⟩
  have h1 := hp _ (key p)
  have h2 := hq _ (key q)
  rw [hf.natDegree_map] at h1 h2
  rcases hS _ h1 h2 with h0 | hn
  · exact Or.inl h0
  · rw [← hfh, hf.natDegree_mul hh] at hn
    exact Or.inr (by omega)

/-! ### The third cuboid polynomial modulo `p` -/

/-- The coefficients of `cuboidThreePoly` in terms of `A = a², B = b², C = c²`. -/
def cuboidCoeffsZ (A B C : ℤ) : List ℤ :=
  [C ^ 2 * A ^ 2 * B ^ 2, 0, 6 * A ^ 2 * C * B ^ 2 - 2 * C ^ 2 * A ^ 2 * B - 2 * C ^ 2 * A * B ^ 2,
    0, 4 * C * B ^ 2 * A + 4 * A ^ 2 * C * B - 12 * C ^ 2 * A * B + C ^ 2 * A ^ 2 + C ^ 2 * B ^ 2
      + A ^ 2 * B ^ 2,
    0, 6 * A ^ 2 * C + 6 * C * B ^ 2 - 8 * A * B * C - 2 * C ^ 2 * A - 2 * C ^ 2 * B
      - 2 * A ^ 2 * B - 2 * B ^ 2 * A,
    0, C ^ 2 + B ^ 2 + A ^ 2 + 4 * A * C + 4 * B * C - 12 * B * A, 0, 6 * C - 2 * A - 2 * B, 0, 1]

/-- The coefficients of `cuboidThreePoly` modulo `p`, from `A = a², B = b², C = c²` mod `p`. -/
def cuboidCoeffs (p A B C : ℕ) : List ℕ :=
  (cuboidCoeffsZ A B C).map fun e ↦ (e % (p : ℤ)).toNat

theorem cast_toNat_emod {p : ℕ} (hp : 0 < p) (e : ℤ) :
    (((e % (p : ℤ)).toNat : ℕ) : ZMod p) = (e : ZMod p) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne')),
    ZMod.intCast_mod]

theorem map_cuboidThreePoly {p : ℕ} (hp : 0 < p) {a b c : ℤ} {A B C : ℕ}
    (hA : (A : ZMod p) = (a : ZMod p) ^ 2) (hB : (B : ZMod p) = (b : ZMod p) ^ 2)
    (hC : (C : ZMod p) = (c : ZMod p) ^ 2) :
    (cuboidThreePoly a b c).map (Int.castRingHom (ZMod p)) = toPoly p (cuboidCoeffs p A B C) := by
  simp only [cuboidCoeffs, cuboidCoeffsZ, List.map_cons, List.map_nil, toPoly_cons, toPoly_nil,
    cast_toNat_emod hp, cuboidThreePoly, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Int.coe_castRingHom]
  push_cast
  rw [hA, hB, hC]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, C_0, C_1]
  ring

theorem monic_cuboidThreePoly (a b c : ℤ) : (cuboidThreePoly a b c).Monic := by
  unfold cuboidThreePoly; monicity!

theorem natDegree_cuboidThreePoly (a b c : ℤ) : (cuboidThreePoly a b c).natDegree = 12 := by
  unfold cuboidThreePoly; compute_degree!

/-! ### Certificates for residue classes -/

/-- Product of a list of coefficient lists. -/
def prodL (p : ℕ) (fs : List (List ℕ)) : List ℕ := fs.foldr (mulL p) [1]

theorem toPoly_prodL (p : ℕ) : ∀ fs, toPoly p (prodL p fs) = (fs.map (toPoly p)).prod
  | [] => by simp [prodL]
  | f :: fs => by
    have := toPoly_prodL p fs
    simp only [prodL, List.foldr_cons, List.map_cons, List.prod_cons] at this ⊢
    rw [toPoly_mulL, this, mul_comm]

/-- The degrees of a list of (monic) coefficient lists. -/
def degs (fs : List (List ℕ)) : List ℕ := fs.map (·.length - 1)

/-- A certificate for one residue class `(A, B, C) = (a², b², c²) mod p`: the factorization of
`cuboidThreePoly` modulo `p` into irreducible monic factors. -/
def classOK (p : ℕ) (e : (ℕ × ℕ × ℕ) × List (List ℕ)) : Bool :=
  eqb p (cuboidCoeffs p e.1.1 e.1.2.1 e.1.2.2) (prodL p e.2) && e.2.all (irredB p)

theorem natDegree_mem_of_classOK {p : ℕ} [Fact p.Prime] {e : (ℕ × ℕ × ℕ) × List (List ℕ)}
    (he : classOK p e = true) {a b c : ℤ} (hA : (e.1.1 : ZMod p) = (a : ZMod p) ^ 2)
    (hB : (e.1.2.1 : ZMod p) = (b : ZMod p) ^ 2) (hC : (e.1.2.2 : ZMod p) = (c : ZMod p) ^ 2)
    (u : (ZMod p)[X]) (hu : u ∣ (cuboidThreePoly a b c).map (Int.castRingHom (ZMod p))) :
    u.natDegree ∈ sums (degs e.2) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simp only [classOK, Bool.and_eq_true, List.all_eq_true] at he
  rw [map_cuboidThreePoly hp hA hB hC, toPoly_eq_of_eqb _ _ _ he.1, toPoly_prodL] at hu
  have hd : (e.2.map (toPoly p)).map natDegree = degs e.2 := by
    rw [degs, List.map_map]
    refine List.map_congr_left fun f hf ↦ ?_
    have := he.2 f hf
    simp only [irredB, Bool.and_eq_true] at this
    exact (monic_toPoly (p := p) f this.1.1).2
  rw [← hd]
  refine natDegree_mem_sums _ ?_ u hu
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  exact irreducible_of_irredB (he.2 f hf)

/-- Two tables are compatible: subset sums of degrees meet only in `0` and `12`. -/
def compatB (tP tQ : List ((ℕ × ℕ × ℕ) × List (List ℕ))) : Bool :=
  tP.all fun e ↦ tQ.all fun e' ↦
    (sums (degs e.2)).all fun d ↦ !((sums (degs e'.2)).contains d) || d == 0 || d == 12

/-- `a² mod p` as a natural number. -/
def sqMod (p : ℕ) (a : ℤ) : ℕ := (a ^ 2 % (p : ℤ)).toNat

theorem cast_sqMod {p : ℕ} (hp : 0 < p) (a : ℤ) : (sqMod p a : ZMod p) = (a : ZMod p) ^ 2 := by
  rw [sqMod, cast_toNat_emod hp]; push_cast; rfl

/-- **Main criterion.** If `(a², b², c²)` modulo `p` and modulo `q` are covered by compatible
certified tables, then `cuboidThreePoly a b c` is irreducible over `ℤ`. -/
theorem irreducible_of_tables {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {tP tQ : List ((ℕ × ℕ × ℕ) × List (List ℕ))} (hP : tP.all (classOK p) = true)
    (hQ : tQ.all (classOK q) = true) (hc : compatB tP tQ = true) {a b c : ℤ}
    (ha : (sqMod p a, sqMod p b, sqMod p c) ∈ tP.map Prod.fst)
    (hb : (sqMod q a, sqMod q b, sqMod q c) ∈ tQ.map Prod.fst) :
    Irreducible (cuboidThreePoly a b c) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hq : 0 < q := (Fact.out : q.Prime).pos
  obtain ⟨e, he, hek⟩ := List.mem_map.1 ha
  obtain ⟨e', he', hek'⟩ := List.mem_map.1 hb
  rw [List.all_eq_true] at hP hQ
  have hg1 : cuboidThreePoly a b c ≠ 1 := fun h ↦ by
    have := natDegree_cuboidThreePoly a b c
    rw [h, natDegree_one] at this; omega
  refine irreducible_of_two_primes (monic_cuboidThreePoly a b c) hg1
    (natDegree_mem_of_classOK (hP e he) ?_ ?_ ?_)
    (natDegree_mem_of_classOK (hQ e' he') ?_ ?_ ?_) ?_
  · rw [hek]; exact cast_sqMod hp a
  · rw [hek]; exact cast_sqMod hp b
  · rw [hek]; exact cast_sqMod hp c
  · rw [hek']; exact cast_sqMod hq a
  · rw [hek']; exact cast_sqMod hq b
  · rw [hek']; exact cast_sqMod hq c
  · intro d hd hd'
    rw [natDegree_cuboidThreePoly]
    have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 hc e he) e' he') d hd
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    rcases this with (h | h) | h
    · simp_all
    · exact Or.inl h
    · exact Or.inr h

end PerfectCuboid.ThirdConjecture.ModP
