module

public import LeanPlayground.PerfectCuboid.DescentTR

/-!
# The descent with the class lemma

`LeanPlayground.PerfectCuboid.Descent` reduces a solution of `IsSol p q` to the cases
`(λ, c₁, c₂, c₃, c₄, σ)` of `CasesOK p q D`. For a large pair there are millions of cases. Most of
them die for a reason that only depends on `(λ, σ)`: the `2`-descent class `(qλ, Dλσ)` of the
point is not in the `2`-Selmer group (`ClassKill`, proved by `classKill_sound`). The class only
depends on `σ` up to squares, so this file groups the cases by `λ` and by `σ₀`, where
`σ = σ₀ t²`, and checks the class once per group. Only the few groups whose class survives are
split into their cases `(c₁, c₃, t)`, each handled by a torsion family or a residue check.

The divisors are listed from factorizations (`facOf`, `divsF`, `sqGroups`) over a list of primes
`Ps`, instead of by trial division, since `λ'` can be close to `10¹²`. The classes are checked
modulo prime powers; the distinct ones (`keys`) are checked once, in a binary tree (`KTree`) that
the groups index into.

## Main results

* `exists_sqGroups` — every divisor `σ` of `∏ lᵉ` is `σ₀ t²` for a group `(σ₀, ts)` with `t ∈ ts`.
* `casesOn_of_classCert` — soundness of the grouped certificate.
* `CasesOn.casesOK` — the certificates for all `λ` and `σ` give `CasesOK p q D`.
-/

@[expose] public section

namespace PerfectCuboid

namespace Descent

/-! ### Primes and factorizations -/

/-- Trial division: `l` is prime. -/
def primeB (l : ℕ) : Bool :=
  decide (2 ≤ l) && allBelow l fun d ↦ decide (d < 2) || l % d != 0

theorem prime_of_primeB {l : ℕ} (h : primeB l = true) : l.Prime := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq, allBelow_iff, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at h
  refine Nat.prime_def_lt'.mpr ⟨h.1, fun m hm hml hdvd ↦ ?_⟩
  rcases h.2 m hml with h' | h'
  · omega
  · exact h' (Nat.mod_eq_zero_of_dvd hdvd)

theorem primes_of_all {Ps : List ℕ} (h : Ps.all primeB = true) : ∀ l ∈ Ps, l.Prime :=
  fun l hl ↦ prime_of_primeB (List.all_eq_true.mp h l hl)

/-- `∏ lᵉ` over a list of pairs `(l, e)`. -/
def prodF : List (ℕ × ℕ) → ℕ
  | [] => 1
  | x :: F => x.1 ^ x.2 * prodF F

theorem prodF_pos {F : List (ℕ × ℕ)} (hF : ∀ x ∈ F, x.1.Prime) : 0 < prodF F := by
  induction F with
  | nil => exact Nat.one_pos
  | cons x F ih =>
    exact Nat.mul_pos (pow_pos (hF x List.mem_cons_self).pos _)
      (ih fun y hy ↦ hF y (List.mem_cons_of_mem _ hy))

/-- The exponent of `l` in `n`, with `f` steps of fuel. -/
def valF (l : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n != 0 && n % l == 0 then valF l f (n / l) + 1 else 0

/-- The exponents of the primes `Ps` in `n`. This is the factorization of `n` when
`prodF (facOf Ps n) = n`, which the checks below test. -/
def facOf (Ps : List ℕ) (n : ℕ) : List (ℕ × ℕ) := Ps.map fun l ↦ (l, valF l 256 n)

theorem primes_facOf {Ps : List ℕ} (hPs : ∀ l ∈ Ps, l.Prime) (n : ℕ) :
    ∀ x ∈ facOf Ps n, x.1.Prime := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  exact hPs l hl

/-- `1, l, …, lᵉ`. -/
def powsUpTo (l e : ℕ) : List ℕ := (List.range (e + 1)).map (l ^ ·)

theorem mem_powsUpTo {l e u : ℕ} (hl : l.Prime) (hu : u ∣ l ^ e) : u ∈ powsUpTo l e := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hl).mp hu
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩

/-- The divisors of `prodF F`. -/
def divsF : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | x :: F => divsProd (powsUpTo x.1 x.2) (x.1 ^ x.2) (divsF F)

theorem mem_divsF : ∀ {F : List (ℕ × ℕ)}, (∀ x ∈ F, x.1.Prime) → ∀ {d : ℕ}, d ∣ prodF F →
    d ∈ divsF F
  | [], _, d, hd => by
    rw [prodF, Nat.dvd_one] at hd
    simp [divsF, hd]
  | x :: F, hF, _, hd => by
    have hx := hF x List.mem_cons_self
    have hF' : ∀ y ∈ F, y.1.Prime := fun y hy ↦ hF y (List.mem_cons_of_mem _ hy)
    exact mem_divsProd (pow_pos hx.pos _) (prodF_pos hF') (fun u hu ↦ mem_powsUpTo hx hu)
      (fun v hv ↦ mem_divsF hF' hv) hd

/-- The divisors `σ` of `prodF F` grouped by `σ₀`: each group `(σ₀, ts)` stands for the
divisors `σ₀ t²` with `t ∈ ts`. -/
def sqGroups : List (ℕ × ℕ) → List (ℕ × List ℕ)
  | [] => [(1, [1])]
  | x :: F => (sqGroups F).flatMap fun g ↦
      (g.1, (List.range (x.2 / 2 + 1)).flatMap fun j ↦ g.2.map (x.1 ^ j * ·)) ::
        if x.2 == 0 then [] else
          [(x.1 * g.1, (List.range ((x.2 - 1) / 2 + 1)).flatMap fun j ↦ g.2.map (x.1 ^ j * ·))]

/-- Every divisor of `prodF F` is `σ₀ t²` for a group `(σ₀, ts)` of `sqGroups F` and `t ∈ ts`. -/
theorem exists_sqGroups : ∀ {F : List (ℕ × ℕ)}, (∀ x ∈ F, x.1.Prime) → ∀ {σ : ℕ},
    σ ∣ prodF F → ∃ g ∈ sqGroups F, ∃ t ∈ g.2, σ = g.1 * t ^ 2
  | [], _, σ, hσ => by
    rw [prodF, Nat.dvd_one] at hσ
    exact ⟨(1, [1]), by simp [sqGroups], 1, by simp, by simp [hσ]⟩
  | x :: F, hF, _, hσ => by
    have hx := hF x List.mem_cons_self
    have hF' : ∀ y ∈ F, y.1.Prime := fun y hy ↦ hF y (List.mem_cons_of_mem _ hy)
    obtain ⟨u, v, hu, hv, rfl⟩ := Nat.dvd_mul.mp hσ
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hx).mp hu
    obtain ⟨g, hg, t, ht, rfl⟩ := exists_sqGroups hF' hv
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · refine ⟨(g.1, (List.range (x.2 / 2 + 1)).flatMap fun j ↦ g.2.map (x.1 ^ j * ·)),
        List.mem_flatMap.mpr ⟨g, hg, List.mem_cons_self⟩, x.1 ^ j * t, ?_, by ring⟩
      exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (by omega), List.mem_map.mpr ⟨t, ht, rfl⟩⟩
    · have he : (x.2 == 0) = false := by simp; omega
      refine ⟨(x.1 * g.1, (List.range ((x.2 - 1) / 2 + 1)).flatMap fun j ↦ g.2.map (x.1 ^ j * ·)),
        List.mem_flatMap.mpr ⟨g, hg, ?_⟩, x.1 ^ j * t, ?_, by ring⟩
      · simp [he]
      · exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (by omega),
          List.mem_map.mpr ⟨t, ht, rfl⟩⟩

/-! ### Certificates -/

/-- `f a b` for the pairs of two lists of the same length. -/
def allZip {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && allZip f as bs
  | _, _ => false

theorem allZip_sound {α β : Type} {f : α → β → Bool} :
    ∀ {L : List α} {C : List β}, allZip f L C = true → ∀ a ∈ L, ∃ b, f a b = true
  | [], _, _, _, ha => absurd ha List.not_mem_nil
  | _ :: _, [], h, _, _ => by simp [allZip] at h
  | a :: L, b :: C, h, a', ha' => by
    simp only [allZip, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact ⟨b, h.1⟩
    · exact allZip_sound h.2 a' ha'

/-- A class test modulo a prime power: `(N, l, k, A, B)` with `N = lᵏ`, for the classes `A`, `B`
of `x`, `x + p²` modulo `N`. -/
abbrev Key := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The class check succeeds for the key: `classCheck` for `N ≤ 10⁵`, and `classCheckE` above,
where the mask of squares modulo `N` needs too much kernel memory. -/
def keyOK (p q : ℕ) : Key → Bool
  | (N, l, k, A, B) => primeB l && decide (0 < k) && N == l ^ k &&
      if N ≤ 100000 then classCheck N l A B (A * B % N) (p ^ 2 % N) (q ^ 2 % N)
      else classCheckE N l A B (A * B % N) (p ^ 2 % N) (q ^ 2 % N)

/-- A binary tree of keys: the root has index `0`, the left subtree the odd indices and the right
subtree the even ones. -/
inductive KTree where
  | leaf
  | node (l : KTree) (k : Key) (r : KTree)

/-- The key with index `j`. -/
def KTree.get : KTree → ℕ → Option Key
  | .leaf, _ => none
  | .node l k r, j => if j == 0 then some k else if j % 2 == 1 then l.get (j / 2) else
      r.get (j / 2 - 1)

/-- `f` holds on every key of the tree. -/
def KTree.all (f : Key → Bool) : KTree → Bool
  | .leaf => true
  | .node l k r => f k && l.all f && r.all f

theorem KTree.all_get {f : Key → Bool} : ∀ {t : KTree}, t.all f = true → ∀ {j : ℕ} {k : Key},
    t.get j = some k → f k = true
  | .leaf, _, _, _, h => by simp [KTree.get] at h
  | .node l k' r, ht, j, k, h => by
    simp only [KTree.all, Bool.and_eq_true] at ht
    simp only [KTree.get] at h
    split_ifs at h
    · cases h
      exact ht.1.1
    · exact KTree.all_get ht.1.2 h
    · exact KTree.all_get ht.2 h

/-- The test of one case `(c₁, c₂, c₃, c₄, σ)`: a torsion family with a box of at most `lim`
pairs, the residue check modulo `N`, or family TR (`trOK`). -/
inductive TCert where
  | torsion (lim : ℕ)
  | modulus (N l : ℕ)
  | tr (d1 yT X Y N k : ℕ) (Z : List ℤ)

/-- The test `c` succeeds on the case `x = (c₁, c₂, c₃, c₄, σ)`; family TR only counts when
`t4`, for the descent up to `±T₄`. -/
def tStep (t4 : Bool) (p q lam : ℕ) (x : ℕ × ℕ × ℕ × ℕ × ℕ) : TCert → Bool
  | .torsion lim => torsionOKL lim p q lam x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  | .modulus N l => decide (0 < N) && decide (2 ≤ l) && N % l == 0 &&
      tupleOK [(N, l)] q lam x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  | .tr d1 yT X Y N k Z => t4 && trOK p q lam x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 d1 yT X Y N k Z

theorem tStep_sound {t4 : Bool} {p q D lam : ℕ} {x : ℕ × ℕ × ℕ × ℕ × ℕ} {c : TCert}
    (h : tStep t4 p q lam x c = true) :
    CaseOKT t4 p q D lam x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  cases c with
  | torsion lim => exact Or.inl (Or.inl ⟨lim, h⟩)
  | modulus N l =>
    simp only [tStep, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact Or.inl (Or.inr (Or.inl ⟨N, l, h.1.1.1, h.1.1.2, Nat.dvd_of_mod_eq_zero h.1.2, h.2⟩))
  | tr d1 yT X Y N k Z =>
    simp only [tStep, Bool.and_eq_true] at h
    exact Or.inr ⟨h.1, d1, yT, X, Y, N, k, Z, h.2⟩

/-- The certificate of a group `(σ₀, ts)` of one `λ`: its class is ruled out by the key with
index `j`, with `b₀ ≡ Dλσ₀` modulo squares, or the list of the tests of its cases. -/
inductive GCert where
  | kill (j b0 : ℕ)
  | cases (cs : List TCert)

/-- The cases of a group `(σ₀, ts)`: `(c₁, c₂, c₃, c₄, σ₀ t²)` for `t ∈ ts`, `c₁ c₂ = p'` and
`c₃ c₄ = λ'` coprime splits, with `c₁`, `c₃` from the lists `C1`, `C3` of divisors of `p'`,
`λ'`, and `σlo ≤ σ₀ t² < σhi`. -/
def groupCases (slo shi p' l' s0 : ℕ) (ts C1 C3 : List ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (ts.filter fun t ↦ decide (slo ≤ s0 * t ^ 2) && decide (s0 * t ^ 2 < shi)).flatMap fun t ↦
    C1.flatMap fun c1 ↦
    if Nat.gcd c1 (p' / c1) != 1 then [] else
    C3.flatMap fun c3 ↦ if Nat.gcd c3 (l' / c3) != 1 then [] else
      [(c1, p' / c1, c3, l' / c3, s0 * t ^ 2)]

/-- The class of `(λ, σ₀)` is ruled out by the key with index `j`. -/
def killOK (keys : KTree) (D lam a0 s0 j b0 : ℕ) : Bool :=
  match keys.get j with
  | some (N, _, _, A, B) => decide (0 < b0) && isSq (D * lam * s0 * b0) && a0 % N == A &&
      b0 % N == B
  | none => false

/-- The certificate `c` handles the group `g`. -/
def groupOK (t4 : Bool) (p q D slo shi lam a0 p' l' : ℕ) (C1 C3 : List ℕ) (keys : KTree)
    (g : ℕ × List ℕ) : GCert → Bool
  | .kill j b0 => killOK keys D lam a0 g.1 j b0
  | .cases cs => allZip (tStep t4 p q lam) (groupCases slo shi p' l' g.1 g.2 C1 C3) cs

/-- `lamOK` with `p' = p / gcd(p, λ)`, `λ' = λ / gcd(p, λ)` and the factorizations `F1` of `p'`,
`F3` of `λ'` and `Fσ` of `λ'² D`. -/
def lamOKWith (t4 : Bool) (p q D slo shi : ℕ) (keys : KTree) (lam a0 p' l' : ℕ)
    (F1 F3 Fσ : List (ℕ × ℕ)) (gs : List GCert) : Bool :=
  decide (0 < a0) && isSq (q * lam * a0) && prodF F1 == p' && prodF F3 == l' &&
    prodF Fσ == l' ^ 2 * D &&
    allZip (groupOK t4 p q D slo shi lam a0 p' l' (divsF F1) (divsF F3) keys) (sqGroups Fσ) gs

/-- The certificate `(a₀, gs)` handles every case of `λ` with `σlo ≤ σ < σhi`: `a₀ ≡ qλ` modulo
squares and `gs` handles the groups of `sqGroups`. -/
def lamOK (t4 : Bool) (p q D slo shi : ℕ) (Ps : List ℕ) (keys : KTree) (lam : ℕ)
    (c : ℕ × List GCert) : Bool :=
  lamOKWith t4 p q D slo shi keys lam c.1 (p / Nat.gcd p lam) (lam / Nat.gcd p lam)
    (facOf Ps (p / Nat.gcd p lam)) (facOf Ps (lam / Nat.gcd p lam))
    (facOf Ps ((lam / Nat.gcd p lam) ^ 2 * D)) c.2

/-- The grouped certificate for the `λ ∣ pq` with `lo ≤ λ < hi` and the `σlo ≤ σ < σhi`. -/
def classCert (t4 : Bool) (p q D lo hi slo shi : ℕ) (Ps : List ℕ) (keys : KTree)
    (cert : List (ℕ × List GCert)) : Bool :=
  prodF (facOf Ps (p * q)) == p * q &&
    allZip (lamOK t4 p q D slo shi Ps keys)
      ((divsF (facOf Ps (p * q))).filter fun lam ↦ decide (lo ≤ lam) && decide (lam < hi)) cert

/-- Every case with `lo ≤ λ < hi` and `σlo ≤ σ < σhi` is handled (`CaseOKT t4`; by default
`t4 = false`, without family TR). -/
def CasesOn (p q D lo hi slo shi : ℕ) (t4 : Bool := false) : Prop :=
  ∀ ⦃lam c1 c2 c3 c4 σ : ℕ⦄, 0 < lam → lam ∣ p * q → lo ≤ lam → lam < hi → slo ≤ σ → σ < shi →
    c1 * c2 = p / Nat.gcd p lam → Nat.Coprime c1 c2 → c3 * c4 = lam / Nat.gcd p lam →
    Nat.Coprime c3 c4 → σ ∣ (lam / Nat.gcd p lam) ^ 2 * D → CaseOKT t4 p q D lam c1 c2 c3 c4 σ

theorem CasesOn.trans {p q D lo mid hi slo shi : ℕ} {t4 : Bool}
    (h1 : CasesOn p q D lo mid slo shi t4) (h2 : CasesOn p q D mid hi slo shi t4) :
    CasesOn p q D lo hi slo shi t4 := by
  intro lam c1 c2 c3 c4 σ h0 hd hlo hhi
  rcases lt_or_ge lam mid with h | h
  · exact h1 h0 hd hlo h
  · exact h2 h0 hd h hhi

theorem CasesOn.transσ {p q D lo hi slo smid shi : ℕ} {t4 : Bool}
    (h1 : CasesOn p q D lo hi slo smid t4) (h2 : CasesOn p q D lo hi smid shi t4) :
    CasesOn p q D lo hi slo shi t4 := by
  intro lam c1 c2 c3 c4 σ h0 hd hlo hhi hslo hshi
  rcases lt_or_ge σ smid with h | h
  · exact h1 h0 hd hlo hhi hslo h
  · exact h2 h0 hd hlo hhi h hshi

/-- The range `σ < (pq)² D + 1` holds for every case, since `σ ∣ λ'² D` and `λ' ≤ pq`. -/
theorem CasesOn.casesOKT {p q D : ℕ} {t4 : Bool}
    (h : CasesOn p q D 0 (p * q + 1) 0 ((p * q) ^ 2 * D + 1) t4)
    (hp : 0 < p) (hq : 0 < q) (hD : 0 < D) : CasesOKT t4 p q D := by
  intro lam c1 c2 c3 c4 σ h0 hd hc12 hc12' hc34 hc34' hσd
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have hl' : 0 < lam / Nat.gcd p lam :=
    Nat.div_pos (Nat.gcd_le_right _ h0) (Nat.gcd_pos_of_pos_left _ hp)
  have hl : lam / Nat.gcd p lam ≤ p * q := (Nat.div_le_self _ _).trans (Nat.le_of_dvd hpq hd)
  refine h h0 hd (Nat.zero_le _) (Nat.lt_succ_of_le (Nat.le_of_dvd hpq hd)) (Nat.zero_le _)
    (Nat.lt_succ_of_le ((Nat.le_of_dvd (Nat.mul_pos (pow_pos hl' 2) hD) hσd).trans ?_)) hc12
    hc12' hc34 hc34' hσd
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hl 2)

/-- `CasesOn.casesOKT` without family TR. -/
theorem CasesOn.casesOK {p q D : ℕ} (h : CasesOn p q D 0 (p * q + 1) 0 ((p * q) ^ 2 * D + 1))
    (hp : 0 < p) (hq : 0 < q) (hD : 0 < D) : CasesOK p q D := by
  intro lam c1 c2 c3 c4 σ h0 hd hc12 hc12' hc34 hc34' hσd
  rcases h.casesOKT hp hq hD h0 hd hc12 hc12' hc34 hc34' hσd with h | ⟨h, -⟩
  · exact h
  · exact absurd h Bool.false_ne_true

theorem isSq_mul_sq {n : ℕ} (h : isSq n = true) (t : ℕ) : isSq (n * t ^ 2) = true := by
  have hn := eq_sq_of_isSq h
  rw [isSq, beq_iff_eq, show n * t ^ 2 = (Nat.sqrt n * t) ^ 2 by rw [hn, Nat.sqrt_eq']; ring,
    Nat.sqrt_eq', sq]

/-- A killed group: every `σ = σ₀ t²` of the group has a class outside the Selmer group. -/
theorem classKill_of_killOK {p q D lam a0 s0 j b0 : ℕ} {keys : KTree}
    (hkeys : keys.all (keyOK p q) = true) (ha0 : 0 < a0) (hA : isSq (q * lam * a0) = true)
    (h : killOK keys D lam a0 s0 j b0 = true) (t : ℕ) : ClassKill p q D lam (s0 * t ^ 2) := by
  unfold killOK at h
  split at h
  · rename_i N l k A B hk
    have hK := KTree.all_get hkeys hk
    simp only [keyOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hK
    obtain ⟨⟨⟨hl, hk0⟩, hN⟩, hc⟩ := hK
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨hb0, hB⟩, rfl⟩, rfl⟩ := h
    refine ⟨a0, b0, N, l, k, prime_of_primeB hl, hN, hk0, ?_⟩
    simp only [classKillOK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨ha0, hb0⟩, hA⟩, ?_⟩, ?_⟩
    · rw [show D * lam * (s0 * t ^ 2) * b0 = D * lam * s0 * b0 * t ^ 2 by ring]
      exact isSq_mul_sq hB t
    · rw [Nat.mul_mod a0 b0 N, Bool.or_eq_true]
      split at hc
      · exact Or.inl hc
      · exact Or.inr hc
  · simp at h

/-- **Soundness of the grouped certificate.** -/
theorem casesOn_of_classCert {t4 : Bool} {p q D lo hi slo shi : ℕ} {Ps : List ℕ} {keys : KTree}
    {cert : List (ℕ × List GCert)} (hp : 0 < p) (hPs : ∀ l ∈ Ps, l.Prime)
    (hkeys : keys.all (keyOK p q) = true)
    (h : classCert t4 p q D lo hi slo shi Ps keys cert = true) :
    CasesOn p q D lo hi slo shi t4 := by
  simp only [classCert, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hpq, h⟩ := h
  intro lam c1 c2 c3 c4 σ hlam hlpq hlo hhi hslo hshi hc12 hc12' hc34 hc34' hσd
  have hmem : lam ∈ (divsF (facOf Ps (p * q))).filter
      fun lam ↦ decide (lo ≤ lam) && decide (lam < hi) :=
    List.mem_filter.mpr ⟨mem_divsF (primes_facOf hPs _)
      (show lam ∣ prodF _ by rw [hpq]; exact hlpq), by simp [hlo, hhi]⟩
  obtain ⟨⟨a0, gs⟩, hc⟩ := allZip_sound h lam hmem
  simp only [lamOK, lamOKWith, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨ha0, hA⟩, hF1⟩, hF3⟩, hFσ⟩, hgs⟩ := hc
  set g := Nat.gcd p lam
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hp
  have hp' : 0 < p / g := Nat.div_pos (Nat.gcd_le_left _ hp) hg
  have hl' : 0 < lam / g := Nat.div_pos (Nat.gcd_le_right _ hlam) hg
  obtain ⟨G, hG, t, ht, rfl⟩ :=
    exists_sqGroups (primes_facOf hPs _) (show σ ∣ prodF _ by rw [hFσ]; exact hσd)
  obtain ⟨gc, hgc⟩ := allZip_sound hgs G hG
  cases gc with
  | kill j b0 => exact Or.inl (Or.inr (Or.inr (classKill_of_killOK hkeys ha0 hA hgc t)))
  | cases cs =>
    have hc1 : 0 < c1 := Nat.pos_of_mul_pos_right (hc12 ▸ hp')
    have hc3 : 0 < c3 := Nat.pos_of_mul_pos_right (hc34 ▸ hl')
    have e2 : p / g / c1 = c2 := by rw [← hc12, Nat.mul_div_cancel_left _ hc1]
    have e4 : lam / g / c3 = c4 := by rw [← hc34, Nat.mul_div_cancel_left _ hc3]
    have hx : (c1, c2, c3, c4, G.1 * t ^ 2) ∈
        groupCases slo shi (p / g) (lam / g) G.1 G.2 (divsF (facOf Ps (p / g)))
          (divsF (facOf Ps (lam / g))) := by
      simp only [groupCases, List.mem_flatMap]
      refine ⟨t, List.mem_filter.mpr ⟨ht, by simp [hslo, hshi]⟩, c1,
        mem_divsF (primes_facOf hPs _) (show c1 ∣ prodF _ by
        rw [hF1]; exact ⟨c2, hc12.symm⟩), ?_⟩
      rw [e2, hc12'.gcd_eq_one]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap]
      refine ⟨c3, mem_divsF (primes_facOf hPs _) (show c3 ∣ prodF _ by
        rw [hF3]; exact ⟨c4, hc34.symm⟩), ?_⟩
      rw [e4, hc34'.gcd_eq_one]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
    rw [groupOK] at hgc
    obtain ⟨c, hc⟩ := allZip_sound hgc _ hx
    exact tStep_sound (t4 := t4) (p := p) (q := q) (D := D) (lam := lam)
      (x := (c1, c2, c3, c4, G.1 * t ^ 2)) hc

end Descent

end PerfectCuboid
