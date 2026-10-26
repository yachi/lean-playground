module

public import Mathlib.Data.Int.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination

/-!
# A residue checker for the descent cases

The generic descent of `LeanPlayground.PerfectCuboid.Descent` splits into a few hundred cases.
In each case four pairwise coprime integers `α, β, γ, δ` would satisfy

  `A₁ γ² − B₁ β² = s₁ δ²`,   `A₂ β² − B₂ γ² = s₂ α²`

for explicit natural numbers `A₁, B₁, s₁, A₂, B₂, s₂`, together with coprimality conditions
`c₁ ⊥ γ, δ`, `c₂ ⊥ α, β`, `c₃ ⊥ β, δ` and `c₄ ⊥ α, γ`. Almost all of these cases are impossible
modulo a small number `N`. This file contains a `Bool` function `check` that tests every residue
class modulo `N`, and the theorem `check_sound` that turns a successful run into a proof.

The function is run by the kernel (`decide +kernel`). To keep it fast, the possible values of
`s d² mod N` are stored as the bits of a natural number (`sqMask`), every value that is used
repeatedly is evaluated once (`withNat`), the loops are `Nat.rec` (`allBelow`), and `β, γ` only
run up to `N / 2`, so the work is about `N² / 4` steps.

The cases that are not impossible are the images of torsion points. They are recognized by
`torsionOK`, which tests the hypotheses of the three torsion families of
`LeanPlayground.PerfectCuboid.Descent` (`linOK`, `quadDOK`, `quadKOK`) together with a size bound
(`boundOK`, or for `quadKOK` the finite search `smallCheck` over the box
`quadKBoxβ × quadKBoxγ`). The whole case list of one pair `(p, q)` is `fiberCheck`;
`fiberCheckOn` checks only the `λ` in a range, so that a large fiber can be split into several
kernel runs.

`fiberCheck` tries every modulus on every case. It is much cheaper to replay a certificate
(`fiberCheckCert`) that names the one test that handles each case of `fiberCases`: `.torsion` or
a single modulus `.modulus N l`. `fiberCases` also lists the divisors `σ` of `λ'² a²` without
trial division up to `λ' a` (`divsMul`, `divsSq`), and a certificate can be split into pieces by
`caseKey`, the position of `(λ, c₁, c₃)`, and further by a range of `σ`, so that each kernel
run stays small. Either way the
result is `Covered p q a`, the hypothesis of the descent (`covered_of_fiberCheck`,
`coveredOn_of_fiberCheckCert`).
-/

@[expose] public section

namespace PerfectCuboid

namespace Descent

/-- `-x mod N` as a natural number. -/
def negMod (N x : ℕ) : ℕ := (N - x % N) % N

/-- The bit mask of the residues `s d² mod N` over `d < N`, restricted to `l ∣ d` (if `z`) or to
`l ∤ d` (if `!z`). -/
def sqMask (N l s : ℕ) (z : Bool) : ℕ :=
  (List.range N).foldl
    (fun m d ↦ if (d % l == 0) == z then m ||| 1 <<< (s * d * d % N) else m) 0

/-- The coprimality conditions on the flags `az = (l ∣ α)`, …, `c₁z = (l ∣ c₁)`, …. -/
def okB (az bz gz dz c1z c2z c3z c4z : Bool) : Bool :=
  !(az && bz) && !(az && gz) && !(az && dz) && !(bz && gz) && !(bz && dz) && !(gz && dz) &&
    (!c1z || (!gz && !dz)) && (!c2z || (!az && !bz)) && (!c3z || (!bz && !dz)) &&
    (!c4z || (!az && !gz))

/-- `f n`. The kernel reduces the `match` by evaluating `n` to a numeral first, so `f` receives
a numeral instead of the expression `n`, which it would otherwise evaluate at every use. -/
def withNat (n : ℕ) (f : ℕ → Bool) : Bool :=
  match n with
  | 0 => f 0
  | k + 1 => f (k + 1)

theorem withNat_eq (n : ℕ) (f : ℕ → Bool) : withNat n f = f n := by
  cases n <;> rfl

/-- `f k` for all `k < n`. The kernel evaluates this `Nat.rec` much faster than `List.all` over
`List.range n`. -/
def allBelow (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec true (fun k acc ↦ f k && acc) n

theorem allBelow_iff {n : ℕ} {f : ℕ → Bool} : allBelow n f = true ↔ ∀ k < n, f k = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    change (f n && allBelow n f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      exacts [h2 k hk, h1]
    · exact fun h ↦ ⟨h n n.lt_succ_self, fun k hk ↦ h k (hk.trans n.lt_succ_self)⟩

/-- `f true && f false`. -/
def allBool (f : Bool → Bool) : Bool := f true && f false

theorem allBool_iff {f : Bool → Bool} : allBool f = true ↔ ∀ z, f z = true := by
  rw [allBool, Bool.and_eq_true]
  exact ⟨fun h z ↦ by cases z; exacts [h.2, h.1], fun h ↦ ⟨h true, h false⟩⟩

/-- `true` if no residues `α, β, γ, δ` modulo `N` satisfy both equations modulo `N` and the
coprimality conditions modulo `l`. The coefficients are expected to be reduced modulo `N`, and
`B₁, B₂` to be negated already. Since `β, γ` only enter through `β², γ²` and `l ∣ β, l ∣ γ`, it
suffices to take `β, γ ≤ N / 2` (`exists_half`). The arguments, the four masks and the two
residues for each `(β, γ)` are evaluated once (`withNat`), so the work is `O(N²)`. -/
def check (N l A1 B1 s1 A2 B2 s2 c1 c2 c3 c4 : ℕ) : Bool :=
  withNat N fun N ↦ withNat l fun l ↦ withNat A1 fun A1 ↦ withNat B1 fun B1 ↦
  withNat s1 fun s1 ↦ withNat A2 fun A2 ↦ withNat B2 fun B2 ↦ withNat s2 fun s2 ↦
  withNat c1 fun c1 ↦ withNat c2 fun c2 ↦ withNat c3 fun c3 ↦ withNat c4 fun c4 ↦
  withNat (sqMask N l s1 true) fun m1t ↦ withNat (sqMask N l s1 false) fun m1f ↦
  withNat (sqMask N l s2 true) fun m2t ↦ withNat (sqMask N l s2 false) fun m2f ↦
  allBelow (N / 2 + 1) fun b ↦ withNat (b * b % N) fun bb ↦
  allBelow (N / 2 + 1) fun g ↦ withNat (g * g % N) fun gg ↦
    withNat ((A1 * gg + B1 * bb) % N) fun r1 ↦ withNat ((A2 * bb + B2 * gg) % N) fun r2 ↦
    allBool fun az ↦ allBool fun dz ↦
      !((bif dz then m1t else m1f).testBit r1 && (bif az then m2t else m2f).testBit r2 &&
        okB az (b % l == 0) (g % l == 0) dz (c1 % l == 0) (c2 % l == 0) (c3 % l == 0)
          (c4 % l == 0))

/-! ### Soundness -/

theorem testBit_foldl (N l s : ℕ) (z : Bool) (X : ℕ) :
    ∀ (L : List ℕ) (m : ℕ), (L.foldl
      (fun m d ↦ if (d % l == 0) == z then m ||| 1 <<< (s * d * d % N) else m) m).testBit X =
      (m.testBit X || L.any fun d ↦ (d % l == 0) == z && s * d * d % N == X) := by
  intro L
  induction L with
  | nil => intro m; simp
  | cons d L ih =>
    intro m
    rw [List.foldl_cons, ih, List.any_cons]
    split_ifs with h
    · rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hx : s * d * d % N = X <;> cases m.testBit X <;> simp [h, hx]
    · simp [h]

theorem testBit_sqMask {N l s : ℕ} {z : Bool} {d : ℕ} (hd : d < N) (hz : (d % l == 0) = z) :
    (sqMask N l s z).testBit (s * d * d % N) = true := by
  rw [sqMask, testBit_foldl]
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  exact Or.inr ⟨d, hd, by rw [hz], rfl⟩

theorem cond_sqMask (N l s : ℕ) (z : Bool) :
    (bif z then sqMask N l s true else sqMask N l s false) = sqMask N l s z := by
  cases z <;> rfl

theorem okB_spec : ∀ az bz gz dz c1z c2z c3z c4z : Bool,
    (az && bz) = false → (az && gz) = false → (az && dz) = false → (bz && gz) = false →
    (bz && dz) = false → (gz && dz) = false → (c1z && gz) = false → (c1z && dz) = false →
    (c2z && az) = false → (c2z && bz) = false → (c3z && bz) = false → (c3z && dz) = false →
    (c4z && az) = false → (c4z && gz) = false → okB az bz gz dz c1z c2z c3z c4z = true := by
  decide

/-- Two coprime integers are not both divisible by `l ≥ 2`. -/
theorem not_dvd_and_dvd {x y : ℤ} (h : IsCoprime x y) {l : ℕ} (hl : 2 ≤ l) :
    ¬ ((l : ℤ) ∣ x ∧ (l : ℤ) ∣ y) := by
  rintro ⟨hx, hy⟩
  have := h.isUnit_of_dvd' hx hy
  rw [Int.isUnit_iff] at this
  omega

/-- The residue of an integer modulo `N`, as a natural number. -/
def res (N : ℕ) (x : ℤ) : ℕ := (x % N).toNat

theorem res_lt {N : ℕ} (hN : 0 < N) (x : ℤ) : res N x < N := by
  have h1 := Int.emod_nonneg x (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos x (by exact_mod_cast hN : (0 : ℤ) < N)
  rw [res]
  omega

theorem natCast_res {N : ℕ} (hN : 0 < N) (x : ℤ) : (res N x : ℤ) = x % N :=
  Int.toNat_of_nonneg (Int.emod_nonneg x (by exact_mod_cast hN.ne'))

theorem zmod_res {N : ℕ} (hN : 0 < N) (x : ℤ) : ((res N x : ℕ) : ZMod N) = (x : ZMod N) := by
  rw [← Int.cast_natCast, natCast_res hN, ZMod.intCast_mod]

theorem res_mod_eq_zero_iff {N l : ℕ} (hN : 0 < N) (hlN : l ∣ N) (x : ℤ) :
    (res N x % l == 0) = decide ((l : ℤ) ∣ x) := by
  have key : ((res N x % l : ℕ) : ℤ) = x % l := by
    rw [Int.natCast_mod, natCast_res hN, Int.emod_emod_of_dvd x (by exact_mod_cast hlN)]
  rw [Bool.beq_eq_decide_eq]
  exact decide_eq_decide.mpr (by rw [Int.dvd_iff_emod_eq_zero, ← key]; omega)

theorem natCast_mod_dvd {l c : ℕ} : (c % l == 0) = decide ((l : ℤ) ∣ (c : ℤ)) := by
  simp only [Int.natCast_dvd_natCast]
  exact decide_eq_decide.mpr Nat.dvd_iff_mod_eq_zero.symm

theorem and_false_of_coprime {x y : ℤ} (h : IsCoprime x y) {l : ℕ} (hl : 2 ≤ l) :
    (decide ((l : ℤ) ∣ x) && decide ((l : ℤ) ∣ y)) = false := by
  have := not_dvd_and_dvd h hl
  by_cases hx : (l : ℤ) ∣ x <;> by_cases hy : (l : ℤ) ∣ y <;> simp_all

theorem zmod_negMod {N : ℕ} (hN : 0 < N) (x : ℕ) :
    ((negMod N x : ℕ) : ZMod N) = -(x : ZMod N) := by
  rw [negMod, ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt x hN).le, ZMod.natCast_self,
    ZMod.natCast_mod, zero_sub]

theorem mask_of_eq {N l A B s : ℕ} (hN : 0 < N) (hlN : l ∣ N) {x y w : ℤ}
    (E : (A : ℤ) * x ^ 2 - B * y ^ 2 = s * w ^ 2) :
    (sqMask N l (s % N) (decide ((l : ℤ) ∣ w))).testBit
      ((A % N * res N x * res N x + negMod N B * res N y * res N y) % N) = true := by
  have key := testBit_sqMask (N := N) (l := l) (s := s % N) (res_lt hN w)
    (res_mod_eq_zero_iff hN hlN w)
  convert key using 2
  rw [← ZMod.natCast_eq_natCast_iff']
  have E' := congrArg (Int.cast : ℤ → ZMod N) E
  push_cast [zmod_res hN, zmod_negMod hN, ZMod.natCast_mod] at E' ⊢
  linear_combination E'

theorem flag_false {x y : ℤ} (h : IsCoprime x y) {l : ℕ} (hl : 2 ≤ l) :
    (decide ((l : ℤ) ∣ x) && decide ((l : ℤ) ∣ y)) = false :=
  and_false_of_coprime h hl

/-- A residue `x` and `N − x` have the same square and the same divisibility by `l ∣ N`, and one
of them is at most `N / 2`. -/
theorem exists_half {N l x : ℕ} (hlN : l ∣ N) (hx : x < N) :
    ∃ y < N / 2 + 1, y * y % N = x * x % N ∧ (y % l == 0) = (x % l == 0) := by
  by_cases h : 2 * x ≤ N
  · exact ⟨x, by omega, rfl, rfl⟩
  refine ⟨N - x, by omega, ?_, ?_⟩
  · rw [← ZMod.natCast_eq_natCast_iff']
    push_cast [Nat.cast_sub hx.le, ZMod.natCast_self]
    ring
  · have key : l ∣ N - x ↔ l ∣ x :=
      ⟨fun h ↦ Nat.sub_sub_self hx.le ▸ Nat.dvd_sub hlN h, fun h ↦ Nat.dvd_sub hlN h⟩
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← Nat.dvd_iff_mod_eq_zero,
      ← Nat.dvd_iff_mod_eq_zero, key]

theorem mod_sq_comb (N a b x y : ℕ) :
    (a * (x * x % N) + b * (y * y % N)) % N = (a * x * x + b * y * y) % N := by
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast [ZMod.natCast_mod]
  ring

/-- **Soundness of the residue check.** -/
theorem check_sound {N l : ℕ} (hN : 0 < N) (hl : 2 ≤ l) (hlN : l ∣ N)
    {A1 B1 s1 A2 B2 s2 c1 c2 c3 c4 : ℕ}
    (h : check N l (A1 % N) (negMod N B1) (s1 % N) (A2 % N) (negMod N B2) (s2 % N) c1 c2 c3 c4 =
      true)
    {α β γ δ : ℤ} (hab : IsCoprime α β) (hag : IsCoprime α γ) (had : IsCoprime α δ)
    (hbg : IsCoprime β γ) (hbd : IsCoprime β δ) (hgd : IsCoprime γ δ)
    (h1g : IsCoprime (c1 : ℤ) γ) (h1d : IsCoprime (c1 : ℤ) δ) (h2a : IsCoprime (c2 : ℤ) α)
    (h2b : IsCoprime (c2 : ℤ) β) (h3b : IsCoprime (c3 : ℤ) β) (h3d : IsCoprime (c3 : ℤ) δ)
    (h4a : IsCoprime (c4 : ℤ) α) (h4g : IsCoprime (c4 : ℤ) γ)
    (E1 : (A1 : ℤ) * γ ^ 2 - B1 * β ^ 2 = s1 * δ ^ 2)
    (E2 : (A2 : ℤ) * β ^ 2 - B2 * γ ^ 2 = s2 * α ^ 2) : False := by
  simp only [check, withNat_eq, cond_sqMask, allBelow_iff, allBool_iff] at h
  obtain ⟨b, hb, hbb, hbl⟩ := exists_half hlN (res_lt hN β)
  obtain ⟨g, hg, hgg, hgl⟩ := exists_half hlN (res_lt hN γ)
  have H := h b hb g hg (decide ((l : ℤ) ∣ α)) (decide ((l : ℤ) ∣ δ))
  rw [hbb, hgg, hbl, hgl, mod_sq_comb, mod_sq_comb] at H
  have hok := okB_spec _ _ _ _ _ _ _ _ (flag_false hab hl) (flag_false hag hl) (flag_false had hl)
    (flag_false hbg hl) (flag_false hbd hl) (flag_false hgd hl) (flag_false h1g hl)
    (flag_false h1d hl) (flag_false h2a hl) (flag_false h2b hl) (flag_false h3b hl)
    (flag_false h3d hl) (flag_false h4a hl) (flag_false h4g hl)
  rw [mask_of_eq hN hlN E1, mask_of_eq hN hlN E2, res_mod_eq_zero_iff hN hlN,
    res_mod_eq_zero_iff hN hlN, natCast_mod_dvd, natCast_mod_dvd, natCast_mod_dvd,
    natCast_mod_dvd, hok] at H
  simp at H

/-! ### The case list of one fiber -/

/-- The divisors of `n`, found by trial division up to `√n`. -/
def divs (n : ℕ) : List ℕ :=
  (List.range (Nat.sqrt n + 1)).flatMap fun d ↦
    if d != 0 && n % d == 0 then (if d * d == n then [d] else [d, n / d]) else []

theorem mem_divs {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) : d ∈ divs n := by
  obtain ⟨e, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_mul_pos_right hn
  have he0 : 0 < e := Nat.pos_of_mul_pos_left hn
  simp only [divs, List.mem_flatMap, List.mem_range]
  rcases le_or_gt d (Nat.sqrt (d * e)) with h | h
  · refine ⟨d, by omega, ?_⟩
    have hc : (d != 0 && d * e % d == 0) = true := by simp [hd0.ne', Nat.mul_mod_right]
    simp only [hc, ↓reduceIte]
    split_ifs <;> simp
  · refine ⟨e, ?_, ?_⟩
    · by_contra h'
      have h1 : d * e < (Nat.sqrt (d * e) + 1) * (Nat.sqrt (d * e) + 1) := Nat.lt_succ_sqrt _
      have : (Nat.sqrt (d * e) + 1) * (Nat.sqrt (d * e) + 1) ≤ d * e :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    · have hc : (e != 0 && d * e % e == 0) = true := by simp [he0.ne', Nat.mul_mod_left]
      simp only [hc, ↓reduceIte]
      split_ifs with h2
      · rw [beq_iff_eq] at h2
        simp [Nat.eq_of_mul_eq_mul_right he0 h2.symm]
      · simp [Nat.mul_div_cancel _ he0]

/-- The divisors of `x y`: products of divisors of `x` and of `y` if they are coprime. -/
def divsMul (x y : ℕ) : List ℕ :=
  if Nat.gcd x y == 1 then (divs x).flatMap fun u ↦ (divs y).map (u * ·) else divs (x * y)

theorem mem_divsMul {x y d : ℕ} (hx : 0 < x) (hy : 0 < y) (hd : d ∣ x * y) : d ∈ divsMul x y := by
  rw [divsMul]
  split_ifs with h
  · have hc : Nat.Coprime x y := by simpa using h
    simp only [List.mem_flatMap, List.mem_map]
    refine ⟨Nat.gcd d x, mem_divs hx (Nat.gcd_dvd_right _ _), Nat.gcd d y,
      mem_divs hy (Nat.gcd_dvd_right _ _), ?_⟩
    rw [← Nat.Coprime.gcd_mul d hc, Nat.gcd_eq_left hd]
  · exact mem_divs (Nat.mul_pos hx hy) hd

/-- The divisors of `m²`, given the list `D` of the divisors of `m`: each one is `u v` with
`u = gcd(u v, m)` and `u, v ∣ m`, in exactly one way. -/
def divsSq (D : List ℕ) (m : ℕ) : List ℕ :=
  D.flatMap fun u ↦ (D.filter fun v ↦ Nat.gcd (u * v) m == u).map (u * ·)

theorem mem_divsSq {D : List ℕ} {m σ : ℕ} (hm : 0 < m) (hD : ∀ d, d ∣ m → d ∈ D)
    (hσ : σ ∣ m * m) : σ ∈ divsSq D m := by
  have hσ0 : 0 < σ := Nat.pos_of_dvd_of_pos hσ (Nat.mul_pos hm hm)
  set u := Nat.gcd σ m with hu
  have hu0 : 0 < u := Nat.gcd_pos_of_pos_left _ hσ0
  obtain ⟨v, hv⟩ : u ∣ σ := Nat.gcd_dvd_left _ _
  obtain ⟨w, hw⟩ : u ∣ m := Nat.gcd_dvd_right _ _
  have hvw : Nat.Coprime v w := by
    have := Nat.coprime_div_gcd_div_gcd (m := σ) (n := m) hu0
    rwa [← hu, hv, hw, Nat.mul_div_cancel_left _ hu0, Nat.mul_div_cancel_left _ hu0] at this
  have hvm : v ∣ m := by
    have h1 : u * v ∣ u * (w * m) := by
      rw [← hv, ← mul_assoc, ← hw]
      exact hσ
    exact hvw.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hu0 h1)
  simp only [divsSq, List.mem_flatMap, List.mem_map, List.mem_filter, beq_iff_eq]
  exact ⟨u, hD _ (Nat.gcd_dvd_right _ _), v, ⟨hD _ hvm, by rw [← hv]⟩, hv.symm⟩

/-- The first equation `q c₃² γ² − λ c₁² β² = σ δ²` divided by the gcd of its coefficients, and
likewise the second, are checked modulo each `(N, l)` in `mods` until one succeeds. -/
def tupleOK (mods : List (ℕ × ℕ)) (q lam c1 c2 c3 c4 σ : ℕ) : Bool :=
  let A1 := q * c3 ^ 2
  let B1 := lam * c1 ^ 2
  let g1 := Nat.gcd (Nat.gcd A1 B1) σ
  let A2 := q * c4 ^ 2
  let B2 := lam * c2 ^ 2
  let g2 := Nat.gcd (Nat.gcd A2 B2) σ
  mods.any fun x ↦
    check x.1 x.2 (A1 / g1 % x.1) (negMod x.1 (B1 / g1)) (σ / g1 % x.1) (A2 / g2 % x.1)
      (negMod x.1 (B2 / g2)) (σ / g2 % x.1) c1 c2 c3 c4

theorem div_gcd_eq {A B σ : ℕ} (hσ : 0 < σ) {x y w : ℤ}
    (E : (A : ℤ) * x ^ 2 - B * y ^ 2 = σ * w ^ 2) :
    ((A / Nat.gcd (Nat.gcd A B) σ : ℕ) : ℤ) * x ^ 2 -
        ((B / Nat.gcd (Nat.gcd A B) σ : ℕ) : ℤ) * y ^ 2
      = ((σ / Nat.gcd (Nat.gcd A B) σ : ℕ) : ℤ) * w ^ 2 := by
  set g := Nat.gcd (Nat.gcd A B) σ
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hσ
  have hA : g ∣ A := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hB : g ∣ B := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hS : g ∣ σ := Nat.gcd_dvd_right _ _
  refine mul_left_cancel₀ (by exact_mod_cast hg.ne' : (g : ℤ) ≠ 0) ?_
  have e1 : ((A / g : ℕ) : ℤ) * g = A := by exact_mod_cast Nat.div_mul_cancel hA
  have e2 : ((B / g : ℕ) : ℤ) * g = B := by exact_mod_cast Nat.div_mul_cancel hB
  have e3 : ((σ / g : ℕ) : ℤ) * g = σ := by exact_mod_cast Nat.div_mul_cancel hS
  linear_combination E + x ^ 2 * e1 - y ^ 2 * e2 - w ^ 2 * e3

theorem tupleOK_sound {mods : List (ℕ × ℕ)} (hmods : ∀ x ∈ mods, 0 < x.1 ∧ 2 ≤ x.2 ∧ x.2 ∣ x.1)
    {q lam c1 c2 c3 c4 σ : ℕ} (h : tupleOK mods q lam c1 c2 c3 c4 σ = true) (hσ : 0 < σ)
    {α β γ δ : ℤ} (hab : IsCoprime α β) (hag : IsCoprime α γ) (had : IsCoprime α δ)
    (hbg : IsCoprime β γ) (hbd : IsCoprime β δ) (hgd : IsCoprime γ δ)
    (h1g : IsCoprime (c1 : ℤ) γ) (h1d : IsCoprime (c1 : ℤ) δ) (h2a : IsCoprime (c2 : ℤ) α)
    (h2b : IsCoprime (c2 : ℤ) β) (h3b : IsCoprime (c3 : ℤ) β) (h3d : IsCoprime (c3 : ℤ) δ)
    (h4a : IsCoprime (c4 : ℤ) α) (h4g : IsCoprime (c4 : ℤ) γ)
    (E1 : (q : ℤ) * c3 ^ 2 * γ ^ 2 - lam * c1 ^ 2 * β ^ 2 = σ * δ ^ 2)
    (E2 : (q : ℤ) * c4 ^ 2 * β ^ 2 - lam * c2 ^ 2 * γ ^ 2 = σ * α ^ 2) : False := by
  obtain ⟨⟨N, l⟩, hm, hc⟩ := List.any_eq_true.mp h
  obtain ⟨hN, hl, hlN⟩ := hmods _ hm
  have E1' := div_gcd_eq (A := q * c3 ^ 2) (B := lam * c1 ^ 2) (x := γ) (y := β) (w := δ) hσ
    (by push_cast; linear_combination E1)
  have E2' := div_gcd_eq (A := q * c4 ^ 2) (B := lam * c2 ^ 2) (x := β) (y := γ) (w := α) hσ
    (by push_cast; linear_combination E2)
  exact check_sound hN hl hlN hc hab hag had hbg hbd hgd h1g h1d h2a h2b h3b h3d h4a h4g E1' E2'

/-- `n` is a perfect square. -/
def isSq (n : ℕ) : Bool := Nat.sqrt n * Nat.sqrt n == n

theorem eq_sq_of_isSq {n : ℕ} (h : isSq n = true) : n = Nat.sqrt n ^ 2 := by
  rw [isSq, beq_iff_eq] at h
  rw [sq, h]

/-! ### The cases that give a smaller solution

A tuple `(λ, c₁, c₂, c₃, c₄, σ)` that comes from a rational point is the image of a torsion point
under the `2`-descent map. Since `λ, σ > 0`, only two classes occur (see
`LeanPlayground.PerfectCuboid.Descent`):

* the trivial class, `qλ` and `λσ` squares: family L (`linOK`), a linear formula;
* the class of a `4`-torsion point, `c₁c₂`, `c₃c₄` and `σ (q − p)` squares: family Q, with the two
  representations QD (`quadDOK`) and QK (`quadKOK`) of the same new solution.

Each family gives a new solution `e'` with `X e'² ≤ Y (αβγδ)²` (or `<`), and `boundOK` checks that
one of the three bounds of the descent then makes `|e'| < |e|`. -/

/-- `x ≤ y` if `weak`, else `x < y`. -/
def leB (weak : Bool) (x y : ℕ) : Bool := if weak then decide (x ≤ y) else decide (x < y)

/-- With `A = (αβγδ)²`, the descent knows `A ≤ e²`, `4 P² A ≤ p² e²` and `N² A ≤ q² e²`
(`P = c₁c₂`, `N = c₃c₄`). If the new solution has `X e'² < Y A` (`weak`) or `X e'² ≤ Y A`
(`!weak`), one of these tests makes `e'² < e²`. -/
def boundOK (weak : Bool) (p q P N X Y : ℕ) : Bool :=
  leB weak Y X || leB weak (Y * p ^ 2) (X * (4 * P ^ 2)) || leB weak (Y * q ^ 2) (X * N ^ 2)

/-- Family L, for `qλ = W²`, `λσ = h²` and `qσ = H²`: the new solution is `M' = u δ`, `e' = v α`
with `v = c₃ / gcd(c₃, c₂W)`, and `|βγδ| ≥ 2` unless `q c₃² = λ c₁² + σ`. -/
def linOK (p q lam c1 c2 c3 c4 σ : ℕ) : Bool :=
  isSq (q * lam) && isSq (lam * σ) && isSq (q * σ) &&
    boundOK false p q (c1 * c2) (c3 * c4) (if q * c3 ^ 2 == lam * c1 ^ 2 + σ then 1 else 4)
      ((c3 / Nat.gcd c3 (c2 * Nat.sqrt (q * lam))) ^ 2)

/-- `F` with all prime factors of `x` removed (given enough fuel). -/
def coprimePart : ℕ → ℕ → ℕ → ℕ
  | 0, F, _ => F
  | n + 1, F, x => if Nat.gcd F x == 1 then F else coprimePart n (F / Nat.gcd F x) x

/-- The divisor `F` of family QD: the part prime to `λ c₁` of the gcd of the coefficients. -/
def quadDF (p q lam c1 c2 c3 c4 σ : ℕ) : ℕ :=
  coprimePart 64 (Nat.gcd (Nat.gcd (Nat.sqrt (c1 * c2) * (q - p) * (c3 * c4))
    (Nat.sqrt (c1 * c2) * σ)) (Nat.gcd (Nat.sqrt (c3 * c4) * c4 * c3 ^ 2 * (q - p))
    (Nat.sqrt (c3 * c4) * c4 * σ))) (lam * c1)

/-- Family QD, for `c₁c₂ = w_d²`, `c₃c₄ = w_n²` and `σ (q − p) = h²`: the new solution is
`M' = w_d ((q − p) c₃c₄ βγ + σαδ) / F`, `e' = w_n (c₁c₄β² − c₂c₃γ²) / F`. -/
def quadDOK (p q lam c1 c2 c3 c4 σ : ℕ) : Bool :=
  isSq (c1 * c2) && isSq (c3 * c4) && isSq (σ * (q - p)) &&
    decide (0 < quadDF p q lam c1 c2 c3 c4 σ) &&
    (Nat.sqrt (c1 * c2) * (q - p) * (c3 * c4)) % quadDF p q lam c1 c2 c3 c4 σ == 0 &&
    (Nat.sqrt (c1 * c2) * σ) % quadDF p q lam c1 c2 c3 c4 σ == 0 &&
    (Nat.sqrt (c3 * c4) * c4 * c3 ^ 2 * (q - p)) % quadDF p q lam c1 c2 c3 c4 σ == 0 &&
    (Nat.sqrt (c3 * c4) * c4 * σ) % quadDF p q lam c1 c2 c3 c4 σ == 0 &&
    Nat.gcd (quadDF p q lam c1 c2 c3 c4 σ) (lam * c1) == 1 &&
    boundOK true p q (c1 * c2) (c3 * c4) (p * q * quadDF p q lam c1 c2 c3 c4 σ ^ 2)
      (c1 * c2 * (q - p) ^ 2 * (c3 * c4) ^ 2)

/-- The box of family QK. With `w_n = √(c₃c₄)` and `F = gcd(q, w_n)`, the new solution of QK is
smaller than the old one as soon as `F |γδ| > 2 w_n c₁` and `F |αβ| > 2 w_n c₂`. Otherwise
`|γδ| ≤ 2 w_n c₁ / F` or `|αβ| ≤ 2 w_n c₂ / F`, and the equations `E₁`, `E₂` bound `|β|` by
`quadKBoxβ` and `|γ|` by `quadKBoxγ`. -/
def quadKBoxβ (q lam c1 c2 c3 c4 : ℕ) : ℕ :=
  max (Nat.sqrt (q * c3 ^ 2 * (2 * Nat.sqrt (c3 * c4) * c1 / Nat.gcd q (Nat.sqrt (c3 * c4))) ^ 2 /
    (lam * c1 ^ 2))) (2 * Nat.sqrt (c3 * c4) * c2 / Nat.gcd q (Nat.sqrt (c3 * c4)))

/-- The bound on `|γ|` of the box of family QK, see `quadKBoxβ`. -/
def quadKBoxγ (q lam c1 c2 c3 c4 : ℕ) : ℕ :=
  max (2 * Nat.sqrt (c3 * c4) * c1 / Nat.gcd q (Nat.sqrt (c3 * c4)))
    (Nat.sqrt (q * c4 ^ 2 * (2 * Nat.sqrt (c3 * c4) * c2 / Nat.gcd q (Nat.sqrt (c3 * c4))) ^ 2 /
      (lam * c2 ^ 2)))

/-- `(|β|, |γ|) = (b, g)` extends to a solution `(α, β, γ, δ)` of `E₁`, `E₂` with `k₁² ≠ k₂²`:
`q c₃² g² − λ c₁² b² = σ δ²` and `q c₄² b² − λ c₂² g² = σ α²` with `α, δ ≠ 0` and
`c₁ |αβ| ≠ c₂ |γδ|`. -/
def smallBad (q lam c1 c2 c3 c4 σ b g : ℕ) : Bool :=
  decide (lam * c1 ^ 2 * b ^ 2 < q * c3 ^ 2 * g ^ 2) &&
  decide (lam * c2 ^ 2 * g ^ 2 < q * c4 ^ 2 * b ^ 2) &&
  (q * c3 ^ 2 * g ^ 2 - lam * c1 ^ 2 * b ^ 2) % σ == 0 &&
  (q * c4 ^ 2 * b ^ 2 - lam * c2 ^ 2 * g ^ 2) % σ == 0 &&
  isSq ((q * c3 ^ 2 * g ^ 2 - lam * c1 ^ 2 * b ^ 2) / σ) &&
  isSq ((q * c4 ^ 2 * b ^ 2 - lam * c2 ^ 2 * g ^ 2) / σ) &&
  c1 * Nat.sqrt ((q * c4 ^ 2 * b ^ 2 - lam * c2 ^ 2 * g ^ 2) / σ) * b !=
    c2 * g * Nat.sqrt ((q * c3 ^ 2 * g ^ 2 - lam * c1 ^ 2 * b ^ 2) / σ)

/-- No `(β, γ)` with `1 ≤ |β| ≤ B_β` and `1 ≤ |γ| ≤ B_γ` extends to a solution of `E₁`, `E₂`
with `k₁² ≠ k₂²`. -/
def smallCheck (q lam c1 c2 c3 c4 σ Bβ Bγ : ℕ) : Bool :=
  (List.range' 1 Bβ).all fun b ↦ (List.range' 1 Bγ).all fun g ↦ !smallBad q lam c1 c2 c3 c4 σ b g

/-- Family QK, for `c₁c₂ = w_d²`, `c₃c₄ = w_n²` and `σ (q − p) = h²`: with `F = gcd(q, w_n)`,
the new solution is `M' = (q/F) w_d (j₁ + j₂)`, `e' = (w_n/F)(k₁ − k₂)`. Either one of the three
bounds of `boundOK` makes it smaller, or `F² e'² ≤ 2 w_n² (k₁² + k₂²) < F² (αβγδ)²` as soon as
`F |γδ| > 2 w_n c₁` and `F |αβ| > 2 w_n c₂`; the remaining `(β, γ)` lie in a box that `smallCheck`
searches (at most `65536` pairs). -/
def quadKOK (p q lam c1 c2 c3 c4 σ : ℕ) : Bool :=
  isSq (c1 * c2) && isSq (c3 * c4) && isSq (σ * (q - p)) &&
    (boundOK true p q (c1 * c2) (c3 * c4) (Nat.gcd q (Nat.sqrt (c3 * c4)) ^ 2)
      (Nat.sqrt (c3 * c4) ^ 2 * (c1 * c2) ^ 2) ||
    (decide (quadKBoxβ q lam c1 c2 c3 c4 * quadKBoxγ q lam c1 c2 c3 c4 ≤ 65536) &&
      smallCheck q lam c1 c2 c3 c4 σ (quadKBoxβ q lam c1 c2 c3 c4) (quadKBoxγ q lam c1 c2 c3 c4)))

theorem isSq_sq (n : ℕ) : isSq (n ^ 2) = true := by
  simp [isSq, sq]

/-- **Soundness of `smallCheck`.** -/
theorem smallCheck_sound {q lam c1 c2 c3 c4 σ Bβ Bγ : ℕ}
    (h : smallCheck q lam c1 c2 c3 c4 σ Bβ Bγ = true) (hσ : 0 < σ) {α β γ δ : ℤ}
    (E1 : (q : ℤ) * c3 ^ 2 * γ ^ 2 - lam * c1 ^ 2 * β ^ 2 = σ * δ ^ 2)
    (E2 : (q : ℤ) * c4 ^ 2 * β ^ 2 - lam * c2 ^ 2 * γ ^ 2 = σ * α ^ 2)
    (hne : ((c1 : ℤ) * (α * β)) ^ 2 ≠ (c2 * (γ * δ)) ^ 2)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (hB : β.natAbs ≤ Bβ) (hG : γ.natAbs ≤ Bγ) : False := by
  simp only [smallCheck, List.all_eq_true, List.mem_range'_1, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  have hb := h β.natAbs ⟨Int.natAbs_pos.mpr hβ, by omega⟩ γ.natAbs
    ⟨Int.natAbs_pos.mpr hγ, by omega⟩
  have e1 : q * c3 ^ 2 * γ.natAbs ^ 2 = lam * c1 ^ 2 * β.natAbs ^ 2 + σ * δ.natAbs ^ 2 := by
    have : ((q * c3 ^ 2 * γ.natAbs ^ 2 : ℕ) : ℤ) =
        ((lam * c1 ^ 2 * β.natAbs ^ 2 + σ * δ.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      simp only [sq_abs]
      linear_combination E1
    exact_mod_cast this
  have e2 : q * c4 ^ 2 * β.natAbs ^ 2 = lam * c2 ^ 2 * γ.natAbs ^ 2 + σ * α.natAbs ^ 2 := by
    have : ((q * c4 ^ 2 * β.natAbs ^ 2 : ℕ) : ℤ) =
        ((lam * c2 ^ 2 * γ.natAbs ^ 2 + σ * α.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      simp only [sq_abs]
      linear_combination E2
    exact_mod_cast this
  have hd : 0 < σ * δ.natAbs ^ 2 := Nat.mul_pos hσ (pow_pos (Int.natAbs_pos.mpr hδ) 2)
  have ha : 0 < σ * α.natAbs ^ 2 := Nat.mul_pos hσ (pow_pos (Int.natAbs_pos.mpr hα) 2)
  have hD : q * c3 ^ 2 * γ.natAbs ^ 2 - lam * c1 ^ 2 * β.natAbs ^ 2 = σ * δ.natAbs ^ 2 := by
    omega
  have hA : q * c4 ^ 2 * β.natAbs ^ 2 - lam * c2 ^ 2 * γ.natAbs ^ 2 = σ * α.natAbs ^ 2 := by
    omega
  have hlt1 : lam * c1 ^ 2 * β.natAbs ^ 2 < q * c3 ^ 2 * γ.natAbs ^ 2 := by omega
  have hlt2 : lam * c2 ^ 2 * γ.natAbs ^ 2 < q * c4 ^ 2 * β.natAbs ^ 2 := by omega
  have hne' : c1 * α.natAbs * β.natAbs ≠ c2 * γ.natAbs * δ.natAbs := by
    intro h0
    apply hne
    rw [← Int.natAbs_eq_iff_sq_eq]
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    rw [← mul_assoc, ← mul_assoc]
    exact h0
  rw [smallBad, hD, hA] at hb
  simp [hlt1, hlt2, Nat.mul_div_cancel_left _ hσ, Nat.mul_mod_right, isSq_sq, Nat.sqrt_eq',
    hne'] at hb

/-- One of the three families applies. -/
def torsionOK1 (p q lam c1 c2 c3 c4 σ : ℕ) : Bool :=
  linOK p q lam c1 c2 c3 c4 σ || quadDOK p q lam c1 c2 c3 c4 σ || quadKOK p q lam c1 c2 c3 c4 σ

/-- One of the three families applies, possibly after the symmetry
`(α, β, γ, δ, c₁, c₂, c₃, c₄) ↦ (δ, γ, β, α, c₂, c₁, c₄, c₃)`, which swaps the two equations. -/
def torsionOK (p q lam c1 c2 c3 c4 σ : ℕ) : Bool :=
  torsionOK1 p q lam c1 c2 c3 c4 σ || torsionOK1 p q lam c2 c1 c4 c3 σ

/-- The moduli are usable: `0 < N`, `2 ≤ l` and `l ∣ N`. -/
def modsOK (mods : List (ℕ × ℕ)) : Bool :=
  mods.all fun x ↦ 0 < x.1 && 2 ≤ x.2 && x.1 % x.2 == 0

/-- The cases with a given `λ`: every tuple `(λ, c₁, c₂, c₃, c₄, σ)` is handled by one of the
torsion families or is ruled out by a congruence. -/
def lamCheck (p q a : ℕ) (mods : List (ℕ × ℕ)) (lam : ℕ) : Bool :=
  (divs (p / Nat.gcd p lam)).all fun c1 ↦
    Nat.gcd c1 (p / Nat.gcd p lam / c1) != 1 || (divs (lam / Nat.gcd p lam)).all fun c3 ↦
      Nat.gcd c3 (lam / Nat.gcd p lam / c3) != 1 ||
      (divs ((lam / Nat.gcd p lam) ^ 2 * a ^ 2)).all fun σ ↦
        torsionOK p q lam c1 (p / Nat.gcd p lam / c1) c3 (lam / Nat.gcd p lam / c3) σ ||
        tupleOK mods q lam c1 (p / Nat.gcd p lam / c1) c3 (lam / Nat.gcd p lam / c3) σ

/-- `lamCheck` for the divisors `λ` of `pq` with `lo ≤ λ < hi`. Large fibers are checked in a
few such ranges, so that each kernel run stays small. -/
def fiberCheckOn (p q a : ℕ) (mods : List (ℕ × ℕ)) (lo hi : ℕ) : Bool :=
  (divs (p * q)).all fun lam ↦ !(decide (lo ≤ lam) && decide (lam < hi)) || lamCheck p q a mods lam

/-- The whole case list of the pair `(p, q)` with `q² − p² = a²`. -/
def fiberCheck (p q a : ℕ) (mods : List (ℕ × ℕ)) : Bool :=
  modsOK mods && fiberCheckOn p q a mods 0 (p * q + 1)

theorem fiberCheckOn_trans {p q a lo mid hi : ℕ} {mods : List (ℕ × ℕ)}
    (h1 : fiberCheckOn p q a mods lo mid = true) (h2 : fiberCheckOn p q a mods mid hi = true) :
    fiberCheckOn p q a mods lo hi = true := by
  simp only [fiberCheckOn, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le, not_lt] at h1 h2 ⊢
  intro lam hlam
  rcases h1 lam hlam with (h | h) | h
  · exact Or.inl (Or.inl h)
  · rcases h2 lam hlam with (h' | h') | h'
    · exact Or.inr (by omega)
    · exact Or.inl (Or.inr h')
    · exact Or.inr h'
  · exact Or.inr h

theorem fiberCheck_of_on {p q a : ℕ} {mods : List (ℕ × ℕ)} (hm : modsOK mods = true)
    (h : fiberCheckOn p q a mods 0 (p * q + 1) = true) : fiberCheck p q a mods = true := by
  rw [fiberCheck, hm, h, Bool.and_self]

theorem fiberCheck_mods {p q a : ℕ} {mods : List (ℕ × ℕ)} (h : fiberCheck p q a mods = true) :
    ∀ x ∈ mods, 0 < x.1 ∧ 2 ≤ x.2 ∧ x.2 ∣ x.1 := by
  simp only [fiberCheck, modsOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  intro x hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := h.1 x hx
  exact ⟨h1, h2, Nat.dvd_of_mod_eq_zero h3⟩

theorem fiberCheck_spec {p q a : ℕ} {mods : List (ℕ × ℕ)} (h : fiberCheck p q a mods = true)
    (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) {lam c1 c2 c3 c4 σ : ℕ} (hlam : 0 < lam)
    (hlpq : lam ∣ p * q) (hc12 : c1 * c2 = p / Nat.gcd p lam) (hc12' : Nat.Coprime c1 c2)
    (hc34 : c3 * c4 = lam / Nat.gcd p lam) (hc34' : Nat.Coprime c3 c4)
    (hσd : σ ∣ (lam / Nat.gcd p lam) ^ 2 * a ^ 2) :
    torsionOK p q lam c1 c2 c3 c4 σ = true ∨ tupleOK mods q lam c1 c2 c3 c4 σ = true := by
  have hg : 0 < Nat.gcd p lam := Nat.gcd_pos_of_pos_left _ hp
  have hp' : 0 < p / Nat.gcd p lam := Nat.div_pos (Nat.gcd_le_left _ hp) hg
  have hl' : 0 < lam / Nat.gcd p lam := Nat.div_pos (Nat.gcd_le_right _ hlam) hg
  have hc1 : 0 < c1 := Nat.pos_of_mul_pos_right (hc12 ▸ hp')
  have hc3 : 0 < c3 := Nat.pos_of_mul_pos_right (hc34 ▸ hl')
  have e2 : p / Nat.gcd p lam / c1 = c2 := by rw [← hc12, Nat.mul_div_cancel_left _ hc1]
  have e4 : lam / Nat.gcd p lam / c3 = c4 := by rw [← hc34, Nat.mul_div_cancel_left _ hc3]
  have hle : lam < p * q + 1 := Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.mul_pos hp hq) hlpq)
  simp only [fiberCheck, fiberCheckOn, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 lam (mem_divs (Nat.mul_pos hp hq) hlpq)
  simp only [Nat.zero_le, hle, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    lamCheck, List.all_eq_true] at this
  have := this c1 (mem_divs hp' ⟨c2, hc12.symm⟩)
  rw [e2, hc12'.gcd_eq_one] at this
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at this
  have := this c3 (mem_divs hl' ⟨c4, hc34.symm⟩)
  rw [e4, hc34'.gcd_eq_one] at this
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at this
  have := this σ (mem_divs (Nat.mul_pos (pow_pos hl' 2) (pow_pos ha 2)) hσd)
  simpa only [Bool.or_eq_true, or_assoc] using this

/-! ### Coverage

`Covered p q a` is the hypothesis of the descent: every case is a torsion translate or is ruled
out modulo a single `(N, l)`. It follows from `fiberCheck` (`covered_of_fiberCheck`) or from a
certificate (`coveredOn_of_fiberCheckCert`). `CoveredOn` restricts it to the cases whose
`caseKey`, which orders the cases by `(λ, c₁, c₃)`, lies in a range, so that the kernel can check
a large fiber in pieces. -/

/-- The cases `(λ, c₁, c₂, c₃, c₄, σ)` ordered by `(λ, c₁, c₃)`, using `c₁ ≤ p` and `c₃ ≤ pq`. -/
def caseKey (p q lam c1 c3 : ℕ) : ℕ := (lam * (p + 1) + c1) * (p * q + 1) + c3

theorem le_caseKey (p q lam c1 c3 : ℕ) :
    lam * ((p + 1) * (p * q + 1)) ≤ caseKey p q lam c1 c3 :=
  calc lam * ((p + 1) * (p * q + 1))
      ≤ lam * ((p + 1) * (p * q + 1)) + (c1 * (p * q + 1) + c3) := Nat.le_add_right _ _
    _ = caseKey p q lam c1 c3 := by rw [caseKey]; ring

theorem caseKey_lt {p q lam c1 c3 : ℕ} (hc1 : c1 ≤ p) (hc3 : c3 ≤ p * q) :
    caseKey p q lam c1 c3 < (lam + 1) * ((p + 1) * (p * q + 1)) :=
  calc caseKey p q lam c1 c3
      < (lam * (p + 1) + c1) * (p * q + 1) + (p * q + 1) :=
        Nat.add_lt_add_left (Nat.lt_succ_of_le hc3) _
    _ = (lam * (p + 1) + (c1 + 1)) * (p * q + 1) := by ring
    _ ≤ (lam * (p + 1) + (p + 1)) * (p * q + 1) :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.succ_le_succ hc1) _)
    _ = (lam + 1) * ((p + 1) * (p * q + 1)) := by ring

/-- Every case `(λ, c₁, c₂, c₃, c₄, σ)` of the pair `(p, q)` with `lo ≤ caseKey p q λ c₁ c₃ < hi`
and `σlo ≤ σ < σhi` is a torsion translate (`torsionOK`) or is ruled out modulo some `(N, l)`
with `0 < N`, `2 ≤ l` and `l ∣ N`. -/
def CoveredOn (p q a lo hi σlo σhi : ℕ) : Prop :=
  ∀ ⦃lam c1 c2 c3 c4 σ : ℕ⦄, 0 < lam → lam ∣ p * q → lo ≤ caseKey p q lam c1 c3 →
    caseKey p q lam c1 c3 < hi → σlo ≤ σ → σ < σhi → c1 * c2 = p / Nat.gcd p lam →
    Nat.Coprime c1 c2 → c3 * c4 = lam / Nat.gcd p lam → Nat.Coprime c3 c4 →
    σ ∣ (lam / Nat.gcd p lam) ^ 2 * a ^ 2 →
    torsionOK p q lam c1 c2 c3 c4 σ = true ∨
      ∃ N l : ℕ, 0 < N ∧ 2 ≤ l ∧ l ∣ N ∧ tupleOK [(N, l)] q lam c1 c2 c3 c4 σ = true

/-- Every case of the pair `(p, q)` is covered: the hypothesis of the descent. Since
`σ ∣ λ'² a²` and `λ' ≤ pq`, the range `σ < (pq)² a² + 1` holds for every case. -/
def Covered (p q a : ℕ) : Prop :=
  CoveredOn p q a 0 ((p * q + 1) * ((p + 1) * (p * q + 1))) 0 ((p * q) ^ 2 * a ^ 2 + 1)

/-- Two certificates on adjacent key ranges cover their union. -/
theorem CoveredOn.trans {p q a lo mid hi σlo σhi : ℕ} (h1 : CoveredOn p q a lo mid σlo σhi)
    (h2 : CoveredOn p q a mid hi σlo σhi) : CoveredOn p q a lo hi σlo σhi := by
  intro lam c1 c2 c3 c4 σ h0 hd hlo hhi hσlo hσhi
  rcases lt_or_ge (caseKey p q lam c1 c3) mid with h | h
  · exact h1 h0 hd hlo h hσlo hσhi
  · exact h2 h0 hd h hhi hσlo hσhi

/-- Two certificates on the same key range and adjacent `σ` ranges cover their union. -/
theorem CoveredOn.transσ {p q a lo hi σlo σmid σhi : ℕ} (h1 : CoveredOn p q a lo hi σlo σmid)
    (h2 : CoveredOn p q a lo hi σmid σhi) : CoveredOn p q a lo hi σlo σhi := by
  intro lam c1 c2 c3 c4 σ h0 hd hlo hhi hσlo hσhi
  rcases lt_or_ge σ σmid with h | h
  · exact h1 h0 hd hlo hhi hσlo h
  · exact h2 h0 hd hlo hhi h hσhi

/-- The cases of a covered pair, without the range. -/
theorem Covered.cases {p q a : ℕ} (h : Covered p q a) (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    {lam c1 c2 c3 c4 σ : ℕ}
    (hlam : 0 < lam) (hlpq : lam ∣ p * q) (hc12 : c1 * c2 = p / Nat.gcd p lam)
    (hc12' : Nat.Coprime c1 c2) (hc34 : c3 * c4 = lam / Nat.gcd p lam) (hc34' : Nat.Coprime c3 c4)
    (hσd : σ ∣ (lam / Nat.gcd p lam) ^ 2 * a ^ 2) :
    torsionOK p q lam c1 c2 c3 c4 σ = true ∨
      ∃ N l : ℕ, 0 < N ∧ 2 ≤ l ∧ l ∣ N ∧ tupleOK [(N, l)] q lam c1 c2 c3 c4 σ = true := by
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have hc1 : c1 ≤ p := (Nat.le_of_dvd (Nat.div_pos (Nat.gcd_le_left _ hp)
    (Nat.gcd_pos_of_pos_left _ hp)) ⟨c2, hc12.symm⟩).trans (Nat.div_le_self _ _)
  have hc3 : c3 ≤ p * q := ((Nat.le_of_dvd (Nat.div_pos (Nat.gcd_le_right _ hlam)
    (Nat.gcd_pos_of_pos_left _ hp)) ⟨c4, hc34.symm⟩).trans (Nat.div_le_self _ _)).trans
    (Nat.le_of_dvd hpq hlpq)
  have hσ : σ < (p * q) ^ 2 * a ^ 2 + 1 := by
    have hl' : 0 < lam / Nat.gcd p lam :=
      Nat.div_pos (Nat.gcd_le_right _ hlam) (Nat.gcd_pos_of_pos_left _ hp)
    have hl : lam / Nat.gcd p lam ≤ p * q := (Nat.div_le_self _ _).trans (Nat.le_of_dvd hpq hlpq)
    refine Nat.lt_succ_of_le ((Nat.le_of_dvd (Nat.mul_pos (pow_pos hl' 2) (pow_pos ha 2)) hσd).trans
      ?_)
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hl 2)
  refine h hlam hlpq (Nat.zero_le _) ((caseKey_lt hc1 hc3).trans_le ?_) (Nat.zero_le _) hσ hc12
    hc12' hc34 hc34' hσd
  exact Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.le_of_dvd hpq hlpq))

theorem covered_of_fiberCheck {p q a : ℕ} {mods : List (ℕ × ℕ)} (h : fiberCheck p q a mods = true)
    (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) : Covered p q a := by
  intro lam c1 c2 c3 c4 σ h0 hd _ _ _ _ hc12 hc12' hc34 hc34' hσ
  rcases fiberCheck_spec h hp hq ha h0 hd hc12 hc12' hc34 hc34' hσ with h' | h'
  · exact Or.inl h'
  · obtain ⟨⟨N, l⟩, hm, hc⟩ := List.any_eq_true.mp h'
    obtain ⟨hN, hl, hlN⟩ := fiberCheck_mods h _ hm
    exact Or.inr ⟨N, l, hN, hl, hlN, by simpa [tupleOK] using hc⟩

/-! ### Certificates

`fiberCheck` tries `torsionOK` and then every modulus of `mods` on each case. A certificate
instead names, for each case of `fiberCases` in order, the one test that succeeds: `.torsion`, or
`.modulus N l` for a single residue check. The kernel then does one `O(N²)` check per case that
is not a torsion translate. Certificates are produced by `scripts/cuboid_cert.py`, which mirrors
the definitions of this file. -/

/-- The test that handles one case: a torsion family, or the residue check modulo `N` with the
coprimality conditions modulo `l`. -/
inductive Cert where
  | torsion
  | modulus (N l : ℕ)

/-- The test `c` succeeds on the case `(λ, c₁, c₂, c₃, c₄, σ)`. -/
def certStep (p q lam c1 c2 c3 c4 σ : ℕ) : Cert → Bool
  | .torsion => torsionOK p q lam c1 c2 c3 c4 σ
  | .modulus N l =>
    decide (0 < N) && decide (2 ≤ l) && N % l == 0 && tupleOK [(N, l)] q lam c1 c2 c3 c4 σ

/-- The cases `(c₁, c₂, c₃, c₄, σ)` of one `λ` with `lo ≤ caseKey p q λ c₁ c₃ < hi` and
`σlo ≤ σ < σhi`: as in `lamCheck`, but the divisors `σ` of `λ'² a²` are listed by `divsSq`,
which is much cheaper than trial division up to `λ' a`. The range of `σ` lets a certificate split
the cases of one `(λ, c₁, c₃)` into several kernel runs. -/
def lamCases (p q a lo hi σlo σhi lam : ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (divs (p / Nat.gcd p lam)).flatMap fun c1 ↦
    if Nat.gcd c1 (p / Nat.gcd p lam / c1) != 1 then [] else
    (divs (lam / Nat.gcd p lam)).flatMap fun c3 ↦
      if Nat.gcd c3 (lam / Nat.gcd p lam / c3) != 1 ||
        !(decide (lo ≤ caseKey p q lam c1 c3) && decide (caseKey p q lam c1 c3 < hi)) then [] else
      ((divsSq (divsMul (lam / Nat.gcd p lam) a) (lam / Nat.gcd p lam * a)).filter fun σ ↦
        decide (σlo ≤ σ) && decide (σ < σhi)).map fun σ ↦
        (c1, p / Nat.gcd p lam / c1, c3, lam / Nat.gcd p lam / c3, σ)

/-- The cases `(λ, c₁, c₂, c₃, c₄, σ)` of the pair `(p, q)` with `lo ≤ caseKey p q λ c₁ c₃ < hi`
and `σlo ≤ σ < σhi`, in the order of `fiberCheckOn`. The `λ` whose keys all miss the range are
skipped at once. -/
def fiberCases (p q a lo hi σlo σhi : ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (divs (p * q)).flatMap fun lam ↦
    if decide (lam * ((p + 1) * (p * q + 1)) < hi) &&
        decide (lo < (lam + 1) * ((p + 1) * (p * q + 1))) then
      (lamCases p q a lo hi σlo σhi lam).map ((lam, ·))
    else []

/-- Each case of the list passes the corresponding test of the certificate, and the two lists
have the same length. -/
def certOK (p q : ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) → List Cert → Bool
  | [], [] => true
  | (lam, c1, c2, c3, c4, σ) :: ts, c :: cs => certStep p q lam c1 c2 c3 c4 σ c && certOK p q ts cs
  | _, _ => false

/-- The certificate `cert` handles every case of `(p, q)` with `lo ≤ caseKey p q λ c₁ c₃ < hi` and
`σlo ≤ σ < σhi`. -/
def fiberCheckCert (p q a lo hi σlo σhi : ℕ) (cert : List Cert) : Bool :=
  decide (0 < p) && decide (0 < q) && decide (0 < a) &&
    certOK p q (fiberCases p q a lo hi σlo σhi) cert

theorem certStep_sound {p q lam c1 c2 c3 c4 σ : ℕ} {c : Cert}
    (h : certStep p q lam c1 c2 c3 c4 σ c = true) :
    torsionOK p q lam c1 c2 c3 c4 σ = true ∨
      ∃ N l : ℕ, 0 < N ∧ 2 ≤ l ∧ l ∣ N ∧ tupleOK [(N, l)] q lam c1 c2 c3 c4 σ = true := by
  cases c with
  | torsion => exact Or.inl h
  | modulus N l =>
    simp only [certStep, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact Or.inr ⟨N, l, h.1.1.1, h.1.1.2, Nat.dvd_of_mod_eq_zero h.1.2, h.2⟩

theorem certOK_sound {p q : ℕ} :
    ∀ (L : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (C : List Cert), certOK p q L C = true →
      ∀ t ∈ L, ∃ c, certStep p q t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 c = true
  | [], _, _, t, ht => absurd ht List.not_mem_nil
  | (_, _, _, _, _, _) :: _, [], h, _, _ => by simp [certOK] at h
  | (lam, c1, c2, c3, c4, σ) :: L, c :: C, h, t, ht => by
    simp only [certOK, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨c, h.1⟩
    · exact certOK_sound L C h.2 t ht

theorem mem_fiberCases {p q a lo hi σlo σhi : ℕ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    {lam c1 c2 c3 c4 σ : ℕ} (hlam : 0 < lam) (hlpq : lam ∣ p * q)
    (hlo : lo ≤ caseKey p q lam c1 c3) (hhi : caseKey p q lam c1 c3 < hi)
    (hσlo : σlo ≤ σ) (hσhi : σ < σhi)
    (hc12 : c1 * c2 = p / Nat.gcd p lam) (hc12' : Nat.Coprime c1 c2)
    (hc34 : c3 * c4 = lam / Nat.gcd p lam) (hc34' : Nat.Coprime c3 c4)
    (hσd : σ ∣ (lam / Nat.gcd p lam) ^ 2 * a ^ 2) :
    (lam, c1, c2, c3, c4, σ) ∈ fiberCases p q a lo hi σlo σhi := by
  have hg : 0 < Nat.gcd p lam := Nat.gcd_pos_of_pos_left _ hp
  have hp' : 0 < p / Nat.gcd p lam := Nat.div_pos (Nat.gcd_le_left _ hp) hg
  have hl' : 0 < lam / Nat.gcd p lam := Nat.div_pos (Nat.gcd_le_right _ hlam) hg
  have hc1 : 0 < c1 := Nat.pos_of_mul_pos_right (hc12 ▸ hp')
  have hc3 : 0 < c3 := Nat.pos_of_mul_pos_right (hc34 ▸ hl')
  have e2 : p / Nat.gcd p lam / c1 = c2 := by rw [← hc12, Nat.mul_div_cancel_left _ hc1]
  have e4 : lam / Nat.gcd p lam / c3 = c4 := by rw [← hc34, Nat.mul_div_cancel_left _ hc3]
  have hc1p : c1 ≤ p := (Nat.le_of_dvd hp' ⟨c2, hc12.symm⟩).trans (Nat.div_le_self _ _)
  have hc3l : c3 ≤ p * q := ((Nat.le_of_dvd hl' ⟨c4, hc34.symm⟩).trans
    (Nat.div_le_self _ _)).trans (Nat.le_of_dvd (Nat.mul_pos hp hq) hlpq)
  have h1 : lam * ((p + 1) * (p * q + 1)) < hi := (le_caseKey p q lam c1 c3).trans_lt hhi
  have h2 : lo < (lam + 1) * ((p + 1) * (p * q + 1)) := hlo.trans_lt (caseKey_lt hc1p hc3l)
  simp only [fiberCases, List.mem_flatMap]
  refine ⟨lam, mem_divs (Nat.mul_pos hp hq) hlpq, ?_⟩
  simp only [h1, h2, decide_true, Bool.and_self, ↓reduceIte, List.mem_map, Prod.mk.injEq,
    true_and, exists_eq_right, lamCases, List.mem_flatMap]
  refine ⟨c1, mem_divs hp' ⟨c2, hc12.symm⟩, ?_⟩
  rw [e2, hc12'.gcd_eq_one]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap]
  refine ⟨c3, mem_divs hl' ⟨c4, hc34.symm⟩, ?_⟩
  rw [e4, hc34'.gcd_eq_one]
  simp only [bne_self_eq_false, hlo, hhi, decide_true, Bool.and_self, Bool.not_true,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, List.mem_map, List.mem_filter]
  refine ⟨σ, ⟨mem_divsSq (Nat.mul_pos hl' ha) (fun d hd ↦ mem_divsMul hl' ha hd) ?_,
    by simp [hσlo, hσhi]⟩, rfl⟩
  rwa [show lam / Nat.gcd p lam * a * (lam / Nat.gcd p lam * a) =
    (lam / Nat.gcd p lam) ^ 2 * a ^ 2 by ring]

/-- **Soundness of a certificate.** -/
theorem coveredOn_of_fiberCheckCert {p q a lo hi σlo σhi : ℕ} {cert : List Cert}
    (h : fiberCheckCert p q a lo hi σlo σhi cert = true) : CoveredOn p q a lo hi σlo σhi := by
  simp only [fiberCheckCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, hq⟩, ha⟩, h⟩ := h
  intro lam c1 c2 c3 c4 σ h0 hd hlo hhi hσlo hσhi hc12 hc12' hc34 hc34' hσ
  obtain ⟨c, hc⟩ := certOK_sound _ _ h _
    (mem_fiberCases hp hq ha h0 hd hlo hhi hσlo hσhi hc12 hc12' hc34 hc34' hσ)
  exact certStep_sound hc

end Descent

end PerfectCuboid
