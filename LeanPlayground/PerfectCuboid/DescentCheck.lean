module

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
`s d² mod N` are stored as the bits of a natural number (`sqMask`), so the work is `O(N²)`.
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

/-- `true` if no residues `α, β, γ, δ` modulo `N` satisfy both equations modulo `N` and the
coprimality conditions modulo `l`. The coefficients are expected to be reduced modulo `N`, and
`B₁, B₂` to be negated already. -/
def check (N l A1 B1 s1 A2 B2 s2 c1 c2 c3 c4 : ℕ) : Bool :=
  (List.range N).all fun b ↦ (List.range N).all fun g ↦
    [true, false].all fun az ↦ [true, false].all fun dz ↦
      !((sqMask N l s1 dz).testBit ((A1 * g * g + B1 * b * b) % N) &&
        (sqMask N l s2 az).testBit ((A2 * b * b + B2 * g * g) % N) &&
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
  simp only [check, List.all_eq_true, List.mem_range] at h
  have H := h (res N β) (res_lt hN β) (res N γ) (res_lt hN γ) (decide ((l : ℤ) ∣ α))
    (by cases decide ((l : ℤ) ∣ α) <;> simp) (decide ((l : ℤ) ∣ δ))
    (by cases decide ((l : ℤ) ∣ δ) <;> simp)
  have hok := okB_spec _ _ _ _ _ _ _ _ (flag_false hab hl) (flag_false hag hl) (flag_false had hl)
    (flag_false hbg hl) (flag_false hbd hl) (flag_false hgd hl) (flag_false h1g hl)
    (flag_false h1d hl) (flag_false h2a hl) (flag_false h2b hl) (flag_false h3b hl)
    (flag_false h3d hl) (flag_false h4a hl) (flag_false h4g hl)
  rw [mask_of_eq hN hlN E1, mask_of_eq hN hlN E2, res_mod_eq_zero_iff hN hlN,
    res_mod_eq_zero_iff hN hlN, natCast_mod_dvd, natCast_mod_dvd, natCast_mod_dvd,
    natCast_mod_dvd, hok] at H
  simp at H

/-! ### The case list of one fiber -/

/-- The divisors of `n` (with repetitions), found by trial division up to `√n`. -/
def divs (n : ℕ) : List ℕ :=
  (List.range (Nat.sqrt n + 1)).flatMap fun d ↦ if d != 0 && n % d == 0 then [d, n / d] else []

theorem mem_divs {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) : d ∈ divs n := by
  obtain ⟨e, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_mul_pos_right hn
  have he0 : 0 < e := Nat.pos_of_mul_pos_left hn
  simp only [divs, List.mem_flatMap, List.mem_range]
  rcases le_or_gt d (Nat.sqrt (d * e)) with h | h
  · refine ⟨d, by omega, ?_⟩
    simp [hd0.ne', Nat.mul_mod_right]
  · refine ⟨e, ?_, ?_⟩
    · by_contra h'
      have h1 : d * e < (Nat.sqrt (d * e) + 1) * (Nat.sqrt (d * e) + 1) := Nat.lt_succ_sqrt _
      have : (Nat.sqrt (d * e) + 1) * (Nat.sqrt (d * e) + 1) ≤ d * e :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    · simp [he0.ne', Nat.mul_mod_left, Nat.mul_div_cancel _ he0]

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

/-- The first surviving shape: `λ = p`, all `cᵢ = 1`, `σ = (q − p) s²`. -/
def classI (p q lam c1 c2 c3 c4 σ : ℕ) : Bool :=
  lam == p && c1 == 1 && c2 == 1 && c3 == 1 && c4 == 1 && σ % (q - p) == 0 && isSq (σ / (q - p))

/-- The second surviving shape: `λ = q`, `{c₃, c₄} = {1, q}`, `σ = q s²`. -/
def classII (q lam c3 c4 σ : ℕ) : Bool :=
  lam == q && ((c3 == q && c4 == 1) || (c3 == 1 && c4 == q)) && σ % q == 0 && isSq (σ / q)

/-- The third surviving shape, for `q = w²` and `q − p = d²`: `λ = pq`, `c₁ = c₂ = 1`,
`{c₃, c₄} = {1, q}`, `σ = q s²`. -/
def classIII (p q lam c1 c2 c3 c4 σ : ℕ) : Bool :=
  lam == p * q && c1 == 1 && c2 == 1 && ((c3 == 1 && c4 == q) || (c3 == q && c4 == 1)) &&
    σ % q == 0 && isSq (σ / q) && isSq q && isSq (q - p)

/-- The fourth surviving shape, for `q = w²`: `λ = 1`, `c₃ = c₄ = 1`, `σ = s²`. -/
def classIV (q lam c3 c4 σ : ℕ) : Bool :=
  lam == 1 && c3 == 1 && c4 == 1 && isSq σ && isSq q

/-- The whole case list of the pair `(p, q)` with `q² − p² = a²`: every tuple
`(λ, c₁, c₂, c₃, c₄, σ)` that the descent can produce is of one of the four surviving shapes or is
ruled out by a congruence. -/
def fiberCheck (p q a : ℕ) (mods : List (ℕ × ℕ)) : Bool :=
  (mods.all fun x ↦ 0 < x.1 && 2 ≤ x.2 && x.1 % x.2 == 0) &&
  (divs (p * q)).all fun lam ↦
    (divs (p / Nat.gcd p lam)).all fun c1 ↦
      Nat.gcd c1 (p / Nat.gcd p lam / c1) != 1 || (divs (lam / Nat.gcd p lam)).all fun c3 ↦
        Nat.gcd c3 (lam / Nat.gcd p lam / c3) != 1 ||
        (divs ((lam / Nat.gcd p lam) ^ 2 * a ^ 2)).all fun σ ↦
          classI p q lam c1 (p / Nat.gcd p lam / c1) c3 (lam / Nat.gcd p lam / c3) σ ||
          classII q lam c3 (lam / Nat.gcd p lam / c3) σ ||
          classIII p q lam c1 (p / Nat.gcd p lam / c1) c3 (lam / Nat.gcd p lam / c3) σ ||
          classIV q lam c3 (lam / Nat.gcd p lam / c3) σ ||
          tupleOK mods q lam c1 (p / Nat.gcd p lam / c1) c3 (lam / Nat.gcd p lam / c3) σ

theorem fiberCheck_mods {p q a : ℕ} {mods : List (ℕ × ℕ)} (h : fiberCheck p q a mods = true) :
    ∀ x ∈ mods, 0 < x.1 ∧ 2 ≤ x.2 ∧ x.2 ∣ x.1 := by
  simp only [fiberCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  intro x hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := h.1 x hx
  exact ⟨h1, h2, Nat.dvd_of_mod_eq_zero h3⟩

theorem fiberCheck_spec {p q a : ℕ} {mods : List (ℕ × ℕ)} (h : fiberCheck p q a mods = true)
    (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) {lam c1 c2 c3 c4 σ : ℕ} (hlam : 0 < lam)
    (hlpq : lam ∣ p * q) (hc12 : c1 * c2 = p / Nat.gcd p lam) (hc12' : Nat.Coprime c1 c2)
    (hc34 : c3 * c4 = lam / Nat.gcd p lam) (hc34' : Nat.Coprime c3 c4)
    (hσd : σ ∣ (lam / Nat.gcd p lam) ^ 2 * a ^ 2) :
    classI p q lam c1 c2 c3 c4 σ = true ∨ classII q lam c3 c4 σ = true ∨
      classIII p q lam c1 c2 c3 c4 σ = true ∨ classIV q lam c3 c4 σ = true ∨
      tupleOK mods q lam c1 c2 c3 c4 σ = true := by
  have hg : 0 < Nat.gcd p lam := Nat.gcd_pos_of_pos_left _ hp
  have hp' : 0 < p / Nat.gcd p lam := Nat.div_pos (Nat.gcd_le_left _ hp) hg
  have hl' : 0 < lam / Nat.gcd p lam := Nat.div_pos (Nat.gcd_le_right _ hlam) hg
  have hc1 : 0 < c1 := Nat.pos_of_mul_pos_right (hc12 ▸ hp')
  have hc3 : 0 < c3 := Nat.pos_of_mul_pos_right (hc34 ▸ hl')
  have e2 : p / Nat.gcd p lam / c1 = c2 := by rw [← hc12, Nat.mul_div_cancel_left _ hc1]
  have e4 : lam / Nat.gcd p lam / c3 = c4 := by rw [← hc34, Nat.mul_div_cancel_left _ hc3]
  simp only [fiberCheck, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 lam (mem_divs (Nat.mul_pos hp hq) hlpq) c1 (mem_divs hp' ⟨c2, hc12.symm⟩)
  rw [e2, hc12'.gcd_eq_one] at this
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at this
  have := this c3 (mem_divs hl' ⟨c4, hc34.symm⟩)
  rw [e4, hc34'.gcd_eq_one] at this
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at this
  have := this σ (mem_divs (Nat.mul_pos (pow_pos hl' 2) (pow_pos ha 2)) hσd)
  simpa only [Bool.or_eq_true, or_assoc] using this

end Descent

end PerfectCuboid
