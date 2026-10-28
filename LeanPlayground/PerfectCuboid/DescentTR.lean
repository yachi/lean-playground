module

public import LeanPlayground.PerfectCuboid.Descent

/-!
# The descent with the `±T₄` exception

For the pair `(p, q) = (U², V²)` of a fiber, the point `T₄ = (pq, ·)` of the pair curve is `2P₈`
for an `8`-torsion point `P₈`, so it is a solution: `IsSol p q (UV e) e` holds for every `e ≠ 0`.
The descent can then only show that every solution is `±T₄`, `M² = pq e²`
(`sq_eq_of_isSol_of_casesOK4`), which is enough for a perfect cuboid
(`Kubert.IsPerfectCuboid.isSol_sq` gives a solution with `M² ≠ pq e²`).

The families L, QD and QK of `LeanPlayground.PerfectCuboid.Descent` never output `±T₄`. The
cases in the class of `P₈` need a new family, **TR**: the half-point `Q` of the solution `S`
(`2Q = S`) has the class of a torsion point `T = (d₁, y_T)` of order `8`, and the new solution is
`Q − T`, with `x(Q − T) = (M'/e')²` for
`M' = c₁c₄ (w d₂d₃ σ² αδ + d₁ c₃c₄ h H βγ)` and `e' = y_T σ² (qλ c₁² α² − d₁ c₄² δ²)`, where
`d₂ = d₁ + p²`, `d₃ = d₁ + q²`, `w² = qλd₁`, `h² = Dλσd₂`, `H² = Dqσd₃` and `y_T² = d₁d₂d₃`
(`tr_sq`). If `Q − T` is `O`, `(0, 0)` or `±T₄`, then `S = 2Q` is `±T₄`; algebraically, each of
these makes a binary form `R(β², γ²)` vanish, and a certificate `N G^k = R Z` shows that
`G(β², γ²) = σ² (p (k₁² − k₂²)² − 4q (k₁k₂)²)` vanishes too (`trCert_sound`). The forms are
coefficient lists (`pmul`, `pev`).

## Main results

* `trOK_sound` — the family TR gives a smaller solution that is not `±T₄`.
* `exists_smaller4` — one descent step for `CasesOK4`.
* `sq_eq_of_isSol_of_casesOK4` — every solution is `±T₄`.
-/

@[expose] public section

namespace PerfectCuboid

namespace Descent

/-! ### Polynomials as coefficient lists -/

/-- The sum of two polynomials, as coefficient lists with the constant term first. -/
def padd : List ℤ → List ℤ → List ℤ
  | [], l => l
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: padd as bs

/-- `c` times a polynomial. -/
def pscale (c : ℤ) (l : List ℤ) : List ℤ := l.map (c * ·)

/-- The difference of two polynomials. -/
def psub (a b : List ℤ) : List ℤ := padd a (pscale (-1) b)

/-- The product of two polynomials. -/
def pmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, b => padd (pscale a b) (0 :: pmul as b)

/-- The `k`-th power of a polynomial. -/
def ppow (l : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | k + 1 => pmul (ppow l k) l

/-- The value of a polynomial at `t : ℚ`. -/
def pev (l : List ℤ) (t : ℚ) : ℚ := l.foldr (fun a acc ↦ a + t * acc) 0

@[simp] theorem pev_nil (t : ℚ) : pev [] t = 0 := rfl

@[simp] theorem pev_cons (a : ℤ) (l : List ℤ) (t : ℚ) : pev (a :: l) t = a + t * pev l t := rfl

theorem pev_padd (t : ℚ) : ∀ a b : List ℤ, pev (padd a b) t = pev a t + pev b t
  | [], l => by simp [padd]
  | a :: as, [] => by simp [padd]
  | a :: as, b :: bs => by
    simp only [padd, pev_cons, pev_padd t as bs]
    push_cast
    ring

theorem pev_pscale (t : ℚ) (c : ℤ) : ∀ l : List ℤ, pev (pscale c l) t = c * pev l t
  | [] => by simp [pscale]
  | a :: l => by
    have := pev_pscale t c l
    simp only [pscale, List.map_cons, pev_cons] at this ⊢
    rw [this]
    push_cast
    ring

theorem pev_psub (t : ℚ) (a b : List ℤ) : pev (psub a b) t = pev a t - pev b t := by
  rw [psub, pev_padd, pev_pscale]
  push_cast
  ring

theorem pev_pmul (t : ℚ) : ∀ a b : List ℤ, pev (pmul a b) t = pev a t * pev b t
  | [], _ => by simp [pmul]
  | a :: as, b => by
    rw [pmul, pev_padd, pev_pscale, pev_cons, pev_cons, pev_pmul t as b]
    push_cast
    ring

theorem pev_ppow (t : ℚ) (l : List ℤ) : ∀ k, pev (ppow l k) t = pev l t ^ k
  | 0 => by simp [ppow]
  | k + 1 => by rw [ppow, pev_pmul, pev_ppow t l k, pow_succ]

theorem pev_eq_zero (t : ℚ) : ∀ l : List ℤ, l.all (· == 0) = true → pev l t = 0
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [pev_cons, h.1, pev_eq_zero t l h.2]
    simp

/-! ### The forms of family TR -/

/-- `A(t) = q c₄² t − λ c₂²`, so that `σα² = γ² A(β²/γ²)`. -/
def trA (q L c2 c4 : ℤ) : List ℤ := [-(L * c2 ^ 2), q * c4 ^ 2]

/-- `D(t) = q c₃² − λ c₁² t`, so that `σδ² = γ² D(β²/γ²)`. -/
def trD (q L c1 c3 : ℤ) : List ℤ := [q * c3 ^ 2, -(L * c1 ^ 2)]

/-- The form `Ã₀` with `σ² (M'² − pq e'²) = σ⁴ d₁d₂d₃ (Ã₀ + 2 c₁²c₃c₄³ w h H αβγδ)`. -/
def trA0 (p q L c1 c2 c3 c4 d1 : ℤ) : List ℤ :=
  psub (pscale (c1 ^ 2 * c4 ^ 2 * q * L)
      (padd (pscale ((d1 + p ^ 2) * (d1 + q ^ 2)) (pmul (trA q L c2 c4) (trD q L c1 c3)))
        (pscale (d1 * c3 ^ 2 * c4 ^ 2 * (q ^ 2 - p ^ 2) ^ 2) [0, 1])))
    (pscale (p * q) (ppow (psub (pscale (q * L * c1 ^ 2) (trA q L c2 c4))
      (pscale (d1 * c4 ^ 2) (trD q L c1 c3))) 2))

/-- `R₀ = Ã₀² − 4 c₁⁴c₃²c₄⁶ q²λ²D² d₁d₂d₃ A D t`, which vanishes when `M'² = pq e'²`. -/
def trR0 (p q L c1 c2 c3 c4 d1 : ℤ) : List ℤ :=
  psub (ppow (trA0 p q L c1 c2 c3 c4 d1) 2)
    (pscale (4 * c1 ^ 4 * c3 ^ 2 * c4 ^ 6 * q ^ 2 * L ^ 2 * (q ^ 2 - p ^ 2) ^ 2 * d1 *
      (d1 + p ^ 2) * (d1 + q ^ 2)) (pmul (pmul (trA q L c2 c4) (trD q L c1 c3)) [0, 1]))

/-- `R_M = d₂d₃ A D − d₁ c₃²c₄² D² t`, which vanishes when `M' = 0`. -/
def trRM (p q L c1 c2 c3 c4 d1 : ℤ) : List ℤ :=
  psub (pscale ((d1 + p ^ 2) * (d1 + q ^ 2)) (pmul (trA q L c2 c4) (trD q L c1 c3)))
    (pscale (d1 * c3 ^ 2 * c4 ^ 2 * (q ^ 2 - p ^ 2) ^ 2) [0, 1])

/-- `R_e = qλ c₁² A − d₁ c₄² D`, which vanishes when `e' = 0`. -/
def trRe (q L c1 c2 c3 c4 d1 : ℤ) : List ℤ :=
  psub (pscale (q * L * c1 ^ 2) (trA q L c2 c4)) (pscale (d1 * c4 ^ 2) (trD q L c1 c3))

/-- `G = p (K₁ − K₂)² − 4q K₁K₂` with `K₁ = c₁² A t`, `K₂ = c₂² D`: it vanishes exactly when the
solution is `±T₄`. -/
def trG (p q L c1 c2 c3 c4 : ℤ) : List ℤ :=
  psub (pscale p (ppow (psub (pscale (c1 ^ 2) (pmul (trA q L c2 c4) [0, 1]))
      (pscale (c2 ^ 2) (trD q L c1 c3))) 2))
    (pscale (4 * q) (pmul (pscale (c1 ^ 2) (pmul (trA q L c2 c4) [0, 1]))
      (pscale (c2 ^ 2) (trD q L c1 c3))))

/-- The certificate `N G^k = R₀ R_M R_e Z`. -/
def trCert (p q L c1 c2 c3 c4 d1 N : ℤ) (k : ℕ) (Z : List ℤ) : Bool :=
  (psub (pscale N (ppow (trG p q L c1 c2 c3 c4) k))
    (pmul (pmul (pmul (trR0 p q L c1 c2 c3 c4 d1) (trRM p q L c1 c2 c3 c4 d1))
      (trRe q L c1 c2 c3 c4 d1)) Z)).all (· == 0)

/-- `Ã₀` as a form in `a = σα²`, `d = σδ²`, `b = β²`, `g = γ²`. -/
def trA0F (p q L c1 c3 c4 d1 a d b g : ℚ) : ℚ :=
  c1 ^ 2 * c4 ^ 2 * q * L * ((d1 + p ^ 2) * (d1 + q ^ 2) * a * d +
    d1 * c3 ^ 2 * c4 ^ 2 * (q ^ 2 - p ^ 2) ^ 2 * (b * g)) -
    p * q * (q * L * c1 ^ 2 * a - d1 * c4 ^ 2 * d) ^ 2

/-- `R₀` as a form in `a, d, b, g`. -/
def trR0F (p q L c1 c3 c4 d1 a d b g : ℚ) : ℚ :=
  trA0F p q L c1 c3 c4 d1 a d b g ^ 2 - 4 * c1 ^ 4 * c3 ^ 2 * c4 ^ 6 * q ^ 2 * L ^ 2 *
    (q ^ 2 - p ^ 2) ^ 2 * d1 * (d1 + p ^ 2) * (d1 + q ^ 2) * (a * d) * (b * g)

/-- `R_M` as a form in `a, d, b, g`. -/
def trRMF (p q c3 c4 d1 a d b g : ℚ) : ℚ :=
  (d1 + p ^ 2) * (d1 + q ^ 2) * (a * d) - d1 * c3 ^ 2 * c4 ^ 2 * (q ^ 2 - p ^ 2) ^ 2 * (b * g)

/-- `R_e` as a form in `a, d`. -/
def trReF (q L c1 c4 d1 a d : ℚ) : ℚ := q * L * c1 ^ 2 * a - d1 * c4 ^ 2 * d

/-- `G` as a form in `a, d, b, g`. -/
def trGF (p q c1 c2 a d b g : ℚ) : ℚ :=
  p * (c1 ^ 2 * (a * b) - c2 ^ 2 * d * g) ^ 2 - 4 * q * (c1 ^ 2 * (a * b)) * (c2 ^ 2 * d * g)

/-- **Soundness of `trCert`.** With `a = σα²`, `d = σδ²`, `b = β²`, `g = γ²`, if one of
`R₀`, `R_M`, `R_e` vanishes, then so does `G`. -/
theorem trCert_sound {p q L c1 c2 c3 c4 d1 N : ℤ} {k : ℕ} {Z : List ℤ}
    (h : trCert p q L c1 c2 c3 c4 d1 N k Z = true) (hN : N ≠ 0) {a d b g : ℚ} (hg : g ≠ 0)
    (ha : a = q * c4 ^ 2 * b - L * c2 ^ 2 * g) (hd : d = q * c3 ^ 2 * g - L * c1 ^ 2 * b)
    (hz : trR0F p q L c1 c3 c4 d1 a d b g = 0 ∨ trRMF p q c3 c4 d1 a d b g = 0 ∨
      trReF q L c1 c4 d1 a d = 0) :
    trGF p q c1 c2 a d b g = 0 := by
  set t : ℚ := b / g with ht
  have hA : pev (trA q L c2 c4) t = a / g := by
    simp only [trA, pev_cons, pev_nil, ht, ha]
    push_cast
    field_simp
    ring
  have hD : pev (trD q L c1 c3) t = d / g := by
    simp only [trD, pev_cons, pev_nil, ht, hd]
    push_cast
    field_simp
    ring
  have hT : pev [0, 1] t = b / g := by simp [ht]
  have e0 : pev (trR0 p q L c1 c2 c3 c4 d1) t = trR0F p q L c1 c3 c4 d1 a d b g / g ^ 4 := by
    simp only [trR0, trA0, pev_psub, pev_pscale, pev_ppow, pev_pmul, pev_padd, hA, hD, hT]
    unfold trR0F trA0F
    push_cast
    field_simp
  have eM : pev (trRM p q L c1 c2 c3 c4 d1) t = trRMF p q c3 c4 d1 a d b g / g ^ 2 := by
    simp only [trRM, pev_psub, pev_pscale, pev_pmul, hA, hD, hT]
    unfold trRMF
    push_cast
    field_simp
  have ee : pev (trRe q L c1 c2 c3 c4 d1) t = trReF q L c1 c4 d1 a d / g := by
    simp only [trRe, pev_psub, pev_pscale, hA, hD]
    unfold trReF
    push_cast
    field_simp
  have eG : pev (trG p q L c1 c2 c3 c4) t = trGF p q c1 c2 a d b g / g ^ 4 := by
    simp only [trG, pev_psub, pev_pscale, pev_ppow, pev_pmul, hA, hD, hT]
    unfold trGF
    push_cast
    field_simp
  have hev := pev_eq_zero t _ h
  simp only [pev_psub, pev_pscale, pev_ppow, pev_pmul, e0, eM, ee, eG] at hev
  have hR : trR0F p q L c1 c3 c4 d1 a d b g / g ^ 4 * (trRMF p q c3 c4 d1 a d b g / g ^ 2) *
      (trReF q L c1 c4 d1 a d / g) = 0 := by
    rcases hz with hz | hz | hz <;> simp [hz]
  rw [hR, zero_mul, sub_zero] at hev
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have hG := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hev).resolve_left hN')
  exact (div_eq_zero_iff.mp hG).resolve_right (pow_ne_zero 4 hg)

/-! ### The identities of family TR -/

/-- **The new solution of family TR.** `M'² + p² e'²` and `M'² + q² e'²` are squares. -/
theorem tr_sq {p q L c1 c2 c3 c4 σ α β γ δ d1 yT w h H : ℤ}
    (hrel : L * (c1 * c2) = p * (c3 * c4))
    (E1 : q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2 = σ * δ ^ 2)
    (E2 : q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2 = σ * α ^ 2)
    (hy : yT ^ 2 = d1 * (d1 + p ^ 2) * (d1 + q ^ 2)) (hw : w ^ 2 = q * L * d1)
    (hh : h ^ 2 = (q ^ 2 - p ^ 2) * L * σ * (d1 + p ^ 2))
    (hH : H ^ 2 = (q ^ 2 - p ^ 2) * q * σ * (d1 + q ^ 2)) (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0)
    (hσ : σ ≠ 0) :
    (c4 * c1 * (w * (d1 + p ^ 2) * (d1 + q ^ 2) * σ ^ 2 * (α * δ) +
        d1 * c3 * c4 * h * H * (β * γ))) ^ 2 +
      p ^ 2 * (yT * σ ^ 2 * (q * L * c1 ^ 2 * α ^ 2 - d1 * c4 ^ 2 * δ ^ 2)) ^ 2 =
      (σ * c1 * c4 * (h * d1 * (d1 + q ^ 2) * c4 * (β * δ) +
        w * H * c3 * (d1 + p ^ 2) * (α * γ))) ^ 2 ∧
    (c4 * c1 * (w * (d1 + p ^ 2) * (d1 + q ^ 2) * σ ^ 2 * (α * δ) +
        d1 * c3 * c4 * h * H * (β * γ))) ^ 2 +
      q ^ 2 * (yT * σ ^ 2 * (q * L * c1 ^ 2 * α ^ 2 - d1 * c4 ^ 2 * δ ^ 2)) ^ 2 =
      (σ * c4 * (H * c3 * c4 * d1 * (d1 + p ^ 2) * (γ * δ) +
        w * h * c1 ^ 2 * (d1 + q ^ 2) * (α * β))) ^ 2 := by
  have hm : c1 ^ 4 * c2 ^ 4 * σ ^ 6 ≠ 0 := by positivity
  constructor
  · refine mul_left_cancel₀ hm ?_
    linear_combination (c1 ^ 4 * c2 ^ 4 * p ^ 2 * σ ^ 10 * (L * c1 ^ 2 * q * α ^ 2 - c4 ^ 2 * d1 *
      δ ^ 2) ^ 2) * hy + (c1 ^ 6 * c2 ^ 4 * c4 ^ 2 * α ^ 2 * σ ^ 8 * (d1 + p ^ 2) ^ 2 * (-H * c3 * γ
      + d1 * δ * σ + q ^ 2 * δ * σ) * (H * c3 * γ + d1 * δ * σ + q ^ 2 * δ * σ)) * hw + (-c1 ^ 6 *
      c2 ^ 4 * c4 ^ 4 * d1 ^ 2 * β ^ 2 * σ ^ 6 * (-H * c3 * γ + d1 * δ * σ + q ^ 2 * δ * σ) * (H *
      c3 * γ + d1 * δ * σ + q ^ 2 * δ * σ)) * hh + (-L * c1 ^ 6 * c2 ^ 4 * c3 ^ 2 * c4 ^ 2 * d1 *
      γ ^ 2 * σ ^ 7 * (d1 + p ^ 2) * (c4 ^ 2 * d1 * p ^ 2 * β ^ 2 - c4 ^ 2 * d1 * q ^ 2 * β ^ 2 + d1
      * q * α ^ 2 * σ + p ^ 2 * q * α ^ 2 * σ)) * hH + (-L * c1 ^ 6 * c2 ^ 4 * d1 * q * σ ^ 8 * (d1
      + p ^ 2) * (d1 + q ^ 2) * (-L ^ 2 * c1 ^ 2 * c2 ^ 2 * p ^ 2 * q * γ ^ 2 + L * c1 ^ 2 * c4 ^ 2
      * p ^ 2 * q ^ 2 * β ^ 2 + L * c1 ^ 2 * p ^ 2 * q * α ^ 2 * σ + c3 ^ 2 * c4 ^ 2 * d1 * p ^ 2 *
      q * γ ^ 2 - c3 ^ 2 * c4 ^ 2 * d1 * q ^ 3 * γ ^ 2 + c3 ^ 2 * c4 ^ 2 * p ^ 4 * q * γ ^ 2 -
      c3 ^ 2 * c4 ^ 2 * p ^ 2 * q ^ 3 * γ ^ 2 + c4 ^ 2 * d1 ^ 2 * δ ^ 2 * σ - c4 ^ 2 * d1 * p ^ 2 *
      δ ^ 2 * σ + c4 ^ 2 * d1 * q ^ 2 * δ ^ 2 * σ + c4 ^ 2 * p ^ 2 * q ^ 2 * δ ^ 2 * σ)) * E2 +
      (-c1 ^ 4 * c2 ^ 4 * c4 ^ 2 * d1 * σ ^ 8 * (d1 + p ^ 2) * (d1 + q ^ 2) * (-L ^ 2 * c1 ^ 2 *
      c2 ^ 2 * d1 ^ 2 * q * γ ^ 2 + L ^ 2 * c1 ^ 2 * c2 ^ 2 * d1 * p ^ 2 * q * γ ^ 2 - L ^ 2 *
      c1 ^ 2 * c2 ^ 2 * d1 * q ^ 3 * γ ^ 2 - L ^ 2 * c1 ^ 2 * c2 ^ 2 * p ^ 2 * q ^ 3 * γ ^ 2 + L *
      c1 ^ 2 * c4 ^ 2 * p ^ 2 * q ^ 4 * β ^ 2 + c3 ^ 2 * c4 ^ 2 * d1 ^ 2 * p ^ 2 * q * γ ^ 2 +
      c4 ^ 2 * d1 ^ 2 * p ^ 2 * δ ^ 2 * σ)) * E1 + (-c1 ^ 4 * c2 ^ 4 * d1 * q * γ ^ 2 * σ ^ 8 * (d1
      + p ^ 2) * (d1 + q ^ 2) * (L * c1 * c2 + c3 * c4 * p) * (-L ^ 2 * c1 ^ 2 * c2 ^ 2 * p ^ 2 * q
      * γ ^ 2 - L * c1 ^ 2 * c4 ^ 2 * d1 ^ 2 * β ^ 2 + L * c1 ^ 2 * c4 ^ 2 * d1 * p ^ 2 * β ^ 2 - L
      * c1 ^ 2 * c4 ^ 2 * d1 * q ^ 2 * β ^ 2 + L * c1 ^ 2 * c4 ^ 2 * p ^ 2 * q ^ 2 * β ^ 2 + c3 ^ 2
      * c4 ^ 2 * d1 ^ 2 * q * γ ^ 2)) * hrel
  · refine mul_left_cancel₀ hm ?_
    linear_combination (c1 ^ 4 * c2 ^ 4 * q ^ 2 * σ ^ 10 * (L * c1 ^ 2 * q * α ^ 2 - c4 ^ 2 * d1 *
      δ ^ 2) ^ 2) * hy + (c1 ^ 6 * c2 ^ 4 * c4 ^ 2 * α ^ 2 * σ ^ 8 * (d1 + q ^ 2) ^ 2 * (-c1 * h * β
      + d1 * δ * σ + p ^ 2 * δ * σ) * (c1 * h * β + d1 * δ * σ + p ^ 2 * δ * σ)) * hw + (-c1 ^ 6 *
      c2 ^ 4 * c4 ^ 2 * d1 * β ^ 2 * σ ^ 6 * (-H ^ 2 * c3 ^ 2 * c4 ^ 2 * d1 * γ ^ 2 + L * c1 ^ 2 *
      d1 ^ 2 * q * α ^ 2 * σ ^ 2 + 2 * L * c1 ^ 2 * d1 * q ^ 3 * α ^ 2 * σ ^ 2 + L * c1 ^ 2 * q ^ 5
      * α ^ 2 * σ ^ 2)) * hh + (-c1 ^ 4 * c2 ^ 4 * c3 ^ 2 * c4 ^ 4 * d1 ^ 2 * γ ^ 2 * σ ^ 7 * (d1 +
      p ^ 2) * (L * c1 ^ 2 * p ^ 2 * β ^ 2 - L * c1 ^ 2 * q ^ 2 * β ^ 2 + d1 * δ ^ 2 * σ + p ^ 2 *
      δ ^ 2 * σ)) * hH + (-L * c1 ^ 6 * c2 ^ 4 * d1 * q * σ ^ 8 * (d1 + p ^ 2) * (d1 + q ^ 2) *
      (-L ^ 2 * c1 ^ 2 * c2 ^ 2 * q ^ 3 * γ ^ 2 + L * c1 ^ 2 * c4 ^ 2 * d1 * p ^ 2 * β ^ 2 - L *
      c1 ^ 2 * c4 ^ 2 * d1 * q ^ 2 * β ^ 2 + L * c1 ^ 2 * c4 ^ 2 * p ^ 2 * q ^ 2 * β ^ 2 + L *
      c1 ^ 2 * q ^ 3 * α ^ 2 * σ + c4 ^ 2 * d1 ^ 2 * δ ^ 2 * σ + c4 ^ 2 * d1 * p ^ 2 * δ ^ 2 * σ -
      c4 ^ 2 * d1 * q ^ 2 * δ ^ 2 * σ + c4 ^ 2 * p ^ 2 * q ^ 2 * δ ^ 2 * σ)) * E2 + (-c1 ^ 4 *
      c2 ^ 4 * c4 ^ 2 * d1 * q * σ ^ 8 * (d1 + p ^ 2) * (d1 + q ^ 2) * (-L ^ 2 * c1 ^ 2 * c2 ^ 2 *
      d1 ^ 2 * γ ^ 2 - L ^ 2 * c1 ^ 2 * c2 ^ 2 * d1 * p ^ 2 * γ ^ 2 + L ^ 2 * c1 ^ 2 * c2 ^ 2 * d1 *
      q ^ 2 * γ ^ 2 - L ^ 2 * c1 ^ 2 * c2 ^ 2 * p ^ 2 * q ^ 2 * γ ^ 2 + L * c1 ^ 2 * c4 ^ 2 * d1 *
      p ^ 2 * q * β ^ 2 - L * c1 ^ 2 * c4 ^ 2 * d1 * q ^ 3 * β ^ 2 + L * c1 ^ 2 * c4 ^ 2 * p ^ 2 *
      q ^ 3 * β ^ 2 + c3 ^ 2 * c4 ^ 2 * d1 ^ 2 * p ^ 2 * γ ^ 2 + c3 ^ 2 * c4 ^ 2 * d1 * p ^ 4 *
      γ ^ 2 - c3 ^ 2 * c4 ^ 2 * d1 * p ^ 2 * q ^ 2 * γ ^ 2 + c4 ^ 2 * d1 ^ 2 * q * δ ^ 2 * σ)) * E1
      + (-c1 ^ 4 * c2 ^ 4 * d1 * q * γ ^ 2 * σ ^ 8 * (d1 + p ^ 2) * (d1 + q ^ 2) * (L * c1 * c2 + c3
      * c4 * p) * (-L ^ 2 * c1 ^ 2 * c2 ^ 2 * q ^ 3 * γ ^ 2 - L * c1 ^ 2 * c4 ^ 2 * d1 ^ 2 * β ^ 2 +
      L * c1 ^ 2 * c4 ^ 2 * q ^ 4 * β ^ 2 + c3 ^ 2 * c4 ^ 2 * d1 ^ 2 * q * γ ^ 2 + c3 ^ 2 * c4 ^ 2 *
      d1 * p ^ 2 * q * γ ^ 2 - c3 ^ 2 * c4 ^ 2 * d1 * q ^ 3 * γ ^ 2)) * hrel

/-- **`±T₄`, `O` and `(0, 0)` in family TR.** If `M' = 0`, `e' = 0` or `M'² = pq e'²`, then
`R₀`, `R_M` or `R_e` vanishes at `a = σα²`, `d = σδ²`, `b = β²`, `g = γ²`. -/
theorem tr_t4 {p q L c1 c2 c3 c4 σ α β γ δ d1 yT w h H : ℚ}
    (E1 : q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2 = σ * δ ^ 2)
    (E2 : q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2 = σ * α ^ 2)
    (hy : yT ^ 2 = d1 * (d1 + p ^ 2) * (d1 + q ^ 2)) (hw : w ^ 2 = q * L * d1)
    (hh : h ^ 2 = (q ^ 2 - p ^ 2) * L * σ * (d1 + p ^ 2))
    (hH : H ^ 2 = (q ^ 2 - p ^ 2) * q * σ * (d1 + q ^ 2)) (hc1 : c1 ≠ 0) (hc4 : c4 ≠ 0)
    (hσ : σ ≠ 0) (hq : q ≠ 0) (hL : L ≠ 0) (hd1 : d1 ≠ 0) (hd2 : d1 + p ^ 2 ≠ 0)
    (hd3 : d1 + q ^ 2 ≠ 0) (hyT : yT ≠ 0)
    (hz : c4 * c1 * (w * (d1 + p ^ 2) * (d1 + q ^ 2) * σ ^ 2 * (α * δ) +
        d1 * c3 * c4 * h * H * (β * γ)) = 0 ∨
      yT * σ ^ 2 * (q * L * c1 ^ 2 * α ^ 2 - d1 * c4 ^ 2 * δ ^ 2) = 0 ∨
      (c4 * c1 * (w * (d1 + p ^ 2) * (d1 + q ^ 2) * σ ^ 2 * (α * δ) +
        d1 * c3 * c4 * h * H * (β * γ))) ^ 2 =
        p * q * (yT * σ ^ 2 * (q * L * c1 ^ 2 * α ^ 2 - d1 * c4 ^ 2 * δ ^ 2)) ^ 2) :
    trR0F p q L c1 c3 c4 d1 (q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2)
        (q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2) (β ^ 2) (γ ^ 2) = 0 ∨
      trRMF p q c3 c4 d1 (q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2)
        (q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2) (β ^ 2) (γ ^ 2) = 0 ∨
      trReF q L c1 c4 d1 (q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2)
        (q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2) = 0 := by
  rcases hz with hz | hz | hz
  · -- `M' = 0`
    right; left
    have h1 : w * (d1 + p ^ 2) * (d1 + q ^ 2) * σ ^ 2 * (α * δ) =
        -(d1 * c3 * c4 * h * H * (β * γ)) := by
      linear_combination (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hc4 hc1)
    have hsq : (w * (d1 + p ^ 2) * (d1 + q ^ 2) * σ ^ 2 * (α * δ)) ^ 2 =
        (d1 * c3 * c4 * h * H * (β * γ)) ^ 2 := by rw [h1, neg_sq]
    have h2 : q * L * d1 * (d1 + p ^ 2) * (d1 + q ^ 2) * σ ^ 2 *
        trRMF p q c3 c4 d1 (q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2)
          (q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2) (β ^ 2) (γ ^ 2) = 0 := by
      unfold trRMF
      linear_combination hsq + q * L * d1 * (d1 + p ^ 2) ^ 2 * (d1 + q ^ 2) ^ 2 * σ ^ 2 *
        ((q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2) * E1 + σ * δ ^ 2 * E2) -
        (d1 + p ^ 2) ^ 2 * (d1 + q ^ 2) ^ 2 * σ ^ 4 * α ^ 2 * δ ^ 2 * hw +
        d1 ^ 2 * c3 ^ 2 * c4 ^ 2 * β ^ 2 * γ ^ 2 *
          (H ^ 2 * hh + (q ^ 2 - p ^ 2) * L * σ * (d1 + p ^ 2) * hH)
    exact (mul_eq_zero.mp h2).resolve_left (by positivity)
  · -- `e' = 0`
    right; right
    have h1 := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hyT (pow_ne_zero 2 hσ))
    unfold trReF
    linear_combination σ * h1 + q * L * c1 ^ 2 * E2 - d1 * c4 ^ 2 * E1
  · -- `M'² = pq e'²`
    left
    have H3 : σ ^ 2 * ((c4 * c1 * (w * (d1 + p ^ 2) * (d1 + q ^ 2) * σ ^ 2 * (α * δ) +
        d1 * c3 * c4 * h * H * (β * γ))) ^ 2 - p * q *
        (yT * σ ^ 2 * (q * L * c1 ^ 2 * α ^ 2 - d1 * c4 ^ 2 * δ ^ 2)) ^ 2) =
        σ ^ 4 * d1 * (d1 + p ^ 2) * (d1 + q ^ 2) *
          (trA0F p q L c1 c3 c4 d1 (q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2)
            (q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2) (β ^ 2) (γ ^ 2) +
          2 * c1 ^ 2 * c3 * c4 ^ 3 * w * h * H * (α * β * γ * δ)) := by
      unfold trA0F
      refine mul_left_cancel₀ (pow_ne_zero 6 hσ) ?_
      linear_combination (-p * q * σ ^ 12 * (L * c1 ^ 2 * q * α ^ 2 - c4 ^ 2 * d1 * δ ^ 2) ^ 2) * hy +
        (c1 ^ 2 * c4 ^ 2 * α ^ 2 * δ ^ 2 * σ ^ 12 * (d1 + p ^ 2) ^ 2 * (d1 + q ^ 2) ^ 2) * hw + (H ^ 2
        * c1 ^ 2 * c3 ^ 2 * c4 ^ 4 * d1 ^ 2 * β ^ 2 * γ ^ 2 * σ ^ 8) * hh + (-L * c1 ^ 2 * c3 ^ 2 *
        c4 ^ 4 * d1 ^ 2 * β ^ 2 * γ ^ 2 * σ ^ 9 * (d1 + p ^ 2) * (p - q) * (p + q)) * hH + (-L *
        c1 ^ 2 * d1 * q * σ ^ 10 * (d1 + p ^ 2) * (d1 + q ^ 2) * (L ^ 2 * c1 ^ 2 * c2 ^ 2 * p * q ^ 2
        * γ ^ 2 - L * c1 ^ 2 * c4 ^ 2 * p * q ^ 3 * β ^ 2 - L * c1 ^ 2 * p * q ^ 2 * α ^ 2 * σ +
        c4 ^ 2 * d1 ^ 2 * δ ^ 2 * σ + c4 ^ 2 * d1 * p ^ 2 * δ ^ 2 * σ + 2 * c4 ^ 2 * d1 * p * q *
        δ ^ 2 * σ + c4 ^ 2 * d1 * q ^ 2 * δ ^ 2 * σ + c4 ^ 2 * p ^ 2 * q ^ 2 * δ ^ 2 * σ)) * E2 +
        (-c4 ^ 2 * d1 * q * σ ^ 10 * (d1 + p ^ 2) * (d1 + q ^ 2) * (-L ^ 2 * c1 ^ 2 * c2 ^ 2 * d1 ^ 2
        * γ ^ 2 - L ^ 2 * c1 ^ 2 * c2 ^ 2 * d1 * p ^ 2 * γ ^ 2 - 2 * L ^ 2 * c1 ^ 2 * c2 ^ 2 * d1 * p
        * q * γ ^ 2 - L ^ 2 * c1 ^ 2 * c2 ^ 2 * d1 * q ^ 2 * γ ^ 2 - L ^ 2 * c1 ^ 2 * c2 ^ 2 * p ^ 2 *
        q ^ 2 * γ ^ 2 + L * c1 ^ 2 * c4 ^ 2 * d1 ^ 2 * p * β ^ 2 + L * c1 ^ 2 * c4 ^ 2 * d1 ^ 2 * q *
        β ^ 2 + L * c1 ^ 2 * c4 ^ 2 * d1 * p ^ 2 * q * β ^ 2 + 2 * L * c1 ^ 2 * c4 ^ 2 * d1 * p *
        q ^ 2 * β ^ 2 + L * c1 ^ 2 * c4 ^ 2 * d1 * q ^ 3 * β ^ 2 + L * c1 ^ 2 * c4 ^ 2 * p ^ 2 * q ^ 3
        * β ^ 2 - c3 ^ 2 * c4 ^ 2 * d1 ^ 2 * p * q * γ ^ 2 - c4 ^ 2 * d1 ^ 2 * p * δ ^ 2 * σ)) * E1
    have hA0 : trA0F p q L c1 c3 c4 d1 (q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2)
        (q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2) (β ^ 2) (γ ^ 2) +
        2 * c1 ^ 2 * c3 * c4 ^ 3 * w * h * H * (α * β * γ * δ) = 0 := by
      rw [hz, sub_self, mul_zero] at H3
      exact (mul_eq_zero.mp H3.symm).resolve_left (by positivity)
    have R0 : σ ^ 2 * ((2 * c1 ^ 2 * c3 * c4 ^ 3 * w * h * H * (α * β * γ * δ)) ^ 2 -
        4 * c1 ^ 4 * c3 ^ 2 * c4 ^ 6 * q ^ 2 * L ^ 2 * (q ^ 2 - p ^ 2) ^ 2 * d1 * (d1 + p ^ 2) *
          (d1 + q ^ 2) * ((q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2) *
            (q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2)) * (β ^ 2 * γ ^ 2)) = 0 := by
      linear_combination (4 * H ^ 2 * c1 ^ 4 * c3 ^ 2 * c4 ^ 6 * h ^ 2 * α ^ 2 * β ^ 2 * γ ^ 2 * δ ^ 2
        * σ ^ 2) * hw + (4 * H ^ 2 * L * c1 ^ 4 * c3 ^ 2 * c4 ^ 6 * d1 * q * α ^ 2 * β ^ 2 * γ ^ 2 *
        δ ^ 2 * σ ^ 2) * hh + (-4 * L ^ 2 * c1 ^ 4 * c3 ^ 2 * c4 ^ 6 * d1 * q * α ^ 2 * β ^ 2 * γ ^ 2
        * δ ^ 2 * σ ^ 3 * (d1 + p ^ 2) * (p - q) * (p + q)) * hH + (-4 * L ^ 2 * c1 ^ 4 * c3 ^ 2 *
        c4 ^ 6 * d1 * q ^ 2 * β ^ 2 * γ ^ 2 * δ ^ 2 * σ ^ 3 * (d1 + p ^ 2) * (d1 + q ^ 2) * (p -
        q) ^ 2 * (p + q) ^ 2) * E2 + (-4 * L ^ 2 * c1 ^ 4 * c3 ^ 2 * c4 ^ 6 * d1 * q ^ 2 * β ^ 2 *
        γ ^ 2 * σ ^ 2 * (d1 + p ^ 2) * (d1 + q ^ 2) * (p - q) ^ 2 * (p + q) ^ 2 * (-L * c2 ^ 2 * γ ^ 2
        + c4 ^ 2 * q * β ^ 2)) * E1
    have h2 : σ ^ 2 * trR0F p q L c1 c3 c4 d1 (q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2)
        (q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2) (β ^ 2) (γ ^ 2) = 0 := by
      unfold trR0F
      linear_combination σ ^ 2 * (trA0F p q L c1 c3 c4 d1 (q * c4 ^ 2 * β ^ 2 - L * c2 ^ 2 * γ ^ 2)
        (q * c3 ^ 2 * γ ^ 2 - L * c1 ^ 2 * β ^ 2) (β ^ 2) (γ ^ 2) -
          2 * c1 ^ 2 * c3 * c4 ^ 3 * w * h * H * (α * β * γ * δ)) * hA0 + R0
    exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 hσ)

end Descent

end PerfectCuboid
