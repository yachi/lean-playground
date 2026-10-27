module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import LeanPlayground.PerfectCuboid.CongruentRank

/-!
# Division polynomials of the congruent-number curves

Asiryan's reduction of a rank-one configuration (arXiv:2610.10643, §5) writes the abscissa of a
multiple of a point on `D_N : Nη² = t − t³` as `t([k]G) = P_k(z)/Q_k(z)` with `z = t(G)` and
integer polynomials `P_k`, `Q_k` that **do not depend on `N`**, of degrees `k²` and `k² − 1` and
leading coefficients `1` and `k²`. On `E_N : Y² = X³ − N²X` with `X = −Nt` this is a weighted
homogeneity of the division polynomials: substituting `X = vz` with `v = −N` turns the
division polynomials of `E_N` into powers of `v` times those of `E_1' : y² = x³ − x`
(`Φ_scale`, `ΨSq_scale`). The polynomials `P_k = Φ_k`, `Q_k = ΨSq_k` of `E_1'` have integer
coefficients (`cΦ`, `cΨSq`), with the degrees and leading coefficients from Mathlib's
`DivisionPolynomial.Degree`.
-/

@[expose] public section

namespace PerfectCuboid.CongruentRank

open WeierstrassCurve Polynomial

/-! ### Weighted homogeneity of the normalised EDS -/

/-- The weight of the `n`-th term of the auxiliary sequence `preΨ'`, counted in powers of
`v = u²` where the curve coefficient `a₄` has weight `4` in `u`: `(n² − 1)/2` for odd `n` and
`(n² − 4)/2` for even `n` (the even terms are divided by `ψ₂`, of weight `3`). -/
def wt (n : ℕ) : ℕ := (n ^ 2 - if Even n then 4 else 1) / 2

theorem wt_odd (k : ℕ) : wt (2 * k + 1) = 2 * k * (k + 1) := by
  simp only [wt, Nat.not_even_two_mul_add_one, ↓reduceIte]
  rw [show (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * (k + 1)) by ring_nf; omega]
  omega

theorem wt_even (k : ℕ) : wt (2 * k + 2) = 2 * k * (k + 2) := by
  simp only [wt, show Even (2 * k + 2) from ⟨k + 1, by ring⟩, ↓reduceIte]
  rw [show (2 * k + 2) ^ 2 - 4 = 2 * (2 * k * (k + 2)) by ring_nf; omega]
  omega

variable {R : Type*} [CommRing R]

/-- Scaling the parameters `b, c, d` of a normalised EDS by `v⁶, v⁴, v⁶` scales its `n`-th term
by `v ^ wt n`. -/
theorem preNormEDS'_scale (v b c d : R) (n : ℕ) :
    preNormEDS' (v ^ 6 * b) (v ^ 4 * c) (v ^ 6 * d) n = v ^ wt n * preNormEDS' b c d n := by
  induction n using normEDSRec' with
  | zero => simp
  | one => simp [wt]
  | two => simp [wt]
  | three => simp only [preNormEDS'_three]; norm_num [wt, Nat.even_iff]
  | four => simp only [preNormEDS'_four]; norm_num [wt, Nat.even_iff]
  | even m ih =>
    have hO : ∀ k, 2 * k + 1 < 2 * (m + 3) → preNormEDS' (v ^ 6 * b) (v ^ 4 * c) (v ^ 6 * d)
        (2 * k + 1) = v ^ (2 * k * (k + 1)) * preNormEDS' b c d (2 * k + 1) := fun k hk ↦ by
      rw [ih _ hk, wt_odd]
    have hE : ∀ k, 2 * k + 2 < 2 * (m + 3) → preNormEDS' (v ^ 6 * b) (v ^ 4 * c) (v ^ 6 * d)
        (2 * k + 2) = v ^ (2 * k * (k + 2)) * preNormEDS' b c d (2 * k + 2) := fun k hk ↦ by
      rw [ih _ hk, wt_even]
    rw [preNormEDS'_even, preNormEDS'_even]
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [show 2 * (2 * j + 3) = 2 * (2 * j + 2) + 2 by ring, wt_even,
        show 2 * j + 3 = 2 * (j + 1) + 1 by ring, show 2 * j + 4 = 2 * (j + 1) + 2 by ring,
        show 2 * j + 5 = 2 * (j + 2) + 1 by ring, hO j (by omega), hE j (by omega),
        hO (j + 1) (by omega), hE (j + 1) (by omega), hO (j + 2) (by omega)]
      ring
    · rw [show 2 * (2 * j + 1 + 3) = 2 * (2 * j + 3) + 2 by ring, wt_even,
        show 2 * j + 1 + 1 = 2 * j + 2 by ring, show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring,
        show 2 * j + 1 + 3 = 2 * (j + 1) + 2 by ring, show 2 * j + 1 + 4 = 2 * (j + 2) + 1 by ring,
        show 2 * j + 1 + 5 = 2 * (j + 2) + 2 by ring, hE j (by omega), hO (j + 1) (by omega),
        hE (j + 1) (by omega), hO (j + 2) (by omega), hE (j + 2) (by omega)]
      ring
  | odd m ih =>
    have hO : ∀ k, 2 * k + 1 < 2 * (m + 2) + 1 → preNormEDS' (v ^ 6 * b) (v ^ 4 * c) (v ^ 6 * d)
        (2 * k + 1) = v ^ (2 * k * (k + 1)) * preNormEDS' b c d (2 * k + 1) := fun k hk ↦ by
      rw [ih _ hk, wt_odd]
    have hE : ∀ k, 2 * k + 2 < 2 * (m + 2) + 1 → preNormEDS' (v ^ 6 * b) (v ^ 4 * c) (v ^ 6 * d)
        (2 * k + 2) = v ^ (2 * k * (k + 2)) * preNormEDS' b c d (2 * k + 2) := fun k hk ↦ by
      rw [ih _ hk, wt_even]
    rw [preNormEDS'_odd, preNormEDS'_odd, wt_odd]
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
    · simp only [even_two_mul, ↓reduceIte]
      rw [show 2 * j + 3 = 2 * (j + 1) + 1 by ring, show 2 * j + 4 = 2 * (j + 1) + 2 by ring,
        hO j (by omega), hE j (by omega), hO (j + 1) (by omega), hE (j + 1) (by omega)]
      ring
    · simp only [Nat.not_even_two_mul_add_one, ↓reduceIte]
      rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring, show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring,
        show 2 * j + 1 + 3 = 2 * (j + 1) + 2 by ring, show 2 * j + 1 + 4 = 2 * (j + 2) + 1 by ring,
        hE j (by omega), hO (j + 1) (by omega), hE (j + 1) (by omega), hO (j + 2) (by omega)]
      ring

/-! ### The curves `E_N` and `E_1'` -/

/-- The curve `E_1' : y² = x³ − x` over `ℤ`; `E_N` is its quadratic twist by `−N`. -/
def E1 : WeierstrassCurve ℤ := ⟨0, 0, 0, -1, 0⟩

/-- `P_k`: the division polynomial `Φ_k` of `E_1'`, with integer coefficients. -/
noncomputable def cΦ (k : ℕ) : ℤ[X] := E1.Φ k

/-- `Q_k`: the division polynomial `ΨSq_k` of `E_1'`, with integer coefficients. -/
noncomputable def cΨSq (k : ℕ) : ℤ[X] := E1.ΨSq k

/-- `E_1'` over `ℚ`. -/
def E1Q : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

theorem E1_map : E1.map (Int.castRingHom ℚ) = E1Q := by
  simp [E1, E1Q, WeierstrassCurve.map]

/-- The substitution `X ↦ vX`. -/
noncomputable abbrev sub (v : ℚ) : ℚ[X] →+* ℚ[X] := compRingHom (C v * X)

theorem sub_Ψ₂Sq (N : ℚ) : sub (-N) (curve N).Ψ₂Sq = C (-N) ^ 3 * E1Q.Ψ₂Sq := by
  simp [Ψ₂Sq, b₂, b₄, b₆, curve, E1Q]
  ring

theorem sub_Ψ₃ (N : ℚ) : sub (-N) (curve N).Ψ₃ = C (-N) ^ 4 * E1Q.Ψ₃ := by
  simp [Ψ₃, b₂, b₄, b₆, b₈, curve, E1Q]
  ring

theorem sub_preΨ₄ (N : ℚ) : sub (-N) (curve N).preΨ₄ = C (-N) ^ 6 * E1Q.preΨ₄ := by
  simp [preΨ₄, b₂, b₄, b₆, b₈, curve, E1Q]
  ring

theorem sub_preΨ' (N : ℚ) (n : ℕ) :
    sub (-N) ((curve N).preΨ' n) = C (-N) ^ wt n * E1Q.preΨ' n := by
  rw [preΨ', map_preNormEDS', map_pow, sub_Ψ₂Sq, sub_Ψ₃, sub_preΨ₄,
    show (C (-N) ^ 3 * E1Q.Ψ₂Sq) ^ 2 = C (-N) ^ 6 * E1Q.Ψ₂Sq ^ 2 by ring, preNormEDS'_scale,
    preΨ']

theorem sub_ΨSq (N : ℚ) (n : ℕ) :
    sub (-N) ((curve N).ΨSq n) = C (-N) ^ (n ^ 2 - 1) * E1Q.ΨSq n := by
  rw [ΨSq_ofNat, ΨSq_ofNat, map_mul, map_pow, sub_preΨ', apply_ite (sub (-N)), sub_Ψ₂Sq,
    map_one]
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · rcases j with _ | j
    · simp
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, wt_even, ite_eq_left ⟨j + 1, by ring⟩,
      ite_eq_left ⟨j + 1, by ring⟩, show (2 * j + 2) ^ 2 - 1 = 2 * (2 * j * (j + 2)) + 3 by
        ring_nf; omega]
    ring
  · rw [wt_odd, ite_eq_right (Nat.not_even_two_mul_add_one j),
      ite_eq_right (Nat.not_even_two_mul_add_one j),
      show (2 * j + 1) ^ 2 - 1 = 2 * (2 * j * (j + 1)) by ring_nf; omega]
    ring

theorem sub_Φ (N : ℚ) (n : ℕ) :
    sub (-N) ((curve N).Φ n) = C (-N) ^ (n ^ 2) * E1Q.Φ n := by
  rcases n with _ | n
  · simp
  push_cast
  rw [Φ_ofNat, Φ_ofNat, map_sub, map_mul, map_mul, map_mul, map_mul, map_pow, sub_preΨ',
    sub_preΨ', sub_preΨ', apply_ite (sub (-N)), apply_ite (sub (-N)), sub_Ψ₂Sq, map_one,
    coe_compRingHom_apply, X_comp]
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · simp only [even_two_mul, ↓reduceIte]
    rcases j with _ | j
    · simp [wt]
    rw [show 2 * (j + 1) + 1 = 2 * (j + 1) + 1 from rfl, wt_odd,
      show 2 * (j + 1) + 2 = 2 * (j + 1) + 2 from rfl, wt_even, show 2 * (j + 1) = 2 * j + 2 by
        ring, wt_even]
    ring
  · simp only [Nat.not_even_two_mul_add_one, ↓reduceIte]
    rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring, wt_even,
      show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring, wt_odd, wt_odd]
    ring

/-! ### Degrees and leading coefficients -/

theorem natDegree_cΦ (k : ℕ) : (cΦ k).natDegree ≤ k ^ 2 := by
  have := E1.natDegree_Φ_le k
  rwa [Int.natAbs_natCast] at this

theorem coeff_cΦ (k : ℕ) : (cΦ k).coeff (k ^ 2) = 1 := by
  have := E1.coeff_Φ k
  rwa [Int.natAbs_natCast] at this

theorem natDegree_cΨSq_le (k : ℕ) : (cΨSq k).natDegree ≤ k ^ 2 - 1 := by
  have := E1.natDegree_ΨSq_le k
  rwa [Int.natAbs_natCast] at this

theorem natDegree_cΨSq (k : ℕ) : (cΨSq k).natDegree ≤ k ^ 2 :=
  (natDegree_cΨSq_le k).trans (Nat.sub_le _ _)

theorem coeff_cΨSq {k : ℕ} (hk : 1 ≤ k) : (cΨSq k).coeff (k ^ 2) = 0 :=
  coeff_eq_zero_of_natDegree_lt <|
    (natDegree_cΨSq_le k).trans_lt (Nat.sub_lt (by positivity) one_pos)

/-! ### Table (20) and the polynomial `Z` of Lemma 2

An entry of a triple is `A_k(G)` (label `false`) or `B_k(G)` (label `true`). With `z = t(G)`,
`P = P_k(z)` and `Q = Q_k(z)`, its abscissa `t` is `num/den` with

| | `k` odd | `k` even |
|---|---|---|
| `A_k` | `P / Q` | `−Q / P` |
| `B_k` | `(Q − P)/(Q + P)` | `(P + Q)/(P − Q)` |
-/

/-- Numerator of an entry of table (20). -/
noncomputable def num : Bool → ℕ → ℤ[X]
  | false, k => if Even k then -cΨSq k else cΦ k
  | true, k => if Even k then cΦ k + cΨSq k else cΨSq k - cΦ k

/-- Denominator of an entry of table (20). -/
noncomputable def den : Bool → ℕ → ℤ[X]
  | false, k => if Even k then cΦ k else cΨSq k
  | true, k => if Even k then cΦ k - cΨSq k else cΨSq k + cΦ k

/-- Coefficient of `z ^ k²` in the numerator; the second argument says whether `k` is even. -/
def topNum : Bool → Bool → ℤ
  | false, false => 1
  | false, true => 0
  | true, false => -1
  | true, true => 1

/-- Coefficient of `z ^ k²` in the denominator. -/
def topDen : Bool → Bool → ℤ
  | false, false => 0
  | _, _ => 1

theorem natDegree_num (L : Bool) (k : ℕ) : (num L k).natDegree ≤ k ^ 2 := by
  have h₁ := natDegree_cΦ k
  have h₂ := natDegree_cΨSq k
  cases L <;> simp only [num] <;> split_ifs <;>
    first
    | exact h₁ | exact (natDegree_neg _).le.trans h₂
    | exact natDegree_add_le_of_degree_le h₁ h₂
    | exact (natDegree_sub_le_of_le h₂ h₁).trans (max_self _).le

theorem natDegree_den (L : Bool) (k : ℕ) : (den L k).natDegree ≤ k ^ 2 := by
  have h₁ := natDegree_cΦ k
  have h₂ := natDegree_cΨSq k
  cases L <;> simp only [den] <;> split_ifs <;>
    first
    | exact h₁ | exact h₂
    | exact natDegree_add_le_of_degree_le h₂ h₁
    | exact (natDegree_sub_le_of_le h₁ h₂).trans (max_self _).le

theorem coeff_num (L : Bool) {k : ℕ} (hk : 1 ≤ k) :
    (num L k).coeff (k ^ 2) = topNum L (decide (Even k)) := by
  cases L <;> by_cases he : Even k <;>
    simp [num, topNum, he, coeff_cΦ, coeff_cΨSq hk]

theorem coeff_den (L : Bool) {k : ℕ} (hk : 1 ≤ k) :
    (den L k).coeff (k ^ 2) = topDen L (decide (Even k)) := by
  cases L <;> by_cases he : Even k <;>
    simp [den, topDen, he, coeff_cΦ, coeff_cΨSq hk]

/-- The polynomial `Z = n₁n₂d₃ + n₁n₃d₂ + n₂n₃d₁ − d₁d₂d₃` of equation (21). -/
noncomputable def bigZ (n₁ d₁ n₂ d₂ n₃ d₃ : ℤ[X]) : ℤ[X] :=
  n₁ * n₂ * d₃ + n₁ * n₃ * d₂ + n₂ * n₃ * d₁ - d₁ * d₂ * d₃

/-- The top coefficient of `Z`, from the top coefficients of the entries. -/
def topZ (a₁ b₁ a₂ b₂ a₃ b₃ : ℤ) : ℤ := a₁ * a₂ * b₃ + a₁ * a₃ * b₂ + a₂ * a₃ * b₁ - b₁ * b₂ * b₃

theorem coeff_mul_mul {p q r : ℤ[X]} {a b c : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b)
    (hr : r.natDegree ≤ c) :
    (p * q * r).coeff (a + b + c) = p.coeff a * q.coeff b * r.coeff c := by
  rw [coeff_mul_add_eq_of_natDegree_le (natDegree_mul_le_of_le hp hq) hr,
    coeff_mul_add_eq_of_natDegree_le hp hq]

theorem natDegree_mul_mul {p q r : ℤ[X]} {a b c : ℕ} (hp : p.natDegree ≤ a)
    (hq : q.natDegree ≤ b) (hr : r.natDegree ≤ c) : (p * q * r).natDegree ≤ a + b + c :=
  natDegree_mul_le_of_le (natDegree_mul_le_of_le hp hq) hr

theorem natDegree_bigZ {n₁ d₁ n₂ d₂ n₃ d₃ : ℤ[X]} {D₁ D₂ D₃ : ℕ}
    (hn₁ : n₁.natDegree ≤ D₁) (hd₁ : d₁.natDegree ≤ D₁) (hn₂ : n₂.natDegree ≤ D₂)
    (hd₂ : d₂.natDegree ≤ D₂) (hn₃ : n₃.natDegree ≤ D₃) (hd₃ : d₃.natDegree ≤ D₃) :
    (bigZ n₁ d₁ n₂ d₂ n₃ d₃).natDegree ≤ D₁ + D₂ + D₃ := by
  have e₁ : D₁ + D₂ + D₃ = D₁ + D₃ + D₂ := by ring
  have e₂ : D₁ + D₂ + D₃ = D₂ + D₃ + D₁ := by ring
  refine (natDegree_sub_le_of_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_mul_mul hn₁ hn₂ hd₃) ?_) ?_)
    (natDegree_mul_mul hd₁ hd₂ hd₃)).trans (max_self _).le
  · rw [e₁]; exact natDegree_mul_mul hn₁ hn₃ hd₂
  · rw [e₂]; exact natDegree_mul_mul hn₂ hn₃ hd₁

theorem coeff_bigZ {n₁ d₁ n₂ d₂ n₃ d₃ : ℤ[X]} {D₁ D₂ D₃ : ℕ}
    (hn₁ : n₁.natDegree ≤ D₁) (hd₁ : d₁.natDegree ≤ D₁) (hn₂ : n₂.natDegree ≤ D₂)
    (hd₂ : d₂.natDegree ≤ D₂) (hn₃ : n₃.natDegree ≤ D₃) (hd₃ : d₃.natDegree ≤ D₃) :
    (bigZ n₁ d₁ n₂ d₂ n₃ d₃).coeff (D₁ + D₂ + D₃) = topZ (n₁.coeff D₁) (d₁.coeff D₁)
      (n₂.coeff D₂) (d₂.coeff D₂) (n₃.coeff D₃) (d₃.coeff D₃) := by
  have e₁ : D₁ + D₂ + D₃ = D₁ + D₃ + D₂ := by ring
  have e₂ : D₁ + D₂ + D₃ = D₂ + D₃ + D₁ := by ring
  rw [bigZ, coeff_sub, coeff_add, coeff_add, coeff_mul_mul hn₁ hn₂ hd₃, e₁,
    coeff_mul_mul hn₁ hn₃ hd₂, ← e₁, e₂, coeff_mul_mul hn₂ hn₃ hd₁, ← e₂,
    coeff_mul_mul hd₁ hd₂ hd₃, topZ]

/-- **Rational root theorem**, in the form used in Lemma 2: a root of an integer polynomial whose
coefficient of `z ^ D` is `±1` and whose degree is at most `D` is an integer, so it is not in
`(0, 1)`. -/
theorem aeval_ne_zero_of_coeff {F : ℤ[X]} {D : ℕ} (hdeg : F.natDegree ≤ D)
    (hc : F.coeff D = 1 ∨ F.coeff D = -1) {z : ℚ} (hz0 : 0 < z) (hz1 : z < 1) :
    aeval z F ≠ 0 := by
  intro hz
  have hD : F.natDegree = D :=
    le_antisymm hdeg (le_natDegree_of_ne_zero (by rcases hc with h | h <;> rw [h] <;> decide))
  have hlc : IsUnit F.leadingCoeff := by
    rw [leadingCoeff, hD]
    rcases hc with h | h <;> rw [h] <;> simp
  obtain ⟨m, hm⟩ := IsFractionRing.isInteger_of_isUnit_den
    (isUnit_of_dvd_unit (den_dvd_of_is_root hz) hlc)
  simp only [algebraMap_int_eq, eq_intCast] at hm
  rw [← hm] at hz0 hz1
  have h0 : (0 : ℤ) < m := by exact_mod_cast hz0
  have h1 : m < (1 : ℤ) := by exact_mod_cast hz1
  omega

/-- The entries `(L₁, k₁), (L₂, k₂), (L₃, k₃)` of a triple are *excluded* by Lemma 2 when the
top coefficient of `Z` is `±1`, or when all three come from the `B` sequence. The Boolean `eᵢ`
records whether `kᵢ` is even. -/
def Excluded (L₁ e₁ L₂ e₂ L₃ e₃ : Bool) : Prop :=
  topZ (topNum L₁ e₁) (topDen L₁ e₁) (topNum L₂ e₂) (topDen L₂ e₂) (topNum L₃ e₃)
      (topDen L₃ e₃) = 1 ∨
    topZ (topNum L₁ e₁) (topDen L₁ e₁) (topNum L₂ e₂) (topDen L₂ e₂) (topNum L₃ e₃)
      (topDen L₃ e₃) = -1 ∨
    (L₁ = true ∧ L₂ = true ∧ L₃ = true)

instance (L₁ e₁ L₂ e₂ L₃ e₃ : Bool) : Decidable (Excluded L₁ e₁ L₂ e₂ L₃ e₃) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The `B` entries have `num ≡ den` modulo `2`: `den = num + 2 • gap`. -/
noncomputable def gap (k : ℕ) : ℤ[X] := if Even k then -cΨSq k else cΦ k

theorem den_true (k : ℕ) : den true k = num true k + 2 * gap k := by
  by_cases h : Even k <;> simp [den, num, gap, h] <;> ring

theorem natDegree_gap (k : ℕ) : (gap k).natDegree ≤ k ^ 2 := by
  unfold gap
  split_ifs
  · exact (natDegree_neg _).le.trans (natDegree_cΨSq k)
  · exact natDegree_cΦ k

/-- **Asiryan, Lemma 2**, polynomial core: for an excluded triple, `Z` has no root in `(0, 1)`. -/
theorem aeval_bigZ_ne_zero {L₁ L₂ L₃ : Bool} {k₁ k₂ k₃ : ℕ} (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂)
    (h₃ : 1 ≤ k₃) (hex : Excluded L₁ (decide (Even k₁)) L₂ (decide (Even k₂)) L₃
      (decide (Even k₃))) {z : ℚ} (hz0 : 0 < z) (hz1 : z < 1) :
    aeval z (bigZ (num L₁ k₁) (den L₁ k₁) (num L₂ k₂) (den L₂ k₂) (num L₃ k₃) (den L₃ k₃)) ≠
      0 := by
  have hdeg := natDegree_bigZ (natDegree_num L₁ k₁) (natDegree_den L₁ k₁) (natDegree_num L₂ k₂)
    (natDegree_den L₂ k₂) (natDegree_num L₃ k₃) (natDegree_den L₃ k₃)
  have hco := coeff_bigZ (natDegree_num L₁ k₁) (natDegree_den L₁ k₁) (natDegree_num L₂ k₂)
    (natDegree_den L₂ k₂) (natDegree_num L₃ k₃) (natDegree_den L₃ k₃)
  rw [coeff_num _ h₁, coeff_den _ h₁, coeff_num _ h₂, coeff_den _ h₂, coeff_num _ h₃,
    coeff_den _ h₃] at hco
  rcases hex with hex | hex | ⟨rfl, rfl, rfl⟩
  · exact aeval_ne_zero_of_coeff hdeg (.inl (hco.trans hex)) hz0 hz1
  · exact aeval_ne_zero_of_coeff hdeg (.inr (hco.trans hex)) hz0 hz1
  -- all three from `B`: `Z = 2W` and the top coefficient of `W` is `±1`
  set n₁ := num true k₁
  set n₂ := num true k₂
  set n₃ := num true k₃
  set g₁ := gap k₁
  set g₂ := gap k₂
  set g₃ := gap k₃
  set W := n₁ * n₂ * n₃ - 2 * (g₁ * g₂ * n₃ + g₁ * n₂ * g₃ + n₁ * g₂ * g₃) - 4 * (g₁ * g₂ * g₃)
  have hZW : bigZ n₁ (den true k₁) n₂ (den true k₂) n₃ (den true k₃) = 2 * W := by
    rw [den_true, den_true, den_true, bigZ]
    ring
  rw [hZW] at hdeg hco ⊢
  have hcoeff2 : ∀ j, (2 * W).coeff j = 2 * W.coeff j := fun j ↦ by
    rw [show (2 : ℤ[X]) = C 2 by rfl, coeff_C_mul]
  have hWdeg : W.natDegree ≤ k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    have := coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hj)
    rw [hcoeff2] at this
    omega
  rw [hcoeff2] at hco
  rw [map_mul, mul_ne_zero_iff]
  refine ⟨by rw [show (2 : ℤ[X]) = C 2 by rfl, aeval_C]; norm_num,
    aeval_ne_zero_of_coeff hWdeg ?_ hz0 hz1⟩
  revert hco
  cases decide (Even k₁) <;> cases decide (Even k₂) <;> cases decide (Even k₃) <;>
    simp [topZ, topNum, topDen] <;> omega

end PerfectCuboid.CongruentRank
