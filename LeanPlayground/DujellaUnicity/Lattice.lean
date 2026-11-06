import Mathlib

/-!
# Dujella unicity: the lattice step

Pure combinatorics on `ℤ × ℤ`. `S` is the group of "direction vectors" of `{2,p}`-smooth
elements of `ℤ[√(k²+1)]`, `k = 2^(A+1) p^m`; `E = (2A, 2m)` is the vector of `√d - 1`.
The weight of `u` is `M u = 2^|u.1| * p^|u.2|`.
-/

namespace DujellaUnicity

/-- Weight of a direction vector. -/
def wt (p : ℕ) (u : ℤ × ℤ) : ℕ := 2 ^ u.1.natAbs * p ^ u.2.natAbs

/-- A *solution vector*: even, in the box `|u.1| ≤ 2A`, `|u.2| ≤ 2m`, and not `0, ±E`. -/
def IsSolVec (A m : ℕ) (u : ℤ × ℤ) : Prop :=
  Even u.1 ∧ Even u.2 ∧ |u.1| ≤ 2 * A ∧ |u.2| ≤ 2 * m ∧ u ≠ 0 ∧
    u ≠ ((2 * A : ℤ), (2 * m : ℤ)) ∧ u ≠ (-(2 * A : ℤ), -(2 * m : ℤ))

lemma wt_add (p : ℕ) (x y : ℤ × ℤ) (h1 : (0 ≤ x.1 ∧ 0 ≤ y.1) ∨ (x.1 ≤ 0 ∧ y.1 ≤ 0))
    (h2 : (0 ≤ x.2 ∧ 0 ≤ y.2) ∨ (x.2 ≤ 0 ∧ y.2 ≤ 0)) :
    wt p (x + y) = wt p x * wt p y := by
  have e1 : (x + y).1.natAbs = x.1.natAbs + y.1.natAbs := by
    simp only [Prod.fst_add]; omega
  have e2 : (x + y).2.natAbs = x.2.natAbs + y.2.natAbs := by
    simp only [Prod.snd_add]; omega
  unfold wt; rw [e1, e2, pow_add, pow_add]; ring

lemma wt_le (A m p : ℕ) (hp : 1 ≤ p) (z : ℤ × ℤ) (h1 : z.1.natAbs ≤ 2 * A)
    (h2 : z.2.natAbs ≤ 2 * m) : wt p z ≤ (2 ^ A * p ^ m) ^ 2 := by
  have : (2 ^ A * p ^ m) ^ 2 = 2 ^ (2 * A) * p ^ (2 * m) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm A, mul_comm m]
  rw [this]; unfold wt
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) h1) (Nat.pow_le_pow_right hp h2)

lemma no_split (K a b c : ℕ) (ha : K < a) (hb : K < b) (hc : c ≤ K ^ 2) (h : c = a * b) :
    False := by
  have := Nat.mul_lt_mul'' ha hb
  rw [sq] at hc; omega

lemma big_of_key (A m p : ℕ) (S : AddSubgroup (ℤ × ℤ))
    (hkey : ∀ u ∈ S, u = 0 ∨ u = ((A : ℤ), (m : ℤ)) ∨ u = (-(A : ℤ), -(m : ℤ)) ∨
      2 ^ A * p ^ m < wt p u)
    (x : ℤ × ℤ) (hx : x ∈ S) (h0 : x.1 ≠ 0 ∨ x.2 ≠ 0) (h1 : x.1 ≠ A ∨ x.2 ≠ m)
    (h2 : x.1 ≠ -A ∨ x.2 ≠ -m) : 2 ^ A * p ^ m < wt p x := by
  rcases hkey x hx with h | h | h | h
  · subst h; simp at h0
  · subst h; simp at h1
  · subst h; simp at h2
  · exact h

lemma solvec_coords {A m : ℕ} {u : ℤ × ℤ} (h : IsSolVec A m u) :
    u.1 % 2 = 0 ∧ u.2 % 2 = 0 ∧ -(2 * A : ℤ) ≤ u.1 ∧ u.1 ≤ 2 * A ∧
    -(2 * m : ℤ) ≤ u.2 ∧ u.2 ≤ 2 * m ∧ (u.1 ≠ 0 ∨ u.2 ≠ 0) ∧
    (u.1 ≠ 2 * A ∨ u.2 ≠ 2 * m) ∧ (u.1 ≠ -(2 * A) ∨ u.2 ≠ -(2 * m)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  obtain ⟨a3, b3⟩ := abs_le.mp h3
  obtain ⟨a4, b4⟩ := abs_le.mp h4
  refine ⟨Int.even_iff.mp h1, Int.even_iff.mp h2, a3, b3, a4, b4, ?_, ?_, ?_⟩
  · by_contra hc; push Not at hc; exact h5 (Prod.ext hc.1 hc.2)
  · by_contra hc; push Not at hc; exact h6 (Prod.ext hc.1 hc.2)
  · by_contra hc; push Not at hc; exact h7 (Prod.ext hc.1 hc.2)

lemma solvec_neg {A m : ℕ} {u : ℤ × ℤ} (h : IsSolVec A m u) : IsSolVec A m (-u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h1.neg
  · simpa using h2.neg
  · simpa using h3
  · simpa using h4
  · simpa using h5
  · intro hc; apply h7; rw [← neg_neg u, hc]; simp
  · intro hc; apply h6; rw [← neg_neg u, hc]; simp

theorem lattice_main (A m p : ℕ) (hA : 1 ≤ A) (hm : 1 ≤ m) (hp : 2 ≤ p)
    (hpar : ¬ (Even A ∧ Even m))
    (S : AddSubgroup (ℤ × ℤ)) (hE : ((2 * A : ℤ), (2 * m : ℤ)) ∈ S)
    (hkey : ∀ u ∈ S, u = 0 ∨ u = ((A : ℤ), (m : ℤ)) ∨ u = (-(A : ℤ), -(m : ℤ)) ∨
      2 ^ A * p ^ m < wt p u)
    (v w : ℤ × ℤ) (hv : v ∈ S) (hw : w ∈ S) (hvs : IsSolVec A m v) (hws : IsSolVec A m w) :
    v = w ∨ v = -w := by
  have hp1 : 1 ≤ p := by omega
  have hpar' : A % 2 = 1 ∨ m % 2 = 1 := by
    rw [Nat.even_iff, Nat.even_iff] at hpar; omega
  have hsplit : ∀ x y z : ℤ × ℤ, x ∈ S → y ∈ S → x + y = z →
      ((0 ≤ x.1 ∧ 0 ≤ y.1) ∨ (x.1 ≤ 0 ∧ y.1 ≤ 0)) →
      ((0 ≤ x.2 ∧ 0 ≤ y.2) ∨ (x.2 ≤ 0 ∧ y.2 ≤ 0)) →
      -(2 * A : ℤ) ≤ z.1 → z.1 ≤ 2 * A → -(2 * m : ℤ) ≤ z.2 → z.2 ≤ 2 * m →
      (x.1 ≠ 0 ∨ x.2 ≠ 0) → (x.1 ≠ A ∨ x.2 ≠ m) → (x.1 ≠ -A ∨ x.2 ≠ -m) →
      (y.1 ≠ 0 ∨ y.2 ≠ 0) → (y.1 ≠ A ∨ y.2 ≠ m) → (y.1 ≠ -A ∨ y.2 ≠ -m) → False := by
    intro x y z hx hy hxy s1 s2 b1 b2 b3 b4 x0 x1 x2 y0 y1 y2
    have e := wt_add p x y s1 s2
    rw [hxy] at e
    exact no_split _ _ _ _ (big_of_key A m p S hkey x hx x0 x1 x2)
      (big_of_key A m p S hkey y hy y0 y1 y2) (wt_le A m p hp1 z (by omega) (by omega)) e
  -- Step 1: solution vectors are mixed.
  have hmixed : ∀ u ∈ S, IsSolVec A m u → (0 < u.1 ∧ u.2 < 0) ∨ (u.1 < 0 ∧ 0 < u.2) := by
    have pos : ∀ u ∈ S, IsSolVec A m u → ¬ (0 ≤ u.1 ∧ 0 ≤ u.2) := by
      rintro u hu hus ⟨h1, h2⟩
      obtain ⟨e1, e2, c1, c2, c3, c4, n0, nE, nE'⟩ := solvec_coords hus
      refine hsplit u (((2 * A : ℤ), (2 * m : ℤ)) - u) ((2 * A : ℤ), (2 * m : ℤ)) hu
        (S.sub_mem hE hu) (by abel) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        (try simp only [Prod.fst_sub, Prod.snd_sub]) <;> omega
    intro u hu hus
    have h1 := pos u hu hus
    have h2 := pos (-u) (S.neg_mem hu) (solvec_neg hus)
    simp only [Prod.fst_neg, Prod.snd_neg] at h2
    omega
  -- Step 2: two solution vectors with positive first coordinate coincide.
  have hQ : ∀ v ∈ S, ∀ w ∈ S, IsSolVec A m v → IsSolVec A m w → 0 < v.1 → 0 < w.1 →
      v.1 ≤ w.1 → v = w := by
    intro v hv w hw hvs hws hv1 hw1 hle
    have mv := hmixed v hv hvs
    have mw := hmixed w hw hws
    obtain ⟨ve1, ve2, vc1, vc2, vc3, vc4, -, -, -⟩ := solvec_coords hvs
    obtain ⟨we1, we2, wc1, wc2, wc3, wc4, -, -, -⟩ := solvec_coords hws
    by_contra hne
    have hne' : v.1 ≠ w.1 ∨ v.2 ≠ w.2 := by
      by_contra hc; push Not at hc; exact hne (Prod.ext hc.1 hc.2)
    rcases le_or_gt w.2 v.2 with h | h
    · -- domination: w = v + (w - v) with the same sign pattern
      refine hsplit v (w - v) w hv (S.sub_mem hw hv) (by abel)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        (try simp only [Prod.fst_sub, Prod.snd_sub]) <;> omega
    · -- crossing: E = (w - v) + (E - (w - v)), both nonnegative
      refine hsplit (w - v) (((2 * A : ℤ), (2 * m : ℤ)) - (w - v)) ((2 * A : ℤ), (2 * m : ℤ))
        (S.sub_mem hw hv) (S.sub_mem hE (S.sub_mem hw hv)) (by abel)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        (try simp only [Prod.fst_sub, Prod.snd_sub]) <;> omega
  have hP : ∀ v ∈ S, ∀ w ∈ S, IsSolVec A m v → IsSolVec A m w → 0 < v.1 → 0 < w.1 →
      v = w := by
    intro v hv w hw hvs hws h1 h2
    rcases le_total v.1 w.1 with h | h
    · exact hQ v hv w hw hvs hws h1 h2 h
    · exact (hQ w hw v hv hws hvs h2 h1 h).symm
  have mv := hmixed v hv hvs
  have mw := hmixed w hw hws
  have hnv := S.neg_mem hv
  have hnw := S.neg_mem hw
  have snv := solvec_neg hvs
  have snw := solvec_neg hws
  rcases lt_or_gt_of_ne (show v.1 ≠ 0 by omega) with h1 | h1 <;>
    rcases lt_or_gt_of_ne (show w.1 ≠ 0 by omega) with h2 | h2
  · left
    have := hP (-v) hnv (-w) hnw snv snw (by simp only [Prod.fst_neg]; omega)
      (by simp only [Prod.fst_neg]; omega)
    simpa using this
  · right
    have := hP (-v) hnv w hw snv hws (by simp only [Prod.fst_neg]; omega) h2
    rw [← this]; simp
  · right
    exact hP v hv (-w) hnw hvs snw h1 (by simp only [Prod.fst_neg]; omega)
  · left
    exact hP v hv w hw hvs hws h1 h2

end DujellaUnicity
