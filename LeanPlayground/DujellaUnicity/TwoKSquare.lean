import LeanPlayground.DujellaUnicity.Main
import LeanPlayground.DujellaUnicity.LatticeSquare

/-!
# Dujella's unicity conjecture for `k = 2^a p^m` when `2k` is a square

`dujella_unicity` (PR #64) needs `2k` not a square. When `2k = 4g²` is a square
(`a` odd, `m` even), the equation `x² - (k²+1) y² = k²` has the extra solution
`(x, y) = ((k+1) g, g)`, and the direction vector `H = (a-1, m)` of `k - 1 + √d` is itself a
solution vector, so the lattice argument breaks down.

Main results:

* `two_k_square_solution`: `((k+1)g, g)` is a solution with `0 < g < k - 1`.
* `dujella_at_most_three`: for every `k = 2^a p^m` (`a ≥ 2`, `m ≥ 1`) there are at most three
  solutions with `0 < y < k - 1`. Proof: the halves of solution vectors lie in
  `{w | 2w ∈ S}`, which has at most four classes modulo `S`; the class of `0` holds no
  solution and every other class holds at most one.
* `dujella_two_k_square`: if `2k` is a square and some `{2,p}`-smooth norm
  `x² - (k²+1) y² = ±2^i p^j` has `i` or `j` odd, then `((k+1)g, g)` is the only solution.
  The odd norm puts an odd vector in `S`, so `{w | 2w ∈ S} / S` has two elements.
-/

namespace DujellaUnicity

open PadicInt

/-- The extra solution when `2k = (2g)²`. -/
theorem two_k_square_solution {g : ℤ} (hg : 2 ≤ g) :
    ((2 * g ^ 2 + 1) * g) ^ 2 - ((2 * g ^ 2) ^ 2 + 1) * g ^ 2 = (2 * g ^ 2) ^ 2 ∧
      0 < g ∧ g < 2 * g ^ 2 - 1 := by
  refine ⟨by ring, by omega, by nlinarith⟩

section Package

set_option linter.unusedSectionVars false

variable {p : ℕ} [hpF : Fact p.Prime] {k : ℤ} {a m : ℕ}

/-- A solution `s = (x, y)` in the range of the conjecture. -/
def Valid (k : ℤ) (s : ℤ × ℤ) : Prop :=
  0 < s.1 ∧ 0 < s.2 ∧ s.2 < k - 1 ∧ s.1 ^ 2 - (k ^ 2 + 1) * s.2 ^ 2 = k ^ 2

/-- Everything the lattice step needs, packaged: the group `S` of direction vectors, the
relation `R s v` "the solution `s` has direction vector `v`", and their properties. -/
theorem package (hp2 : p ≠ 2) (ha : 2 ≤ a) (hm : 1 ≤ m) (hk : k = 2 ^ a * p ^ m) :
    ∃ (S : AddSubgroup (ℤ × ℤ)) (R : ℤ × ℤ → ℤ × ℤ → Prop),
      ((2 * (a - 1 : ℕ) : ℤ), (2 * m : ℤ)) ∈ S ∧
      (((a - 1 : ℕ) : ℤ), (m : ℤ)) ∈ S ∧
      (∀ u ∈ S, u = 0 ∨ u = (((a - 1 : ℕ) : ℤ), (m : ℤ)) ∨
        u = (-((a - 1 : ℕ) : ℤ), -(m : ℤ)) ∨ 2 ^ (a - 1) * p ^ m < wt p u) ∧
      (∀ s, Valid k s → ∃ v ∈ S, IsSolVec (a - 1) m v ∧ R s v) ∧
      (∀ s₁ s₂ v₁ v₂, Valid k s₁ → Valid k s₂ → R s₁ v₁ → R s₂ v₂ →
        (v₁ = v₂ ∨ v₁ = -v₂) → s₁ = s₂) ∧
      (∀ g : ℤ, 0 < g → k = 2 * g ^ 2 →
        R ((k + 1) * g, g) (-((a - 1 : ℕ) : ℤ), -(m : ℤ))) ∧
      (∀ γ : ℤ√(k ^ 2 + 1), ∀ i j : ℕ, γ.norm.natAbs = 2 ^ i * p ^ j → (Odd i ∨ Odd j) →
        ∃ o ∈ S, Odd o.1 ∨ Odd o.2) := by
  have hk0 := k_pos hk
  have hns := nonsquare k hk0
  obtain ⟨l2, hl2, h4⟩ := exists_sqrt_two (q := 2) rfl k (four_dvd_k hk ha)
  obtain ⟨lp, hlp, hp1⟩ := exists_sqrt_odd (q := p) hp2 k (p_dvd_k hk hm)
  have hcast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ a)]; ring
  let S : AddSubgroup (ℤ × ℤ) :=
    { carrier := {u | ∃ γ, Smooth p γ ∧ V l2 hl2 lp hlp γ = u}
      zero_mem' := ⟨1, smooth_one, by
        unfold V; simpa using ⟨dir_intCast l2 hl2 1, dir_intCast lp hlp 1⟩⟩
      add_mem' := by
        rintro _ _ ⟨γ, hγ, rfl⟩ ⟨δ, hδ, rfl⟩
        exact ⟨γ * δ, smooth_mul hns hγ hδ, V_mul l2 hl2 lp hlp hns hγ.1 hδ.1⟩
      neg_mem' := by
        rintro _ ⟨γ, hγ, rfl⟩
        exact ⟨star γ, smooth_star hγ, V_star l2 hl2 lp hlp γ⟩ }
  let R : ℤ × ℤ → ℤ × ℤ → Prop := fun s v =>
    ∃ g t : ℤ, ∃ α : ℤ√(k ^ 2 + 1), 0 < t ∧ k = g * t ∧ s.1 = g * α.re ∧ s.2 = g * α.im ∧
      α.norm = t ^ 2 ∧ V l2 hl2 lp hlp α = v
  refine ⟨S, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `E`
    refine ⟨⟨-1, 1⟩, ⟨ne_zero_of_im, 2 * a, 2 * m, by
      rw [norm_E, Int.natAbs_neg, natAbs_k_sq hk]⟩, ?_⟩
    unfold V; rw [dir2_E l2 hl2 hp2 hk h4, dirp_E lp hlp hp2 hk hm hp1, hcast]
    ext <;> simp
    ring
  · -- `H`, the direction of `k - 1 + √d`
    refine ⟨⟨k - 1, 1⟩, ⟨ne_zero_of_im, a + 1, m, by
      rw [norm_minus, Int.natAbs_neg, natAbs_two_mul_k hk]⟩, ?_⟩
    unfold V; rw [dir2_minus l2 hl2 hp2 hk ha h4, dirp_minus lp hlp hp2 hk hm hp1, hcast]
  · rintro _ ⟨γ, hγ, rfl⟩
    exact key l2 hl2 lp hlp hp2 hk ha hm h4 hp1 hγ
  · rintro ⟨x, y⟩ ⟨hx, hy, hyk, h⟩
    obtain ⟨g, t, α, ht, hkt, hxg, hyg, hN, hsm, hv⟩ :=
      sol_vec l2 hl2 lp hlp hp2 hk ha hm h4 hp1 hx hy hyk h
    exact ⟨_, ⟨α, hsm, rfl⟩, hv, g, t, α, ht, hkt, hxg, hyg, hN, rfl⟩
  · rintro ⟨x1, y1⟩ ⟨x2, y2⟩ v₁ v₂ ⟨hx1, hy1, hy1k, h1⟩ ⟨hx2, hy2, hy2k, h2⟩
      ⟨g1, t1, α1, ht1, hkt1, hx1g, hy1g, hN1, rfl⟩ ⟨g2, t2, α2, ht2, hkt2, hx2g, hy2g, hN2, rfl⟩
      hrel
    obtain ⟨e1, e2⟩ := uniq l2 hl2 lp hlp hp2 hk ha h4 hp1 hx1 hx2 hy1 hy2 (by omega)
      (by omega) h1 h2 ht1 hkt1 hx1g hy1g hN1 ht2 hkt2 hx2g hy2g hN2 hrel
    exact Prod.ext e1 e2
  · intro g hg hkg
    refine ⟨g, 2 * g, ⟨k + 1, 1⟩, by omega, by rw [hkg]; ring, by simp [mul_comm], by simp, ?_, ?_⟩
    · rw [norm_plus, hkg]; ring
    · unfold V
      rw [dir2_plus l2 hl2 hp2 hk ha h4, dirp_plus lp hlp hp2 hk hm hp1, hcast]
      ext <;> simp
  · intro γ i j hN hodd
    have hγ : γ ≠ 0 := by
      intro h0; rw [h0, Zsqrtd.norm_zero] at hN
      have hp0 := hpF.out.pos
      have : 0 < 2 ^ i * p ^ j := by positivity
      rw [← hN] at this; simp at this
    refine ⟨V l2 hl2 lp hlp γ, ⟨γ, ⟨hγ, i, j, hN⟩, rfl⟩, ?_⟩
    unfold V; simp only
    rw [dir_eq_of_vP l2 hl2 hns hγ, dir_eq_of_vP lp hlp hns hγ, pv2 hp2 hN, pvp hp2 hN]
    rcases hodd with ⟨r, hr⟩ | ⟨r, hr⟩
    · left; exact ⟨(vP l2 hl2 γ : ℤ) - r - 1, by rw [hr]; push_cast; ring⟩
    · right; exact ⟨(vP lp hlp γ : ℤ) - r - 1, by rw [hr]; push_cast; ring⟩

end Package

/-- A solution vector is even, so it is `w + w`. -/
theorem solvec_half {A m : ℕ} {v : ℤ × ℤ} (h : IsSolVec A m v) :
    ∃ w : ℤ × ℤ, v = w + w := by
  obtain ⟨⟨r, hr⟩, ⟨s, hs⟩, -⟩ := h
  exact ⟨(r, s), Prod.ext hr hs⟩

set_option linter.flexible false in
/-- **At most three solutions.** For `k = 2^a p^m` (`p` an odd prime, `a ≥ 2`, `m ≥ 1`), among
any four solutions of `x² - (k²+1) y² = k²` with `x, y > 0`, `y < k - 1`, two coincide. -/
theorem dujella_at_most_three {p a m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 2 ≤ a)
    (hm : 1 ≤ m) {k : ℤ} (hk : k = 2 ^ a * p ^ m) (s : Fin 4 → ℤ × ℤ)
    (hs : ∀ i, 0 < (s i).1 ∧ 0 < (s i).2 ∧ (s i).2 < k - 1 ∧
      (s i).1 ^ 2 - (k ^ 2 + 1) * (s i).2 ^ 2 = k ^ 2) :
    ∃ i j, i ≠ j ∧ s i = s j := by
  have := Fact.mk hp
  obtain ⟨S, R, hE, -, hkey, hsol, huniq, -, -⟩ := package (p := p) hp2 ha hm hk
  have hA : 1 ≤ a - 1 := by omega
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hE' : ((2 * (a - 1 : ℕ) : ℤ), (2 * m : ℤ)) ∈ S := hE
  choose v hvS hvs hR using fun i => hsol (s i) (hs i)
  choose w hw using fun i => solvec_half (hvs i)
  by_contra hcon
  push Not at hcon
  have hwS : ∀ i, w i + w i ∈ S := fun i => hw i ▸ hvS i
  have hws : ∀ i, IsSolVec (a - 1) m (w i + w i) := fun i => hw i ▸ hvs i
  -- distinct solutions have direction vectors that differ up to sign
  have hdist : ∀ i j, i ≠ j → w i - w j ∈ S → False := by
    intro i j hij hd
    rcases class_uniq (a - 1) m p hA hm hp1 S (by exact_mod_cast hE') hkey (hwS i) (hwS j)
      (hws i) (hws j) hd with h | h
    · exact hcon i j hij (huniq _ _ _ _ (hs i) (hs j) (hR i) (hR j)
        (Or.inl (by rw [hw i, hw j, h])))
    · exact hcon i j hij (huniq _ _ _ _ (hs i) (hs j) (hR i) (hR j)
        (Or.inr (by rw [hw i, hw j, h]; abel)))
  have hnot : ∀ i, w i ∈ S → False := fun i h =>
    not_half (a - 1) m p hp1 S hkey h (hws i)
  obtain ⟨i, j, hij, z, hz, e⟩ := half_pigeon S ![0, w 0, w 1, w 2, w 3] (by
    intro i; fin_cases i
    · exact (half S).zero_mem
    all_goals exact hwS _)
  rw [mem_half] at hz
  have hD := e ▸ hz
  fin_cases i <;> fin_cases j <;> simp at hij hD
  all_goals first
    | exact hnot _ hD
    | exact hdist _ _ (by decide) hD

/-- **Dujella's unicity conjecture when `2k` is a square, under an odd-norm hypothesis.**
Let `p` be an odd prime, `a ≥ 3` odd, `m ≥ 2` even, `k = 2^a p^m = 2g²`. Suppose some
`γ ∈ ℤ[√(k²+1)]` has norm `±2^i p^j` with `i` or `j` odd. Then `((k+1)g, g)` is the only
solution of `x² - (k²+1) y² = k²` with `x, y > 0` and `y < k - 1`. -/
theorem dujella_two_k_square {p a m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 3 ≤ a)
    (haodd : Odd a) (hm : 2 ≤ m) (hmeven : Even m) {k : ℤ} (hk : k = 2 ^ a * p ^ m) {g : ℤ}
    (hg : 0 < g) (hkg : k = 2 * g ^ 2)
    (hodd : ∃ γ : ℤ√(k ^ 2 + 1), ∃ i j : ℕ, γ.norm.natAbs = 2 ^ i * p ^ j ∧ (Odd i ∨ Odd j))
    {x y : ℤ} (hx : 0 < x) (hy : 0 < y) (hyk : y < k - 1)
    (h : x ^ 2 - (k ^ 2 + 1) * y ^ 2 = k ^ 2) : x = (k + 1) * g ∧ y = g := by
  have := Fact.mk hp
  obtain ⟨S, R, hE, hH, hkey, hsol, huniq, hR0, hoddS⟩ := package (p := p) hp2 (by omega) (by omega) hk
  have hA : 1 ≤ a - 1 := by omega
  have hp1 : 1 ≤ p := hp.one_lt.le
  obtain ⟨A2, hA2⟩ : ∃ A2 : ℕ, a - 1 = A2 + A2 := by
    obtain ⟨r, hr⟩ := haodd; exact ⟨r, by omega⟩
  obtain ⟨m2, hm2⟩ := hmeven
  set h0 : ℤ × ℤ := ((A2 : ℤ), (m2 : ℤ)) with hh0
  have hhH : h0 + h0 = (((a - 1 : ℕ) : ℤ), (m : ℤ)) := by
    rw [hh0]; ext <;> simp <;> push_cast [hA2, hm2] <;> ring
  -- `h0 ∉ S`: its weight is too small
  have hh0S : h0 ∉ S := by
    intro hmem
    rcases hkey h0 hmem with e | e | e | e
    · simp [hh0, Prod.ext_iff] at e; omega
    · simp [hh0, Prod.ext_iff] at e; omega
    · simp [hh0, Prod.ext_iff] at e; omega
    · have : wt p h0 ≤ 2 ^ (a - 1) * p ^ m := by
        unfold wt; simp only [hh0, Int.natAbs_natCast]
        exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
          (Nat.pow_le_pow_right hp1 (by omega))
      omega
  have hHs : IsSolVec (a - 1) m (h0 + h0) := by
    rw [hhH]
    refine ⟨⟨A2, by push_cast [hA2]; ring⟩, ⟨m2, by push_cast [hm2]; ring⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [abs_of_nonneg (by positivity)]; omega
    · rw [abs_of_nonneg (by positivity)]; omega
    · simp [Prod.ext_iff]; omega
    · simp [Prod.ext_iff]; omega
    · simp [Prod.ext_iff]; omega
  have hh0S2 : h0 + h0 ∈ S := hhH ▸ hH
  -- the given solution and its half
  obtain ⟨v, hvS, hvs, hRv⟩ := hsol (x, y) ⟨hx, hy, hyk, h⟩
  obtain ⟨w, rfl⟩ := solvec_half hvs
  obtain ⟨γ, i, j, hN, hij⟩ := hodd
  obtain ⟨o, ho, hoo⟩ := hoddS γ i j hN hij
  rcases half_rank_one S ho hoo (h := h0) hh0S2 hh0S (w := w) hvS with hw | hw
  · exact (not_half (a - 1) m p hp1 S hkey hw hvs).elim
  have hcl := class_uniq (a - 1) m p hA (by omega) hp1 S (by exact_mod_cast hE) hkey hvS
    hh0S2 hvs hHs hw
  have hk4 : (4 : ℤ) ∣ k := four_dvd_k hk (by omega)
  have hg2 : 2 ≤ g := by
    by_contra hlt
    have : g = 1 := by omega
    rw [this] at hkg; omega
  have hvalid0 : Valid k ((k + 1) * g, g) := by
    refine ⟨by nlinarith, hg, ?_, ?_⟩
    · show g < k - 1
      nlinarith
    · show ((k + 1) * g) ^ 2 - (k ^ 2 + 1) * g ^ 2 = k ^ 2
      rw [hkg]; ring
  have := huniq (x, y) _ (w + w) _ ⟨hx, hy, hyk, h⟩ hvalid0 hRv (hR0 g hg hkg) (by
    rcases hcl with e | e
    · right; rw [e, hhH]; ext <;> simp
    · left; rw [e, ← neg_add, hhH]; ext <;> simp)
  simp only [Prod.ext_iff] at this
  exact this

/-- `k = 968 = 2³·11²`: `22263² - (968²+1)·23² = -2¹²·11` has an odd exponent, so `(21318, 22)`
is the only solution. -/
example {x y : ℤ} (hx : 0 < x) (hy : 0 < y) (hyk : y < 968 - 1)
    (h : x ^ 2 - (968 ^ 2 + 1) * y ^ 2 = 968 ^ 2) : x = 21318 ∧ y = 22 := by
  have := dujella_two_k_square (p := 11) (a := 3) (m := 2) (by norm_num) (by norm_num) le_rfl
    (by decide) le_rfl (by decide) (k := 968) (by norm_num) (g := 22) (by norm_num) (by norm_num)
    ⟨⟨22263, 23⟩, 12, 1, by rw [Zsqrtd.norm_def]; norm_num, Or.inr (by decide)⟩ hx hy hyk h
  norm_num at this; exact this

/-- `k = 288 = 2⁵·3²`: `929381² - (288²+1)·3227² = -2⁹·3⁷`, so `(3468, 12)` is the only
solution. -/
example {x y : ℤ} (hx : 0 < x) (hy : 0 < y) (hyk : y < 288 - 1)
    (h : x ^ 2 - (288 ^ 2 + 1) * y ^ 2 = 288 ^ 2) : x = 3468 ∧ y = 12 := by
  have := dujella_two_k_square (p := 3) (a := 5) (m := 2) (by norm_num) (by norm_num)
    (by norm_num) (by decide) le_rfl (by decide) (k := 288) (by norm_num) (g := 12) (by norm_num)
    (by norm_num) ⟨⟨929381, 3227⟩, 9, 7, by rw [Zsqrtd.norm_def]; norm_num, Or.inl (by decide)⟩
    hx hy hyk h
  norm_num at this; exact this

end DujellaUnicity
