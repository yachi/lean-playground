import LeanPlayground.DujellaUnicity.Lattice

/-!
# Dujella unicity: the lattice step when `2k` is a square

`S ⊆ ℤ × ℤ` is the group of direction vectors of `{2,p}`-smooth elements,
`H = (A, m)` the direction of `k - 1 + √d` and `E = 2H` that of `√d - 1`.
A solution vector `v` is even, so `v = w + w`. When `2k` is a square, `H` itself is a
solution vector (of the extra solution `y = √(k/2)`), and the argument of `lattice_main` breaks.

Here we work with the halves `w`:

* `not_half`: `w ∉ S`;
* `class_uniq`: if `w₀ - w₁ ∈ S` then `w₀ = ± w₁` (one solution per class of `{w | 2w ∈ S} / S`);
* `half_pigeon`: among five elements of `{w | 2w ∈ S}` two differ by `2z` with `2z ∈ S`,
  since that group is free of rank `≤ 2`.
-/

namespace DujellaUnicity

/-- The group of `w` with `2w ∈ S`. -/
def half (S : AddSubgroup (ℤ × ℤ)) : AddSubgroup (ℤ × ℤ) where
  carrier := {w | w + w ∈ S}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    have := S.add_mem hx hy
    convert this using 1; abel
  neg_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at *
    have := S.neg_mem hx
    convert this using 1; abel

lemma mem_half {S : AddSubgroup (ℤ × ℤ)} {w : ℤ × ℤ} : w ∈ half S ↔ w + w ∈ S := Iff.rfl

lemma big_of_key' (A m p : ℕ) (S : AddSubgroup (ℤ × ℤ))
    (hkey : ∀ u ∈ S, u = 0 ∨ u = ((A : ℤ), (m : ℤ)) ∨ u = (-(A : ℤ), -(m : ℤ)) ∨
      2 ^ A * p ^ m < wt p u)
    {x : ℤ × ℤ} (hx : x ∈ S) (h0 : x ≠ 0) (h1 : x ≠ ((A : ℤ), (m : ℤ)))
    (h2 : x ≠ (-(A : ℤ), -(m : ℤ))) : 2 ^ A * p ^ m < wt p x := by
  rcases hkey x hx with h | h | h | h
  · exact absurd h h0
  · exact absurd h h1
  · exact absurd h h2
  · exact h

lemma wt_pm (A m p : ℕ) (hp : 1 ≤ p) (u w : ℤ × ℤ)
    (h1 : (u.1 - w.1).natAbs + (u.1 + w.1).natAbs ≤ 2 * A)
    (h2 : (u.2 - w.2).natAbs + (u.2 + w.2).natAbs ≤ 2 * m) :
    wt p (u - w) * wt p (u + w) ≤ (2 ^ A * p ^ m) ^ 2 := by
  unfold wt
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
  calc 2 ^ (u.1 - w.1).natAbs * p ^ (u.2 - w.2).natAbs *
        (2 ^ (u.1 + w.1).natAbs * p ^ (u.2 + w.2).natAbs)
      = 2 ^ ((u.1 - w.1).natAbs + (u.1 + w.1).natAbs) *
        p ^ ((u.2 - w.2).natAbs + (u.2 + w.2).natAbs) := by ring
    _ ≤ 2 ^ (2 * A) * p ^ (2 * m) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) h1) (Nat.pow_le_pow_right hp h2)
    _ = (2 ^ A * p ^ m) ^ 2 := by ring

lemma lt_sq_false {K x y : ℕ} (hx : K < x) (hy : K < y) (h : x * y ≤ K ^ 2) : False := by
  have := Nat.mul_lt_mul'' hx hy
  rw [sq] at h; omega

/-- A solution vector in the closed positive quadrant is `H = (A, m)`. -/
theorem pos_sq (A m p : ℕ) (hA : 1 ≤ A) (hm : 1 ≤ m) (hp : 1 ≤ p)
    (S : AddSubgroup (ℤ × ℤ)) (hE : ((2 * A : ℤ), (2 * m : ℤ)) ∈ S)
    (hkey : ∀ u ∈ S, u = 0 ∨ u = ((A : ℤ), (m : ℤ)) ∨ u = (-(A : ℤ), -(m : ℤ)) ∨
      2 ^ A * p ^ m < wt p u)
    {u : ℤ × ℤ} (hu : u ∈ S) (hus : IsSolVec A m u) (h1 : 0 ≤ u.1) (h2 : 0 ≤ u.2) :
    u = ((A : ℤ), (m : ℤ)) := by
  by_contra hne
  obtain ⟨-, -, c1, c2, c3, c4, n0, nE, -⟩ := solvec_coords hus
  have hne' : u.1 ≠ A ∨ u.2 ≠ m := by
    by_contra hc; push Not at hc; exact hne (Prod.ext hc.1 hc.2)
  have hy : ((2 * A : ℤ), (2 * m : ℤ)) - u ∈ S := S.sub_mem hE hu
  have bu := big_of_key' A m p S hkey hu
    (by intro h; simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h; omega) hne
    (by intro h; simp only [Prod.ext_iff] at h; omega)
  have bv := big_of_key' A m p S hkey hy
    (by intro h; simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero,
      Prod.snd_zero] at h; omega)
    (by intro h; simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub] at h; omega)
    (by intro h; simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub] at h; omega)
  have e := wt_add p u (((2 * A : ℤ), (2 * m : ℤ)) - u)
    (by left; simp only [Prod.fst_sub]; omega) (by left; simp only [Prod.snd_sub]; omega)
  rw [add_sub_cancel] at e
  have hle := wt_le A m p hp ((2 * A : ℤ), (2 * m : ℤ)) (by simp; omega) (by simp; omega)
  rw [e] at hle
  exact lt_sq_false bu bv hle

/-- The half of a solution vector is never in `S`. -/
theorem not_half (A m p : ℕ) (hp : 1 ≤ p) (S : AddSubgroup (ℤ × ℤ))
    (hkey : ∀ u ∈ S, u = 0 ∨ u = ((A : ℤ), (m : ℤ)) ∨ u = (-(A : ℤ), -(m : ℤ)) ∨
      2 ^ A * p ^ m < wt p u)
    {w : ℤ × ℤ} (hw : w ∈ S) (hs : IsSolVec A m (w + w)) : False := by
  obtain ⟨-, -, c1, c2, c3, c4, n0, nE, nE'⟩ := solvec_coords hs
  simp only [Prod.fst_add, Prod.snd_add] at c1 c2 c3 c4 n0 nE nE'
  rcases hkey w hw with h | h | h | h
  · subst h; simp at n0
  · rw [h] at nE; simp at nE; try omega
  · rw [h] at nE'; simp at nE'; try omega
  · have : wt p w ≤ 2 ^ A * p ^ m := by
      unfold wt
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
        (Nat.pow_le_pow_right hp (by omega))
    omega

/-- **One solution per class.** Two halves of solution vectors that are congruent modulo `S`
agree up to sign. -/
theorem class_uniq (A m p : ℕ) (hA : 1 ≤ A) (hm : 1 ≤ m) (hp : 1 ≤ p)
    (S : AddSubgroup (ℤ × ℤ)) (hE : ((2 * A : ℤ), (2 * m : ℤ)) ∈ S)
    (hkey : ∀ u ∈ S, u = 0 ∨ u = ((A : ℤ), (m : ℤ)) ∨ u = (-(A : ℤ), -(m : ℤ)) ∨
      2 ^ A * p ^ m < wt p u)
    {w₀ w₁ : ℤ × ℤ} (h₀ : w₀ + w₀ ∈ S) (h₁ : w₁ + w₁ ∈ S) (hs₀ : IsSolVec A m (w₀ + w₀))
    (hs₁ : IsSolVec A m (w₁ + w₁)) (hd : w₀ - w₁ ∈ S) : w₀ = w₁ ∨ w₀ = -w₁ := by
  obtain ⟨-, -, a1, a2, a3, a4, -, -, -⟩ := solvec_coords hs₀
  obtain ⟨-, -, b1, b2, b3, b4, -, -, -⟩ := solvec_coords hs₁
  simp only [Prod.fst_add, Prod.snd_add] at a1 a2 a3 a4 b1 b2 b3 b4
  have hsum : w₀ + w₁ ∈ S := by
    have := S.add_mem hd h₁
    convert this using 1; abel
  have hn₁ : -(w₁ + w₁) ∈ S := S.neg_mem h₁
  have hns₁ := solvec_neg hs₁
  have hn₀ : -(w₀ + w₀) ∈ S := S.neg_mem h₀
  have hns₀ := solvec_neg hs₀
  rcases hkey _ hd with hz | hz | hz | hz
  · left; exact sub_eq_zero.mp hz
  · simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub] at hz
    have e0 := pos_sq A m p hA hm hp S hE hkey h₀ hs₀ (by simp; omega) (by simp; omega)
    have e1 := pos_sq A m p hA hm hp S hE hkey hn₁ hns₁ (by simp; omega) (by simp; omega)
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at e0 e1
    right; ext <;> simp <;> omega
  · simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub] at hz
    have e0 := pos_sq A m p hA hm hp S hE hkey hn₀ hns₀ (by simp; omega) (by simp; omega)
    have e1 := pos_sq A m p hA hm hp S hE hkey h₁ hs₁ (by simp; omega) (by simp; omega)
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at e0 e1
    right; ext <;> simp <;> omega
  · rcases hkey _ hsum with hz' | hz' | hz' | hz'
    · right; exact eq_neg_of_add_eq_zero_left hz'
    · simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at hz'
      have e0 := pos_sq A m p hA hm hp S hE hkey h₀ hs₀ (by simp; omega) (by simp; omega)
      have e1 := pos_sq A m p hA hm hp S hE hkey h₁ hs₁ (by simp; omega) (by simp; omega)
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at e0 e1
      left; ext <;> omega
    · simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at hz'
      have e0 := pos_sq A m p hA hm hp S hE hkey hn₀ hns₀ (by simp; omega) (by simp; omega)
      have e1 := pos_sq A m p hA hm hp S hE hkey hn₁ hns₁ (by simp; omega) (by simp; omega)
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at e0 e1
      left; ext <;> omega
    · exact (lt_sq_false hz hz' (wt_pm A m p hp w₀ w₁ (by omega) (by omega))).elim

/-- The group `half S` is free of rank `≤ 2`, so among five of its elements two differ by
`z + z` with `z ∈ half S`. -/
theorem half_pigeon (S : AddSubgroup (ℤ × ℤ)) (f : Fin 5 → ℤ × ℤ) (hf : ∀ i, f i ∈ half S) :
    ∃ i j, i ≠ j ∧ ∃ z ∈ half S, f i - f j = z + z := by
  set N : Submodule ℤ (ℤ × ℤ) := (half S).toIntSubmodule with hN
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Module.Basis.finTwoProd ℤ) N
  have hn : n ≤ 2 := by
    have h1 := Module.finrank_eq_card_basis b
    have h2 := Submodule.finrank_le N
    rw [Module.finrank_prod, Module.finrank_self] at h2
    simp at h1; omega
  let g : Fin 5 → (Fin n → ZMod 2) := fun i t => ((b.repr ⟨f i, hf i⟩ t : ℤ) : ZMod 2)
  have hcard : Fintype.card (Fin n → ZMod 2) < Fintype.card (Fin 5) := by
    simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn
      _ < 5 := by norm_num
  obtain ⟨i, j, hij, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  refine ⟨i, j, hij, ?_⟩
  set x : N := ⟨f i, hf i⟩ - ⟨f j, hf j⟩ with hx
  have hev : ∀ t, (2 : ℤ) ∣ b.repr x t := by
    intro t
    have := congrFun hg t
    simp only [g] at this
    rw [hx, map_sub, Finsupp.sub_apply]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 2).1 this.symm
  choose c hc using hev
  set z : N := ∑ t, c t • b t with hz
  refine ⟨(z : ℤ × ℤ), z.2, ?_⟩
  have hxz : x = z + z := by
    rw [← b.sum_repr x, hz, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hc t, ← add_smul]; congr 1; ring
  have := congrArg (fun y : N => (y : ℤ × ℤ)) hxz
  simpa [hx] using this

set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option linter.flexible false in
/-- If `S` contains a vector with an odd coordinate, `half S / S` has at most two elements:
every `w ∈ half S` is congruent to `0` or to a fixed `h ∈ half S \ S`. -/
theorem half_rank_one (S : AddSubgroup (ℤ × ℤ)) {o : ℤ × ℤ} (ho : o ∈ S)
    (hodd : Odd o.1 ∨ Odd o.2) {h : ℤ × ℤ} (hh : h ∈ half S) (hhS : h ∉ S) {w : ℤ × ℤ}
    (hw : w ∈ half S) : w ∈ S ∨ w - h ∈ S := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hwS, hwhS⟩ := hcon
  have hoH : o ∈ half S := by rw [mem_half]; exact S.add_mem ho ho
  have hwh : w - h ∈ half S := (half S).sub_mem hw hh
  obtain ⟨i, j, hij, z, hz, e⟩ :=
    half_pigeon S ![0, o, h, w, w - h] (by
      intro i; fin_cases i
      · exact (half S).zero_mem
      · exact hoH
      · exact hh
      · exact hw
      · exact hwh)
  rw [mem_half] at hz
  have hhh : h + h ∈ S := hh
  fin_cases i <;> fin_cases j <;> simp at hij e <;>
    (try (rcases hodd with ⟨r, hr⟩ | ⟨r, hr⟩ <;>
      simp only [Prod.ext_iff, Prod.fst_neg, Prod.snd_neg, Prod.fst_add, Prod.snd_add] at e <;>
      omega)) <;>
    (rw [← e] at hz) <;>
    first
    | (apply hhS; convert hz using 1 <;> abel1)
    | (apply hhS; convert S.neg_mem hz using 1 <;> abel1)
    | (apply hhS; convert S.sub_mem ho hz using 1 <;> abel1)
    | (apply hhS; convert S.sub_mem hz ho using 1 <;> abel1)
    | (apply hhS; convert S.add_mem hz ho using 1 <;> abel1)
    | (apply hhS; convert S.sub_mem hhh hz using 1 <;> abel1)
    | (apply hhS; convert S.sub_mem hz hhh using 1 <;> abel1)
    | (apply hhS; convert S.add_mem hz hhh using 1 <;> abel1)
    | (apply hwS; convert hz using 1 <;> abel1)
    | (apply hwS; convert S.neg_mem hz using 1 <;> abel1)
    | (apply hwS; convert S.sub_mem ho hz using 1 <;> abel1)
    | (apply hwS; convert S.sub_mem hz ho using 1 <;> abel1)
    | (apply hwS; convert S.add_mem hz ho using 1 <;> abel1)
    | (apply hwS; convert S.sub_mem hhh hz using 1 <;> abel1)
    | (apply hwS; convert S.sub_mem hz hhh using 1 <;> abel1)
    | (apply hwS; convert S.add_mem hz hhh using 1 <;> abel1)
    | (apply hwhS; convert hz using 1 <;> abel1)
    | (apply hwhS; convert S.neg_mem hz using 1 <;> abel1)
    | (apply hwhS; convert S.sub_mem ho hz using 1 <;> abel1)
    | (apply hwhS; convert S.sub_mem hz ho using 1 <;> abel1)
    | (apply hwhS; convert S.add_mem hz ho using 1 <;> abel1)

end DujellaUnicity
