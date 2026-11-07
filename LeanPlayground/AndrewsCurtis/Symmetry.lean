import LeanPlayground.AndrewsCurtis.Checker

/-!
# Signed generator permutations and AC-triviality

The eight signed permutations of `{x, y}` act on rank-2 presentations. They
commute with AC moves (any group endomorphism does), and they fix the standard
presentation up to AC moves. Hence a presentation is AC-trivial iff its image is.

Main results:

* `AC.Reachable.map`: any endomorphism `φ` of the free group maps an AC path
  `R → S` to an AC path `φ ∘ R → φ ∘ S`.
* `AC.Checker.triv_iff_of_run_eq_perm`: if a run of moves takes `s` to a signed
  permutation of `t`, then `s` is AC-trivial iff `t` is.
-/

namespace AC

open Function

theorem Step.map {n : ℕ} (φ : Word n →* Word n) {R S : Relators n} (h : Step R S) :
    Step (φ ∘ R) (φ ∘ S) := by
  cases h with
  | inv i =>
    rw [comp_update]
    simpa using Step.inv (φ ∘ R) i
  | mulRight i j h =>
    rw [comp_update]
    simpa using Step.mulRight (φ ∘ R) i j h
  | conj i w =>
    rw [comp_update]
    simpa using Step.conj (φ ∘ R) i (φ w)

theorem Reachable.map {n : ℕ} (φ : Word n →* Word n) {R S : Relators n}
    (h : Reachable R S) : Reachable (φ ∘ R) (φ ∘ S) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (hs.map φ)

namespace Checker

/-- A signed permutation of the generators: optionally swap `x ↔ y`, then
optionally invert the (new) `x` and the (new) `y`. -/
structure SPerm where
  swap : Bool
  nx : Bool
  ny : Bool
  deriving DecidableEq, Repr

/-- The action on integer letters (non-letters are fixed). -/
def act (p : SPerm) (a : ℤ) : ℤ :=
  let b := if p.swap then
      (if a = 1 then 2 else if a = -1 then -2 else if a = 2 then 1 else if a = -2 then -1 else a)
    else a
  if (b = 1 ∨ b = -1) ∧ p.nx = true then -b
  else if (b = 2 ∨ b = -2) ∧ p.ny = true then -b else b

/-- The inverse signed permutation. -/
def SPerm.inv (p : SPerm) : SPerm :=
  if p.swap then ⟨true, p.ny, p.nx⟩ else p

theorem act_fix (p : SPerm) (a : ℤ) (a1 : a ≠ 1) (a2 : a ≠ -1) (a3 : a ≠ 2) (a4 : a ≠ -2) :
    act p a = a := by
  rcases p with ⟨_ | _, _ | _, _ | _⟩ <;> simp [act, a1, a2, a3, a4]

theorem act_inv_act (p : SPerm) (a : ℤ) : act p.inv (act p a) = a := by
  by_cases a1 : a = 1
  · subst a1; rcases p with ⟨_ | _, _ | _, _ | _⟩ <;> decide
  by_cases a2 : a = -1
  · subst a2; rcases p with ⟨_ | _, _ | _, _ | _⟩ <;> decide
  by_cases a3 : a = 2
  · subst a3; rcases p with ⟨_ | _, _ | _, _ | _⟩ <;> decide
  by_cases a4 : a = -2
  · subst a4; rcases p with ⟨_ | _, _ | _, _ | _⟩ <;> decide
  rw [act_fix p a a1 a2 a3 a4, act_fix p.inv a a1 a2 a3 a4]

/-- The induced automorphism of the free group. -/
def phi (p : SPerm) : Word 2 →* Word 2 :=
  FreeGroup.lift (fun i => letter (act p (if i = 0 then 1 else 2)))

theorem letter_act (p : SPerm) (a : ℤ) : letter (act p a) = phi p (letter a) := by
  have h0 : phi p (FreeGroup.of 0) = letter (act p 1) := by simp [phi]
  have h1 : phi p (FreeGroup.of 1) = letter (act p 2) := by simp [phi]
  by_cases a1 : a = 1
  · subst a1; simp [letter, h0]
  by_cases a2 : a = -1
  · subst a2
    have : act p (-1) = -act p 1 := by
      rcases p with ⟨_ | _, _ | _, _ | _⟩ <;> simp [act]
    rw [this, letter_neg, ← h0]
    simp [letter]
  by_cases a3 : a = 2
  · subst a3; simp [letter, h1]
  by_cases a4 : a = -2
  · subst a4
    have : act p (-2) = -act p 2 := by
      rcases p with ⟨_ | _, _ | _, _ | _⟩ <;> simp [act]
    rw [this, letter_neg, ← h1]
    simp [letter]
  rw [act_fix p a a1 a2 a3 a4]
  simp [letter, a1, a2, a3, a4]

/-- Apply a signed permutation to a word. -/
def permW (p : SPerm) (w : List ℤ) : List ℤ := w.map (act p)

/-- Apply a signed permutation to a state. -/
def permS (p : SPerm) (s : State) : State := (permW p s.1, permW p s.2)

theorem eval_permW (p : SPerm) (w : List ℤ) : eval (permW p w) = phi p (eval w) := by
  induction w with
  | nil => simp [permW]
  | cons a w ih =>
    simp only [permW, List.map_cons, eval_cons, map_mul] at ih ⊢
    rw [ih, letter_act]

theorem rel_permS (p : SPerm) (s : State) : rel (permS p s) = phi p ∘ rel s := by
  funext k; fin_cases k <;> simp [rel, permS, eval_permW]

theorem permS_inv_permS (p : SPerm) (s : State) : permS p.inv (permS p s) = s := by
  obtain ⟨a, b⟩ := s
  simp [permS, permW, List.map_map, Function.comp_def, act_inv_act]

/-- Moves bringing each signed permutation of `(x, y)` back to `(x, y)`
(the official canonicalization table, on our encoding). -/
def canonSuffix (p : SPerm) : List ℕ :=
  match p with
  | ⟨false, false, false⟩ => []
  | ⟨false, false, true⟩ => [1]
  | ⟨false, true, false⟩ => [0]
  | ⟨false, true, true⟩ => [0, 1]
  | ⟨true, false, false⟩ => [0, 2, 5, 2, 8]
  | ⟨true, false, true⟩ => [2, 5, 2, 8]
  | ⟨true, true, false⟩ => [3, 4, 3, 10]
  | ⟨true, true, true⟩ => [2, 0, 4, 3]

theorem run_canonSuffix (p : SPerm) :
    run (canonSuffix p) (permS p ([1], [2])) = ([1], [2]) := by
  rcases p with ⟨_ | _, _ | _, _ | _⟩ <;> decide +kernel

theorem reachable_phi_standard (p : SPerm) : Reachable (phi p ∘ standard 2) (standard 2) := by
  have h := reachable_standard_of_run _ _ (run_canonSuffix p)
  rwa [rel_permS, rel_standard] at h

/-- AC-triviality is invariant under signed generator permutations. -/
theorem triv_phi_iff (p : SPerm) (R : Relators 2) :
    Reachable (phi p ∘ R) (standard 2) ↔ Reachable R (standard 2) := by
  constructor
  · intro h
    have h1 := (h.map (phi p.inv)).trans (reachable_phi_standard p.inv)
    have hcomp : (phi p.inv).comp (phi p) = MonoidHom.id _ := by
      refine FreeGroup.ext_hom _ _ (fun i => ?_)
      have hi : FreeGroup.of i = letter (if i = 0 then 1 else 2) := by
        fin_cases i <;> simp [letter]
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [hi, ← letter_act, ← letter_act, act_inv_act]
    have hR : phi p.inv ∘ (phi p ∘ R) = R := by
      funext k
      simpa using DFunLike.congr_fun hcomp (R k)
    rwa [hR] at h1
  · intro h
    exact ((Reachable.map (phi p) h).trans (reachable_phi_standard p))

/-- **Certificate of equal AC-hardness.** If a run of moves takes `s` to a signed
permutation of `t`, then `s` is AC-trivial iff `t` is. -/
theorem triv_iff_of_run_eq_perm (s t : State) (ms : List ℕ) (p : SPerm)
    (h : run ms s = permS p t) :
    Reachable (rel s) (standard 2) ↔ Reachable (rel t) (standard 2) := by
  have hst : Reachable (rel s) (phi p ∘ rel t) := by
    simpa [h, rel_permS] using reachable_run ms s
  rw [← triv_phi_iff p (rel t)]
  exact ⟨fun hs => hst.symm.trans hs, fun ht => hst.trans ht⟩

end Checker

end AC
