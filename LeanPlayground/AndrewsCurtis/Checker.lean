import LeanPlayground.AndrewsCurtis.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
# A verified checker for rank-2 Andrews–Curtis move sequences

The SAIR ACC Challenge encodes a rank-2 presentation as two freely reduced words
over the letters `1 = x`, `-1 = x⁻¹`, `2 = y`, `-2 = y⁻¹`, and a solution as a list
of move ids `0–13` (`move_spec_version = "ac-r2-v1"`):

| id | effect | id | effect |
|---:|---|---:|---|
| 0 | `r₀ ← r₀⁻¹` | 7 | `r₀ ← x⁻¹ r₀ x` |
| 1 | `r₁ ← r₁⁻¹` | 8 | `r₀ ← y r₀ y⁻¹` |
| 2 | `r₀ ← r₀ r₁` | 9 | `r₀ ← y⁻¹ r₀ y` |
| 3 | `r₀ ← r₀ r₁⁻¹` | 10 | `r₁ ← x r₁ x⁻¹` |
| 4 | `r₁ ← r₁ r₀` | 11 | `r₁ ← x⁻¹ r₁ x` |
| 5 | `r₁ ← r₁ r₀⁻¹` | 12 | `r₁ ← y r₁ y⁻¹` |
| 6 | `r₀ ← x r₀ x⁻¹` | 13 | `r₁ ← y⁻¹ r₁ y` |

This file implements exactly that move table on lists of integers (with the same
left-fold free reduction as the official Python verifier) and proves it sound
against the official `AC.Reachable` of `AC.lean`:

* `AC.Checker.reachable_run`: running any list of moves from a state gives an
  `AC.Reachable` presentation.
* `AC.Checker.reachable_standard_of_run`: if the moves end at `([1], [2])`, the
  start presentation is AC-trivial in the official sense.
* `AC.Reachable.symm`: the official reachability relation is symmetric, so two
  presentations whose runs meet are AC-equivalent.

A concrete certificate is then a single `decide +kernel` on lists of integers.
-/

namespace AC

open Function

/-! ### Symmetry of the official reachability relation -/

theorem Reachable.trans {n : ℕ} {R S T : Relators n} (h₁ : Reachable R S)
    (h₂ : Reachable S T) : Reachable R T :=
  Relation.ReflTransGen.trans h₁ h₂

theorem Reachable.single {n : ℕ} {R S : Relators n} (h : Step R S) : Reachable R S :=
  Relation.ReflTransGen.single h

/-- Right multiplication by the inverse of another relator is reachable:
invert `R j`, multiply, invert `R j` back. -/
theorem Reachable.mulRightInv {n : ℕ} (R : Relators n) (i j : Fin n) (h : i ≠ j) :
    Reachable R (update R i (R i * (R j)⁻¹)) := by
  set R₁ := update R j (R j)⁻¹ with hR₁
  set R₂ := update R₁ i (R₁ i * R₁ j) with hR₂
  have h1 : Reachable R R₁ := Reachable.single (Step.inv R j)
  have h2 : Reachable R₁ R₂ := Reachable.single (Step.mulRight R₁ i j h)
  have h3 : Reachable R₂ (update R₂ j (R₂ j)⁻¹) := Reachable.single (Step.inv R₂ j)
  have hfin : update R₂ j (R₂ j)⁻¹ = update R i (R i * (R j)⁻¹) := by
    funext k
    by_cases hki : k = i
    · subst hki
      simp [R₂, R₁, update_of_ne h, update_of_ne h.symm]
    · by_cases hkj : k = j
      · subst hkj
        simp [R₂, R₁, update_of_ne hki]
      · simp [R₂, R₁, update_of_ne hki, update_of_ne hkj]
  exact (h1.trans h2).trans (hfin ▸ h3)

/-- Every single AC move can be undone by finitely many AC moves. -/
theorem Step.reachable_symm {n : ℕ} {R S : Relators n} (h : Step R S) : Reachable S R := by
  cases h with
  | inv i =>
    have := Reachable.single (Step.inv (update R i (R i)⁻¹) i)
    simpa using this
  | mulRight i j h =>
    have := Reachable.mulRightInv (update R i (R i * R j)) i j h
    simpa [update_of_ne h.symm] using this
  | conj i w =>
    have := Reachable.single (Step.conj (update R i (w * R i * w⁻¹)) i w⁻¹)
    simpa [mul_assoc] using this

/-- The official reachability relation is symmetric. -/
theorem Reachable.symm {n : ℕ} {R S : Relators n} (h : Reachable R S) : Reachable S R := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact hs.reachable_symm.trans ih

namespace Checker

/-! ### Words as lists of integer letters -/

/-- The letter encoding of the challenge: `1 = x`, `-1 = x⁻¹`, `2 = y`, `-2 = y⁻¹`
(any other integer is read as the identity). -/
def letter (a : ℤ) : Word 2 :=
  if a = 1 then FreeGroup.of 0 else if a = -1 then (FreeGroup.of 0)⁻¹
  else if a = 2 then FreeGroup.of 1 else if a = -2 then (FreeGroup.of 1)⁻¹ else 1

theorem letter_neg (a : ℤ) : letter (-a) = (letter a)⁻¹ := by
  unfold letter
  by_cases h1 : a = 1
  · subst h1; simp
  by_cases h2 : a = -1
  · subst h2; simp
  by_cases h3 : a = 2
  · subst h3; simp
  by_cases h4 : a = -2
  · subst h4; simp
  have e1 : ¬ -a = 1 := by omega
  have e2 : ¬ -a = -1 := by omega
  have e3 : ¬ -a = 2 := by omega
  have e4 : ¬ -a = -2 := by omega
  simp [h1, h2, h3, h4, e1, e2, e3, e4]

/-- The free-group element spelled by a list of letters. -/
def eval (w : List ℤ) : Word 2 := (w.map letter).prod

@[simp] theorem eval_nil : eval [] = 1 := rfl

@[simp] theorem eval_cons (a : ℤ) (w : List ℤ) : eval (a :: w) = letter a * eval w := by
  simp [eval]

@[simp] theorem eval_append (v w : List ℤ) : eval (v ++ w) = eval v * eval w := by
  simp [eval]

/-- One step of the official left-fold reduction, on a reversed stack. -/
def push (o : List ℤ) (a : ℤ) : List ℤ :=
  match o with
  | b :: t => if b = -a then t else a :: b :: t
  | [] => [a]

/-- Free reduction by a single left fold, exactly as in the official verifier. -/
def red (w : List ℤ) : List ℤ := (w.foldl push []).reverse

theorem eval_reverse_push (o : List ℤ) (a : ℤ) :
    eval (push o a).reverse = eval o.reverse * letter a := by
  cases o with
  | nil => simp [push]
  | cons b t =>
    simp only [push]
    split_ifs with h
    · subst h
      simp [letter_neg, mul_assoc]
    · simp [mul_assoc]

theorem eval_reverse_foldl (o w : List ℤ) :
    eval (w.foldl push o).reverse = eval o.reverse * eval w := by
  induction w generalizing o with
  | nil => simp
  | cons a w ih => simp [List.foldl_cons, ih, eval_reverse_push, mul_assoc]

@[simp] theorem eval_red (w : List ℤ) : eval (red w) = eval w := by
  simp [red, eval_reverse_foldl]

/-- The formal inverse of a word. -/
def winv (w : List ℤ) : List ℤ := w.reverse.map (fun a => -a)

@[simp] theorem eval_winv (w : List ℤ) : eval (winv w) = (eval w)⁻¹ := by
  induction w with
  | nil => simp [winv]
  | cons a w ih =>
    unfold winv at ih ⊢
    rw [List.reverse_cons, List.map_append, eval_append, ih]
    simp [letter_neg]

/-! ### States and moves -/

/-- A rank-2 state: the two relator words. -/
abbrev State := List ℤ × List ℤ

/-- The official relator tuple of a state. -/
def rel (s : State) : Relators 2 := ![eval s.1, eval s.2]

/-- The move table `ac-r2-v1`, plus the derived move `14`: swap the two relators
(not an official challenge id; it is a composite of official AC moves, see
`reachable_swap`). Other ids do nothing. -/
def move (m : ℕ) (s : State) : State :=
  let a := s.1
  let b := s.2
  match m with
  | 0 => (winv a, b)
  | 1 => (a, winv b)
  | 2 => (red (a ++ b), b)
  | 3 => (red (a ++ winv b), b)
  | 4 => (a, red (b ++ a))
  | 5 => (a, red (b ++ winv a))
  | 6 => (red ([1] ++ a ++ [-1]), b)
  | 7 => (red ([-1] ++ a ++ [1]), b)
  | 8 => (red ([2] ++ a ++ [-2]), b)
  | 9 => (red ([-2] ++ a ++ [2]), b)
  | 10 => (a, red ([1] ++ b ++ [-1]))
  | 11 => (a, red ([-1] ++ b ++ [1]))
  | 12 => (a, red ([2] ++ b ++ [-2]))
  | 13 => (a, red ([-2] ++ b ++ [2]))
  | 14 => (b, a)
  | _ => (a, b)

/-- Run a list of moves. -/
def run (ms : List ℕ) (s : State) : State := ms.foldl (fun s m => move m s) s

theorem rel_eq_update0 (s : State) (u : List ℤ) :
    rel (u, s.2) = update (rel s) 0 (eval u) := by
  funext k; fin_cases k <;> simp [rel]

theorem rel_eq_update1 (s : State) (u : List ℤ) :
    rel (s.1, u) = update (rel s) 1 (eval u) := by
  funext k; fin_cases k <;> simp [rel]

theorem reachable_conj0 (s : State) (w : Word 2) (u : List ℤ)
    (hu : eval u = w * eval s.1 * w⁻¹) : Reachable (rel s) (rel (u, s.2)) := by
  rw [rel_eq_update0 s u, hu]
  exact Reachable.single (Step.conj (rel s) 0 w)

theorem reachable_conj1 (s : State) (w : Word 2) (u : List ℤ)
    (hu : eval u = w * eval s.2 * w⁻¹) : Reachable (rel s) (rel (s.1, u)) := by
  rw [rel_eq_update1 s u, hu]
  exact Reachable.single (Step.conj (rel s) 1 w)

private theorem letter_one : letter 1 = FreeGroup.of 0 := by simp [letter]
private theorem letter_negone : letter (-1) = (FreeGroup.of 0)⁻¹ := by simp [letter]
private theorem letter_two : letter 2 = FreeGroup.of 1 := by simp [letter]
private theorem letter_negtwo : letter (-2) = (FreeGroup.of 1)⁻¹ := by simp [letter]

/-- Swapping the two relators is a composite of official AC moves:
`(a, b) → (ab, b) → (ab, a⁻¹) → (aba⁻¹, a⁻¹) → (b, a⁻¹) → (b, a)`. -/
theorem reachable_swap (a b : List ℤ) : Reachable (rel (a, b)) (rel (b, a)) := by
  set A := eval a
  set B := eval b
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have e : ∀ u v : Word 2, update ![u, v] 0 = fun w => ![w, v] := by
    intro u v; funext w k; fin_cases k <;> simp
  have e' : ∀ u v : Word 2, update ![u, v] 1 = fun w => ![u, w] := by
    intro u v; funext w k; fin_cases k <;> simp
  have s1 : Reachable ![A, B] ![A * B, B] := by
    simpa [e] using Reachable.single (Step.mulRight ![A, B] 0 1 h01)
  have s2 : Reachable ![A * B, B] ![A * B, A⁻¹] := by
    have := Reachable.mulRightInv ![A * B, B] 1 0 h01.symm
    simpa [e', mul_assoc] using this
  have s3 : Reachable ![A * B, A⁻¹] ![A * B * A⁻¹, A⁻¹] := by
    simpa [e] using Reachable.single (Step.mulRight ![A * B, A⁻¹] 0 1 h01)
  have s4 : Reachable ![A * B * A⁻¹, A⁻¹] ![B, A⁻¹] := by
    have := Reachable.single (Step.conj ![A * B * A⁻¹, A⁻¹] 0 A⁻¹)
    simpa [e, mul_assoc] using this
  have s5 : Reachable ![B, A⁻¹] ![B, A] := by
    simpa [e'] using Reachable.single (Step.inv ![B, A⁻¹] 1)
  exact s1.trans (s2.trans (s3.trans (s4.trans s5)))

/-- Every move of the table is a finite sequence of official AC moves. -/
theorem reachable_move (m : ℕ) (s : State) : Reachable (rel s) (rel (move m s)) := by
  obtain ⟨a, b⟩ := s
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have l1 := And.intro letter_one letter_negone
  have l2 := And.intro letter_two letter_negtwo
  match m with
  | 0 =>
    change Reachable _ (rel (winv a, b))
    rw [rel_eq_update0 (a, b) (winv a)]
    simpa [rel] using Reachable.single (Step.inv (rel (a, b)) 0)
  | 1 =>
    change Reachable _ (rel (a, winv b))
    rw [rel_eq_update1 (a, b) (winv b)]
    simpa [rel] using Reachable.single (Step.inv (rel (a, b)) 1)
  | 2 =>
    change Reachable _ (rel (red (a ++ b), b))
    rw [rel_eq_update0 (a, b) (red (a ++ b))]
    simpa [rel] using Reachable.single (Step.mulRight (rel (a, b)) 0 1 h01)
  | 3 =>
    change Reachable _ (rel (red (a ++ winv b), b))
    rw [rel_eq_update0 (a, b) (red (a ++ winv b))]
    simpa [rel] using Reachable.mulRightInv (rel (a, b)) 0 1 h01
  | 4 =>
    change Reachable _ (rel (a, red (b ++ a)))
    rw [rel_eq_update1 (a, b) (red (b ++ a))]
    simpa [rel] using Reachable.single (Step.mulRight (rel (a, b)) 1 0 h01.symm)
  | 5 =>
    change Reachable _ (rel (a, red (b ++ winv a)))
    rw [rel_eq_update1 (a, b) (red (b ++ winv a))]
    simpa [rel] using Reachable.mulRightInv (rel (a, b)) 1 0 h01.symm
  | 6 => exact reachable_conj0 (a, b) (FreeGroup.of 0) _ (by simp [l1, mul_assoc])
  | 7 => exact reachable_conj0 (a, b) (FreeGroup.of 0)⁻¹ _ (by simp [l1, mul_assoc])
  | 8 => exact reachable_conj0 (a, b) (FreeGroup.of 1) _ (by simp [l2, mul_assoc])
  | 9 => exact reachable_conj0 (a, b) (FreeGroup.of 1)⁻¹ _ (by simp [l2, mul_assoc])
  | 10 => exact reachable_conj1 (a, b) (FreeGroup.of 0) _ (by simp [l1, mul_assoc])
  | 11 => exact reachable_conj1 (a, b) (FreeGroup.of 0)⁻¹ _ (by simp [l1, mul_assoc])
  | 12 => exact reachable_conj1 (a, b) (FreeGroup.of 1) _ (by simp [l2, mul_assoc])
  | 13 => exact reachable_conj1 (a, b) (FreeGroup.of 1)⁻¹ _ (by simp [l2, mul_assoc])
  | 14 => exact reachable_swap a b
  | _ + 15 => exact Relation.ReflTransGen.refl

/-- **Soundness.** Any run of moves stays in the official AC class. -/
theorem reachable_run (ms : List ℕ) (s : State) : Reachable (rel s) (rel (run ms s)) := by
  induction ms generalizing s with
  | nil => exact Relation.ReflTransGen.refl
  | cons m ms ih => exact (reachable_move m s).trans (ih (move m s))

theorem rel_standard : rel ([1], [2]) = standard 2 := by
  funext k; fin_cases k <;> simp [rel, standard, eval, letter]

/-- **Certificate of AC-triviality.** If the moves end exactly at `(x, y)`, the
start presentation reaches the standard presentation by official AC moves. -/
theorem reachable_standard_of_run (s : State) (ms : List ℕ) (h : run ms s = ([1], [2])) :
    Reachable (rel s) (standard 2) := by
  simpa [h, rel_standard] using reachable_run ms s

/-- **Certificate of AC-equivalence.** Two runs that meet prove the two start
presentations AC-equivalent. -/
theorem reachable_of_run_eq (s t : State) (ms ns : List ℕ) (h : run ms s = run ns t) :
    Reachable (rel s) (rel t) :=
  (reachable_run ms s).trans (h ▸ (reachable_run ns t).symm)

/-- Sanity check: `⟨x, y | x⁻¹, y⁻¹⟩` reaches `(x, y)` by inverting both relators. -/
example : run [0, 1] ([-1], [-2]) = ([1], [2]) := by decide +kernel

end Checker

end AC
