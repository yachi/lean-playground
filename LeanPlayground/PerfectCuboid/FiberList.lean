module

public import LeanPlayground.PerfectCuboid.Fiber
public import LeanPlayground.PerfectCuboid.FiberDescent
public import LeanPlayground.PerfectCuboid.Fibers.F_100_629
public import LeanPlayground.PerfectCuboid.Fibers.F_120_169
public import LeanPlayground.PerfectCuboid.Fibers.F_132_157
public import LeanPlayground.PerfectCuboid.Fibers.F_132_493
public import LeanPlayground.PerfectCuboid.Fibers.F_136_305
public import LeanPlayground.PerfectCuboid.Fibers.F_144_145
public import LeanPlayground.PerfectCuboid.Fibers.F_152_377
public import LeanPlayground.PerfectCuboid.Fibers.F_156_685
public import LeanPlayground.PerfectCuboid.Fibers.F_228_397
public import LeanPlayground.PerfectCuboid.Fibers.F_24_145
public import LeanPlayground.PerfectCuboid.Fibers.F_336_505
public import LeanPlayground.PerfectCuboid.Fibers.F_336_625
public import LeanPlayground.PerfectCuboid.Fibers.F_352_377
public import LeanPlayground.PerfectCuboid.Fibers.F_36_85
public import LeanPlayground.PerfectCuboid.Fibers.F_396_445
public import LeanPlayground.PerfectCuboid.Fibers.F_396_565
public import LeanPlayground.PerfectCuboid.Fibers.F_400_689
public import LeanPlayground.PerfectCuboid.Fibers.F_416_425
public import LeanPlayground.PerfectCuboid.Fibers.F_432_793
public import LeanPlayground.PerfectCuboid.Fibers.F_44_125
public import LeanPlayground.PerfectCuboid.Fibers.F_460_629
public import LeanPlayground.PerfectCuboid.Fibers.F_468_493
public import LeanPlayground.PerfectCuboid.Fibers.F_52_173
public import LeanPlayground.PerfectCuboid.Fibers.F_52_677
public import LeanPlayground.PerfectCuboid.Fibers.F_56_785
public import LeanPlayground.PerfectCuboid.Fibers.F_60_229
public import LeanPlayground.PerfectCuboid.Fibers.F_644_725
public import LeanPlayground.PerfectCuboid.Fibers.F_684_1525
public import LeanPlayground.PerfectCuboid.Fibers.F_684_685
public import LeanPlayground.PerfectCuboid.Fibers.F_68_293
public import LeanPlayground.PerfectCuboid.Fibers.F_72_97
public import LeanPlayground.PerfectCuboid.Fibers.F_736_785
public import LeanPlayground.PerfectCuboid.Fibers.F_96_265

/-!
# The fibers on which no perfect cuboid lies

Every perfect cuboid lies on a fiber `(m, n)` of Peschmann's master-tuple parametrization
(`IsEulerBrick.exists_fiber`): two of its edges `X, Z` satisfy `(m² − n²) X = 2mn Z` for coprime
`m > n > 0` of opposite parity. This file collects the 41 fibers that the descent of
`LeanPlayground.PerfectCuboid.Descent` has ruled out unconditionally, in `FiberTwoOne.lean`,
`FiberDescent.lean` and `Fibers/F_<p>_<q>.lean`, into one statement:

* `provedFibers` — the list of the 41 pairs `(m, n)`;
* `IsPerfectCuboid.not_onFiber_of_mem` — a perfect cuboid has no two edges `X, Z` with
  `(m² − n²) X = 2mn Z` for `(m, n)` in the list;
* `IsPerfectCuboid.exists_fiber_not_mem` — every perfect cuboid lies on a fiber outside the list.

In terms of edge ratios, the fibers are `3 : 4`, `5 : 12`, `15 : 8`, `7 : 24`, `35 : 12`, `45 : 28`,
`13 : 84`, `63 : 16`, `77 : 36`, `65 : 72`, `17 : 144`, `117 : 44`, `85 : 132`, `143 : 24`,
`119 : 120`, `165 : 52`, `221 : 60`, `247 : 96`, `135 : 352`, `87 : 416`, `285 : 68`, `273 : 136`,
`203 : 396`, `155 : 468`, `345 : 152`, `325 : 228`, `37 : 684`, `377 : 336`, `475 : 132`,
`403 : 396`, `429 : 460`, `333 : 644`, `273 : 736`, `527 : 336`, `621 : 100`, `561 : 400`,
`675 : 52`, `667 : 156`, `665 : 432`, `783 : 56`, `1363 : 684`.

The descent can only work on a fiber whose curve `y² = x (x + p²)(x + q²)`, `p = 2mn`,
`q = m² + n²`, has rank `0` and `Ш[2] = 0`. By PARI/GP, among the `331` fibers with `m ≤ 40`
these are `70`. The list has all of them with `q ≤ 829` except `(22, 17)`, `(26, 9)` and
`(27, 10)`: their certificates exist, but `q = 773, 757, 829` is prime and is needed as a modulus,
and a residue check modulo a prime that size costs minutes and gigabytes of kernel memory. The
other usable fibers have `q ≥ 853`.
-/

@[expose] public section

namespace PerfectCuboid

/-- The fibers `(m, n)` ruled out unconditionally by the descent. -/
def provedFibers : List (ℕ × ℕ) :=
  [(2, 1), (3, 2), (4, 1), (4, 3), (6, 1), (7, 2), (7, 6), (8, 1), (9, 2), (9, 4), (9, 8), (11, 2),
   (11, 6), (12, 1), (12, 5), (13, 2), (15, 2), (16, 3), (16, 11), (16, 13), (17, 2), (17, 4),
   (18, 11), (18, 13), (19, 4), (19, 6), (19, 18), (21, 8), (22, 3), (22, 9), (23, 10), (23, 14),
   (23, 16), (24, 7), (25, 2), (25, 8), (26, 1), (26, 3), (27, 8), (28, 1), (38, 9)]

theorem provedFibers_length : provedFibers.length = 41 := rfl

/-- A perfect cuboid has no two edges `X, Z` with `(m² − n²) X = 2mn Z` for `(m, n)` in
`provedFibers`. -/
theorem IsPerfectCuboid.not_onFiber_of_mem {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) {m n : ℕ}
    (hmn : (m, n) ∈ provedFibers) : (m ^ 2 - n ^ 2) * X ≠ 2 * m * n * Z := by
  simp only [provedFibers, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hmn
  rcases hmn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact not_isPerfectCuboid_three_four h.swap
  · exact (not_isPerfectCuboid_five_twelve h.swap).symm
  · exact not_isPerfectCuboid_eight_fifteen h
  · exact (not_isPerfectCuboid_seven_twentyfour h.swap).symm
  · exact not_isPerfectCuboid_twelve_thirtyfive h
  · exact not_isPerfectCuboid_twentyeight_fortyfive h
  · exact (not_isPerfectCuboid_thirteen_eightyfour h.swap).symm
  · exact not_isPerfectCuboid_sixteen_sixtythree h
  · exact not_isPerfectCuboid_thirtysix_seventyseven h
  · exact not_isPerfectCuboid_sixtyfive_seventytwo h
  · exact not_isPerfectCuboid_seventeen_144 h
  · exact not_isPerfectCuboid_fortyfour_117 h
  · exact not_isPerfectCuboid_eightyfive_132 h
  · exact not_isPerfectCuboid_twentyfour_143 h
  · exact not_isPerfectCuboid_119_120 h
  · exact not_isPerfectCuboid_fiftytwo_165 h
  · exact not_isPerfectCuboid_sixty_221 h
  · exact not_isPerfectCuboid_ninetysix_247 h
  · exact not_isPerfectCuboid_135_352 h
  · exact not_isPerfectCuboid_eightyseven_416 h
  · exact not_isPerfectCuboid_sixtyeight_285 h
  · exact not_isPerfectCuboid_136_273 h
  · exact not_isPerfectCuboid_203_396 h
  · exact not_isPerfectCuboid_155_468 h
  · exact not_isPerfectCuboid_152_345 h
  · exact not_isPerfectCuboid_228_325 h
  · exact not_isPerfectCuboid_thirtyseven_684 h
  · exact not_isPerfectCuboid_336_377 h
  · exact not_isPerfectCuboid_132_475 h
  · exact not_isPerfectCuboid_396_403 h
  · exact not_isPerfectCuboid_429_460 h
  · exact not_isPerfectCuboid_333_644 h
  · exact not_isPerfectCuboid_273_736 h
  · exact not_isPerfectCuboid_336_527 h
  · exact not_isPerfectCuboid_100_621 h
  · exact not_isPerfectCuboid_400_561 h
  · exact not_isPerfectCuboid_fiftytwo_675 h
  · exact not_isPerfectCuboid_156_667 h
  · exact not_isPerfectCuboid_432_665 h
  · exact not_isPerfectCuboid_fiftysix_783 h
  · exact not_isPerfectCuboid_684_1363 h

/-- **Every perfect cuboid lies on a fiber outside `provedFibers`**: there are coprime `m > n > 0`
of opposite parity with `(m, n) ∉ provedFibers` and `Z (m² − n²) = X · 2mn` or
`X (m² − n²) = Z · 2mn`. -/
theorem IsPerfectCuboid.exists_fiber_not_mem {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) :
    ∃ m n : ℕ, 0 < n ∧ n < m ∧ Nat.Coprime m n ∧ (m + n) % 2 = 1 ∧ (m, n) ∉ provedFibers ∧
      ((Z : ℚ) * Fiber.U m n = X * Fiber.V m n ∨ (X : ℚ) * Fiber.U m n = Z * Fiber.V m n) := by
  obtain ⟨m, n, hn, hnm, hmn, hpar, hf⟩ := h.toIsEulerBrick.exists_fiber
  refine ⟨m, n, hn, hnm, hmn, hpar, fun hmem ↦ ?_, hf⟩
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm.le 2
  rcases hf with hf | hf
  · refine h.swap.not_onFiber_of_mem hmem ?_
    have : (((m ^ 2 - n ^ 2) * Z : ℕ) : ℚ) = ((2 * m * n * X : ℕ) : ℚ) := by
      push_cast [hle]
      rw [Fiber.U, Fiber.V] at hf
      linear_combination hf
    exact_mod_cast this
  · refine h.not_onFiber_of_mem hmem ?_
    have : (((m ^ 2 - n ^ 2) * X : ℕ) : ℚ) = ((2 * m * n * Z : ℕ) : ℚ) := by
      push_cast [hle]
      rw [Fiber.U, Fiber.V] at hf
      linear_combination hf
    exact_mod_cast this

end PerfectCuboid
