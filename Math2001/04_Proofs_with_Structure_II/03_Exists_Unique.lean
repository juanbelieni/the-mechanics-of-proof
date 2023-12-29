/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  . intro a h1 h2
    have h3 : -1 ≤ a - 2 := by linarith
    have h4 : a - 2 ≤ 1 := by linarith
    apply sq_le_sq' at h3
    apply h3 at h4
    linarith
  . intro y hy
    have h1 : (1 - y)^2 ≤ 1 := by apply hy; all_goals (linarith)
    have h2 : (3 - y)^2 ≤ 1 := by apply hy; all_goals (linarith)
    have h3 := calc
      (y - 2)^2 = ((1 - y)^2 + (3 - y)^2 - 2) / 2 := by ring
      _ ≤ (1 + 1 - 2) / 2 := by linarith
      _ = 0 := by ring
    have h4 : (y - 2)^2 = 0 := by
      apply le_antisymm
      exact h3
      apply pow_two_nonneg
    simp at h4
    linarith

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  sorry

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  sorry

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  sorry
