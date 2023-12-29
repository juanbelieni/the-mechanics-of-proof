/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
attribute [-simp] Nat.not_two_dvd_bit1 two_dvd_bit0


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m h_m_dvd_p
  have h_0_lt_p : 0 < p := by extra
  have h_1_le_m : 1 ≤ m := Nat.pos_of_dvd_of_pos h_m_dvd_p h_0_lt_p
  obtain h_1_eq_m | h_1_lt_m : 1 = m ∨ 1 < m := eq_or_lt_of_le h_1_le_m
  · -- m = 1
    left
    exact by rw [h_1_eq_m]
  . -- 1 < m
    right
    obtain h_m_lt_p_not_m_dvd_p : m < p → ¬m ∣ p  := by apply H; exact h_1_lt_m
    obtain h_m_le_p : m ≤ p := Nat.le_of_dvd h_0_lt_p h_m_dvd_p
    obtain h_m_eq_p | h_m_lt_p : m = p ∨ m < p := eq_or_lt_of_le h_m_le_p
    . -- m = p
      exact h_m_eq_p
    . -- m < p
      obtain h_not_m_dvd_p := h_m_lt_p_not_m_dvd_p h_m_lt_p
      contradiction


example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain h_a_le_2 | h_2_lt_a := le_or_lt a 2
  . obtain h_b_le_1 | h_1_lt_b := le_or_lt b 1
    . have h_c_sq_lt_9 : c^2 < 3^2 := calc
        c^2 = a^2 + b^2 := by linarith
        _ ≤ 2^2 + 1^2 := by rel [h_a_le_2, h_b_le_1]
        _ < 3^2 := by linarith
      have h_c_lt_3 : c < 3 := by cancel 2 at h_c_sq_lt_9;
      interval_cases a
      <;> interval_cases c
      <;> interval_cases b
      <;> simp_arith at h_pyth
    . have h_b_sq_lt_c_sq : b^2 < c^2 := by calc
        b^2 < a^2 + b^2 := by apply lt_add_of_pos_left; aesop
        _ = c^2 := by linarith
      have h_c_sq_lt_b_1_sq : c^2 < (b + 1)^2 := by calc
        c^2 = a^2 + b^2 := by rw [h_pyth]
        _ ≤ 2^2 + b^2 := by rel [h_a_le_2]
        _ = b^2 + 2 * 2 := by ring
        _ ≤ b^2 + 2 * b := by linarith
        _ < (b + 1)^2 := by linarith
      have h_b_1_le_c : b + 1 <= c := by cancel 2 at h_b_sq_lt_c_sq
      have h_b_1_gt_c : b + 1 > c := by cancel 2 at h_c_sq_lt_b_1_sq
      have h_not_b_1_le_c : ¬ b + 1 ≤ c := not_le_of_gt h_b_1_gt_c
      contradiction
  . exact h_2_lt_a

/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  sorry

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  sorry

example : Prime 7 := by
  sorry

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  sorry

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  sorry
