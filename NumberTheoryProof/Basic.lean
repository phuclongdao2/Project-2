import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.ModCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Int

theorem problem_1 (n : ℤ) : 2 ∣ (3 * n^2 - 5 * n + 4) := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11 : 3 * n^2 - 5 * n + 4 ≡ 0 [ZMOD 2] := by
    calc
      3 * n^2 - 5 * n + 4
        ≡ 3 * 0^2 - 5 * 0 + 4 [ZMOD 2] := by
          rel [ModEq.mul_left 3 (ModEq.pow 2 h1),
               ModEq.mul_left 5 h1
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rwa [modEq_zero_iff_dvd] at h11

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : 3 * n^2 - 5 * n + 4 ≡ 0 [ZMOD 2] := by
    calc
      3 * n^2 - 5 * n + 4
        ≡ 3 * 1^2 - 5 * 1 + 4 [ZMOD 2] := by
          rel [ModEq.mul_left 3 (ModEq.pow 2 h2),
               ModEq.mul_left 5 h2
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rwa [modEq_zero_iff_dvd] at h21

theorem problem_2 (n : ℤ) : -7 * n^2 + 11 * n + 8 ≡ 0 [ZMOD 2] := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11 : -7 * n^2 + 11 * n + 8 ≡ 0 [ZMOD 2] := by
    calc
      -7 * n^2 + 11 * n + 8
        ≡ -7 * 0^2 + 11 * 0 + 8 [ZMOD 2] := by
          rel [ModEq.mul_left (-7) (ModEq.pow 2 h1),
               ModEq.mul_left 11 h1
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  exact h11

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : -7 * n^2 + 11 * n + 8 ≡ 0 [ZMOD 2] := by
    calc
      -7 * n^2 + 11 * n + 8
        ≡ -7 * 1^2 + 11 * 1 + 8 [ZMOD 2] := by
          rel [ModEq.mul_left (-7) (ModEq.pow 2 h2),
               ModEq.mul_left 11 h2
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  exact h21

theorem problem_3 (n : ℤ) : n^2 + 17 * n ≡ 0 [ZMOD 2] := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11 : n^2 + 17 * n ≡ 0 [ZMOD 2] := by
    calc
      n^2 + 17 * n
        ≡ 0^2 + 17 * 0 [ZMOD 2] := by
          rel [ModEq.pow 2 h1,
               ModEq.mul_left 17 h1
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  exact h11

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : n^2 + 17 * n ≡ 0 [ZMOD 2] := by
    calc
      n^2 + 17 * n
        ≡ 1^2 + 17 * 1 [ZMOD 2] := by
          rel [ModEq.pow 2 h2,
               ModEq.mul_left 17 h2
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  exact h21

theorem problem_4 (n : ℤ) : 2 ∣ (5 * n^2 - n) := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11 : 5 * n^2 - n ≡ 0 [ZMOD 2] := by
    calc
      5 * n^2 - n
        ≡ 5 * 0^2 - 0 [ZMOD 2] := by
          rel [ModEq.mul_left 5 (ModEq.pow 2 h1),
               h1
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rwa [modEq_zero_iff_dvd] at h11

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : 5 * n^2 - n ≡ 0 [ZMOD 2] := by
    calc
      5 * n^2 - n
        ≡ 5 * 1^2 - 1 [ZMOD 2] := by
          rel [ModEq.mul_left 5 (ModEq.pow 2 h2),
               h2
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rwa [modEq_zero_iff_dvd] at h21

theorem problem_5 (n : ℤ) : 2 ∣ (3 * n^3 - 2 * n^2 + 3 * n - 4) := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11 : 3 * n^3 - 2 * n^2 + 3 * n - 4 ≡ 0 [ZMOD 2] := by
    calc
      3 * n^3 - 2 * n^2 + 3 * n - 4
        ≡ 3 * 0^3 - 2 * 0^2 + 3 * 0 - 4 [ZMOD 2] := by
          rel [ModEq.mul_left 3 (ModEq.pow 3 h1),
               ModEq.mul_left 2 (ModEq.pow 2 h1),
               ModEq.mul_left 3 h1
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rwa [modEq_zero_iff_dvd] at h11

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : 3 * n^3 - 2 * n^2 + 3 * n - 4 ≡ 0 [ZMOD 2] := by
    calc
      3 * n^3 - 2 * n^2 + 3 * n - 4
        ≡ 3 * 1^3 - 2 * 1^2 + 3 * 1 - 4 [ZMOD 2] := by
          rel [ModEq.mul_left 3 (ModEq.pow 3 h2),
               ModEq.mul_left 2 (ModEq.pow 2 h2),
               ModEq.mul_left 3 h2
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rwa [modEq_zero_iff_dvd] at h21

theorem problem_6 (n : ℤ) : -10 * n^3 - n^2 + 5 * n - 19 ≡ 1 [ZMOD 2] := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11 : -10 * n^3 - n^2 + 5 * n - 19 ≡ 1 [ZMOD 2] := by
    calc
      -10 * n^3 - n^2 + 5 * n - 19
        ≡ -10 * 0^3 - 0^2 + 5 * 0 - 19 [ZMOD 2] := by
          rel [ModEq.mul_left (-10) (ModEq.pow 3 h1),
               ModEq.pow 2 h1,
               ModEq.mul_left 5 h1
              ]
      _ ≡ 1 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  exact h11

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : -10 * n^3 - n^2 + 5 * n - 19 ≡ 1 [ZMOD 2] := by
    calc
      -10 * n^3 - n^2 + 5 * n - 19
        ≡ -10 * 1^3 - 1^2 + 5 * 1 - 19 [ZMOD 2] := by
          rel [ModEq.mul_left (-10) (ModEq.pow 3 h2),
               ModEq.pow 2 h2,
               ModEq.mul_left 5 h2
              ]
      _ ≡ 1 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  exact h21

theorem problem_7 (n : ℤ) : -n^3 + 5 * n^2 + 3 ≡ 1 [ZMOD 2] := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11 : -n^3 + 5 * n^2 + 3 ≡ 1 [ZMOD 2] := by
    calc
      -n^3 + 5 * n^2 + 3
        ≡ -0^3 + 5 * 0^2 + 3 [ZMOD 2] := by
          rel [ModEq.pow 3 h1,
               ModEq.mul_left 5 (ModEq.pow 2 h1)
              ]
      _ ≡ 1 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  exact h11

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : -n^3 + 5 * n^2 + 3 ≡ 1 [ZMOD 2] := by
    calc
      -n^3 + 5 * n^2 + 3
        ≡ -1^3 + 5 * 1^2 + 3 [ZMOD 2] := by
          rel [ModEq.pow 3 h2,
               ModEq.mul_left 5 (ModEq.pow 2 h2)
              ]
      _ ≡ 1 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  exact h21

theorem problem_8 (n : ℤ) : 2 ∣ (3 * n^3 - n) := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11 : 3 * n^3 - n ≡ 0 [ZMOD 2] := by
    calc
      3 * n^3 - n
        ≡ 3 * 0^3 - 0 [ZMOD 2] := by
          rel [ModEq.mul_left 3 (ModEq.pow 3 h1),
               h1
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rwa [modEq_zero_iff_dvd] at h11

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : 3 * n^3 - n ≡ 0 [ZMOD 2] := by
    calc
      3 * n^3 - n
        ≡ 3 * 1^3 - 1 [ZMOD 2] := by
          rel [ModEq.mul_left 3 (ModEq.pow 3 h2),
               h2
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rwa [modEq_zero_iff_dvd] at h21

theorem problem_9 (n : ℤ) : 2 ∣ (2 * n^3 - 6 * n^2 + 14 * n - 4) := by
  have : 2 * n^3 - 6 * n^2 + 14 * n - 4 = 2 * (n^3 - 3 * n^2 + 7 * n - 2) := by ring
  rw [this]
  exact dvd_mul_right 2 (n^3 - 3 * n^2 + 7 * n - 2)

theorem problem_10 (n : ℤ) : 4 * n^4 + 10 * n^3 - 12 ≡ 0 [ZMOD 2] := by
  have : 4 * n^4 + 10 * n^3 - 12 = 2 * (2 * n^4 + 5 * n^3 - 6) := by ring
  rw [this]
  rw [modEq_zero_iff_dvd]
  exact dvd_mul_right 2 (2 * n^4 + 5 * n^3 - 6)

theorem problem_11 (n : ℤ) : 2 ∣ ((3 * n + 5) * (5 * n - 4)) := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11 : 5 * n - 4 ≡ 0 [ZMOD 2] := by
    calc
      5 * n - 4
        ≡ 5 * 0 - 4 [ZMOD 2] := by
          rel [ModEq.mul_left 5 h1]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rw [modEq_zero_iff_dvd] at h11
  exact dvd_mul_of_dvd_right h11 (3*n + 5)

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : 3 * n + 5 ≡ 0 [ZMOD 2] := by
    calc
      3 * n + 5
        ≡ 3 * 1 + 5 [ZMOD 2] := by
          rel [ModEq.mul_left 3 h2]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rw [modEq_zero_iff_dvd] at h21
  exact dvd_mul_of_dvd_left h21 (5*n - 4)

theorem problem_12 (n : ℤ) : 2 ∣ ((-7 * n - 9) * n) := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  rw [modEq_zero_iff_dvd] at h1
  exact dvd_mul_of_dvd_right h1 (-7 * n - 9)

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : -7 * n - 9 ≡ 0 [ZMOD 2] := by
    calc
      -7 * n - 9
        ≡ -7 * 1 - 9 [ZMOD 2] := by
          rel [ModEq.mul_left (-7) h2]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rw [modEq_zero_iff_dvd] at h21
  exact dvd_mul_of_dvd_left h21 n
