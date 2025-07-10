import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.ModCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Int

theorem problem_1 (n : ℤ) : 2 ∣ (3 * n^2 - 5 * n + 4) := by
  rw [← modEq_zero_iff_dvd]
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  calc
    3 * n^2 - 5 * n + 4
      ≡ 3 * 0^2 - 5 * 0 + 4 [ZMOD 2] := by
        rel [ModEq.mul_left 3 (ModEq.pow 2 h1),
             ModEq.mul_left 5 h1
            ]
    _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  calc
    3 * n^2 - 5 * n + 4
      ≡ 3 * 1^2 - 5 * 1 + 4 [ZMOD 2] := by
        rel [ModEq.mul_left 3 (ModEq.pow 2 h2),
             ModEq.mul_left 5 h2
            ]
    _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

theorem problem_2 (n : ℤ) : -7 * n^2 + 11 * n + 8 ≡ 0 [ZMOD 2] := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  calc
    -7 * n^2 + 11 * n + 8
      ≡ -7 * 0^2 + 11 * 0 + 8 [ZMOD 2] := by
        rel [ModEq.mul_left (-7) (ModEq.pow 2 h1),
             ModEq.mul_left 11 h1
            ]
    _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  calc
    -7 * n^2 + 11 * n + 8
      ≡ -7 * 1^2 + 11 * 1 + 8 [ZMOD 2] := by
        rel [ModEq.mul_left (-7) (ModEq.pow 2 h2),
             ModEq.mul_left 11 h2
            ]
    _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

theorem problem_3 (n : ℤ) : n^2 + 17 * n ≡ 0 [ZMOD 2] := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  calc
    n^2 + 17 * n
      ≡ 0^2 + 17 * 0 [ZMOD 2] := by
        rel [ModEq.pow 2 h1,
             ModEq.mul_left 17 h1
            ]
    _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  calc
    n^2 + 17 * n
      ≡ 1^2 + 17 * 1 [ZMOD 2] := by
        rel [ModEq.pow 2 h2,
             ModEq.mul_left 17 h2
            ]
    _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

theorem problem_4 (n : ℤ) : 2 ∣ (5 * n^2 - n) := by
  rw [← modEq_zero_iff_dvd]
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  calc
    5 * n^2 - n
      ≡ 5 * 0^2 - 0 [ZMOD 2] := by
        rel [ModEq.mul_left 5 (ModEq.pow 2 h1),
             h1
            ]
    _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  calc
    5 * n^2 - n
      ≡ 5 * 1^2 - 1 [ZMOD 2] := by
        rel [ModEq.mul_left 5 (ModEq.pow 2 h2),
             h2
            ]
    _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

theorem problem_5 (n : ℤ) : 2 ∣ (3 * n^3 - 2 * n^2 + 3 * n - 4) := by
  rw [← modEq_zero_iff_dvd]
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  calc
    3 * n^3 - 2 * n^2 + 3 * n - 4
      ≡ 3 * 0^3 - 2 * 0^2 + 3 * 0 - 4 [ZMOD 2] := by
        rel [ModEq.mul_left 3 (ModEq.pow 3 h1),
             ModEq.mul_left 2 (ModEq.pow 2 h1),
             ModEq.mul_left 3 h1
            ]
    _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  calc
    3 * n^3 - 2 * n^2 + 3 * n - 4
      ≡ 3 * 1^3 - 2 * 1^2 + 3 * 1 - 4 [ZMOD 2] := by
        rel [ModEq.mul_left 3 (ModEq.pow 3 h2),
             ModEq.mul_left 2 (ModEq.pow 2 h2),
             ModEq.mul_left 3 h2
            ]
    _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

theorem problem_6 (n : ℤ) : -10 * n^3 - n^2 + 5 * n - 19 ≡ 1 [ZMOD 2] := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  calc
    -10 * n^3 - n^2 + 5 * n - 19
      ≡ -10 * 0^3 - 0^2 + 5 * 0 - 19 [ZMOD 2] := by
        rel [ModEq.mul_left (-10) (ModEq.pow 3 h1),
             ModEq.pow 2 h1,
             ModEq.mul_left 5 h1
            ]
    _ ≡ 1 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  calc
    -10 * n^3 - n^2 + 5 * n - 19
      ≡ -10 * 1^3 - 1^2 + 5 * 1 - 19 [ZMOD 2] := by
        rel [ModEq.mul_left (-10) (ModEq.pow 3 h2),
             ModEq.pow 2 h2,
             ModEq.mul_left 5 h2
            ]
    _ ≡ 1 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

theorem problem_7 (n : ℤ) : -n^3 + 5 * n^2 + 3 ≡ 1 [ZMOD 2] := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  calc
    -n^3 + 5 * n^2 + 3
      ≡ -0^3 + 5 * 0^2 + 3 [ZMOD 2] := by
        rel [ModEq.pow 3 h1,
             ModEq.mul_left 5 (ModEq.pow 2 h1)
            ]
    _ ≡ 1 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  calc
    -n^3 + 5 * n^2 + 3
      ≡ -1^3 + 5 * 1^2 + 3 [ZMOD 2] := by
        rel [ModEq.pow 3 h2,
             ModEq.mul_left 5 (ModEq.pow 2 h2)
            ]
    _ ≡ 1 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

theorem problem_8 (n : ℤ) : 2 ∣ (3 * n^3 - n) := by
  rw [← modEq_zero_iff_dvd]
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  calc
    3 * n^3 - n
      ≡ 3 * 0^3 - 0 [ZMOD 2] := by
        rel [ModEq.mul_left 3 (ModEq.pow 3 h1),
             h1
            ]
    _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  calc
    3 * n^3 - n
      ≡ 3 * 1^3 - 1 [ZMOD 2] := by
        rel [ModEq.mul_left 3 (ModEq.pow 3 h2),
             h2
            ]
    _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num

theorem problem_9 (n : ℤ) : 2 ∣ (2 * n^3 - 6 * n^2 + 14 * n - 4) := by
  have : 2 * n^3 - 6 * n^2 + 14 * n - 4 = 2 * (n^3 - 3 * n^2 + 7 * n - 2) := by ring
  rw [this]
  exact dvd_mul_right 2 (n^3 - 3 * n^2 + 7 * n - 2)

theorem problem_10 (n : ℤ) : 4 * n^4 + 10 * n^3 - 12 ≡ 0 [ZMOD 2] := by
  have : 4 * n^4 + 10 * n^3 - 12 = 2 * (2 * n^4 + 5 * n^3 - 6) := by ring
  rw [this, modEq_zero_iff_dvd]
  exact dvd_mul_right 2 (2 * n^4 + 5 * n^3 - 6)

theorem problem_11 (n : ℤ) : 2 ∣ ((3 * n + 5) * (5 * n - 4)) := by
  rw [← modEq_zero_iff_dvd]
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11 : 5 * n - 4 ≡ 0 [ZMOD 2] := by
    calc
      5 * n - 4
        ≡ 5 * 0 - 4 [ZMOD 2] := by
          rel [ModEq.mul_left 5 h1]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  calc
    (3 * n + 5) * (5 * n - 4)
      ≡ (3 * n + 5) * 0 [ZMOD 2] := by rel [h11]
    _ ≡ 0 [ZMOD 2] := by norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : 3 * n + 5 ≡ 0 [ZMOD 2] := by
    calc
      3 * n + 5
        ≡ 3 * 1 + 5 [ZMOD 2] := by
          rel [ModEq.mul_left 3 h2]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  calc
    (3 * n + 5) * (5 * n - 4)
      ≡ 0 * (5 * n - 4) [ZMOD 2] := by rel [h21]
    _ ≡ 0 [ZMOD 2] := by norm_num

theorem problem_12 (n : ℤ) : 2 ∣ ((-7 * n - 9) * n) := by
  rw [← modEq_zero_iff_dvd]
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  calc
    (-7 * n - 9) * n
      ≡ (-7 * n - 9) * 0 [ZMOD 2] := by rel[h]
    _ ≡ 0 [ZMOD 2] := by norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : -7 * n - 9 ≡ 0 [ZMOD 2] := by
    calc
      -7 * n - 9
        ≡ -7 * 1 - 9 [ZMOD 2] := by
          rel [ModEq.mul_left (-7) h2]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  calc
    (-7 * n - 9) * n
      ≡ 0 * n [ZMOD 2] := by rel[h21]
    _ ≡ 0 [ZMOD 2] := by norm_num

theorem problem_13 (n : ℤ) : n * (n^2 + 1) * (n^3 + 2) ≡ 0 [ZMOD 2] := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  calc
    n * (n^2 + 1) * (n^3 + 2)
      ≡ 0 * (n^2 + 1) * (n^3 + 2) [ZMOD 2] := by
        rel [h1]
    _ ≡ 0 [ZMOD 2] := by norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21: n^2 + 1 ≡ 0 [ZMOD 2] := by
    calc
      n^2 + 1
        ≡ 1^2 + 1 [ZMOD 2] := by
          rel [ModEq.pow 2 h2]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  calc
    n * (n^2 + 1) * (n^3 + 2)
      ≡ n * 0 * (n^3 + 2) [ZMOD 2] := by
        rel [h21]
    _ ≡ 0 [ZMOD 2] := by norm_num

theorem problem_14 (n : ℤ) : (n^4 - 2 * n + 3) * (n^2 + 2) * (n^3 + n + 1) ≡ 0 [ZMOD 2] := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11: n^2 + 2 ≡ 0 [ZMOD 2] := by
    calc
      n^2 + 2
        ≡ 0^2 + 2 [ZMOD 2] := by
          rel [ModEq.pow 2 h1]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  calc
    (n^4 - 2 * n + 3) * (n^2 + 2) * (n^3 + n + 1)
      ≡ (n^4 - 2 * n + 3) * 0 * (n^3 + n + 1) [ZMOD 2] := by
        rel [h11]
    _ ≡ 0 [ZMOD 2] := by norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21: n^4 - 2 * n + 3 ≡ 0 [ZMOD 2] := by
    calc
      n^4 - 2 * n + 3
        ≡ 1^4 - 2 * 1 + 3 [ZMOD 2] := by
          rel [ModEq.pow 4 h2,
               ModEq.mul_left 2 h2]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  calc
    (n^4 - 2 * n + 3) * (n^2 + 2) * (n^3 + n + 1)
      ≡ 0 * (n^2 + 2) * (n^3 + n + 1) [ZMOD 2] := by
        rel [h21]
    _ ≡ 0 [ZMOD 2] := by norm_num

theorem problem_15 (n : ℤ) : (n^2 - n + 3) * (3 * n^3 + 4 * n^2 + 2) * (-n^3 - 2 * n^2 - 1) ≡ 0 [ZMOD 2] := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11: 3 * n^3 + 4 * n^2 + 2 ≡ 0 [ZMOD 2] := by
    calc
      3 * n^3 + 4 * n^2 + 2
        ≡ 3 * 0^3 + 4 * 0^2 + 2 [ZMOD 2] := by
          rel [ModEq.mul_left 3 (ModEq.pow 3 h1),
               ModEq.mul_left 4 (ModEq.pow 2 h1)]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  calc
    (n^2 - n + 3) * (3 * n^3 + 4 * n^2 + 2) * (-n^3 - 2 * n^2 - 1)
      ≡ (n^2 - n + 3) * 0 * (-n^3 - 2 * n^2 - 1) [ZMOD 2] := by
        rel [h11]
    _ ≡ 0 [ZMOD 2] := by norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21: -n^3 - 2 * n^2 - 1 ≡ 0 [ZMOD 2] := by
    calc
      -n^3 - 2 * n^2 - 1
        ≡ -1^3 - 2 * 1^2 - 1 [ZMOD 2] := by
          rel [ModEq.pow 3 h2,
               ModEq.mul_left 2 (ModEq.pow 2 h2)]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  calc
    (n^2 - n + 3) * (3 * n^3 + 4 * n^2 + 2) * (-n^3 - 2 * n^2 - 1)
      ≡ (n^2 - n + 3) * (3 * n^3 + 4 * n^2 + 2) * 0 [ZMOD 2] := by
        rel [h21]
    _ ≡ 0 [ZMOD 2] := by norm_num

theorem problem_16 (n : ℤ) : 2 ∣ ((3 * n^2 - 5 * n + 1) * (-5 * n^3 + 1) * (7 * n^4 - 4)) := by
  rw [← modEq_zero_iff_dvd]
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11: 7 * n^4 - 4 ≡ 0 [ZMOD 2] := by
    calc
      7 * n^4 - 4
        ≡ 7 * 0^4 - 4 [ZMOD 2] := by
          rel [ModEq.mul_left 7 (ModEq.pow 4 h1)]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  calc
    (3 * n^2 - 5 * n + 1) * (-5 * n^3 + 1) * (7 * n^4 - 4)
      ≡ (3 * n^2 - 5 * n + 1) * (-5 * n^3 + 1) * 0 [ZMOD 2] := by
        rel [h11]
    _ ≡ 0 [ZMOD 2] := by norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21: -5 * n^3 + 1 ≡ 0 [ZMOD 2] := by
    calc
      -5 * n^3 + 1
        ≡ -5 * 1^3 + 1 [ZMOD 2] := by
          rel [ModEq.mul_left (-5) (ModEq.pow 3 h2)]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  calc
    (3 * n^2 - 5 * n + 1) * (-5 * n^3 + 1) * (7 * n^4 - 4)
      ≡ (3 * n^2 - 5 * n + 1) * 0 * (7 * n^4 - 4) [ZMOD 2] := by
        rel [h21]
    _ ≡ 0 [ZMOD 2] := by norm_num

theorem problem_17 (n : ℤ) : 2 ∣ (n * (-2 * n^2 + 1) * (-5 * n^2 + 3)) := by
  rw [← modEq_zero_iff_dvd]
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  calc
    n * (-2 * n^2 + 1) * (-5 * n^2 + 3)
      ≡ 0 * (-2 * n^2 + 1) * (-5 * n^2 + 3) [ZMOD 2] := by rel[h1]
    _ ≡ 0 [ZMOD 2] := by norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21: -5 * n^2 + 3 ≡ 0 [ZMOD 2] := by
    calc
      -5 * n^2 + 3
        ≡ -5 * 1^2 + 3 [ZMOD 2] := by
          rel [ModEq.mul_left (-5) (ModEq.pow 2 h2)]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  calc
    n * (-2 * n^2 + 1) * (-5 * n^2 + 3)
      ≡ n * (-2 * n^2 + 1) * 0 [ZMOD 2] := by rel[h21]
    _ ≡ 0 [ZMOD 2] := by norm_num

theorem problem_18 (n : ℤ) : 2 ∣ ((-9 * n^2 + 1) * (-12 * n^2 + 5) * n) := by
  rw [← modEq_zero_iff_dvd]
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  calc
    (-9 * n^2 + 1) * (-12 * n^2 + 5) * n
      ≡ (-9 * n^2 + 1) * (-12 * n^2 + 5) * 0 [ZMOD 2] := by rel[h1]
    _ ≡ 0 [ZMOD 2] := by norm_num

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21: -9 * n^2 + 1 ≡ 0 [ZMOD 2] := by
    calc
      -9 * n^2 + 1
        ≡ -9 * 1^2 + 1 [ZMOD 2] := by
          rel [ModEq.mul_left (-9) (ModEq.pow 2 h2)]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  calc
    (-9 * n^2 + 1) * (-12 * n^2 + 5) * n
      ≡ 0 * (-12 * n^2 + 5) * n [ZMOD 2] := by rel[h21]
    _ ≡ 0 [ZMOD 2] := by norm_num
