import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.ModCases
import Mathlib.Tactic.NormNum

open Int

theorem poly_divisible_by_two (n : ℤ) : 2 ∣ (n^3 + 2 * n^2 + 3 * n + 4) := by
  mod_cases h : n % 2
  have h1: n ≡ 0 [ZMOD 2] := h
  have h11 : n^3 + 2 * n^2 + 3 * n + 4 ≡ 0 [ZMOD 2] := by
    calc
      n^3 + 2 * n^2 + 3 * n + 4
        ≡ (0^3) + (2 * 0^2) + (3 * 0) + 4 [ZMOD 2] := by
          rel [ModEq.pow 3 h1,
               ModEq.mul_left 2 (ModEq.pow 2 h1),
               ModEq.mul_left 3 h1
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rwa [modEq_zero_iff_dvd] at h11

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : n^3 + 2 * n^2 + 3 * n + 4 ≡ 0 [ZMOD 2] := by
    calc
      n^3 + 2 * n^2 + 3 * n + 4
        ≡ (1^3) + (2 * 1^2) + (3 * 1) + 4 [ZMOD 2] := by
          rel [ModEq.pow 3 h2,
               ModEq.mul_left 2 (ModEq.pow 2 h2),
               ModEq.mul_left 3 h2
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rwa [modEq_zero_iff_dvd] at h21

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

theorem problem_2 (n : ℤ) : 2 ∣ (-7 * n^2 + 11 * n + 8) := by
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
  rwa [modEq_zero_iff_dvd] at h11

  have h2: n ≡ 1 [ZMOD 2] := h
  have h21 : -7 * n^2 + 11 * n + 8 ≡ 0 [ZMOD 2] := by
    calc
      -7 * n^2 + 11 * n + 8
        ≡ -7 * 1^2 + 11 * 1 + 8 [ZMOD 2] := by
          rel [ModEq.mul_left (-7) (ModEq.pow 2 h2),
               ModEq.mul_left 11 h2
              ]
      _ ≡ 0 [ZMOD 2] := by rw [modEq_iff_dvd]; norm_num
  rwa [modEq_zero_iff_dvd] at h21
