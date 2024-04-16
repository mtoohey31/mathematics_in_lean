import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    apply add_le_add (le_abs_self x) (le_abs_self y)
  · rw [abs_of_neg h]
    rw [neg_add]
    apply add_le_add (neg_le_abs_self x) (neg_le_abs_self y)

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
      exact Or.inl
    · rw [abs_of_neg h]
      exact Or.inr
  · rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
      rintro (h' | h')
      · exact h'
      · linarith
    · rw [abs_of_neg h]
      rintro (h' | h')
      · linarith
      · exact h'

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
      intro h'
      constructor <;> linarith
    · rw [abs_of_neg h]
      intro h'
      constructor <;> linarith
  · rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
      exact And.right
    · rw [abs_of_neg h]
      intro h'
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨a, b, h | h⟩; repeat linarith [pow_two_nonneg a, pow_two_nonneg b]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1 : x ^ 2 = (x + 1) * (x - 1) + 1 := by ring
  have h2 : (x + 1) * (x - 1) = 0 := by
    rw [<- add_left_inj 1, zero_add, <- h1]
    exact h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h2 with h3 | h3
  . right
    rw [<- add_left_inj 1]
    simp
    exact h3
  . left
    rw [<- add_left_inj 1] at h3
    simp at h3
    exact h3

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1 : x ^ 2 - y ^ 2 = (x + y) * (x - y) := by ring
  have h2 : (x + y) * (x - y) = 0 := by
    rw [<- h1, <- add_left_inj (y ^ 2)]
    simp
    exact h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h2 with h3 | h3
  . right
    rw [<- add_left_inj y]
    simp
    exact h3
  . left
    rw [<- add_left_inj y] at h3
    simp at h3
    exact h3

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1 : x ^ 2 = (x + 1) * (x - 1) + 1 := by ring
  have h2 : (x + 1) * (x - 1) = 0 := by
    rw [<- add_left_inj 1, zero_add, <- h1]
    exact h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h2 with h3 | h3
  . right
    rw [<- add_left_inj 1]
    simp
    exact h3
  . left
    rw [<- add_left_inj 1] at h3
    simp at h3
    exact h3

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1 : x ^ 2 - y ^ 2 = (x + y) * (x - y) := by ring
  have h2 : (x + y) * (x - y) = 0 := by
    rw [<- h1, <- add_left_inj (y ^ 2)]
    simp
    exact h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h2 with h3 | h3
  . right
    rw [<- add_left_inj y]
    simp
    exact h3
  . left
    rw [<- add_left_inj y] at h3
    simp at h3
    exact h3

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  . intro h
    by_cases h' : P
    . right
      exact h h'
    . exact Or.inl h'
  . intro h p
    rcases h with h' | h'
    . contradiction
    . exact h'

