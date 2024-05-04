import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    apply even_of_even_sqr
    apply dvd_iff_exists_eq_mul_left.mpr
    use n ^ 2
    rw [mul_comm]
    exact sqr_eq
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 := (mul_right_inj' (Nat.succ_ne_zero 1)).mp this
  have : 2 ∣ n := by
    apply even_of_even_sqr
    apply dvd_iff_exists_eq_mul_left.mpr
    use k ^ 2
    rw [mul_comm]
    symm
    exact this
  have : 2 ∣ m.gcd n := by
    apply Nat.dvd_gcd
    repeat assumption
  have : 2 ∣ 1 := by
    rw [coprime_mn] at this
    exact this
  norm_num at this

theorem dvd_p_of_dvd_p_sqr {m p : ℕ} (prime_p : p.Prime) (h : p ∣ m ^ 2) : p ∣ m := by
  rw [pow_two, prime_p.dvd_mul] at h
  cases h <;> assumption

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have : p ∣ m := by
    apply dvd_p_of_dvd_p_sqr prime_p
    apply dvd_iff_exists_eq_mul_left.mpr
    use n ^ 2
    rw [mul_comm]
    exact sqr_eq
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : p * k ^ 2 = n ^ 2 := (mul_right_inj' (Nat.Prime.ne_zero prime_p)).mp this
  have : p ∣ n := by
    apply dvd_p_of_dvd_p_sqr prime_p
    apply dvd_iff_exists_eq_mul_left.mpr
    use k ^ 2
    rw [mul_comm]
    symm
    exact this
  have : p ∣ m.gcd n := by
    apply Nat.dvd_gcd
    repeat assumption
  have : p ∣ 1 := by
    rw [coprime_mn] at this
    exact this
  have : p ≤ 1 := by
    apply Nat.le_of_dvd
    · norm_num
    · assumption
  have : 2 ≤ p := Nat.Prime.two_le prime_p
  absurd this
  push_neg
  apply Nat.lt_succ.mpr
  assumption

#check Nat.factors
#check Nat.prime_of_mem_factors
#check Nat.prod_factors
#check Nat.factors_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have p_nez : p ≠ 0 := Nat.Prime.ne_zero prime_p
  have pnsqr_nez : p * n ^ 2 ≠ 0 := by
    apply mul_ne_zero <;> assumption
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    rw [pow_two, two_mul]
    have mnz : m ≠ 0 := by
      rw [←sqr_eq] at pnsqr_nez
      exact right_ne_zero_of_mul pnsqr_nez
    exact factorization_mul' mnz mnz p
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [factorization_mul' p_nez nsqr_nez, Nat.Prime.factorization' prime_p, factorization_pow']
    ring
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} (prime_p : p.Prime) :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := factorization_pow' _ _ _
  have eq2 : (r.succ * n ^ k).factorization p =
      k * n.factorization p + r.succ.factorization p := by
    rw [factorization_mul' (Nat.succ_ne_zero r) npow_nz, factorization_pow']
    ring
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  apply Nat.dvd_sub' <;> apply Nat.dvd_mul_right

#check multiplicity
