import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have ngeNs : n ≥ Ns := by
    apply ge_trans nge
    exact le_max_left Ns Nt
  have ngeNt : n ≥ Nt := by
    apply ge_trans nge
    exact le_max_right Ns Nt
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := abs_add (s n - a) (t n - b)
    _ < ε / 2 + ε / 2 := add_lt_add (hs n ngeNs) (ht n ngeNt)
    _ = ε := by norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  use Ns
  intro n nge
  calc
    |c * s n - c * a| = |c * (s n - a)| := by
      congr
      linarith
    _ = |c| * |s n - a| := abs_mul c (s n - a)
    _ < |c| * (ε / |c|) := (mul_lt_mul_left acpos).mpr (hs n nge)
    _ = |c| / |c| * ε := (mul_comm_div |c| |c| ε).symm
    _ = 1 * ε := by
      congr
      apply div_self
      exact ne_of_gt acpos
    _ = ε := by norm_num

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n Nlen
  have sb : |s n - a| < 1 := h n Nlen
  have h0 : |a| + |s n - a| < |a| + 1 := (add_lt_add_iff_left |a|).mpr sb
  have h1 : |a + (s n - a)| ≤ |a| + |s n - a| := by apply abs_add
  have h2 : |a + (s n - a)| < |a| + 1 := LE.le.trans_lt h1 h0
  convert h2
  ring

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n ngeN
  have sb : |s n| < B := h₀ n (le_of_max_le_left ngeN)
  have tb : |t n - 0| < ε / B := h₁ n (le_of_max_le_right ngeN)
  rw [sub_zero] at tb
  rw [sub_zero, abs_mul, ←one_mul ε, ←div_self (ne_of_gt Bpos), ←mul_div_right_comm, mul_div_assoc]
  exact mul_lt_mul' (le_of_lt sb) tb (abs_nonneg (t n)) Bpos

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply gt_iff_lt.mpr
    apply lt_of_le_of_ne (abs_nonneg (a - b))
    contrapose! abne with abeqz
    symm at abeqz
    rw [<- sub_left_inj, sub_self b]
    exact (abs_eq_zero).mp abeqz
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_max_left _ _)
  have absb : |s N - b| < ε := hNb N (le_max_right _ _)
  have : |a - b| < |a - b| := calc
    |a - b| = |b - a| := abs_sub_comm _ _
    _ = |(s N - a) + -(s N - b)| := by ring
    _ ≤ |s N - a| + |-(s N - b)| := abs_add _ _
    _ = |s N - a| + |s N - b| := by rw [abs_neg]
    _ < ε + ε := add_lt_add absa absb
    _ = |a - b| := by ring
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
