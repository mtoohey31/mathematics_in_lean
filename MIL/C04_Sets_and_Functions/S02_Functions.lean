import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . intro fpssv
    intro x xs
    apply fpssv
    use x
  . intro ssfpv
    rintro x ⟨y, ys, fyx, rfl⟩
    exact ssfpv ys

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x xin
  have ⟨y, yins, fyeqfx⟩ := xin
  have h' : x = y := symm (h fyeqfx)
  rw [h']
  exact yins

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x xin
  have ⟨y, yin, fyeqx⟩ := xin
  have fyin : f y ∈ u := yin
  rw [fyeqx] at fyin
  exact fyin

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x xinu
  show ∃ y ∈ f ⁻¹' u, f y = x
  by_contra! h'
  dsimp [Surjective] at h
  have ⟨z, fz⟩ := h x
  apply h' z
  show f z ∈ u
  rw [fz]
  . exact xinu
  . exact fz

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x xin
  have ⟨y, yin, fyeqx⟩ := xin
  use y
  exact ⟨h yin, fyeqx⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := fun _ xin ↦ h xin

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor <;>
  . intro xin
    rcases xin with fxinu | fxinv
    . left
      exact fxinu
    . right
      exact fxinv

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x xin
  have ⟨y, ⟨yins, yint⟩, fyeqx⟩ := xin
  constructor <;> use y

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro x ⟨⟨y, yins, fyeqx⟩, ⟨z, zint, fzeqx⟩⟩
  use y
  constructor
  . constructor
    . exact yins
    . have h' : y = z := by
        apply h
        rw [fyeqx, fzeqx]
      rw [h']
      exact zint
  . exact fyeqx

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro x ⟨⟨y, yins, fyeqx⟩, xninft⟩
  use y
  constructor
  . constructor
    . exact yins
    . contrapose! xninft
      use y
  . exact fyeqx

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
  fun _ ⟨xinfpu, xninfpv⟩ ↦ ⟨xinfpu, xninfpv⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  . rintro ⟨⟨y, yins, fyeqx⟩, xinv⟩
    use y
    constructor
    . constructor
      . exact yins
      . show f y ∈ v
        rw [fyeqx]
        exact xinv
    . exact fyeqx
  . rintro ⟨y, ⟨yins, fyinv⟩, fyeqx⟩
    constructor
    . use y
    . rw [←fyeqx]
      exact fyinv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro x ⟨y, ⟨yins, fyinv⟩, fyeqx⟩
  constructor
  . use y
  . rw [←fyeqx]
    exact fyinv

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xins, fxinu⟩
  show f x ∈ f '' s ∩ u
  constructor
  . use x
  . exact fxinu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x
  intro xin
  rcases xin with xins | xinfpu
  . left
    use x
  . exact Or.inr xinfpu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  constructor
  . rintro ⟨y, yinuai, fyeqx⟩
    simp only [mem_iUnion] at *
    have ⟨i, yinai⟩ := yinuai
    use i, y
  . intro xinuai
    simp only [mem_iUnion] at xinuai
    have ⟨i, ⟨y, yinai, fyeqx⟩⟩ := xinuai
    use y
    constructor
    . simp only [mem_iUnion]
      use i
    . exact fyeqx


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro x ⟨y, yinuai, fyeqx⟩
  simp only [mem_iInter] at *
  intro i
  use y
  constructor
  . exact yinuai i
  . exact fyeqx

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro x xinufai
  simp only [mem_iInter] at xinufai
  have ⟨y, _, fyeqx⟩ := xinufai i
  use y
  constructor
  . simp only [mem_iInter]
    intro i'
    have ⟨z, xinai', fzeqx⟩ := xinufai i'
    have h : y = z := by
      apply injf
      rw [fyeqx, fzeqx]
    rw [h]
    exact xinai'
  . exact fyeqx

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor
  . intro xin
    have fxin : f x ∈ ⋃ i, B i := xin
    simp only [mem_iUnion] at *
    have ⟨i, fxinbi⟩ := fxin
    use i
    exact fxinbi
  . intro xin
    show f x ∈ ⋃ i, B i
    simp only [mem_iUnion] at *
    have ⟨i, fxin⟩ := xin
    use i
    exact fxin

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor
  . intro xin
    have fxin : f x ∈ ⋂ i, B i := xin
    simp only [mem_iInter] at *
    intro i
    exact fxin i
  . intro xin
    show f x ∈ ⋂ i, B i
    simp only [mem_iInter] at *
    intro i
    exact xin i

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnneg y ynneg
  intro e
  calc
    x = (sqrt x) ^ 2 := symm (sq_sqrt xnneg)
    _ = (sqrt y) ^ 2 := by rw [e]
    _ = y := sq_sqrt ynneg

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnneg y ynneg
  intro e
  dsimp at e
  calc
    x = sqrt (x ^ 2) := symm (sqrt_sq xnneg)
    _ = sqrt (y ^ 2) := by rw [e]
    _ = y := sqrt_sq ynneg

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext z
  constructor
  . rintro ⟨y, _, rfl⟩
    exact sqrt_nonneg y
  . intro zin
    use z ^ 2
    constructor
    . exact sq_nonneg z
    . exact sqrt_sq zin

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  constructor
  . rintro ⟨y, rfl⟩
    exact sq_nonneg y
  . intro xin
    use sqrt x
    exact sq_sqrt xin

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . intro h' x
    have h'' : ∃ y, f y = f x := by use x
    rw [inverse, dif_pos]
    apply h'
    apply Classical.choose_spec h''
  . intro inv x y e
    dsimp [LeftInverse] at inv
    calc
      x = inverse f (f x) := symm (inv x)
      _ = inverse f (f y) := by rw [e]
      _ = y := inv y

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  . intro h' x
    have h'' : ∃ y, f y = x := h' x
    rw [inverse, dif_pos h'']
    apply Classical.choose_spec h''
  . intro inv y
    use inverse f y
    exact inv y

example : Surjective f ↔ RightInverse (inverse f) f :=
  ⟨
    fun sur x ↦
    let h'' : ∃ y, f y = x := sur x
    by rw [inverse, dif_pos h'']; exact Classical.choose_spec h'',
    fun inv y ↦ Exists.intro (inverse f y) (inv y)
  ⟩

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    dsimp [S]
    push_neg
    rwa [h]
  contradiction

-- COMMENTS: TODO: improve this
end
