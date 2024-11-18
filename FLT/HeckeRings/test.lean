/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.Commensurable
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Finsupp
/-

# Construction of Hecke rings following Shimura

We define Hecke rings abstractly as a ring of formal sums of double cosets `HgH`, with H a subgroup
of a group G, and `g` in a submonoid `Δ` of the commensurator of `H`.

In practice we might have `G = GL₂(ℚ)` (which will also be the relevant commensurator)
and `H = SL₂(ℤ)`, and `Δ = Δ₀(N)` (this is where the condition on the determininat being positive
comes in).

## TODO

show they are rings (associativity is gonna be hard). golf/clean everything

-/
open Commensurable Classical Doset MulOpposite Set

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G) (h₀ : H.toSubmonoid ≤ Δ)
  (h₁ : (Δ ≤ (commensurator H).toSubmonoid))

instance sr : Semiring (Set G) where
  add f g := f ∪ g
  add_assoc := union_assoc
  zero := ⊥
  zero_add := by 
    intro a
    have : ⊥ ∪ a = a := by simp 
    exact this
  add_zero := by
    intro a
    have : a ∪ ⊥ = a := by simp 
    exact this
  nsmul n s := ⋃ i : Fin n, s
  nsmul_zero := by
    intro s 
    simp 
    rfl 
  nsmul_succ := by 
    intro n s 
    simp 
    simp [iUnion_const]
    by_cases h : n = 0
    rw [h]
    simp
    have : ⊥ ∪ s = s := by simp 
    nth_rw 1 [← this]
    rfl
    haveI : Nonempty (Fin n) :=  by refine Fin.pos_iff_nonempty.mp (by omega)
    simp [iUnion_const]
    have : s ∪ s = s := by simp
    exact this.symm 
  add_comm f g := union_comm f g
  mul f g := f * g 
  left_distrib := _
  right_distrib := _
  zero_mul := _
  mul_zero := _
  mul_assoc := _
  one := {1}
  one_mul := _
  mul_one := _
  natCast n := ⋃ i : Fin n, {1}
  natCast_zero := _
  natCast_succ := _
  npow n s := s ^ n
  npow_zero := _
  npow_succ := _


end HeckeRing
