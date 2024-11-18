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

variable {G α : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G) (h₀ : H.toSubmonoid ≤ Δ)
  (h₁ : (Δ ≤ (commensurator H).toSubmonoid))

lemma ConjAct_smul_coe_Eq (g : G) :  ((ConjAct.toConjAct g • H) : Set G) = {g} * H * {g⁻¹} := by
  ext x
  refine ⟨ ?_, ?_⟩ <;>  intro h
  · rw [mem_smul_set] at h
    obtain ⟨a, ha⟩ := h
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at ha
    rw [← ha.2]
    simp only [singleton_mul, image_mul_left, mul_singleton, image_mul_right, inv_inv, mem_preimage,
      inv_mul_cancel_right, inv_mul_cancel_left, SetLike.mem_coe, ha.1]
  · rw [mem_smul_set]
    use g⁻¹ * x * g
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    group
    simp only [singleton_mul, image_mul_left, mul_singleton, image_mul_right, inv_inv, mem_preimage,
      SetLike.mem_coe, Int.reduceNeg, zpow_neg, zpow_one, and_true] at *
    rw [← mul_assoc] at h
    exact h

lemma ConjAct_smul_elt_eq (h : H) : ConjAct.toConjAct (h : G) • H = H := by
  have : ConjAct.toConjAct (h : G) • (H : Set G) = H := by
    rw [ConjAct_smul_coe_Eq,Subgroup.singleton_mul_subgroup h.2,
      Subgroup.subgroup_mul_singleton (by simp)]
  rw [← Subgroup.coe_pointwise_smul] at this
  norm_cast at *


/-maybe call this commensurable pair??-/
/-- This is a pair cosisting of a subgroup `H` and a submonoid `Δ` of some group, such that
`H ≤ Δ ≤ commensurator H`. -/
structure ArithmeticGroupPair (G : Type*) [Group G]  where
  H : Subgroup G
  Δ : Submonoid G
  h₀ : H.toSubmonoid ≤ Δ
  h₁ : Δ ≤ (commensurator H).toSubmonoid

/--Given an arithmetic pair `P`, consisting of a subgroup `H` of `G` and a submonoid `Δ` of
the commensurator of H, this is  the data of a set in `G` equal to some double coset
`HgH`, with `g : Δ`. -/
structure T' (P : ArithmeticGroupPair G) where
  set : Set G
  eql : ∃ s : Finset P.Δ,  set = ⋃ (i ∈ s), Doset.doset (i : G) P.H P.H

def T (P : ArithmeticGroupPair G) := {set : Set G | ∃ s : Finset P.Δ,  
    set = ⋃ (i ∈ s), Doset.doset (i : G) P.H P.H }

lemma T_mem (P : ArithmeticGroupPair G) (S : Set G) : S ∈ T P ↔ ∃ s : Finset P.Δ,  
    S = ⋃ (i ∈ s), Doset.doset (i : G) P.H P.H := by rfl 

lemma union_mem (P : ArithmeticGroupPair G) (a b : T P) : a.1 ∪ b ∈ T P := by
  rw [T_mem]
  use a.2.choose ∪ b.2.choose
  have ha := a.2.choose_spec
  have hb := b.2.choose_spec
  have := congrFun (congrArg Union.union ha) b.1 
  rw [@Finset.set_biUnion_union]
  nth_rw 2 [hb] at this 
  rw [this]


  
  


/-
noncomputable instance uninon_monoid : Monoid (Set G) where
  mul f g := f ∪ g
  mul_assoc f g h := union_assoc f g h
  one := ⊥
  one_mul := by
    intro a
    have : ⊥ ∪ a = a := by simp only [bot_eq_empty, empty_union]
    exact this
  mul_one := by
    intro a
    have : a ∪ ⊥ = a := by simp only [bot_eq_empty, union_empty]
    exact this
-/

structure M (P : ArithmeticGroupPair G) where
  set : Set G
  eql : ∃ elt : P.Δ,  set = {(elt : G)} * (P.H : Set G)

@[ext]
lemma ext (P : ArithmeticGroupPair G) (D1 D2 : T' P) (h : D1.set = D2.set): D1 = D2 := by
  cases D1
  cases D2
  simp at *
  exact h


/--Make an element of `T' P` given an element `g : P.Δ`, i.e make `HgH`.  -/
def T_mk (P : ArithmeticGroupPair G) (g : P.Δ) : T' P := ⟨doset g P.H P.H, {g} , by simp⟩

/--Make an element of `M P` given an element `g : P.Δ`, i.e make `gH`.  -/
def M_mk (P : ArithmeticGroupPair G) (g : P.Δ) : M P := ⟨{(g : G)} * (P.H : Set G), g, rfl⟩

/--The multiplicative identity. -/
def T_one (P : ArithmeticGroupPair G) : T' P := T_mk P (1 : P.Δ)

def M_one (P : ArithmeticGroupPair G) : M P := M_mk P (1 : P.Δ)

lemma smul_eq_mul_singleton (s : Set G) (g : G) : g • s = {g} * s := by
    rw [← Set.singleton_smul]
    exact rfl

lemma set_eq_iUnion_leftCosets (K : Subgroup G) (hK : K ≤ H) : (H : Set G) = ⋃ (i : H ⧸ K.subgroupOf H),
    (i.out' : G) • (K : Set G) := by
  ext a
  constructor
  · intro ha
    simp only [mem_iUnion]
    use (⟨a, ha⟩ : H)
    have := QuotientGroup.mk_out'_eq_mul (K.subgroupOf H) (⟨a, ha⟩ : H)
    obtain ⟨h, hh⟩ := this
    rw [hh]
    simp
    refine mem_smul_set.mpr ?h.intro.a
    have : (h : H) • (K : Set G) = K := by
      apply smul_coe_set
      simp
      refine Subgroup.mem_subgroupOf.mp ?ha.a
      simp only [SetLike.coe_mem]
    use h⁻¹
    simp
    refine Subgroup.mem_subgroupOf.mp ?h.a
    exact SetLike.coe_mem h
  · intro ha
    simp only [mem_iUnion] at ha
    obtain ⟨i, hi⟩ := ha
    have :  Quotient.out' i • (K : Set G) ⊆ (H : Set G) := by
      intro a ha
      rw [mem_smul_set] at ha
      obtain ⟨h, hh⟩ := ha
      rw [← hh.2]
      simp
      rw [show  Quotient.out' i • h =  Quotient.out' i * h by rfl]
      apply mul_mem
      simp
      apply hK hh.1
    exact this hi

lemma ConjAct_mul_self_eq_self (g : G) : ((ConjAct.toConjAct g • H) : Set G) *
    (ConjAct.toConjAct g • H) = (ConjAct.toConjAct g • H) := by
  rw [ConjAct_smul_coe_Eq , show {g} * (H : Set G) * {g⁻¹} * ({g} * ↑H * {g⁻¹}) = {g} * ↑H *
      (({g⁻¹} * {g}) * ↑H) * {g⁻¹} by simp_rw [← mul_assoc],Set.singleton_mul_singleton ]
  conv =>
    enter [1,1,2]
    simp
  conv =>
    enter [1,1]
    rw [mul_assoc, coe_mul_coe H]

lemma inter_mul_conjact_eq_conjact (g : G) : ((H : Set G) ∩ (ConjAct.toConjAct g • H)) *
    (ConjAct.toConjAct g • H) = (ConjAct.toConjAct g • H) := by
  have := Set.inter_mul_subset (s₁ := (H : Set G)) (s₂ := (ConjAct.toConjAct g • H))
    (t := (ConjAct.toConjAct g • H))
  apply Subset.antisymm
  · apply le_trans this
    simp only [ConjAct_mul_self_eq_self, le_eq_subset, inter_subset_right]
  · refine subset_mul_right (ConjAct.toConjAct g • (H : Set G)) ?h₂.hs
    simp only [mem_inter_iff, SetLike.mem_coe]
    refine ⟨  Subgroup.one_mem H, Subgroup.one_mem (ConjAct.toConjAct g • H)⟩

lemma mul_singleton_cancel (g : G) (K L : Set G)  (h:  K * {g} = L * {g}) : K = L := by
  have h2 := congrFun (congrArg HMul.hMul h) {g⁻¹}
  simp_rw [mul_assoc, Set.singleton_mul_singleton] at h2
  simpa using h2

lemma doset_eq_iUnion_leftCosets (g : G) : doset g H H =
  ⋃ (i : (H ⧸ (ConjAct.toConjAct g • H).subgroupOf H)), (i.out' * g) • (H : Set G) := by
  rw [doset]
  have := set_eq_iUnion_leftCosets H (((ConjAct.toConjAct g • H).subgroupOf H).map H.subtype)
  simp only [Subgroup.subgroupOf_map_subtype, inf_le_right, Subgroup.coe_inf,
    Subgroup.coe_pointwise_smul, true_implies] at this
  have h2 := congrFun (congrArg HMul.hMul this) ((ConjAct.toConjAct g • H) : Set G)
  rw [iUnion_mul, inter_comm] at h2
  apply mul_singleton_cancel g⁻¹
  rw [ConjAct_smul_coe_Eq ] at *
  simp_rw [← mul_assoc] at h2
  rw [h2]
  have : (Subgroup.map H.subtype ((ConjAct.toConjAct g • H).subgroupOf H)).subgroupOf H =
    (ConjAct.toConjAct g • H).subgroupOf H := by
    simp
  rw [this]
  have h1 : ∀ (i : H ⧸ (ConjAct.toConjAct g • H).subgroupOf H),
    ((i.out') : G) • ((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) * {g} * ↑H * {g⁻¹} =
      (↑(Quotient.out' i) * g) • ↑H * {g⁻¹} := by
    intro i
    have := inter_mul_conjact_eq_conjact H g
    rw [ConjAct_smul_coe_Eq ] at this
    have hr : ((i.out' ) : G) • ((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) * {g} * ↑H * {g⁻¹} =
      (i.out' : G) • (((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) * {g} * ↑H * {g⁻¹}) := by
      simp_rw [smul_mul_assoc]
    rw [hr]
    simp_rw [← mul_assoc] at this
    conv =>
      enter [1,2]
      rw [this]
    simp_rw [smul_eq_mul_singleton, ← singleton_mul_singleton, ← mul_assoc]
  have := iUnion_congr h1
  convert this
  rw [iUnion_mul]

lemma doset_mul_doset_left (g h : G) :
    (doset g H H) * (doset h H H) = (doset (g) H H) * {h} * H := by
  simp_rw [doset, show (H : Set G) * {g} * (H : Set G) * (H * {h} * H) =
    H * {g} * (H * H) * {h} * H by simp_rw [← mul_assoc], coe_mul_coe H]

lemma doset_mul_doset_right (g h : G) :
    (doset g H H) * (doset h H H) = H * {g} * (doset (h) H H) := by
  simp_rw [doset, show (H : Set G) * {g} * (H : Set G) * (H * {h} * H) =
    H * {g} * (H * H) * {h} * H by simp_rw [← mul_assoc], coe_mul_coe H, ← mul_assoc]

lemma doset_mul_doset_eq_union_doset (g h : G) :
    (doset (g : G) (H : Set G) H) * doset (h : G) (H : Set G) H =
        ⋃ (i : H ⧸ (ConjAct.toConjAct h • H).subgroupOf H), doset (g * i.out' * h : G) H H := by
  rw [doset_mul_doset_right, doset_eq_iUnion_leftCosets, Set.mul_iUnion]
  simp_rw [doset]
  have h1 : ∀ (i : H ⧸ (ConjAct.toConjAct h • H).subgroupOf H),
    (H : Set G) * {g} * (↑(Quotient.out' i) * h) • ↑H = ↑H * {g * ↑(Quotient.out' i) * h} * ↑H := by
    intro i
    rw [smul_eq_mul_singleton, show (H : Set G) * {g} * ({↑(Quotient.out' i) * h} * ↑H) =
      H * {g} * {↑(Quotient.out' i) * h} * ↑H by simp_rw [← mul_assoc],
        ← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton]
    simp_rw [← mul_assoc]
  apply iUnion_congr h1




/--Finite linear combinations of double cosets `HgH` with `g` in the commensurator of `H`. -/
def 𝕋 (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] := Finsupp (T' P) Z

def 𝕄 (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] := Finsupp (M P) Z

variable  (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z]

noncomputable instance (P : ArithmeticGroupPair G) (D : T' P) (r : D.eql.choose) :
    Fintype (P.H ⧸ ((ConjAct.toConjAct (r : G)) • P.H).subgroupOf P.H) := by
  apply Subgroup.fintypeOfIndexNeZero (P.h₁ (SetLike.coe_mem _)).1

lemma doset_mul_doset_mem (P : ArithmeticGroupPair G) (a b : P.Δ) : Doset.doset (a : G) P.H P.H *
    Doset.doset (b : G) P.H P.H ∈ T P := by
  rw [T_mem]
  sorry 

lemma mul_mem (a b : T P) : a.1 * b ∈ T P := by
  rw [T_mem]
  sorry

noncomputable instance : Mul (T P) where
    mul a b := ⟨a * b, mul_mem P a b⟩

instance : Ring (Finsupp (T P) Z) :=     



lemma rep_mem (a b : Δ) (i : H) : (a : G) * i * b ∈ Δ := by
  rw [mul_assoc]
  apply Submonoid.mul_mem _ (a.2) (Submonoid.mul_mem _ (h₀ i.2) b.2)

lemma rep_mem2  (i : H) (a b : Δ) : a * (i : G) * b ∈ Δ := by
 rw [mul_assoc]
 apply Submonoid.mul_mem _ (a.2) (Submonoid.mul_mem _ (h₀ i.2) b.2)

/-Test func. not needed
noncomputable def mul' (D1 D2 : T' H Δ) : 𝕋 H Δ :=
    ((∑ (i : H ⧸ (ConjAct.toConjAct (D2.elt : G) • H).subgroupOf H),
      Finsupp.single (T_mk H Δ D1.h₀ D1.h₁ ⟨((D1.elt : G) * (i.out' : G) * (D2.elt : G)),
        rep_mem H Δ D1.h₀ D1.elt D2.elt i.out'⟩) (1 : ℤ) : (T' H Δ) →₀ ℤ))
-/

noncomputable instance addCommMonoid : AddCommGroup (𝕋 P Z) :=
  inferInstanceAs (AddCommGroup ((T' P) →₀ Z))

noncomputable instance 𝕄addCommGroup : AddCommGroup (𝕄 P Z) :=
  inferInstanceAs (AddCommGroup ((M P) →₀ Z))



/-- Take two doble cosets `HgH` and `HhH`, we define `HgH`*`HhH` by the sum over the double cosets
in `HgHhH`, i.e., if `HgHhH = ⋃ i, HiH` , then `HgH * HhH = ∑ i, HiH` and then extends
linearly to get multiplication on the finite formal sums of double cosets. -/
noncomputable instance (P : ArithmeticGroupPair G) : Mul (𝕋 P Z) where
 mul f g := Finsupp.sum f (fun D1 b₁ => g.sum fun D2 b₂ =>
    ((∑ (i : P.H ⧸ (ConjAct.toConjAct (D2.eql.choose : G) • P.H).subgroupOf P.H),
      Finsupp.single (T_mk P ⟨((D1.eql.choose : G) * (i.out' : G) * (D2.eql.choose : G)),
        rep_mem P.H P.Δ P.h₀ D1.eql.choose D2.eql.choose i.out'⟩) (b₁ * b₂ : Z)) : (T' P) →₀ Z))

lemma mul_def (f g : 𝕋 P Z) : f * g = Finsupp.sum f (fun D1 b₁ => g.sum fun D2 b₂ =>
    ((∑ (i : P.H ⧸ (ConjAct.toConjAct (D2.eql.choose : G) • P.H).subgroupOf P.H),
      Finsupp.single (T_mk P ⟨((D1.eql.choose : G) * (i.out' : G) * (D2.eql.choose : G)),
        rep_mem P.H P.Δ P.h₀ D1.eql.choose D2.eql.choose i.out'⟩) (b₁ * b₂ : Z)) : (T' P) →₀ Z)) := rfl

noncomputable abbrev T_single (a : T' P) (b : Z) : (𝕋 P Z) := Finsupp.single a b

noncomputable abbrev M_single (a : M P) (b : Z) : (𝕄 P Z) := Finsupp.single a b

lemma 𝕋_mul_singleton (D1 D2 : (T' P)) (a b : Z) :
  (T_single P Z D1 a) * (T_single P Z D2 b) =
    ((∑ (i : P.H ⧸ (ConjAct.toConjAct (D2.eql.choose : G) • P.H).subgroupOf P.H),
      Finsupp.single (T_mk P ⟨((D1.eql.choose : G) * (i.out' : G) * (D2.eql.choose : G)),
        rep_mem P.H P.Δ P.h₀ D1.eql.choose D2.eql.choose i.out'⟩) (a * b : Z)) : (T' P) →₀ Z) := by
  rw [T_single, mul_def]
  simp only [mul_zero, Finsupp.single_zero, Finset.sum_const_zero, Finsupp.sum_single_index,
    zero_mul, Int.cast_mul]

open Finsupp

noncomputable instance nonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (𝕋 P Z) :=
  {  (addCommMonoid P Z) with
    left_distrib := fun f g h => by
      simp only [mul_def]
      refine Eq.trans (congr_arg (Finsupp.sum f) (funext₂ fun a₁ b₁ => Finsupp.sum_add_index ?_ ?_))
        ?_ <;>
        simp
      intro D1 _ a b
      rw [← Finset.sum_add_distrib ]
      congr
      group
      simp only [Finsupp.single_add]
    right_distrib := fun f g h => by
      simp only [mul_def]
      refine Eq.trans (Finsupp.sum_add_index ?_ ?_) ?_ <;>
        simp
      intro D1 _ a b
      rw [← Finsupp.sum_add]
      apply congr_arg
      ext i
      rw [← Finset.sum_add_distrib ]
      congr
      group
      simp only [Finsupp.single_add]
    zero_mul := fun f => by
      simp only [mul_def]
      exact Finsupp.sum_zero_index
    mul_zero := fun f => by
      simp only [mul_def]
      exact Eq.trans (congr_arg (sum f) (funext₂ fun a₁ b₁ => sum_zero_index)) sum_zero }


noncomputable instance smul : SMul (𝕋 P Z) (𝕋 P Z) where
  smul := (·  *  · )

/-- Define `HgH • v H = ∑ i, v*a_i*g H` with the sum elements comming form
`doset_eq_iUnion_leftCosets` and then extend linearly. This is like defining
`HgH • v H = v H * HgH` and turning unions into sums. There should be a clean way to do this turning
union into sums...-/
noncomputable instance 𝕄smul : SMul (𝕋 P Z) (𝕄 P Z) where
  smul := fun t => fun mm => Finsupp.sum t (fun D1 b₁ => mm.sum fun m b₂ =>
    ((∑ (i : P.H ⧸ (ConjAct.toConjAct (D1.eql.choose : G) • P.H).subgroupOf P.H),
      Finsupp.single (M_mk P ⟨((m.eql.choose : G) * (i.out' : G) * (D1.eql.choose : G)),
        rep_mem2 P.H P.Δ P.h₀ i.out' m.eql.choose D1.eql.choose⟩) (b₁*b₂ : Z) : (M P) →₀ Z)))

lemma 𝕋smul_def (T : 𝕋 P Z) (m : 𝕄 P Z) : T • m = Finsupp.sum T (fun D1 b₁ => m.sum fun m b₂ =>
    ((∑ (i : P.H ⧸ (ConjAct.toConjAct (D1.eql.choose : G) • P.H).subgroupOf P.H),
      Finsupp.single (M_mk P ⟨((m.eql.choose : G) * (i.out' : G) * (D1.eql.choose : G)),
      rep_mem2 P.H P.Δ P.h₀ i.out' m.eql.choose D1.eql.choose⟩) (b₁*b₂ : Z) : (M P) →₀ Z))) := by rfl

noncomputable instance hSMul : HSMul (𝕋 P Z) (𝕄 P Z) (𝕄 P Z) := inferInstance

variable (t : T' P) (m : 𝕄 P Z) (a : Z)




lemma single_smul_single (t : T' P) (m : M P) (a b : Z) :
  (hSMul P Z).hSMul ((Finsupp.single t a) : 𝕋 P Z) ((Finsupp.single m b) : 𝕄 P Z)  =
  ((∑ (i : P.H ⧸ (ConjAct.toConjAct (t.eql.choose : G) • P.H).subgroupOf P.H),
      Finsupp.single (M_mk P ⟨((m.eql.choose : G) * (i.out' : G) * (t.eql.choose : G)),
      rep_mem2 P.H P.Δ P.h₀ i.out' m.eql.choose t.eql.choose⟩) (a * b : Z) : (M P) →₀ Z)) := by
  rw [𝕋smul_def]
  simp only [singleton_mul, image_mul_left, mul_zero, single_zero, Finset.sum_const_zero,
    sum_single_index, zero_mul]


lemma single_basis {α : Type*} (t : Finsupp α Z) : t = ∑ (i ∈ t.support), single i (t.toFun i) := by
  apply Finsupp.ext
  intro a
  simp_rw [Finsupp.finset_sum_apply, Finsupp.single_apply]
  simp only [Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not]
  aesop

lemma support_eq {α : Type*} (t s : Finsupp α Z) (h : t.support = s.support) (h2 :∀ a ∈ t.support,
  t a = s a) : t = s := by
  refine Finsupp.ext ?h
  intro a
  by_cases ha : a ∈ t.support
  exact h2 a ha
  have hsa := ha
  rw [h] at hsa
  rw [not_mem_support_iff] at *
  rw [ha, hsa]

#check (M_single P Z (M_one P) (1 : Z))

lemma smul_one𝕄 (a : 𝕋 P Z) : a • (M_single P Z (M_one P) (1 : Z))  = a := by sorry

lemma 𝕋eq_of_smul_eq_smul (T1 T2 : (𝕋 P Z)) (h : ∀ (a : 𝕄 P Z), T1 • a = T2 • a) : T1 = T2 := by



  /-
  let a := Finsupp.single (M_mk P (1 : P.Δ)) (1 : Z)
  have h1 := h a
  have h2 := single_basis Z ((hSMul P Z).hSMul T1 a)
  have h3 := single_basis Z ((hSMul P Z).hSMul T2 a)
  have ha := h1
  rw [h2, h3] at h1
  apply support_eq
  -/

  sorry

noncomputable instance 𝕄smulFaithful : FaithfulSMul (𝕋 P Z) (𝕄 P Z) where
  eq_of_smul_eq_smul  {t1 t2} h := 𝕋eq_of_smul_eq_smul P Z t1 t2 h

lemma smul_def (f g : 𝕋 P Z) : f • g = f * g := rfl

noncomputable instance isScalarTower : IsScalarTower (𝕋 P Z) (𝕋 P Z) (𝕄 P Z) := by sorry

lemma 𝕋_mul_assoc (f g h : 𝕋 P Z) : (f * g) * h = f * (g * h) := by

  have := (𝕄smulFaithful P Z).eq_of_smul_eq_smul (M := (𝕋 P Z)) (m₁ := (f * g) * h)
      (m₂ := f * (g * h) )
  apply this
  intro a
  have e1 :=  (isScalarTower P Z).smul_assoc f (g* h) a
  have e2 :=  (isScalarTower P Z).smul_assoc g h a
  have e3 :=  (isScalarTower P Z).smul_assoc (f  * g) h a
  have e4 :=  (isScalarTower P Z).smul_assoc f g (h • a)
  simp at *
  rw [e2] at e1
  rw [e4] at e3
  rw [e1, e3]

noncomputable instance nonUnitalSemiring : NonUnitalSemiring (𝕋 P Z) :=
  {nonUnitalNonAssocSemiring P Z  with
    mul_assoc := 𝕋_mul_assoc P Z} -- known in the 1980s so Kevin can't complain.


/- The identity is `H1H`. -/
noncomputable instance one : One (𝕋 P Z) := ⟨T_single P Z (T_one P) (1 : Z)⟩

theorem one_def : (1 : (𝕋 P Z)) = T_single P Z (T_one P) (1 : Z):=
  rfl

noncomputable instance nonAssocSemiring : NonAssocSemiring (𝕋 P Z) :=
  { nonUnitalNonAssocSemiring P Z with
    natCast := fun n => T_single P Z (T_one P) (n : Z)
    natCast_zero := by simp
    natCast_succ := fun _ => by simp; rfl
    one_mul :=  fun f => by
      simp [one_def, mul_def, one_mul, zero_mul, single_zero,
        Finset.sum_const_zero, sum_zero, sum_single_index, T_one, T_mk]

      have := Finsupp.sum_single  f
      nth_rw 2 [← this]
      congr
      ext D z v
      rw [Finsupp.finset_sum_apply]
      simp_rw [Finsupp.single_apply]
      sorry










    mul_one :=sorry }

noncomputable instance semiring : Semiring (𝕋 P Z) :=
  {HeckeRing.nonUnitalSemiring P Z,
    (HeckeRing.nonAssocSemiring P Z) with}

noncomputable instance addCommGroup : AddCommGroup (𝕋 P Z) :=
  Finsupp.instAddCommGroup

noncomputable instance nonAssocRing : NonAssocRing (𝕋 P Z) :=
  { HeckeRing.addCommGroup P Z,
    (HeckeRing.nonAssocSemiring P Z) with
    intCast := sorry
    intCast_ofNat := sorry
    intCast_negSucc := sorry }

noncomputable instance ring : Ring (𝕋 P Z) :=
    {HeckeRing.nonAssocRing P Z, HeckeRing.semiring P Z with }



end HeckeRing
