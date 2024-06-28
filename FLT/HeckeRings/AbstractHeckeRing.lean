/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.Commensurable
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Order
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
    rw [ConjAct_smul_coe_Eq, Subgroup.singleton_mul_subgroup h.2,
      Subgroup.subgroup_mul_singleton (by simp)]
  rw [← Subgroup.coe_pointwise_smul] at this
  norm_cast at *

--chatgpt gave me 70% of this proof
lemma sub_eq (a b : G) (h : {a} * (H : Set G) ⊆ {b} * H) : {a} * (H : Set G) = {b} * H := by
  have ha : a ∈ {a} * (H : Set G) := by
    rw [Set.mem_mul]
    use a
    simp [Subgroup.one_mem]
  have hb := h ha
  rw [Set.mem_mul] at hb
  obtain ⟨b', hb', y, hy, hb_eq⟩ := hb
  simp at hb'
  rw [← hb_eq, hb', ← Set.singleton_mul_singleton, mul_assoc, Subgroup.singleton_mul_subgroup hy]


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
  eql : ∃ elt : P.Δ,  set = Doset.doset (elt : G) P.H P.H

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
def T_mk (P : ArithmeticGroupPair G) (g : P.Δ) : T' P := ⟨doset g P.H P.H, g, rfl⟩

/--Make an element of `M P` given an element `g : P.Δ`, i.e make `gH`.  -/
def M_mk (P : ArithmeticGroupPair G) (g : P.Δ) : M P := ⟨{(g : G)} * (P.H : Set G), g, rfl⟩

/--The multiplicative identity. -/
def T_one (P : ArithmeticGroupPair G) : T' P := T_mk P (1 : P.Δ)

lemma T_one_eq (P : ArithmeticGroupPair G) : T_one P = T_mk P (1 : P.Δ) := rfl

lemma T_one_eq_doset_one (P : ArithmeticGroupPair G) : T_one P = ⟨doset (1 : P.Δ) P.H P.H, 1, rfl⟩ := rfl

lemma T_one_eq_doset_one' (P : ArithmeticGroupPair G) : doset ((T_one P).eql.choose : G) P.H P.H =
  doset (1 : G) P.H P.H := by
  have := (T_one P).eql.choose_spec
  have h2 := T_one_eq_doset_one P
  rw [h2] at this
  simp at this
  exact id (Eq.symm this)

lemma T_one_choose_eq (P : ArithmeticGroupPair G) : ∃ h₁ h₂ : P.H,
    h₁ * ((T_one P).eql.choose : G) * h₂ = 1 := by
  have := (T_one P).eql.choose_spec
  rw [T_one, T_mk] at this
  have h2 := (Doset.eq P.H P.H _ _).mp (Doset.mk_eq_of_doset_eq this.symm)
  obtain ⟨h₁, h1, h₂, h2 ⟩ := h2
  refine  ⟨⟨h₁,h1⟩, ⟨h₂,h2.1⟩,h2.2.symm⟩


lemma T_one_choose_mem_H (P : ArithmeticGroupPair G) : ((T_one P).eql.choose : G) ∈ P.H := by
  obtain ⟨h₁, h₂, h₃⟩ := T_one_choose_eq P
  rw [@mul_eq_one_iff_eq_inv, ← @eq_inv_mul_iff_mul_eq] at h₃
  rw [h₃]
  apply Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁.2) (Subgroup.inv_mem _ h₂.2)



lemma doset_mul_left_eq_self (P : ArithmeticGroupPair G) (h : P.H) (g : G) : doset ((h : G) * g) P.H P.H =
  doset g P.H P.H := by
  simp_rw [doset, ← singleton_mul_singleton, ← mul_assoc]
  conv =>
    enter [1,1,1]
    rw [Subgroup.subgroup_mul_singleton h.2]

lemma doset_mul_right_eq_self (P : ArithmeticGroupPair G) (h : P.H) (g : G) : doset ( g * h) P.H P.H =
  doset g P.H P.H := by
  simp_rw [doset, ← singleton_mul_singleton, ← mul_assoc]
  conv =>
    enter [1]
    rw [mul_assoc]
    rw [Subgroup.singleton_mul_subgroup h.2]



lemma doset_mul_assoc (f g h : G) : doset ((f * g) * h) H H = doset (f * (g * h)) H H := by
  simp_rw [doset, ← singleton_mul_singleton, ← mul_assoc]

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

lemma doset_one_mul (h : G) : doset (h : G) (H : Set G) H =
    ⋃ (_ : H ⧸ (ConjAct.toConjAct h • H).subgroupOf H), doset (h : G) H H := by
  simp [iUnion_const]


/--Finite linear combinations of double cosets `HgH` with `g` in the commensurator of `H`. -/
def 𝕋 (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] := Finsupp (T' P) Z

def 𝕄 (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] := Finsupp (M P) Z

variable  (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] [IsDomain Z]

noncomputable instance (P : ArithmeticGroupPair G) (D : T' P) :
    Fintype (P.H ⧸ ((ConjAct.toConjAct (D.eql.choose : G)) • P.H).subgroupOf P.H) := by
  have := (D.eql.choose.2 )
  apply Subgroup.fintypeOfIndexNeZero (P.h₁ D.eql.choose.2 ).1

noncomputable instance (P : ArithmeticGroupPair G) (D : T' P) :
  Finite (P.H ⧸ ((ConjAct.toConjAct (D.eql.choose : G)) • P.H).subgroupOf P.H) := by
  apply Finite.of_fintype

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

noncomputable example (s : Set G) (h : Nat.card s ≠ 0) : Finset G :=
  Set.Finite.toFinset (Nat.finite_of_card_ne_zero h)

abbrev Q (D : T' P) := (P.H ⧸ (ConjAct.toConjAct (D.eql.choose : G) • P.H).subgroupOf P.H)

lemma Q_T_one_eq_bot : (ConjAct.toConjAct ((T_one P).eql.choose : G) • P.H).subgroupOf P.H = ⊤:= by
  have h := T_one_choose_mem_H P
  -- Since (T_one P).eql.choose is in P.H, its conjugation should also be within P.H.
  rw [Subgroup.subgroupOf_eq_top ]
  intro x hx
  rw [← @SetLike.mem_coe]
  simp only [Subgroup.coe_pointwise_smul]
  rw [ConjAct_smul_coe_Eq, Subgroup.singleton_mul_subgroup (by exact h),
    Subgroup.subgroup_mul_singleton (by simp [h])]
  exact hx


lemma one_in_Q_T_one : Nonempty (Q P (T_one P)) := by
  use (1 : P.H)

lemma subsingleton_Q_T_one : Subsingleton (Q P (T_one P)) := by
  unfold Q
  rw [Q_T_one_eq_bot]
  apply QuotientGroup.subsingleton_quotient_top


lemma Set.exists_mul_eq_of_mem_mul {G : Type*} [Group G] {A B : Set G} {x : G} (hx : x ∈ A * B) :
  ∃ a b, a ∈ A ∧ b ∈ B ∧ x = a * b := by
  rw [mem_mul] at hx
  simp at *
  obtain ⟨a,ha,b, hb, hx⟩ := hx
  refine ⟨a,ha,b,hb,hx.symm⟩

lemma mem_mul_self (a : G) : a ∈ {a} * (H : Set G) := by
  rw [@mem_mul]
  simp [Subgroup.one_mem]

lemma GG (d : Δ) (h h' : H)
  (hyp : {(h : G)} * {(d : G)} * (H : Set G) = {(h' : G)} * {(d : G)} * (H : Set G)):
    (h')⁻¹ * h ∈ (ConjAct.toConjAct (d : G) • H).subgroupOf H  := by
/-   simp_rw [Set.singleton_mul_singleton] at hyp
  obtain ⟨g1, g2, hg1, hg2, hg12⟩ := Set.exists_mul_eq_of_mem_mul (mem_mul_self H (h * d))
  simp at hg1
  obtain ⟨h1, h1_mem, h2, h2_mem, h_eq⟩ := hg
  simp_rw [Set.singleton_mul_singleton, Set.mul_assoc, ← Subgroup.mul_assoc] at h_eq
  have : h'⁻¹ * h = (h'⁻¹ * g1) * d * (g2 * d⁻¹) := by
    simp_rw [h_eq, mul_assoc, ← Subgroup.mul_assoc, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
  rw [this]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ _ _) (Subgroup.mul_mem _ _ _)
  · exact Subgroup.inv_mem _ (Subgroup.coe_inv_mem h1_mem)
  · exact Subgroup.coe_inv_mem h2_mem
  · exact Subgroup.inv_mem _ (Subgroup.coe_inv_mem h2_mem)  -/
  sorry

lemma Q_coset_diff (D : T' P) (i j : Q P D) (hij : i ≠ j) :
  {((i.out' : G) * (D.eql.choose : G))} * (P.H : Set G) ≠
    {((j.out' : G) * (D.eql.choose : G))} * (P.H : Set G) := by
  intro h
  simp_rw [← Set.singleton_mul_singleton] at h
  have := GG P.H P.Δ D.eql.choose i.out' j.out' h
  rw [← @QuotientGroup.leftRel_apply, ← @Quotient.eq''] at this
  simp only [Quotient.out_eq'] at this
  exact hij (id (Eq.symm this))

lemma cosets_inf_eq (f g : G) (h : ¬ Disjoint (g • (H : Set G)) (f • H)) :
    {g} * (H : Set G) = {f} * H := by
  simp_rw  [← Set.singleton_smul]   at *
  rw [@not_disjoint_iff] at h
  obtain ⟨a, ha, ha2⟩ := h
  simp only [smul_eq_mul, singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe] at ha ha2
  refine Set.ext ?intro.intro.h
  intro Y
  simp only [smul_eq_mul, singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe]
  simp_rw  [← @QuotientGroup.eq] at *
  rw [← ha] at ha2
  rw [ha2]

lemma AUX (g : G) ( T S : Set G) (h : g ∈ S)  : {g} * T ⊆ S * T  := by
  refine mul_subset_mul_right <| singleton_subset_iff.mpr h

lemma left_coset_exist (D : T' P) : ∃ (i : Q P D),
  {(D.eql.choose : G)} * (P.H : Set G) = {(i.out' : G)} * {(D.eql.choose : G)} * P.H := by
  have hc := D.eql.choose_spec
  rw [doset_eq_iUnion_leftCosets] at hc
  have h1 : {(D.eql.choose : G)} * (P.H : Set G) ⊆ D.set := by
    have v0 := D.eql.choose_spec
    conv =>
      enter [2]
      rw [v0]
    intro i hi
    simp only [singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe] at *
    rw [mem_doset]
    use 1
    simp only [SetLike.mem_coe, one_mem, one_mul, true_and]
    use (D.eql.choose : G)⁻¹ * i
    simp [hi]
  have hr := hc.le
  have h3 := le_trans h1 hr
  simp only [le_eq_subset] at h3
  have h4 : (D.eql.choose : G) ∈ {(D.eql.choose : G)} * (P.H : Set G) := by
    simp only [singleton_mul, image_mul_left, mem_preimage, mul_left_inv, SetLike.mem_coe,
    Subgroup.one_mem]
  have h45 := h3 h4
  simp only [mem_iUnion] at h45
  obtain ⟨i, hi⟩ := h45
  use i
  rw [smul_eq_mul_singleton] at hi
  have h6 := AUX _ P.H _ hi
  conv at h6 =>
    enter [2]
    rw [mul_assoc, coe_mul_coe]
  rw [Set.singleton_mul_singleton]
  apply cosets_inf_eq
  apply Set.Nonempty.not_disjoint
  simp_rw [smul_eq_mul_singleton]
  rw [Set.inter_eq_self_of_subset_left h6]
  exact nonempty_of_mem h4

lemma left_coset_exist_unique (D : T' P) : ∃! (i : Q P D),
  {(D.eql.choose : G)} * (P.H : Set G) = {(i.out' : G) * (D.eql.choose : G)} * P.H := by
  have := left_coset_exist P D
  obtain ⟨i, hi⟩ := this
  use i
  rw [Set.singleton_mul_singleton] at hi
  simp only [hi,true_and]
  intro j h
  by_contra c
  have := (Q_coset_diff P D j i c).symm
  aesop


noncomputable def m' (D1 D2 d : T' P) : Z :=
 (Nat.card {⟨i, j⟩ : (Q P D1) × (Q P D2) |
  ({(i.out' : G) * (D1.eql.choose : G)} : Set G) * {(j.out' : G) * (D2.eql.choose : G)} * P.H =
   {(d.eql.choose : G)} * (P.H : Set G)})

lemma aa (a : H) (g : Δ) :  (a : G) * (g : G) ∈ Δ := by
  apply Submonoid.mul_mem _ (h₀ a.2) (g.2)

def map1 (D1 D2 : T' P) (i : Q P D1 × Q P D2) : T' P := T_mk P
    ⟨i.1.out' * D1.eql.choose * (i.2.out' * D2.eql.choose),
      Submonoid.mul_mem _ (aa P.H P.Δ P.h₀ i.1.out' D1.eql.choose)
        (aa P.H P.Δ P.h₀ i.2.out' D2.eql.choose)⟩

noncomputable def mmm (D1 D2 : T' P) : (Finset (T' P)) := Finset.image (map1 P D1 D2) ⊤

noncomputable def mm (D1 D2 d : T' P) : Finset (T' P) :=
    Finset.filter (fun x => x = d) (mmm P D1 D2)
--noncomputable def mm (D1 D2 : T' P) : Set (T' P) := {d : T' P | m' P Z D1 D2 d ≠ 0}


lemma rep_indep (D1 D2 d : T' P) : (mm P D1 D2 d).card = m' P Z D1 D2 d := by
  rw [m']
  congr
  rw [mm, mmm]
  simp
  rw [Fintype.card_eq_nat_card]
  rw [←  Nat.card_eq_finsetCard]
  refine Nat.card_eq_of_bijective ?_ ?_
  sorry



 /-  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, exists_prop, Finset.mem_top, Finset.mem_univ_val]
  split
  { intro ⟨⟨i, j⟩, h1, h2⟩
    use [i, j]
    exact h2 }
  { intro ⟨i, j, h⟩
    exact ⟨⟨i, j⟩, trivial, h⟩ } -/
  --this is true, but a pain to prove.
  sorry

lemma m'_T_one (D1 d : T' P) : D1 = d ↔ m' P Z D1 (T_one P) d = 1 := by
  constructor
  · intro h
    rw [← h]
    rw [m'] at *
    simp only [Nat.card_eq_fintype_card]
    have : (1 : Z) = (1 : ℕ) := by simp only [Nat.cast_one]
    rw [this]
    congr
    refine Fintype.card_eq_one_iff.mpr ?_
    obtain ⟨i, hi⟩ := left_coset_exist_unique P D1
    use  ⟨(⟨i , (1 : P.H)⟩ : (P.H ⧸ (ConjAct.toConjAct (D1.eql.choose : G) • P.H).subgroupOf P.H) ×
    (P.H ⧸ (ConjAct.toConjAct ((T_one P).eql.choose : G) • P.H).subgroupOf P.H)), by
      simp only [mem_setOf_eq]
      have := T_one_choose_eq P
      rw [mul_assoc]
      conv =>
        enter [1,2]
        rw [Subgroup.singleton_mul_subgroup
          (by apply Subgroup.mul_mem _ (by simp only [SetLike.coe_mem]) (T_one_choose_mem_H P))]
      exact hi.1.symm⟩
    intro y
    have hy := y.2
    simp only [mem_setOf_eq] at hy
    ext
    simp
    apply hi.2
    symm
    conv =>
      enter [2]
      rw [← hy]
    rw [mul_assoc]
    conv =>
      enter [2,2]
      rw [Subgroup.singleton_mul_subgroup
      (by apply Subgroup.mul_mem _ (by simp only [SetLike.coe_mem]) (T_one_choose_mem_H P))]
    simp
    have := subsingleton_Q_T_one P
    rw [@subsingleton_iff] at this
    apply this
  · intro h
    sorry

lemma m'_one_T (D1 d : T' P) : D1 = d ↔ (mm P (T_one P) D1 d).card = 1 := by
  constructor
  · intro h
    rw [mm, mmm]
    simp [map1]
    rw [@Finset.card_eq_one]
    use D1
    rw [@Finset.ext_iff]
    intro A
    simp [h]
    intro hh
    rw [ hh, ← h]
    refine ⟨(1 : P.H), (1 : P.H), ?_⟩
    rw [map1]
    have := D1.eql.choose_spec
    apply HeckeRing.ext P
    rw [T_mk]
    simp
    rw [mul_assoc]
    simp_rw [doset_mul_left_eq_self,
      doset_mul_left_eq_self P ⟨(T_one P).eql.choose, T_one_choose_mem_H P⟩,doset_mul_left_eq_self]
    nth_rw 2 [this]
  · intro h
    rw [@Finset.card_eq_one] at h
    obtain ⟨a, ha⟩ := h
    rw [mm] at ha
    rw [@Finset.eq_singleton_iff_unique_mem] at ha
    simp at ha





    sorry



noncomputable instance smulZeroClass : SMulZeroClass Z (α →₀ Z) where
  smul a v := v.mapRange (a • ·) (smul_zero _)
  smul_zero a := by
    ext
    apply smul_zero

/-
lemma auxx (D1 D2 a : T' P) (h : (mm P D1 D2 a).card ≠ 0) :
    a ∈ mm P D1 D2 ↔ m' P Z D1 D2 a ≠ 0 := by
  simp_rw [mm, m']
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists,
    coe_setOf,
    Nat.card_eq_fintype_card, ne_eq]
  rw [ show (0 : Z) = (0 : ℕ) by simp only [Nat.cast_zero]]
  conv =>
    enter [2]



  sorry
 -/

lemma eufa (a : ℕ) : ¬ a = 0 ↔ a ≠ 0 := by exact Eq.to_iff rfl

noncomputable def m (D1 D2 : T' P) : (T' P) →₀ ℤ :=
  ⟨mmm P D1 D2, fun d => (mm P D1 D2 d).card, by
   intro a
   simp_rw [mm, mmm]
   simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists, ne_eq,
     Nat.cast_eq_zero]
   rw [eufa, Finset.card_ne_zero, @Finset.filter_nonempty_iff ]
   simp ⟩

/-
lemma m'_comm (a b : Z) (D1 D2 : T' P) : m' P Z a b D1 D2 = m' P Z b a D1 D2 := by
  unfold m'
  ext A
  ring

lemma m'_left_distrib (a b c : Z) (D1 D2 D3 : T' P) : m' P Z a (b + c) D1 D2 D3 =
  m' P Z a b D1 D2 D3 + m' P Z a c D1 D2 D3 := by
  unfold m'
  simp only [mul_singleton, image_singleton, singleton_mul, image_mul_left, mul_inv_rev, coe_setOf,
    Nat.card_eq_fintype_card, mul_add]

lemma m'_right_distrib (a b c : Z) (D1 D2 D3 : T' P) : m' P Z (a + b) c D1 D2 D3 =
  m' P Z a c D1 D2 D3 + m' P Z b c D1 D2 D3 := by
  unfold m'
  simp only [mul_singleton, image_singleton, singleton_mul, image_mul_left, mul_inv_rev, coe_setOf,
    Nat.card_eq_fintype_card, mul_add, add_mul]

lemma m'_distrib_lem_1 (a b c : Z) (D1 D2 D3 : T' P) : m' P Z a (b + c) D1 D2 D3 = 0 ↔
    (m P Z a b D1 D2 = 0 ∧ m P Z a c D1 D2 = 0) ∨ a = 0 ∨ b + c = 0  := by


  sorry


lemma m_left_distrib (a b c : Z) (D1 D2 D3 : T' P) : m P Z a (b + c) D1 D2 =
    m P Z a b D1 D2 + m P Z a c D1 D2 := by
  unfold m
  split_ifs with h1 h2 h3
  simp
  simp
  rw [mm] at *
  rw [Nat.card_eq_zero] at h1 h2

  all_goals {sorry}











lemma m_comm (a b : Z) (D1 D2 : T' P) : m P Z a b D1 D2 = m P Z b a D1 D2 := by
  simp only [m, mm, ne_eq, coe_setOf, Finsupp.single_zero, m'_comm]


lemma m_zero_b (a : Z) (D1 D2 : T' P) : m P Z a 0 D1 D2 = 0 := by
  simp only [m, mm, ne_eq, coe_setOf, Nat.card_eq_zero, isEmpty_subtype, Decidable.not_not,
    Finsupp.single_zero, dite_eq_left_iff, not_or, not_forall, not_infinite_iff_finite]
  intros h
  apply Finsupp.ext
  intro a
  simp [m, m',mm]

lemma m_a_zero (b : Z) (D1 D2 : T' P) : m P Z 0 b D1 D2 = 0 := by
  rw [m_comm]
  apply m_zero_b
-/

/-- Take two doble cosets `HgH` and `HhH`, we define `HgH`*`HhH` by the sum over the double cosets
in `HgHhH`, i.e., if `HgHhH = ⋃ i, HiH` , then `HgH * HhH = ∑ i, m(g,h,i)*HiH` and then extends
linearly to get multiplication on the finite formal sums of double cosets. -/
noncomputable instance (P : ArithmeticGroupPair G) : Mul (𝕋 P ℤ) where
 mul f g := Finsupp.sum f (fun D1 b₁ => g.sum fun D2 b₂ => b₁ • b₂ • m P D1 D2)

lemma mul_def (f g : 𝕋 P ℤ) : f * g = Finsupp.sum f
  (fun D1 b₁ => g.sum fun D2 b₂ => b₁ • b₂ • m P D1 D2) := rfl

noncomputable abbrev T_single (a : T' P) (b : Z) : (𝕋 P Z) := Finsupp.single a b

noncomputable abbrev M_single (a : M P) (b : Z) : (𝕄 P Z) := Finsupp.single a b



lemma 𝕋_mul_singleton (D1 D2 : (T' P)) (a b : ℤ) :
  (T_single P ℤ D1 a) * (T_single P ℤ D2 b) = a • b • m P D1 D2 := by
  simp_rw [T_single, mul_def]
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index, m]
  simp only [zero_smul, smul_zero]
  apply Finsupp.ext
  intro a
  simp only [m, mm, zero_smul, Finsupp.sum_zero, Finsupp.coe_zero, Pi.zero_apply]




open Finsupp

lemma 𝕋_singleton_one_mul (D2 : (T' P)) (b : ℤ) :
  (T_single P ℤ D2 b) * T_single P ℤ (T_one P) (1 : ℤ)  = (T_single P ℤ D2 b) := by
  simp only [T_single, T_one, T_mk, OneMemClass.coe_one, 𝕋_mul_singleton, one_smul]
  rw [← Finsupp.smul_single_one]
  congr
  rw [m]
  apply Finsupp.ext
  intro A
  simp
  rw [rep_indep, Finsupp.single_apply]
  split_ifs with h1
  rw [← h1]
  have := m'_T_one P ℤ D2 D2
  simpa using this
  rw [← rep_indep, mm,mmm, show (0 : ℤ) = (0 : ℕ) by simp only [Nat.cast_zero]]
  congr
  by_contra h
  rw [eufa, Finset.card_ne_zero, @Finset.filter_nonempty_iff] at h
  simp [map1] at h
  obtain ⟨x,y, hxy⟩ := h
  have key : A = D2 := by
    rw [← hxy]
    have := D2.eql.choose_spec
    apply HeckeRing.ext P
    rw [T_mk]
    simp only
    conv =>
      enter [2]
      rw [this]
    rw [mul_assoc,doset_mul_left_eq_self]
    apply doset_mul_right_eq_self P ⟨y.out' * (T_one P).eql.choose, by
      apply Subgroup.mul_mem _ (by simp) (T_one_choose_mem_H P) ⟩
  exact h1 (id (Eq.symm key))


lemma 𝕋_one_mul_singleton (D2 : (T' P)) (b : ℤ) :
  T_single P ℤ (T_one P) (1 : ℤ) * (T_single P ℤ D2 b)   = (T_single P ℤ D2 b) := by
  simp only [T_single, T_one, T_mk, OneMemClass.coe_one, 𝕋_mul_singleton, one_smul]
  rw [← Finsupp.smul_single_one]
  congr
  rw [m]
  apply Finsupp.ext
  intro A
  simp
  rw [rep_indep, Finsupp.single_apply]
  split_ifs with h1
  rw [← h1]
  have := m'_one_T P D2 D2
  sorry
  sorry


noncomputable instance nonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (𝕋 P ℤ) :=
  {  (addCommMonoid P ℤ) with
    left_distrib := fun f g h => by
      simp only [mul_def]
      refine Eq.trans (congr_arg (Finsupp.sum f) (funext₂ fun a₁ b₁ => Finsupp.sum_add_index ?_ ?_))
        ?_ <;>
        simp
      intro D1 _ a b
      simp_rw [← smul_assoc, smul_eq_mul]
      ring_nf
      rw [@add_smul]

    right_distrib := fun f g h => by
      simp only [mul_def]
      refine Eq.trans (Finsupp.sum_add_index ?_ ?_) ?_ <;>
        simp only [Finset.mem_union, mem_support_iff, ne_eq, zero_smul, sum_zero, implies_true]
      intro D1 _ a b
      apply Finsupp.ext
      intro t
      simp_rw [add_smul]
      simp only [sum_add, coe_add, Pi.add_apply, sum_apply, coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [add_apply]
      simp only [sum_apply, coe_smul, Pi.smul_apply, smul_eq_mul]

    zero_mul := fun f => by
      simp only [mul_def]
      exact Finsupp.sum_zero_index
    mul_zero := fun f => by
      simp only [mul_def]
      exact Eq.trans (congr_arg (sum f) (funext₂ fun a₁ b₁ => sum_zero_index)) sum_zero }


noncomputable instance smul : SMul (𝕋 P ℤ) (𝕋 P ℤ) where
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

--CHATGPT did 98% of this proof
/- lemma support_eqd {α : Type*} (t s : α →₀ ℤ) (h : t.support = s.support) (h2 : ∀ a ∈ t.support, t a = s a) : t = s := by
  ext a
  by_cases ha : a ∈ t.support
  { -- Case where `a` is in `t.support`

    exact h2 a ha }
  { -- Case where `a` is not in `t.support`
    have ht : t a = 0 := Finsupp.not_mem_support_iff.1 ha
    have hs : s a = 0 := Finsupp.not_mem_support_iff.1 (h ▸ ha)
    rw [ht, hs] } -/

noncomputable instance 𝕄one : One (𝕄 P Z) := ⟨Finsupp.single (M_one P) (1 : Z)⟩

lemma 𝕄one_def : (1 : 𝕄 P Z) = Finsupp.single (M_one P) (1 : Z) := by rfl

/- lemma smul_one𝕄 (a : 𝕋 P Z) : a • (1 : 𝕄 P Z) =
  ((∑ (i : P.H ⧸ (ConjAct.toConjAct (a.eql.choose : G) • P.H).subgroupOf P.H),
      Finsupp.single (M_mk P ⟨((m.eql.choose : G) * (i.out' : G) * (t.eql.choose : G)),
      rep_mem2 P.H P.Δ P.h₀ i.out' m.eql.choose t.eql.choose⟩) (a * b : Z) : (M P) →₀ Z))
     := by

  sorry -/

example (a b : M P) (x y : ℤ) (h : single a x + single b y =0 ) : a = b ∧ x = -y := by
  rw [@add_eq_zero_iff_eq_neg] at h
  rw [← @single_neg] at h
  rw [@single_eq_single_iff] at h
  simp at h
  --aesop doenst help, it should, complain to Jeremy
  sorry

lemma sum_single_eq_zero  (s : Finset (M P)) (fs : (M P) → Z)
    (h : ∑ i in s, single (i : M P) (fs i) = 0) :  ∀ i ∈ s, fs i = 0 := by
  induction' s using Finset.induction_on with i s hi hs
  simp only [Finset.sum_empty, Finset.not_mem_empty, false_implies, implies_true] at *
  have hfin := h
  rw [Finset.sum_insert hi] at h hfin
  rw [@add_eq_zero_iff_eq_neg] at h hfin
  rw [← @Finset.sum_neg_distrib] at h
  conv at h =>
    enter [2,2]
    ext r
    rw [← @single_neg]
  rw [eq_comm] at h
  rw [eq_single_iff] at h
  simp at h
  cases' h.1 with hl hr
  . intro j hj
    simp at hj
    cases' hj with hj1 hj2
    · have h2 := h.2
      rw [hl] at h2
      simp at h2
      aesop
    · apply hs hl
      exact hj2
  · simp at hr
    intro j hj
    simp at hj
    cases' hj with hj1 hj2
    · have h2 := h.2
      rw [← hj1] at h2 hr
      have hgg := Finsupp.support_finset_sum (s := s) (f := fun m => single m (fs m))
      rw [hr] at hgg
      simp only [Finset.singleton_subset_iff, Finset.mem_biUnion, mem_support_iff, ne_eq] at hgg
      obtain ⟨x, hx, hxx⟩ := hgg
      rw [@single_apply_eq_zero] at hxx
      simp at hxx
      rw [hj1] at hxx
      rw [← hxx.1] at hx
      exfalso
      exact hi hx
    · /- have hgg := Finsupp.support_finset_sum (s := s) (f := fun m => single m (fs m))
      rw [hr] at hgg
      simp only [Finset.singleton_subset_iff, Finset.mem_biUnion, mem_support_iff, ne_eq] at hgg
      obtain ⟨x, hx, hxx⟩ := hgg  -/
      sorry





















 /-  rw [Finset.sum_insert hi, Finsupp.add_eq_zero_iff (single i (fs i))] at h
  simp only [single_eq_zero] at h
  intro j hj
  simp at hj
  aesop  -/

lemma sum_finset_single_indep (s t : Finset (M P)) (fs ts : (M P) → ℤ)
  (h : ∑ (i ∈ s), single (i : M P) (fs i) = ∑ (i ∈ t), single (i : M P) (ts i)) :
    ∃ (a : s × t), single (a.1 : M P) (fs a.1) = single (a.2 : M P) (ts a.2) := by
  simp at *
  have : ∑ i in s, single i (fs i) - ∑ i in t, single i (ts i) = 0 := by
    rw [h, sub_self]
  --rw [Finset.sum_disjiUnion]
  have h_support : (∑ i in s, single i (fs i) - ∑ i in t, single i (ts i)).support = ∅ := by
    rw [this, support_zero]







 /-  rw [← @Finset.nonempty_iff_ne_empty]
  rw [@support_nonempty_iff]

  rw [@ne_iff]


  use (∑ i in s, single i (fs i) - ∑ i in t, single i (ts i)).support,
  rw [finsupp.support_sum_eq] at h_support,
  simp only [finset.not_subset] at h_support,
  obtain ⟨a, ha⟩ := h_support,
  rw [finsupp.support_sum_eq] at ha,
  simp only [finsupp.support_single_ne_zero, finset.mem_bUnion, finset.mem_union, finset.mem_empty, finset.not_mem_empty] at ha,
  obtain ⟨i, hi⟩ := ha,
  exact ⟨i, finset.mem_inter.mpr ⟨hi.1, hi.2⟩, rfl⟩, -/
  sorry

lemma sdf {α : Type*} (s : Finsupp α Z) (a : α) : s.toFun a = s a := by
  exact rfl

lemma 𝕋eq_of_smul_single_eq_smul (T1 T2 : (T' P)) (c₁ c₂ : Z)
  (h : ∀ (a : 𝕄 P Z), (T_single P Z T1 c₁) • a = (T_single P Z T2 c₂) • a) :
    (T_single P Z T1 c₁) = (T_single P Z T2 c₂) := by
  have h1 := h 1

  simp_rw [𝕋smul_def, 𝕄one_def] at h1
  --apply Finsupp.sum_congr
  simp at h1
  simp_rw [T_single]
  rw [Finsupp.single_eq_single_iff]
  have := congrFun (congrArg toFun h1) (M_mk P ((1 : P.Δ)))

  have  fv:= finset_sum_apply ⊤ (fun (i : Q P T1) => single
  (M_mk P ⟨(((M_one P).eql.choose : G) * (i.out' : G) * (T1.eql.choose : G)),
      rep_mem2 P.H P.Δ P.h₀ i.out' (M_one P).eql.choose T1.eql.choose⟩) (c₁ : Z))
        (M_mk P ((1 : P.Δ)))
  have  fv2:= finset_sum_apply ⊤ (fun (i : Q P T2) => single
  (M_mk P ⟨(((M_one P).eql.choose : G) * (i.out' : G) * (T2.eql.choose : G)),
      rep_mem2 P.H P.Δ P.h₀ i.out' (M_one P).eql.choose T2.eql.choose⟩) (c₂ : Z))
        (M_mk P ((1 : P.Δ)))
  simp at fv fv2
  unfold Q at fv
  rw [sdf, fv, sdf, fv2] at this
  conv at this =>
    enter [1,2]
    ext u
    rw [single_apply]







  --rw [Finset.sum_apply'] at h1





lemma 𝕋eq_of_smul_eq_smul (T1 T2 : (𝕋 P Z)) (h : ∀ (a : 𝕄 P Z), T1 • a = T2 • a) : T1 = T2 := by
  have h1 := h 1
  simp_rw [𝕋smul_def, 𝕄one_def] at h1
  simp at h1
  rw [← sub_eq_zero]
  apply induction_linear (p:= fun x => x = 0)
  --apply support_eq





  --have := congrFun (congrArg toFun h1)
  --rw [Finsupp.sum_fintype] at h1



 /-  rw [single_basis Z (T1 • (1 : 𝕄 P Z)), single_basis Z (T2 • (1 : 𝕄 P Z))] at h1
  have h2 : (T1 • (1 : 𝕄 P Z)).support = (T2 • (1 : 𝕄 P Z)).support := by rw [h 1]
  rw [h2] at h1 -/






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

noncomputable instance 𝕄smulFaithful : FaithfulSMul (𝕋 P ℤ) (𝕄 P ℤ) where
  eq_of_smul_eq_smul  {t1 t2} h := 𝕋eq_of_smul_eq_smul P ℤ t1 t2 h

lemma smul_def (f g : 𝕋 P ℤ) : f • g = f * g := rfl

noncomputable instance isScalarTower : IsScalarTower (𝕋 P ℤ) (𝕋 P ℤ) (𝕄 P ℤ) := by sorry

lemma 𝕋_mul_assoc (f g h : 𝕋 P ℤ) : (f * g) * h = f * (g * h) := by

  have := (𝕄smulFaithful P).eq_of_smul_eq_smul (M := (𝕋 P ℤ)) (m₁ := (f * g) * h)
      (m₂ := f * (g * h) )
  apply this
  intro a
  have e1 :=  (isScalarTower P ).smul_assoc f (g* h) a
  have e2 :=  (isScalarTower P ).smul_assoc g h a
  have e3 :=  (isScalarTower P ).smul_assoc (f  * g) h a
  have e4 :=  (isScalarTower P ).smul_assoc f g (h • a)
  simp at *
  rw [e2] at e1
  rw [e4] at e3
  rw [e1, e3]

noncomputable instance nonUnitalSemiring : NonUnitalSemiring (𝕋 P ℤ) :=
  {nonUnitalNonAssocSemiring P   with
    mul_assoc := 𝕋_mul_assoc P } -- known in the 1980s so Kevin can't complain.


/- The identity is `H1H`. -/
noncomputable instance one : One (𝕋 P Z) := ⟨T_single P Z (T_one P) (1 : Z)⟩

theorem one_def : (1 : (𝕋 P Z)) = T_single P Z (T_one P) (1 : Z):=
  rfl

noncomputable instance nonAssocSemiring : NonAssocSemiring (𝕋 P ℤ) :=
  { nonUnitalNonAssocSemiring P  with
    natCast := fun n => T_single P ℤ (T_one P) (n : ℤ)
    natCast_zero := by simp only [Nat.cast_zero, single_zero]
    natCast_succ := fun _ => by simp only [Nat.cast_add, Nat.cast_one, single_add, add_right_inj]; rfl
    one_mul :=  fun f => by
      simp only [one_def, mul_def, zero_smul, smul_zero, sum_single_index, one_smul]

      rw [T_single]
      simp
      have := Finsupp.sum_single  f
      nth_rw 2 [← this]
      congr
      ext D z v
      have :=  𝕋_one_mul_singleton P D z
      simp_rw [T_single] at *
      rw [← this]
      rw [𝕋_mul_singleton]
      simp only [smul_eq_mul, one_smul, mul_eq_mul_left_iff]
    mul_one :=fun f => by
      simp only [one_def, mul_def, zero_smul, smul_zero, sum_single_index, one_smul]
      have := Finsupp.sum_single  f
      nth_rw 2 [← this]
      congr
      ext D z v
      have :=  𝕋_singleton_one_mul P  D z
      simp_rw [T_single] at this
      rw [← this]
      rw [𝕋_mul_singleton]
      simp only [smul_eq_mul, one_smul, mul_eq_mul_left_iff] }

noncomputable instance semiring : Semiring (𝕋 P ℤ) :=
  {HeckeRing.nonUnitalSemiring P ,
    (HeckeRing.nonAssocSemiring P ) with}

noncomputable instance addCommGroup : AddCommGroup (𝕋 P Z) :=
  Finsupp.instAddCommGroup

noncomputable instance nonAssocRing : NonAssocRing (𝕋 P ℤ) :=
  { HeckeRing.addCommGroup P ℤ,
    (HeckeRing.nonAssocSemiring P ) with
    intCast := sorry
    intCast_ofNat := sorry
    intCast_negSucc := sorry }

noncomputable instance ring : Ring (𝕋 P ℤ) :=
    {HeckeRing.nonAssocRing P , HeckeRing.semiring P with }




end HeckeRing
