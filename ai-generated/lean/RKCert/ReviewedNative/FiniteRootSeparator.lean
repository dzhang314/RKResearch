module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.Finset.Max
public import Mathlib.Topology.Algebra.Polynomial

import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Finite separator roots on gaps between two selected families

Draft. The intermediate-value assumption concerns one polynomial on
ordered images of base samples. No density of the base field, and no
transfer of a sign-variation census, belongs to the separator lemma.
-/
namespace RKCert.ReviewedNative.FiniteRootSeparator

open Polynomial Set
open scoped Topology

noncomputable section

/-- A finite candidate set lets one select a single common strict cut
from pairwise feasibility, even for two infinite index families. -/
theorem finite_strict_separator {α β γ : Type*} [LinearOrder γ]
    (roots : Finset γ) (A : Set α) (B : Set β) (f : α → γ) (g : β → γ)
    (Ane : A.Nonempty) (Bne : B.Nonempty)
    (gap : ∀ a ∈ A, ∀ b ∈ B, ∃ x ∈ roots, f a < x ∧ x < g b) :
    ∃ x ∈ roots, (∀ a ∈ A, f a < x) ∧ (∀ b ∈ B, x < g b) := by
  classical
  let C := roots.filter (fun x => ∀ b ∈ B, x < g b)
  have one (a : α) (ha : a ∈ A) : ∃ x ∈ C, f a < x := by
    let S := roots.filter (fun x => f a < x)
    have S0 : S.Nonempty := by
      obtain ⟨b,hb⟩ := Bne
      obtain ⟨x,hx,hax,_⟩ := gap a ha b hb
      exact ⟨x,Finset.mem_filter.mpr ⟨hx,hax⟩⟩
    let x := S.min' S0
    have hxS : x ∈ S := Finset.min'_mem S S0
    have hx : x ∈ roots ∧ f a < x := Finset.mem_filter.mp hxS
    have below (b : β) (hb : b ∈ B) : x < g b := by
      obtain ⟨y,hy,hay,hyb⟩ := gap a ha b hb
      have hyS : y ∈ S := Finset.mem_filter.mpr ⟨hy,hay⟩
      exact (Finset.min'_le S y hyS).trans_lt hyb
    exact ⟨x,Finset.mem_filter.mpr ⟨hx.1,below⟩,hx.2⟩
  have C0 : C.Nonempty := by
    obtain ⟨a,ha⟩ := Ane
    obtain ⟨x,hx,_⟩ := one a ha
    exact ⟨x,hx⟩
  let x := C.max' C0
  have hxC : x ∈ C := Finset.max'_mem C C0
  have hx : x ∈ roots ∧ ∀ b ∈ B, x < g b := Finset.mem_filter.mp hxC
  refine ⟨x,hx.1,?_,hx.2⟩
  intro a ha
  obtain ⟨y,hy,hay⟩ := one a ha
  exact hay.trans_le (Finset.le_max' C y hy)

section Fields

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L]

def Opposite (x y : K) : Prop := (0<x ∧ y<0) ∨ (x<0 ∧ 0<y)

theorem eval_on_base (e : K →+* L) (P : K[X]) (x : K) :
    (P.map e).eval (e x) = e (P.eval x) := by rw [eval_map,eval₂_at_apply]

/-- The minimal root-source premise. Only opposite-signed *base* pairs
inside the unit interval are asked to supply an ordered extension root. -/
def UnitRootSource (e : K →+* L) (P : K[X]) : Prop :=
  ∀ {a b : K}, a ∈ Ioo (0:K) 1 → b ∈ Ioo (0:K) 1 → a<b →
    Opposite (P.eval a) (P.eval b) →
    ∃ r : L, e a<r ∧ r<e b ∧ (P.map e).IsRoot r

theorem eval_pos_somewhere_right (P : K[X]) {x b : K} (xb : x<b) (pos : 0<P.eval x) :
    ∃ y : K, x<y ∧ y<b ∧ 0<P.eval y := by
  letI : TopologicalSpace K := Preorder.topology K
  letI : OrderTopology K := ⟨rfl⟩
  have ho : IsOpen ((fun t : K => P.eval t) ⁻¹' Ioi (0:K)) := isOpen_Ioi.preimage P.continuous
  have hx : x ∈ (fun t : K => P.eval t) ⁻¹' Ioi (0:K) := pos
  obtain ⟨z,hz,inside⟩ := exists_Ico_subset_of_mem_nhds' (ho.mem_nhds hx) xb
  obtain ⟨y,xy,yz⟩ := exists_between hz.1
  exact ⟨y,xy,yz.trans_le hz.2,inside ⟨xy.le,yz⟩⟩

theorem eval_pos_somewhere_left (P : K[X]) {a x : K} (ax : a<x) (pos : 0<P.eval x) :
    ∃ y : K, a<y ∧ y<x ∧ 0<P.eval y := by
  letI : TopologicalSpace K := Preorder.topology K
  letI : OrderTopology K := ⟨rfl⟩
  have ho : IsOpen ((fun t : K => P.eval t) ⁻¹' Ioi (0:K)) := isOpen_Ioi.preimage P.continuous
  have hx : x ∈ (fun t : K => P.eval t) ⁻¹' Ioi (0:K) := pos
  obtain ⟨z,hz,inside⟩ := exists_Ioc_subset_of_mem_nhds' (ho.mem_nhds hx) ax
  obtain ⟨y,zy,yx⟩ := exists_between hz.2
  exact ⟨y,hz.1.trans_lt zy,yx,inside ⟨zy,yx.le⟩⟩

theorem eval_neg_somewhere_right (P : K[X]) {x b : K} (xb : x<b) (neg : P.eval x<0) :
    ∃ y : K, x<y ∧ y<b ∧ P.eval y<0 := by
  obtain ⟨y,xy,yb,hy⟩ := eval_pos_somewhere_right (-P) xb (by
    simpa only [eval_neg,neg_pos] using neg)
  exact ⟨y,xy,yb,by simpa only [eval_neg,neg_pos] using hy⟩

theorem eval_neg_somewhere_left (P : K[X]) {a x : K} (ax : a<x) (neg : P.eval x<0) :
    ∃ y : K, a<y ∧ y<x ∧ P.eval y<0 := by
  obtain ⟨y,ay,yx,hy⟩ := eval_pos_somewhere_left (-P) ax (by
    simpa only [eval_neg,neg_pos] using neg)
  exact ⟨y,ay,yx,by simpa only [eval_neg,neg_pos] using hy⟩

/-- If a chosen extension root belongs to the base, remove that factor
over the base before reasoning about its nearby sign. -/
theorem map_base_quotient (e : K →+* L) (P : K[X]) (x : K) (B : L[X])
    (factor : P.map e = (X-C (e x))*B) :
    (P /ₘ (X-C x)).map e = B := by
  rw [map_divByMonic e (monic_X_sub_C x),Polynomial.map_sub,map_X,map_C,
    factor,mul_divByMonic_cancel_left _ (monic_X_sub_C (e x))]

theorem isRoot_of_mapped_factor (e : K →+* L) (P : K[X]) (x : K) {B : L[X]}
    (factor : P.map e = (X-C (e x))*B) : P.IsRoot x := by
  have he := congrArg (Polynomial.eval (e x)) factor
  have hz : e (P.eval x) = 0 := by
    simpa only [eval_on_base,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul] using he
  change P.eval x = 0
  exact e.injective (by simpa only [map_zero] using hz)

/-- Two distinct actual roots of a monic quartic leave a monic quadratic. -/
theorem monic_quadratic_of_two_roots (P : L[X]) (monic : P.Monic) (degree : P.natDegree=4)
    {r s : L} (rs : r<s) (hr : P.IsRoot r) (hs : P.IsRoot s) :
    ∃ B : L[X], B.Monic ∧ B.natDegree=2 ∧ P = B*((X-C r)*(X-C s)) := by
  have cop : IsCoprime (X-C r : L[X]) (X-C s) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr rs.ne).isUnit
  obtain ⟨B,hB⟩ := cop.mul_dvd (dvd_iff_isRoot.mpr hr) (dvd_iff_isRoot.mpr hs)
  have dn : ((X-C r)*(X-C s) : L[X]) ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  have bn : B ≠ 0 := fun h => monic.ne_zero (by rw [hB,h,mul_zero])
  have dm : ((X-C r)*(X-C s) : L[X]).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have bm : B.Monic := by
    change B.leadingCoeff = 1
    have h := monic.leadingCoeff
    rw [hB,leadingCoeff_mul,dm.leadingCoeff,one_mul] at h
    exact h
  have d := degree
  rw [hB,natDegree_mul dn bn,natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    natDegree_X_sub_C,natDegree_X_sub_C] at d
  exact ⟨B,bm,by omega,hB.trans (mul_comm _ _)⟩

end Fields
end
end RKCert.ReviewedNative.FiniteRootSeparator
