module

public import RKCert.ReviewedNative.WeakFiveSoleInnerFourCutBracket
public import RKCert.ReviewedNative.WeakFiveSoleInnerFiniteRank

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Signed degree-eight law and the exact reflected two-node erasure

The three signed masses come from the reviewed positive finite rule on
the actual seven sites. A true local affine factor erases exactly its
own unit label, leaving the two other original marks and their signs. -/
namespace RKCert.ReviewedNative.WeakFiveSoleInnerChronology

open Polynomial
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.RightPoleInterpolation
open RKCert.ReviewedNative.FiniteStoppedBracket
open RKCert.ReviewedNative.FiniteGaussianGridPositivity
open RKCert.ReviewedNative.CrossedGaussianSignedAdapter
open RKCert.ReviewedNative.WeakFiveSoleInner
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
set_option maxHeartbeats 1200000

def SignedThreeLaw (a : K) (q : K[X]) (t s k : K) (η : K → K) : Prop :=
  ∀ F : K[X], F.natDegree≤8 →
    integral 0 1 (unitWeight K*(X-C a)*q*F) = η t*F.eval t+η s*F.eval s+η k*F.eval k

/-- Multiplying the existing positive degree-12 test by the actual
cubic and exterior factor leaves the signed degree-8 law. The signs
are not assumed; each mass is a positive multiple of the same q-value. -/
theorem signed_law_of_ports {a e u h z r₀ r₁ r₂ : K}
    (B : OrientedPorts a e u h z r₀ r₁ r₂) :
    ∃ η : K → K, SignedThreeLaw a (profile e r₀ r₁ r₂) z h u η ∧
      ∀ x ∈ ({z,h,u} : Finset K), ∃ c : K, 0 < c ∧ η x=c*(profile e r₀ r₁ r₂).eval x := by
  obtain ⟨μ,paid,pos⟩ := B.radau
  let R := cubic r₀ r₁ r₂
  let η (x : K) := μ x*(x-a)*R.eval x
  let marks : Finset K := {z,h,u}
  have marksSub : marks ⊆ radauSites a u h z r₀ r₁ r₂ := by
    intro x hx
    change x∈insert a (marks ∪ ({r₀,r₁,r₂} : Finset K))
    exact Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inl hx))
  have η_zero (x : K) (hx : x∈radauSites a u h z r₀ r₁ r₂) (skip : x∉marks) : η x=0 := by
    have m : x=a ∨ x∈marks ∨ x=r₀ ∨ x=r₁ ∨ x=r₂ := by
      simpa only [radauSites,inside,marks,Finset.mem_insert,Finset.mem_union,
        Finset.mem_singleton,or_assoc] using hx
    rcases m with rfl | m | rfl | rfl | rfl
    · simp [η]
    · exact (skip m).elim
    · simp [η,R,cubic]
    · simp [η,R,cubic]
    · simp [η,R,cubic]
  refine ⟨η,?_,?_⟩
  · intro F fd
    let G := (X-C a)*R*F
    have gd : G.natDegree≤12 := by
      have rd : R.natDegree≤3 := le_of_eq (WeakFiveSoleInner.cubic_degree _ _ _)
      exact natDegree_mul_le_of_le
        (natDegree_mul_le_of_le (natDegree_X_sub_C a).le rd) fd
    have hU : h∉({u} : Finset K) := by simp [B.hu]
    have zHU : z∉({h,u} : Finset K) := by simp [B.hz.symm,B.zu.ne]
    calc
      _ = baseMoment e G := by
        simp only [baseMoment,unitMoment_apply,G,R,profile]
        congr 1
        ring
      _ = ∑ x ∈ radauSites a u h z r₀ r₁ r₂, η x*F.eval x := by
        rw [paid G gd]
        simp only [id_eq,G,η,eval_mul,eval_sub,eval_X,eval_C,mul_assoc]
      _ = ∑ x ∈ marks, η x*F.eval x := by
        symm
        apply Finset.sum_subset marksSub
        intro x hx skip
        rw [η_zero x hx skip,zero_mul]
      _ = _ := by
        change (∑ x ∈ ({z,h,u} : Finset K), η x*F.eval x) = _
        rw [Finset.sum_insert zHU,Finset.sum_insert hU,Finset.sum_singleton]
        ring
  · intro x hx
    have x0 : 0 < x := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact B.zUnit.1
      · exact B.hUnit.1
      · exact B.uUnit.1
    have ae := sub_pos.mpr (B.ae.trans (B.eNeg.trans x0))
    have ee := sub_pos.mpr (B.eNeg.trans x0)
    have mass := pos x (marksSub hx)
    refine ⟨μ x*(x-a)/(x-e),div_pos (mul_pos mass ae) ee,?_⟩
    simp only [η,profile,eval_mul,eval_sub,eval_X,eval_C,R]
    field_simp [ee.ne'] <;> ring

def mirrorErased (q : K[X]) (k : K) : K[X] := ((X-C k)*q).comp (1-X)

private theorem reflect_twice (P : K[X]) : (P.comp (1-X)).comp (1-X)=P := by
  rw [comp_assoc,show ((1-X : K[X]).comp (1-X))=X by
    simp only [sub_comp,one_comp,X_comp,sub_sub_cancel],comp_X]

private theorem mirrored_degree (P : K[X]) : (P.comp (1-X)).natDegree≤P.natDegree := by
  have d : (1-X : K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
  exact natDegree_comp_le.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left P.natDegree d)

private theorem reflect_weight (a : K) :
    (unitWeight K*(X-C a)).comp (1-X)=X*poleProduct [(1 : K),1-a] := by
  simp only [unitWeight,poleProduct,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    mul_comp,sub_comp,one_comp,X_comp,C_comp,map_sub,map_one,mul_one]
  ring

/-- The real tilt pays degree seven because one degree of the original
law is spent on the erased mark. The right suffix is reflected with
the two right poles 1 and 1-a. -/
theorem reflected_erasure {a t s k : K} {q : K[X]} {η : K → K}
    (law : SignedThreeLaw a q t s k η) :
    ∀ F : K[X], F.natDegree≤7 →
      integral 0 1 (X*poleProduct [(1 : K),1-a]*mirrorErased q k*F) =
        (η s*(s-k))*F.eval (1-s)+(η t*(t-k))*F.eval (1-t) := by
  intro F fd
  let G : K[X] := (X-C k)*(F.comp (1-X))
  have gd : G.natDegree≤8 :=
    natDegree_mul_le_of_le (natDegree_X_sub_C k).le ((mirrored_degree F).trans fd)
  have shape : (unitWeight K*(X-C a)*q*G).comp (1-X) =
      X*poleProduct [(1 : K),1-a]*mirrorErased q k*F := by
    calc
      _ = ((unitWeight K*(X-C a)).comp (1-X))*mirrorErased q k*F := by
        simp only [G,mirrorErased,mul_comp,reflect_twice]
        ring
      _ = _ := by rw [reflect_weight]
  have w := integral_reflect (unitWeight K*(X-C a)*q*G) (0 : K)
  rw [sub_zero,shape,law G gd] at w
  rw [w]
  simp only [G,eval_mul,eval_sub,eval_X,eval_C,eval_comp,eval_one,
    sub_self,zero_mul,mul_zero,add_zero]
  ring

theorem reflected_erasure_zero {t k : K} {q : K[X]}
    (paid : integral t 1 ((1-X)*(X-C k)*q)=0) :
    integral 0 (1-t) (X*mirrorErased q k)=0 := by
  have e : (((1-X)*(X-C k)*q).comp (1-X))=X*mirrorErased q k := by
    simp only [mirrorErased,mul_comp,sub_comp,one_comp,X_comp,sub_sub_cancel]
    ring
  rw [←e,integral_reflect,paid]

theorem right_pair_pays_erasure {t k : K} {q : K[X]}
    (m1 : integral t 1 ((1-X)*q)=0) (m2 : integral t 1 ((1-X)^2*q)=0) :
    integral t 1 ((1-X)*(X-C k)*q)=0 := by
  have e : (1-X)*(X-C k)*q=C (1-k)*((1-X)*q)-(1-X)^2*q := by
    simp only [map_sub,map_one]
    ring
  rw [e,map_sub,←Polynomial.smul_eq_C_mul,map_smul,m1,m2,smul_zero,sub_zero]

private theorem mirror_unit {x : K} (hx : x∈Set.Ioo (0 : K) 1) :
    1-x∈Set.Ioo (0 : K) 1 := ⟨sub_pos.mpr hx.2,by linarith only [hx.1]⟩

private theorem mirror_actual_four_factors (e r₀ r₁ r₂ k : K) :
    mirrorErased (profile e r₀ r₁ r₂) k =
      (C (1-e)-X)*cutProduct [1-r₀,1-r₁,1-r₂,1-k] := by
  simp only [mirrorErased,profile,cubic,cutProduct_cons,cutProduct_nil,mul_comp,sub_comp,X_comp,
    C_comp,map_sub,map_one,mul_one]
  ring

/-- Actual right receipt after one true erasure: the surviving mark
lies strictly above the stop and the two tilted q-values have opposite signs. -/
theorem actual_right_erasure {a e t s k r₀ r₁ r₂ : K} {η : K → K}
    (a0 : a < 0) (e0 : e < 0) (ht : t∈Set.Ioo (0 : K) 1) (hs : s∈Set.Ioo (0 : K) 1)
    (st : s≠t) (kt : k≠t) (qt : (profile e r₀ r₁ r₂).eval t≠0)
    (law : SignedThreeLaw a (profile e r₀ r₁ r₂) t s k η)
    (mt : ∃ c : K, 0 < c ∧ η t=c*(profile e r₀ r₁ r₂).eval t)
    (ms : ∃ c : K, 0 < c ∧ η s=c*(profile e r₀ r₁ r₂).eval s)
    (zero : integral t 1 ((1-X)*(X-C k)*profile e r₀ r₁ r₂)=0) :
    t < s ∧
      ((profile e r₀ r₁ r₂).eval t*(t-k))*((profile e r₀ r₁ r₂).eval s*(s-k)) < 0 := by
  let R : List K := [1-r₀,1-r₁,1-r₂,1-k]
  have n₀ : r₀≠t := fun z => qt (by simp [←z,profile,cubic])
  have n₁ : r₁≠t := fun z => qt (by simp [←z,profile,cubic])
  have n₂ : r₂≠t := fun z => qt (by simp [←z,profile,cubic])
  have fit (x : K) (hx : x∈R) : x≠1-t := by
    simp [R] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact fun q => n₀ (by linarith only [q])
    · exact fun q => n₁ (by linarith only [q])
    · exact fun q => n₂ (by linarith only [q])
    · exact fun q => kt (by linarith only [q])
  obtain ⟨order,sign⟩ := two_node_paid_left (t := 1-t) (s := 1-s)
    (mt := η t*(t-k)) (ms := η s*(s-k)) a0 (show 1 < 1-e by linarith only [e0])
    R (by rfl) (mirror_actual_four_factors e r₀ r₁ r₂ k) fit
    (mirror_unit ht) (mirror_unit hs) (fun q => st (by linarith only [q]))
    (reflected_erasure law) (reflected_erasure_zero zero)
  obtain ⟨M,pM,hm⟩ := mt
  obtain ⟨N,pN,hn⟩ := ms
  rw [hm,hn] at sign
  have e' : ((N*(profile e r₀ r₁ r₂).eval s)*(s-k))*
      ((M*(profile e r₀ r₁ r₂).eval t)*(t-k)) =
      (M*N)*(((profile e r₀ r₁ r₂).eval t*(t-k))*
        ((profile e r₀ r₁ r₂).eval s*(s-k))) := by ring
  rw [e'] at sign
  exact ⟨by linarith only [order],neg_of_mul_neg_right sign (mul_pos pM pN).le⟩

end
end RKCert.ReviewedNative.WeakFiveSoleInnerChronology
