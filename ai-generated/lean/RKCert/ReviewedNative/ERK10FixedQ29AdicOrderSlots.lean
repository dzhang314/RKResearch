module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicWordAll
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical

open Nonlinear Polynomial
open scoped BigOperators Ring
noncomputable section
set_option maxHeartbeats 400000

variable {R : Type*} [CommRing R]

/-- The four retained columns enter unchanged. The eleven raw slots are
indexed by their original reverse labels after this insertion. -/
def oldSlot (j : Old) : Fin 15 := Fin.castAdd 11 j
def rawSlot (i : Site) : Fin 15 := Fin.natAdd 4 i.rev

theorem split_oldSlot (j : Old) : splitStage (oldSlot j)=.inl j := by
  have h : oldSlot j=Fin.castLE (by decide : 4≤15) j := Fin.ext rfl
  rw [h,splitStage_old]

theorem split_rawSlot (i : Site) : splitStage (rawSlot i)=.inr i.rev := by
  have h : ¬ (rawSlot i).val<4 := by
    change ¬ 4+i.rev.val<4
    omega
  unfold splitStage
  rw [dif_neg h]
  apply congrArg Sum.inr
  apply Fin.ext
  change 4+i.rev.val-4=i.rev.val
  omega

theorem sum_slots {T : Type*} [AddCommMonoid T] (v : Fin 15→T) :
    (∑ i : Fin 15,v i)=(∑ j : Old,v (oldSlot j))+(∑ j : Site,v (rawSlot j)) := by
  rw [Fin.sum_univ_add (a:=4) (b:=11)]
  change (∑ j : Old,v (oldSlot j))+(∑ j : Site,v (Fin.natAdd 4 j))=_
  congr 1
  exact (Equiv.sum_comp Fin.revPerm (fun j : Site => v (Fin.natAdd 4 j))).symm

def rawClock (c a b : R) (i : Site) : R := 1-rawY c a b i

def oldBasis (j : Old) (k : Old) : R := if k=j then 1 else 0

def rawTransact (K : Site→Site→R) (v : Site→R) (i : Site) : R :=
  ∑ j : Site,K j i*v j

theorem forward_at_rawSlot (c a b : R) (i : Site) :
    forwardClock c a b i.rev=rawClock c a b i := by
  simp only [forwardClock,rawClock,Fin.rev_rev]

theorem tableauWeights_rawSlot (c a b : R) (i : Site) :
    tableauWeights c a b (rawSlot i)=rawW c a b i := by
  rw [tableauWeights,split_rawSlot]
  simp only [forwardWeight,Fin.rev_rev]

theorem tableauWeights_oldSlot (c a b : R) (i : Old) :
    tableauWeights c a b (oldSlot i)=
      if i=0 then score (nodal c a b) oldOrigin else 0 := by
  rw [tableauWeights,split_oldSlot]

theorem matrix_raw_raw (c a b : R) (K : Site→Site→R) (i j : Site) :
    tableau15 c a b K (rawSlot i) (rawSlot j)=K j i := by
  rw [tableau15,split_rawSlot,split_rawSlot]
  change K j.rev.rev i.rev.rev=_
  rw [Fin.rev_rev,Fin.rev_rev]

theorem matrix_old_raw (c a b : R) (K : Site→Site→R) (i : Old) (j : Site) :
    tableau15 c a b K (oldSlot i) (rawSlot j)=0 := by
  rw [tableau15,split_oldSlot,split_rawSlot]
  rfl

theorem matrix_old_old (c a b : R) (K : Site→Site→R) (i j : Old) :
    tableau15 c a b K (oldSlot i) (oldSlot j) =
      (actualHost c a b).retainedOpening ((8:R)⁻¹ʳ) i j := by
  rw [tableau15,split_oldSlot,split_oldSlot]
  rfl

theorem retained_eval_sum (p : HostInput R) (g : Old→R) (y : R) :
    ∑ j : Old,(p.retainedPoly (oldBasis j)).eval y*g j =
      (p.retainedPoly g).eval y := by
  simp only [Fin.sum_univ_four]
  simp [HostInput.retainedPoly,HostInput.decode,oldBasis,Quad.eval]
  ring

theorem retained_primitive_sum (p : HostInput R) (g : Old→R) (y : R) :
    ∑ j : Old,(p.retainedPoly (oldBasis j)).primitive y*g j =
      (p.retainedPoly g).primitive y := by
  simp only [Fin.sum_univ_four]
  simp [HostInput.retainedPoly,HostInput.decode,oldBasis,Quad.primitive]
  ring

theorem matrix_raw_old (c a b : R) (K : Site→Site→R) (i : Site) (j : Old) :
    let p := (actualHost c a b).retainedPoly (oldBasis j)
    tableau15 c a b K (rawSlot i) (oldSlot j) =
      p.primitive (rawClock c a b i) - rawTransact K (fun k => p.eval (rawClock c a b k)) i := by
  let p := (actualHost c a b).retainedPoly (oldBasis j)
  change tableau15 c a b K (rawSlot i) (oldSlot j) = _
  rw [tableau15,split_rawSlot,split_oldSlot]
  change p.primitive (forwardClock c a b i.rev) -
    (∑ k : Site,K k.rev i.rev.rev*p.eval (forwardClock c a b k)) = _
  rw [forward_at_rawSlot,Fin.rev_rev]
  change p.primitive (rawClock c a b i) -
    (∑ k : Site,K k.rev i*p.eval (rawClock c a b k.rev)) = _
  exact congrArg (p.primitive (rawClock c a b i) - ·)
    (Equiv.sum_comp Fin.revPerm (fun k : Site => K k i*p.eval (rawClock c a b k)))

/-- The true raw action of the physical 15-stage tableau on an arbitrary
full stage vector, including its retained decoder contact. -/
theorem tableau15_raw_action (c a b : R) (K : Site→Site→R) (g : Fin 15→R) (i : Site) :
    let q := (actualHost c a b).retainedPoly (g ∘ oldSlot)
    (∑ j : Fin 15,tableau15 c a b K (rawSlot i) j*g j) =
      q.primitive (rawClock c a b i) -
      rawTransact K (fun k => q.eval (rawClock c a b k)) i +
      rawTransact K (g ∘ rawSlot) i := by
  let p:=actualHost c a b
  let q:=p.retainedPoly (g∘oldSlot)
  let f (j : Old) := p.retainedPoly (oldBasis j)
  have hFold :
      (∑ j : Old,(∑ k : Site,K k i*(f j).eval (rawClock c a b k))*g (oldSlot j))=
        ∑ k : Site,K k i*q.eval (rawClock c a b k) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_assoc,←Finset.mul_sum]
    congr 1
    exact retained_eval_sum p (g∘oldSlot) (rawClock c a b k)
  rw [sum_slots]
  simp_rw [matrix_raw_raw,matrix_raw_old]
  change (∑ j : Old,((f j).primitive (rawClock c a b i) -
    rawTransact K (fun k => (f j).eval (rawClock c a b k)) i)*g (oldSlot j))+
    rawTransact K (g∘rawSlot) i = _
  simp only [sub_mul,Finset.sum_sub_distrib,rawTransact]
  rw [hFold]
  have hPri := retained_primitive_sum p (g∘oldSlot) (rawClock c a b i)
  change (∑ j : Old,(f j).primitive (rawClock c a b i)*g (oldSlot j))=q.primitive (rawClock c a b i) at hPri
  rw [hPri]

/-- Strict explicitness of the actual literal width-15 tableau. -/
theorem actual_tableau_strict (c a b : R) :
    strictlyLower (tableau15 c a b (actualK c a b)) :=
  tableau15_strict c a b _ (actualK_strict c a b)

end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.sum_slots
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.tableau15_raw_action
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_tableau_strict
