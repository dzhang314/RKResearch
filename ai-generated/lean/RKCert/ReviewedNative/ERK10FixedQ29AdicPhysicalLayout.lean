module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicRawReadout
public import RKCert.ReviewedNative.ERK10FixedQ29AdicDecoder

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical

open Nonlinear Polynomial
open scoped Ring BigOperators Polynomial

noncomputable section
set_option maxHeartbeats 400000

variable {R : Type*} [CommRing R]

def forwardClock (c a b : R) : Site→R := fun i => 1-rawY c a b i.rev
def forwardEta (c a b : R) : Site→R := fun i => rawEta c a b i.rev
def forwardWeight (c a b : R) : Site→R := fun i => rawW c a b i.rev

theorem forward_host_nodes (c a b : R) :
    forwardClock c a b 0=(actualHost c a b).r ∧
    forwardClock c a b 1=(actualHost c a b).v ∧
    forwardClock c a b 2=(actualHost c a b).z ∧
    forwardEta c a b 1=(actualHost c a b).ηv ∧
    forwardEta c a b 2=(actualHost c a b).ηz := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Precisely four retained opening rows followed by all eleven raw rows. -/
def splitStage (j : Fin 15) : PhysicalStage :=
  if h : j.val<4 then .inl ⟨j.val,h⟩ else .inr ⟨j.val-4,by omega⟩

theorem splitStage_index (j : Fin 15) : physicalIndex (splitStage j)=j.val := by
  unfold splitStage
  split
  · rfl
  · simp only [physicalIndex]
    omega

theorem splitStage_fifth : splitStage (4:Fin 15)=.inr 0 := rfl

theorem splitStage_old (j : Old) :
    splitStage (Fin.castLE (by decide : 4≤15) j)=.inl j := by
  unfold splitStage
  have hj : (Fin.castLE (by decide : 4≤15) j).val<4 := j.isLt
  rw [dite_eq_left hj]
  rfl

def tableau15 (c a b : R) (K : Site→Site→R) : Fin 15→Fin 15→R :=
  fun i j => physicalDecoder (actualHost c a b) (reverseTranspose K)
    (forwardClock c a b) (8:R)⁻¹ʳ (splitStage i) (splitStage j)

def tableauWeights (c a b : R) (j : Fin 15) : R :=
  match splitStage j with
  | .inl i => if i=0 then score (nodal c a b) oldOrigin else 0
  | .inr i => forwardWeight c a b i

theorem tableau15_strict (c a b : R) (K : Site→Site→R) (hK : strictlyLower K) :
    strictlyLower (tableau15 c a b K) := by
  intro i j hij
  apply physicalDecoder_strict _ _ _ _ (reverseTranspose_strict hK)
  change i.val≤j.val at hij
  simpa only [splitStage_index] using hij

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

omit hp ha hb in
theorem actual_forward_host_eta : forwardEta c a b 0=1 := by
  change -(closureU c).eval 15=1
  rw [closure_host ρ c hc,neg_neg]

theorem tableau15_fifth (K : Site→Site→R) (hK : strictlyLower K) (j : Old) :
    tableau15 c a b K 4 (Fin.castLE (by decide : 4≤15) j) =
      (actualHost c a b).retainedAtHost j := by
  rw [tableau15,splitStage_fifth,splitStage_old]
  exact actual_physical_fifth ρ c a b hp hc ha hb _ _ _ (reverseTranspose_strict hK)
    (forward_host_nodes c a b).1 j

/-- The shared physical column is the genuine old-host column provided
the raw block pays its quadratic forward receipt at that row. -/
theorem tableau15_shared_tap {K : Site→Site→R} (i : Site)
    (hModel : ∑ j : Site, reverseTranspose K i j *
      (actualHost c a b).eval2 (forwardClock c a b j) =
      (actualHost c a b).int2 (forwardClock c a b i)) :
    let p:=actualHost c a b
    p.hostIntegral (forwardClock c a b i) -
      ∑ j∈Finset.univ.erase 0, reverseTranspose K i j*p.hostBasis (forwardClock c a b j) =
        reverseTranspose K i 0 := by
  exact (actualHost c a b).shared_column _ _
    (actual_host_guards ρ c a b hp hc ha hb 9) (forward_host_nodes c a b).1 i hModel

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.forward_host_nodes
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.tableau15_strict
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_forward_host_eta
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.tableau15_fifth
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.tableau15_shared_tap
