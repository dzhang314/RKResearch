module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicOrderBush

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear
open scoped Ring BigOperators
noncomputable section
set_option maxHeartbeats 500000

variable {R : Type*} [CommRing R]

def retainedClock (p : HostInput R) (ε : R) : Old→R := ![0,ε,p.s,p.q]

def retainedAct (p : HostInput R) (ε : R) (g : Old→R) (i : Old) : R :=
  ∑ j : Old,p.retainedOpening ε i j*g j

def retainedProj (p : HostInput R) (g : Old→R) : R := g 3-p.α*g 2

def firstEpsTap (p : HostInput R) (ε : R) : R :=
  p.s^2*Ring.inverse (2*ε)
def secondEpsTap (p : HostInput R) (ε : R) : R := p.α*firstEpsTap p ε
def oldThirdTap (p : HostInput R) (ε : R) : R :=
  (p.q^2*Ring.inverse (2:R)-ε*secondEpsTap p ε)*Ring.inverse p.s

theorem retainedAct_add (p : HostInput R) (ε : R) (v w : Old→R) (i : Old) :
    retainedAct p ε (v+w) i=retainedAct p ε v i+retainedAct p ε w i := by
  simp [retainedAct,mul_add,Finset.sum_add_distrib]

theorem retainedAct_scale (p : HostInput R) (ε : R) (u : R) (v : Old→R) (i : Old) :
    retainedAct p ε (fun j=>u*v j) i = u*retainedAct p ε v i := by
  rw [retainedAct,retainedAct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem retainedAct_one (p : HostInput R) (ε : R) :
    retainedAct p ε 1=retainedClock p ε := by
  funext i
  fin_cases i <;> simp [retainedAct,retainedClock,HostInput.retainedOpening,Fin.sum_univ_four] <;> ring

theorem retained_order_taps (p : HostInput R) (ε : R)
    (he : IsUnit ε) (h2 : IsUnit (2:R)) (hs : IsUnit p.s) :
    firstEpsTap p ε*ε=p.s^2*Ring.inverse (2:R) ∧
    oldThirdTap p ε*p.s=p.q^2*Ring.inverse (2:R)-ε*secondEpsTap p ε := by
  have hi2 := Ring.mul_inverse_cancel _ h2
  have hiS := Ring.mul_inverse_cancel _ hs
  have hI := Ring.mul_inverse_cancel _ (h2.mul he)
  constructor
  · apply h2.mul_left_cancel
    unfold firstEpsTap
    linear_combination p.s^2*(hI-hi2)
  · unfold oldThirdTap
    rw [mul_assoc,mul_comm (Ring.inverse p.s) p.s,hiS,mul_one]

theorem retained_linear_primitive (p : HostInput R) (ε : R)
    (he : IsUnit ε) (h2 : IsUnit (2:R)) (hs : IsUnit p.s) :
    retainedAct p ε (retainedClock p ε)=
      fun i=> (retainedClock p ε i)^2*Ring.inverse (2:R)-
          (ε^2*Ring.inverse (2:R))*oldBasis 1 i := by
  obtain ⟨hx,hz⟩ := retained_order_taps p ε he h2 hs
  funext i
  fin_cases i
  · simp [retainedAct,HostInput.retainedOpening,retainedClock,oldBasis,Fin.sum_univ_four]
  · simp [retainedAct,HostInput.retainedOpening,retainedClock,oldBasis,Fin.sum_univ_four]
  · simp [retainedAct,HostInput.retainedOpening,retainedClock,oldBasis,Fin.sum_univ_four]
    change firstEpsTap p ε*ε=p.s^2*Ring.inverse (2:R)
    exact hx
  · simp [retainedAct,HostInput.retainedOpening,retainedClock,oldBasis,Fin.sum_univ_four]
    change secondEpsTap p ε*ε+oldThirdTap p ε*p.s=p.q^2*Ring.inverse (2:R)
    linear_combination hz

theorem retained_basis_drop (p : HostInput R) (ε : R) :
    retainedProj p (retainedAct p ε (oldBasis 1))=0 := by
  simp [retainedProj,retainedAct,HostInput.retainedOpening,oldBasis,Fin.sum_univ_four] <;> ring

theorem retained_quadratic_primitive (p : HostInput R) (ε : R)
    (he : IsUnit ε) (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (hs : IsUnit p.s) :
    retainedProj p (retainedAct p ε (fun i=>(retainedClock p ε i)^2)) =
      retainedProj p (fun i=>(retainedClock p ε i)^3*Ring.inverse (3:R)) := by
  have hα : p.α*p.s^3=p.q^2*(3*p.s-2*p.q) := by
    unfold HostInput.α
    rw [mul_assoc,mul_comm (Ring.inverse (p.s^3)) (p.s^3),
      Ring.mul_inverse_cancel _ (hs.pow 3),mul_one]
  obtain ⟨hx,hz⟩ := retained_order_taps p ε he h2 hs
  have hI := Ring.mul_inverse_cancel _ h2
  have hJ := Ring.mul_inverse_cancel _ h3
  simp [retainedProj,retainedAct,HostInput.retainedOpening,retainedClock,Fin.sum_univ_four]
  change secondEpsTap p ε*ε^2+oldThirdTap p ε*p.s^2-p.α*(firstEpsTap p ε*ε^2) =
    p.q^3*Ring.inverse (3:R)-p.α*(p.s^3*Ring.inverse (3:R))
  apply (h2.mul h3).mul_left_cancel
  unfold secondEpsTap at hz ⊢
  linear_combination
    6*p.s*hz-6*p.α*p.s*hx+
    3*(p.s*p.q^2-p.α*p.s^3)*hI-
    2*(p.q^3-p.α*p.s^3)*hJ-hα

theorem tableau15_old_action (c a b : R) (K : Site→Site→R) (g : Fin 15→R) (i : Old) :
    (∑ j : Fin 15,tableau15 c a b K (oldSlot i) j*g j)=
      retainedAct (actualHost c a b) (Ring.inverse (8:R)) (g∘oldSlot) i := by
  rw [sum_slots]
  simp [matrix_old_old,matrix_old_raw,retainedAct]

theorem retainedTreeProfile_attach (c a b : R) (u v : RKCert.Tree) :
    retainedTreeProfile c a b (.attach u v)=
      retainedAct (actualHost c a b) (Ring.inverse (8:R)) (retainedTreeProfile c a b u)*
        retainedTreeProfile c a b v := by
  funext i
  simp only [retainedTreeProfile,RKCert.stageWeight,Pi.mul_apply]
  rw [tableau15_old_action]
  rfl

end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.retained_linear_primitive
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.retained_quadratic_primitive
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.retainedTreeProfile_attach
