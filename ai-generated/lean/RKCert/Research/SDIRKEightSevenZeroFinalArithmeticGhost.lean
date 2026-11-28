import Mathlib.Tactic.Ring.Basic

/-!
Division-free affine and two-atom identities for the final silent-ghost
case. The actual flag ingress and exact algebraic fibres are separate.
-/

namespace RKResearch.Certified.SDIRKEightSevenZeroFinalArithmeticGhost

variable {R : Type*} [CommRing R]

def ghostH (v : R) : R := v^3-4*v^2-v+2
def kappa (v : R) : R := 1+2*v-v^2

/-- Six times the primitive of the quadratic rear profile in reflected time. -/
def prim6 (v y : R) : R := 6*(1+v)*y-3*(2+v)*y^2+2*y^3

theorem ghost_affine_factor (v e : R) :
    v*kappa v*prim6 v 1+(e-1)*(prim6 v (1+v)-kappa v*prim6 v 1) =
      (e-1-2*v)*(prim6 v (1+v)-kappa v*prim6 v 1)+v*ghostH v := by
  unfold prim6 kappa ghostH
  ring1

/-- Clearing the two reproducing kernels loses all dependence on the
unknown cardinal mass. No root of the quartic is divided here. -/
theorem two_atom_curve_clear
    {x s t α β L Ls Lt S CS CL F W q Ds Dt : R}
    (hDisc : L*CS-S*CL=-(α*Ds+β*Dt))
    (hs : (x-s)*Ds=L-Ls) (ht : (x-t)*Dt=L-Lt)
    (hW : (x-s)*(x-t)*W=F*(α*(x-t)+β*(x-s))+q)
    (hLin : F*(L*CS-S*CL)+L*W=0) :
    q*L+F*(α*Ls*(x-t)+β*Lt*(x-s))=0 := by
  have aux : (x-s)*(x-t)*(L*CS-S*CL) =
      -(α*(x-t)*(L-Ls)+β*(x-s)*(L-Lt)) := by
    calc
      _ = -(α*(x-t)*((x-s)*Ds)+β*(x-s)*((x-t)*Dt)) := by rw [hDisc]; ring1
      _ = _ := by rw [hs,ht]
  calc
    _ = F*(-(α*(x-t)*(L-Ls)+β*(x-s)*(L-Lt)))+
          L*(F*(α*(x-t)+β*(x-s))+q) := by ring1
    _ = F*((x-s)*(x-t)*(L*CS-S*CL))+L*((x-s)*(x-t)*W) := by rw [← aux,← hW]
    _ = (x-s)*(x-t)*(F*(L*CS-S*CL)+L*W) := by ring1
    _ = _ := by rw [hLin,mul_zero]

end RKResearch.Certified.SDIRKEightSevenZeroFinalArithmeticGhost
