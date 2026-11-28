module
public import Init
@[expose] public section

namespace RKResearch.Certified.ERK10AdjointCore
set_option maxHeartbeats 0
set_option maxRecDepth 40000

def integralNumerator (f : Int → Int) : Int :=
  2082753*f 0+9449717*f 1-11271304*f 2+16002320*f 3-17283646*f 4+
    13510082*f 5-7394032*f 6+2687864*f 7-583435*f 8+57281*f 9

abbrev betaRow (k : Nat) : Prop :=
  ∀ i : Fin 9,k+i.val ≤ 8 →
    Int.ofNat (i.val+1)*integralNumerator (fun y=>y^(k+1)*(1-y)^i.val)=
      Int.ofNat (k+1)*integralNumerator (fun y=>y^k*(1-y)^(i.val+1))

theorem b0 : betaRow 0 := by decide +kernel
theorem b1 : betaRow 1 := by decide +kernel
theorem b2 : betaRow 2 := by decide +kernel
theorem b3 : betaRow 3 := by decide +kernel
theorem b4 : betaRow 4 := by decide +kernel
theorem b5 : betaRow 5 := by decide +kernel
theorem b6 : betaRow 6 := by decide +kernel
theorem b7 : betaRow 7 := by decide +kernel
theorem b8 : betaRow 8 := by decide +kernel

theorem beta_grid (k : Fin 9) : betaRow k.val := by
  have h0 := k.isLt
  have h : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨
      k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 := by omega
  rcases h with h|h|h|h|h|h|h|h|h <;> rw [h]
  · exact b0
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · exact b5
  · exact b6
  · exact b7
  · exact b8

def jac (y : Int) : Int := y-14*y^2+56*y^3-84*y^4+42*y^5

theorem jacobi_grid : ∀ i : Fin 5, i.val ≠ 0 →
    integralNumerator (fun y=>jac y*(1-y)^i.val)=0 := by decide +kernel

end RKResearch.Certified.ERK10AdjointCore

#print axioms RKResearch.Certified.ERK10AdjointCore.beta_grid
#print axioms RKResearch.Certified.ERK10AdjointCore.jacobi_grid
