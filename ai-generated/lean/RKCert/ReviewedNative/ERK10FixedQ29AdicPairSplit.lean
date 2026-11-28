module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPairInputs

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical

open PaidBarycentric Nonlinear Polynomial
open scoped Ring BigOperators Polynomial

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

structure PairInput (R : Type*) where
  W : R
  U : R
  L : R
  Q : R
  Λ : R
deriving DecidableEq

structure PairOutput (R : Type*) where
  w1 : R
  w2 : R
  u1 : R
  u2 : R
  eta1 : R
  eta2 : R
deriving DecidableEq

namespace PairInput

variable {R S : Type*} [CommRing R] [CommRing S]

def balance (p : PairInput R) : R := p.Λ*p.Q⁻¹ʳ
def tDen (p : PairInput R) : R := p.balance*p.L + p.W*p.L⁻¹ʳ-2*p.U
def firstU (p : PairInput R) : R := (p.balance*p.W-p.U^2)*p.tDen⁻¹ʳ

def split (p : PairInput R) : PairOutput R :=
  let t:=p.firstU
  let w2:=p.W-p.L*t
  let u2:=p.U-t
  ⟨p.L*t,w2,t,u2,p.Q*p.L⁻¹ʳ,p.Q*u2*w2⁻¹ʳ⟩

def guards (p : PairInput R) : Prop :=
  IsUnit p.L ∧ IsUnit p.Q ∧ IsUnit p.tDen ∧ IsUnit p.split.w2

def map (p : PairInput R) (ρ : R→+*S) : PairInput S :=
  ⟨ρ p.W,ρ p.U,ρ p.L,ρ p.Q,ρ p.Λ⟩

def PairOutputMap (z : PairOutput R) (ρ : R→+*S) : PairOutput S :=
  ⟨ρ z.w1,ρ z.w2,ρ z.u1,ρ z.u2,ρ z.eta1,ρ z.eta2⟩

theorem map_tDen (ρ : R→+*S) [IsLocalHom ρ] (p : PairInput R) :
    ρ p.tDen = (p.map ρ).tDen := by
  simp [tDen,balance,map,map_ringInverse,map_ofNat]

theorem map_split (ρ : R→+*S) [IsLocalHom ρ] (p : PairInput R) :
    PairOutputMap p.split ρ = (p.map ρ).split := by
  simp [PairOutputMap,split,firstU,tDen,balance,map,map_ringInverse,map_ofNat]

/-- Exact pair readout, on the paid nonzero quadratic branch. -/
theorem split_equations (p : PairInput R) (hh : p.guards) :
    p.split.w1+p.split.w2=p.W ∧ p.split.u1+p.split.u2=p.U ∧
    p.split.w1*p.split.eta1=p.Q*p.split.u1 ∧ p.split.w2*p.split.eta2=p.Q*p.split.u2 ∧
    p.split.eta1*p.split.u1+p.split.eta2*p.split.u2=p.Λ := by
  obtain ⟨hL,hQ,hD,hW2⟩ := hh
  let z := p.split
  have h1 : p.L*z.eta1=p.Q := by
    change p.L*(p.Q*p.L⁻¹ʳ)=p.Q
    rw [mul_left_comm,Ring.mul_inverse_cancel _ hL,mul_one]
  have h2 : z.w2*z.eta2=p.Q*z.u2 := by
    change z.w2*((p.Q*z.u2)*z.w2⁻¹ʳ)=p.Q*z.u2
    rw [mul_left_comm,Ring.mul_inverse_cancel _ hW2,mul_one]
  have hB : p.Q*p.balance=p.Λ := by
    rw [balance,mul_left_comm,Ring.mul_inverse_cancel _ hQ,mul_one]
  have hWL : p.L*(p.W*p.L⁻¹ʳ)=p.W := by
    rw [mul_left_comm,Ring.mul_inverse_cancel _ hL,mul_one]
  have ht : p.tDen*z.u1=p.balance*p.W-p.U^2 := by
    change p.tDen*((p.balance*p.W-p.U^2)*p.tDen⁻¹ʳ)=p.balance*p.W-p.U^2
    rw [mul_left_comm,Ring.mul_inverse_cancel _ hD,mul_one]
  have hPair : p.balance*p.L*z.w2=p.L*z.u2^2+z.u1*z.w2 := by
    apply sub_eq_zero.mp
    calc
      _ = -p.L*(p.tDen*z.u1-(p.balance*p.W-p.U^2))+
            z.u1*(p.L*(p.W*p.L⁻¹ʳ)-p.W) := by
        change p.balance*p.L*(p.W-p.L*p.firstU)-
          (p.L*(p.U-p.firstU)^2+p.firstU*(p.W-p.L*p.firstU)) =
          -p.L*(p.tDen*p.firstU-(p.balance*p.W-p.U^2))+
          p.firstU*(p.L*(p.W*p.L⁻¹ʳ)-p.W)
        unfold tDen
        ring
      _ = 0 := by rw [ht,hWL]; ring
  have wsum : z.w1+z.w2=p.W := by change p.L*p.firstU+(p.W-p.L*p.firstU)=_; ring
  have usum : z.u1+z.u2=p.U := by change p.firstU+(p.U-p.firstU)=_; ring
  have wone : z.w1*z.eta1=p.Q*z.u1 := by
    calc
      _ = (p.L*z.eta1)*z.u1 := by change (p.L*p.firstU)*z.eta1=(p.L*z.eta1)*p.firstU; ring
      _ = _ := by rw [h1]
  refine ⟨wsum,usum,wone,h2,?_⟩
  apply (hL.mul hW2).mul_left_cancel
  calc
    _ = (p.L*z.eta1)*z.u1*z.w2 + p.L*(z.w2*z.eta2)*z.u2 := by ring
    _ = p.Q*(p.L*z.u2^2+z.u1*z.w2) := by rw [h1,h2];ring
    _ = _ := by rw [←hPair];calc
          _ = (p.L*z.w2)*(p.Q*p.balance) := by ring
          _ = _ := by rw [hB]

end PairInput

variable {R : Type*} [CommRing R]

def physicalPair (c a b : R) : PairInput R :=
  let x:=nodal c a b
  ⟨score x center,uAggregate x (actualScale x) center,
    centerRatio c a b,(actualQ c x).eval c,splitLambda (closureU c) x (actualScale x)⟩

def pairMod : PairInput F := ⟨18,25,8,8,11⟩
def splitMod : PairOutput F := ⟨5,13,26,28,1,15⟩

theorem pair_split_mod : pairMod.split = splitMod := by
  simp only [pairMod,splitMod,PairInput.split,PairInput.firstU,PairInput.tDen,PairInput.balance,
    Ring.inverse_eq_inv]
  decide +kernel

theorem pair_den_mod : pairMod.tDen=14 := by
  simp only [pairMod,PairInput.tDen,PairInput.balance,Ring.inverse_eq_inv]
  decide +kernel

section Actual
variable (ρ : R →+* F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

theorem physicalPair_reduce :
    (physicalPair c a b).map ρ = pairMod := by
  have hcen : center∈ordinary := by decide +kernel
  simp only [physicalPair,PairInput.map,actual_weight_residue ρ c a b hc ha hb,
    actual_u_residue ρ c a b hc ha hb hcen,actual_Lc_residue ρ c a b hc ha hb,
    actual_Qc_residue ρ c a b hp hc ha hb,actual_lambda_residue ρ c a b hp hc ha hb]
  decide +kernel

theorem physicalSplit_reduce :
    PairInput.PairOutputMap (physicalPair c a b).split ρ = splitMod := by
  rw [PairInput.map_split,physicalPair_reduce ρ c a b hp hc ha hb,pair_split_mod]

theorem physicalPair_guards : (physicalPair c a b).guards := by
  have h := physicalPair_reduce ρ c a b hp hc ha hb
  have hs := physicalSplit_reduce ρ c a b hp hc ha hb
  refine ⟨IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr ?_),
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr ?_),
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr ?_),
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr ?_)⟩
  · have H := congrArg PairInput.L h
    change ρ (physicalPair c a b).L=8 at H
    rw [H]; decide +kernel
  · have H := congrArg PairInput.Q h
    change ρ (physicalPair c a b).Q=8 at H
    rw [H]; decide +kernel
  · rw [PairInput.map_tDen ρ, h, pair_den_mod]; decide +kernel
  · have H := congrArg PairOutput.w2 hs
    change ρ (physicalPair c a b).split.w2=13 at H
    rw [H]; decide +kernel

theorem physical_pair_independent :
    IsUnit ((physicalPair c a b).W-(physicalPair c a b).L*(physicalPair c a b).U) := by
  have H := congrArg (fun p : PairInput F => p.W-p.L*p.U) (physicalPair_reduce ρ c a b hp hc ha hb)
  change ρ (physicalPair c a b).W-ρ (physicalPair c a b).L*ρ (physicalPair c a b).U =
    (18:F)-8*25 at H
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [map_sub,map_mul,H]
  decide +kernel

theorem physical_pair_firstU_unit : IsUnit (physicalPair c a b).split.u1 := by
  have h := congrArg PairOutput.u1 (physicalSplit_reduce ρ c a b hp hc ha hb)
  change ρ (physicalPair c a b).split.u1=26 at h
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [h]; decide +kernel

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.PairInput.split_equations
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.physicalSplit_reduce
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.physicalPair_guards
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.physical_pair_independent
