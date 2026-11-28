module
public import RKCert.ReviewedNative.ERK10FixedQ29AdicWordB
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section

/- BUNDLE CenterScalar -/
namespace RKResearch.Certified.ERK10CenterScalar

/-! Paid denominator-clearance for the first and second center donors. -/
set_option maxHeartbeats 500000

variable {U : Type*} [CommRing U]
variable (s t k d iS iT iD iR i2 i3 i4 : U)

def gainB (s k : U) : U := -2-4*k*(s-1)
def gainC (s t k iD : U) : U := (-2)*(2*s*t*k^2+2*s*t*k-2*s*k^2+s*k-2*t*k+t)*iD
def pickB (s t k iD iR : U) : U := s*k*(t-1)*(t-s)*iD*iR
def pickA (s t k iD iR : U) : U := k*(t-1)-pickB s t k iD iR
def modelP (s t k i3 : U) : U := 2*t*i3+k*(4*s*i3-2)*(t-1)
def modelQ (s t k iD : U) : U := k*(t-1)+s*k*(t-1)*(t-s)*iD
def modelR (s t k iD i2 : U) : U := t^2*i2+k*(s^2-2)*(t-1)-s*k*(s*k-t*k-t+2)*(t-1)*(t-s)*iD
def nullGain (s t k iS iT iD : U) : U := -2*(t-s)+(1-t)*gainB s k*iS+(s-1)*gainC s t k iD*iT

def clearDen (s t d : U) : U := 12*s*t*d*(s-1)

theorem read1 (hS : s*iS=1) (hD : d*iD=1) (hR : (s-1)*iR=1) (h2 : 2*i2=1) (hdelta : d=3*s*k-2*t*k+t) :
    clearDen s t d * ((-2*(pickA s t k iD iR)+(gainB s k)*iS*(pickB s t k iD iR))-((gainC s t k iD)*i2+1))=0 := by
  unfold clearDen pickA pickB gainB gainC
  linear_combination (24*k*s*t*(s - t)*(t - 1)*(2*k*s - 2*k + 1))*hS +
    (12*s*t*(4*iS*k^2*s^3*t - 4*iS*k^2*s^3 - 4*iS*k^2*s^2*t^2 + 4*iS*k^2*s^2 + 4*iS*k^2*s*t^2 - 4*iS*k^2*s*t + 2*iS*k*s^2*t - 2*iS*k*s^2 - 2*iS*k*s*t^2 + 2*iS*k*s*t + 2*k^2*s^2*t - 2*k^2*s^2 - 2*k^2*s*t + 2*k^2*s + 3*k*s^2 + 2*k*s*t^2 - 6*k*s*t - k*s + 2*k*t + s*t - t))*hD +
    (24*d*iD*k*s^2*t*(s - t)*(t - 1)*(2*iS*k*s - 2*iS*k + iS - 1))*hR +
    (12*d*iD*s*t*(s - 1)*(2*k^2*s*t - 2*k^2*s + 2*k*s*t + k*s - 2*k*t + t))*h2 +
    (-12*s*t*(s - 1)*(2*k*t - 2*k + 1))*hdelta

theorem read2 (hD : d*iD=1) (hR : (s-1)*iR=1) (h3 : 3*i3=1) (hdelta : d=3*s*k-2*t*k+t) :
    clearDen s t d * ((-2*(pickA s t k iD iR)+(gainB s k)*(pickB s t k iD iR))-((gainC s t k iD)*t*i3+(modelP s t k i3)))=0 := by
  unfold clearDen pickA pickB gainB gainC modelP
  linear_combination (8*s*t*(s - 1)*(3*k*s - 2*k*t + t)*(2*k*s*t - 2*k*s + t))*hD +
    (48*d*iD*k^2*s^2*t*(s - 1)*(s - t)*(t - 1))*hR +
    (8*d*s*t*(s - 1)*(2*iD*k^2*s*t^2 - 2*iD*k^2*s*t + 2*iD*k*s*t^2 + iD*k*s*t - 2*iD*k*t^2 + iD*t^2 - 2*k*s*t + 2*k*s - t))*h3 +
    (-8*s*t*(s - 1)*(2*k*s*t - 2*k*s + t))*hdelta

theorem read3 (hD : d*iD=1) (hR : (s-1)*iR=1) (h2 : 2*i2=1) (h4 : 4*i4=1) (hdelta : d=3*s*k-2*t*k+t) :
    clearDen s t d * ((-2*(pickA s t k iD iR)+s*(gainB s k)*(pickB s t k iD iR))-((gainC s t k iD)*t^2*i4+(modelR s t k iD i2)))=0 := by
  unfold clearDen pickA pickB gainB gainC modelR
  linear_combination (6*s*t*(s - 1)*(3*k*s - 2*k*t + t)*(2*k*s^2*t - 2*k*s^2 + t^2))*hD +
    (24*d*iD*k*s^2*t*(s - 1)*(s - t)*(t - 1)*(2*k*s + 1))*hR +
    (-6*d*s*t^3*(s - 1))*h2 +
    (6*d*iD*s*t^3*(s - 1)*(2*k^2*s*t - 2*k^2*s + 2*k*s*t + k*s - 2*k*t + t))*h4 +
    (-6*s*t*(s - 1)*(2*k*s^2*t - 2*k*s^2 + t^2))*hdelta

theorem readU  :
    clearDen s t d * (((pickA s t k iD iR)+(pickB s t k iD iR))-(k*(t-1)))=0 := by
  unfold clearDen pickA pickB
  ring

theorem readYU (hR : (s-1)*iR=1) :
    clearDen s t d * (((pickA s t k iD iR)+s*(pickB s t k iD iR))-((modelQ s t k iD)))=0 := by
  unfold clearDen pickA pickB modelQ
  linear_combination (-12*d*iD*k*s^2*t*(s - 1)*(s - t)*(t - 1))*hR

theorem vary2 (hS : s*iS=1) (hT : t*iT=1) (hD : d*iD=1) (h3 : 3*i3=1) (hdelta : d=3*s*k-2*t*k+t) (hk : 2*k*(t-2*s)=t) :
    clearDen s t d * ((-2*(t-s)+(1-t)*(gainB s k)+(s-1)*(gainC s t k iD))-(2*t*i3*(nullGain s t k iS iT iD)))=0 := by
  unfold clearDen nullGain gainB gainC
  linear_combination (-16*d*t^2*(s - 1)*(t - 1)*(2*k*s - 2*k + 1))*hS +
    (16*s*t*(s - 1)^2*(2*k^2*s*t - 2*k^2*s + 2*k*s*t + k*s - 2*k*t + t))*hT +
    (8*s*t*(s - 1)^2*(2*iT*t - 3)*(2*k^2*s*t - 2*k^2*s + 2*k*s*t + k*s - 2*k*t + t))*hD +
    (16*d*s*t^2*(s - 1)*(2*iD*iT*k^2*s^2*t - 2*iD*iT*k^2*s^2 - 2*iD*iT*k^2*s*t + 2*iD*iT*k^2*s + 2*iD*iT*k*s^2*t + iD*iT*k*s^2 - 4*iD*iT*k*s*t - iD*iT*k*s + 2*iD*iT*k*t + iD*iT*s*t - iD*iT*t - 2*iS*k*s*t + 2*iS*k*s + 2*iS*k*t - 2*iS*k - iS*t + iS - s + t))*h3 +
    (8*t*(s - 1)^2*(6*k*s*t - 6*k*s - 4*k*t^2 + 4*k*t - 2*s*t + 3*s + 2*t^2 - 2*t))*hdelta +
    (-16*t*(2*k - 1)*(s - 1)^2*(s - t)*(t - 1))*hk

theorem vary3 (hS : s*iS=1) (hT : t*iT=1) (hD : d*iD=1) (h2 : 2*i2=1) (hdelta : d=3*s*k-2*t*k+t) (hk : 2*k*(t-2*s)=t) :
    clearDen s t d * ((-2*(t-s)+(1-t)*s*(gainB s k)+(s-1)*t*(gainC s t k iD))-(t^2*i2*(nullGain s t k iS iT iD)))=0 := by
  unfold clearDen nullGain gainB gainC
  linear_combination (-12*d*t^3*(s - 1)*(t - 1)*(2*k*s - 2*k + 1))*hS +
    (12*s*t^2*(s - 1)^2*(2*k^2*s*t - 2*k^2*s + 2*k*s*t + k*s - 2*k*t + t))*hT +
    (12*s*t^2*(s - 1)^2*(iT*t - 2)*(2*k^2*s*t - 2*k^2*s + 2*k*s*t + k*s - 2*k*t + t))*hD +
    (12*d*s*t^3*(s - 1)*(2*iD*iT*k^2*s^2*t - 2*iD*iT*k^2*s^2 - 2*iD*iT*k^2*s*t + 2*iD*iT*k^2*s + 2*iD*iT*k*s^2*t + iD*iT*k*s^2 - 4*iD*iT*k*s*t - iD*iT*k*s + 2*iD*iT*k*t + iD*iT*s*t - iD*iT*t - 2*iS*k*s*t + 2*iS*k*s + 2*iS*k*t - 2*iS*k - iS*t + iS - s + t))*h2 +
    (12*t*(s - 1)^2*(4*k*s^2*t - 4*k*s^2 - 2*k*t^3 + 2*k*t^2 - s*t^2 + 2*s*t + t^3 - t^2))*hdelta +
    (-12*t*(s - 1)^2*(s - t)*(t - 1)*(3*k*s + 2*k*t - t))*hk

end RKResearch.Certified.ERK10CenterScalar

#print axioms RKResearch.Certified.ERK10CenterScalar.read1
#print axioms RKResearch.Certified.ERK10CenterScalar.read2
#print axioms RKResearch.Certified.ERK10CenterScalar.read3
#print axioms RKResearch.Certified.ERK10CenterScalar.readU
#print axioms RKResearch.Certified.ERK10CenterScalar.readYU
#print axioms RKResearch.Certified.ERK10CenterScalar.vary2
#print axioms RKResearch.Certified.ERK10CenterScalar.vary3

/- BUNDLE CenterReadout -/
namespace RKResearch.Certified.ERK10CenterScalar

open scoped BigOperators
set_option maxHeartbeats 400000

variable {R : Type*} [CommRing R]

structure Chart (R : Type*) where
  s : R
  t : R
  k : R
  d : R
  iS : R
  iT : R
  iD : R
  iR : R
  i2 : R
  i3 : R
  i4 : R

namespace Chart
variable (X : Chart R)

def B : R := pickB X.s X.t X.k X.iD X.iR
def A : R := pickA X.s X.t X.k X.iD X.iR
def Rb : R := gainB X.s X.k
def L : R := gainC X.s X.t X.k X.iD
def G : R := nullGain X.s X.t X.k X.iS X.iT X.iD

def donors : Fin 3→Fin 5→R :=
  ![![-2,-2,-2,1,1],![X.Rb*X.iS,X.Rb,X.s*X.Rb,1,X.s],
    ![X.L*X.iT,X.L,X.t*X.L,1,X.t]]

def target (M U : R) : Fin 5→R :=
  ![M*X.i2+U,M*X.t*X.i3+U*modelP X.s X.t X.k X.i3,
    M*X.t^2*X.i4+U*modelR X.s X.t X.k X.iD X.i2,U*(X.k*(X.t-1)),
    U*modelQ X.s X.t X.k X.iD]

def n : Fin 3→R := ![X.t-X.s,1-X.t,X.s-1]
def scale (M U iG : R) : R := (M-X.L*U)*X.i2*iG
def taps (M U iG : R) : Fin 3→R :=
  ![U*X.A+X.scale M U iG*(X.t-X.s),U*X.B+X.scale M U iG*(1-X.t),
    X.scale M U iG*(X.s-1)]

def baseRead : Fin 5→R := fun j => X.A*X.donors 0 j+X.B*X.donors 1 j
def variation : Fin 5→R := fun j => ∑ l : Fin 3,X.n l*X.donors l j

structure Paid : Prop where
  c : IsUnit (clearDen X.s X.t X.d)
  u4 : IsUnit (4:R)
  aS : X.s*X.iS=1
  aT : X.t*X.iT=1
  aD : X.d*X.iD=1
  aR : (X.s-1)*X.iR=1
  a2 : 2*X.i2=1
  a3 : 3*X.i3=1
  a4 : 4*X.i4=1
  delta : X.d=3*X.s*X.k-2*X.t*X.k+X.t
  kappa : 2*X.k*(X.t-2*X.s)=X.t

theorem eq_of_clear (H : X.Paid) {l r : R} (h : clearDen X.s X.t X.d*(l-r)=0) :
    l=r := sub_eq_zero.mp (H.c.mul_left_cancel (by rwa [mul_zero]))

theorem base_reads (H : X.Paid) (j : Fin 5) :
    X.baseRead j=X.target X.L 1 j := by
  fin_cases j
  · change X.A*(-2)+X.B*(X.Rb*X.iS)=X.L*X.i2+1
    have zz : -2*X.A+X.Rb*X.iS*X.B=X.L*X.i2+1 :=
      X.eq_of_clear H (read1 X.s X.t X.k X.d X.iS X.iD X.iR X.i2 H.aS H.aD H.aR H.a2 H.delta)
    linear_combination zz
  · change X.A*(-2)+X.B*X.Rb=X.L*X.t*X.i3+1*modelP X.s X.t X.k X.i3
    have zz : -2*X.A+X.Rb*X.B=X.L*X.t*X.i3+modelP X.s X.t X.k X.i3 :=
      X.eq_of_clear H (read2 X.s X.t X.k X.d X.iD X.iR X.i3 H.aD H.aR H.a3 H.delta)
    linear_combination zz
  · change X.A*(-2)+X.B*(X.s*X.Rb)=X.L*X.t^2*X.i4+1*modelR X.s X.t X.k X.iD X.i2
    have zz : -2*X.A+X.s*X.Rb*X.B=X.L*X.t^2*X.i4+modelR X.s X.t X.k X.iD X.i2 :=
      X.eq_of_clear H (read3 X.s X.t X.k X.d X.iD X.iR X.i2 X.i4 H.aD H.aR H.a2 H.a4 H.delta)
    linear_combination zz
  · change X.A*1+X.B*1=1*(X.k*(X.t-1))
    simp only [mul_one,one_mul]
    exact X.eq_of_clear H (readU X.s X.t X.k X.d X.iD X.iR)
  · change X.A*1+X.B*X.s=1*modelQ X.s X.t X.k X.iD
    have zz : X.A+X.s*X.B=modelQ X.s X.t X.k X.iD :=
      X.eq_of_clear H (readYU X.s X.t X.k X.d X.iD X.iR H.aR)
    linear_combination zz

/-- The null perturbation is exact before any second-center weight is specified. -/
theorem variation_reads (H : X.Paid) (j : Fin 5) :
    X.variation j=(![X.G,2*X.t*X.i3*X.G,X.t^2*X.i2*X.G,0,0] : Fin 5→R) j := by
  unfold variation
  rw [Fin.sum_univ_three]
  fin_cases j
  · change (X.t-X.s)*(-2)+(1-X.t)*(X.Rb*X.iS)+(X.s-1)*(X.L*X.iT)=X.G
    unfold G nullGain Rb L
    ring
  · change (X.t-X.s)*(-2)+(1-X.t)*X.Rb+(X.s-1)*X.L=2*X.t*X.i3*X.G
    have zz : -2*(X.t-X.s)+(1-X.t)*X.Rb+(X.s-1)*X.L=2*X.t*X.i3*X.G :=
      X.eq_of_clear H (vary2 X.s X.t X.k X.d X.iS X.iT X.iD X.i3
        H.aS H.aT H.aD H.a3 H.delta H.kappa)
    linear_combination zz
  · change (X.t-X.s)*(-2)+(1-X.t)*(X.s*X.Rb)+(X.s-1)*(X.t*X.L)=X.t^2*X.i2*X.G
    have zz : -2*(X.t-X.s)+(1-X.t)*X.s*X.Rb+(X.s-1)*X.t*X.L=X.t^2*X.i2*X.G :=
      X.eq_of_clear H (vary3 X.s X.t X.k X.d X.iS X.iT X.iD X.i2
        H.aS H.aT H.aD H.a2 H.delta H.kappa)
    linear_combination zz
  · change (X.t-X.s)*1+(1-X.t)*1+(X.s-1)*1=0
    ring
  · change (X.t-X.s)*1+(1-X.t)*X.s+(X.s-1)*X.t=0
    ring

theorem first_center_reads (H : X.Paid) (U : R) (j : Fin 5) :
    (U*X.A)*X.donors 0 j+(U*X.B)*X.donors 1 j=X.target (X.L*U) U j := by
  calc
    _ = U*X.baseRead j := by unfold baseRead;ring
    _ = _ := by
      rw [X.base_reads H]
      fin_cases j <;> simp only [target,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> ring

theorem paid_inv_square (H : X.Paid) : X.i2^2=X.i4 := by
  apply H.u4.mul_left_cancel
  linear_combination (2*X.i2+1)*H.a2-H.a4

/-- Exact 5-word readout of the second center, with the third donor
available. No sign, ordering of the ground ring or nonzero second
center score is assumed. -/
theorem second_center_reads (H : X.Paid) (M U iG : R) (hp : X.G*iG=1) (j : Fin 5) :
    ∑ l : Fin 3,X.taps M U iG l*X.donors l j=X.target M U j := by
  have hsq := X.paid_inv_square H
  calc
    _ = U*X.baseRead j+X.scale M U iG*X.variation j := by
      unfold variation
      rw [Fin.sum_univ_three,Fin.sum_univ_three]
      let z:=X.scale M U iG
      change (U*X.A+z*(X.t-X.s))*X.donors 0 j+(U*X.B+z*(1-X.t))*X.donors 1 j+
        (z*(X.s-1))*X.donors 2 j =
        U*(X.A*X.donors 0 j+X.B*X.donors 1 j)+
          z*((X.t-X.s)*X.donors 0 j+(1-X.t)*X.donors 1 j+(X.s-1)*X.donors 2 j)
      ring
    _ = _ := by
      rw [X.base_reads H,X.variation_reads H]
      fin_cases j
      · simp only [target,scale,Matrix.cons_val_zero',Matrix.cons_val_succ']
        linear_combination ((M-X.L*U)*X.i2)*hp
      · simp only [target,scale,Matrix.cons_val_zero',Matrix.cons_val_succ']
        have Hmul : (2*X.i2)*(X.G*iG)=1 := by rw [H.a2,hp,mul_one]
        linear_combination ((M-X.L*U)*X.t*X.i3)*Hmul
      · simp only [target,scale,Matrix.cons_val_zero',Matrix.cons_val_succ']
        linear_combination ((M-X.L*U)*X.t^2*X.i2^2)*hp+((M-X.L*U)*X.t^2)*hsq
      · simp only [target,Matrix.cons_val_zero',Matrix.cons_val_succ',one_mul,mul_zero,add_zero]
      · simp only [target,Matrix.cons_val_zero',Matrix.cons_val_succ',one_mul,mul_zero,add_zero]

end Chart
end RKResearch.Certified.ERK10CenterScalar

#print axioms RKResearch.Certified.ERK10CenterScalar.Chart.first_center_reads
#print axioms RKResearch.Certified.ERK10CenterScalar.Chart.second_center_reads

/- BUNDLE WordWitness -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Matrix
open scoped BigOperators Ring Matrix
noncomputable section
set_option maxHeartbeats 400000

variable {R : Type*} [CommRing R]

/-- A row supported on the paid prefix and the prescribed free taps
is unique once it pays the leading word cut. -/
theorem chronologicalK_eq_witness (A T : Site→Word→R) (D : Site→Site→R)
    (i : Site) (hu : IsUnit (leadWords A (leadingLength i) (leading_le i)).det) (w : Site→R)
    (hs : ∀ j : Site, leadingLength i ≤ j.val → w j = D i j)
    (hw : ∀ k : Word, ∑ j : Site, w j*A j k=T i k) :
    chronologicalK A T D i=w := by
  let m := leadingLength i
  let M := leadWords A m (leading_le i)
  let q : Fin m→R := fun j => w (Fin.castLE (leading_le_sites i) j)-D i (Fin.castLE (leading_le_sites i) j)
  let v : Fin m→R := fun k => rowRight A T D i (Fin.castLE (leading_le i) k)
  have he (j : Site) : extendLeading q j+D i j=w j := by
    by_cases hj : j.val<m
    · have heq : Fin.castLE (leading_le_sites i) (⟨j.val,hj⟩ : Fin m)=j := Fin.ext rfl
      simp only [extendLeading,dite_eq_left hj,q,heq,sub_add_cancel]
    · rw [extendLeading,dite_eq_right hj,zero_add,hs _ (Nat.le_of_not_gt hj)]
  have hp : q ᵥ* M=v := by
    ext k
    have h := hw (Fin.castLE (leading_le i) k)
    simp_rw [←he,add_mul,Finset.sum_add_distrib,sum_extendLeading (leading_le_sites i)] at h
    change (∑ j : Fin m, q j*A (Fin.castLE (leading_le_sites i) j) (Fin.castLE (leading_le i) k))+
      (∑ j : Site,D i j*A j (Fin.castLE (leading_le i) k))=T i (Fin.castLE (leading_le i) k) at h
    change (∑ j : Fin m, q j*A (Fin.castLE (leading_le_sites i) j) (Fin.castLE (leading_le i) k))=
      T i (Fin.castLE (leading_le i) k)-∑ j : Site,D i j*A j (Fin.castLE (leading_le i) k)
    exact eq_sub_of_add_eq h
  have hq : q=rowCoeffs A T D i := by
    change q=v ᵥ* M⁻¹
    rw [←hp,Matrix.vecMul_vecMul,Matrix.mul_nonsing_inv _ hu,Matrix.vecMul_one]
  funext j
  rw [chronologicalK,←hq,he]

/-- Fill the endpoint tap \(j=0\) without affecting a positive word. -/
def fillEndpoint (A T : Site→Word→R) (i : Site) (w : Site→R) : Site→R :=
  fun j => w j + if j=0 then (T i 0 - ∑ l : Site, w l*A l 0)*(A 0 0)⁻¹ʳ else 0

theorem fillEndpoint_reads (A T : Site→Word→R) (i : Site) (w : Site→R)
    (hu : IsUnit (A 0 0)) (hz : ∀ k : Word,k≠0→A 0 k=0)
    (hw : ∀ k : Word,k≠0→∑ j : Site,w j*A j k=T i k) (k : Word) :
    ∑ j : Site,fillEndpoint A T i w j*A j k=T i k := by
  let alpha := (T i 0 - ∑ l : Site,w l*A l 0)*(A 0 0)⁻¹ʳ
  have hA : (∑ j : Site,(if j=0 then alpha else 0)*A j k)=alpha*A 0 k := by
    simp_rw [ite_mul,zero_mul]
    exact Finset.sum_ite_eq' _ _ _
  simp only [fillEndpoint,add_mul,Finset.sum_add_distrib]
  change (∑ j : Site,w j*A j k)+(∑ j : Site,(if j=0 then alpha else 0)*A j k)=T i k
  rw [hA]
  by_cases hh : k=0
  · subst k
    unfold alpha
    rw [mul_assoc,mul_comm ((A 0 0)⁻¹ʳ),Ring.mul_inverse_cancel _ hu,mul_one,add_sub_cancel]
  · rw [hz k hh,mul_zero,add_zero,hw k hh]

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

theorem actualK_early_from_positive (i : Site) (hi0 : 0 < i.val) (hi8 : i.val < 8)
    (w : Site→R) (hs : ∀ j : Site,i.val≤j.val→w j=0)
    (hw : ∀ k : Word,k≠0→∑ j : Site,w j*wordInput c a b j k=wordTarget c a b i k)
    (k : Word) :
    ∑ j : Site,actualK c a b i j*wordInput c a b j k=wordTarget c a b i k := by
  let A:=wordInput c a b
  let T:=wordTarget c a b
  let D:=(actualHost c a b).chronologicalPorts
  have hu : IsUnit (A 0 0) := by
    apply IsUnit.of_map ρ
    apply isUnit_iff_ne_zero.mpr
    change ρ (wordInput c a b 0 0)≠0
    rw [actual_word_input_mod ρ c a b hp hc ha hb]
    decide +kernel
  have hz (k : Word) (hk : k≠0) : A 0 k=0 := input_at_endpoint c a b _ hk
  have he : ∀ j : Site, leadingLength i ≤ j.val → fillEndpoint A T i w j=D i j := by
    intro j hj
    have hi : leadingLength i=i.val := Nat.min_eq_left hi8.le
    rw [hi] at hj
    have h0 : j≠0 := by intro hh;subst j;exact (Nat.not_le_of_gt hi0) hj
    have h9 : i≠9 := by intro h;subst i;contradiction
    have h10 : i≠10 := by intro h;subst i;contradiction
    simp [fillEndpoint,h0,hs _ hj,D,HostInput.chronologicalPorts,h9,h10]
  have hfull := fillEndpoint_reads A T i w hu hz hw
  have hK : actualK c a b i=fillEndpoint A T i w :=
    chronologicalK_eq_witness A T D i (actual_lead_paid ρ c a b hp hc ha hb _ _) _ he hfull
  simpa only [hK] using hfull k

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.chronologicalK_eq_witness
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_early_from_positive
