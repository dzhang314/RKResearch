module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPaidBarycentric
public import RKCert.ReviewedNative.ERK10FixedQ29AdicNonlinearLimit
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open PaidBarycentric Nonlinear Polynomial
open scoped Ring BigOperators Polynomial

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

abbrev Site := Fin 11
abbrev endNode : Site := 0
abbrev oldOrigin : Site := 1
abbrev headA : Site := 2
abbrev headB : Site := 3
abbrev center : Site := 4
abbrev nodeD : Site := 5
abbrev nodeE : Site := 6
abbrev nodeF : Site := 7
abbrev nodeG : Site := 8
abbrev nodeH : Site := 9
abbrev host : Site := 10

def cardSites : Finset Site := Finset.univ.erase host
def ordinary : Finset Site := (Finset.univ.erase endNode).erase oldOrigin
def withoutCenter : Finset Site := ordinary.erase center
def singletonSites : Finset Site := withoutCenter.erase host

def nodal {R : Type*} [CommRing R] (c a b : R) : Site → R :=
  ![0,1,a,b,c,26,eTail c,fTail c,6,hTail c,15]

def nodeResidues : Site → F := ![0,1,11,20,2,26,27,7,6,22,15]
def weightResidues : Site → F := ![2,4,16,1,18,7,1,26,9,4,0]
def muResidues : Site → F := ![0,0,7,6,0,11,21,14,24,9,0]

theorem cardSites_card : cardSites.card = 10 := by decide +kernel
theorem ordinary_card : ordinary.card = 9 := by decide +kernel
theorem withoutCenter_card : withoutCenter.card = 8 := by decide +kernel
theorem singletonSites_card : singletonSites.card = 7 := by decide +kernel

theorem cardSites_insert :
    cardSites = insert endNode (insert oldOrigin (insert center singletonSites)) := by
  decide +kernel

theorem ordinary_insert : ordinary = insert center withoutCenter := by decide +kernel
theorem withoutCenter_insert : withoutCenter = insert host singletonSites := by decide +kernel

section Ring
variable {R : Type*} [CommRing R]

def rawNumer (s : Finset Site) (x : Site → R) (i : Site) (y : R) : R :=
  ∏ j ∈ s.erase i, (y-x j)

def cardinal (s : Finset Site) (x : Site → R) (i : Site) : R :=
  avg (rawNumer s x i)*(Den s x i)⁻¹ʳ

/-- The actual degree-nine cardinal weights, with the terminal zero score. -/
def score (x : Site → R) (i : Site) : R :=
  if i=host then 0 else cardinal cardSites x i

theorem den_mul_cardinal {s : Finset Site} {x : Site → R} {i : Site}
    (h : IsUnit (Den s x i)) :
    Den s x i*cardinal s x i = avg (rawNumer s x i) := by
  rw [cardinal,mul_left_comm,Ring.mul_inverse_cancel _ h,mul_one]

variable (ρ : R →+* F) [IsLocalHom ρ]

theorem map_den (s : Finset Site) (x : Site → R) (i : Site) :
    ρ (Den s x i) = Den s (ρ ∘ x) i := by simp [Den,map_prod]

theorem map_numer (s : Finset Site) (x : Site → R) (i : Site) (y : R) :
    ρ (rawNumer s x i y) = rawNumer s (ρ ∘ x) i (ρ y) := by simp [rawNumer,map_prod]

theorem map_cardinal (s : Finset Site) (x : Site → R) (i : Site) :
    ρ (cardinal s x i) = cardinal s (ρ ∘ x) i := by
  rw [cardinal,cardinal,map_mul,map_ringInverse,map_den]
  rw [map_avg ρ (map_numer ρ s x i)]

theorem map_score (x : Site → R) (i : Site) :
    ρ (score x i) = score (ρ ∘ x) i := by
  unfold score
  split_ifs with hi
  · exact map_zero _
  · exact map_cardinal ρ _ _ _

theorem nodes_reduce (c a b : R) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20) :
    ρ ∘ nodal c a b = nodeResidues := by
  funext i
  fin_cases i <;> simp [nodal,nodeResidues,hc,ha,hb,map_ofNat,
    eTail_residue,fTail_residue,hTail_residue]

end Ring

theorem residue_distinct : ∀ i j : Site, i≠j → nodeResidues i-nodeResidues j≠0 := by
  decide +kernel

theorem paid_residue_sites (s : Finset Site) : Paid s nodeResidues := by
  intro i _ j _ hij
  exact isUnit_iff_ne_zero.mpr (residue_distinct i j hij)

theorem field_weight_cross : ∀ i : Site, i≠host →
    ((avgDen:F)*Den cardSites nodeResidues i)*weightResidues i =
      avgRaw (rawNumer cardSites nodeResidues i) := by
  decide +kernel

theorem field_score (i : Site) : score nodeResidues i = weightResidues i := by
  by_cases hi : i=host
  · subst i
    rw [score,ite_eq_left rfl]
    decide +kernel
  · have hii : i∈cardSites := Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩
    have hDen := den_unit (paid_residue_sites cardSites) hii
    have hD : IsUnit (avgDen:F) := by
      rw [avgDen_two]
      exact isUnit_iff_ne_zero.mpr (by decide +kernel)
    apply (hD.mul hDen).mul_left_cancel
    calc
      _ = (avgDen:F)*(Den cardSites nodeResidues i*cardinal cardSites nodeResidues i) := by
        rw [score,ite_eq_right hi,mul_assoc]
      _ = avgRaw (rawNumer cardSites nodeResidues i) := by
        rw [den_mul_cardinal hDen,paidAvg hD]
      _ = _ := (field_weight_cross i hi).symm

theorem field_weights_nonzero : ∀ i : Site, i≠host → weightResidues i≠0 := by
  decide +kernel

theorem field_mu_nonzero : ∀ i : Site, i∈singletonSites → muResidues i≠0 := by
  decide +kernel

open RKCert.ReviewedNative.IntegerHornerCertificate
theorem fromCoeffs_eval {R : Type*} [CommRing R] (as : List R) (x : R) :
    (fromCoeffs as).eval x = horner as x := by
  induction as with
  | nil => simp [fromCoeffs,horner]
  | cons a as ih => simp [fromCoeffs,horner,ih]

theorem field_mu_values : ∀ i : Site, i∈singletonSites →
    horner ([16,16,7,22,7,10,22]:List F) (nodeResidues i)=muResidues i := by
  decide +kernel

section Actual
variable {R : Type*} [CommRing R] (ρ : R →+* F) [IsLocalHom ρ]
variable (c a b : R) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hc ha hb

theorem actual_paid_sites (s : Finset Site) : Paid s (nodal c a b) := by
  intro i _ j _ hij
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  have h {i : Site} : ρ (nodal c a b i)=nodeResidues i :=
    congrFun (nodes_reduce ρ c a b hc ha hb) i
  rw [map_sub,h,h]
  exact residue_distinct i j hij

theorem actual_weight_residue (i : Site) :
    ρ (score (nodal c a b) i) = weightResidues i := by
  rw [map_score,nodes_reduce ρ c a b hc ha hb,field_score]

theorem actual_weights_unit {i : Site} (hi : i≠host) : IsUnit (score (nodal c a b) i) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [actual_weight_residue ρ c a b hc ha hb]
  exact field_weights_nonzero i hi

theorem actual_mu_residue (hp : (decic R).eval c=0) {i : Site} (hi : i∈singletonSites) :
    ρ ((actualMu c).eval (nodal c a b i)) = muResidues i := by
  have hxi : ρ (nodal c a b i)=nodeResidues i := congrFun (nodes_reduce ρ c a b hc ha hb) i
  rw [←eval_map_apply,ResiduePivot.mapMu ρ c hp hc,hxi,ResiduePivot.muMod,fromCoeffs_eval]
  exact field_mu_values i hi

theorem actual_mu_unit (hp : (decic R).eval c=0) {i : Site} (hi : i∈singletonSites) :
    IsUnit ((actualMu c).eval (nodal c a b i)) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [actual_mu_residue ρ c a b hc ha hb hp hi]
  exact field_mu_nonzero i hi

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_weight_residue
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_weights_unit
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_mu_unit
