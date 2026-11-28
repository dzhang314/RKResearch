module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhysicalLayout

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear
open scoped Ring BigOperators

noncomputable section
set_option maxHeartbeats 400000

abbrev Word := Fin 8

variable {R : Type*} [CommRing R]

def headN (c a b y : R) : R :=
  2*b*c*(2*b-c)⁻¹ʳ+2*(-2*a*b+a*c+b*c-c^2)*(a*(2*b-c))⁻¹ʳ*y

def scalarM (c y : R) : R := y^2*(y-c)^2
def scalarL (c y : R) : R := y^3-(3*c*y^2-c^2*y)*(2:R)⁻¹ʳ

def observerZ (c a b y w u : R) : R := w*scalarM c y-(y-c)*headN c a b y*u
def observerG (c a y w u : R) : R :=
  (y-26)*(w*scalarL c y+(2-cOverA c a)*(y-c)*u)

/-- The last two words are deliberately G then Z, so every paid
prefix is a leading principal block of the same matrix. -/
def wordLine (c a b y w u : R) : Word→R :=
  ![w,y*w,y^2*w,y^3*w,u,y*u,observerG c a y w u,observerZ c a b y w u]

def wordInput (c a b : R) : Site→Word→R :=
  fun i => wordLine c a b (rawY c a b i) (rawW c a b i) (rawU c a b i)

def Ymod : Site→F := ![0,11,20,2,2,26,27,7,6,22,15]
def Wmod : Site→F := ![2,16,1,5,13,7,1,26,9,4,0]
def Umod : Site→F := ![0,18,23,26,28,7,11,5,17,9,1]
def EMod : Site→F := ![0,16,6,1,15,2,15,3,8,21,1]

def wordMod : Site→Word→F :=
  ![![2,0,0,0,0,0,0,0],![16,2,22,10,18,24,0,0],![1,20,23,25,23,25,0,0],
    ![5,10,20,11,26,23,0,0],![13,26,23,17,28,27,0,0],![7,8,5,14,7,8,0,0],
    ![1,27,4,21,11,7,12,0],![26,8,27,15,5,6,2,17],![9,25,5,1,17,15,21,25],
    ![4,1,22,20,9,24,19,2],![0,0,0,0,1,15,1,26]]

theorem kernel_word_field :
    ∀ i j, wordLine (2:F) 11 20 (Ymod i) (Wmod i) (Umod i) j = wordMod i j := by
  simp only [wordLine,observerZ,observerG,headN,scalarM,scalarL,cOverA,Ring.inverse_eq_inv]
  decide +kernel

theorem wordLine_map {S : Type*} [CommRing S] (ρ : R→+*S) [IsLocalHom ρ]
    (c a b y w u : R) : ρ ∘ wordLine c a b y w u =
      wordLine (ρ c) (ρ a) (ρ b) (ρ y) (ρ w) (ρ u) := by
  funext j
  fin_cases j <;> simp [wordLine,observerZ,observerG,headN,scalarM,scalarL,cOverA,map_ringInverse,map_ofNat]

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

omit hp in
theorem actual_Y_mod : ρ ∘ rawY c a b=Ymod := by
  rw [rawY,expand2_map,nodes_reduce ρ c a b hc ha hb,hc]
  rfl

theorem actual_W_mod : ρ ∘ rawW c a b=Wmod := by
  have hs : ρ ∘ score (nodal c a b)=weightResidues := by
    funext i
    exact actual_weight_residue ρ c a b hc ha hb i
  have h := physicalSplit_reduce ρ c a b hp hc ha hb
  have h1 : ρ (physicalPair c a b).split.w1=5 := congrArg PairOutput.w1 h
  have h2 : ρ (physicalPair c a b).split.w2=13 := congrArg PairOutput.w2 h
  rw [rawW,expand2_map,hs,h1,h2]
  rfl

theorem actual_U_mod : ρ ∘ rawU c a b=Umod := by
  have h := physicalSplit_reduce ρ c a b hp hc ha hb
  have h1 : ρ (physicalPair c a b).split.u1=26 := congrArg PairOutput.u1 h
  have h2 : ρ (physicalPair c a b).split.u2=28 := congrArg PairOutput.u2 h
  unfold rawU
  dsimp only
  rw [expand2_map,h1,h2]
  change expand2 _ 26 28=expand2 uResidues 26 28
  apply expand2_congr
  intro i hi
  obtain rfl | hi := Finset.mem_insert.mp hi
  · change ρ 0=0
    exact map_zero _
  · have ne0 : i≠endNode := by intro H;subst i;exact end_notOrdinary (split_sites _ hi).1
    simp only [Function.comp_apply,ite_eq_right ne0]
    exact actual_u_residue ρ c a b hc ha hb (split_sites _ hi).1

theorem actual_eta_mod : ρ ∘ rawEta c a b=EMod := by
  have h := physicalSplit_reduce ρ c a b hp hc ha hb
  have h1 : ρ (physicalPair c a b).split.eta1=1 := congrArg PairOutput.eta1 h
  have h2 : ρ (physicalPair c a b).split.eta2=15 := congrArg PairOutput.eta2 h
  unfold rawEta
  dsimp only
  rw [expand2_map,h1,h2]
  change expand2 _ 1 15=expand2 etaResidues 1 15
  apply expand2_congr
  intro i hi
  obtain rfl | hi := Finset.mem_insert.mp hi
  · change ρ 0=0
    exact map_zero _
  · have ne0 : i≠endNode := by intro H;subst i;exact end_notOrdinary (split_sites _ hi).1
    simp only [Function.comp_apply,ite_eq_right ne0]
    exact actual_eta_residue ρ c a b hp hc ha hb hi

theorem actual_word_input_mod (i : Site) (j : Word) :
    ρ (wordInput c a b i j)=wordMod i j := by
  have hY : ρ (rawY c a b i)=Ymod i := congrFun (actual_Y_mod ρ c a b hc ha hb) i
  have hW : ρ (rawW c a b i)=Wmod i := congrFun (actual_W_mod ρ c a b hp hc ha hb) i
  have hU : ρ (rawU c a b i)=Umod i := congrFun (actual_U_mod ρ c a b hp hc ha hb) i
  have h := congrFun (wordLine_map ρ c a b (rawY c a b i) (rawW c a b i) (rawU c a b i)) j
  change ρ (wordInput c a b i j)=_ at h
  rw [hc,ha,hb,hY,hW,hU] at h
  exact h.trans (kernel_word_field i j)

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_word_input_mod
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_eta_mod
