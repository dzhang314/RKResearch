module
public import RKCert.ERKEvenBalancedHorizon
public import RKCert.ERKEvenHiddenCompletion
public import RKCert.ERKEvenInvariantCap
public import RKCert.ERKThinReverseInvisibility

@[expose] public section
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.ReverseHull RKCert.Paired.ERKEvenHidden RKCert.Endpoint
open Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s q:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

structure EvenHiddenChart (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) (q:ℕ) : Prop where
  balanced : EvenBalanced A b q
  horizon : EvenThinHorizon A b q
  midBand : annih (treeSpace A q)=orbitBand (mirror A) (backSeed2 A b) (q-2)
  seedTerminal : backSeed2 A b (Fin.last s)=0
  invisibility : ∀v∈zeroSpace A 4,∀i, backSeed2 A b i*v i=0 ∧ mirror A i*b i*v i=0
  contained : carrier (nodes A) b (backSeed2 A b) 0 (Fin.last s)≤zeroSpace A q
  fifthCap : (blindRows (nodes A) b (backSeed2 A b) 0 (Fin.last s)).card≤5
  actualBasis : ∀i∈blindRows (nodes A) b (backSeed2 A b) 0 (Fin.last s),
    b i=0 ∧ (Pi.single i (1:K):Vec K (s+1))∈zeroSpace A q

set_option maxHeartbeats 1500000 in
theorem balanced_hidden_chart (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q))
    (q9:9≤q) (size:s+1=3*q) : EvenHiddenChart A b q := by
  classical
  let _ : DecidableEq K := Classical.decEq K
  let S:=balanced_even_ranks ha ho q9 size
  let H:=balanced_even_thin_horizon ha ho q9 size S
  let y:=mirror A
  let d:=backSeed2 A b
  let t:=Fin.last s
  have col : ∀k,A k t=0 := fun k=>ha k t (Fin.le_last k)
  have bdim:=H.exactRanks (q-2) (by omega)
  have R:orbitBand y d (q-2)=primitiveBack A b (q-2) := by
    apply Submodule.eq_of_le_of_finrank_le (orbitBand_le_primitiveBack (A:=A) (b:=b) (q-2))
    rw [←bdim.2,bdim.1,orbitBand_rank y d _ (by have h:=H.manySites;change q≤(orbitSites y d).card at h;omega)]
  have eq : annih (treeSpace A q)=orbitBand y d (q-2) :=
    S.reverseMid.symm.trans (bdim.2.trans R.symm)
  have dt:d t=0:=primitiveBack_terminal t S.lastReflect col S.seedZero 1
    (seed2_mem_primitiveBack (A:=A) (b:=b) 0)
  have supp : ∀v∈annih (treeSpace A q),∀i,d i=0→v i=0 := by
    intro v hv i h
    rw [eq] at hv
    obtain ⟨a,rfl⟩:=hv
    change weightedEval y d (ofFn (q-2) a) i=0
    rw [weightedEval_apply,h,mul_zero]
  have ct:nodes A t=1 := (sub_eq_zero.mp S.lastReflect).symm
  have tn:t≠0:=by
    intro e
    have v:=congrArg Fin.val e
    change s=0 at v
    omega
  have inc:=carrier_le_defects_even ha ho le_rfl (by omega) tn ct dt supp
  have ranks:=balanced_invariant_core_cap ha ho (by omega) size S.separated S.forwardMid
    _ inc (carrier_invariant ct)
  rw [carrier_rank S.lastLive] at ranks
  have cover : ∀v∈annih (treeSpace A (q-1))⊓LinearMap.ker (LinearMap.proj t),
      ∃P:K[X],P.natDegree≤q-2 ∧ weightedEval y d P=v := by
    intro v hv
    change v∈annih (treeSpace A (q-1))⊓LinearMap.ker (LinearMap.proj (Fin.last s)) at hv
    rw [H.band] at hv
    obtain ⟨a,rfl⟩:=hv
    refine ⟨ofFn (q-1) a,?_,rfl⟩
    have h:=ofFn_natDegree_lt (by omega : 0<q-1) a
    omega
  have big:q-2+1<(Clock.headSites y d).card := by
    have h:=H.manySites
    change q≤(Clock.headSites y d).card at h
    omega
  have vanish (v:Vec K (s+1)) (hv:v∈zeroSpace A 4) :
      ∀i,d i*v i=0 ∧ y i*b i*v i=0 :=
    ordered_thin_invisible ha ho hv (by decide) (by omega) le_rfl (by omega)
      (by omega) (by omega) t S.lastReflect col dt big cover
  exact ⟨S,H,eq,dt,vanish,inc,ranks,fun _ h=>carrier_basis_of_terminal_zero S.lastLive inc S.forwardTerminalZero h⟩

/-- Every actual fourth-grade defect is in the physical hidden carrier. -/
theorem balanced_four_to_carrier (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q))
    (q9:9≤q) (Z:EvenHiddenChart A b q) :
    zeroSpace A 4≤carrier (nodes A) b (backSeed2 A b) 0 (Fin.last s) := by
  intro v hv
  apply carrier_of_no_visibility (origin_zeroSpace A ha 4 hv)
  · have h:=probe_zeroSpace ho (k:=0) (by omega) hv
    change probe A b 0 v=0 at h
    simpa only [probe,pow_zero,mul_one] using h
  · exact fun i=>(Z.invisibility v hv i).1
  · exact fun i=>(Z.invisibility v hv i).2

end RKCert.Paired.FiniteMidpoint
