module

public import RKCert.ReviewedNative.NativeHiddenCarrier
public import RKCert.ReviewedNative.ReversePhysicalPorts
public import RKCert.ReviewedNative.ClockHeadFibers

@[expose] public section

/-! # A same-grade paid clock core lies in the actual physical carrier

The two available reflected traces refund one degree per paid iterate.
When the resulting true endpoint budget is 3+2, every vector in the
iterated core is invisible at both actual reverse measurements. -/
namespace RKResearch.Certified.Graded.Reverse.Thin

open RKResearch Polynomial RKCert.OneEscape RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s p m h j k : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

/-- Generic degree-refund seam shared by the m=7 and m=8 charts.
Neither a carrier dimension nor clock invariance is assumed. -/
theorem paid_clock_core_le_carrier
    (ha : ∀ i l, i≤l → A i l=0) (ho : HasOrder p A b)
    (y0 : reflectedClock A (Fin.last s)=0)
    (d0 : quadraticSeed A b (Fin.last s)=0)
    (one : 1≤j) (jh : j≤h) (shift : k<j)
    (fitBudget : m+h+3≤p)
    (degree : j-k≤4) (portBudget : m+(j-k)+5≤p)
    (momentBudget : 2*(j-k)+4≤p)
    (sites : h+1<(weightedSites (reflectedClock A) (quadraticSeed A b)).card)
    (cover : ∀ v∈zeroAt (annih (treeSpace A m)) (Fin.last s),
      ∃ P : K[X], P.natDegree≤h ∧
        weightedEval (reflectedClock A) (quadraticSeed A b) P=v) :
    core (diag (nodes A)) (zeroSpace A j) k ≤
      Hidden.carrier (nodes A) b (quadraticSeed A b) 0 (Fin.last s) := by
  intro f hf
  let D := diag (nodes A)
  let t := Fin.last s
  have paid (l : ℕ) (hl : l≤k) : (D^l) f∈zeroSpace A j := mem_core.mp hf l hl
  obtain ⟨Q,P,qdeg,pdeg,qfit,pfit⟩ :=
    thin_reverse_traces_same_grade_drop (m:=m) (h:=h) ho one jh fitBudget
      t y0 d0 sites cover (k:=k) (f:=f) (fun l => (D^l) f) paid
      (fun l _ i _ => HeadFiber.clock_power_value _ _ l i)
  have col (i : Fin (s+1)) : A i t=0 := ha i t (Fin.le_last i)
  have supp : SupportsComplement A b m t := supportsComplement_of_cover cover
  have invisible := ordered_thin_invisible_given_reps ha ho y0 col supp Q P (qdeg.trans degree)
    (by omega) (by omega) (by omega) (by omega) qfit pfit
  have f0 : f∈zeroSpace A j := by simpa only [D,pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using paid 0 (Nat.zero_le _)
  exact Hidden.actual_defect_hidden ha ho (by omega) f0
    (fun i=>(invisible i).1) (fun i=>(invisible i).2)

end RKResearch.Certified.Graded.Reverse.Thin
