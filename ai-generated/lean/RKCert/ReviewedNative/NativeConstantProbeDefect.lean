module

public import RKCert.ReviewedNative.EndpointCauchy
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # A zero-origin midpoint column with constant physical probes is a defect

All probes are actual b-polynomial dot products. This strengthens the
single-coordinate paid-constant Cauchy test to an arbitrary original tree
column, retaining its defect-space membership. -/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module
open scoped Matrix
noncomputable section
variable {K : Type*} [Field K] {s p q : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b x : Fin (s+1)→K}

theorem defect_of_constant_probe_at_origin_zero
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder p A b) (pay : 2*q+1≤p)
    (hx : x∈treeSpace A q) (origin : x 0=0) {c : K}
    (profile : ∀ i : Fin (q+1),probe A b i.val x=c) :
    x∈zeroSpace A q ∧ c=0 := by
  rw [treeSpace_coeff_sup ho (by omega)] at hx
  obtain ⟨v,⟨a,rfl⟩,f,hf,e⟩ := Submodule.mem_sup.mp hx
  have a0 : a 0=0 := by
    have h := congrFun e 0
    have hf0 : f 0 = 0 := origin_zeroSpace ha q hf
    rw [Pi.add_apply, coeffEval_origin ha, hf0, add_zero, origin] at h
    exact h
  have tests (i : Fin (q+1)) :
      (∑ j : Fin q,a j.succ/((i.val+j.val+2:ℕ):K))=c := by
    have h := congrArg (probe A b i.val) e
    have wz : probe A b i.val f=0 := probe_zeroSpace ho (by have :=i.isLt; omega) hf
    rw [map_add,wz,add_zero,probe_coeffEval ho (by have :=i.isLt; omega),
      Fin.sum_univ_succ,a0,zero_div,zero_add,profile i] at h
    simpa only [Fin.val_succ,Nat.add_assoc] using h
  obtain ⟨tail,cz⟩ := paid_constant_cauchy ho pay (fun j:Fin q=>a j.succ) c tests
  have az : a=0 := funext (Fin.cases a0 (fun j=>congrFun tail j))
  rw [az,map_zero,zero_add] at e
  exact ⟨e ▸ hf,cz⟩

end
end RKResearch.Certified.Graded.Reverse
