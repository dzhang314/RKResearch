module
public import RKCert.ERKPrimitiveReverseFlag

@[expose] public section
namespace RKCert.Paired.ReverseHull
open RKCert.Paired RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ}
variable {A:Fin s→Fin s→K} {b:Vec K s}

/-- The outgoing companion of the incoming arbitrary-r physical Hermite
bound. It needs invariance only on the lower, original reverse space. -/
theorem outgoing_actual_paid (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    {r:ℕ} (pay:2*r≤p) (U W:Submodule K (Vec K s))
    (inc:U≤W) (hm:MaskInvariant (mirror A) U)
    (mass:∀v∈U,∑i,v i=0) (advance:U.map (transMat A)≤W)
    (prim:∀P:K[X],P.natDegree+1≤2*r → reflectedError A b P∈W) :
    finrank K U+r≤finrank K W := by
  let T:=revVec (K:=K) (s:=s)
  let U':=U.map T.toLinearMap
  let W':=W.map T.toLinearMap
  let y:=mirror A
  have hm':MaskInvariant (T y) U':=by
    rintro a _ ⟨w,hw,rfl⟩
    exact ⟨_,hm a w hw,rfl⟩
  have mass' (w:Vec K s) (hw:w∈U') : (∑i,w i)=0 := by
    obtain ⟨x,hx,rfl⟩:=hw
    change (∑i:Fin s,x i.rev)=0
    rw [show (∑i:Fin s,x i.rev)=∑i,x i from Equiv.sum_comp Fin.revPerm x]
    exact mass x hx
  have wc (P:K[X]):weightedEval (T y) (T b) P=T (weightedEval y b P):=by
    ext i;simp only [T,revVec_apply,weightedEval_apply]
  have fail:r≤(failedNodes (T y) (T b) U' s).card:=by
    apply failed_at_least_of_scalar_budget _ _ _ hm' mass'
    intro P hP
    rw [wc]
    change (∑i:Fin s,weightedEval y b P i.rev)=_
    rw [show (∑i:Fin s,weightedEval y b P i.rev)=∑i,weightedEval y b P i from
      Equiv.sum_comp Fin.revPerm _]
    exact reflected_scalar_budget ho P (by omega)
  have cnt:=outgoing_nodal_gain (T y) (T b) U' W' (reverseOp A)
    (reverseOp_strict ha) hm' (Submodule.map_mono inc) (by
      rintro _ ⟨v,hv,rfl⟩
      rw [show T.toLinearMap v=revVec v from rfl,reverseOp_rev]
      exact Submodule.mem_map_of_mem (advance (Submodule.mem_map_of_mem hv))) r fail (by
      intro P hP
      rw [wc,wc,show T=revVec from rfl,reverseOp_rev,←map_sub]
      exact Submodule.mem_map_of_mem (prim P hP))
  simpa only [U',W',LinearEquiv.finrank_map_eq] using cnt

/-- An invariant augmented reverse grade pays floor((n+2)/2) additional
dimensions at the very next actual grade. -/
theorem primitiveBack_invariant_gain (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (n:ℕ) (pay:n+2≤p)
    (inv:(primitiveBack A b n).map (diag (mirror A))≤primitiveBack A b n) :
    finrank K (primitiveBack A b n)+(n+2)/2≤finrank K (primitiveBack A b (n+1)) := by
  have mass (v:Vec K s) (hv:v∈primitiveBack A b n) : (∑i,v i)=0 := by
    have h:=mem_annih.mp (primitiveBack_annih ho 0 n (by omega) hv) (1:Vec K s)
      (stageWeight_mem_space A .leaf (by decide))
    simpa only [row_apply,Pi.one_apply,mul_one] using h
  exact outgoing_actual_paid ha ho (by omega) (primitiveBack A b n) (primitiveBack A b (n+1))
    (primitiveBack_le_succ n) (fun a _ hv=>Clock.fiber_mem inv a hv)
    mass (primitiveBack_trans n) (fun P hp=>reflectedError_mem_primitiveBack P n (by omega))

end RKCert.Paired.ReverseHull
