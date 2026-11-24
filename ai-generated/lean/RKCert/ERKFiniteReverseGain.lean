module
public import RKCert.ERKFiniteTail
public import RKCert.ERKFiniteReflectedSix

@[expose] public section
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.ReverseHull RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

/-- A reverse gain of two or three paid against the actual marked forward
space. The terminal line is already absent from every tested reverse column. -/
theorem finite_reverse_gain (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (d j r:ℕ) (hr:2≤r) (hr3:r≤3) (hp:6≤p) (hpay:j+2*r+1≤p)
    (htail:d≠0→nodes A (Fin.last s)=1)
    (hC:(treePlus A d (j+1)).map (diag (nodes A))≤treePlus A d (j+1)) :
    finrank K (treePlus A d j)+r≤finrank K (treePlus A d (j+1)) := by
  classical
  let V := treePlus A d (j+1)
  let W := treePlus A d j
  let U := annih V
  let Z := annih W
  let T := revVec (K:=K) (s:=s+1)
  let Ur := U.map T.toLinearMap
  let Zr := Z.map T.toLinearMap
  let y := mirror A
  have hUZ : U≤Z := fun w hw=>mem_annih.mpr (fun v hv=>mem_annih.mp hw v (Eplus_mono A d (by omega) hv))
  have hNZ (w:Vec K (s+1)) (hw:w∈U) : transMat A w∈Z := by
    apply mem_annih.mpr
    intro v hv
    rw [row_flip_mat]
    exact mem_annih.mp hw _ (Eplus_mat ha d j (Submodule.mem_map_of_mem hv))
  have hm : MaskInvariant y U := reflected_mask_annih (maskInvariant_of_diag (fun _ h=>hC (Submodule.mem_map_of_mem h)))
  have hrm : MaskInvariant (T y) Ur := by
    rintro a _ ⟨x,hx,rfl⟩
    exact Submodule.mem_map_of_mem (hm a x hx)
  have hmass (w:Vec K (s+1)) (hw:w∈Ur) : (∑i,w i)=0 := by
    obtain ⟨x,hx,rfl⟩:=hw
    have e := mem_annih.mp hx (1:Vec K (s+1))
      ((show treeSpace A (j+1)≤V from le_sup_left) (stageWeight_mem_space A .leaf (by simp [Tree.order])))
    change (∑i:Fin (s+1),x i.rev)=0
    rw [show (∑i:Fin (s+1),x i.rev)=∑i,x i from Equiv.sum_comp Fin.revPerm x]
    simpa [row_apply] using e
  have rsum (k:ℕ) : (∑i,(T y i)^k*T b i)=∑i,(y i)^k*b i :=
    Equiv.sum_comp Fin.revPerm (fun i=>y i^k*b i)
  have nod : r≤(failedNodes (T y) (T b) Ur (s+1)).card := by
    apply le_trans hr3
    apply three_failed_of_five_moments _ _ _ hrm hmass
    intro k hk h5
    rw [rsum]
    exact mirror_moments_five ho hp k hk h5
  have wc (P:K[X]) : weightedEval (T y) (T b) P=T (weightedEval y b P) := by
    ext i
    simp only [T,revVec_apply,weightedEval_apply]
  have rowtest (P:K[X]) (hP:P.natDegree+1≤2*r) :
      transMat A (weightedEval y b P)-weightedEval y b (formalPrimitive P)∈Z := by
    let v := transMat A (weightedEval y b P)-weightedEval y b (formalPrimitive P)
    have raw : v∈annih (treeSpace A j) := by
      interval_cases r
      · exact reverse_primitive_annih ho j (by omega) P (by omega)
      · exact reverse_primitive_annih_six ho j (by omega) P (by omega)
    have tail : v∈annih (tailPlane K s d) := by
      apply mem_annih.mpr
      by_cases e:d=0
      · intro x hx
        have hx':x=0 := (Submodule.mem_bot K).mp (by simpa [tailPlane,e] using hx)
        rw [hx',map_zero]
      · rw [tailPlane,ite_eq_right e]
        change Submodule.span K {terminal s}≤(row v).ker
        apply (Submodule.span_singleton_le_iff_mem ..).mpr
        change row v (terminal s)=0
        rw [row_terminal]
        have hm0 : y (Fin.last s)=0 := by change 1-nodes A (Fin.last s)=0;rw [htail e,sub_self]
        have h := transMat_vanish ha (Fin.last s) (weightedEval y b P)
          (fun i hi=>False.elim ((not_lt_of_ge (Fin.le_last i)) hi)) (Fin.last s) le_rfl
        change transMat A (weightedEval y b P) (Fin.last s)=0 at h
        have hF :(formalPrimitive P).eval 0=0 := by
          rw [formalPrimitive_eq_treePrimitive,←coeff_zero_eq_eval_zero,primitive_coeff_zero]
        simp only [v,Pi.sub_apply,h,weightedEval_apply,hm0,hF,zero_mul,sub_zero]
    apply mem_annih.mpr
    change W≤(row v).ker
    exact sup_le (mem_annih.mp raw) (mem_annih.mp tail)
  have rank := outgoing_nodal_gain (T y) (T b) Ur Zr (reverseOp A) (reverseOp_strict ha) hrm
    (Submodule.map_mono hUZ) (by
      rintro _ ⟨x,hx,rfl⟩
      rw [show T.toLinearMap x=revVec x from rfl,reverseOp_rev]
      exact Submodule.mem_map_of_mem (hNZ x hx)) r nod (by
        intro P hP
        rw [wc,wc,show T=revVec from rfl,reverseOp_rev,←map_sub]
        exact Submodule.mem_map_of_mem (rowtest P hP))
  rw [←(T.submoduleMap U).finrank_eq,←(T.submoduleMap Z).finrank_eq] at rank
  change finrank K U+r≤finrank K Z at rank
  have a:=RKCert.Paired.OrderTwelve.backward_exact_dim V
  have b:=RKCert.Paired.OrderTwelve.backward_exact_dim W
  change finrank K V+finrank K U=s+1 at a
  change finrank K W+finrank K Z=s+1 at b
  change finrank K W+r≤finrank K V
  omega

end RKCert.Paired.FiniteMidpoint

