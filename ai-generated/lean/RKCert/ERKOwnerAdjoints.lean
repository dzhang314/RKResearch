module
public import RKCert.ERKOwnerCompression
public import RKCert.OrderTwelveReverseRows

@[expose] public section
/-! # Adjoint tests under literal stage class aggregation
If the earlier representative rows agree on `E_q`, all true columns up to
grade `q+1` restrict exactly. Any original reflected primitive that is paid
on a column `v∈E_j` with `j+1≤q` gives the same test on the compressed
column. This does not require the compressed tableau to have the original
order or any projected backward-hull equality.
-/
namespace RKCert.Paired.OwnerCompression
open RKCert.Paired.OrderTwelve Module
variable {K:Type*} [Field K] {s n q j p:ℕ}
variable {A:Fin s→Fin s→K} {b:Vec K s} {e:Fin n→Fin s} {owner:Fin s→Fin n}
set_option maxHeartbeats 1500000

theorem restrict_treeSpace
    (matched:∀v∈treeSpace A q,∀i,v (e (owner i))=v i) (hj:j≤q+1) :
    (treeSpace A j).map (restrictCol e)=treeSpace (compressMat A e (stencil owner)) j := by
  simp only [treeSpace,Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨_,⟨t,ht,rfl⟩,rfl⟩
    exact ⟨t,ht, actual_stage_weights (t:=t) e owner matched (by omega)⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨_,⟨t,ht,rfl⟩,actual_stage_weights e owner matched (by omega)⟩

theorem restrict_treeSpace_rank
    (matched:∀v∈treeSpace A q,∀i,v (e (owner i))=v i) (hj:j≤q) :
    finrank K (treeSpace (compressMat A e (stencil owner)) j)=finrank K (treeSpace A j) := by
  let H:=treeSpace A j
  let R:=restrictCol (K:=K) e
  let F:=R.comp H.subtype
  have h : ∀v∈H,∀i,∑ k,stencil (K:=K) owner i k*v (e k)=v i :=
    stencil_replay e owner (fun _ hv=>matched _ (treeSpace_mono A hj hv))
  have inj : Function.Injective F := by
    intro v w he
    apply Subtype.ext
    exact restrictCol_inj_on h v.property w.property he
  have rr : LinearMap.range F=H.map R := by
    rw [LinearMap.range_comp,Submodule.range_subtype]
  rw [←restrict_treeSpace matched (by omega),←rr]
  exact (LinearEquiv.ofInjective F inj).finrank_eq.symm

theorem restrict_nodes (matched:∀v∈treeSpace A q,∀i,v (e (owner i))=v i) :
    nodes (compressMat A e (stencil owner))=restrictCol e (nodes A) := by
  have eq := actual_stage_weights (A:=A) (t:=.attach .leaf .leaf) e owner matched (by
    change 2≤q+2
    omega)
  ext i
  simpa [stageWeight,mat_apply,nodes] using (congrFun eq i).symm

theorem restrict_mirror (matched:∀v∈treeSpace A q,∀i,v (e (owner i))=v i) :
    mirror (compressMat A e (stencil owner))=restrictCol e (mirror A) := by
  ext i
  simp only [mirror,Pi.sub_apply,Pi.one_apply,restrictCol_apply,restrict_nodes matched]

theorem row_merge_clock
    (matched:∀v∈treeSpace A q,∀i,v (e (owner i))=v i) (hq:1≤q)
    (k:ℕ) {v:Vec K s} (hv:v∈treeSpace A q) :
    row (powerWeight (mirror (compressMat A e (stencil owner))) (weightMerge b owner) k)
      (restrictCol e v)=row (powerWeight (mirror A) b k) v := by
  have nc : nodes A∈treeSpace A q := by
    have h:=stageWeight_mem_space A (.attach .leaf .leaf)
      (by change 2≤q+1;omega)
    convert h using 1
    ext i
    simp [stageWeight,nodes]
  have same : ∀i,mirror A (e (owner i))=mirror A i := by
    intro i
    simp only [mirror,Pi.sub_apply,Pi.one_apply,matched _ nc i]
  have pow_pair {u:ℕ} (y w v:Vec K u) :
      row (powerWeight y w k) v=row w (fun i=>y i^k*v i) := by
    simp only [row_apply,powerWeight]
    apply Finset.sum_congr rfl
    intro _ _
    ring
  rw [pow_pair,pow_pair]
  have h : (fun i=>(mirror (compressMat A e (stencil owner))) i^k*restrictCol e v i)=
      restrictCol e (fun j=>mirror A j^k*v j) := by
    ext i
    simp only [restrict_mirror matched,restrictCol_apply]
  rw [h,merged_output_at,row_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [same i,matched v hv i]

private theorem row_residual_formula [CharZero K] {A:Fin s→Fin s→K}
    (b v:Vec K s) (k:ℕ) :
    row (reverseResidual A b k) v =
      row (powerWeight (mirror A) b k) (mat A v)-
      ((k+1:ℕ):K)⁻¹*row (powerWeight (mirror A) b (k+1)) v := by
  have h : ((k+1:ℕ):K)≠0 := by exact_mod_cast Nat.succ_ne_zero k
  have row_sub (u w:Vec K s) : row (u-w) v=row u v-row w v :=
    congrArg (fun a:Module.Dual K (Vec K s)=>a v) (rowL.map_sub u w)
  have row_smul (t:K) (w:Vec K s) : row (t • w) v=t*row w v :=
    congrArg (fun a:Module.Dual K (Vec K s)=>a v) (rowL.map_smul t w)
  rw [reverseResidual_eq _ _ _ h,reflWeight_power,reflWeight_power,row_sub,row_smul,row_flip_mat]

theorem residual_merge_test [CharZero K]
    (matched:∀v∈treeSpace A q,∀i,v (e (owner i))=v i) (hj:j+1≤q)
    (k:ℕ) {v:Vec K s} (hv:v∈treeSpace A j) :
    row (reverseResidual (compressMat A e (stencil owner)) (weightMerge b owner) k)
      (restrictCol e v)=row (reverseResidual A b k) v := by
  have hi : j≤q := by omega
  have hq : 1≤q := by omega
  have vq:=treeSpace_mono A hi hv
  have av : mat A v∈treeSpace A q :=
    treeSpace_mono A hj (mat_treeSpace A j hv)
  have col:=compress_mat_comm A e _ (stencil_replay e owner matched) v vq
  rw [row_residual_formula,row_residual_formula,col,row_merge_clock matched hq k av,
    row_merge_clock matched hq (k+1) vq]

theorem residual_merge_annih [CharZero K] (ho:HasTreeOrderAtLeast A b p)
    (matched:∀v∈treeSpace A q,∀i,v (e (owner i))=v i)
    {k:ℕ} (hk:k≤3) (hj:j+1≤q) (hp:j+k+2≤p) :
    reverseResidual (compressMat A e (stencil owner)) (weightMerge b owner) k ∈
      annih (treeSpace (compressMat A e (stencil owner)) j) := by
  apply mem_annih.mpr
  intro x hx
  rw [←restrict_treeSpace matched (by omega)] at hx
  obtain ⟨v,hv,rfl⟩:=hx
  rw [residual_merge_test matched hj]
  · exact mem_annih.mp (reverseResidual_mem ho hk hp) _ hv
  · exact hv

end RKCert.Paired.OwnerCompression
