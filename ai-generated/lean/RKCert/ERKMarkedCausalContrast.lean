module
public import RKCert.ERKOrder13MarkedCore
public import RKCert.ERKOrder13MarkedJacobi

@[expose] public section

/-! # Causal polynomial masks with one paid leakage coefficient
A single first-nonzero detector works for any test polynomial. Multiplying
its test by any factor nonzero at the detected clock preserves the physical
chronology. The primitive residual is linear in the test.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Module Polynomial
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w e:Vec K (s+1)} {G P:K[X]}
set_option maxHeartbeats 2800000

omit [CharZero K] in
noncomputable def maskedContrast (A:Fin (s+1)→Fin (s+1)→K) (w e:Vec K (s+1)) (P:K[X]) :
    K[X] →ₗ[K] Vec K (s+1) :=
  weightedEval (nodes A) (evalNodes A P-w-weightedEval (nodes A) e P)

omit [CharZero K] in
theorem contrast_apply (B:K[X]) (i:Fin (s+1)) :
    maskedContrast A w e P B i =
      B.eval (nodes A i)*(P.eval (nodes A i)-w i-P.eval (nodes A i)*e i) := by
  simp only [maskedContrast,weightedEval_apply,Pi.sub_apply,evalNodes_apply]

omit [CharZero K] in
theorem contrast_rewrite (B:K[X]) :
    maskedContrast A w e P B =
      evalNodes A (B*P) -
        (weightedEval (nodes A) w B+weightedEval (nodes A) e (B*P)) := by
  ext i
  simp only [contrast_apply,Pi.sub_apply,Pi.add_apply,evalNodes_apply,weightedEval_apply,eval_mul]
  ring

noncomputable def maskedResponse (A:Fin (s+1)→Fin (s+1)→K) (w e:Vec K (s+1)) (P:K[X]) :
    K[X] →ₗ[K] Vec K (s+1) where
  toFun B := evalNodes A (Paired.primitive (B*P))-mat A (maskedContrast A w e P B)
  map_add' B C := by
    rw [add_mul,map_add,map_add,map_add]
    ext i
    simp only [Pi.add_apply,Pi.sub_apply,evalNodes_apply,eval_add]
    ring
  map_smul' t B := by
    rw [smul_mul_assoc,map_smul,map_smul,map_smul]
    ext i
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,evalNodes_apply,eval_smul,RingHom.id_apply]
    ring

/-- Being a chronological detector is preserved by multiplication by
any additional polynomial nonzero at the detecting clock. -/
def FirstContrast (A:Fin (s+1)→Fin (s+1)→K) (w e:Vec K (s+1))
    (P B:K[X]) (i:Fin (s+1)) : Prop :=
  maskedContrast A w e P B i≠0 ∧∀ j < i,maskedContrast A w e P B j=0

omit [CharZero K] in
theorem FirstContrast.mul {B:K[X]} {i:Fin (s+1)}
    (h:FirstContrast A w e P B i) (L:K[X]) (hl:L.eval (nodes A i)≠0) :
    FirstContrast A w e P (L*B) i := by
  have eq (k:Fin (s+1)) :
      maskedContrast A w e P (L*B) k =
        L.eval (nodes A k)*maskedContrast A w e P B k := by
    rw [contrast_apply,eval_mul,contrast_apply,mul_assoc]
  exact ⟨by rw [eq];exact mul_ne_zero hl h.1,fun j hj=>by rw [eq,h.2 j hj,mul_zero]⟩

omit [CharZero K] in
theorem firstContrast_off (C:Chart13 A 1 a r U w G)
    (rep:∀ i,w i≠0→w i=P.eval (nodes A i))
    (dis:∀ i,Live U i→w i=0)
    (ev:∀i,e i=if Live U i then 1 else 0)
    {B:K[X]} {i:Fin (s+1)} (h:FirstContrast A w e P B i) :
    ¬Live U i ∧ w i=0 ∧ G.eval (nodes A i)=0 ∧ (B*P).eval (nodes A i)≠0 := by
  have core0 : ¬Live U i := by
    intro hi
    exact h.1 (by simp [contrast_apply,ev,hi,dis i hi])
  have wi:w i=0 := by
    by_contra wn
    exact h.1 (by simp [contrast_apply,ev,core0,rep i wn])
  have gm:=C.meshPaid
  rw [C.marked.edge] at gm
  obtain ⟨v,hv,Q,_,eq⟩:=exists_head_poly gm
  have vz:v i=0 := by
    by_contra hn
    exact core0 ⟨v,hv,hn⟩
  exact ⟨core0,wi,by simpa only [evalNodes_apply,vz,wi,mul_zero,add_zero] using eq i,
    by simpa only [contrast_apply,ev,ite_eq_right core0,wi,mul_zero,sub_zero,eval_mul] using h.1⟩

omit [CharZero K] in
theorem firstContrast_exists (S:Saturated A b 6 1) (M:Margin A b 6 1 1)
    (C:Chart13 A 1 a r U w G) (he:e∈U)
    (B:K[X]) (pn:P≠0) (bn:B≠0) (pd:(B*P).natDegree≤6)
    (pay:weightedEval (nodes A) w B∈defectPlus A 1 6) :
    ∃i,FirstContrast A w e P B i := by
  classical
  have nn:maskedContrast A w e P B≠0 := by
    intro z
    rw [contrast_rewrite,sub_eq_zero] at z
    have zer:=separated_plus S M (B*P) pd (by
      rw [z]
      exact Submodule.add_mem _ pay
        (Fplus_mono A 1 (by decide) (C.marked.core (weighted_core C.marked _ he))))
    exact mul_ne_zero bn pn zer
  let T:=Finset.univ.filter (fun i=>maskedContrast A w e P B i≠0)
  have ne:T.Nonempty := by
    by_contra h
    apply nn
    ext i
    change maskedContrast A w e P B i=0
    by_contra hn
    exact h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩
  refine ⟨T.min' ne,(Finset.mem_filter.mp (T.min'_mem ne)).2,?_⟩
  intro j hj
  by_contra hn
  exact (not_le_of_gt hj) (T.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))

theorem markedResponse_paid (ha:StrictLower A) (C:Chart13 A 1 a r U w G) (he:e∈U)
    {j:ℕ} (hj:5≤j) (B:K[X]) (hd:(B*P).natDegree≤j)
    (pay:weightedEval (nodes A) w B∈defectPlus A 1 j) :
    maskedResponse A w e P B∈defectPlus A 1 (j+1) := by
  let W:=weightedEval (nodes A) w B+weightedEval (nodes A) e (B*P)
  have wp:W∈defectPlus A 1 j :=
    Submodule.add_mem _ pay (Fplus_mono A 1 hj (C.marked.core (weighted_core C.marked _ he)))
  have x:=primitive_defect A _ hd
  have y:=Fplus_mat ha 1 j ⟨W,wp,rfl⟩
  change evalNodes A (Paired.primitive (B*P))-mat A (maskedContrast A w e P B)∈_
  rw [contrast_rewrite,map_sub]
  change evalNodes A (Paired.primitive (B*P))-(mat A (evalNodes A (B*P))-mat A W)∈_
  rw [show evalNodes A (Paired.primitive (B*P))-(mat A (evalNodes A (B*P))-mat A W)=
    -(mat A (evalNodes A (B*P))-evalNodes A (Paired.primitive (B*P)))+mat A W by abel]
  exact Submodule.add_mem _ (Submodule.neg_mem _ ((show zeroSpace A (j+1)≤defectPlus A 1 (j+1) from le_sup_left) x)) y

omit [CharZero K] in
theorem markedResponse_at_first (ha:StrictLower A) {B:K[X]} {i:Fin (s+1)}
    (h:FirstContrast A w e P B i) :
    maskedResponse A w e P B i=(Paired.primitive (B*P)).eval (nodes A i) := by
  have z:=strictlyCausal_mat ha i (maskedContrast A w e P B) 0
    (fun j hj=>by simpa only [Pi.zero_apply] using h.2 j hj)
  change (Paired.primitive (B*P)).eval (nodes A i)-mat A (maskedContrast A w e P B) i=_
  simp only [z,map_zero,Pi.zero_apply,sub_zero]

omit [CharZero K] in
theorem marked13_off_chain_zero {v:Vec K (s+1)} {n:ℕ}
    (hv:v∈chain (diag (nodes A)) U w n) {i:Fin (s+1)} (off:¬Live U i) (wi:w i=0) :
    v i=0 := by
  obtain ⟨x,hx,Q,_,eq⟩:=exists_head_poly hv
  have xi:x i=0 := by
    by_contra hn
    exact off ⟨x,hx,hn⟩
  simpa only [xi,wi,mul_zero,add_zero] using eq i

omit [CharZero K] in
theorem marked13_off_six (C:Chart13 A 1 a r U w G) {v:Vec K (s+1)}
    (hv:v∈defectPlus A 1 6) {i:Fin (s+1)} (off:¬Live U i) (wi:w i=0) :
    v i=0 := by
  rw [C.marked.paid 6 (by decide) le_rfl] at hv
  exact marked13_off_chain_zero hv off wi

theorem marked13_seven_line (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 6 r U w G)
    {v:Vec K (s+1)} (hv:v∈defectPlus A 1 7) :
    ∃ t:K,v-evalNodes A (t•(X*(RKCert.OrderTwelve.dFivePoly:K[X])))∈Band13 A 6 r U w 7 := by
  classical
  have ht:v∈treePlus A 1 7 := (sup_le_sup (zeroSpace_le_treeSpace A 7) le_rfl) hv
  rw [C.chart 7 (by decide) (by decide)] at ht
  obtain ⟨p,⟨c,rfl⟩,z,hz,eq⟩:=Submodule.mem_sup.mp ht
  let Q:=ofFn 7 c
  have qd:Q.natDegree≤6 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have ev:evalNodes A Q=polyEval A 6 c:=evalNodes_ofFn A 6 c
  have hp:evalNodes A Q∈defectPlus A 1 7 := by
    rw [ev,show polyEval A 6 c=v-z by rw [←eq];abel]
    exact Submodule.sub_mem _ hv (band13_paid C (by decide) hz)
  have o:=marked_eval_origin ha (by have:=S.size;omega) Q hp
  obtain ⟨t,u,f⟩:=mesh13Prefix_decode Q (by omega) o (fun k=>marked_moment_difference ho Q hp
    (by omega) M.atOne (by have:=k.isLt;omega))
  have u0:u=0 := by
    by_contra un
    have l:=natDegree_smul_le t (dx5:K[X])
    have d:=natDegree_smul (dx6:K[X]) un
    rw [dx5_degree] at l
    rw [dx6_degree] at d
    rw [f,natDegree_add_eq_right_of_natDegree_lt (by omega),d] at qd
    omega
  rw [u0,zero_smul,add_zero,dx5_mark_factor,smul_smul] at f
  refine ⟨t*42,?_⟩
  rw [←f,ev,←eq]
  simpa only [add_sub_cancel_left] using hz

theorem marked13_off_seven_line (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 6 r U w G)
    {v:Vec K (s+1)} (hv:v∈defectPlus A 1 7) :
    ∃t:K,∀i,¬Live U i→w i=0→v i=t*(nodes A i)*
      (RKCert.OrderTwelve.dFivePoly:K[X]).eval (nodes A i) := by
  obtain ⟨t,ht⟩:=marked13_seven_line ha ho S M C hv
  refine ⟨t,fun i off wi=>?_⟩
  have h:=marked13_off_chain_zero ht off wi
  change v i-(t•(X*(RKCert.OrderTwelve.dFivePoly:K[X]))).eval (nodes A i)=0 at h
  rw [eval_smul,smul_eq_mul,eval_mul,eval_X,←mul_assoc] at h
  exact sub_eq_zero.mp h

end RKCert.Paired.FiniteMidpoint
