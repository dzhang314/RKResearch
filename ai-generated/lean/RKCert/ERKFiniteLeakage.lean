module
public import RKCert.ERKFiniteGhost

@[expose] public section

/-! # The physical triple-overlap removes all degree-ten leakage -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s q ε d a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}

omit [CharZero K] in
theorem chart_band_next (C:Chart A q ε d a r U w G) {j:ℕ} (hj:a+1≤j) :
    forwardBand A q a r U w j ⊔ (forwardBand A q a r U w j).map (diag (nodes A))=
      forwardBand A q a r U w (j+1) := by
  have hlen:headLen q a r (j+1)=headLen q a r j+1 := by unfold headLen;omega
  unfold forwardBand
  rw [hlen]
  exact chain_sup_map C.marked.stable (by unfold headLen;have:=C.marked.rTwo;omega)

omit [CharZero K] in
theorem chart_band_first (C:Chart A q ε d a r U w G) {j:ℕ} (_hj:a+1≤j) :
    firstEscape A d q≤forwardBand A q a r U w j := by
  rw [C.marked.edge]
  unfold forwardBand headLen
  have old := (chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) (r+(q-4)+(j-(a+1)))).mp le_rfl
  exact (chain_le_iff _).mpr ⟨old.1,fun k hk=>old.2 k (by omega)⟩

omit [CharZero K] in
theorem chain_eval_zero {c:Vec K (s+1)} (i:Fin (s+1))
    (hU:∀v∈U,v i=0) (hw:w i=0) {n:ℕ} {v:Vec K (s+1)}
    (hv:v∈chain (diag c) U w n) : v i=0 := by
  let V : Submodule K (Vec K (s+1)) := LinearMap.ker (LinearMap.proj i)
  have h : chain (diag c) U w n≤V := by
    apply (chain_le_iff _).mpr
    refine ⟨hU,?_⟩
    intro k hk
    change (diag c^k) w i=0
    rw [pow_diag_apply,hw,mul_zero]
  exact h hv

theorem chart_even_zero (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:8≤q) (S:Saturated A b q ε) (M:Margin A b q ε d) (C:Chart A q ε d a r U w G)
    (he:ε=0) (j:ℕ) {v:Vec K (s+1)} (hb:v∈forwardBand A q a r U w j) :
    v (Fin.last s)=0 := by
  have hd:d=0 := by have:=M.budget;omega
  subst ε;subst d
  have h5 (v:Vec K (s+1)) (hv:v∈defectPlus A 0 5) : v (Fin.last s)=0 :=
    even_last_zero ha (by simpa using ho) hq S _ (zeroSpace_mono A (by omega) (tail_zero_iff.mp hv))
  have hw:w∈defectPlus A 0 5 := by
    have hm := (chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) r).mp le_rfl
    simp only [C.marked.paid 5 (by omega) (by omega),Nat.sub_self,Nat.add_zero]
    simpa using hm.2 0 (by have:=C.marked.rTwo;omega)
  exact chain_eval_zero _ (fun x hx=>h5 x (C.marked.core hx)) (h5 w hw) hb

theorem ghost_decompose (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:q=8∨q=9) (he:ε≤1) (S:Saturated A b q ε) (M:Margin A b q ε d)
    (C:Chart A q ε d a r U w G) {v:Vec K (s+1)}
    (hv:v∈defectPlus A d 10) (hl:ε=0→v (Fin.last s)=0) :
    ∃ P:K[X],P.natDegree≤a∧Ghost P q ε d a∧
      v-evalNodes A P∈forwardBand A q a r U w 10 := by
  classical
  have alo:=C.aLo
  have ale:=C.aLe
  have hE : v∈treePlus A d 10 := (sup_le_sup (zeroSpace_le_treeSpace A 10) (show tailPlane K s d≤_ from le_rfl)) hv
  rw [C.chart 10 (by omega) (by omega)] at hE
  obtain ⟨u,⟨c,rfl⟩,z,hz,eq⟩:=Submodule.mem_sup.mp hE
  let P:=ofFn (a+1) c
  have pd:P.natDegree≤a := Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
  have ev:evalNodes A P=polyEval A a c := evalNodes_ofFn A a c
  have hPd : evalNodes A P∈defectPlus A d (10+(q-a)) := by
    rw [ev,show polyEval A a c=v-z by rw [←eq];abel]
    exact Submodule.sub_mem _ (Fplus_mono A d (by omega) hv) (chart_band_paid C (by omega) hz)
  have hP1 (h:ε=0) : P.eval 1=0 := by
    have z0 := chart_even_zero ha ho (by omega) S M C h _ hz
    have ht: nodes A (Fin.last s)=1 := by
      subst ε
      exact (even_terminal_column ha (by simpa using ho) (by omega) S).1
    have h'e := congrFun eq (Fin.last s)
    rw [Pi.add_apply,z0,add_zero,hl h,←ev,evalNodes_apply,ht] at h'e
    exact h'e
  exact ⟨P,pd,get_ghost ha ho hq he S M C P pd hPd hP1,by rw [ev,←eq];simpa only [add_sub_cancel_left] using hz⟩

omit [CharZero K] in
theorem chart_next_polynomial {P:K[X]} (S:Saturated A b q ε) (M:Margin A b q ε d)
    (C:Chart A q ε d a r U w G) (hj:a+1≤11) (hmax:11≤2*q+ε-3)
    (hp:P.natDegree≤a+1) (hP:evalNodes A P∈forwardBand A q a r U w 11) :
    ∃ τ:K,P=τ•G := by
  have GL : G.coeff (a+1)≠0 := by
    rw [←C.meshDegree,coeff_natDegree,leadingCoeff_ne_zero]
    intro h
    have dg := C.meshDegree
    rw [h,natDegree_zero] at dg
    omega
  let τ := P.coeff (a+1)/G.coeff (a+1)
  let T := P-τ•G
  have dh:T.natDegree≤a := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    change (P-τ•G).coeff i=0
    rw [coeff_sub,AddMonoidAlgebra.coeff_smul_apply,smul_eq_mul]
    by_cases h:i=a+1
    · subst i
      unfold τ
      rw [div_mul_cancel₀ _ GL,sub_self]
    · have P0 := coeff_eq_zero_of_natDegree_lt (p:=P) (n:=i) (by omega)
      have G0 := coeff_eq_zero_of_natDegree_lt (p:=G) (n:=i) (by have :=C.meshDegree;omega)
      rw [P0,G0,mul_zero,sub_self]
  have hG := chart_band_first C hj C.meshPaid
  have ht : evalNodes A T∈forwardBand A q a r U w 11 := by
    have e:evalNodes A T=evalNodes A P-τ•evalNodes A G := by ext i; simp [T,evalNodes,eval_smul]
    rw [e]
    exact Submodule.sub_mem _ hP (Submodule.smul_mem _ _ hG)
  refine ⟨τ,?_⟩
  exact sub_eq_zero.mp (chart_band_sep S M C hj hmax T dh ht)

omit [CharZero K] in
theorem ghost_shift {P Q:K[X]} (S:Saturated A b q ε) (M:Margin A b q ε d)
    (C:Chart A q ε d a r U w G) (hj:a+1≤10) (hmax:11≤2*q+ε-3)
    {v:Vec K (s+1)} (dp:P.natDegree≤a) (dq:Q.natDegree≤a)
    (hp:v-evalNodes A P∈forwardBand A q a r U w 10)
    (hq:diag (nodes A) v-evalNodes A Q∈forwardBand A q a r U w 10) :
    ∃ τ:K,X*P-Q=τ•G := by
  let D:=diag (nodes A)
  let B:=forwardBand A q a r U w 10
  let W:=forwardBand A q a r U w 11
  have he:B⊔B.map D=W := chart_band_next C hj
  have m1 : D (v-evalNodes A P)∈W := by
    rw [←he]
    exact (show B.map D≤B⊔B.map D from le_sup_right) (Submodule.mem_map_of_mem hp)
  have m2 : D v-evalNodes A Q∈W := by
    rw [←he]
    exact (show B≤B⊔B.map D from le_sup_left) hq
  have hmem := W.sub_mem m2 m1
  rw [map_sub,show D v-evalNodes A Q-(D v-D (evalNodes A P))=
        D (evalNodes A P)-evalNodes A Q by abel] at hmem
  have e : evalNodes A (X*P-Q)=D (evalNodes A P)-evalNodes A Q := by ext i; simp [D,evalNodes]
  apply chart_next_polynomial S M C (by omega) hmax (diff_clock_degree P Q a dp dq)
  rw [e]
  exact hmem

omit [CharZero K] in
theorem Mesh.smul (h:Mesh G q ε d) (τ:K) : Mesh (τ•G) q ε d := by
  cases h with
  | even8 t h => exact .even8 (τ*t) (by rw [h,smul_smul])
  | even9 t h => exact .even9 (τ*t) (by rw [h,smul_smul])
  | full8 t h => exact .full8 (τ*t) (by rw [h,smul_smul])
  | full9 t h => exact .full9 (τ*t) (by rw [h,smul_smul])
  | prefix8 t u h => exact .prefix8 (τ*t) (τ*u) (by rw [h,smul_add,smul_smul,smul_smul])
  | prefix9 t u h => exact .prefix9 (τ*t) (τ*u) (by rw [h,smul_add,smul_smul,smul_smul])

theorem leak_free (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:q=8∨q=9) (he:ε≤1) (S:Saturated A b q ε) (M:Margin A b q ε d)
    (C:Chart A q ε d a r U w G) {v:Vec K (s+1)}
    (h0:v∈defectPlus A d 10) (h1:diag (nodes A) v∈defectPlus A d 10)
    (h2:diag (nodes A) (diag (nodes A) v)∈defectPlus A d 10)
    (hL:ε=0→v (Fin.last s)=0) :
    v∈forwardBand A q a r U w 10 ∧ diag (nodes A) v∈forwardBand A q a r U w 10 ∧
      diag (nodes A) (diag (nodes A) v)∈forwardBand A q a r U w 10 := by
  have aLe:=C.aLe
  obtain ⟨P,dP,gP,p0⟩:=ghost_decompose ha ho hq he S M C h0 hL
  obtain ⟨Q,dQ,gQ,q0⟩:=ghost_decompose ha ho hq he S M C h1
    (fun h=>by rw [diag_apply,hL h,mul_zero])
  obtain ⟨R,dR,gR,r0⟩:=ghost_decompose ha ho hq he S M C h2
    (fun h=>by rw [diag_apply,diag_apply,hL h,mul_zero,mul_zero])
  obtain ⟨t,e0⟩:=ghost_shift S M C (by omega) (by omega) dP dQ p0 q0
  obtain ⟨u,e1⟩:=ghost_shift S M C (by omega) (by omega) dQ dR q0 r0
  have m0 : Mesh (X*P-Q) q ε d := by rw [e0]; exact C.mesh.smul t
  have m1 : Mesh (X*Q-R) q ε d := by rw [e1]; exact C.mesh.smul u
  have zP:=ghost_cancel gP gQ gR dP dQ dR m0 m1
  have reduce (V:K[X]) (vdeg:V.natDegree≤a) (τ:K) (h:-V=τ•G) : V=0 := by
    by_contra hv
    have nz : -V≠0 := neg_ne_zero.mpr hv
    have dd:V.natDegree=G.natDegree := by
      simpa only [natDegree_neg] using mesh_line_degree h nz
    rw [C.meshDegree] at dd
    omega
  have zQ:=reduce Q dQ t (by simpa only [zP,mul_zero,zero_sub] using e0)
  have zR:=reduce R dR u (by simpa only [zQ,mul_zero,zero_sub] using e1)
  have zz : evalNodes A (0:K[X])=(0:Vec K (s+1)) := by ext i;simp only [evalNodes_apply,eval_zero,Pi.zero_apply]
  exact ⟨by simpa only [zP,zz,sub_zero] using p0,by simpa only [zQ,zz,sub_zero] using q0,
    by simpa only [zR,zz,sub_zero] using r0⟩

end RKCert.Paired.FiniteMidpoint

