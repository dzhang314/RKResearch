module
public import RKCert.ERKOrderedQ7Chart

@[expose] public section

/-! # The genuine order-14 triple-shift leakage removal -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Endpoint RKCert.OneEscape RKCert.Paired.Clock Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 1700000

theorem even_seven_decompose (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) (C:EvenSevenChart A r U w G) {v:Vec K (s+1)}
    (hv:v∈defectPlus A 0 10) (hl:v (Fin.last s)=0) :
    ∃ P:K[X],P.natDegree≤7 ∧ (∃ x y:K,P=x•even4+y•even5) ∧
      v-evalNodes A P∈SevenBand A r U w 10 := by
  classical
  have hE : v∈treePlus A 0 10 := (sup_le_sup (zeroSpace_le_treeSpace A 10) (show tailPlane K s 0≤_ from le_rfl)) hv
  rw [C.chart 10 (by decide) (by decide)] at hE
  obtain ⟨p,⟨c,rfl⟩,z,hz,eq⟩:=Submodule.mem_sup.mp hE
  let P:=ofFn 8 c
  have pd:P.natDegree≤7 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have ev:evalNodes A P=polyEval A 7 c := evalNodes_ofFn A 7 c
  have hPaid : evalNodes A P∈defectPlus A 0 10 := by
    rw [ev,show polyEval A 7 c=v-z by rw [←eq];abel]
    exact Submodule.sub_mem _ hv (even_seven_paid C 2 hz)
  have z0 := even_seven_band_zero ha ho S C 10 hz
  have one := (even_terminal_column_short (q:=7) ha ho (by decide) S).1
  have hP1 : P.eval 1=0 := by
    have h := congrFun eq (Fin.last s)
    rwa [Pi.add_apply,z0,add_zero,hl,←ev,evalNodes_apply,one] at h
  have hP0 := marked_eval_origin ha (by have := S.size;omega) P hPaid
  have e := ghostEven7_decode P pd hP0 hP1 (fun k=>
    marked_moment_zero ho P hPaid (by omega) (by have :=k.isLt;omega))
  exact ⟨P,pd,e,by rw [ev,←eq];simpa only [add_sub_cancel_left] using hz⟩

omit [CharZero K] in
theorem seven_next_polynomial {P:K[X]} (S:Saturated A b 7 0) (M:Margin A b 7 0 0)
    (C:EvenSevenChart A r U w G) (hp:P.natDegree≤8) (hP:evalNodes A P∈SevenBand A r U w 11) :
    ∃ τ:K,P=τ•G := by
  have GL : G.coeff 8≠0 := by
    rw [←C.meshDegree,coeff_natDegree,leadingCoeff_ne_zero]
    intro hz
    have h:=C.meshDegree
    rw [hz,natDegree_zero] at h
    omega
  let τ:=P.coeff 8/G.coeff 8
  let T:=P-τ•G
  have dh:T.natDegree≤7 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    change (P-τ•G).coeff i=0
    rw [coeff_sub,AddMonoidAlgebra.coeff_smul_apply,smul_eq_mul]
    by_cases he:i=8
    · subst i;unfold τ;rw [div_mul_cancel₀ _ GL,sub_self]
    · have P0 := coeff_eq_zero_of_natDegree_lt (p:=P) (n:=i) (by omega)
      have G0 := coeff_eq_zero_of_natDegree_lt (p:=G) (n:=i) (by have := C.meshDegree;omega)
      rw [P0,G0,mul_zero,sub_self]
  have hG := even_seven_first (j:=11) C C.meshPaid
  have ht : evalNodes A T∈SevenBand A r U w 11 := by
    have e:evalNodes A T=evalNodes A P-τ•evalNodes A G := by ext i; simp [T,evalNodes,eval_smul]
    rw [e]
    exact Submodule.sub_mem _ hP (Submodule.smul_mem _ _ hG)
  refine ⟨τ,?_⟩
  exact sub_eq_zero.mp (even_seven_band_sep S M C (by decide) (by decide) T dh ht)

omit [CharZero K] in
theorem even_seven_shift {P Q:K[X]} (S:Saturated A b 7 0) (M:Margin A b 7 0 0)
    (C:EvenSevenChart A r U w G) {v:Vec K (s+1)}
    (pD:P.natDegree≤7) (qD:Q.natDegree≤7)
    (hp:v-evalNodes A P∈SevenBand A r U w 10)
    (hq:diag (nodes A) v-evalNodes A Q∈SevenBand A r U w 10) : ∃ τ:K,X*P-Q=τ•G := by
  let D:=diag (nodes A)
  let B:=SevenBand A r U w 10
  let W:=SevenBand A r U w 11
  have he:B⊔B.map D=W := even_seven_next C (by decide)
  have m1 : D (v-evalNodes A P)∈W := by
    rw [←he]
    exact (show B.map D≤B⊔B.map D from le_sup_right) (Submodule.mem_map_of_mem hp)
  have m2 : D v-evalNodes A Q∈W := by
    rw [←he]
    exact (show B≤B⊔B.map D from le_sup_left) hq
  have hmem := W.sub_mem m2 m1
  rw [map_sub,show D v-evalNodes A Q-(D v-D (evalNodes A P))=
        D (evalNodes A P)-evalNodes A Q by abel] at hmem
  have e : evalNodes A (X*P-Q)=D (evalNodes A P)-evalNodes A Q := by ext i;simp [D,evalNodes]
  apply seven_next_polynomial S M C (diff_clock_degree P Q 7 pD qD)
  rwa [e]

theorem even_seven_leak_free (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) (M:Margin A b 7 0 0) (C:EvenSevenChart A r U w G) {v:Vec K (s+1)}
    (h0:v∈defectPlus A 0 10) (h1:diag (nodes A) v∈defectPlus A 0 10)
    (h2:diag (nodes A) (diag (nodes A) v)∈defectPlus A 0 10) (hl:v (Fin.last s)=0) :
    v∈SevenBand A r U w 10 ∧ diag (nodes A) v∈SevenBand A r U w 10 ∧
      diag (nodes A) (diag (nodes A) v)∈SevenBand A r U w 10 := by
  obtain ⟨P,dP,⟨t0,t1,p⟩,p0⟩:=even_seven_decompose ha ho S C h0 hl
  obtain ⟨Q,dQ,⟨u0,u1,q⟩,q0⟩:=even_seven_decompose ha ho S C h1 (by rw [diag_apply,hl,mul_zero])
  obtain ⟨R,dR,⟨v0,v1,l⟩,r0⟩:=even_seven_decompose ha ho S C h2
    (by rw [diag_apply,diag_apply,hl,mul_zero,mul_zero])
  obtain ⟨t,e0⟩:=even_seven_shift S M C dP dQ p0 q0
  obtain ⟨u,e1⟩:=even_seven_shift S M C dQ dR q0 r0
  obtain ⟨g,ge⟩:=C.mesh
  have e0' : (X:K[X])*(t0•even4+t1•even5)-(u0•even4+u1•even5)=(t*g)•even6 := by
    simpa only [p,q,ge,smul_smul] using e0
  have e1' : (X:K[X])*(u0•even4+u1•even5)-(v0•even4+v1•even5)=(u*g)•even6 := by
    simpa only [q,l,ge,smul_smul] using e1
  obtain ⟨z0,z1⟩:=shiftEven7 t0 t1 u0 u1 v0 v1 (t*g) (u*g) e0' e1'
  have zP : P=0 := by simp [p,z0,z1]
  have reduce (H:K[X]) (vd:H.natDegree≤7) (τ:K) (h:-H=τ•G) : H=0 := by
    by_contra hn
    have v : H.natDegree=G.natDegree := by
      simpa only [natDegree_neg] using mesh_line_degree h (neg_ne_zero.mpr hn)
    rw [C.meshDegree] at v
    omega
  have zQ:=reduce Q dQ t (by simpa only [zP,mul_zero,zero_sub] using e0)
  have zR:=reduce R dR u (by simpa only [zQ,mul_zero,zero_sub] using e1)
  have zz : evalNodes A (0:K[X])=(0:Vec K (s+1)) := by ext i;simp only [evalNodes_apply,eval_zero,Pi.zero_apply]
  exact ⟨by simpa only [zP,zz,sub_zero] using p0,by simpa only [zQ,zz,sub_zero] using q0,
    by simpa only [zR,zz,sub_zero] using r0⟩

end RKCert.Paired.FiniteMidpoint

