module
public import RKCert.ERKOrder13MarkedCore
public import RKCert.OrderTwelveCoreRows

@[expose] public section
/-! # Physical prefix feature counting before or after terminal entry -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Paired.OrderTwelve Polynomial Module
variable {K:Type*} [Field K] {s a:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G H:K[X]}
set_option maxHeartbeats 2400000

theorem polyBand_le_six {a:ℕ} (ha:a≤6) : polyBand A a≤pBand A := by
  classical
  rintro u ⟨c,rfl⟩
  let P:=ofFn (a+1) c
  have pd:P.natDegree≤a := Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
  refine ⟨fun i=>P.coeff i.val,?_⟩
  calc
    polyEval A 6 (fun i=>P.coeff i.val)=evalNodes A (ofFn 7 (fun i=>P.coeff i.val)) := (evalNodes_ofFn A 6 _).symm
    _ = evalNodes A P := by
      have e : ofFn 7 (fun i=>P.coeff i.val)=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (n:=7) (p:=P) (by omega)
      rw [e]
    _ = _ := evalNodes_ofFn A a c

theorem marked13_ghost_feature_contradiction [CharZero K]
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 2 U w G)
    (alg:MulClosed U) (dis:∀i,Live U i→w i=0)
    (ghost:w*w-evalNodes A H∈Band13 A a 2 U w 8)
    (gate:∀ Q R:K[X],Q.natDegree≤3→R.natDegree<headLen 6 a 2 8→
      (∀ x∈headFeatures (nodes A) w,x.2≠0 ∧ G.eval x.1=x.2*Q.eval x.1∧
        x.2^2=H.eval x.1+x.2*R.eval x.1)→
      (headFeatures (nodes A) w).card≤13∧(∀ x:K,G.eval x=0→H.eval x=0→x=0)) :
    False := by
  classical
  let c:=nodes A
  have gm : evalNodes A G∈chain (diag c) U w 4 := by
    change evalNodes A G∈chain (diag (nodes A)) U w (2+(6-4))
    rw [←C.marked.edge]
    exact C.meshPaid
  obtain ⟨u,hu,Q,dQ,g⟩:=exists_head_poly gm
  obtain ⟨v,hv,R,dR,h⟩:=exists_head_poly ghost
  have qd:Q.natDegree≤3 := by
    by_cases qn:Q=0
    · simp [qn]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt qn).mpr dQ)
  have rd:R.natDegree<headLen 6 a 2 8 := by
    by_cases rn:R=0
    · simp [rn,headLen]
    · exact (natDegree_lt_iff_degree_lt rn).mpr dR
  have zero (j:Fin (s+1)) (hj:¬Live U j) (z:Vec K (s+1)) (hz:z∈U) : z j=0 := by
    by_contra hn;exact hj ⟨z,hz,hn⟩
  have gEq (i:Fin (s+1)) (hn:¬Live U i) : G.eval (c i)=Q.eval (c i)*w i := by
    have e:=g i
    change G.eval (c i)=u i+Q.eval (c i)*w i at e
    rwa [zero i hn u hu,zero_add] at e
  have hEq (i:Fin (s+1)) (hn:¬Live U i) : (w i)^2=H.eval (c i)+w i*R.eval (c i) := by
    have e:=h i
    change w i*w i-H.eval (c i)=v i+R.eval (c i)*w i at e
    rw [zero i hn v hv,zero_add] at e
    linear_combination e
  obtain ⟨hCnt,roots⟩:=gate Q R qd rd (by
    intro x hx
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    have wn: w i≠0 := (Finset.mem_filter.mp hi).2
    have hn:¬Live U i := fun q=>wn (dis i q)
    exact ⟨wn,by simpa only [mul_comm] using gEq i hn,hEq i hn⟩)
  have oCnt : (offFeatures U c w).card≤1 := by
    apply (Finset.card_le_card (t:=({0}:Finset K)) ?_).trans (by simp)
    intro x hx
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨nu,nw⟩:=(Finset.mem_filter.mp hi).2
    have p0:=gEq i nu
    have q0:=hEq i nu
    rw [nw,mul_zero] at p0
    rw [nw,zero_mul,add_zero] at q0
    have e := roots _ p0 (by simpa only [zero_pow (by decide : 2≠0)] using q0.symm)
    simp [e]
  have hw:=C.width.2
  obtain ⟨hfull,ex⟩:=thirteen_prefix_exact_eleven ha ho S M C
  have e : pBand A⊔Band13 A a 2 U w 11=⊤ := by
    apply le_antisymm le_top
    rw [←hfull,ex]
    exact sup_le_sup (polyBand_le_six hw) le_rfl
  have count := count_by_features U w (headLen 6 a 2 11) C.marked.stable alg dis e
  have ur := C.marked.rank
  change (headFeatures (nodes A) w).card≤13 at hCnt
  change (offFeatures U (nodes A) w).card≤1 at oCnt
  have ss := S.size
  omega

end RKCert.Paired.FiniteMidpoint
