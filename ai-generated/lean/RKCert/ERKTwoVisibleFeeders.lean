module
public import RKCert.ERKEvenCarrierChart

@[expose] public section
/-! # Two paid chronological feeder rows of the actual hidden block -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.ERKEvenHidden RKCert.Endpoint Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s p q:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b d:Vec K (s+1)}

def evenVisible (A:Fin (s+1)→Fin (s+1)→K) (b d:Vec K (s+1)) (i:Fin (s+1)) : Prop :=
  d i≠0∨mirror A i*b i≠0

/-- A nonzero net-weight node away from 1 supplies an actual visible row. -/
theorem two_different_visible_nonzero (ho:HasTreeOrderAtLeast A b p) (pay:6≤p) :
    ∃i j,evenVisible A b d i ∧ evenVisible A b d j ∧
      nodes A i≠0 ∧ nodes A j≠0 ∧ nodes A j≠nodes A i := by
  classical
  let S:=activeNonzero (nodes A) b
  have min:=activeNonzero_card_of_treeOrder ho
  change p/2≤S.card at min
  have act (a:K) (h:a∈S) (n:a≠1) :
      ∃ i,evenVisible A b d i ∧ nodes A i≠0 ∧ nodes A i=a := by
    obtain ⟨_,a0,net⟩:=Finset.mem_filter.mp h
    have hz : ∃ i:Fin (s+1),nodes A i=a ∧ b i≠0 := by
      by_contra! zero
      apply net
      unfold combinedMass
      exact Finset.sum_eq_zero (fun i hi=>zero i (Finset.mem_filter.mp hi).2)
    obtain ⟨i,eq,bi⟩:=hz
    have y0:mirror A i≠0 := by
      change 1-nodes A i≠0
      rw [eq]
      exact sub_ne_zero.mpr (Ne.symm n)
    exact ⟨i,Or.inr (mul_ne_zero y0 bi),(fun z=>a0 (eq.symm.trans z)),eq⟩
  have aS:(S.erase 1).Nonempty := Finset.card_pos.mp
    (by have :=Finset.pred_card_le_card_erase (s:=S) (a:=(1:K));omega)
  obtain ⟨a,ha⟩:=aS
  have eS:((S.erase 1).erase a).Nonempty := Finset.card_pos.mp (by
    have h1:=Finset.pred_card_le_card_erase (s:=S) (a:=(1:K))
    have h2:=Finset.pred_card_le_card_erase (s:=S.erase 1) (a:=a)
    omega)
  obtain ⟨e,he⟩:=eS
  have aa:=Finset.mem_erase.mp ha
  have ee:=Finset.mem_erase.mp he
  have ee':=Finset.mem_erase.mp ee.2
  obtain ⟨i,vi,ni,ci⟩:=act a aa.2 aa.1
  obtain ⟨j,vj,nj,cj⟩:=act e ee'.2 ee'.1
  exact ⟨i,j,vi,vj,ni,nj,by rw [ci,cj];exact ee.1⟩

private theorem primitive_X_pow_value (x:K) (k:ℕ) :
    (primitive (X^k:K[X])).eval x=x^(k+1)/((k+1:ℕ):K) := by
  have H:X^k=monomial k (1:K):=by simp [←C_mul_X_pow_eq_monomial]
  rw [H,primitive_monomial,eval_monomial]
  ring

set_option maxHeartbeats 2400000 in
/-- Independent chronological visible rows consume two dimensions in the
physical hidden-coordinate domain in addition to every genuine F3 vector. -/
theorem hidden_feeder_two_rank (ha:StrictLower A)
    (v4:∀v∈zeroSpace A 4,∀i,evenVisible A b d i→v i=0)
    (F3:zeroSpace A 3≤carrier (nodes A) b d 0 (Fin.last s))
    (bt:b (Fin.last s)≠0)
    (different:∃i j,evenVisible A b d i ∧ evenVisible A b d j ∧
      nodes A i≠0 ∧ nodes A j≠0 ∧ nodes A j≠nodes A i) :
    finrank K (zeroSpace A 3)+2≤(blindRows (nodes A) b d 0 (Fin.last s)).card := by
  classical
  let _ : DecidableEq K := Classical.decEq K
  let c:=nodes A
  let t:=Fin.last s
  let G:=blindRows c b d 0 t
  let V:=evenVisible A b d
  let E:=Finset.univ.filter (fun l:Fin (s+1)=>V l∧c l≠0)
  obtain ⟨k,l,hk,hl,k0,l0,kl⟩:=different
  have e:E.Nonempty:=⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk,k0⟩⟩
  let i:=E.min' e
  have hi:V i∧c i≠0:=(Finset.mem_filter.mp (E.min'_mem e)).2
  let u:=c i
  let L:=E.filter (fun l=>c l≠u)
  have ne:L.Nonempty := by
    by_cases h:c k=u
    · exact ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl,l0⟩,
        fun sq=>kl (sq.trans h.symm)⟩⟩
    · exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk,k0⟩,h⟩⟩
  let j:=L.min' ne
  have hj:=Finset.mem_filter.mp (L.min'_mem ne)
  have jV:V j∧c j≠0:=(Finset.mem_filter.mp hj.1).2
  let v:=c j
  have i_before : ∀ l < i,V l→c l=0 := by
    intro l hl vv
    by_contra h
    exact (not_le_of_gt hl) (E.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,vv,h⟩))
  have j_before : ∀ l < j,V l→c l=0∨c l=u := by
    intro l hl vv
    by_contra! h
    exact (not_le_of_gt hl) (L.min'_le _ (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,vv,h.1⟩,h.2⟩))
  have origin:c 0=0:=by
    change (∑ l,A 0 l)=0
    exact Finset.sum_eq_zero (fun l _=>ha 0 l (Fin.zero_le l))
  let P:K[X]:=X*(X-C u)
  have PP:P=X^2-u•(X:K[X]) := by
    dsimp only [P]
    rw [Polynomial.smul_eq_C_mul]
    ring
  have PQ:X*P=X^3-u•(X^2:K[X]) := by
    rw [PP,Polynomial.smul_eq_C_mul,Polynomial.smul_eq_C_mul]
    ring
  have dP:P.natDegree≤2:=natDegree_mul_le.trans (by rw [natDegree_X,natDegree_X_sub_C])
  have dQ:(X*P).natDegree≤3:=natDegree_mul_le.trans (by rw [natDegree_X];omega)
  let emb : (G→K)→ₗ[K]Vec K (s+1) :=
    LinearMap.pi (fun l=>if h:l∈G then LinearMap.proj (⟨l,h⟩:G) else 0)
  have embAt (x:G→K) (l:Fin (s+1)) :
      emb x l=(if h:l∈G then x ⟨l,h⟩ else 0) := by
    by_cases h:l∈G <;> simp [emb,h]
  let T : (G→K)→ₗ[K](K×K) :=
    ((LinearMap.proj i).comp ((mat A).comp emb)).prod ((LinearMap.proj j).comp ((mat A).comp emb))
  let h (Q:K[X]):G→K:=fun l=>Q.eval (c l.val)
  have atRow (Q:K[X]) (D:Q.natDegree≤3) (z:Fin (s+1)) (vz:V z)
      (pre:∀ l < z,V l→c l=0∨c l=u)
      (r0:Q.eval 0=0) (ru:Q.eval u=0) : mat A (emb (h Q)) z=(primitive Q).eval (c z) := by
    have E : mat A (emb (h Q)) z=mat A (evalNodes A Q) z := by
      apply strictlyCausal_mat ha
      intro l hl
      rw [embAt]
      by_cases hg:l∈G
      · simp [hg,h,c]
      have nt:l≠t:=fun z=>not_lt_of_ge (Fin.le_last _) (z ▸ hl)
      have lv:c l=0∨c l=u := by
        by_cases o:l=0
        · exact Or.inl (o.symm ▸ origin)
        have vv:V l := by
          by_contra bad
          have dd:d l=0:=by by_contra z;exact bad (Or.inl z)
          have bb:mirror A l*b l=0:=by by_contra z;exact bad (Or.inr z)
          exact hg ((mem_blindRows _).mpr ⟨o,nt,dd,bb⟩)
        exact pre l hl vv
      rcases lv with hz|hz <;> simp [hg,evalNodes,show nodes A l=c l from rfl,hz,r0,ru]
    rw [E]
    have paid:mat A (evalNodes A Q)-evalNodes A (primitive Q)∈zeroSpace A 4 :=
      zeroSpace_mono A (by omega) (primitive_defect A Q D)
    have eqv:=v4 _ paid z vz
    exact sub_eq_zero.mp eqv
  have aP (x:K) : (primitive P).eval x=x^3/3-u*(x^2/2) := by
    have px:(primitive (X:K[X])).eval x=x^2/2:=by simpa using primitive_X_pow_value x 1
    rw [PP,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,primitive_X_pow_value,px]
    norm_num
  have aQ (x:K) : (primitive (X*P)).eval x=x^4/4-u*(x^3/3) := by
    rw [PQ,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,
      primitive_X_pow_value,primitive_X_pow_value]
    norm_num
  have pp0:P.eval 0=0:=by simp [P]
  have ppu:P.eval u=0:=by simp [P]
  have ti (Q:K[X]) (D:Q.natDegree≤3) (q0:Q.eval 0=0) (qu:Q.eval u=0) :
      T (h Q)=((primitive Q).eval u,(primitive Q).eval v) :=
    Prod.ext (atRow Q D i hi.1 (fun _ e a=>Or.inl (i_before _ e a)) q0 qu)
      (atRow Q D j jV.1 j_before q0 qu)
  have X0:T (h P)=(u^3/3-u*(u^2/2),v^3/3-u*(v^2/2)) := by
    rw [ti P (by omega) pp0 ppu,aP,aP]
  have X1:T (h (X*P))=(u^4/4-u*(u^3/3),v^4/4-u*(v^3/3)) := by
    rw [ti _ dQ (by simp) (by simp [ppu]),aQ,aQ]
  let a:=T (h P)
  let w:=T (h (X*P))
  let Δ:=a.1*w.2-a.2*w.1
  have D0:Δ≠0 := by
    have cube:Δ=-(u^3*v^2*(v-u)^2)/24 := by
      dsimp only [Δ,a,w]
      rw [X0,X1]
      ring
    rw [cube]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hi.2)
      (pow_ne_zero _ jV.2)) (pow_ne_zero _ (sub_ne_zero.mpr hj.2)))) (by norm_num)
  have surj:Function.Surjective T := by
    rintro ⟨x,y⟩
    refine ⟨((x*w.2-y*w.1)/Δ)•h P+((a.1*y-a.2*x)/Δ)•h (X*P),?_⟩
    rw [map_add,map_smul,map_smul]
    apply Prod.ext
    · change (x*w.2-y*w.1)/Δ*a.1+(a.1*y-a.2*x)/Δ*w.1=x
      field_simp [D0]
      dsimp [Δ];ring
    · change (x*w.2-y*w.1)/Δ*a.2+(a.1*y-a.2*x)/Δ*w.2=y
      field_simp [D0]
      dsimp [Δ];ring
  let F:=zeroSpace A 3
  let J : F→ₗ[K](G→K) := LinearMap.pi (fun j:G=>(LinearMap.proj j.val).comp F.subtype)
  have Jval (x:F) (i:G) : J x i=x.val i.val:=rfl
  have embJ (x:F) : emb (J x)=x.val-x.val t • terminal s := by
    ext z
    rw [embAt]
    change (if h:z∈G then J x ⟨z,h⟩ else 0)=x.val z-x.val t*terminal s z
    by_cases m:z∈G
    · have nt:z≠t:=((mem_blindRows _).mp m).2.1
      rw [dite_eq_left m,Jval,terminal_at_ne nt,mul_zero,sub_zero]
    rw [dite_eq_right m]
    by_cases e:z=t
    · subst z
      rw [terminal_at_last,mul_one,sub_self]
    rw [terminal_at_ne e,mul_zero,sub_zero]
    exact ((mem_ambientHidden.mp (F3 x.property)).1 z m e).symm
  have Jker (x:F) : J x∈T.ker := by
    have D:=mat_zeroSpace_charZero A 3 x.property
    change mat A x.val∈zeroSpace A 4 at D
    have w : mat A (emb (J x))=mat A x.val := by
      rw [embJ,map_sub,map_smul,terminal_mat ha,smul_zero,sub_zero]
    change (mat A (emb (J x)) i,mat A (emb (J x)) j)=0
    rw [w,v4 _ D i hi.1,v4 _ D j jV.1]
    rfl
  let L:=J.codRestrict T.ker Jker
  have inj:Function.Injective L := by
    intro x z eq
    apply Subtype.ext
    have e:J x=J z:=congrArg Subtype.val eq
    have eb: x.val-x.val t • terminal s=z.val-z.val t • terminal s :=
      (embJ x).symm.trans ((congrArg emb e).trans (embJ z))
    have m:=congrArg (row b) eb
    have xm : row b x.val=0:=(mem_ambientHidden.mp (F3 x.property)).2
    have zm : row b z.val=0:=(mem_ambientHidden.mp (F3 z.property)).2
    rw [map_sub,map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul,row_terminal,
      xm,zm,zero_sub,zero_sub,neg_inj] at m
    have qv:=mul_right_cancel₀ bt m
    change x.val t=z.val t at qv
    rw [qv,sub_left_inj] at eb
    exact eb
  have lr:=LinearMap.finrank_le_finrank_of_injective inj
  have rk:=T.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surj,finrank_top,Module.finrank_prod,Module.finrank_self,
    Module.finrank_fintype_fun_eq_card,Fintype.card_coe] at rk
  change finrank K F≤finrank K T.ker at lr
  change finrank K F+2≤G.card
  omega

end RKCert.Paired.FiniteMidpoint
