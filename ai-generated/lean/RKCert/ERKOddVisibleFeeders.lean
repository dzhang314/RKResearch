module
public import RKCert.ERKOddContrastSites
public import RKCert.ERKFourHiddenDispatch
public import RKCert.ERKOddHiddenFiller

@[expose] public section
/-! # Four hidden dimensions cannot survive the zero-seed p17 chart -/
namespace RKCert.Paired.ERKOddHidden
open RKCert.Paired.FiniteMidpoint RKCert.Paired.ReverseHull RKCert.Paired.ERKEvenHidden
open RKCert.Paired.Clock RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K} {b:Vec K 26}
noncomputable section

def oddVisible (A:Fin 26→Fin 26→K) (b:Vec K 26) (i:Fin 26):Prop:=
  backSeed2 A b i≠0∨mirror A i*b i≠0

private theorem primitive_X_power_at (x:K)(k:ℕ):
    (primitive (X^k:K[X])).eval x=x^(k+1)/((k+1:ℕ):K):=by
  rw [show (X:K[X])^k=monomial k 1 from by simp [←C_mul_X_pow_eq_monomial],
    primitive_monomial,eval_monomial];ring

set_option maxHeartbeats 2300000 in
/-- Work directly in the compensated hidden domain; its final coordinate
need not be zero because strict chronology makes its A-column zero. -/
theorem odd17_two_visible_feeders (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (S:OddBalanced (s:=25) A b 8)(Z:OddZeroReverse (s:=25) A b 8)
    (incl:zeroSpace A 4≤carrier (nodes A) b (backSeed2 A b) 0 (Fin.last 25)):
    finrank K (zeroSpace A 3)+2≤finrank K (carrier (nodes A) b (backSeed2 A b) 0 (Fin.last 25)):=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let c:=nodes A
  let d:=backSeed2 A b
  let t:=Fin.last 25
  let U:=carrier c b d 0 t
  let G:=blindRows c b d 0 t
  let V:=oddVisible A b
  let B:=activeNonzero c b
  have paid:8≤B.card:=activeNonzero_card_of_treeOrder ho
  let B':=B.erase 1
  have many:1<B'.card:=by have h:=Finset.pred_card_le_card_erase (s:=B) (a:=(1:K));change B.card-1≤B'.card at h;omega
  obtain ⟨a,aa,z,zz,az⟩:=Finset.one_lt_card.mp many
  have chooseNode(a:K)(mem:a∈B'):∃i,V i∧c i≠0∧c i=a:=by
    obtain ⟨a1,ab⟩:=Finset.mem_erase.mp mem
    obtain ⟨_,a0,h⟩:=Finset.mem_filter.mp ab
    have act:∃i:Fin 26,c i=a ∧ b i≠0:=by
      by_contra! no
      apply h
      unfold combinedMass
      exact Finset.sum_eq_zero fun i hi=>no i (Finset.mem_filter.mp hi).2
    obtain ⟨i,e,bi⟩:=act
    have yi:mirror A i≠0:=by change 1-c i≠0;rw [e];exact sub_ne_zero.mpr (Ne.symm a1)
    exact ⟨i,Or.inr (mul_ne_zero yi bi),e ▸ a0,e⟩
  obtain ⟨i0,vi0,ni0,ci0⟩:=chooseNode a aa
  obtain ⟨j0,vj0,nj0,cj0⟩:=chooseNode z zz
  let L:=Finset.univ.filter (fun i:Fin 26=>V i∧c i≠0)
  have lin:L.Nonempty:=⟨i0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,vi0,ni0⟩⟩
  let i:=L.min' lin
  let u:=c i
  have iv:V i∧u≠0:=(Finset.mem_filter.mp (L.min'_mem lin)).2
  let M:=L.filter (fun i=>c i≠u)
  have min:M.Nonempty:=by
    by_cases e:c i0=u
    · refine ⟨j0,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,vj0,nj0⟩,?_⟩⟩
      intro f;exact az (ci0.symm.trans (e.trans (f.symm.trans cj0)))
    · exact ⟨i0,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,vi0,ni0⟩,e⟩⟩
  let j:=M.min' min
  let v:=c j
  have jj:=Finset.mem_filter.mp (M.min'_mem min)
  have jv:V j∧v≠0:=(Finset.mem_filter.mp jj.1).2
  have diff:v≠u:=jj.2
  have ip(k:Fin 26)(before:k < i)(vk:V k):c k=0∨c k=u:=by
    left
    by_contra n
    exact (not_le_of_gt before) (L.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,vk,n⟩))
  have jp(k:Fin 26)(before:k < j)(vk:V k):c k=0∨c k=u:=by
    by_contra! n
    exact (not_le_of_gt before) (M.min'_le _ (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,vk,n.1⟩,n.2⟩))
  let F:U→ₗ[K] K×K:=((LinearMap.proj i).comp ((mat A).comp U.subtype)).prod
    ((LinearMap.proj j).comp ((mat A).comp U.subtype))
  have hide (w:Vec K 26)(hw:w∈U)(k:Fin 26)(vk:V k):w k=0:=by
    rcases vk with d0|b0
    · exact carrier_zero_on_active Z.lastSeed hw d0
    · exact (mul_eq_zero.mp (carrier_mirror_weight_zero Z.lastNode hw k)).resolve_left b0
  have root0:c 0=0:=Finset.sum_eq_zero fun k _=>ha 0 k (Fin.zero_le k)
  have realize(R:K[X])(dR:R.natDegree≤3)(R0:R.eval 0=0)(Ru:R.eval u=0):
      ∃w:U,F w=((primitive R).eval u,(primitive R).eval v):=by
    obtain ⟨w,wu,fill⟩:=carrier_filler (c:=c) (d:=d) (o:=0) (t:=t) (f:=evalNodes A R) S.lastLive
    have T (k:Fin 26)(vk:V k)(before:∀l:Fin 26,l < k → V l → c l=0∨c l=u):
        mat A w k=(primitive R).eval (c k):=by
      have e:mat A w k=mat A (evalNodes A R) k:=by
        apply strictlyCausal_mat ha
        intro l hl
        by_cases g:l∈G
        · exact fill l g
        have nt:l≠t:=fun e=>not_lt_of_ge (Fin.le_last k) (show t < k by simpa only [e] using hl)
        have wz:w l=0:=(mem_ambientHidden.mp wu).1 l g nt
        rw [wz,evalNodes_apply]
        by_cases e:l=0
        · rw [e];change 0=R.eval (c 0);rw [root0,R0]
        have vl:V l:=by
          by_contra no
          exact g ((mem_blindRows l).mpr ⟨e,nt,not_ne_iff.mp (fun h=>no (Or.inl h)),
            not_ne_iff.mp (fun h=>no (Or.inr h))⟩)
        rcases before l hl vl with yz|yz
        · change 0=R.eval (c l);rw [yz,R0]
        · change 0=R.eval (c l);rw [yz,Ru]
      rw [e]
      have defect:=primitive_defect A R dR
      exact sub_eq_zero.mp (hide _ (incl defect) _ vk)
    exact ⟨⟨w,wu⟩,Prod.ext (T i iv.1 ip) (T j jv.1 jp)⟩
  let P:K[X]:=X*(X-C u)
  have P2:P=X^2-u•(X:K[X]):=by dsimp [P];rw [smul_eq_C_mul];ring
  have P3:X*P=X^3-u•(X^2:K[X]):=by simp only [P2,smul_eq_C_mul];ring
  have pd:P.natDegree≤2:=natDegree_mul_le.trans (by rw [natDegree_X,natDegree_X_sub_C])
  have xd:(X*P).natDegree≤3:=natDegree_mul_le.trans (by rw [natDegree_X];omega)
  obtain ⟨α,ea⟩:=realize P (by omega) (by simp [P]) (by simp [P])
  obtain ⟨β,eb⟩:=realize (X*P) xd (by simp [P]) (by simp [P])
  have f0(x:K):(primitive P).eval x=x^3/3-u*(x^2/2):=by
    rw [P2,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,primitive_X_power_at,←pow_one (X:K[X]),primitive_X_power_at]
    norm_num
  have f1(x:K):(primitive (X*P)).eval x=x^4/4-u*(x^3/3):=by
    rw [P3,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,primitive_X_power_at,primitive_X_power_at]
    norm_num
  let a:=F α
  let r:=F β
  let Δ:=a.1*r.2-a.2*r.1
  have D:Δ≠0:=by
    have h:Δ=-(u^3*v^2*(v-u)^2)/24:=by
      dsimp only [Δ,a,r]
      rw [ea,eb,f0,f0,f1,f1];ring
    rw [h]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ iv.2)
      (pow_ne_zero _ jv.2)) (pow_ne_zero _ (sub_ne_zero.mpr diff)))) (by norm_num)
  have onto:Function.Surjective F:=by
    rintro ⟨x,y⟩
    refine ⟨((x*r.2-y*r.1)/Δ)•α+((a.1*y-a.2*x)/Δ)•β,?_⟩
    rw [map_add,map_smul,map_smul];apply Prod.ext
    · change (x*r.2-y*r.1)/Δ*a.1+(a.1*y-a.2*x)/Δ*r.1=x
      field_simp [D];dsimp [Δ];ring
    · change (x*r.2-y*r.1)/Δ*a.2+(a.1*y-a.2*x)/Δ*r.2=y
      field_simp [D];dsimp [Δ];ring
  have f3:zeroSpace A 3≤U:=(zeroSpace_mono A (by decide:3≤4)).trans incl
  let J:=Submodule.inclusion f3
  have kills(z:zeroSpace A 3):J z∈F.ker:=by
    change (mat A z.val i,mat A z.val j)=0
    have hin:=incl (mat_zeroSpace_charZero A 3 z.property)
    rw [hide _ hin _ iv.1,hide _ hin _ jv.1];rfl
  have inj:Function.Injective (J.codRestrict F.ker kills):=by
    intro x z e;apply Subtype.ext
    exact congrArg (fun a:F.ker=>a.val.val) e
  have dims:=LinearMap.finrank_le_finrank_of_injective inj
  change finrank K (zeroSpace A 3)≤finrank K F.ker at dims
  have r:=F.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr onto,finrank_top,Module.finrank_prod,Module.finrank_self] at r
  change finrank K (zeroSpace A 3)+2≤finrank K U
  omega
end
end RKCert.Paired.ERKOddHidden
