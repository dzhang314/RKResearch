module
public import RKCert.DirkWeightedFourHeads
@[expose] public section
namespace RKCert.Paired.LocalProjection.WeightedFour
open RKCert.Endpoint Polynomial RKCert.OneEscape RKCert.Paired.Clock RKCert.FourDebut Module
open scoped Classical
variable {K:Type*} [Field K] {s:ℕ}
noncomputable section
variable (D:WeightedFour K s)

/-- Only active observed rows use this scalar. All compatibility tests below
still include every physical coordinate, including zero-weight knots. -/
def amp (i:Fin s):K:=D.head i/D.base i

theorem amp_mul (i:Fin s) (h:D.base i≠0) : D.amp i*D.base i=D.head i:=div_mul_cancel₀ _ h

theorem normalize (i:Fin s) (h:D.base i≠0) {x z:K} (eqn:x*D.base i=D.head i*z) : x=D.amp i*z := by
  apply mul_right_cancel₀ h
  rwa [mul_right_comm,D.amp_mul _ h]

def compatible (i:Fin s):Submodule K K[X] where
  carrier:={q | ∃F:K→K,F 0=0 ∧ ∀l,i < l → D.head l*q.eval (D.clock l)=D.base l*F (D.clock l)}
  zero_mem':=⟨0,rfl,by simp⟩
  add_mem':=by
    rintro p q ⟨f,hf,hp⟩ ⟨g,hg,hq⟩
    refine ⟨f+g,by simp [hf,hg],?_⟩
    intro l hl
    simp only [eval_add,Pi.add_apply,mul_add,hp l hl,hq l hl]
  smul_mem':=by
    rintro a p ⟨f,hf,hp⟩
    refine ⟨a • f,by simp [hf],?_⟩
    intro l hl
    simp only [Polynomial.eval_smul,Pi.smul_apply,smul_eq_mul]
    rw [mul_left_comm,hp l hl,mul_left_comm]

theorem fitted {i:Fin s} {n:ℕ} (ix:Fin n→Fin s) {P q:K[X]} (h0:P.eval 0=0) (hq:q∈D.compatible i)
    (prior:∀k,i < ix k) (active:∀k,D.base (ix k)≠0)
    (cover:∀l,i < l → D.base l≠0 → D.clock l≠0 → ∃k,D.clock l=D.clock (ix k))
    (fiteq:∀k,P.eval (D.clock (ix k))=D.amp (ix k)*q.eval (D.clock (ix k))) :
    PriorZero (weightedEval D.clock D.base P-weightedEval D.clock D.head q) i := by
  obtain ⟨F,F0,matchF⟩:=hq
  intro l hl
  rw [Pi.sub_apply,weightedEval_apply,weightedEval_apply,sub_eq_zero,mul_comm (q.eval _),matchF l hl,mul_comm (D.base l) (F _)]
  by_cases hb:D.base l=0
  · simp [hb]
  congr 1
  by_cases hc:D.clock l=0
  · simp [hc,h0,F0]
  obtain ⟨k,hk⟩:=cover l hl hb hc
  rw [hk,fiteq k]
  apply mul_right_cancel₀ (active k)
  rw [mul_right_comm,D.amp_mul _ (active k),matchF _ (prior k),mul_comm]

private noncomputable def atRows {d : ℕ} (c : Vec K s) (ix : Fin d→Fin s) :
    Polynomial K →ₗ[K] Vec K d := LinearMap.pi fun i => Polynomial.leval (c (ix i))

set_option maxHeartbeats 1200000 in

theorem paired_cut [CharZero K] {k:ℕ} (hk:k≤2) {i:Fin s} (ix:Fin (k+1)→Fin s)
    (prior:∀l,i < ix l) (active:∀l,D.base (ix l)≠0) (ai:D.base i≠0)
    (cover:∀l,i < l → D.base l≠0 → D.clock l≠0 → ∃t,D.clock l=D.clock (ix t))
    (wi:∀l,D.amp (ix l)≠0) (distinct:Function.Injective (D.clock ∘ ix)) (off:D.pivot i=0) :
    ∃P Q:K[X],P≠0 ∧ P.natDegree≤k+3 ∧ P.eval 0=0 ∧ Q.degree<(k:WithBot ℕ) ∧
      (∀l,P.eval (D.clock (ix l))=D.amp (ix l)*Q.eval (D.clock (ix l))) ∧
      (Paired.primitive P).eval (D.clock i)=0 ∧ ∀l,(Paired.primitive P).eval (D.clock (ix l))=0 := by
  classical
  let H := D.compatible i
  let V := degreeLT K (k+3)
  let W := H ⊓ degreeLT K k
  let T := H ⊓ degreeLT K (k+1)
  let (n : ℕ) : FiniteDimensional K (degreeLT K n) := Module.Finite.equiv (degreeLTEquiv K n).symm
  let : FiniteDimensional K W := FiniteDimensional.of_injective
    (Submodule.inclusion (show W≤degreeLT K k from inf_le_right)) (Submodule.inclusion_injective _)
  let : FiniteDimensional K T := FiniteDimensional.of_injective
    (Submodule.inclusion (show T≤degreeLT K (k+1) from inf_le_right)) (Submodule.inclusion_injective _)
  let Vx : V→ₗ[K]Polynomial K := (LinearMap.mulLeft K Polynomial.X).comp V.subtype
  let obs := atRows (D.clock) ix
  let oldw := (diag (D.amp ∘ ix)).comp obs
  let L := (obs.comp Vx).coprod (-(oldw.comp W.subtype))
  let iy : Fin ((k+1)+1)→Fin s := Fin.cons i ix
  let G := (atRows (D.clock) iy).comp (Paired.primitive.comp Vx)
  let B := ((diag (D.amp ∘ iy)).comp (atRows (D.clock) iy)).comp T.subtype
  have eqL (f : V) (q : W) (hl : L (f,q)=0) (l : Fin (k+1)) :
      (Vx f).eval (D.clock (ix l))=D.amp (ix l)*q.val.eval (D.clock (ix l)) := by
    have e := congrFun hl l
    change (Vx f).eval (D.clock (ix l)) + -(D.amp (ix l)*q.val.eval (D.clock (ix l)))=0 at e
    exact sub_eq_zero.mp (by rwa [sub_eq_add_neg])
  have hd (f : V) : (Vx f).natDegree≤k+3 := by
    change (X*f.val).natDegree≤k+3
    by_cases z : f.val=0
    · simp [z]
    · rw [Polynomial.natDegree_X_mul z]
      have h := (Polynomial.natDegree_lt_iff_degree_lt z).mpr (Polynomial.mem_degreeLT.mp f.property)
      omega
  have hzero (f : V) : (Vx f).eval 0=0 := by change (X*f.val).eval 0=0; simp
  have resp (f : V) (q : W) (hl : L (f,q)=0) : G f∈LinearMap.range B := by
    have pre:=D.fitted ix (hzero f) q.property.1 prior active cover (eqL f q hl)
    have dq:q.val.degree < ((k+3)-3:ℕ):=by simpa using Polynomial.mem_degreeLT.mp q.property.2
    obtain ⟨R,degree,he⟩:=D.primitive_cut (by omega:3≤k+3) (by omega) off (hd f) dq pre
    have ok:R∈D.compatible i:=by
      refine ⟨fun x=>(formalPrimitive (Vx f)).eval x,formalPrimitive_eval_zero _,?_⟩
      intro l hl; rw [←he l hl.le,mul_comm]
    refine ⟨⟨R,ok,Polynomial.mem_degreeLT.mpr (by simpa only [show k+3-2=k+1 by omega] using degree)⟩,?_⟩
    ext t
    change D.amp (iy t)*R.eval (D.clock (iy t)) = (Paired.primitive (Vx f)).eval (D.clock (iy t))
    rw [←formalPrimitive_eq_treePrimitive]
    exact Fin.cases (D.normalize i ai (he i le_rfl)).symm (fun t=>(D.normalize _ (active t) (he _ (prior t).le)).symm) t
  have uniq (q : W) (hl : L (0,q)=0) : q=0 := by
    have z (t : Fin (k+1)) : q.val.eval (D.clock (ix t))=0 := by
      have h := eqL 0 q hl t
      rw [map_zero,Polynomial.eval_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (wi t)
    have hd : q.val.degree < (k:WithBot ℕ) := Polynomial.mem_degreeLT.mp q.property.2
    exact Subtype.ext (Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ distinct.injOn
      (by rw [Finset.card_univ,Fintype.card_fin]; exact hd.trans (by exact_mod_cast Nat.lt_succ_self k)) (fun j _=>z j))
  have big : k+1+2 ≤ finrank K V := by
    rw [(degreeLTEquiv K (k+3)).finrank_eq,Module.finrank_fin_fun]
  have step : finrank K T ≤ finrank K W+1 := RKCert.FourDebut.degree_charge H k
  obtain ⟨f,q,fnz,l0,g0⟩ := RKCert.FourDebut.paired_kernel L G B big step resp uniq
  have fp : f.val≠0 := fun h => fnz (Subtype.ext h)
  have ge (j : Fin ((k+1)+1)) : (Paired.primitive (Vx f)).eval (D.clock (iy j))=0 := congrFun g0 j
  exact ⟨Vx f,q.val,mul_ne_zero X_ne_zero fp,hd f,hzero f,Polynomial.mem_degreeLT.mp q.property.2,
    eqL f q l0,ge 0,fun l=>ge l.succ⟩

theorem bary [CharZero K] {k:ℕ} (hk:k≤2) {i:Fin s} (ix:Fin (k+1)→Fin s)
    (prior:∀l,i < ix l) (active:∀l,D.base (ix l)≠0) (ai:D.base i≠0)
    (cover:∀l,i < l → D.base l≠0 → D.clock l≠0 → ∃t,D.clock l=D.clock (ix t))
    (wi:∀l,D.amp (ix l)≠0) (fresh:∀l,D.clock i≠D.clock (ix l)) (nz:D.clock i≠0)
    (oldnz:∀l,D.clock (ix l)≠0) (distinct:Function.Injective (D.clock ∘ ix)) (off:D.pivot i=0) :
    (∑l,(D.clock (ix l)^2/D.amp (ix l))*(D.clock (ix l)-D.clock i))=0 := by
  obtain ⟨P,Q,Pn,dp,P0,dq,pv,vi,vb⟩:=D.paired_cut hk ix prior active ai cover wi distinct off
  exact RKCert.FourDebut.barycentric_sum (D.clock ∘ ix) (D.amp ∘ ix) (D.clock i) distinct fresh nz oldnz wi Pn dp P0 dq pv vi vb

end
end RKCert.Paired.LocalProjection.WeightedFour
