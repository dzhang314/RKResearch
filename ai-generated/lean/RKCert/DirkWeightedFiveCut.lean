module

public import RKCert.DirkWeightedFiveHeads

@[expose] public section

/-! # Weighted compatibility and the two actual fifth-debut rank cuts

Compatibility is imposed on every physical row of the prefix and is only
tested through the same one-degree inclusion on both sides. A numerical
clock with a zero-base/nonzero-head row is not skipped.
-/
namespace RKCert.Paired.LocalProjection.WeightedFive
open RKCert.Endpoint RKCert.Paired.Pivot RKCert.FourDebut Module Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}
variable (D : WeightedFive K s)

def amp (i : Fin s) : K := D.head i/D.base i

theorem amp_mul (i : Fin s) (h : D.base i≠0) : D.amp i*D.base i=D.head i :=
  div_mul_cancel₀ _ h

theorem normalize (i : Fin s) (h : D.base i≠0) {x z : K}
    (eqn : x*D.base i=D.head i*z) : x=D.amp i*z := by
  apply mul_right_cancel₀ h
  rwa [mul_right_comm,D.amp_mul _ h]

def compatible (i : Fin s) : Submodule K K[X] where
  carrier := {q | ∃ F : K→K,F 0=0 ∧ ∀ l < i,D.head l*q.eval (D.clock l)=D.base l*F (D.clock l)}
  zero_mem' := ⟨0,rfl,by simp⟩
  add_mem' := by
    rintro p q ⟨f,hf,hp⟩ ⟨g,hg,hq⟩
    refine ⟨f+g,by simp [hf,hg],?_⟩
    intro l hl
    simp only [eval_add,Pi.add_apply,mul_add,hp l hl,hq l hl]
  smul_mem' := by
    rintro a p ⟨f,hf,hp⟩
    refine ⟨a • f,by simp [hf],?_⟩
    intro l hl
    simp only [Polynomial.eval_smul,Pi.smul_apply,smul_eq_mul]
    rw [mul_left_comm,hp l hl,mul_left_comm]

theorem fitted {i : Fin s} {n : ℕ} (ix : Fin n→Fin s) {P q : K[X]}
    (h0 : P.eval 0=0) (hq : q∈D.compatible i) (prior : ∀ k,ix k < i)
    (active : ∀ k,D.base (ix k)≠0)
    (cover : ∀ l < i,D.base l≠0 → D.clock l≠0 → ∃ k,D.clock l=D.clock (ix k))
    (fiteq : ∀ k,P.eval (D.clock (ix k))=D.amp (ix k)*q.eval (D.clock (ix k))) :
    PrefixZero (weightedEval D.clock D.base P-weightedEval D.clock D.head q) i := by
  obtain ⟨F,F0,matchF⟩ := hq
  intro l hl
  rw [Pi.sub_apply,weightedEval_apply,weightedEval_apply,sub_eq_zero,
    mul_comm (q.eval _),matchF l hl,mul_comm (D.base l) (F _)]
  by_cases hb : D.base l=0
  · simp [hb]
  congr 1
  by_cases hc : D.clock l=0
  · simp [hc,h0,F0]
  obtain ⟨k,hk⟩ := cover l hl hb hc
  rw [hk,fiteq k]
  apply mul_right_cancel₀ (active k)
  rw [mul_right_comm,D.amp_mul _ (active k),matchF _ (prior k),mul_comm]

private def atRows {d : ℕ} (c : Vec K s) (ix : Fin d→Fin s) :
    K[X] →ₗ[K] (Fin d→K) := LinearMap.pi (fun j => leval (c (ix j)))

set_option maxHeartbeats 1000000 in
/-- Here t is the number of input-fitting sites and o the number of paid
primitive sites. On the refunded fifth row they are genuinely different. -/
theorem paired_cut [CharZero K] {j d t o : ℕ} {i : Fin s}
    (ix : Fin t→Fin s) (iy : Fin o→Fin s) (hj : 5≤j) (ju : j≤6) (dd : d=j-4)
    (prior : ∀ k,ix k < i) (active : ∀ k,D.base (ix k)≠0)
    (cover : ∀ l < i,D.base l≠0 → D.clock l≠0 → ∃ k,D.clock l=D.clock (ix k))
    (iy_pay : ∀ k,iy k < i ∨ iy k=i ∧ D.pivot i=0)
    (iy_active : ∀ k,D.base (iy k)≠0)
    (used : Fin d→Fin t) (nonzero : ∀ k,D.amp (ix (used k))≠0)
    (distinct : Function.Injective (fun k => D.clock (ix (used k)))) (big : t+2≤j) :
    ∃ P Q : K[X],P≠0 ∧ P.natDegree≤j ∧ P.eval 0=0 ∧ Q.degree<(d:WithBot ℕ) ∧
      (∀ k,P.eval (D.clock (ix k))=D.amp (ix k)*Q.eval (D.clock (ix k))) ∧
      ∀ k,(Paired.primitive P).eval (D.clock (iy k))=0 := by
  classical
  let H := D.compatible i
  let V := degreeLT K j
  let W := H ⊓ degreeLT K d
  let T := H ⊓ degreeLT K (d+1)
  let (n : ℕ) : FiniteDimensional K (degreeLT K n) := Module.Finite.equiv (degreeLTEquiv K n).symm
  let : FiniteDimensional K W := FiniteDimensional.of_injective
    (Submodule.inclusion (show W≤degreeLT K d from inf_le_right)) (Submodule.inclusion_injective _)
  let : FiniteDimensional K T := FiniteDimensional.of_injective
    (Submodule.inclusion (show T≤degreeLT K (d+1) from inf_le_right)) (Submodule.inclusion_injective _)
  let Vx : V→ₗ[K]K[X] := (LinearMap.mulLeft K X).comp V.subtype
  let obs := atRows D.clock ix
  let L := (obs.comp Vx).coprod (-(((diag (D.amp ∘ ix)).comp obs).comp W.subtype))
  let G := (atRows D.clock iy).comp (Paired.primitive.comp Vx)
  let B := ((diag (D.amp ∘ iy)).comp (atRows D.clock iy)).comp T.subtype
  have eqL (f : V) (q : W) (hl : L (f,q)=0) (l : Fin t) :
      (Vx f).eval (D.clock (ix l))=D.amp (ix l)*q.val.eval (D.clock (ix l)) := by
    have e := congrFun hl l
    change (Vx f).eval (D.clock (ix l)) + -(D.amp (ix l)*q.val.eval (D.clock (ix l)))=0 at e
    exact sub_eq_zero.mp (by rwa [sub_eq_add_neg])
  have hd (f : V) : (Vx f).natDegree≤j := by
    change (X*f.val).natDegree≤j
    by_cases z : f.val=0
    · simp [z]
    · rw [Polynomial.natDegree_X_mul z]
      have g := (Polynomial.natDegree_lt_iff_degree_lt z).mpr (Polynomial.mem_degreeLT.mp f.property)
      omega
  have hzero (f : V) : (Vx f).eval 0=0 := by change (X*f.val).eval 0=0; simp
  have resp (f : V) (q : W) (hl : L (f,q)=0) : G f∈LinearMap.range B := by
    have pre := D.fitted ix (hzero f) q.property.1 prior active cover (eqL f q hl)
    have dq : q.val.degree<((j-4:ℕ):WithBot ℕ) := by
      rw [←dd]
      exact Polynomial.mem_degreeLT.mp q.property.2
    obtain ⟨R,degree,he⟩ := D.primitive_pay hj ju (hd f) dq pre
    have ok : R∈D.compatible i := by
      refine ⟨fun x => (formalPrimitive (Vx f)).eval x,formalPrimitive_eval_zero _,?_⟩
      intro l hl
      rw [←he l (Or.inl hl),mul_comm]
    refine ⟨⟨R,ok,Polynomial.mem_degreeLT.mpr (by
      simpa only [show j-3=d+1 by omega] using degree)⟩,?_⟩
    ext l
    change D.amp (iy l)*R.eval (D.clock (iy l)) = (Paired.primitive (Vx f)).eval (D.clock (iy l))
    rw [←formalPrimitive_eq_treePrimitive]
    exact (D.normalize _ (iy_active l) (he _ (iy_pay l))).symm
  have uniq (q : W) (hl : L (0,q)=0) : q=0 := by
    have z (k : Fin d) : q.val.eval (D.clock (ix (used k)))=0 := by
      have h := eqL 0 q hl (used k)
      rw [map_zero,Polynomial.eval_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (nonzero k)
    exact Subtype.ext (Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ
      distinct.injOn (by rw [Finset.card_univ,Fintype.card_fin]; exact mem_degreeLT.mp q.property.2)
      (fun k _ => z k))
  have rank : t+2 ≤ finrank K V := by rw [(degreeLTEquiv K j).finrank_eq,Module.finrank_fin_fun]; exact big
  obtain ⟨f,q,fnz,l0,g0⟩ := paired_kernel L G B rank (degree_charge H d) resp uniq
  have fp : f.val≠0 := fun h => fnz (Subtype.ext h)
  exact ⟨Vx f,q.val,mul_ne_zero X_ne_zero fp,hd f,hzero f,
    Polynomial.mem_degreeLT.mp q.property.2,eqL f q l0,fun l => congrFun g0 l⟩

end
end RKCert.Paired.LocalProjection.WeightedFive
