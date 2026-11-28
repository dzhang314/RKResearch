module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPairSplit

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical

open PaidBarycentric Nonlinear Polynomial
open scoped Ring BigOperators Polynomial

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 300000

/-- Omit the opening origin ordinate 1 and use two physical center rows
in their actual reverse-causal order. -/
def expand2 {T : Type*} (g : Site→T) (l r : T) : Site→T :=
  ![g endNode,g headA,g headB,l,r,g nodeD,g nodeE,g nodeF,g nodeG,g nodeH,g host]

theorem expand2_map {S T : Type*} (f : S→T) (g : Site→S) (l r : S) :
    f ∘ expand2 g l r = expand2 (f ∘ g) (f l) (f r) := by
  funext i
  fin_cases i <;> rfl

theorem expand2_map₂ {S T U : Type*} (f : S→T→U) (g : Site→S) (h : Site→T)
    (l r : S) (l' r' : T) :
    (fun i => f (expand2 g l r i) (expand2 h l' r' i)) =
      expand2 (fun i => f (g i) (h i)) (f l l') (f r r') := by
  funext i
  fin_cases i <;> rfl

theorem expand2_map₃ {S T U V : Type*} (f : S→T→U→V) (g : Site→S) (h : Site→T) (k : Site→U)
    (l r : S) (l' r' : T) (l'' r'' : U) :
    (fun i => f (expand2 g l r i) (expand2 h l' r' i) (expand2 k l'' r'' i)) =
      expand2 (fun i => f (g i) (h i) (k i)) (f l l' l'') (f r r' r'') := by
  funext i
  fin_cases i <;> rfl

theorem expand2_congr {T : Type*} {g h : Site→T} (l r : T)
    (heq : ∀ i∈insert endNode withoutCenter, g i=h i) :
    expand2 g l r=expand2 h l r := by
  unfold expand2
  rw [heq endNode (by decide +kernel),heq headA (by decide +kernel),heq headB (by decide +kernel),
    heq nodeD (by decide +kernel),heq nodeE (by decide +kernel),heq nodeF (by decide +kernel),
    heq nodeG (by decide +kernel),heq nodeH (by decide +kernel),heq host (by decide +kernel)]

theorem end_notOrdinary : endNode∉ordinary := by decide +kernel
theorem origin_notPhysical : oldOrigin∉insert endNode ordinary := by decide +kernel
theorem center_notWithout : center∉withoutCenter := by decide +kernel

theorem withoutCenter_list :
    withoutCenter = {headA,headB,nodeD,nodeE,nodeF,nodeG,nodeH,host} := by decide +kernel
theorem all_sites_expand : (Finset.univ : Finset Site) = insert oldOrigin (insert endNode ordinary) := by
  decide +kernel
theorem all_sites_card : (Finset.univ : Finset Site) = insert host cardSites := by decide +kernel
theorem host_notCard : host∉cardSites := by decide +kernel
theorem host_zero {R : Type*} [CommRing R] (x : Site→R) : score x host=0 := by simp [score]

theorem sum_expand2 {T : Type*} [AddCommMonoid T] (g : Site→T) (l r : T) :
    ∑ i : Site, expand2 g l r i = g endNode + (∑ i∈withoutCenter, g i) + l + r := by
  rw [withoutCenter_list]
  rw [Finset.sum_insert (by decide +kernel),Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),Finset.sum_singleton]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,expand2,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  ac_rfl

variable {R : Type*} [CommRing R]

def rawY (c a b : R) : Site→R := expand2 (nodal c a b) c c
def rawW (c a b : R) : Site→R :=
  expand2 (score (nodal c a b)) (physicalPair c a b).split.w1 (physicalPair c a b).split.w2
def rawU (c a b : R) : Site→R :=
  let x:=nodal c a b
  expand2 (fun i => if i=endNode then 0 else uAggregate x (actualScale x) i)
    (physicalPair c a b).split.u1 (physicalPair c a b).split.u2
def rawEta (c a b : R) : Site→R :=
  let x:=nodal c a b
  expand2 (fun i => if i=endNode then 0 else etaNoncenter (closureU c) x i)
    (physicalPair c a b).split.eta1 (physicalPair c a b).split.eta2

section Actual
variable (ρ : R →+* F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (haRoot : (headQuadratic c).eval a=0) (hbEq : b=headSum c-a)
include ρ hp hc ha hb haRoot hbEq

/-- Actual physical pointwise contact, including both center rows and the
unscored host. The old-origin row is not one of these eleven rows. -/
theorem raw_contact (i : Site) :
    rawW c a b i*rawEta c a b i=(actualQ c (nodal c a b)).eval (rawY c a b i)*rawU c a b i := by
  let x := nodal c a b
  let S := actualScale x
  let P := physicalPair c a b
  let Z := P.split
  have ⟨_,_,hA,hB,_⟩ := P.split_equations (physicalPair_guards ρ c a b hp hc ha hb)
  have hU := actual_scale_unit ρ c a b hc ha hb
  have hs : (fun j => rawW c a b j*rawEta c a b j) =
      (fun j => (actualQ c x).eval (rawY c a b j)*rawU c a b j) := by
    change (fun j => expand2 (score x) Z.w1 Z.w2 j *
        expand2 (fun j => if j=endNode then 0 else etaNoncenter (closureU c) x j) Z.eta1 Z.eta2 j) =
      (fun j => (actualQ c x).eval (expand2 x c c j) *
        expand2 (fun j => if j=endNode then 0 else uAggregate x S j) Z.u1 Z.u2 j)
    rw [expand2_map₂ (fun w e:R => w*e) (score x) _ Z.w1 Z.w2 Z.eta1 Z.eta2,
      expand2_map₂ (fun z u:R => (actualQ c x).eval z*u) x _ c c Z.u1 Z.u2]
    change expand2 _ (Z.w1*Z.eta1) (Z.w2*Z.eta2) =
      expand2 _ (P.Q*Z.u1) (P.Q*Z.u2)
    rw [hA,hB]
    apply expand2_congr
    intro j hj
    obtain hj | hj := Finset.mem_insert.mp hj
    · subst j
      simp
    · have hj0 : j≠endNode := by
        intro z
        subst j
        exact end_notOrdinary (split_sites _ hj).1
      simp only [ite_eq_right hj0,actualQ,eval_mul,eval_C,uAggregate]
      rw [actual_noncenter_contact ρ c a b hp hc ha hb haRoot hbEq hj]
      unfold normMass
      change (normQuad c).eval (x j)*ordInv x j =
         S⁻¹ʳ*(normQuad c).eval (x j)*(S*ordInv x j)
      calc
        _ = (S*S⁻¹ʳ)*((normQuad c).eval (x j)*ordInv x j) := by
          rw [Ring.mul_inverse_cancel _ hU,one_mul]
        _ = _ := by ring
  exact congrFun hs i

omit haRoot hbEq in
theorem raw_cardinal (p : Polynomial R) (hj : p.natDegree≤9) :
    (∑ i : Site, p.eval (rawY c a b i)*rawW c a b i) + p.eval 1*score (nodal c a b) oldOrigin =
      avgLin p := by
  let _ : Nontrivial R := ρ.domain_nontrivial
  let x := nodal c a b
  let Z := (physicalPair c a b).split
  have ⟨hw,_,_,_,_⟩ := (physicalPair c a b).split_equations (physicalPair_guards ρ c a b hp hc ha hb)
  change Z.w1+Z.w2=score x center at hw
  change (∑ i : Site, p.eval (expand2 x c c i)*expand2 (score x) Z.w1 Z.w2 i)+
      p.eval 1*score x oldOrigin=_
  rw [expand2_map₂ (fun y w:R => p.eval y*w) x (score x) c c Z.w1 Z.w2,sum_expand2]
  have hsplit := congrArg (fun v:R => p.eval c*v) hw
  rw [mul_add] at hsplit
  let g : Site→R := fun j => p.eval (x j)*score x j
  calc
    _ = g oldOrigin+(g endNode+(g center+(∑ j∈withoutCenter, g j))) := by
      change g endNode+(∑ j∈withoutCenter, g j)+p.eval c*Z.w1+p.eval c*Z.w2+g oldOrigin=_
      change p.eval c*Z.w1+p.eval c*Z.w2=g center at hsplit
      linear_combination hsplit
    _ = ∑ j : Site,g j := by
      rw [all_sites_expand,Finset.sum_insert origin_notPhysical,
        Finset.sum_insert end_notOrdinary,ordinary_insert,Finset.sum_insert center_notWithout]
    _ = ∑ j∈cardSites,g j := by
      rw [all_sites_card,Finset.sum_insert host_notCard]
      have hh : g host=0 := by simp [g,host_zero]
      rw [hh,zero_add]
    _ = avgLin p := by
      rw [←cardinal_exact (actual_paid_sites ρ c a b hc ha hb cardSites) p
        (by rw [cardSites_card];omega)]
      apply Finset.sum_congr rfl
      intro j hj
      have ht := Finset.ne_of_mem_erase hj
      simp [g,score,ht,x]

omit haRoot hbEq in
theorem raw_u_marks (j : ℕ) (hj : j≤7) :
    ∑ i : Site, (rawY c a b i)^j*rawU c a b i=0 := by
  let _ : Nontrivial R := ρ.domain_nontrivial
  let x := nodal c a b
  let S := actualScale x
  let z := (physicalPair c a b).split
  have ⟨_,hu,_,_,_⟩ := (physicalPair c a b).split_equations (physicalPair_guards ρ c a b hp hc ha hb)
  change z.u1+z.u2=uAggregate x S center at hu
  change ∑ i : Site, (expand2 x c c i)^j*
    expand2 (fun i => if i=endNode then 0 else uAggregate x S i) z.u1 z.u2 i=0
  rw [expand2_map₂ (fun y u:R => y^j*u) x _ c c z.u1 z.u2,sum_expand2]
  simp only [ite_true,mul_zero,zero_add]
  have hs : (∑ i∈withoutCenter, (x i)^j*
      (if i=endNode then 0 else uAggregate x S i)) =
      ∑ i∈withoutCenter,(x i)^j*uAggregate x S i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hn : i≠endNode := by
      intro zz;subst i;exact end_notOrdinary (split_sites _ hi).1
    rw [ite_eq_right hn]
  rw [hs]
  have H := congrArg (fun v:R => c^j*v) hu
  rw [mul_add] at H
  rw [add_assoc,H,add_comm]
  let g : Site→R := fun i => (x i)^j*uAggregate x S i
  have he : ∑ i∈ordinary, g i = c^j*uAggregate x S center+(∑ i∈withoutCenter,g i) := by
    rw [ordinary_insert,Finset.sum_insert center_notWithout]
    rfl
  rw [←he]
  unfold g
  have hh := low_sum (actual_paid_sites ρ c a b hc ha hb ordinary) (X^j : Polynomial R)
    (by rw [ordinary_card];exact (natDegree_X_pow_le _).trans_lt (by omega))
  simp only [eval_pow,eval_X] at hh
  simp only [uAggregate,ordInv]
  simp_rw [mul_left_comm (_^j) S]
  rw [←Finset.mul_sum,hh,mul_zero]

omit haRoot hbEq in
theorem raw_mixed_eta_u (j : ℕ) (hj : j≤3) :
    ∑ i : Site, (rawY c a b i)^j*(rawEta c a b i*rawU c a b i)=0 := by
  let _ : Nontrivial R := ρ.domain_nontrivial
  let x := nodal c a b
  let S := actualScale x
  let z := (physicalPair c a b).split
  have ⟨_,_,_,_,hz⟩ := (physicalPair c a b).split_equations (physicalPair_guards ρ c a b hp hc ha hb)
  change z.eta1*z.u1+z.eta2*z.u2=splitLambda (closureU c) x S at hz
  change (∑ i : Site, (expand2 x c c i)^j*
     (expand2 (fun i => if i=endNode then 0 else etaNoncenter (closureU c) x i) z.eta1 z.eta2 i*
      expand2 (fun i => if i=endNode then 0 else uAggregate x S i) z.u1 z.u2 i))=0
  rw [expand2_map₃ (fun y e u:R => y^j*(e*u)) x _ _ c c z.eta1 z.eta2 z.u1 z.u2,sum_expand2]
  simp only [ite_true,mul_zero,zero_add]
  have hs : (∑ i∈withoutCenter,(x i)^j*
      ((if i=endNode then 0 else etaNoncenter (closureU c) x i)*
       (if i=endNode then 0 else uAggregate x S i))) =
      ∑ i∈withoutCenter,(x i)^j*(etaNoncenter (closureU c) x i*uAggregate x S i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hn : i≠endNode := by
      intro zz;subst i;exact end_notOrdinary (split_sites _ hi).1
    rw [ite_eq_right hn,ite_eq_right hn]
  have H := congrArg (fun v:R => c^j*v) hz
  rw [mul_add] at H
  rw [hs,add_assoc,H]
  exact completed_u_marks (actual_paid_sites ρ c a b hc ha hb ordinary) _ S (closure_degree c) j hj

/-- All six physical score/dirt marks, using the actual quadratic contact
and the eight true cofactor moments. -/
theorem raw_weighted_eta (j : ℕ) (hj : j≤5) :
    ∑ i : Site, (rawY c a b i)^j*(rawW c a b i*rawEta c a b i)=0 := by
  let S := (actualScale (nodal c a b))⁻¹ʳ
  let A := S*phaseSlope c
  let B := S*(phaseIntercept c-15*phaseSlope c)
  let C0 := -S*15*phaseIntercept c
  have he (y u : R) :
      y^j*((actualQ c (nodal c a b)).eval y*u)=
        A*(y^(j+2)*u)+B*(y^(j+1)*u)+C0*(y^j*u) := by
    simp only [pow_add,actualQ,normQuad,eval_mul,eval_C,eval_sub,eval_X,actualQ1_eval]
    change y^j*(S*((y-15)*(phaseIntercept c+phaseSlope c*y))*u)=_
    dsimp [A,B,C0]
    ring
  simp_rw [raw_contact ρ c a b hp hc ha hb haRoot hbEq,he,Finset.sum_add_distrib,
    ←Finset.mul_sum]
  rw [raw_u_marks ρ c a b hp hc ha hb (j+2) (by omega),
    raw_u_marks ρ c a b hp hc ha hb (j+1) (by omega),
    raw_u_marks ρ c a b hp hc ha hb j (by omega)]
  ring

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.raw_contact
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.raw_cardinal
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.raw_u_marks
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.raw_mixed_eta_u
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.raw_weighted_eta
