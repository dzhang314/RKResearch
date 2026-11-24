module

public import RKCert.ERKOrderNineFiveSixPrefix
public import RKCert.ERKOrderNineFiveOnFiveOff

@[expose] public section

/-! # Tail rows in the five-off/six-on chart

The paid full-stage annihilators already give the required row bases;
there is no nonlinear quotient tableau or rank assumption on a
truncated prefix. Dropping the endpoint is a literal zero-weight row
identity because its node is one in the reflected rows.
-/
namespace RKCert.Paired
open Module Polynomial
open scoped Classical
variable {K : Type*} [Field K]

def withoutLast12 (v : Vec K 12) : Vec K 12 :=
  fun i => if i=(11:Fin 12) then 0 else v i

theorem lowNonterminalState_eq_iff {A : Fin 12 → Fin 12 → K} [CharZero K]
    (ha : StrictLower A) {i j : Fin 12}
    (hi : qdef A i=0 → nodes A i≠1) (hj : qdef A j=0 → nodes A j≠1) :
    lowNonterminalStateAt ha i=lowNonterminalStateAt ha j ↔ lowStateAt A i=lowStateAt A j := by
  by_cases g : qdef A i=0
  · by_cases h : qdef A j=0
    · simp [lowNonterminalStateAt,lowStateAt,g,h,hi g,hj h]
    · simp [lowNonterminalStateAt,lowStateAt,g,h,hi g]
  · by_cases h : qdef A j=0
    · simp [lowNonterminalStateAt,lowStateAt,g,h,hj h]
    · simp [lowNonterminalStateAt,lowStateAt,g,h]

theorem gather_multiply_without_last {A : Fin 12 → Fin 12 → K}
    (rep : Fin 12 → Fin 10)
    (node : ∀ i,i≠(11:Fin 12) → nodes A i=nodes A (lowPrefix10 (rep i)))
    (b : Vec K 12) (f : K → K) :
    gatherRow rep (fun i => withoutLast12 b i*f (nodes A i)) =
      fun i => gatherRow rep (withoutLast12 b) i*f (nodes A (lowPrefix10 i)) := by
  ext i
  simp only [gatherRow_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j=(11:Fin 12)
  · subst j
    simp [withoutLast12]
  · by_cases e : rep j=i <;> simp [e,node j h]

theorem gather_without_last_tagged {A : Fin 12→Fin 12→K}
    (rep : Fin 12→Fin 10)
    (rel : ∀ i j,i≠(11:Fin 12) → j≠(11:Fin 12) →
      (rep i=rep j ↔ lowStateAt A i=lowStateAt A j))
    (repr : ∀ i,rep (lowPrefix10 i)=i)
    (hq : qdef A (11:Fin 12)=0) (hc : nodes A (11:Fin 12)=1)
    (hclean : ∀ i : Fin 10,qdef A (lowPrefix10 i)=0 → nodes A (lowPrefix10 i)≠1)
    (b : Vec K 12) (i : Fin 10) :
    gatherRow rep (withoutLast12 b) i=if qdef A (lowPrefix10 i)=0 then
      onWeight A b (nodes A (lowPrefix10 i)) else offWeight A b (nodes A (lowPrefix10 i)) := by
  have inp : lowPrefix10 i≠(11:Fin 12) := by
    intro e
    have t := congrArg Fin.val e
    change i.val=11 at t
    omega
  have h (j : Fin 12) (hj : j≠(11:Fin 12)) :
      rep j=i ↔ lowStateAt A j=lowStateAt A (lowPrefix10 i) := by
    simpa only [repr i] using rel j (lowPrefix10 i) hj inp
  by_cases g : qdef A (lowPrefix10 i)=0
  · rw [gatherRow_apply,ite_eq_left g,onWeight]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j=(11:Fin 12)
    · subst j
      simp [withoutLast12,hc,hq,Ne.symm (hclean i g)]
    · simp [h j hj,lowState_eq_iff,g,withoutLast12,hj]
  · rw [gatherRow_apply,ite_eq_right g,offWeight]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j=(11:Fin 12)
    · subst j
      simp [withoutLast12,hq]
    · simp [h j hj,lowState_eq_iff,g,withoutLast12,hj]

theorem gather_adjoint_without_last {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (D1 : backSeed1 A b=0) (hc : nodes A (11:Fin 12)=1)
    (rep : Fin 12→Fin 10) (hrepr : ∀ i,rep (lowPrefix10 i)=i)
    (node : ∀ i,i≠(11:Fin 12) → nodes A i=nodes A (lowPrefix10 (rep i))) (k : ℕ) :
    gatherRow rep (orderAdjoint A b k) =
      lateResidual (prefixMat10 A) (nodes A∘lowPrefix10) (gatherRow rep (withoutLast12 b)) k -
        (b 10*(1-nodes A 10^k)) • (fun i =>
          A 10 (lowPrefix10 i)-A (lowPrefix10 (rep 10)) (lowPrefix10 i)) := by
  have hw (f : K→K) (hf : f 1=0) :
      (fun i => b i*f (nodes A i))=(fun i => withoutLast12 b i*f (nodes A i)) := by
    ext i
    by_cases e : i=(11:Fin 12)
    · subst i
      simp [withoutLast12,hc,hf]
    · simp [withoutLast12,e]
  rw [orderAdjoint_of_D1 D1,
    hw (fun x=>1-x^k) (by simp),hw (fun x=>(1-x)-(1-x^(k+1))/((k+1:ℕ):K)) (by simp),
    map_add,map_neg,gather_transMat_ten ha rep hrepr _ (by simp [withoutLast12]),
    gather_multiply_without_last rep node b (fun x=>1-x^k),
    gather_multiply_without_last rep node b (fun x=>(1-x)-(1-x^(k+1))/((k+1:ℕ):K)),lateResidual]
  simp only [Function.comp_apply,withoutLast12,show (10:Fin 12)≠11 by decide,ite_false]
  abel

theorem orderAdjoint_terminal_zero {s : ℕ} {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
    (ha : StrictLower A) (hc : nodes A (Fin.last s)=1) (k : ℕ) :
    orderAdjoint A b k (Fin.last s)=0 := by
  unfold orderAdjoint
  simp [transMat_last_zero ha,hc]

theorem mem_annih_sup_single_of {s : ℕ} {U : Submodule K (Vec K s)} {w : Vec K s}
    (i : Fin s) (hw : w∈annih U) (hwi : w i=0) :
    w∈annih (U ⊔ Submodule.span K {Pi.single i 1}) := by
  apply mem_annih.mpr
  rintro x hx
  obtain ⟨v,hv,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hz
  rw [map_add,map_smul,mem_annih.mp hw _ hv,row_single_eq_coord,hwi,smul_zero,add_zero]

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

structure SixOnLateRows (A : Fin 12→Fin 12→K) (b : Vec K 12) where
  rep : Fin 12→Fin 10
  psi : Vec K 10
  nu : K
  alpha : K
  beta : K
  gamma : K
  psi_nonzero : ∀ i,psi i≠0
  nu_nonzero : nu≠0
  eq1 : lateResidual (prefixMat10 A) (nodes A∘lowPrefix10) (gatherRow rep (withoutLast12 b)) 1=nu • psi
  eq2 : lateResidual (prefixMat10 A) (nodes A∘lowPrefix10) (gatherRow rep (withoutLast12 b)) 2=alpha • psi
  eq3 : lateResidual (prefixMat10 A) (nodes A∘lowPrefix10) (gatherRow rep (withoutLast12 b)) 3=
    fun i => (beta+gamma*nodes A (lowPrefix10 i))*psi i
  off_zero : ∀ i,qdef A (lowPrefix10 i)≠0 → gatherRow rep (withoutLast12 b) i=0
  on_b : ∀ i,qdef A (lowPrefix10 i)=0 →
    gatherRow rep (withoutLast12 b) i=onWeight A b (nodes A (lowPrefix10 i))
  on_psi : ∀ i,qdef A (lowPrefix10 i)=0 →
    psi i=onWeight A (transMat A (orderAdjoint A b 1)) (nodes A (lowPrefix10 i))

set_option maxHeartbeats 1200000 in
/-- All three actual late-window row relations, on the genuine prefix.
In the three-row relation, the full-stage annihilator is made small
by adjoining the terminal singleton, not by computing a quotient rank. -/
theorem order9_five_six_late_rows {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=6) :
    Nonempty (SixOnLateRows A b) := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  obtain ⟨_,h3,h4,_,hd4,_,_,_⟩ := order9_twelve_stage_chart ha ho
  obtain ⟨P,_,_,_,_,fit⟩ := two_curve_head h3 h4 (by omega)
  obtain ⟨e5,_,D1,hi,hc,_,hu⟩ := order9_five_six_stage_chart ha ho hN hM fit
  change nodes A (11:Fin 12)=1 at hc
  have dr5 : finrank K (treeSpace A 5)=10 := by
    rw [←e5]
    exact gradeFiveState_rank hM.ge (by omega)
  obtain ⟨_,_,_,endOut,_,_⟩ := order9_rank_five_full ha ho dr5
  obtain ⟨hbij,⟨i,hij,hsi,a,an,hr⟩,wo,wf⟩ := order9_five_six_ten_distinct_prefix ha ho hN hM
  let e := Equiv.ofBijective (fun j => lowNonterminalStateAt ha (lowPrefix10 j)) hbij
  let rep (j : Fin 12) := e.symm (lowNonterminalStateAt ha j)
  have re (j : Fin 10) : rep (lowPrefix10 j)=j := e.symm_apply_apply j
  have inp (j : Fin 10) : lowPrefix10 j≠(11:Fin 12) := by
    intro h
    have v := congrArg Fin.val h
    change j.val=11 at v
    omega
  have hh (j : Fin 12) (hj : j≠(11:Fin 12)) (q : qdef A j=0) : nodes A j≠1 :=
    fun x => hj (hu j q x)
  have rel (j k : Fin 12) (hj : j≠(11:Fin 12)) (hk : k≠(11:Fin 12)) :
      rep j=rep k ↔ lowStateAt A j=lowStateAt A k :=
    (e.symm.injective.eq_iff).trans (lowNonterminalState_eq_iff ha (hh j hj) (hh k hk))
  have repr (j : Fin 12) (hj : j≠(11:Fin 12)) : lowStateAt A j=lowStateAt A (lowPrefix10 (rep j)) :=
    (rel j _ hj (inp _)).mp (re (rep j)).symm
  have node (j : Fin 12) (hj : j≠(11:Fin 12)) : nodes A j=nodes A (lowPrefix10 (rep j)) :=
    stage_node_eq_of_state (repr j hj)
  let r := orderAdjoint A b 1
  let w := transMat A r
  let psi := gatherRow rep w
  let c := nodes A∘lowPrefix10
  let bb := gatherRow rep (withoutLast12 b)
  let L := lateResidual (prefixMat10 A) c bb
  have r10 : r (10:Fin 12)=-a := by
    change orderAdjoint A b 1 10=_
    simp [hr,ne_of_gt hij]
  have rn : r≠0 := fun h => neg_ne_zero.mpr an (r10.symm.trans (by rw [h];rfl))
  have ww : w=a • (A i-A (10:Fin 12)) := by
    change transMat A (orderAdjoint A b 1)=_
    rw [hr,map_smul,map_sub,transMat_single_incoming_row,transMat_single_incoming_row]
  have wcut (j : Fin 12) (hj : (10:Fin 12)≤j) : w j=0 := by
    rw [ww,Pi.smul_apply,Pi.sub_apply,ha i j (hij.le.trans hj),ha 10 j hj,sub_self,smul_zero]
  have w10 := wcut 10 le_rfl
  have w11 := wcut 11 (by decide)
  have wNoEnd : withoutLast12 w=w := by
    ext j
    by_cases e' : j=(11:Fin 12) <;> simp [withoutLast12,e',w11]
  have gW (j : Fin 10) :
      psi j=if qdef A (lowPrefix10 j)=0 then
        onWeight A w (nodes A (lowPrefix10 j)) else offWeight A w (nodes A (lowPrefix10 j)) := by
    change gatherRow rep w j=_
    nth_rw 1 [←wNoEnd]
    exact gather_without_last_tagged rep rel re hi hc (fun j=>hh _ (inp j)) _ j
  have gB (j : Fin 10) :
      bb j=if qdef A (lowPrefix10 j)=0 then
        onWeight A b (nodes A (lowPrefix10 j)) else offWeight A b (nodes A (lowPrefix10 j)) :=
    gather_without_last_tagged rep rel re hi hc (fun j=>hh _ (inp j)) _ j
  have pn (j : Fin 10) : psi j≠0 := by
    rw [gW]
    by_cases g : qdef A (lowPrefix10 j)=0
    · rw [ite_eq_left g]
      exact wo _ (Finset.mem_erase.mpr ⟨hh _ (inp j) g,mem_onNodes.mpr ⟨_,g,rfl⟩⟩)
    · rw [ite_eq_right g]
      exact wf _ (mem_supportedNodes.mpr ⟨_,g,rfl⟩)
  have wn : w≠0 := by
    intro e'
    exact pn 0 (by change gatherRow rep w 0=0; rw [e',map_zero]; rfl)
  have hRi : lowPrefix10 (rep 10)=i := by
    let k : Fin 10 := ⟨i.val,hij⟩
    have hk : lowPrefix10 k=i := Fin.ext rfl
    have he := (rel i 10 (ne_of_lt (hij.trans (by decide))) (by decide)).mpr hsi
    rw [←hk,re] at he
    rw [←he,hk]
  have cor : (fun j => A 10 (lowPrefix10 j)-A (lowPrefix10 (rep 10)) (lowPrefix10 j)) =
      (-a⁻¹) • psi := by
    ext j
    rw [hRi]
    have hwj := gather_prefix_only rep re w w10 w11 j
    change psi j=w (lowPrefix10 j) at hwj
    rw [Pi.smul_apply,smul_eq_mul,hwj,ww,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    field_simp [an]
    ring
  have move (k : ℕ) : L k=gatherRow rep (orderAdjoint A b k) +
      (b 10*(1-nodes A 10^k)) • ((-a⁻¹) • psi) := by
    rw [gather_adjoint_without_last ha D1 hc rep re node,cor,sub_add_cancel]
  have gr : gatherRow rep r=0 := by
    change gatherRow rep (orderAdjoint A b 1)=0
    rw [hr,map_smul,map_sub]
    have eq : gatherRow rep (Pi.single i (1:K)) = gatherRow rep (Pi.single (10:Fin 12) (1:K)) := by
      ext k
      simp only [gatherRow_apply]
      have eqR := (rel i 10 (ne_of_lt (hij.trans (by decide))) (by decide)).mpr hsi
      have ef (j : Fin 12) :
          (∑ l,if rep l=k then (Pi.single j (1:K) : Vec K 12) l else 0)=if rep j=k then 1 else 0 := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro l _ hl; simp [hl]
        · simp
      rw [ef,ef,eqR]
    rw [eq,sub_self,smul_zero]
  have gC : gatherRow rep (diag (nodes A) w)=diag c psi := by
    have e : (fun j => w j*id (nodes A j))=diag (nodes A) w := by ext j; simp [mul_comm]
    have t := gather_multiply_without_last rep node w id
    rw [wNoEnd,e] at t
    ext j
    simpa [diag_apply,c,psi,mul_comm] using congrFun t j
  have rS : r∈annih (treeSpace A 6) := orderAdjoint_annih ho (by decide)
  have wS : w∈annih (treeSpace A 5) := transMat_mem_annih_pred rS
  let U := Submodule.span K {r} ⊔ Submodule.span K {w}
  have nU : w∉Submodule.span K {r} := by
    intro e'
    obtain ⟨m,hm⟩ := Submodule.mem_span_singleton.mp e'
    have h := congrFun hm (10:Fin 12)
    change m*r 10=w 10 at h
    rw [r10,w10] at h
    have z := (mul_eq_zero.mp h).resolve_right (neg_ne_zero.mpr an)
    rw [z,zero_smul] at hm
    exact wn hm.symm
  have uRank : finrank K U=2 := by
    change finrank K ↥(Submodule.span K {r} ⊔ Submodule.span K {w})=2
    rw [Submodule.finrank_sup_span_singleton nU,finrank_span_singleton rn]
  have uInc : U≤annih (treeSpace A 5) :=
    sup_le ((Submodule.span_singleton_le_iff_mem ..).mpr
      (annih_mono_reverse (treeSpace_mono A (by decide)) rS))
      ((Submodule.span_singleton_le_iff_mem ..).mpr wS)
  have uEq : U=annih (treeSpace A 5) :=
    Submodule.eq_of_le_of_finrank_le uInc (by
      have h := finrank_add_annih_eq (treeSpace A 5)
      omega)
  have nC : diag (nodes A) w∉U := by
    intro e'
    obtain ⟨x,hx,y,hy,eq⟩ := Submodule.mem_sup.mp e'
    obtain ⟨k,rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨l,rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hk := congrFun eq (10:Fin 12)
    change k*r 10+l*w 10=nodes A 10*w 10 at hk
    rw [r10,w10,mul_zero,mul_zero,add_zero] at hk
    have k0 := (mul_eq_zero.mp hk).resolve_right (neg_ne_zero.mpr an)
    rw [k0,zero_smul,zero_add] at eq
    have he := congrArg (gatherRow rep) eq
    rw [map_smul,gC] at he
    have hconst (j : Fin 10) : c j=l :=
      mul_right_cancel₀ (pn j) ((congrFun he j).symm)
    have small : supportedNodes A (qdef A)⊆({l}:Finset K) := by
      intro x hx
      obtain ⟨j,hj,rfl⟩ := mem_supportedNodes.mp hx
      have ne : j≠(11:Fin 12) := fun h=>hj (h.symm ▸ hi)
      rw [Finset.mem_singleton,node j ne]
      exact hconst (rep j)
    have t := Finset.card_le_card small
    simp [hN] at t
  let E := treeSpace A 4 ⊔ Submodule.span K {Pi.single (11:Fin 12) 1}
  let V := U ⊔ Submodule.span K {diag (nodes A) w}
  have termRank : finrank K E=9 := by
    change (Pi.single (11:Fin 12) 1 : Vec K 12) ∉ treeSpace A 4 at endOut
    change finrank K ↥(treeSpace A 4 ⊔ Submodule.span K {Pi.single (11:Fin 12) 1})=9
    rw [Submodule.finrank_sup_span_singleton endOut,hd4]
  have vRank : finrank K V=3 := by
    change finrank K ↥(U ⊔ Submodule.span K {diag (nodes A) w})=3
    rw [Submodule.finrank_sup_span_singleton nC,uRank]
  have vInc : V≤annih E := by
    apply sup_le
    · apply sup_le
      · apply (Submodule.span_singleton_le_iff_mem ..).mpr
        exact mem_annih_sup_single_of _ (annih_mono_reverse (treeSpace_mono A (by decide)) rS)
          (orderAdjoint_terminal_zero ha hc 1)
      · apply (Submodule.span_singleton_le_iff_mem ..).mpr
        exact mem_annih_sup_single_of _ (annih_mono_reverse (treeSpace_mono A (by decide)) wS) w11
    · apply (Submodule.span_singleton_le_iff_mem ..).mpr
      apply mem_annih_sup_single_of
      · apply mem_annih.mpr
        intro z hz
        rw [row_flip_diag]
        exact mem_annih.mp wS _ (diag_treeSpace A 4 hz)
      · simp [w11]
  have vEq : V=annih E := Submodule.eq_of_le_of_finrank_le vInc (by
    have h := finrank_add_annih_eq E
    omega)
  have pick2 : orderAdjoint A b 2∈U := uEq.symm ▸ orderAdjoint_annih ho (by decide)
  obtain ⟨x,hx,y,hy,e2⟩ := Submodule.mem_sup.mp pick2
  obtain ⟨k,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨l,rfl⟩ := Submodule.mem_span_singleton.mp hy
  have g2 : gatherRow rep (orderAdjoint A b 2)=l • psi := by
    rw [←e2,map_add,map_smul,map_smul,gr,smul_zero,zero_add]
  have r3E : orderAdjoint A b 3∈annih E :=
    mem_annih_sup_single_of _ (orderAdjoint_annih ho (by decide)) (orderAdjoint_terminal_zero ha hc 3)
  obtain ⟨x,hx,z,hz,e3⟩ := Submodule.mem_sup.mp (vEq.symm ▸ r3E : orderAdjoint A b 3∈V)
  obtain ⟨u,hu',v,hv,e'⟩ := Submodule.mem_sup.mp hx
  obtain ⟨k',rfl⟩ := Submodule.mem_span_singleton.mp hu'
  obtain ⟨l',rfl⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨m,rfl⟩ := Submodule.mem_span_singleton.mp hz
  have g3 : gatherRow rep (orderAdjoint A b 3)=l' • psi+m • diag c psi := by
    rw [←e3,←e',map_add,map_add,map_smul,map_smul,map_smul,gr,gC,smul_zero,zero_add]
  let Ck (k : ℕ) := b 10*(1-nodes A 10^k)*(-a⁻¹)
  have e1 : L 1=Ck 1 • psi := by rw [move,gr,zero_add,smul_smul]
  have e2' : L 2=(l+Ck 2) • psi := by rw [move,g2,smul_smul,add_smul]
  have e3' : L 3=(fun j => ((l'+Ck 3)+m*c j)*psi j) := by
    rw [move,g3,smul_smul]
    ext j
    simp [Ck,diag_apply]
    ring
  have b0 : row (diag (1-c) bb) 1≠0 := by
    have h := back_target_nonzero ho (by decide : 2≤9)
    have eq : row (diag (1-c) bb) 1=row (diag (mirror A) b) 1 := by
      have id1 : diag (1-c) bb= gatherRow rep (diag (mirror A) (withoutLast12 b)) := by
        have p' := gather_multiply_without_last rep node b (fun x=>1-x)
        have q : (fun j => withoutLast12 b j*(1-nodes A j))=diag (mirror A) (withoutLast12 b) := by
          ext j; simp [mirror,mul_comm]
        rw [q] at p'
        ext j
        simpa [diag_apply,bb,mirror,c,mul_comm] using (congrFun p' j).symm
      have id2 : diag (mirror A) (withoutLast12 b)=diag (mirror A) b := by
        ext j
        by_cases t : j=(11:Fin 12)
        · subst j; simp [withoutLast12,mirror,hc]
        · simp [withoutLast12,t]
      rw [id1,id2,gatherRow_pair]
      rfl
    rw [eq]
    exact h
  have nn : Ck 1≠0 := by
    intro h
    apply prefix_late_one_ne_zero (prefixMat10_strict ha) c bb b0
    change L 1=0
    rw [e1,h,zero_smul]
  refine ⟨⟨rep,psi,Ck 1,l+Ck 2,l'+Ck 3,m,pn,nn,e1,e2',e3',?_,?_,?_⟩⟩
  · intro j g
    change bb j=0
    rw [gB,ite_eq_right g]
    exact offWeight_eq_zero_from_head ho P fit (by omega) _
      (mem_supportedNodes.mpr ⟨_,g,rfl⟩)
  · intro j g
    change bb j=onWeight A b (nodes A (lowPrefix10 j))
    rw [gB,ite_eq_left g]
  · intro j g; rw [gW,ite_eq_left g]

end Ordered
end RKCert.Paired
