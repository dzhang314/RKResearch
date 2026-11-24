module

public import RKCert.ERKOrderNineOneOffTailReduction

@[expose] public section

/-! # Two actual chronological tail identities on all twelve coordinates -/
namespace RKCert.Paired.OneOff.Seven
open Polynomial Module RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {A : Fin 12→Fin 12→K} {b : Vec K 12}

def shiftClock (A : Fin 12→Fin 12→K) (x : K) (f : Vec K 12) : Vec K 12 :=
  diag (nodes A) f-x • f

theorem shiftClock_value (A : Fin 12→Fin 12→K) (x : K) (f : Vec K 12) (r : Fin 12) :
    shiftClock A x f r=(nodes A r-x)*f r := by
  simp only [shiftClock,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply,sub_mul]

theorem tailHull_insert {x : K} {S : Finset K} (hn : x∉S) :
    nodalHull (insert x S)=(X-C x)*nodalHull S := by
  simp only [nodalHull,Finset.prod_insert hn]

set_option maxHeartbeats 1600000 in
theorem order9_actual_tail_identities (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (oneOff : (supportedNodes A (g A)).card=1)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide))
    (D7 : TwoFibres A a d (nodes A (5:Fin 12))) :
    let z := nodes A (5:Fin 12)
    let η := nodes A (7:Fin 12)
    let u := nodes A (8:Fin 12)
    let f := physicalTail A a d z
    let v := shiftClock A η f
    u≠η ∧ ∃ κ lam τ₀ τ₁ : K,
      mat A f=κ • v+τ₀ • Pi.single (Fin.last 11) 1 ∧
      mat A v=lam • shiftClock A u v+τ₁ • Pi.single (Fin.last 11) 1 := by
  let z := nodes A (5:Fin 12)
  let t := 2*d
  let η := nodes A (7:Fin 12)
  let u := nodes A (8:Fin 12)
  let f := physicalTail A a d z
  let v := shiftClock A η f
  let w := shiftClock A u v
  let S0 : Finset K := {0,d,t,z}
  let S5 : Finset K := insert η S0
  let S6 : Finset K := insert u S5
  have sixth := order9_sixth_feature ha ho oneOff D F
  have dn := D.base.dn
  have zn : z≠0 := sixth.2.1
  have zd : z≠d := sixth.2.2.1
  have zt : z≠t := sixth.2.2.2.1
  have dt : d≠t := by intro h; exact dn (by change d=2*d at h; linear_combination -h)
  have tn : t≠0 := mul_ne_zero (by norm_num : (2:K)≠0) dn
  obtain ⟨R8,R9,uη⟩ := order9_last_two_new_on ha ho oneOff D F D7
  obtain ⟨gη,nη,dη,tη,zη⟩ := R8
  obtain ⟨gu,nu,du,tu,zu⟩ := R9
  have f0 : nodes A (0:Fin 12)=0 ∧ g A (0:Fin 12)=0 := by
    have e := F.features 0
    simpa [chartNode,chartDefect] using And.intro e.1 e.2.1
  have C4 := order9_clean_four ha ho oneOff D F
  have c0 : S0.card=4 := by simp [S0,dn.symm,tn.symm,zn.symm,dt,zd.symm,zt.symm]
  have hη : η∉S0 := by simp [S0,show η≠0 from nη,show η≠d from dη,show η≠t from tη,show η≠z from zη]
  have hu : u∉S5 := by simp [S5,S0,show u≠η from uη,show u≠0 from nu,show u≠d from du,
    show u≠t from tu,show u≠z from zu]
  have c5 : S5.card=5 := by simp only [S5,Finset.card_insert_of_notMem hη,c0]
  have c6 : S6.card=6 := by simp only [S6,Finset.card_insert_of_notMem hu,c5]
  have hull0 : nodalHull S0=tailPolynomial d t z := by
    have h0 : (0:K)∉({d,t,z}:Finset K) := by simp [dn.symm,tn.symm,zn.symm]
    have hd : d∉({t,z}:Finset K) := by simp [dt,zd.symm]
    have ht : t∉({z}:Finset K) := by simp [zt.symm]
    simp only [S0,nodalHull,Finset.prod_insert h0,Finset.prod_insert hd,Finset.prod_insert ht,
      Finset.prod_singleton,C_0,sub_zero,tailPolynomial,fibrePoly]
  have hull5 : nodalHull S5=(X-C η)*tailPolynomial d t z := by
    rw [show S5=insert η S0 from rfl,tailHull_insert hη,hull0]
  have hull6 : nodalHull S6=(X-C u)*((X-C η)*tailPolynomial d t z) := by
    rw [show S6=insert u S5 from rfl,tailHull_insert hu,hull5]
  have fm : f∈treeSpace A 4 := physicalTail_mem A a d z
  have vm : v∈treeSpace A 5 := (treeSpace A 5).sub_mem (diag_treeSpace A 4 fm)
    ((treeSpace A 5).smul_mem _ (treeSpace_mono A (by decide : 4≤5) fm))
  have fVan := order9_tail_initial_zero ha ho oneOff D F D7
  have vVan (l : Fin 12) (ll : l.val<8) : v l=0 := by
    change shiftClock A η f l=0
    rw [shiftClock_value]
    by_cases small : l < (7:Fin 12)
    · have hf : f l=0 := fVan l small
      rw [hf,mul_zero]
    · have e : l=(7:Fin 12) := Fin.ext (by have lt : 7≤l.val := le_of_not_gt small; omega)
      subst l
      change (η-η)*f (7:Fin 12)=0
      rw [sub_self,zero_mul]
  have afVan (l : Fin 12) (ll : l.val<8) : mat A f l=0 := by
    apply causal_mat ha
    intro k kl
    have klt : k.val<l.val := kl
    exact fVan k (show k.val<7 by omega)
  have avVan (l : Fin 12) (ll : l.val<9) : mat A v l=0 := by
    apply causal_mat ha
    intro k kl
    have klt : k.val<l.val := kl
    exact vVan k (by omega)
  have vOn (r : Fin 12) (gr : g A r=0) : v r=(nodalHull S5).eval (nodes A r) := by
    change shiftClock A η f r=_
    rw [shiftClock_value,hull5,eval_mul,eval_sub,eval_X,eval_C]
    exact congrArg ((nodes A r-η)* ·) (physicalTail_on a d z gr)
  have wOn (r : Fin 12) (gr : g A r=0) : w r=(nodalHull S6).eval (nodes A r) := by
    change shiftClock A u v r=_
    rw [shiftClock_value,hull6,←hull5,eval_mul,eval_sub,eval_X,eval_C,vOn r gr]
  have vOff (r : Fin 12) (gr : g A r≠0) : v r=0 := by
    change shiftClock A η f r=0
    have hf : f r=0 := physicalTail_off D gr
    rw [shiftClock_value,hf,mul_zero]
  have wOff (r : Fin 12) (gr : g A r≠0) : w r=0 := by
    change shiftClock A u v r=0
    rw [shiftClock_value,vOff r gr,mul_zero]
  have roots5 {P : K[X]} {y : Vec K 12}
      (eq : ∀ r, r≠Fin.last 11 → g A r=0 → y r=P.eval (nodes A r))
      (van : ∀ r : Fin 12, r.val<8 → y r=0) :
      ∀ x∈S5, P.eval x=0 := by
    have atRoot (r : Fin 12) (rne : r≠Fin.last 11) (gr : g A r=0) (r8 : r.val<8) :
        P.eval (nodes A r)=0 := (eq r rne gr).symm.trans (van r r8)
    intro x xx
    simp only [S5,S0,Finset.mem_insert,Finset.mem_singleton] at xx
    rcases xx with rfl|rfl|rfl|rfl|rfl
    · exact atRoot 7 (by decide) gη (by decide)
    · simpa only [f0.1] using atRoot 0 (by decide) f0.2 (by decide)
    · simpa only [C4.node2] using atRoot 2 (by decide) C4.g2 (by decide)
    · simpa only [C4.node3] using atRoot 3 (by decide) C4.g3 (by decide)
    · exact atRoot 5 (by decide) C4.g5 (by decide)
  obtain ⟨p5,p6⟩ := order9_native_profiles ha ho oneOff D F
  obtain ⟨P,Pd,PE,PO⟩ := tail_profile_reduction ha ho oneOff D F D7 (by decide : 3≤5)
    (p5 (mat A f) (mat_treeSpace A 4 fm)) (fun r rr=>afVan r (by have h : r.val<7 := rr; omega))
  obtain ⟨κ,τ₀,Id5⟩ := assemble_tail_from_nodal_hull (S:=S5)
    (by rwa [c5]) (roots5 PE afVan) PE PO vOn vOff
  obtain ⟨Q,Qd,QE,QO⟩ := tail_profile_reduction ha ho oneOff D F D7 (by decide : 3≤6)
    (p6 (mat A v) (mat_treeSpace A 5 vm)) (fun r rr=>avVan r (by have h : r.val<7 := rr; omega))
  have roots6 : ∀ x∈S6, Q.eval x=0 := by
    intro x xx
    change x∈insert u S5 at xx
    rcases Finset.mem_insert.mp xx with h|h
    · subst x
      exact (QE 8 (by decide) gu).symm.trans (avVan 8 (by decide))
    · exact roots5 QE (fun r rr=>avVan r (by omega)) x h
  obtain ⟨lam,τ₁,Id6⟩ := assemble_tail_from_nodal_hull (S:=S6)
    (by rwa [c6]) roots6 QE QO wOn wOff
  exact ⟨uη,κ,lam,τ₀,τ₁,Id5,Id6⟩

end RKCert.Paired.OneOff.Seven
