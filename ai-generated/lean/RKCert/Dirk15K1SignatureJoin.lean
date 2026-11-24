module

public import RKCert.Dirk15MinimalK1

@[expose] public section

/-! # Matching the visible forward and reverse quartics on true signatures -/
namespace RKCert.Paired.Signature
open Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K]

set_option maxHeartbeats 2100000 in
theorem visible_profiles_agree (c w v : Fin 18→K) {D S P Q : K[X]}
    (dD : D.natDegree≤8) (dS : S.natDegree≤1) (dP : P.natDegree≤4) (dQ : Q.natDegree≤4)
    (Dn : D≠0) (Sn : S≠0)
    (inj : Function.Injective (fun i => (c i,w i)))
    (cap : ∀ a,(fiberAt c a).card≤2)
    (clean : ∀ i,w i=0 → D.eval (c i)=0)
    (amp : ∀ i,v i=w i*S.eval (c i))
    (ord : ∀ i,w i≠0 → v i=P.eval (c i))
    (rev : ∀ i,v i≠0 → v i=Q.eval (c i)) :
    P=Q := by
  let Z := (Finset.univ:Finset (Fin 18)).filter (fun i => w i=0)
  let O := (Finset.univ:Finset (Fin 18)).filter (fun i => S.eval (c i)=0)
  let J := Finset.univ \ (Z∪O)
  have dec : Set.InjOn c (Z:Set (Fin 18)) := by
    intro i hi j hj eq
    have e : w i=0 := (Finset.mem_filter.mp hi).2
    have f : w j=0 := (Finset.mem_filter.mp hj).2
    exact inj (Prod.ext eq (e.trans f.symm))
  have CZ : Z.image c⊆D.roots.toFinset := by
    intro a ha
    obtain ⟨i,zi,rfl⟩ := Finset.mem_image.mp ha
    exact Multiset.mem_toFinset.mpr ((mem_roots Dn).mpr (clean i (Finset.mem_filter.mp zi).2))
  have z8 : Z.card≤8 := by
    have e := (Finset.card_le_card CZ).trans ((Multiset.toFinset_card_le D.roots).trans ((card_roots' _).trans dD))
    rwa [Finset.card_image_of_injOn dec] at e
  have o2 : O.card≤2 := by
    have e : S.roots.toFinset.card≤1 := (Multiset.toFinset_card_le S.roots).trans ((card_roots' S).trans dS)
    obtain ⟨a,ha⟩ := Finset.card_le_one_iff_subset_singleton.mp e
    have H : O⊆fiberAt c a := by
      intro i hi
      have r : S.eval (c i)=0 := (Finset.mem_filter.mp hi).2
      have p := ha (Multiset.mem_toFinset.mpr ((mem_roots Sn).mpr r))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_singleton.mp p⟩
    exact (Finset.card_le_card H).trans (cap a)
  have j8 : 8≤J.card := by
    have u := Finset.card_union_le Z O
    have e : J.card=18-(Z∪O).card := by
      change (Finset.univ \ (Z∪O)).card=18-(Z∪O).card
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
    omega
  have live (i : Fin 18) (hi : i∈J) : w i≠0 ∧ S.eval (c i)≠0 := by
    have n := (Finset.mem_sdiff.mp hi).2
    exact ⟨fun e => n (Finset.mem_union_left O (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩)),
      fun e => n (Finset.mem_union_right Z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩))⟩
  have same : Set.InjOn c (J:Set (Fin 18)) := by
    intro i hi j hj eq
    have a := ord i (live i hi).1
    have b := ord j (live j hj).1
    have prod : w i*S.eval (c i)=w j*S.eval (c i) := by
      rw [←amp i,a,eq,←b,amp j]
    exact inj (Prod.ext eq (mul_right_cancel₀ (live i hi).2 prod))
  have ix : (J.image c).card=J.card := Finset.card_image_of_injOn same
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (J.image c)
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast (dP.trans_lt (by omega)))
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast (dQ.trans_lt (by omega)))
  · intro a ha
    obtain ⟨i,im,rfl⟩ := Finset.mem_image.mp ha
    have l := live i im
    have nv : v i≠0 := by rw [amp i]; exact mul_ne_zero l.1 l.2
    exact (ord i l.1).symm.trans (rev i nv)

end
end RKCert.Paired.Signature

namespace RKCert.Paired
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

namespace Order15K1Head
variable (h : Order15K1Head A b) (D : h.head.DeletedPencil) (v : Vec K 20)

structure NativeMixedSignature where
  S : K[X]
  P : K[X]
  Q : K[X]
  R : K[X]
  S_ne : S≠0
  P_ne : P≠0
  S_degree : S.natDegree≤1
  P_degree : P.natDegree≤4
  Q_degree : Q.natDegree≤4
  R_degree : R.natDegree≤5
  reflect : P=reflectPolynomial Q
  algebra : D.D*S=P*R
  relation : ∀ i : Fin 20,i≠Fin.last 19 → i∉ghostPositions A b →
    D.D.eval (nodes A i)=h.head.w i*R.eval (nodes A i)
  amplitude : ∀ i : Fin 20,i∉ghostPositions A b → v i=h.head.w i*S.eval (nodes A i)
  fit : ∀ i : Fin 20,i≠Fin.last 19 → i∉ghostPositions A b → h.head.w i≠0 → v i=P.eval (nodes A i)
  marked_fit : ∀ i : Fin 20, reverseCubic A b i≠0 → v i=Q.eval (mirror A i)
  marked_clean : ∀ i : Fin 20,b i≠0 → reverseCubic A b i=0 → v i=0

set_option maxHeartbeats 1900000 in
theorem mixed_signature (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) (hm : finrank K (marked A 15 4)=2)
    (hv : v∈zeroSpace A 4) (vis : v∉simultaneousGhosts A b) :
    Nonempty (h.NativeMixedSignature D v) := by
  obtain ⟨out,Q,qn,dQ,qfit,qclean⟩ := order15_minimal_visible_quartic ha ho H hm h.head hv vis
  obtain ⟨k,hk,S,Sn,dS,Sfit⟩ := h.head.visible_head_degree hv out
  have ds : S.natDegree≤1 := by rw [h.core_one] at dS; exact dS
  have amp (i : Fin 20) (ig : i∉ghostPositions A b) :
      v i=h.head.w i*S.eval (nodes A i) := by
    have eq := congrFun Sfit i
    have z : k i=0 := ghostPositions_vanish (v:=k) (h.core_eq ▸ hk) ig
    simp only [Pi.add_apply,weightedEval_apply,z,zero_add] at eq
    rwa [mul_comm] at eq
  obtain ⟨P,dP,pfit⟩ := h.actual_mixed_polynomial D ha ho H hv
  obtain ⟨u,hu,R,dR,eR⟩ := D.head_profile
  have dr : R.natDegree≤5 := h.length_five ▸ dR
  have rel (i : Fin 20) (nt : i≠Fin.last 19) (ng : i∉ghostPositions A b) :
      D.D.eval (nodes A i)=h.head.w i*R.eval (nodes A i) := by
    have eq := eR i nt
    have z : u i=0 := ghostPositions_vanish (v:=u) (h.core_eq ▸ hu) ng
    simpa only [z,zero_add,mul_comm] using eq
  have dn : D.D≠0 := by intro z; have e:=D.dmin; rw [z,natDegree_zero] at e; contradiction
  obtain ⟨idx,_,rt,_,dc,cap⟩ := h.eighteen_indices ha ho H
  let c := fun i => nodes A (idx i)
  let w := fun i => h.head.w (idx i)
  let vv := fun i => v (idx i)
  have matchD (i : Fin 18) : D.D.eval (c i)=w i*R.eval (c i) :=
    rel _ (rt i).1 (rt i).2
  have pv (i : Fin 18) (wi : w i≠0) : vv i=P.eval (c i) :=
    pfit _ (rt i).1 (rt i).2 wi
  have a18 : D.D.natDegree+(D.D*S-P*R).natDegree<18 := by
    have mx := natDegree_mul_le (p:=D.D) (q:=S)
    have my := natDegree_mul_le (p:=P) (q:=R)
    have mz := natDegree_sub_le (D.D*S) (P*R)
    have q := D.dmax
    omega
  have a := Signature.close_mixed_signatures c w D.D R S P dn a18 dc cap matchD
    (fun i hi => (pv i hi).symm.trans (amp _ (rt i).2))
  have pn : P≠0 := by
    intro e
    rw [e,zero_mul] at a
    exact (mul_ne_zero dn Sn) a
  have rq (i : Fin 18) (nz : vv i≠0) : vv i=(reflectPolynomial Q).eval (c i) := by
    let j := idx i
    have ns : v j≠0 := nz
    have tn : reverseCubic A b j≠0 := by
      intro t0
      by_cases bj : b j≠0
      · exact ns (qclean j bj t0)
      · apply ns
        by_cases j0 : j=0
        · rw [j0]
          exact zeroSpace_first_of_row H.initial.first_zero 4 hv
        · exact ((rt i).2 (mem_ghostPositions.mpr ⟨j0,not_ne_iff.mp bj,t0⟩)).elim
    simpa only [reflectPolynomial,eval_comp,eval_sub,eval_one,eval_X,mirror,Pi.sub_apply,Pi.one_apply,c,vv]
      using qfit j tn
  have agree : P=reflectPolynomial Q := Signature.visible_profiles_agree c w vv
    D.dmax ds dP ((reflectPolynomial_degree Q).trans dQ) dn Sn dc cap
    (fun i e => by rw [matchD i,e,zero_mul]) (fun i => amp _ (rt i).2) pv rq
  exact ⟨⟨S,P,Q,R,Sn,pn,ds,dP,dQ,dr,agree,a,rel,amp,pfit,qfit,qclean⟩⟩

end Order15K1Head
end
end RKCert.Paired
