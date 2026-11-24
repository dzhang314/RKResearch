module
public import RKCert.DirkLobattoQuadrature
public import Mathlib.FieldTheory.Separable
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial
variable {K:Type*} [Field K] [CharZero K] {m:ℕ}
noncomputable section

/-- Three genuinely omitted fixed-grid knots from the *original* all-degree
physical quadrature test.  Neither fixed quadrature weights nor a global
coefficient field ordering are hypothesized. -/
theorem omitted_grid_triple (hm:m=9 ∨ m=10) (Z Q:K[X]) (u:K)
    (dz:Z.natDegree≤m-2) (zm:Z.Monic) (dvd:Z ∣ (X-1)*lobatto m) (zu:Z.eval u=0)
    (dq:Q.natDegree≤5) (pay:∀W:K[X],5+(W*Z).natDegree+1≤2*m → integral ((W*Z)*Q)=0)
    (degree:((X-1)*lobatto (K:=K) m).natDegree=m+1)
    (split:((X-1)*lobatto (K:=K) m).Splits) (sep:((X-1)*lobatto (K:=K) m).Separable) :
    ∃v:Fin 3→K,Function.Injective v ∧ (∀k,v k≠u) ∧
      (∀k,((X-1)*lobatto m).eval (v k)=0) ∧ ∀k,Q.eval (v k)=0 := by
  classical
  let D:K[X]:=(X-1)*lobatto m
  let S:=D.roots.toFinset
  let T:=Z.roots.toFinset
  let E:=S \ T
  have pos:7≤m:=by rcases hm with rfl|rfl <;>decide
  have dnon:D≠0:=by intro e; change D.natDegree=m+1 at degree;rw [e,natDegree_zero] at degree;omega
  have big:S.card=m+1 := by
    change D.roots.toFinset.card=_
    rw [Multiset.toFinset_card_of_nodup (nodup_roots sep),←split.natDegree_eq_card_roots,degree]
  have small:T.card≤m-2 := (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans dz)
  have inc:T⊆S := by
    intro x hx
    have hz:= (mem_roots zm.ne_zero).mp (Multiset.mem_toFinset.mp hx)
    obtain ⟨H,e⟩:=dvd
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots dnon).mpr
    change D.eval x=0
    change D=Z*H at e
    rw [e,eval_mul,hz.eq_zero,zero_mul]
  have size:3≤E.card:=by
    have e:=Finset.card_sdiff_add_card_eq_card inc
    change E.card+T.card=S.card at e
    omega
  let node:Fin 3→E:=fun k=>(Fintype.equivFin E).symm ⟨k.val,by rw [Fintype.card_coe];have:=k.isLt;omega⟩
  let v:Fin 3→K:=fun k=>(node k).val
  have inj:Function.Injective v:=by
    intro a b ab
    have e:node a=node b:=Subtype.ext ab
    have ee:=((Fintype.equivFin E).symm.injective e)
    exact Fin.ext (congrArg (fun x:Fin (Fintype.card E)=>x.val) ee)
  have here(k:Fin 3):v k∈E:=(node k).property
  have vv(k:Fin 3):D.eval (v k)=0:=
    ((mem_roots dnon).mp (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp (here k)).1)).eq_zero
  have zne(k:Fin 3):Z.eval (v k)≠0:=fun e=>(Finset.mem_sdiff.mp (here k)).2
    (Multiset.mem_toFinset.mpr ((mem_roots zm.ne_zero).mpr e))
  refine ⟨v,inj,fun k e=>zne k (e ▸ zu),vv,?_⟩
  intro k
  obtain ⟨B,db⟩:=dvd
  change D=Z*B at db
  have bv:=vv k
  rw [db,eval_mul] at bv
  obtain ⟨V,vv⟩:=dvd_iff_isRoot.mpr ((mul_eq_zero.mp bv).resolve_left (zne k))
  let L:=V*Z
  have rep:(X-C (v k))*L=D:=by rw [db,vv];dsimp [L];ring
  have ln:L≠0:=fun e=>dnon (by rw [←rep,e,mul_zero])
  have lg:=congrArg Polynomial.natDegree rep
  rw [natDegree_mul (X_sub_C_ne_zero _) ln,natDegree_X_sub_C,degree] at lg
  have paid:=pay V (by change 5+L.natDegree+1≤2*m;omega)
  change integral (L*Q)=0 at paid
  rw [grid_cardinal_eval (Or.inr (Or.inr hm)) rep Q (by omega)] at paid
  exact (mul_eq_zero.mp paid).resolve_right (grid_cardinal_nz (Or.inr (Or.inr hm)) rep (by omega) ln)

end
end RKCert.Paired.Terminal
