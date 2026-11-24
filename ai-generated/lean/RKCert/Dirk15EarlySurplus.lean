module
public import RKCert.Dirk15EarlyMultiplier
@[expose] public section
namespace RKCert.Paired.EarlyFifteen
open Module RKCert.OneEscape PivotProjection
variable {K:Type*} [Field K] [CharZero K] {A:Fin 20→Fin 20→K} {b:Vec K 20}

/-- The first mixed-product application makes F4 equal the two-dimensional
core. Its outgoing gain buys exactly two short head powers at grade five.
The same projected multiplier argument can then be reused for paid squares. -/
theorem finish (R:Budget A) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 15) : False:=by
  obtain ⟨U,w,r,h⟩:=heads R ha ho
  have B:=cut R h ho
  have f4U:=grade_four_in_core R B h ha ho
  have strict:=Submodule.finrank_lt_finrank_of_lt
    (dirk_zeroSpace_lt_succ ha ho (j:=3) (by decide) (by decide))
  change finrank K (zeroSpace A 3)<finrank K (zeroSpace A 4) at strict
  have d3:=R.f3
  have small:=h.small
  have f4:finrank K (zeroSpace A 4)=2:=by have a:=Submodule.finrank_mono f4U;omega
  have ku:finrank K U=2:=by have a:=Submodule.finrank_mono f4U;omega
  have eq4:zeroSpace A 4=U:=Submodule.eq_of_le_of_finrank_le f4U (by omega)
  have f4gain:=dirk_forward_invariant_outgoing ha ho (j:=4) (by decide) U eq4.ge
    (fun x hx=>h.inv ⟨x,hx,rfl⟩)
  change finrank K U+2≤finrank K (zeroSpace A 5) at f4gain
  have f56:=Submodule.finrank_lt_finrank_of_lt
    (dirk_zeroSpace_lt_succ ha ho (j:=5) (by decide) (by decide))
  change finrank K (zeroSpace A 5)<finrank K (zeroSpace A 6) at f56
  have f6:=R.f6;have f7:=R.f7;have f8:=R.f8
  have f5:finrank K (zeroSpace A 5)=4:=by omega
  have escape5:¬(zeroSpace A 5).map (diag (nodes A))≤zeroSpace A 5:=by
    intro stay
    have bad:=dirk_forward_invariant_outgoing ha ho (j:=5) (by decide) (zeroSpace A 5)
      le_rfl (fun x hx=>stay ⟨x,hx,rfl⟩)
    change finrank K (zeroSpace A 5)+2≤finrank K (zeroSpace A 6) at bad
    omega
  have unit5:finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 5)+1:=by omega
  obtain ⟨q,V,v,pos,vin,paid,max5,base,cheap,esc,rank,normal,_⟩:=
    Clock.ordinary_normal_head A 5 unit5 escape5
  have vu:V≤U:=by
    intro x hx
    rw [←Clock.sum_fibers (nodes A) x]
    apply Submodule.sum_mem
    intro a _
    have mm:=Clock.fiber_mem vin a hx
    have rr:Clock.fiber (nodes A) a x ∈zeroSpace A 6:=zeroSpace_mono A (by decide:5≤6) (paid mm)
    apply Clock.localized_mem (z:=a) h.inv h.normal
      ((show r≤r+4 by omega).trans_lt B.sites) ((show zeroSpace A 6=chain (diag (nodes A)) U w r from h.band 0 (by decide)).le rr)
    intro i he
    simp [Clock.fiber,he]
  have uv:U≤V:=max5 U h.inv (eq4.ge.trans (zeroSpace_mono A (by decide:4≤5)))
  have vu':V=U:=le_antisymm vu uv
  subst V
  have q2:q=2:=by omega
  subst q
  let C:=diag (nodes A)
  have caps (k:ℕ) (hk:k<3):finrank K (zeroSpace A (5+k+1))≤finrank K (zeroSpace A (5+k))+1:=by
    rcases (show k=0∨k=1∨k=2 by omega) with rfl|rfl|rfl
    · exact unit5
    · change finrank K (zeroSpace A 7)≤finrank K (zeroSpace A 6)+1;omega
    · change finrank K (zeroSpace A 8)≤finrank K (zeroSpace A 7)+1;omega
  have escapes (k:ℕ) (hk:k<3):¬(zeroSpace A (5+k)).map C≤zeroSpace A (5+k):=by
    rcases (show k=0∨k=1∨k=2 by omega) with rfl|rfl|rfl
    · exact escape5
    · exact f6_escape R ha ho
    · exact f7_escape R ha ho
  have grow:=Clock.ordinary_staircase h.inv (by decide:0<2) base caps escapes
  have h':Heads A U v 3:=by
    refine ⟨by decide,small,by omega,h.inv,h.core,normal,fun k hk=>?_⟩
    have now:=grow (k+1) (by omega)
    rw [show 5+(k+1)=6+k by omega,show 2+(k+1)=3+k by omega] at now
    exact now
  have B':=cut R h' ho
  have v5:v∈zeroSpace A 5:=by simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using cheap 0 (by decide)
  have cv5:C v∈zeroSpace A 5:=by simpa only [pow_one] using cheap 1 (by decide)
  have invV:=diagonal_product_invariant R B' h' ho (by decide:5+4≤10) eq4.ge v5
  have infK : Infinite K := Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective
  obtain ⟨π,rcomm⟩:=@exists_joint_retraction K _ 20 infK (nodes A) v U h.inv invV
  have squares (k:ℕ) (hk:k≤2):v*(C^k) v∈zeroSpace A 10:=by
    rcases (show k=0∨k=1∨k=2 by omega) with rfl|rfl|rfl
    · simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using zeroSpace_mul (A:=A) (m:=5) (n:=5) v5 v5
    · simpa only [pow_one] using zeroSpace_mul (A:=A) (m:=5) (n:=5) v5 cv5
    · have eq:v*(C^2) v=C v*C v:=by
        ext i;simp only [Pi.mul_apply,C,diag_apply,Clock.pow_diag_apply];ring
      rw [eq]
      exact zeroSpace_mul (A:=A) (m:=5) (n:=5) cv5 cv5
  have bad:=projected_multiplier R B' h' ha ho rcomm
    (zeroSpace_mono A (by decide:5≤6) v5) cv5 (n:=2) (by decide) (by decide) squares
  exact esc (paid (pow_mem h.inv bad 2))
end RKCert.Paired.EarlyFifteen

namespace RKCert.Paired
open Module
variable {K:Type*} [Field K] [CharZero K] {A:Fin 20→Fin 20→K} {b:Vec K 20}

/-- The actual twenty-row anchored order-fifteen branch cannot have three
or more full marked rows at grade four. This excludes the complete early
surplus branch, not the separate terminal-zero or nonanchored alternatives. -/
theorem order15_no_early_marked_surplus (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 15)
    (h0:q₂ (mat A) (nodes A) 1=0) (hm:3≤finrank K (marked A 15 4)) : False:=
  EarlyFifteen.finish (EarlyFifteen.budget ha ho h0 hm) ha ho
end RKCert.Paired
