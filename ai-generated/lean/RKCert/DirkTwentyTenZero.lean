module
public import RKCert.DirkTwentyJoint
public import RKCert.DirkNineRankDispatch
@[expose] public section
namespace RKCert.Paired.Terminal
open Module
variable {K:Type*} [Field K] [CharZero K] {s:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section

/-- Every F10 column on the actual order-20/28-row boundary is zero at
the true last coordinate. The proof does not assume C(2) or rule out a
signed coefficient field. A one-dimensional quotient cannot hide a new
invariant subspace: otherwise its entire clock-extended F9 would stall. -/
theorem twenty_all_ten_zero (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28):
    ∀f∈zeroSpace A 10,f (Fin.last s)=0:=by
  classical
  obtain ⟨e,h⟩:=twenty_ranks ha ho size
  obtain ⟨_,_,_,_,z9⟩:=twenty_final_row ha ho size h
  obtain ⟨four,core⟩:=twenty_joint_pure ha ho size h
  let F:=zeroSpace A
  let T:=diag (nodes A)
  let Z:=raisedNine A
  let G:=F 10 ⊓ LinearMap.ker (LinearMap.proj (Fin.last s))
  let W:=jointWithOrigin A b e
  have inv:W.map T≤W:=jointWithOrigin_invariant e
  have f9min:=h.nine.1
  have f10:=h.ten
  have f11:=h.eleven
  have esc:¬ (F 9).map T≤F 9:=by
    intro inside
    have gr:=dirk_forward_invariant_outgoing ha ho (j:=9) (by decide) (F 9) le_rfl (fun _ hh=>inside ⟨_,hh,rfl⟩)
    change finrank K (zeroSpace A 9)+4≤finrank K (zeroSpace A 10) at gr;omega
  have fz:F 9<Z:=lt_of_le_of_ne le_sup_left (fun eqn=>esc (le_sup_right.trans eqn.ge))
  have ZG:Z≤G:=by
    apply sup_le
    · exact le_inf (zeroSpace_mono A (by decide)) z9
    · rintro _ ⟨v,hv,rfl⟩
      exact ⟨diag_zeroSpace A 9 hv,by change nodes A (Fin.last s)*v (Fin.last s)=0;rw [z9 _ hv,mul_zero]⟩
  intro f hf
  by_contra nz
  have proper:G<F 10:=lt_of_le_of_ne inf_le_left (fun eqn=>nz ((eqn.symm ▸ hf : f∈G).2))
  have gr1:=Submodule.finrank_lt_finrank_of_lt fz
  have gr2:=Submodule.finrank_mono ZG
  have gr3:=Submodule.finrank_lt_finrank_of_lt proper
  change finrank K (zeroSpace A 9)<finrank K Z at gr1
  change finrank K G<finrank K (zeroSpace A 10) at gr3
  have f9:finrank K (zeroSpace A 9)=8+e:=by omega
  have rz:finrank K Z=9+e:=by omega
  have ident:Z=G:=Submodule.eq_of_le_of_finrank_le ZG (by omega)
  have nonZ:¬Z.map T≤Z:=by
    intro stall
    have price:=dirk_forward_invariant_outgoing ha ho (j:=10) (by decide) Z (ZG.trans inf_le_left)
      (fun _ hp=>stall ⟨_,hp,rfl⟩)
    change finrank K Z+5≤finrank K (zeroSpace A 11) at price;omega
  have wu:W≤Z:=ident ▸ core
  have in9:W≤F 9:=by
    by_contra out
    have bigger:F 9<F 9 ⊔ W:=lt_of_le_of_ne le_sup_left (fun eqn=>out (le_sup_right.trans eqn.ge))
    have inc:F 9 ⊔ W≤Z:=sup_le fz.le wu
    have cmp:=Submodule.finrank_lt_finrank_of_lt bigger
    change finrank K (zeroSpace A 9)<finrank K (F 9 ⊔ W : Submodule K (Vec K (s+1))) at cmp
    have whole:F 9 ⊔ W=Z:=Submodule.eq_of_le_of_finrank_le inc (by omega)
    apply nonZ
    calc
      Z.map T=(F 9).map T ⊔ W.map T:=by rw [←whole,Submodule.map_sup]
      _≤Z:=sup_le le_sup_right (inv.trans wu)
  have products(a:Vec K (s+1))(ha':a∈F 5)(v:Vec K (s+1))(hv:v∈F 5):a*v∈Z:=by
    rw [ident]
    exact ⟨zeroSpace_mul (A:=A) (m:=5) (n:=5) ha' hv,by
      change a (Fin.last s)*v (Fin.last s)=0
      rw [z9 _ (zeroSpace_mono A (by decide:5≤9) ha'),zero_mul]⟩
  obtain ⟨_,_,U,w,r,short,ui,_,band⟩:=nine_rank_dispatch ha ho (by decide) h.three.ge h.five.2
    h.six f9 h.ten.le four in9 inv
  exact no_nine_short_head ha ho (by decide) short ui band nonZ products
end
end RKCert.Paired.Terminal

