module
public import RKCert.Dirk17Minimal
public import RKCert.DirkEightCoreCap
public import RKCert.DirkSynchronousFifth
public import RKCert.FiveDebutObstruction
@[expose] public section
namespace RKCert.Paired.Seventeen
open Module Terminal RKCert.OneEscape RKCert.EndpointPhysical
variable {K:Type*} [Field K] [CharZero K] {A:Fin 23→Fin 23→K} {b:Vec K 23}
noncomputable section
set_option maxRecDepth 4000
/-- Over a field omitting sqrt(-6), there is no 23-row order-17 C(2)
array with the minimal early grade-five marked budget. The proof does
not use a free cardinal pencil, or a merger of repeated stage rows. -/
theorem no_minimal (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (anc:q₂ (mat A) (nodes A) 1=0) (field:NoExceptionalRatio K)
    (budget:finrank K (marked A 17 5)≤3):False:=by
  classical
  let h:=minimal ha ho anc budget
  let F:=zeroSpace A
  let C:=diag (nodes A)
  let W:=jointWithOrigin A b 0
  have wi:W.map C≤W:=jointWithOrigin_invariant _
  have whole:W≤F 8:=minimal_joint_inside ha ho h
  have escapes:¬F 5≤W:=seventeen_five_visible ha ho whole wi
  have f4w:F 4≤W:=by
    intro v hv
    exact jointWithOrigin_iff.mpr ⟨h.D.quartic_jointly_hidden_eight ha ho field (by decide) hv
      (h.zero _ (zeroSpace_mono A (by decide:4≤5) hv)),fun _=>zeroSpace_first_of_row h.origin 4 hv⟩
  have sync(v:Vec K 23)(hv:v∈F 5)(cv:C v∈F 5):v∈W:=
    jointWithOrigin_iff.mpr ⟨h.D.synchronous_fifth_hidden ha ho field (by decide) hv cv (h.zero _ hv),
      fun _=>zeroSpace_first_of_row h.origin 5 hv⟩
  have R:=ranks ha ho
  have ex:excess A=0:=by simp [excess,anc]
  have r5:=R.five;have r6:=R.six;have r7:=R.seven;have r8:=R.eight
  rw [ex] at r5 r6 r7 r8
  change 3≤finrank K (F 5) ∧ finrank K (F 5)≤4 at r5
  change finrank K (F 6)=5 at r6;change finrank K (F 7)=6 at r7;change finrank K (F 8)=7 at r8
  have g3:=R.three;rw [ex] at g3
  have f4low:2≤finrank K (F 4):=by
    have q:=flag_gain ha ho (a:=3) (n:=4) (by decide) (by decide) (by decide)
    change finrank K (F 3)+1≤finrank K (F 4) at q
    change finrank K (F 3)=1 at g3;omega
  have f5n:finrank K (F 5)=4:=by
    by_contra bad
    have one:finrank K (F 5)≤finrank K (F 4)+1:=by omega
    have out:¬(F 4).map C≤F 4:=by
      intro inv
      have gr:=dirk_forward_invariant_outgoing ha ho (j:=4) (by decide) (F 4) le_rfl (fun v hv=>inv ⟨v,hv,rfl⟩)
      change finrank K (F 4)+2≤finrank K (F 5) at gr;omega
    have e:F 5=F 4 ⊔ (F 4).map C:=Clock.ordinary_step one out
    apply escapes
    rw [e];exact sup_le f4w ((Submodule.map_mono f4w).trans wi)
  have flat(k:ℕ)(hk:k<2):finrank K (F (5+k+1))≤finrank K (F (5+k))+1:=by
    rcases (by omega:k=0∨k=1) with rfl|rfl <;> simp only [Nat.reduceAdd] <;> omega
  have non(k:ℕ)(hk:k<2):¬(F (5+k)).map C≤F (5+k):=by
    intro inv
    have g:=dirk_forward_invariant_outgoing ha ho (j:=5+k) (by omega) (F (5+k)) le_rfl (fun v hv=>inv ⟨v,hv,rfl⟩)
    change finrank K (F (5+k))+(5+k)/2≤finrank K (F (5+k+1)) at g
    have one:=flat k hk;omega
  obtain ⟨r,U,w,pos,ui,inc,max5,base,powers,_,_,_,_⟩:=Clock.ordinary_normal_head A 5 (flat 0 (by decide)) (non 0 (by decide))
  have Uw:U≤W:=fun v hv=>sync v (inc hv) (inc (ui ⟨v,hv,rfl⟩))
  by_cases one:r=1
  · obtain ⟨T,tf,ti,largest⟩:=largest_invariant C (F 8)
    have above:W≤T:=largest W whole wi
    have out:¬F 5≤T:=seventeen_five_visible ha ho tf ti
    have quota:=terminal_quotient_growth C F (fun _ _ hh=>zeroSpace_mono A hh)
      (fun j=>Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)) tf ti largest (by decide:5≤8) out
    have same:F 5=F 5⊔T:=Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    have w5:W≤F 5:=above.trans (le_sup_right.trans same.ge)
    have uw:U=W:=le_antisymm Uw (max5 W wi w5)
    have algebra:Clock.MulClosed U:=by
      rw [uw]
      intro v hv z hz
      obtain ⟨⟨bv,tv⟩,v0⟩:=jointWithOrigin_iff.mp hv
      apply jointWithOrigin_iff.mpr
      exact ⟨⟨by rw [←mul_assoc,bv,zero_mul],by rw [←mul_assoc,tv,zero_mul]⟩,fun h0=>by simp [v0 h0]⟩
    apply RKCert.FiveDebut.no_grade5_head ha ho (by decide) ui algebra inc
    simpa only [one] using Clock.ordinary_staircase ui pos base flat non
  · have hw:w∈F 5:=by simpa only [pow_zero,one_apply_eq_self] using powers 0 pos
    have cw:C w∈F 5:=by simpa only [pow_one] using powers 1 (by omega)
    have wW:=sync w hw cw
    apply escapes
    change zeroSpace A 5≤W
    rw [base]
    exact (chain_le_iff _).mpr ⟨Uw,fun k _=>pow_mem wi wW k⟩
end
end RKCert.Paired.Seventeen
