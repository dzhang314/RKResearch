module
public import RKCert.Dirk17Minimal
public import RKCert.DirkEightCoreCap
public import RKCert.DirkSynchronousFifth
public import RKCert.DirkSevenSynchronized
public import RKCert.DirkWeightedFiveOriginal
@[expose] public section
namespace RKCert.Paired.Seventeen
open Module Terminal RKCert.OneEscape RKCert.EndpointPhysical
variable {K:Type*} [Field K] [CharZero K] {A:Fin 23→Fin 23→K} {b:Vec K 23}
noncomputable section
set_option maxRecDepth 4000
/-- The actual minimal anchored reverse-rank chart is impossible over every
characteristic-zero field. The formerly exceptional free 3+2 quartic is
tested against its original physical support before the rank dispatch. -/
theorem no_minimal_charZero (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (anc:q₂ (mat A) (nodes A) 1=0)
    (budget:finrank K (marked A 17 5)≤3):False:=by
  classical
  let h:=minimal ha ho anc budget
  let F:=zeroSpace A
  let C:=diag (nodes A)
  let W:=jointWithOrigin A b 0
  have wi:W.map C≤W:=jointWithOrigin_invariant _
  have whole:W≤F 8:=minimal_joint_inside ha ho h
  have escapes:¬F 5≤W:=seventeen_five_visible ha ho whole wi
  obtain ⟨cap,z⟩:=minimal_seven_sites ha ho h anc
  have sync(v:Vec K 23)(hv:v∈F 5)(cv:C v∈F 5):v∈W:=
    jointWithOrigin_iff.mpr ⟨h.D.synchronous_fifth_seven ha ho cap z hv cv (h.zero _ hv),
      fun _=>zeroSpace_first_of_row h.origin 5 hv⟩
  have f4w:F 4≤W:=fun v hv=>sync v (zeroSpace_mono A (by decide:4≤5) hv) (diag_zeroSpace A 4 hv)
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
  obtain ⟨r,U,w,pos,ui,inc,_,base,powers,_,_,_,_⟩:=Clock.ordinary_normal_head A 5 (flat 0 (by decide)) (non 0 (by decide))
  have Uw:U≤W:=fun v hv=>sync v (inc hv) (inc (ui ⟨v,hv,rfl⟩))
  by_cases one:r=1
  · apply no_invariant_grade5_head ha ho (by decide) ui inc
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
