module
public import RKCert.ERKOrder13RemainingMarked
public import RKCert.ERKOrder13CleanProfiles
public import RKCert.ERKOrder13PencilPhysical
public import RKCert.ERKOrder13PencilCoordinates
public import RKCert.ERKOrder13PencilCoprime

@[expose] public section
/-! # Actual rank-two and all full fourth-defect-rank cases are impossible
This is a structural restriction on Fin19, not yet a 20-stage assertion. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint
  RKCert.OrderTwelve RKCert.Paired.TerminalSteering Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G P:K[X]}

theorem marked13_clean_pure_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    (alg:MulClosed U) (dis:∀i,Live U i→w i=0)
    (pn:P≠0) (pd:P.natDegree+r=a) (pf:P∣G)
    (rep:∀i,w i≠0→w i=P.eval (nodes A i)) : False := by
  rcases C.shape with rfl|⟨rfl,_⟩
  · obtain ⟨θ,u,v,τ,F,un,vn,_,an,fit,z0,z1,z2⟩:=
      marked13_filled_pair ha ho S M C alg dis pn pd pf rep
    obtain ⟨an,om,f₀,f₁⟩:=Pencil13.physical_pair_to_integer θ u v τ F un vn an fit z0 z1 z2
    exact Pencil13.no_common_tape u v un an om f₀ f₁
  · exact marked13_clean_alias_impossible ha S M C alg dis pn (by have:=C.marked.rTwo;omega) pf rep

theorem order13_fin19_forces_low_fourth_defect {A:Fin 19→Fin 19→K} {b:Vec K 19}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13) :
    finrank K (zeroSpace A 4)=3 ∧
      ∃ (a r:ℕ) (U:Submodule K (Vec K 19)) (w:Vec K 19) (G:K[X]),
        Chart13 A 1 a r U w G ∧ 3≤r∧r≤5 := by
  have S:=order13_actual_saturation ha ho
  have M:=order13_fin19_prefix_margin ha ho
  obtain ⟨a,r,U,w,G,C,cases⟩:=order13_fin19_remaining_marked ha ho
  have gn:G≠0 := by intro z;have d:=C.meshDegree;rw [z,natDegree_zero] at d;omega
  have lo:=zeroSpace_finrank ha ho (n:=3) (by decide)
  change 3≤finrank K (zeroSpace A 4) at lo
  have hi:=Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separated ha S.separated (j:=4) (by decide) (by decide))
  change finrank K (zeroSpace A 4)<finrank K (zeroSpace A 5) at hi
  rw [S.fRank 5 le_rfl (by decide)] at hi
  rcases cases with ⟨lr,ur⟩|⟨rfl,_,alg,dis,P,Q,fit,pd,_,rep⟩
  · have size : finrank K (zeroSpace A 4)=3 := by
      by_contra n
      have four:finrank K (zeroSpace A 4)=4 := by omega
      obtain ⟨v,P,Cv,alg,dis,pn,pf,pd,rep⟩:=marked13_four_clean_profile ha ho S M C lr four
      exact marked13_clean_pure_impossible ha ho S M Cv alg dis pn pd pf rep
    exact ⟨size,a,r,U,w,G,C,lr,ur⟩
  · have pn:P≠0 := fun pn=>gn (by rw [fit,pn,zero_mul])
    exact False.elim (marked13_clean_pure_impossible ha ho S M C alg dis pn
      (by have := C.width;omega) ⟨Q,fit⟩ rep)

end RKCert.Paired.FiniteMidpoint
