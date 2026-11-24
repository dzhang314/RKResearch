module
public import RKCert.ERKOddLocalDrop
public import RKCert.ERKOddLocalFeeder
public import RKCert.ERKFiveHiddenStaircase

@[expose] public section
/-! # Localized ordinary mask rank dispatch at the exact p17 boundary -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.OneEscape RKCert.Endpoint Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ:Vec K 26}{r:ℕ}{U:Submodule K (Vec K 26)}
noncomputable section

set_option maxHeartbeats 4000000 in
theorem LocalLinearBand.forward_mask_rank (B:LocalLinearBand A b r U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8):
    let K₀:=reverseHidden b τ U
    finrank K K₀=5 ∨ (r=2∧finrank K K₀=4∧K₀≤zeroSpace A 5∧finrank K (zeroSpace A 6)=7):=by
  let K₀:=reverseHidden b τ U
  let C:=diag (nodes A)
  let F:=zeroSpace A
  change finrank K K₀=5 ∨ (r=2∧finrank K K₀=4∧K₀≤F 5∧finrank K (F 6)=7)
  have mf:Monotone F:=fun _ _ h=>zeroSpace_mono A h
  have step(j:ℕ):(F j).map C≤F (j+1):=Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)
  have mK:K₀≤F 8:=B.hidden_pure ho
  have iK:K₀.map C≤K₀:=B.hidden_invariant
  have f3:2≤finrank K (F 3):=by
    have n:=strict_rank_interval ha S.separated 1 2 (by decide) (by decide)
    change finrank K (F 1)+2≤finrank K (F 3) at n
    omega
  have pay:=B.hidden_feeder ha ho
  change finrank K (F 3)+2≤finrank K K₀ at pay
  have low:4≤finrank K K₀:=by omega
  have cap:finrank K (F 9)≤11:=by
    have d:=S.nextCap
    change finrank K (F 9)+_≤11 at d
    omega
  obtain ⟨T,tF,tC,tmax⟩:=largest_invariant C (F 8)
  have KT:K₀≤T:=tmax K₀ mK iK
  have hi:finrank K T≤5:=
    invariant_core_cap_of_rank ha ho (by decide) (by decide) S.separated S.forwardMid cap T tF tC
  by_cases K5:finrank K K₀=5
  · exact Or.inl K5
  have K4:finrank K K₀=4:=by have s:=Submodule.finrank_mono KT;omega
  have f5:5≤finrank K (F 5):=S.forwardLow 5 (by decide) (by decide)
  have f6:finrank K (F 6)≤7:=S.forwardCap 6 (by decide) (by decide)
  have not5:¬F 5≤T:=by
    intro fT
    have h:=Submodule.finrank_mono fT
    have eq:F 5=T:=Submodule.eq_of_le_of_finrank_le fT (by omega)
    have H:=forward_invariant_hermite_rank ha ho (j:=5) (by decide) T eq.ge
      (fun v hv=>tC (Submodule.mem_map_of_mem hv))
    change finrank K T+3≤finrank K (F 6) at H
    omega
  let G (j:ℕ):Submodule K (Vec K 26):=F j⊔T
  have gb(j:ℕ)(a:5≤j)(b:j≤8):finrank K (G j)≤j+1:=by
    have u:=terminal_quotient_growth C F mf step tF tC tmax b (fun h=>not5 ((mf a).trans h))
    have v:finrank K (F 8)=9:=S.forwardMid
    change finrank K (G j)+ (8-j)≤finrank K (F 8) at u
    omega
  have gnew(j:ℕ)(a:5≤j)(b:j≤8):¬(G j).map C≤G j:=by
    intro step
    exact not5 ((mf a).trans (le_sup_left.trans (tmax _ (sup_le (mf b) tF) step)))
  have gn(j:ℕ):G j⊔(G j).map C≤G (j+1):=by
    refine sup_le (sup_le_sup_right (mf (by omega)) T) ?_
    change (F j⊔T).map C≤F (j+1)⊔T
    rw [Submodule.map_sup]
    exact sup_le ((step j).trans le_sup_left) (tC.trans le_sup_right)
  have h6 (p:K₀≤F 5):7≤finrank K (F 6):=by
    have u:=forward_invariant_hermite_rank ha ho (j:=5) (by decide) K₀ p
      (fun v hv=>iK (Submodule.mem_map_of_mem hv))
    change finrank K K₀+3≤finrank K (F 6) at u
    omega
  by_cases T5:finrank K T=5
  · have one:finrank K T=finrank K K₀+1:=by omega
    obtain ⟨a,off⟩:=extra_invariant_one_fiber KT one iK tC
      (fun v hv=>(mem_reverseHidden.mp hv).1)
    have ksite(j:ℕ)(p:j+r+1≤8):F j⊓T≤K₀:=by
      rintro v ⟨hV,hT⟩
      apply B.single_head_site_hidden ho p hV (a:=1-a)
      intro i ni
      exact off v hT i (fun z=>ni (by change 1-nodes A i=1-a;rw [z]))
    have J:F 5⊓T≤K₀:=ksite 5 (by rcases B.short with z|z <;> omega)
    have e:=Submodule.finrank_sup_add_finrank_inf_eq (F 5) T
    change finrank K (G 5)+finrank K ↥(F 5⊓T)=finrank K (F 5)+finrank K T at e
    have H:=gb 5 (by decide) (by decide)
    have i:F 5⊓T=K₀:=Submodule.eq_of_le_of_finrank_le J (by omega)
    have Ki:K₀≤F 5:=i.symm.le.trans inf_le_left
    have f:=h6 Ki
    have w:=gb 6 (by decide) (by decide)
    have FG:F 6=G 6:=Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    have Tin:T≤F 6:=le_sup_right.trans FG.ge
    have rr:r=2:=by
      rcases B.short with z|z
      · have ex:T≤K₀:=le_trans (le_inf Tin le_rfl) (ksite 6 (by omega))
        have p:=Submodule.finrank_mono ex
        omega
      · exact z
    exact Or.inr ⟨rr,K4,Ki,by omega⟩
  have T4:finrank K T=4:=by have h:=Submodule.finrank_mono KT;omega
  have T_eq:K₀=T:=Submodule.eq_of_le_of_finrank_le KT (by omega)
  have GP(j:ℕ)(jl:5≤j)(jp:j+r+1≤8)(gd:finrank K (G j)=j+1):False:=by
    have nz:=gnew j jl (by omega)
    have nr:finrank K ↥(G j⊔(G j).map C)≤finrank K (G j)+1:=by
      have c:=Submodule.finrank_mono (gn j)
      have d:=gb (j+1) (by omega) (by omega)
      omega
    obtain ⟨m,V,w,_,Vin,Vj,VM,_,pw,last,rv⟩:=single_head nr nz
    have VT:V≤T:=tmax V (Vj.trans (sup_le (mf (by omega)) tF)) Vin
    have TV:T≤V:=VM T tC le_sup_right
    have ve:V=K₀:=(le_antisymm VT TV).trans T_eq.symm
    have d:m=j-3:=by rw [ve,K4,gd] at rv;omega
    have hw:w∈K₀:=by
      apply B.same_grade_refund ha ho jl jp
      intro k hk
      change (C^k) w∈F j⊔K₀
      rw [T_eq]
      exact pw k (by omega)
    have ht:w∈T:=T_eq ▸ hw
    exact last ((show T≤G j from le_sup_right) (pow_mem tC ht m))
  by_cases G6:finrank K (G 5)=6
  · exact False.elim (GP 5 (by decide) (by rcases B.short with z|z <;> omega) G6)
  have G5:finrank K (G 5)=5:=by
    have h:=Submodule.finrank_mono (show F 5≤G 5 from le_sup_left)
    have e:=gb 5 (by decide) (by decide)
    omega
  have fe:F 5=G 5:=Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
  have Ki:K₀≤F 5:=KT.trans (le_sup_right.trans fe.ge)
  have rr:r=2:=by
    rcases B.short with o|o
    · have S6:=h6 Ki
      have G7:finrank K (G 6)=7:=by
        have u:=Submodule.finrank_mono (show F 6≤G 6 from le_sup_left)
        have d:=gb 6 (by decide) (by decide)
        omega
      exact False.elim (GP 6 (by decide) (by omega) G7)
    · exact o
  exact Or.inr ⟨rr,K4,Ki,by have n:=h6 Ki;omega⟩
end
end RKCert.Paired.ReverseHull

