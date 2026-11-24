module
public import RKCert.DirkEvenCore
public import RKCert.DirkNineShortHeads
@[expose] public section
namespace RKCert.Paired.Terminal
open Module RKCert.OneEscape
variable {K:Type*} [Field K] [CharZero K] {s p ε:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}

/-- A common H9 core-rank fork. The input invariant W need only contain
the genuine F4 and sit in F9; no algebra, rank, or product property of
W is needed. Exact middle grades 6,7,8 come from the grade-six payment
and strictness, which avoids a variable degree/codimension argument. -/
theorem nine_rank_dispatch (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (hp:14≤p)
    (f3:1+ε≤finrank K (zeroSpace A 3)) (f5:finrank K (zeroSpace A 5)≤4+ε)
    (f6:5+ε≤finrank K (zeroSpace A 6)) (f9:finrank K (zeroSpace A 9)=8+ε)
    (f10:finrank K (zeroSpace A 10)≤10+ε) {W:Submodule K (Vec K s)}
    (low:zeroSpace A 4≤W) (high:W≤zeroSpace A 9) (iw:W.map (diag (nodes A))≤W) :
    finrank K (zeroSpace A 4)=2+ε ∧ finrank K (zeroSpace A 5)=4+ε ∧
    ∃U:Submodule K (Vec K s), ∃w:Vec K s, ∃r:ℕ,(r=1∨r=2) ∧
      U.map (diag (nodes A))≤U ∧ W≤U ∧
      ∀k≤4,zeroSpace A (5+k)=chain (diag (nodes A)) U w (r+k) :=by
  classical
  let F:=zeroSpace A
  let C:=diag (nodes A)
  have g (a n:ℕ)(lo:2≤a)(h:a≤n)(hi:n≤10) : finrank K (F a)+(n-a)≤finrank K (F n):=
    flag_gain ha ho lo h (by omega)
  have rk(j:ℕ)(a:6≤j)(b:j≤9):finrank K (F j)=j-1+ε:=by
    have h:=g 6 j (by decide) a (by omega)
    have h':=g j 9 (by omega) b (by decide)
    change 5+ε≤finrank K (F 6) at f6;change finrank K (F 9)=8+ε at f9
    omega
  obtain ⟨U,um,ui,maximum⟩:=largest_invariant C (F 9)
  have vsub:W≤U:=maximum W high iw
  have f4U:F 4≤U:=low.trans vsub
  have quota (j:ℕ) (paid:j≤9) (esc:¬F j≤U):finrank K (F j ⊔ U : Submodule K (Vec K s))+(9-j)≤finrank K (F 9):=
    terminal_quotient_growth C F (fun _ _ h=>zeroSpace_mono A h)
      (fun j=>Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)) um ui maximum paid esc
  have grow (j:ℕ) (room:j≤9) (inc:U≤F j):finrank K U+j/2≤finrank K (F (j+1)):=
    dirk_forward_invariant_outgoing ha ho (j:=j) (by omega) U inc (fun v hv=>ui ⟨v,hv,rfl⟩)
  have u6:finrank K U≤6+ε:=by
    have q:=grow 9 (by decide) um
    change finrank K U+4≤finrank K (zeroSpace A 10) at q;omega
  have esc7:¬F 7≤U:=by
    intro inU
    have d:finrank K (F 7)=6+ε:=rk 7 (by decide) (by decide)
    have eq:F 7=U:=Submodule.eq_of_le_of_finrank_le inU (by omega)
    have iv:(F 7).map C≤F 7:=eq ▸ ui
    have q:=dirk_forward_invariant_incoming ha ho (j:=7) (by omega) (fun v hv=>iv ⟨v,hv,rfl⟩)
    change finrank K (F 6)+3≤finrank K (F 7) at q
    have p':finrank K (F 6)=5+ε:=rk 6 (by decide) (by decide)
    omega
  have early (j:ℕ) (paid:j≤9) (exactPay:finrank K (F j)+(9-j)=finrank K (F 9))
      (esc:¬F j≤U):U≤F j:=by
    have cap:=quota j paid esc
    have equal:F j=F j⊔U:=Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    exact le_sup_right.trans equal.ge
  have u7:U≤F 7:=early 7 (by decide) (by have:=rk 7 (by decide) (by decide);change finrank K (F 9)=8+ε at f9;omega) esc7
  have u4:finrank K U≤4+ε:=by
    have q:=grow 7 (by decide) u7;change finrank K U+3≤finrank K (F 8) at q
    have h:=rk 8 (by decide) (by decide);omega
  have esc6:¬F 6≤U:=by
    intro e;have q:=Submodule.finrank_mono e;have h:=rk 6 (by decide) (by decide);omega
  have in6:U≤F 6:=early 6 (by decide) (by have:=rk 6 (by decide) (by decide);change finrank K (F 9)=8+ε at f9;omega) esc6
  have small:finrank K U≤3+ε:=by
    have q:=grow 6 (by decide) in6;change finrank K U+3≤finrank K (F 7) at q
    have h:=rk 7 (by decide) (by decide);omega
  change 1+ε≤finrank K (F 3) at f3;change finrank K (F 5)≤4+ε at f5
  have g34:=g 3 4 (by decide) (by decide) (by decide)
  have g45:=g 4 5 (by decide) (by decide) (by decide)
  have f4n:finrank K (F 4)=2+ε:=by
    by_contra ne
    have e:F 4=U:=Submodule.eq_of_le_of_finrank_le f4U (by omega)
    have q:=grow 4 (by decide) e.ge;change finrank K U+2≤finrank K (F 5) at q
    have b:=Submodule.finrank_mono f4U;omega
  have f5n:finrank K (F 5)=4+ε:=by
    by_contra ne
    have eq:finrank K (F 5)=3+ε:=by omega
    have out4:¬(F 4).map C≤F 4:=by
      intro inv
      have q:=dirk_forward_invariant_outgoing ha ho (j:=4) (by omega) (F 4) le_rfl (fun x hx=>inv ⟨x,hx,rfl⟩)
      change finrank K (F 4)+2≤finrank K (F 5) at q;omega
    have join:=Clock.ordinary_step (A:=A) (j:=4) (by change finrank K (F 5)≤finrank K (F 4)+1;omega) out4
    have jp:F 5=F 4 ⊔ (F 4).map C:=join
    have f5u:F 5≤U:=by rw [jp];exact sup_le f4U ((Submodule.map_mono f4U).trans ui)
    have e:F 5=U:=Submodule.eq_of_le_of_finrank_le f5u (by omega)
    have iv:(F 5).map C≤F 5:=e ▸ ui
    have q:=dirk_forward_invariant_incoming ha ho (j:=5) (by omega) (fun v hv=>iv ⟨v,hv,rfl⟩)
    change finrank K (F 4)+2≤finrank K (F 5) at q;omega
  have esc5:¬F 5≤U:=by intro e;have h:=Submodule.finrank_mono e;omega
  have in5:U≤F 5:=early 5 (by decide) (by change finrank K (F 9)=8+ε at f9;omega) esc5
  have flat(k:ℕ)(hk:k<4):finrank K (F (5+k+1))≤finrank K (F (5+k))+1:=by
    by_cases h:k=0
    · subst k;change finrank K (F 6)≤finrank K (F 5)+1
      have d:=rk 6 (by decide) (by decide);omega
    · have a:=rk (5+k) (by omega) (by omega);have b:=rk (5+k+1) (by omega) (by omega);omega
  have non(k:ℕ)(hk:k<4):¬(F (5+k)).map C≤F (5+k):=by
    intro inv
    have q:=dirk_forward_invariant_outgoing ha ho (j:=5+k) (by omega) (F (5+k)) le_rfl (fun v hv=>inv ⟨v,hv,rfl⟩)
    change finrank K (F (5+k))+(5+k)/2≤finrank K (F (5+k+1)) at q
    have a:=flat k hk;omega
  obtain ⟨r,V,w,pos,vi,vf,max5,base,_,_,dim,_,_⟩:=Clock.ordinary_normal_head A 5 (flat 0 (by decide)) (non 0 (by decide))
  have eqVU:V=U:=le_antisymm (maximum V (vf.trans (zeroSpace_mono A (by decide:5≤9))) vi) (max5 U ui in5)
  subst V
  have dim4:=Submodule.finrank_mono f4U
  change finrank K (F 5)=finrank K U+r at dim
  have short:r=1∨r=2:=by omega
  exact ⟨f4n,f5n,U,w,r,short,ui,vsub,Clock.ordinary_staircase ui pos base flat non⟩

end RKCert.Paired.Terminal
