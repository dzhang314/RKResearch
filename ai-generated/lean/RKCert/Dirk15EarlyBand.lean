module
public import RKCert.Dirk15NativeReverse
public import RKCert.Dirk15OrdinaryCore
public import RKCert.DirkPaidTailDual
public import RKCert.DirkWeightedFiveOriginal
@[expose] public section
namespace RKCert.Paired.EarlyFifteen
open Module RKCert.OneEscape Terminal
variable {K:Type*} [Field K] [CharZero K] {A:Fin 20→Fin 20→K} {b:Vec K 20}

structure Budget (A:Fin 20→Fin 20→K) : Prop where
  first : ∀ j,A 0 j=0
  f3 : finrank K (zeroSpace A 3)=1
  f6 : finrank K (zeroSpace A 6)=5
  f7 : finrank K (zeroSpace A 7)=6
  f8 : finrank K (zeroSpace A 8)=7
  e : ∀ j,7≤j→j≤10→finrank K (treeSpace A j)=j+7
  e8 : treeSpace A 8=LinearMap.range (polyEval A 7) ⊔zeroSpace A 8
  escapes : ∀ j,7≤j→j≤10→¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j

theorem budget (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 15)
    (h0:q₂ (mat A) (nodes A) 1=0) (hm:3≤finrank K (marked A 15 4)) : Budget A:=by
  let ini:=order15_anchored_rank_chart ha ho h0
  have mr (j:ℕ) (lo:4≤j) (hi:j≤7):finrank K (marked A 15 j)=j-1:=
    order15_early_marked_ranks ha ho h0 hm lo hi
  have er (j:ℕ)(lo:7≤j)(hi:j≤10):finrank K (treeSpace A j)=j+7:=by
    have total:=marked_rank A 15 (14-j)
    change finrank K (treeSpace A (15-1-(14-j)))+finrank K (marked A 15 (14-j))=20 at total
    rw [show 15-1-(14-j)=j by omega,mr _ (by omega) (by omega)] at total
    omega
  have escape (j:ℕ)(lo:7≤j)(hi:j≤10):¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j:=by
    intro inv
    have m:marked A 15 (14-j)=annih (treeSpace A j):=by
      change annih (treeSpace A (15-1-(14-j)))=_
      rw [show 15-1-(14-j)=j by omega]
    have invM:(marked A 15 (14-j)).map (diag (mirror A))≤marked A 15 (14-j):=by
      rw [m];rintro _ ⟨y,hy,rfl⟩
      apply mem_annih.mpr;intro x hx
      rw [row_flip_diag]
      apply mem_annih.mp hy
      have eq : diag (mirror A) x=x-diag (nodes A) x := by
        ext i
        simp [mirror,sub_mul]
      rw [eq]
      exact (treeSpace A j).sub_mem hx (inv (Submodule.mem_map_of_mem hx))
    have one (k:ℕ)(a:4≤k)(h:k≤6):finrank K (marked A 15 (k+1))≤finrank K (marked A 15 k)+1:=by
      rw [mr _ (by omega) (by omega),mr _ (by omega) (by omega)];omega
    exact order15_full_marked_escape_of_unit ha ho one (14-j) (by omega) (by omega) invM
  have b8:=er 8 (by decide) (by decide)
  have f78:=Submodule.finrank_lt_finrank_of_lt (dirk_zeroSpace_lt_succ ha ho (j:=7) (by decide) (by decide))
  change finrank K (zeroSpace A 7)<finrank K (zeroSpace A 8) at f78
  have sep:=poly_separated_delayed_first ini.first_zero ho (q:=7) (m:=8) (by decide) (by decide)
  have pay:8+finrank K (zeroSpace A 8)≤finrank K (treeSpace A 8):=
    treeSpace_rank_of_delayed (by decide:7≤8) sep
  have f8:finrank K (zeroSpace A 8)=7:=by have f7:=ini.f7;omega
  exact ⟨ini.first_zero,ini.f3,ini.f6,ini.f7,f8,er,
    poly_pure_full_of_paid_rank (by decide:7≤8) sep (by omega),escape⟩

theorem f6_escape (B:Budget A) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 15) :
    ¬(zeroSpace A 6).map (diag (nodes A))≤zeroSpace A 6:=by
  intro inv
  have g:=dirk_forward_invariant_outgoing ha ho (j:=6) (by decide) (zeroSpace A 6) le_rfl
    (fun _ h=>inv ⟨_,h,rfl⟩)
  change finrank K (zeroSpace A 6)+3≤finrank K (zeroSpace A 7) at g
  have h:=B.f6;have h':=B.f7;omega

theorem f7_escape (B:Budget A) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 15) :
    ¬(zeroSpace A 7).map (diag (nodes A))≤zeroSpace A 7:=by
  intro inv
  have g:=dirk_forward_invariant_outgoing ha ho (j:=7) (by decide) (zeroSpace A 7) le_rfl
    (fun _ h=>inv ⟨_,h,rfl⟩)
  change finrank K (zeroSpace A 7)+3≤finrank K (zeroSpace A 8) at g
  have h:=B.f7;have h':=B.f8;omega

structure Heads (A:Fin 20→Fin 20→K) (U:Submodule K (Vec K 20)) (w:Vec K 20) (r:ℕ) : Prop where
  len : 3≤r
  small : finrank K U≤2
  rank_sum : finrank K U+r=5
  inv : U.map (diag (nodes A))≤U
  core : U≤zeroSpace A 6
  normal : ∀ a, Clock.fiber (nodes A) a w∈U→Clock.fiber (nodes A) a w=0
  band : ∀ k≤2,zeroSpace A (6+k)=chain (diag (nodes A)) U w (r+k)

theorem heads (B:Budget A) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 15) :
    ∃U w r,Heads A U w r:=by
  have f6:=B.f6;have f7:=B.f7;have f8:=B.f8
  have tiny:finrank K (zeroSpace A 7)≤finrank K (zeroSpace A 6)+1:=by omega
  obtain ⟨r,U,w,pos,iv,uf,max6,eq6,_,_,dim,norm,_⟩:=
    Clock.ordinary_normal_head A 6 tiny (f6_escape B ha ho)
  have max7:MaximalClockCore A 7 U:=by
    refine ⟨uf.trans (zeroSpace_mono A (by decide)),iv,?_⟩
    intro W wf wi
    have bound:=dirk_forward_invariant_outgoing ha ho (j:=7) (by decide) W wf
      (fun v h=>wi ⟨v,h,rfl⟩)
    change finrank K W+3≤finrank K (zeroSpace A 8) at bound
    have out:¬zeroSpace A 6≤W:=by
      intro h;have d:=Submodule.finrank_mono h;omega
    -- Invariance plus the earned unit gain places W already inside F6.
    have g:((zeroSpace A 6)⊔W).map (diag (nodes A))≤zeroSpace A 7:=by
      rw [Submodule.map_sup]
      exact sup_le (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 6)) (wi.trans wf)
    have le7:zeroSpace A 6⊔W≤zeroSpace A 7:=sup_le (zeroSpace_mono A (by decide)) wf
    have le6:zeroSpace A 6⊔W=zeroSpace A 6:=by
      by_contra ne
      have sl:=Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (le_sup_left:zeroSpace A 6≤zeroSpace A 6⊔W)
        (fun h=>ne h.symm))
      have h:zeroSpace A 6⊔W=zeroSpace A 7:=Submodule.eq_of_le_of_finrank_le le7 (by omega)
      exact f7_escape B ha ho (h ▸ g)
    exact max6 W wi (le_sup_right.trans le6.le)
  obtain ⟨_,k3,H⟩:=order15_ordinary_core_rank ha ho (e:=0) (by simpa using B.f3)
    (by simpa using B.f6) (by simpa using B.f7) U max7
  have k2:finrank K U≤2:=by
    by_contra! no
    have cut:finrank K U=3+0:=by omega
    obtain ⟨uf5,f5⟩:=H cut
    have esc5:¬(zeroSpace A 5).map (diag (nodes A))≤zeroSpace A 5:=by
      intro inv
      have g:=dirk_forward_invariant_outgoing ha ho (j:=5) (by decide) (zeroSpace A 5) le_rfl
        (fun v h=>inv ⟨v,h,rfl⟩)
      change finrank K (zeroSpace A 5)+2≤finrank K (zeroSpace A 6) at g
      omega
    have one:finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 5)+1:=by omega
    obtain ⟨q,V,z,_qpos,vi,vf,max5,eq5,_,_,d5⟩:=
      Clock.ordinary_single_head A 5 one esc5
    have same:V=U:=le_antisymm (max6 V vi (vf.trans (zeroSpace_mono A (by decide)))) (max5 U iv uf5)
    subst V
    have e:q=1:=by omega
    subst q
    have caps (k:ℕ) (hk:k<2):finrank K (zeroSpace A (5+k+1))≤finrank K (zeroSpace A (5+k))+1:=by
      rcases (show k=0∨k=1 by omega) with rfl|rfl
      · exact one
      · exact tiny
    have esc (k:ℕ) (hk:k<2):¬(zeroSpace A (5+k)).map (diag (nodes A))≤zeroSpace A (5+k):=by
      rcases (show k=0∨k=1 by omega) with rfl|rfl
      · exact esc5
      · exact f6_escape B ha ho
    exact no_invariant_grade5_head ha ho (by decide) iv uf5
      (Clock.ordinary_staircase iv (by decide) eq5 caps esc)
  have caps (k:ℕ) (hk:k<2):finrank K (zeroSpace A (6+k+1))≤finrank K (zeroSpace A (6+k))+1:=by
    rcases (show k=0∨k=1 by omega) with rfl|rfl
    · exact tiny
    · change finrank K (zeroSpace A 8)≤finrank K (zeroSpace A 7)+1
      omega
  have esc (k:ℕ) (hk:k<2):¬(zeroSpace A (6+k)).map (diag (nodes A))≤zeroSpace A (6+k):=by
    rcases (show k=0∨k=1 by omega) with rfl|rfl
    · exact f6_escape B ha ho
    · exact f7_escape B ha ho
  have stack:=Clock.ordinary_staircase iv pos eq6 caps esc
  exact ⟨U,w,r,by omega,k2,by omega,iv,uf,norm,stack⟩
end RKCert.Paired.EarlyFifteen
