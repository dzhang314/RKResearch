module
public import RKCert.Dirk17Ranks
public import RKCert.DirkWeightedFiveOriginal
@[expose] public section
namespace RKCert.Paired.Seventeen.Early
open Module Terminal RKCert.OneEscape RKCert.EndpointPhysical
variable {K:Type*} [Field K] [CharZero K] {A:Fin 23→Fin 23→K} {b:Vec K 23}

structure Budget (A:Fin 23→Fin 23→K) : Prop where
  origin : ∀j,A 0 j=0
  f3 : finrank K (zeroSpace A 3)=1
  f4 : finrank K (zeroSpace A 4)=2
  f5 : finrank K (zeroSpace A 5)=3∨finrank K (zeroSpace A 5)=4
  f6 : finrank K (zeroSpace A 6)=5
  f7 : finrank K (zeroSpace A 7)=6
  f8 : finrank K (zeroSpace A 8)=7
  f9 : finrank K (zeroSpace A 9)=8
  f10 : finrank K (zeroSpace A 10)=10
  e : ∀j,8≤j→j≤11→finrank K (treeSpace A j)=j+8
  e9_full : treeSpace A 9=LinearMap.range (polyEval A 8) ⊔zeroSpace A 9
  escapes : ∀j,8≤j→j≤11→¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j

theorem budget (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (anchor:q₂ (mat A) (nodes A) 1=0) (n4:finrank K (zeroSpace A 4)=2)
    (sur:4≤finrank K (marked A 17 5)) : Budget A:=by
  classical
  have E:excess A=0:=by simp [excess,anchor]
  have org:=dirk_first_row ha anchor
  let R:=Seventeen.ranks ha ho
  have n3:=R.three;have n5:=R.five;have n6:=R.six;have n7:=R.seven;have n8:=R.eight
  have lo9:=R.nine.1;have lo10:=R.ten.1;have e8:=R.e8
  rw [E] at n3 n5 n6 n7 n8 lo9 lo10 e8
  have pair (j:ℕ) (l:5≤j) (u:j≤8) :
      finrank K (treeSpace A (16-j))+finrank K (marked A 17 j)=23:=by
    have e:=marked_rank A 17 j
    change finrank K (treeSpace A (17-1-j))+finrank K (marked A 17 j)=23 at e
    exact e
  have grow(j:ℕ)(l:5≤j)(u:j≤7):finrank K (marked A 17 j)<finrank K (marked A 17 (j+1)):=
    Submodule.finrank_lt_finrank_of_lt (marked_strict ha ho (j:=j) (by omega) (by omega))
  have mark (j:ℕ)(l:5≤j)(u:j≤8):finrank K (marked A 17 j)=j-1:=by
    have p8:=pair 8 (by decide) (by decide)
    change finrank K (treeSpace A 8)+finrank K (marked A 17 8)=23 at p8
    have h5:=grow 5 (by decide) (by decide)
    have h6:=grow 6 (by decide) (by decide)
    have h7:=grow 7 (by decide) (by decide)
    change finrank K (marked A 17 5)<finrank K (marked A 17 6) at h5
    change finrank K (marked A 17 6)<finrank K (marked A 17 7) at h6
    change finrank K (marked A 17 7)<finrank K (marked A 17 8) at h7
    rcases (show j=5∨j=6∨j=7∨j=8 by omega) with rfl|rfl|rfl|rfl <;> omega
  have er (j:ℕ)(l:8≤j)(u:j≤11):finrank K (treeSpace A j)=j+8:=by
    have e:=pair (16-j) (by omega) (by omega)
    rw [show 16-(16-j)=j by omega,mark (16-j) (by omega) (by omega)] at e
    omega
  have escapeM (j:ℕ)(l:5≤j)(u:j≤8):¬(marked A 17 j).map (diag (mirror A))≤marked A 17 j:=by
    intro inv
    by_cases hj:j=8
    · subst j
      have inc:=ReverseHermite.full_incoming ha ho (j:=7) (by decide) inv
      rw [mark _ (by decide) (by decide),mark _ (by decide) (by decide)] at inc
      omega
    · have out:=ReverseHermite.full_outgoing ha ho (j:=j) (by omega) le_rfl inv
      rw [mark j l u,mark (j+1) (by omega) (by omega)] at out
      omega
  have escapes (j:ℕ) (l:8≤j)(u:j≤11):¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j:=by
    intro inv
    have dual:marked A 17 (16-j)=annih (treeSpace A j):=by
      change annih (treeSpace A (17-1-(16-j)))=_
      rw [show 17-1-(16-j)=j by omega]
    apply escapeM (16-j) (by omega) (by omega)
    rw [dual];rintro _ ⟨y,hy,rfl⟩
    apply mem_annih.mpr;intro x hx
    rw [row_flip_diag]
    apply mem_annih.mp hy
    have ex:diag (mirror A) x=x-diag (nodes A) x:=by ext i;simp [mirror,sub_mul]
    rw [ex]
    exact (treeSpace A j).sub_mem hx (inv (Submodule.mem_map_of_mem hx))
  have sep9:=poly_separated_delayed_first org ho (q:=8) (m:=9) (by decide) (by decide)
  have sep10:=poly_separated_delayed_first org ho (q:=7) (m:=10) (by decide) (by decide)
  have e9:=er 9 (by decide) (by decide)
  have e10:=er 10 (by decide) (by decide)
  have u9:9+finrank K (zeroSpace A 9)≤finrank K (treeSpace A 9):=treeSpace_rank_of_delayed (by decide:8≤9) sep9
  have u10:8+finrank K (zeroSpace A 10)≤finrank K (treeSpace A 10):=treeSpace_rank_of_delayed (by decide:7≤10) sep10
  exact ⟨org,by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega,er,
    poly_pure_full_of_paid_rank (by decide:8≤9) sep9 (by omega),escapes⟩

theorem ordinary_steps (R:Budget A) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) :
    ∀j:ℕ,6≤j→j≤9→¬(zeroSpace A j).map (diag (nodes A))≤zeroSpace A j:=by
  intro j lo hi inv
  have h:=dirk_forward_invariant_outgoing ha ho (j:=j) (by omega) (zeroSpace A j) le_rfl
    (fun _ m=>inv ⟨_,m,rfl⟩)
  have a:=R.f6;have d:=R.f7;have e:=R.f8;have f:=R.f9;have g:=R.f10
  rcases (show j=6∨j=7∨j=8∨j=9 by omega) with rfl|rfl|rfl|rfl
  · change finrank K (zeroSpace A 6)+3≤finrank K (zeroSpace A 7) at h;omega
  · change finrank K (zeroSpace A 7)+3≤finrank K (zeroSpace A 8) at h;omega
  · change finrank K (zeroSpace A 8)+4≤finrank K (zeroSpace A 9) at h;omega
  · change finrank K (zeroSpace A 9)+4≤finrank K (zeroSpace A 10) at h;omega

omit [CharZero K] in
theorem units (R:Budget A) (k:ℕ) (hk:k<3):
    finrank K (zeroSpace A (6+k+1))≤finrank K (zeroSpace A (6+k))+1:=by
  have a:=R.f6;have d:=R.f7;have e:=R.f8;have f:=R.f9
  rcases (show k=0∨k=1∨k=2 by omega) with rfl|rfl|rfl
  · change finrank K (zeroSpace A 7)≤finrank K (zeroSpace A 6)+1;omega
  · change finrank K (zeroSpace A 8)≤finrank K (zeroSpace A 7)+1;omega
  · change finrank K (zeroSpace A 9)≤finrank K (zeroSpace A 8)+1;omega

structure Heads (A:Fin 23→Fin 23→K) (U:Submodule K (Vec K 23)) (w:Vec K 23) (n:ℕ) : Prop where
  len : 0<n
  sum_rank : finrank K U+n=5
  inv : U.map (diag (nodes A))≤U
  core : U≤zeroSpace A 6
  normal : ∀a,Clock.fiber (nodes A) a w∈U→Clock.fiber (nodes A) a w=0
  band : ∀k≤3,zeroSpace A (6+k)=chain (diag (nodes A)) U w (n+k)

theorem heads (R:Budget A) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17):
    ∃U w n,Heads A U w n ∧
      ∀V:Submodule K (Vec K 23),V.map (diag (nodes A))≤V→V≤zeroSpace A 6→V≤U:=by
  obtain ⟨n,U,w,n0,iv,uc,max6,e6,_,_,rank,norm,_⟩:=Clock.ordinary_normal_head A 6
    (units R 0 (by decide)) (ordinary_steps R ha ho 6 (by decide) (by decide))
  have f6:=R.f6
  exact ⟨U,w,n,⟨n0,by omega,iv,uc,norm,Clock.ordinary_staircase iv n0 e6 (units R)
    (fun k hk=>ordinary_steps R ha ho (6+k) (by omega) (by omega))⟩,max6⟩

end RKCert.Paired.Seventeen.Early
