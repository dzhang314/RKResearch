module

public import RKCert.ReviewedNative.NativeFlatClockHead
public import RKCert.ReviewedNative.ERKGradeFiveSurplus

@[expose] public section

/-! # Five-dimensional cap on a tight midpoint clock core

Native Hermite rank growth caps every invariant subspace in a
separated tight forward midpoint, independently of any physical
carrier or reverse case split. -/
namespace RKResearch.Certified.Graded
open Module RKCert.OneEscape

variable {K : Type*} [Field K] {s q : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

set_option maxRecDepth 3500
set_option maxHeartbeats 750000

section Iterates
variable {T : (Fin s→K) →ₗ[K] (Fin s→K)}
variable {U W : Submodule K (Fin s→K)} {v : Fin s→K}

/-- More paid iterates than dimensions in the quotient force membership
in the maximal invariant core. No inner product is needed. -/
theorem belongs_to_maximal_core_of_many_iterates
    (inc:U≤W) (inv:U.map T≤U)
    (maximal:∀S:Submodule K ((Fin s→K)),S.map T≤S→S≤W→S≤U)
    (m:ℕ) (paid:∀k<m,(T^k) v∈W) (few:finrank K W<finrank K U+m) : v∈U := by
  by_contra out
  have cover (k:ℕ) (hk:k≤m) : chain T U v k≤W :=
    (clock_chain_le_iff k).mpr ⟨inc,fun i hi=>paid i (hi.trans_le hk)⟩
  have strict (k:ℕ) (hk:k<m) : chain T U v k<chain T U v (k+1) := by
    refine lt_of_le_of_ne (by exact le_sup_left) (fun eq=>?_ )
    have vm : v∈chain T U v (k+1) := by
      simpa only [pow_zero,one_apply_eq_self] using
        ((clock_chain_le_iff (k+1)).mp le_rfl).2 0 (by omega)
    by_cases z:k=0
    · subst k
      have on : v∈chain T U v 0:=eq.symm ▸ vm
      exact out on
    have stable : (chain T U v k).map T≤chain T U v k := by
      have e:=clock_chain_next (w:=v) inv (Nat.pos_of_ne_zero z)
      exact le_sup_right.trans (le_of_eq (e.trans eq.symm))
    exact out (maximal _ stable (cover k hk.le) (eq.symm ▸ vm))
  have R (k:ℕ) (hk:k≤m) : finrank K U+k≤finrank K (chain T U v k) := by
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have d:=Submodule.finrank_lt_finrank_of_lt (strict k (by omega))
      have h:=ih (by omega)
      omega
  exact (not_le_of_gt few) ((R m le_rfl).trans (Submodule.finrank_mono (cover m le_rfl)))

end Iterates

variable [CharZero K]

/-- The greatest clock-invariant subspace inside the ordinary midpoint has
dimension at most five; hence all invariant pure subspaces there do also. -/
theorem invariant_core_cap_of_rank (ha : ∀ i j,i≤j → A i j=0) (q8 : 8≤q)
    (sep : ∀ a, coeffEval A q a∈zeroSpace A q → a=0)
    (fmid:finrank K (zeroSpace A q)=q+1) (cap:finrank K (zeroSpace A (q+1))≤q+3)
    (V:Submodule K ((Fin s→K))) (vi:V≤zeroSpace A q)
    (invV:V.map (diag (nodes A))≤V) : finrank K V≤5 := by
  let C:=diag (nodes A)
  have ps : PolySeparated A q := PolySeparated.of_coeff sep
  let F:=zeroSpace A
  obtain ⟨k,_,plateau⟩:=exists_plateau C (F q)
  let U:=core C (F q) k
  let u:=finrank K U
  have Uin:U≤F q := fun _ hv=>by simpa only [pow_zero,one_apply_eq_self] using
    (mem_core.mp hv 0 (Nat.zero_le _))
  have Uinv:U.map C≤U:=invariant_of_plateau plateau
  have maxU (W:Submodule K ((Fin s→K))) (hi:W.map C≤W) (hF:W≤F q) : W≤U :=
    invariant_le_core hF hi k
  have hV:=Submodule.finrank_mono (maxU V invV vi)
  suffices u≤5 by omega
  by_contra! large
  have uc1:=clock_invariant_outgoing ha ps Uin Uinv
  change u+(q+1)/2≤finrank K (zeroSpace A (q+1)) at uc1
  have ub:u+1≤q := by omega
  have f5:=grade_five_surplus ha (ps.mono (by omega : 5≤q))
  have lower (j:ℕ) (lo:5≤j) (hi:j≤q) : j≤finrank K (F j) := by
    have g:=zeroSpace_rank_interval_of_separation ha sep (j:=5) (d:=j-5) (by omega) (by omega)
    rw [show 5+(j-5)=j by omega] at g
    change j≤finrank K (zeroSpace A j)
    omega
  have upper (j:ℕ) (lo:1≤j) (hi:j≤q) : finrank K (F j)≤j+1 := by
    have g:=zeroSpace_rank_interval_of_separation ha sep (j:=j) (d:=q-j) lo (by omega)
    rw [show j+(q-j)=q by omega,fmid] at g
    change finrank K (zeroSpace A j)≤j+1
    omega
  have prev : F (u-1)≤U := by
    intro v hv
    apply belongs_to_maximal_core_of_many_iterates Uin Uinv maxU (q-(u-1)+1)
    · intro l hl
      have step (d:ℕ) : (C^d) v∈F (u-1+d) := by
        induction d with
        | zero => simpa only [pow_zero,one_apply_eq_self,Nat.add_zero] using hv
        | succ d ih =>
          rw [pow_succ',mul_apply_eq_comp,show u-1+(d+1)=u-1+d+1 by omega]
          exact diag_zeroSpace A _ ih
      exact zeroSpace_mono A (by omega) (step l)
    · change finrank K (zeroSpace A q)<u+(q-(u-1)+1)
      rw [fmid]
      omega
  have mid : U≤F u := by
    by_cases e:finrank K (F (u-1))=u
    · have eq:=Submodule.eq_of_le_of_finrank_le prev (by change u≤_;omega)
      exact eq ▸ zeroSpace_mono A (by omega : u-1≤u)
    have low:=lower (u-1) (by omega) (by omega)
    have up:=upper (u-1) (by omega) (by omega)
    have d:finrank K (F (u-1))=u-1:=by omega
    have out:¬(F (u-1)).map C≤F (u-1) := by
      intro hc
      have g:=clock_invariant_outgoing ha
        (ps.mono (by omega : u-1≤q)) (U:=F (u-1)) le_rfl hc
      change finrank K (F (u-1))+(u-1+1)/2≤finrank K (F (u-1+1)) at g
      rw [show u-1+1=u by omega,d] at g
      have r:=upper u (by omega) (by omega)
      omega
    let J:=F (u-1)⊔(F (u-1)).map C
    have ji:J≤U:=sup_le prev ((Submodule.map_mono prev).trans Uinv)
    have jl:F (u-1)<J:=lt_of_le_of_ne le_sup_left
      (fun eq=>out (le_sup_right.trans (le_of_eq eq.symm)))
    have jR:=Submodule.finrank_lt_finrank_of_lt jl
    have eq:=Submodule.eq_of_le_of_finrank_le ji (by change u≤_;omega)
    have jp:J≤F u:=by
      apply sup_le (zeroSpace_mono A (by omega))
      have p:=Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A (u-1))
      rwa [show u-1+1=u by omega] at p
    exact eq ▸ jp
  have h:=clock_invariant_outgoing ha (ps.mono (by omega : u≤q)) mid Uinv
  change u+(u+1)/2≤finrank K (F (u+1)) at h
  have r:=upper (u+1) (by omega) ub
  omega

end RKResearch.Certified.Graded
