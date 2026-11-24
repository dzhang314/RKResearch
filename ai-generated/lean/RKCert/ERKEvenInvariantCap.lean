module
public import RKCert.ERKEvenBalancedRanks

@[expose] public section
/-! # Maximal pure core in a balanced even-order tableau -/

namespace RKCert.OneEscape
open RKCert.Paired Module
variable {K:Type*} [Field K] {s:ℕ} {T:Vec K s→ₗ[K]Vec K s}
variable {U W:Submodule K (Vec K s)} {v:Vec K s}

/-- More paid iterates than dimensions in the quotient force membership
in the maximal invariant core. No inner product is needed. -/
theorem belongs_to_maximal_core_of_many_iterates
    (inc:U≤W) (inv:U.map T≤U)
    (maximal:∀S:Submodule K (Vec K s),S.map T≤S→S≤W→S≤U)
    (m:ℕ) (paid:∀k<m,(T^k) v∈W) (few:finrank K W<finrank K U+m) : v∈U := by
  by_contra out
  have cover (k:ℕ) (hk:k≤m) : chain T U v k≤W :=
    (chain_le_iff k).mpr ⟨inc,fun i hi=>paid i (hi.trans_le hk)⟩
  have strict (k:ℕ) (hk:k<m) : chain T U v k<chain T U v (k+1) := by
    refine lt_of_le_of_ne (by exact le_sup_left) (fun eq=>?_ )
    have vm : v∈chain T U v (k+1) := by
      simpa only [pow_zero,one_apply_eq_self] using
        ((chain_le_iff (k+1)).mp le_rfl).2 0 (by omega)
    by_cases z:k=0
    · subst k
      have on : v∈chain T U v 0:=eq.symm ▸ vm
      exact out on
    have stable : (chain T U v k).map T≤chain T U v k := by
      have e:=chain_sup_map (w:=v) inv (Nat.pos_of_ne_zero z)
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

end RKCert.OneEscape

namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
section Ordered
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s q:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

theorem balanced_one_past_defect_cap (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q))
    (q8:8≤q) (size:s+1=3*q) : finrank K (zeroSpace A (q+1))≤q+3 := by
  classical
  let _ : DecidableEq K := Classical.decEq K
  have sep (a:Fin ((q-1)+1)→K) (h:polyEval A (q-1) a∈zeroSpace A (q+1)) : a=0 := by
    let P:=ofFn (q-1+1) a
    have deg := ofFn_natDegree_lt (by omega : 0<q-1+1) a
    rw [←evalNodes_ofFn A _ a] at h
    have z:=RKCert.OrderedGram.ordered_anchored_separation ha ho P (by dsimp [P];omega)
      (by dsimp [P];omega) h
    exact injective_ofFn _ (z.trans (ofFn_zero _).symm)
  have rank:=poly_band_rank_add sep
  have inc:polyBand A (q-1)⊔zeroSpace A (q+1)≤treeSpace A (q+1) :=
    sup_le (polyBand_le A (by omega)) (zeroSpace_le_treeSpace A _)
  have n:=Submodule.finrank_mono inc
  have back:=backward_count ha ho (q+1) (q-3) (by omega)
  omega

end Ordered

section Field
variable {K:Type*} [Field K] [CharZero K] {s q p:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

set_option maxHeartbeats 2200000 in
/-- The greatest clock-invariant subspace inside the ordinary midpoint has
dimension at most five; hence all invariant pure subspaces there do also. -/
theorem invariant_core_cap_of_rank (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (q8:8≤q) (pay:q+1≤p) (sep:Separated A q)
    (fmid:finrank K (zeroSpace A q)=q+1) (cap:finrank K (zeroSpace A (q+1))≤q+3)
    (V:Submodule K (Vec K (s+1))) (vi:V≤zeroSpace A q)
    (invV:V.map (diag (nodes A))≤V) : finrank K V≤5 := by
  let C:=diag (nodes A)
  let F:=zeroSpace A
  obtain ⟨k,_,plateau⟩:=exists_plateau C (F q)
  let U:=core C (F q) k
  let u:=finrank K U
  have Uin:U≤F q := fun _ hv=>by simpa only [pow_zero,one_apply_eq_self] using
    (mem_core.mp hv 0 (Nat.zero_le _))
  have Uinv:U.map C≤U:=invariant_of_plateau plateau
  have maxU (W:Submodule K (Vec K (s+1))) (hi:W.map C≤W) (hF:W≤F q) : W≤U :=
    invariant_le_core hF hi k
  have hV:=Submodule.finrank_mono (maxU V invV vi)
  suffices u≤5 by omega
  by_contra! large
  have uc1:=forward_invariant_hermite_rank ha ho (j:=q) (by omega) U Uin
    (fun _ hv=>Uinv (Submodule.mem_map_of_mem hv))
  change u+(q+1)/2≤finrank K (zeroSpace A (q+1)) at uc1
  have ub:u+1≤q := by omega
  have f5:=grade_five_surplus ha (sep.mono (by omega : 5≤q))
  have lower (j:ℕ) (lo:5≤j) (hi:j≤q) : j≤finrank K (F j) := by
    have g:=strict_rank_interval ha sep 5 (j-5) (by omega) (by omega)
    rw [show 5+(j-5)=j by omega] at g
    change j≤finrank K (zeroSpace A j)
    omega
  have upper (j:ℕ) (lo:1≤j) (hi:j≤q) : finrank K (F j)≤j+1 := by
    have g:=strict_rank_interval ha sep j (q-j) lo (by omega)
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
      have g:=forward_invariant_hermite_rank ha ho (j:=u-1) (by omega) (F (u-1))
        le_rfl (fun _ hv=>hc (Submodule.mem_map_of_mem hv))
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
  have h:=forward_invariant_hermite_rank ha ho (j:=u) (by omega) U mid
    (fun _ hv=>Uinv (Submodule.mem_map_of_mem hv))
  change u+(u+1)/2≤finrank K (F (u+1)) at h
  have r:=upper (u+1) (by omega) ub
  omega

end Field

/-- Convenience form for the physical even balance, including q=8. -/
theorem balanced_invariant_core_cap {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {s q:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q))
    (q8:8≤q) (size:s+1=3*q) (sep:Separated A q) (fmid:finrank K (zeroSpace A q)=q+1)
    (V:Submodule K (Vec K (s+1))) (vi:V≤zeroSpace A q)
    (invV:V.map (diag (nodes A))≤V) : finrank K V≤5 :=
  invariant_core_cap_of_rank ha ho q8 (by omega) sep fmid
    (balanced_one_past_defect_cap ha ho q8 size) V vi invV

end RKCert.Paired.FiniteMidpoint
