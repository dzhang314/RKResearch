module
public import RKCert.ERKEightEarlyPhysical
public import RKCert.ERKFiniteTail
public import RKCert.OrderTwelveOffMask

@[expose] public section
/-! # Actual even-order balance at exactly three times the midpoint

At the balanced count the original terminal coordinate is in the midpoint
tree space and not in the preceding tree space. Reverse ranks are therefore
different from naïvely deleting a stage. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.OrderTwelve RKCert.Endpoint Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s q:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

structure EvenBalanced (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) (q:ℕ) : Prop where
  separated : Separated A q
  lastLive : b (Fin.last s)≠0
  lastReflect : mirror A (Fin.last s)=0
  forwardMid : finrank K (zeroSpace A q)=q+1
  forwardPrev : finrank K (zeroSpace A (q-1))=q
  treeMid : finrank K (treeSpace A q)=2*q+2
  treePrev : finrank K (treeSpace A (q-1))=2*q
  seedZero : backSeed1 A b=0
  terminalIn : terminal (K:=K) s∈treeSpace A q
  terminalOut : terminal (K:=K) s∉treeSpace A (q-1)
  reverseMid : back A b (q-2)=annih (treeSpace A q)
  reversePrev : back A b (q-1)=annih (treeSpace A (q-1))⊓LinearMap.ker (LinearMap.proj (Fin.last s))
  forwardTerminalZero : ∀v∈zeroSpace A q,v (Fin.last s)=0

set_option maxHeartbeats 1400000 in
theorem balanced_even_ranks (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q))
    (hq:9≤q) (size:s+1=3*q) : EvenBalanced A b q := by
  classical
  have sep:Separated A q:=explicit_separated ha ho le_rfl (by omega)
  have lastLive:b (Fin.last s)≠0 := by
    intro hz
    have tr:=order_trim ha ho hz
    have cnt:=explicit_even_rank_floor_from_eight (trim_strict ha) tr (by omega)
    omega
  have seedEarly:=grade_eight_surplus_ordered ha ho (by omega)
  have R (d:ℕ) (lo:8≤d) (hi:d≤q) : d+1≤finrank K (zeroSpace A d) := by
    have h:=strict_rank_interval ha sep 8 (d-8) (by omega) (by omega)
    rw [show 8+(d-8)=d by omega] at h
    omega
  have forward_q:=R q (by omega) le_rfl
  have forward_prev:=R (q-1) (by omega) (by omega)
  have strict:=strict_rank_interval ha sep (q-1) 1 (by omega) (by omega)
  rw [show q-1+1=q by omega] at strict
  have treeQ:=tree_rank_eq ho sep (by omega)
  have treeP:=tree_rank_eq ho (sep.mono (show q-1≤q by omega)) (by omega)
  have count:=backward_count ha ho q (q-2) (by omega)
  have fQ:finrank K (zeroSpace A q)=q+1:=by omega
  have fP:finrank K (zeroSpace A (q-1))=q:=by omega
  have eQ:finrank K (treeSpace A q)=2*q+2:=by omega
  have eP:finrank K (treeSpace A (q-1))=2*q:=by omega
  have seed_zero:backSeed1 A b=0:=seed_zero_of_rank_zero (by omega)
  have no : ∀ i,Fin.last s < i →b i=0 := fun _ h=>False.elim ((not_lt_of_ge (Fin.le_last _)) h)
  have y0:=last_mirror_zero ha lastLive no seed_zero
  have bQ:back A b (q-2)=annih (treeSpace A q) := by
    apply Submodule.eq_of_le_of_finrank_le (back_annih ho q (q-2) (by omega))
    have a:=backward_exact_dim (treeSpace A q)
    have b:=back_finrank ha ho (q-2) (by omega)
    omega
  have tin : terminal (K:=K) s∈treeSpace A q := by
    apply row_annih_test
    intro v hv
    rw [←bQ] at hv
    rw [row_terminal]
    exact back_vanish ha lastLive no seed_zero _ hv _ le_rfl
  have cout:nodes A (Fin.last s)=1 := (sub_eq_zero.mp y0).symm
  have tout : terminal (K:=K) s∉treeSpace A (q-1) :=
    terminal_single_not_mem ha ho (by omega) _ lastLive cout
  let T := Submodule.span K {terminal (K:=K) s}
  let S := treeSpace A (q-1)⊔T
  have Srank : finrank K S=2*q+1 := by
    have ht : treeSpace A (q-1)⊓T=⊥ := by
      apply le_antisymm _ bot_le
      rintro v ⟨hv,ht⟩
      obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp ht
      have a0:a=0 := by
        by_contra an
        exact tout (((treeSpace A (q-1)).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr an)).mp hv)
      rw [a0,zero_smul]
      exact (⊥:Submodule K (Vec K (s+1))).zero_mem
    have k:=Submodule.finrank_sup_add_finrank_inf_eq (treeSpace A (q-1)) T
    rw [Submodule.finrank_eq_zero.mpr ht,add_zero,eP] at k
    change finrank K S=2*q+finrank K T at k
    rwa [show finrank K T=1 from finrank_span_singleton terminal_ne] at k
  have ann : annih S=annih (treeSpace A (q-1))⊓LinearMap.ker (LinearMap.proj (Fin.last s)) := by
    ext v
    constructor
    · intro hv
      refine ⟨mem_annih.mpr (fun u hu=>mem_annih.mp hv _ ((show treeSpace A (q-1)≤S from le_sup_left) hu)),?_⟩
      change v (Fin.last s)=0
      rw [←row_terminal v]
      exact mem_annih.mp hv _ ((show T≤S from le_sup_right) (Submodule.subset_span (Set.mem_singleton _)))
    · rintro ⟨hv,h0⟩
      apply mem_annih.mpr
      change S≤(row v).ker
      apply sup_le (mem_annih.mp hv)
      apply (Submodule.span_singleton_le_iff_mem ..).mpr
      change row v (terminal s)=0
      rw [row_terminal]
      exact h0
  have bP:back A b (q-1)=annih (treeSpace A (q-1))⊓LinearMap.ker (LinearMap.proj (Fin.last s)) := by
    rw [←ann]
    apply Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [ann]
      exact le_inf (back_annih ho (q-1) _ (by omega))
        (fun _ hw=>back_vanish ha lastLive no seed_zero _ hw _ le_rfl)
    · have ar:=backward_exact_dim S
      have br:=back_finrank ha ho (q-1) (by omega)
      omega
  have prev_zero (v:Vec K (s+1)) (hv:v∈zeroSpace A (q-1)) : v (Fin.last s)=0 := by
    have h:=zeroSpace_mul_treeSpace ho (by omega : q+1≤2*q) hv tin
    have z:=probe_zeroSpace ho (k:=0) (by omega) h
    change probe A b 0 (v*terminal s)=0 at z
    rw [mul_comm,terminal_mul,map_smul,smul_eq_mul] at z
    have bz:probe A b 0 (terminal s)=b (Fin.last s) := by
      rw [show probe A b 0 (terminal s)=row b (terminal s) by simp [probe],row_terminal]
    rw [bz] at z
    exact (mul_eq_zero.mp z).resolve_right lastLive
  have escape : ¬(zeroSpace A (q-1)).map (diag (nodes A))≤zeroSpace A (q-1) := by
    intro hinv
    have h:=forward_invariant_hermite_rank ha ho (j:=q-1) (by omega) (zeroSpace A (q-1)) le_rfl
      (fun _ hv=>hinv (Submodule.mem_map_of_mem hv))
    rw [show q-1+1=q by omega,fP,fQ] at h
    omega
  have Fstep:zeroSpace A q=zeroSpace A (q-1)⊔(zeroSpace A (q-1)).map (diag (nodes A)) := by
    have o:=Clock.ordinary_step (j:=q-1) (by rw [show q-1+1=q by omega,fQ,fP]) escape
    rwa [show q-1+1=q by omega] at o
  refine ⟨sep,lastLive,y0,fQ,fP,eQ,eP,seed_zero,tin,tout,bQ,bP,fun v hv=>?_⟩
  rw [Fstep] at hv
  obtain ⟨x,hx,_,⟨w,hw,rfl⟩,rfl⟩:=Submodule.mem_sup.mp hv
  simp [prev_zero x hx,prev_zero w hw]

end RKCert.Paired.FiniteMidpoint
