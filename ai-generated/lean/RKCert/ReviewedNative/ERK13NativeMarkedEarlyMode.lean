module

public import RKCert.ReviewedNative.ERK13NativeMarkedPrefixPort

import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The exact initial extra mode when the terminal is already in E7

Its coefficient is the actual last-row value in F7. The statement does
not say the rank-eight case is impossible, and does not replace it by a
pure head. Normalization of the one polynomial is independent of the
local port or the chosen matching vector. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape MarkedAdjacent
open scoped Matrix Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w x : Fin 19 → K} {r a : ℕ} {G : K[X]}

/-- Early literal mark times an F5 column is paid in actual F12. -/
theorem early_terminal_zeroSpace_five_last (ho : HasOrder 13 A b)
    (L : LastActive b (Fin.last 18))
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7)
    (hx : x∈zeroSpace A 5) : x (Fin.last 18)=0 := by
  have prod := zeroSpace_mul_treeSpace ho (m:=5) (n:=7) (by decide) hx early
  have eq : x*coordinate (K:=K) (Fin.last 18)=
      x (Fin.last 18) • coordinate (K:=K) (Fin.last 18) := by
    ext i
    by_cases h : i=Fin.last 18
    · subst i
      simp [coordinate,smul_eq_mul]
    · have off : coordinate (K:=K) (Fin.last 18) i = 0 :=
        @Pi.single_eq_of_ne (Fin 19) (fun _ => K) _ (Classical.decEq _) (Fin.last 18) i h 1
      simp only [Pi.mul_apply, Pi.smul_apply, off, mul_zero, smul_zero]
  rw [eq] at prod
  by_contra nz
  exact last_coordinate_not_defect ho (j:=12) L (by decide)
    (((zeroSpace A 12).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr nz)).mp prod)

theorem NativeMarkedEscapeChart.early_head_last_zero
    (H : NativeMarkedEscapeChart A b a G r U w) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7)
    {n : ℕ} (hx : x∈escapeHeadBand A U w n) : x (Fin.last 18)=0 := by
  let V := LinearMap.ker (LinearMap.proj (Fin.last 18) : (Fin 19→K) →ₗ[K] K)
  have last0 {v : Fin 19→K} (hv : v∈zeroSpace A 5) : v (Fin.last 18)=0 :=
    early_terminal_zeroSpace_five_last ho H.head.paidRanks.lastActive early hv
  have eF : zeroSpace A 5=escapeHeadBand A U w r := by
    simpa only [Nat.add_zero] using H.head.head.flags 0 (by decide)
  have hw : w∈zeroSpace A 5 := by
    rw [eF]
    have hw := ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) r).mp le_rfl).2 0 H.head.head.positive
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using hw
  have band : escapeHeadBand A U w n≤V := by
    apply (clock_chain_le_iff n).mpr
    refine ⟨?_,?_⟩
    · intro u hu
      exact LinearMap.mem_ker.mpr (last0 (H.head.head.coreInside hu))
    · intro k _
      apply LinearMap.mem_ker.mpr
      change ((diag (nodes A))^k) w (Fin.last 18)=0
      rw [HeadFiber.clock_power_value,last0 hw,mul_zero]
  exact LinearMap.mem_ker.mp (band hx)

/-- The actual first-escape terminal coefficient is earned at the early
endpoint, not identified with an arbitrary constant on the clock-one fibre. -/
theorem NativeMarkedEscapeChart.early_mesh_exact_mark
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7) :
    ∃ d∈escapeHeadBand A U w (r+2), evalNodes A G=
      d+G.eval 1 • coordinate (K:=K) (Fin.last 18) := by
  have hg : evalNodes A G∈markedEscapeHeadBand A b U w (r+2) := first_alias_mem_markedEscapeHeadBand H.head H.first
  obtain ⟨d,hd,t,ht,e⟩ := Submodule.mem_sup.mp hg
  rw [terminalMark,ite_eq_left H.seed] at ht
  obtain ⟨factor,rfl⟩ := Submodule.mem_span_singleton.mp ht
  have atOne := H.head.paidRanks.lastActive.node_eq_one ha H.seed
  have atLast := congrFun e (Fin.last 18)
  change d (Fin.last 18) + factor * coordinate (K:=K) (Fin.last 18) (Fin.last 18) =
    G.eval (nodes A (Fin.last 18)) at atLast
  have unit : coordinate (K:=K) (Fin.last 18) (Fin.last 18) = 1 := by simp [coordinate]
  rw [H.early_head_last_zero ho early hd, unit, atOne, mul_one, zero_add] at atLast
  exact ⟨d,hd,by simpa only [atLast] using e.symm⟩

structure NativeEarlyF7Mode (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K) (r : ℕ) (J : K[X]) : Prop where
  degree : J.natDegree≤7
  origin : J.eval 0=0
  lastOne : J.eval 1=1
  moments : ∀ k≤5, unitMoment K k J=0
  paid : evalNodes A J∈zeroSpace A 7
  basis : zeroSpace A 7=escapeHeadBand A U w (r+2)⊔(K ∙ evalNodes A J)

/-- With the true terminal already in E7, there is either no extra mode
or one actual normalized polynomial mode. Its six moments are unmarked. -/
theorem NativeMarkedEscapeChart.early_F7_mode
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7) :
    zeroSpace A 7=escapeHeadBand A U w (r+2) ∨ ∃ J, NativeEarlyF7Mode A U w r J := by
  let B := escapeHeadBand A U w (r+2)
  let L := H.head.paidRanks.lastActive
  have bF : B≤zeroSpace A 7 := by
    simpa only [Nat.add_zero] using (escapeHeadBand_paid_from_seven H.head 0)
  have br₁ := rank_sup_terminalMark (A:=A) (b:=b) B
    (fun _ => fun t=>last_coordinate_not_defect ho (j:=7) L (by decide) (bF t))
  have br₂ := H.head.paidRanks.escapeRank
  rw [H.head.escapeShape] at br₂
  change finrank K (↥(B⊔terminalMark A b : Submodule K (Fin 19→K)))=7+terminalDebit A b at br₂
  change finrank K (↥(B⊔terminalMark A b : Submodule K (Fin 19→K)))=
    finrank K B+terminalDebit A b at br₁
  have br : finrank K B=7 := by omega
  have up := H.head.midpoint.nextRoom
  rw [first_dim_zero H.seed] at up
  change finrank K (zeroSpace A 7)+0≤8 at up
  have lo := Submodule.finrank_mono bF
  by_cases rk : finrank K (zeroSpace A 7)=7
  · exact Or.inl (Submodule.eq_of_le_of_finrank_le bF (by omega)).symm
  have f8 : finrank K (zeroSpace A 7)=8 := by omega
  have markIn : terminalMark A b≤treeSpace A 7 := by
    rw [terminalMark,ite_eq_left H.seed,Submodule.span_singleton_le_iff_mem]
    exact early
  have rr := (marked_staircase_ranks13 ha ho H.head H.seed).1 7 (by decide) (by decide)
  change finrank K (↥(treeSpace A 7⊔terminalMark A b : Submodule K (Fin 19→K)))=15 at rr
  rw [sup_eq_left.mpr markIn] at rr
  have atOne := L.node_eq_one ha H.seed
  have sep := coeff_separated_two_endpoints ha ho (n:=6) (j:=7)
    (by decide) (by decide) atOne
  let V := (coeffEval A 7).range
  have vinj : Function.Injective (coeffEval A 7) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v z
    exact sep v (z ▸ (zeroAt (zeroSpace A 7) (Fin.last 18)).zero_mem)
  have vr : finrank K V=8 := (LinearMap.finrank_range_of_inj vinj).trans (Module.finrank_fin_fun K)
  have inter := Submodule.finrank_sup_add_finrank_inf_eq V (zeroSpace A 7)
  rw [show V⊔zeroSpace A 7=treeSpace A 7 from (treeSpace_coeff_sup ho (q:=7) (by decide)).symm,
    rr,vr,f8] at inter
  have inon : V⊓zeroSpace A 7≠⊥ := by
    intro h
    rw [h,finrank_bot] at inter
    omega
  obtain ⟨v,hv,vnz⟩ := (Submodule.ne_bot_iff _).mp inon
  obtain ⟨P,pd,pv⟩ := exists_polynomial_of_coeff_range (Submodule.mem_inf.mp hv).1
  have pf : evalNodes A P∈zeroSpace A 7 := by
    rw [pv]
    exact (Submodule.mem_inf.mp hv).2
  have p1 : P.eval 1≠0 := by
    intro q
    have pz : evalNodes A P∈zeroAt (zeroSpace A 7) (Fin.last 18) :=
      mem_zeroAt.mpr ⟨pf,by rw [evalNodes_apply,atOne,q]⟩
    have z := eval_eq_zero_of_coeff_separated sep P pd pz
    exact vnz (by simpa only [z,map_zero] using pv.symm)
  let J := (P.eval 1)⁻¹ • P
  have jd : J.natDegree≤7 := (natDegree_smul_le _ _).trans pd
  have j1 : J.eval 1=1 := by
    change ((P.eval 1)⁻¹ • P).eval 1=1
    rw [eval_smul,smul_eq_mul,inv_mul_cancel₀ p1]
  have jf : evalNodes A J∈zeroSpace A 7 := by
    unfold J
    rw [map_smul]
    exact (zeroSpace A 7).smul_mem _ pf
  have jj : evalNodes A J (Fin.last 18)=1 := by
    simpa only [evalNodes_apply,atOne] using j1
  have outside : evalNodes A J∉B := by
    intro h
    exact one_ne_zero (jj.symm.trans (H.early_head_last_zero ho early h))
  have basis : zeroSpace A 7=B⊔(K ∙ evalNodes A J) := by
    symm
    apply Submodule.eq_of_le_of_finrank_le
      (sup_le bF ((Submodule.span_singleton_le_iff_mem ..).mpr jf))
    rw [Submodule.finrank_sup_span_singleton outside,br,f8] <;> decide
  refine Or.inr ⟨J,⟨jd,origin_of_marked_defect_polynomial (b:=b) (j:=7) ha (by decide)
    (Submodule.mem_sup_left jf),j1,?_,jf,basis⟩⟩
  intro k hk
  exact (probe_evalNodes ho J k (by omega)).symm.trans
    (probe_zeroSpace (k:=k) ho (by omega) jf)

/-- The coefficient of a genuine early extra mode is measured by the
actual endpoint evaluation, uniformly for every original F7 vector. -/
theorem NativeEarlyF7Mode.remove_measured
    {J : K[X]} (M : NativeEarlyF7Mode A U w r J)
    (zeroHead : ∀ y∈escapeHeadBand A U w (r+2), y (Fin.last 18)=0)
    (one : nodes A (Fin.last 18)=1) (hx : x∈zeroSpace A 7) :
    x-x (Fin.last 18) • evalNodes A J∈escapeHeadBand A U w (r+2) := by
  rw [M.basis] at hx
  obtain ⟨u,hu,v,hv,eq⟩ := Submodule.mem_sup.mp hx
  obtain ⟨factor,rfl⟩ := Submodule.mem_span_singleton.mp hv
  have c := congrFun eq (Fin.last 18)
  simp only [Pi.add_apply,zeroHead _ hu,zero_add,Pi.smul_apply,smul_eq_mul,
    evalNodes_apply,one,M.lastOne,mul_one] at c
  rw [←c,←eq,add_sub_cancel_right]
  exact hu

end
end RKResearch.Certified.Graded.ERK13NativeFirst
