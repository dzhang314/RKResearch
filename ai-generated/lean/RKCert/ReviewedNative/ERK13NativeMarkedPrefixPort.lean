module

public import RKCert.ReviewedNative.ERK13NativeMarkedShiftLocality
public import RKCert.ReviewedNative.JointPrefixDetector
public import RKCert.ReviewedNative.CausalStage

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The original preterminal joint pivot in both marked first escapes

The existing joint-mask detector is promoted to the terminal-marked chart
only after proving the pivot is physically before the terminal. A mode may
be subtracted at its actual coefficient; the resulting primitive trace is
an equality at that exact old physical port. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Matrix Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w v z : Fin 19 → K} {r a : ℕ}
variable {G P S : K[X]}

/-- Constancy in the literal joint fibre, through an original stage cut. -/
def JointPrefixConstant (A : Matrix (Fin 19) (Fin 19) K)
    (v : Fin 19 → K) (k : Fin 19) (f : Fin 19 → K) (t : K) : Prop :=
  ∀ i : Fin 19, i.val<k.val+1 → nodes A i=nodes A k → v i=v k → f i=t

structure NativeMarkedPivot (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19 → K)
    (U : Submodule K (Fin 19 → K)) (w v z : Fin 19 → K) (G S : K[X])
    (k : Fin 19) (g : Fin 19 → K) : Prop where
  preterminal : k<Fin.last 18
  core : g∈U
  matchesBefore : ∀ i<k, g i=z i
  maskNonzero : S.eval (nodes A k)≠0
  meshRoot : G.eval (nodes A k)=0
  pureConstant : ∀ n (f : Fin 19 → K), f∈markedEscapeHeadBand A b U w n →
    ∀ t : K, JointPrefixConstant A v k f t → t=0

private theorem last_coordinate_out_six
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b) :
    coordinate (K:=K) (Fin.last 18) ∉ treeSpace A 6 :=
  endpoint_coordinate_out ha ho (q:=6) (by decide) _ H.head.paidRanks.lastActive.live
    (H.head.paidRanks.lastActive.node_eq_one ha H.seed)

/-- Actual paid grade six prevents the first joint failure from occurring
at the terminal. Hence the terminal mark is zero throughout its own fibre
prefix, and the first alias must vanish at its true clock. -/
theorem NativeMarkedEscapeChart.first_joint_pivot
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (vMask : MaskInvariant v U)
    (profile : v*w-weightedEval (nodes A) w P∈U)
    (defn : ∀ i, z i=S.eval (nodes A i)*(P.eval (nodes A i)-v i))
    (paid : z∈treeSpace A 6) (outside : z∉U) :
    ∃ k g, NativeMarkedPivot A b U w v z G S k g := by
  have cMask : MaskInvariant (nodes A) U := clock_mask_invariant
    (fun f hf=>H.head.head.coreStable (Submodule.mem_map_of_mem hf))
  obtain ⟨k,g,gu,pre,snz,detector⟩ :=
    HeadFiber.joint_prefix_detector cMask vMask P S profile defn outside
  have gT : g∈treeSpace A 6 := zeroSpace_le_treeSpace A 6
    (zeroSpace_mono A (by decide : 5≤6) (H.head.head.coreInside gu))
  have preL : k<Fin.last 18 := by
    by_contra out
    have kl : k=Fin.last 18 := le_antisymm (Fin.le_last _) (le_of_not_gt out)
    subst k
    let q := z-g
    have eq : q=q (Fin.last 18) • coordinate (K:=K) (Fin.last 18) := by
      ext i
      by_cases h : i=Fin.last 18
      · subst i
        simp [coordinate]
      · have il : i<Fin.last 18 := lt_of_le_of_ne (Fin.le_last _) h
        have off : coordinate (K:=K) (Fin.last 18) i = 0 :=
          @Pi.single_eq_of_ne (Fin 19) (fun _ => K) _ (Classical.decEq _) (Fin.last 18) i h 1
        simp only [q, Pi.sub_apply, pre i il, sub_self, Pi.smul_apply, off, smul_zero]
    have qn : q (Fin.last 18)≠0 := by
      intro e
      have q0 : q=0 := by rw [eq,e,zero_smul]
      have ze : z=g := sub_eq_zero.mp (show z-g=0 from q0)
      exact outside (ze.symm ▸ gu)
    have qT : q∈treeSpace A 6 := (treeSpace A 6).sub_mem paid gT
    rw [eq] at qT
    exact last_coordinate_out_six H ha ho
      (((treeSpace A 6).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr qn)).mp qT)
  have pure (n : ℕ) (f : Fin 19 → K) (hf : f∈markedEscapeHeadBand A b U w n)
      (t : K) (fixedValue : JointPrefixConstant A v k f t) : t=0 := by
    obtain ⟨d,hd,m,hm,eq⟩ := Submodule.mem_sup.mp hf
    rw [terminalMark,ite_eq_left H.seed] at hm
    obtain ⟨factor,rfl⟩ := Submodule.mem_span_singleton.mp hm
    apply detector hd t
    intro i hi ci vi
    have ik : i≤k := by change i.val≤k.val; omega
    have hlast : i≠Fin.last 18 := ne_of_lt (lt_of_le_of_lt ik preL)
    calc
      d i = (d+factor • coordinate (K:=K) (Fin.last 18)) i := by
        have off : coordinate (K:=K) (Fin.last 18) i = 0 :=
          @Pi.single_eq_of_ne (Fin 19) (fun _ => K) _ (Classical.decEq _) (Fin.last 18) i hlast 1
        simp only [Pi.add_apply, Pi.smul_apply, off, smul_zero, add_zero]
      _ = t := by rw [eq]; exact fixedValue i hi ci vi
  have mesh : evalNodes A G∈markedEscapeHeadBand A b U w (r+2) := first_alias_mem_markedEscapeHeadBand H.head H.first
  have root : G.eval (nodes A k)=0 := pure (r+2) _ mesh _ (by
    intro i _ ci _
    simp only [evalNodes_apply,ci])
  exact ⟨k,g,⟨preL,gu,pre,snz,root,pure⟩⟩

/-- Strict causality applies pointwise through the same original prefix
for any scalar mask. It does not borrow closure of a synthetic chart. -/
theorem mat_masked_prefix_residual_zero_through
    (ha : ∀ i j, i≤j → A i j=0) {k : Fin 19} {g : Fin 19 → K}
    (pre : ∀ i<k, g i=z i) (mask : Fin 19 → K) {i : Fin 19} (hi : i≤k) :
    mat A (mask*(z-g)) i=0 := by
  apply causal_mat ha i (mask*(z-g))
  intro j hj
  have hji : j < i := hj
  simp only [Pi.mul_apply,Pi.sub_apply,pre j (hji.trans_le hi),sub_self,mul_zero]

/-- A preterminal physical primitive port after subtracting a genuine mode.
For the pure case set factor=0. Nothing is asserted about existence of the mode
or the membership hypothesis by this trace lemma. -/
theorem NativeMarkedPivot.primitive_mode_trace
    {k : Fin 19} {g : Fin 19 → K} (site : NativeMarkedPivot A b U w v z G S k g)
    (ha : ∀ i j, i≤j → A i j=0) (mask : Fin 19 → K) {R J : K[X]} {factor : K} {n : ℕ}
    (paid : evalNodes A (primitive R)-mat A (mask*(z-g))-factor • evalNodes A J∈
      markedEscapeHeadBand A b U w n) :
    (primitive R).eval (nodes A k)=factor*J.eval (nodes A k) := by
  apply sub_eq_zero.mp
  apply site.pureConstant n _ paid
  intro i hi ci _
  have ik : i≤k := by change i.val≤k.val; omega
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,evalNodes_apply,
    mat_masked_prefix_residual_zero_through ha site.matchesBefore mask ik,sub_zero,ci]

/-- Actual primitive transport for the original cubic/quadratic prefix
mask. The head invariant core is paid in F5 and the mask consumes at most
three additional clock degrees before the native A step. -/
theorem NativeMarkedEscapeChart.primitive_prefix_paid
    (H : NativeMarkedEscapeChart A b a G r U w) (ho : HasOrder 13 A b)
    {d : ℕ} (two : 2≤d) (hv : v∈zeroSpace A d) {g : Fin 19 → K} (gu : g∈U)
    (defn : ∀ i, z i=S.eval (nodes A i)*(P.eval (nodes A i)-v i))
    (pd : P.natDegree≤d) (T : K[X]) (td : (T*S).natDegree≤3) :
    evalNodes A (primitive ((T*S)*P)) - mat A (evalNodes A T*(z-g)) ∈
      zeroSpace A (d+4) := by
  have vpay : evalNodes A (T*S)*v∈zeroSpace A (d+3) := by
    rw [mul_comm]
    exact zeroSpace_mul_treeSpace ho (n:=3) (by decide) hv (evalNodes_mem_treeSpace A _ td)
  have gmasked : evalNodes A T*g∈U :=
    clock_function_mem (fun f hf=>H.head.head.coreStable (Submodule.mem_map_of_mem hf)) T.eval gu
  have gpay : evalNodes A T*g∈zeroSpace A (d+3) :=
    zeroSpace_mono A (by omega) (H.head.head.coreInside gmasked)
  have ay := mat_zeroSpace_charZero A (d+3) ((zeroSpace A (d+3)).add_mem vpay gpay)
  have dpay : ((T*S)*P).natDegree≤d+3 := (natDegree_mul_le_of_le td pd).trans (by omega)
  have defect := primitive_defect A _ dpay
  have mask : evalNodes A T*(z-g)=evalNodes A ((T*S)*P)-(evalNodes A (T*S)*v+evalNodes A T*g) := by
    ext i
    simp only [Pi.mul_apply,Pi.sub_apply,Pi.add_apply,evalNodes_apply,eval_mul,defn i]
    ring
  rw [mask,map_sub,show evalNodes A (primitive ((T*S)*P))-
      (mat A (evalNodes A ((T*S)*P))-mat A (evalNodes A (T*S)*v+evalNodes A T*g)) =
      mat A (evalNodes A (T*S)*v+evalNodes A T*g)-
        (mat A (evalNodes A ((T*S)*P))-evalNodes A (primitive ((T*S)*P))) by abel]
  exact (zeroSpace A (d+4)).sub_mem ay defect

end
end RKResearch.Certified.Graded.ERK13NativeFirst
