module
public import RKCert.ReviewedNative.ERK13NativePencilCubicBridge
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

@[expose] public section
/-! # Common physical primitive trace for all three pure pencil factor exits

Use a single live-core indicator and one residual for every mask. Multiplying
that residual by S gives a real first mismatch; multiplying by any further
polynomial cannot move a nonzero value earlier. The endpoint coefficient
is therefore a *single* linear functional of the total mask, even when two
pivots and two different physical sites are used. -/
namespace RKResearch.Certified.Graded.ERK13NativePencil
open ERK13NativeFirst RKResearch Polynomial Reverse Module NativeLobatto MarkedAdjacent
open RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b w v e : Fin 19→K} {r d : ℕ}
variable {U : Submodule K (Fin 19→K)} {G R Q : K[X]}
set_option maxHeartbeats 1800000

def factorBase (A : Matrix (Fin 19) (Fin 19) K) (e v : Fin 19→K) (R : K[X]) :=
  evalNodes A R-v-evalNodes A R*e

def factorTrace (A : Matrix (Fin 19) (Fin 19) K) (e v : Fin 19→K) (R : K[X]) :
    K[X] →ₗ[K] (Fin 19→K) :=
  (evalNodes A).comp (primitive.comp (LinearMap.mulLeft K R))-
    (mat A).comp ((diag (factorBase A e v R)).comp (evalNodes A))

theorem factorTrace_apply (W : K[X]) :
    factorTrace A e v R W=evalNodes A (primitive (W*R))-mat A (evalNodes A W*factorBase A e v R) := by
  change evalNodes A (primitive (R*W))-mat A (factorBase A e v R*evalNodes A W)=_
  rw [mul_comm R W,mul_comm (factorBase A e v R)]

private theorem masked_form (W : K[X]) :
    evalNodes A W*factorBase A e v R=
      evalNodes A (W*R)-(evalNodes A W*v+evalNodes A (W*R)*e) := by
  funext i
  simp only [factorBase,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,evalNodes_apply,eval_mul]
  ring

/-- At order three only X-divisible words are needed, because C v rather
than v itself supplies the extra paid grade. At order two all words are paid. -/
structure FactorBudget (A : Matrix (Fin 19) (Fin 19) K) (v : Fin 19→K) (R : K[X]) (d : ℕ) : Prop where
  order : d=2 ∨ d=3
  cap : ∀ m, m≤1 → ∀ W : K[X], W.natDegree≤d-1+m → (d=3 → W.eval 0=0) →
    (W*R).natDegree≤5+m ∧ evalNodes A W*v∈zeroSpace A (5+m)

theorem quartic_budget (S : PencilCleanHead A b r U w v G) (ho : HasOrder 13 A b)
    (rd : R.natDegree≤4) : FactorBudget A v R 2 := by
  refine ⟨Or.inl rfl,?_⟩
  intro m hm W wd _
  have w1 : W.natDegree≤1+m := wd
  have p := zeroSpace_mul_treeSpace (m:=4) (n:=1+m) ho (by omega) S.headFour (evalNodes_mem_treeSpace A W w1)
  exact ⟨(natDegree_mul_le_of_le w1 rd).trans (by omega),
    by simpa only [show 4+(1+m)=5+m by omega,mul_comm v] using p⟩

theorem cubic_budget (S : PencilCleanHead A b 3 U w v G) (ho : HasOrder 13 A b)
    (rd : R.natDegree≤3) : FactorBudget A v R 3 := by
  have cv : diag (nodes A) v∈zeroSpace A 4 := by
    rw [S.gradeFour]
    simpa only [pow_one] using (band_power_mem (A:=A) (U:=U) (w:=v) (n:=2) (k:=1) (by decide))
  refine ⟨Or.inr rfl,?_⟩
  intro m hm W wd wx
  have w2 : W.natDegree≤2+m := wd
  refine ⟨(natDegree_mul_le_of_le w2 rd).trans (by omega),?_⟩
  obtain ⟨T,we⟩ := X_dvd_iff.mpr (show W.coeff 0=0 by rw [coeff_zero_eq_eval_zero]; exact wx rfl)
  have td : T.natDegree≤1+m := by
    by_cases t0 : T=0
    · simp [t0]
    · rw [we,natDegree_X_mul t0] at w2; omega
  have p := zeroSpace_mul_treeSpace (m:=4) (n:=1+m) ho (by omega) cv (evalNodes_mem_treeSpace A T td)
  have val : evalNodes A W*v=diag (nodes A) v*evalNodes A T := by
    ext i
    simp only [we,Pi.mul_apply,evalNodes_apply,eval_mul,eval_X,diag_apply]
    ring
  rwa [val,show 5+m=4+(1+m) by omega]

private theorem core_mask (S : PencilCleanHead A b r U w v G) (he : e∈U) (W : K[X]) :
    evalNodes A (W*R)*e∈U :=
  clock_function_mem (fun z hz=>S.original.head.head.coreStable (Submodule.mem_map_of_mem hz)) (W*R).eval he

private theorem trace_paid (S : PencilCleanHead A b r U w v G) (he : e∈U)
    (B : FactorBudget A v R d) {m : ℕ} (hm : m≤1)
    {W : K[X]} (wd : W.natDegree≤d-1+m) (wx : d=3 → W.eval 0=0) :
    factorTrace A e v R W∈zeroSpace A (6+m) := by
  obtain ⟨rd,pay⟩ := B.cap m hm W wd wx
  have cm : evalNodes A (W*R)*e∈zeroSpace A (5+m) :=
    zeroSpace_mono A (by omega : 4≤5+m) (S.coreFour (core_mask (R:=R) S he W))
  have ay := mat_zeroSpace_charZero A (5+m) ((zeroSpace A (5+m)).add_mem pay cm)
  have defc := primitive_defect (q:=5+m) A (W*R) rd
  rw [factorTrace_apply,masked_form,map_sub]
  have z := (zeroSpace A (5+m+1)).sub_mem ay defc
  rw [show 5+m+1=6+m by omega] at z
  convert z using 1 <;> abel

structure FactorPivot (A : Matrix (Fin 19) (Fin 19) K) (U : Submodule K (Fin 19→K))
    (e v : Fin 19→K) (R Q M : K[X]) (i : Fin 19) : Prop where
  notLast : i≠Fin.last 18
  dark : ¬LiveCore.live U i
  headZero : v i=0
  maskNonzero : M.eval (nodes A i)≠0
  factorNonzero : R.eval (nodes A i)≠0
  complementZero : Q.eval (nodes A i)=0
  before : ∀ j < i,(evalNodes A M*factorBase A e v R) j=0

theorem factor_pivot (S : PencilCleanHead A b r U w v G)
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (B : FactorBudget A v R d) (he : e∈U) (emask : ∀i,e i=if LiveCore.live U i then 1 else 0)
    (rn : R≠0) (factor : G=R*Q) (amp : ∀ i,v i≠0 → v i=R.eval (nodes A i))
    (mesh : ∃ c∈U,evalNodes A G=c+weightedEval (nodes A) v Q+G.eval 1 • coordinate (Fin.last 18))
    (M : K[X]) (mn : M≠0) (md : M.natDegree≤d) (mx : d=3 → M.eval 0=0) :
    ∃ i, FactorPivot A U e v R Q M i := by
  have ord := B.order
  obtain ⟨rd,mp⟩ := B.cap 1 le_rfl M (by omega) mx
  have y : evalNodes A M*v+evalNodes A (M*R)*e∈zeroSpace A 6 :=
    (zeroSpace A 6).add_mem mp
      (zeroSpace_mono A (by decide : 4≤6) (S.coreFour (core_mask (R:=R) S he M)))
  let z := evalNodes A M*factorBase A e v R
  have zt : z∈treeSpace A 6 := by
    dsimp only [z]; rw [masked_form]
    exact (treeSpace A 6).sub_mem (evalNodes_mem_treeSpace A (M*R) rd) (zeroSpace_le_treeSpace A 6 y)
  have zn : z≠0 := by
    intro zero
    change evalNodes A M*factorBase A e v R=0 at zero
    rw [masked_form,sub_eq_zero] at zero
    exact mul_ne_zero mn rn (eval_eq_zero_of_coeff_separated (coeff_separated ho (q:=6) (by decide))
      (M*R) rd (zero.symm ▸ y))
  have ex : ∃ k : ℕ,∃i : Fin 19,i.val=k ∧ z i≠0 := by
    by_contra no
    exact zn (funext (fun i=>not_not.mp (fun h=>no ⟨i.val,i,rfl,h⟩)))
  obtain ⟨i,ik,iz⟩ := Nat.find_spec ex
  have pre (j : Fin 19) (hj : j < i) : z j=0 := by
    by_contra ne
    have small : j.val < Nat.find ex := by rw [←ik]; exact hj
    exact Nat.find_min ex small ⟨j,rfl,ne⟩
  have iL : i≠Fin.last 18 := by
    intro h
    subst i
    have eq : z=z (Fin.last 18) • coordinate (K:=K) (Fin.last 18) := by
      funext j
      by_cases jl : j=Fin.last 18
      · subst j; simp only [Pi.smul_apply,smul_eq_mul,coordinate]; simp
      · rw [pre j (lt_of_le_of_ne (Fin.le_last j) jl),Pi.smul_apply,smul_eq_mul,coordinate_last_apply_zero jl,mul_zero]
    rw [eq] at zt
    exact endpoint_coordinate_out ha ho (q:=6) (by decide) _ S.original.head.paidRanks.lastActive.live
      (S.original.head.paidRanks.lastActive.node_eq_one ha S.original.seed)
      (((treeSpace A 6).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr iz)).mp zt)
  change M.eval (nodes A i)*(R.eval (nodes A i)-v i-R.eval (nodes A i)*e i)≠0 at iz
  have dark : ¬LiveCore.live U i := by
    intro live
    exact iz (by rw [S.clean _ live,emask,if_pos live,mul_one,sub_zero,sub_self,mul_zero])
  have vz : v i=0 := by
    by_contra nz
    exact iz (by rw [amp _ nz,emask,if_neg dark,mul_zero,sub_self,sub_zero,mul_zero])
  have non : M.eval (nodes A i)*R.eval (nodes A i)≠0 := by
    simpa only [vz,emask i,if_neg dark,mul_zero,sub_zero] using iz
  obtain ⟨g,hg,ge⟩ := mesh
  have root : G.eval (nodes A i)=0 := by
    simpa only [evalNodes_apply,Pi.add_apply,weightedEval_apply,Pi.smul_apply,smul_eq_mul,
      LiveCore.val_eq_zero_of_not_live dark hg,vz,coordinate_last_apply_zero iL,mul_zero,add_zero] using congrFun ge i
  rw [factor,eval_mul] at root
  obtain ⟨mnz,rnz⟩ := mul_ne_zero_iff.mp non
  exact ⟨i,⟨iL,dark,vz,mnz,rnz,(mul_eq_zero.mp root).resolve_left rnz,pre⟩⟩

private theorem pivot_zero_on_band (S : PencilCleanHead A b r U w v G)
    {M : K[X]} {i : Fin 19} (site : FactorPivot A U e v R Q M i)
    {x : Fin 19→K} (hx : x∈escapeHeadBand A U w (r+2)) : x i=0 := by
  rw [←S.same _ (by omega)] at hx
  obtain ⟨a,au,J,_,eq⟩ := band_polynomial_repr (by omega) hx
  rw [eq,Pi.add_apply,weightedEval_apply,site.headZero,mul_zero,add_zero]
  exact LiveCore.val_eq_zero_of_not_live site.dark au

theorem shared_factor_trace (S : PencilCleanHead A b r U w v G)
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (he : e∈U) (B : FactorBudget A v R d) :
    ∃ κ : K,∀ (M T : K[X]) (i : Fin 19), FactorPivot A U e v R Q M i →
      (T*M).natDegree≤d → (d=3 → (T*M).eval 0=0) →
      (primitive ((T*M)*R)).eval (nodes A i)=
        (κ*(T*M).coeff d)*radauValue (nodes A i) := by
  let F := factorTrace A e v R
  have ord := B.order
  have pos : 0 < d := by omega
  have pivotRead {M T : K[X]} {i : Fin 19} (site : FactorPivot A U e v R Q M i) :
      F (T*M) i=(primitive ((T*M)*R)).eval (nodes A i) := by
    have mt : mat A (evalNodes A (T*M)*factorBase A e v R) i=0 := by
      apply causal_mat ha
      intro j hj
      have pre := site.before j hj
      change M.eval (nodes A j)*factorBase A e v R j=0 at pre
      change (T*M).eval (nodes A j)*factorBase A e v R j=0
      rw [eval_mul,mul_assoc,pre,mul_zero]
    simp only [F,factorTrace_apply,Pi.sub_apply,mt,sub_zero,evalNodes_apply]
  have topRead (W : K[X]) (wd : W.natDegree≤d) (wx : d=3 → W.eval 0=0) :
      F W (Fin.last 18)=W.coeff d * F (X^d) (Fin.last 18) := by
    obtain ⟨t,ht⟩ := reduction_by_next_degree (a:=d-1)
      (show W.natDegree≤d-1+1 by omega)
      (show ((X:K[X])^d).natDegree=d-1+1 by rw [natDegree_X_pow]; omega)
    have cf := coeff_eq_zero_of_natDegree_lt (ht.trans_lt (show d-1 < d by omega))
    rw [coeff_sub,Polynomial.coeff_smul,smul_eq_mul,
      show ((X:K[X])^d).coeff d=1 by simp,mul_one,sub_eq_zero] at cf
    have adm : d=3 → (W-t • X^d).eval 0=0 := by
      intro th
      simp only [eval_sub,eval_smul,eval_pow,eval_X,wx th,zero_pow (Nat.ne_of_gt pos),smul_zero,sub_zero]
    have low := (width19_last_node_clean_six ha ho).2 _ (trace_paid S he B (m:=0) (by decide) ht adm)
    change F (W-t • X^d) (Fin.last 18)=0 at low
    rw [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,sub_eq_zero,←cf] at low
    exact low
  have early := width19_pays_terminal_by_seven ha ho
  rcases S.original.early_F7_mode ha ho early with pure | ⟨J,H⟩
  · refine ⟨0,?_⟩
    intro M T i site wd wx
    have z := trace_paid S he B (m:=1) (by decide) (by omega : (T*M).natDegree≤d-1+1) wx
    rw [pure] at z
    rw [←pivotRead site,zero_mul,zero_mul]
    exact pivot_zero_on_band S site z
  · refine ⟨F (X^d) (Fin.last 18),?_⟩
    intro M T i site wd wx
    have paid := trace_paid S he B (m:=1) (by decide) (by omega : (T*M).natDegree≤d-1+1) wx
    have one := S.original.head.paidRanks.lastActive.node_eq_one ha S.original.seed
    have pure := H.remove_measured (fun x hx=>S.original.early_head_last_zero ho early hx) one paid
    have z := pivot_zero_on_band S site pure
    change F (T*M) i - F (T*M) (Fin.last 18)*J.eval (nodes A i)=0 at z
    rw [sub_eq_zero,pivotRead site,topRead _ wd wx,H.eval_eq_radauValue ha ho one] at z
    simpa only [mul_comm ((T*M).coeff d) (F (X^d) (Fin.last 18))] using z

end
end RKResearch.Certified.Graded.ERK13NativePencil
