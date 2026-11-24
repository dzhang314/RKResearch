module
public import RKCert.ERKNodalDetectorBudget
public import RKCert.BackwardGrowth

@[expose] public section
/-! # Reverse flag including every affordable reflected primitive

The older back flag is used only as a lower bound. At an exact rank budget
both flags coincide, proving that even the old basis contains the reflected
primitive rows through the paid grade. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired RKCert.Endpoint Polynomial Module
open scoped Classical
set_option maxHeartbeats 1400000
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ}
variable {A:Fin s→Fin s→K} {b:Vec K s}

noncomputable def reflectedError (A:Fin s→Fin s→K) (b:Vec K s) : K[X] →ₗ[K] Vec K s :=
  (transMat A).comp (weightedEval (mirror A) b) -
    (weightedEval (mirror A) b).comp formalPrimitiveLinear

@[simp] theorem reflectedError_apply (P:K[X]) :
    reflectedError A b P=transMat A (weightedEval (mirror A) b P)-
      weightedEval (mirror A) b (formalPrimitive P) := rfl

theorem seed2_reflectedError :
    backSeed2 A b=(2:K) • reflectedError A b X := by
  have prim:formalPrimitive (X:K[X])=C (1/2:K)*X^2:=by
    have x:(X:K[X])=monomial 1 1:=by simp [←C_mul_X_pow_eq_monomial]
    calc
      _=primitive (monomial 1 (1:K)):=by rw [formalPrimitive_eq_treePrimitive,x]
      _=_:=by rw [primitive_monomial,←C_mul_X_pow_eq_monomial];norm_num
  have we:weightedEval (mirror A) b X=diag (mirror A) b := by
    ext i;simp [weightedEval_apply,diag_apply]
  rw [reflectedError_apply,we,prim,backSeed2]
  ext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,weightedEval_apply,eval_mul,eval_C,
    eval_pow,eval_X,diag_apply]
  ring

noncomputable def primitiveBack (A:Fin s→Fin s→K) (b:Vec K s) :
    ℕ→Submodule K (Vec K s)
  | 0 => back A b 0
  | n+1 =>
    let U:=primitiveBack A b n
    U⊔U.map (transMat A)⊔U.map (diag (mirror A))⊔
      LinearMap.range ((reflectedError A b).comp (ofFn (n+2)))

theorem primitiveBack_le_succ (n:ℕ) : primitiveBack A b n≤primitiveBack A b (n+1) :=
  le_sup_left.trans (le_sup_left.trans le_sup_left)

theorem primitiveBack_trans (n:ℕ) : (primitiveBack A b n).map (transMat A)≤primitiveBack A b (n+1) :=
  le_sup_right.trans (le_sup_left.trans le_sup_left)

theorem primitiveBack_clock (n:ℕ) : (primitiveBack A b n).map (diag (mirror A))≤primitiveBack A b (n+1) :=
  le_sup_right.trans le_sup_left

theorem reflectedError_mem_primitiveBack (P:K[X]) (n:ℕ) (pay:P.natDegree≤n+1) :
    reflectedError A b P∈primitiveBack A b (n+1) := by
  classical
  apply (show LinearMap.range ((reflectedError A b).comp (ofFn (n+2)))≤
    primitiveBack A b (n+1) from le_sup_right)
  refine ⟨toFn (n+2) P,?_⟩
  change reflectedError A b (ofFn (n+2) (toFn (n+2) P))=_
  rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega : P.natDegree<n+2)]

theorem seed2_mem_primitiveBack (n:ℕ) : backSeed2 A b∈primitiveBack A b (n+1) := by
  rw [seed2_reflectedError]
  exact (primitiveBack A b (n+1)).smul_mem _
    (reflectedError_mem_primitiveBack X n (by simp))

theorem back_le_primitiveBack (n:ℕ) : back A b n≤primitiveBack A b n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    change _⊔_⊔_⊔_≤_
    exact sup_le (sup_le (sup_le (ih.trans (primitiveBack_le_succ n))
      ((Submodule.map_mono ih).trans (primitiveBack_trans n)))
      ((Submodule.map_mono ih).trans (primitiveBack_clock n)))
      ((Submodule.span_singleton_le_iff_mem ..).mpr (seed2_mem_primitiveBack n))

theorem primitiveBack_annih (ho:HasTreeOrderAtLeast A b p) (j n:ℕ) (pay:j+n+2≤p) :
    primitiveBack A b n≤annih (treeSpace A j) := by
  classical
  induction n generalizing j with
  | zero => exact back_annih ho j 0 pay
  | succ n ih =>
    change _⊔_⊔_⊔_≤_
    refine sup_le (sup_le (sup_le (ih j (by omega)) ?_) ?_) ?_
    · rintro _ ⟨u,hu,rfl⟩
      apply mem_annih.mpr
      intro v hv
      rw [row_flip_mat]
      exact mem_annih.mp (ih (j+1) (by omega) hu) _ (mat_treeSpace A j hv)
    · rintro _ ⟨u,hu,rfl⟩
      apply mem_annih.mpr
      intro v hv
      rw [row_flip_diag]
      exact mem_annih.mp (ih (j+1) (by omega) hu) _ (mirror_treeSpace A j hv)
    · rintro _ ⟨a,rfl⟩
      change reflectedError A b (ofFn (n+2) a)∈annih _
      rw [reflectedError_apply]
      exact primitive_annihilator_paid ho _ (by
        have hh:=ofFn_natDegree_lt (by omega : 0<n+2) a
        omega)

theorem primitiveBack_terminal (t:Fin s) (y0:mirror A t=0) (col:∀i,A i t=0)
    (seed0:backSeed1 A b=0) (n:ℕ) :
    primitiveBack A b n≤LinearMap.ker (LinearMap.proj t) := by
  induction n with
  | zero =>
    change Submodule.span K {backSeed1 A b}≤_
    rw [seed0,Submodule.span_singleton_eq_bot.mpr rfl]
    exact bot_le
  | succ n ih =>
    change _⊔_⊔_⊔_≤_
    refine sup_le (sup_le (sup_le ih ?_) ?_) ?_
    · rintro _ ⟨u,_,rfl⟩
      exact transMat_zero_column t col u
    · rintro _ ⟨u,_,rfl⟩
      change diag (mirror A) u t=0
      rw [diag_apply,y0,zero_mul]
    · rintro _ ⟨a,rfl⟩
      change reflectedError A b (ofFn (n+2) a) t=0
      rw [reflectedError_apply,Pi.sub_apply,transMat_zero_column t col,weightedEval_apply,y0,
        formalPrimitive_eval_zero,zero_mul,sub_zero]

theorem primitiveBack_strict (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p) (n:ℕ) (pay:n+3≤p) :
    primitiveBack A b n<primitiveBack A b (n+1) := by
  refine lt_of_le_of_ne (primitiveBack_le_succ n) (fun eq=>?_ )
  have hmem : diag (mirror A) b∈primitiveBack A b n := by
    apply mem_of_invariant_seed Fin.revPerm (transMat A) (causal_transpose ha) (mirror A) b
    · intro v hv
      rw [eq]
      exact primitiveBack_trans n (Submodule.mem_map_of_mem hv)
    · intro v hv
      rw [eq]
      exact primitiveBack_clock n (Submodule.mem_map_of_mem hv)
    · rw [eq]
      exact seed2_mem_primitiveBack n
  exact (back_target_nonzero ho (by omega)) (mem_annih.mp (primitiveBack_annih ho 0 n (by omega) hmem)
    1 (stageWeight_mem_space A .leaf (by decide)))

theorem primitiveBack_interval (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (n d:ℕ) (pay:n+d+2≤p) :
    finrank K (primitiveBack A b n)+d≤finrank K (primitiveBack A b (n+d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have L:=ih (by omega)
    have G:=Submodule.finrank_lt_finrank_of_lt (primitiveBack_strict ha ho (n+d) (by omega))
    change finrank K (primitiveBack A b n)+(d+1)≤finrank K (primitiveBack A b (n+d+1))
    omega

/-- An actual tight reverse horizon buys all of the intermediate ranks
and promotes every reflected primitive into the ordinary back flag. -/
theorem thin_primitiveBack_agrees (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    {H:ℕ} (pay:H+2≤p) (cap:finrank K (primitiveBack A b H)≤H) :
    ∀ n≤H,finrank K (back A b n)=n ∧ back A b n=primitiveBack A b n := by
  intro n nh
  have upper:=primitiveBack_interval ha ho n (H-n) (by omega)
  rw [show n+(H-n)=H by omega] at upper
  have lower:=back_finrank ha ho n (by omega)
  have inc:=back_le_primitiveBack (A:=A) (b:=b) n
  have mono:=Submodule.finrank_mono inc
  exact ⟨by omega,Submodule.eq_of_le_of_finrank_le inc (by omega)⟩

end RKCert.Paired.ReverseHull
