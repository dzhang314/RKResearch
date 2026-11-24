module
public import RKCert.DirkFixedEvenBoundary
public import RKCert.LobattoTailRecurrence
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial Module
variable {K : Type*} [Field K] [CharZero K] {s m j p : ℕ}
noncomputable section

omit [CharZero K] in
/-- Through each affordable grade the genuine tree space is the sum of
the bounded scalar stage-polynomial space and the true numerical defects. -/
theorem tree_eq_poly_sup_zero {A : Fin s→Fin s→K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (pay : j+1≤p) :
    treeSpace A j=LinearMap.range (polyEval A j) ⊔ zeroSpace A j := by
  refine le_antisymm ?_ (sup_le (by rintro _ ⟨a,rfl⟩;exact polyEval_mem_treeSpace A j a) (zeroSpace_le_treeSpace A j))
  intro v hv
  obtain ⟨a,ea⟩:=exists_poly_zeroSpace ho pay hv
  exact Submodule.mem_sup.mpr ⟨_,⟨a,rfl⟩,_,ea,by abel⟩

omit [CharZero K] in
/-- A landed polynomial of degree exactly m+1 lets the fixed scalar block
absorb multiplication by the clock modulo the given physical space. -/
theorem clock_poly_of_grid_evaluated {A : Fin s→Fin s→K} {V : Submodule K (Vec K s)}
    {D : K[X]} (hd : D.natDegree=m+1) (paid : evalNodes A D∈V) :
    (LinearMap.range (polyEval A m)).map (diag (nodes A))≤LinearMap.range (polyEval A m) ⊔ V := by
  classical
  rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
  let P := ofFn (m+1) a
  let B := X*P
  have dP:P.natDegree≤m:=by have:=ofFn_natDegree_lt (by omega : 1≤m+1) a;exact Nat.le_of_lt_succ this
  have dB:B.natDegree≤m+1:=natDegree_mul_le.trans (by rw [natDegree_X];omega)
  have dn : D≠0 := fun e=>by rw [e,natDegree_zero] at hd;omega
  let t := B.coeff (m+1)/D.leadingCoeff
  let R := B-C t*D
  have dR:R.natDegree≤m:=by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    change (B-C t*D).coeff k=0
    rw [coeff_sub,coeff_C_mul]
    rcases eq_or_lt_of_le (show m+1≤k by omega) with rfl|lt
    · rw [←hd,coeff_natDegree,show t=B.coeff (m+1)/D.leadingCoeff from rfl,hd]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr dn)).symm
    · rw [coeff_eq_zero_of_natDegree_lt (dB.trans_lt lt),coeff_eq_zero_of_natDegree_lt (by omega : D.natDegree<k),mul_zero,sub_zero]
  have mR : evalNodes A R∈LinearMap.range (polyEval A m) := by
    rw [evalNodes_eq_polyEval A R dR];exact ⟨_,rfl⟩
  have eqn : diag (nodes A) (polyEval A m a)=evalNodes A R + t • evalNodes A D := by
    rw [←evalNodes_ofFn A m a]
    ext i
    simp only [R,B,P,diag_apply,evalNodes_apply,eval_sub,eval_mul,eval_X,eval_C,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [eqn]
  exact (Submodule.mem_sup).mpr ⟨_,mR,_,V.smul_mem t paid,rfl⟩

variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}

/-- The actual terminal cardinal pays the full closed Lobatto factor into
F_m+C F_m. The point t and its nonzero weight come from the tableau. -/
theorem closed_grid_paid_on_coordinates (hm : m=7 ∨ m=8 ∨ m=9 ∨ m=10)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m) :
    evalNodes A ((X-1)*lobatto m)∈zeroSpace A m ⊔ (zeroSpace A m).map (diag (nodes A)) := by
  obtain ⟨t,ct,_,pay,bw,_⟩:=fixed_even_boundary hm ha ho he
  let e : Vec K (s+1) := Pi.single t (1:K)
  let f:=e-b t • evalNodes A (lobatto m)
  let V:=zeroSpace A m ⊔ (zeroSpace A m).map (diag (nodes A))
  have bt:b t≠0 := fun z=>by rw [z,zero_mul] at bw;exact zero_ne_one bw
  have paid : f∈zeroSpace A m := pay
  have ef : f-diag (nodes A) f∈V :=
    V.sub_mem ((show zeroSpace A m ≤ V from le_sup_left) paid) ((show (zeroSpace A m).map (diag (nodes A)) ≤ V from le_sup_right) ⟨f,paid,rfl⟩)
  have ce : diag (nodes A) e=e := by
    ext i
    by_cases h:i=t
    · subst i;simp [e,ct]
    · simp [e,Pi.single_eq_of_ne h]
  have eqn : (b t) • evalNodes A ((X-1)*lobatto m)=f-diag (nodes A) f := by
    change _=(e-_) - diag (nodes A) (e-_)
    rw [map_sub,ce,map_smul]
    ext i
    simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,evalNodes_apply,eval_mul,eval_sub,eval_X,eval_one,diag_apply]
    ring
  rw [←eqn] at ef
  simpa only [smul_smul,inv_mul_cancel₀ bt,one_smul] using V.smul_mem (b t)⁻¹ ef

/-- The clock acting on P_m(c) can be absorbed with one increment of
the original defect flag and no increase of the scalar degree bound. -/
theorem midpoint_scalar_shift (hm : m=7 ∨ m=8 ∨ m=9 ∨ m=10)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m) :
    (LinearMap.range (polyEval A m)).map (diag (nodes A)) ≤ LinearMap.range (polyEval A m) ⊔
      (zeroSpace A m ⊔ (zeroSpace A m).map (diag (nodes A))) :=
  clock_poly_of_grid_evaluated (closed_lobatto_degree (by rcases hm with rfl|rfl|rfl|rfl <;>decide))
    (closed_grid_paid_on_coordinates hm ha ho he)

end
end RKCert.Paired.Terminal
