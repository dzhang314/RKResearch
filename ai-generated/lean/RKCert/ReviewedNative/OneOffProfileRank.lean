module

public import RKCert.ReviewedNative.OneOffWideProfiles

@[expose] public section

/-! # Normal profile rank before the doubled-clock obstruction -/
namespace RKResearch.Certified.Graded.OneOff
open RKResearch Module Polynomial
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}

omit [CharZero K] in
theorem wide_at_normal (w : NormalCoeffs K) :
    wideProfileMap A (w,0)=normalProfileMap A w := by
  change normalProfileMap A w+(0:K) • (g A*h A)=normalProfileMap A w
  simp

omit [CharZero K] in
theorem normal_profile_value (w : NormalCoeffs K) (r : Fin 12) :
    normalProfileMap A w r=(ofFn 6 w.1).eval (nodes A r)+
      (w.2.1*g A r+h A r*(ofFn 3 w.2.2).eval (nodes A r)) := by
  rw [normalProfileMap_apply]
  rfl

theorem normal_profile_mem (ho : HasOrder 9 A b) (w : NormalCoeffs K) :
    normalProfileMap A w∈treeSpace A 5 := by
  rw [←wide_at_normal]
  exact wide_profile_mem ho (w,0)

/-- The polynomial of any represented grade-five defect, not just a
kernel relation, is forced by exactly the same four moment equations. -/
theorem normal_profile_defect_poly (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    (w : NormalCoeffs K) (hw : normalProfileMap A w∈zeroSpace A 5) :
    ofFn 6 w.1=C (w.1 5)*anchorRadau := by
  let P := ofFn 6 w.1
  have pd : P.natDegree≤5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  rw [←wide_at_normal,wideProfileMap_apply] at hw
  have hP : evalNodes A P∈zeroSpace A 5 := by
    simpa only [add_sub_cancel_right] using
      (zeroSpace A 5).sub_mem hw (wide_defect_mem ho (w,0))
  have n0 : nodes A (0:Fin 12)=0 := by
    simp only [nodes,Matrix.mulVec,dotProduct,Pi.one_apply,mul_one]
    exact Finset.sum_eq_zero (fun j _=>ha 0 j (Fin.zero_le _))
  have p0 : P.eval 0=0 := by
    have e : evalNodes A P (0:Fin 12)=0 := origin_zeroSpace ha 5 hP
    rwa [evalNodes_apply,n0] at e
  have pm (j : Fin 4) : probe A b j.val (evalNodes A P)=0 :=
    probe_zeroSpace ho (by have := j.isLt; omega) hP
  have coeff : P.coeff 5=w.1 5 := ofFn_coeff_eq_val_of_lt _ (by decide)
  simpa only [coeff] using anchored_radau_span ho P pd p0 pm

theorem normal_coeff_forced_zero (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j)
    (w : NormalCoeffs K) (hw : normalProfileMap A w=0) (cf : w.1 5=0) :
    w=0 := by
  let Q := ofFn 3 w.2.2
  have rad := wide_kernel_poly ha ho (w,0) ((wide_at_normal _).trans hw)
  change ofFn 6 w.1=C (w.1 5)*anchorRadau at rad
  rw [cf,map_zero,zero_mul] at rad
  have eq (r : Fin 12) : w.2.1*g A r+h A r*Q.eval (nodes A r)=0 := by
    have e := congrFun ((normalProfileMap_apply A w).symm.trans hw) r
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,diag_apply,evalNodes_apply,
      rad,eval_zero,zero_add,Pi.zero_apply] using e
  have b0 : w.2.1=0 := by
    have e := eq i
    rw [D.base.origin.h_first ha,zero_mul,add_zero] at e
    exact (mul_eq_zero.mp e).resolve_right D.base.origin.g_ne
  have clean (r : Fin 12) (g0 : g A r=0) (hn : h A r≠0) : Q.eval (nodes A r)=0 := by
    have e := eq r
    rw [g0,mul_zero,zero_add] at e
    exact (mul_eq_zero.mp e).resolve_left hn
  have sep : PolySeparated A 4 :=
    PolySeparated.of_coeff (explicit_coeff_separated ha ho (q:=4) (by decide))
  obtain ⟨_,rank3,rank4,_⟩ := order9_forward_chart ha ho (by decide)
  obtain ⟨r2,gr2,xr2,hr2,_⟩ := first_doubled_clean_clock ha sep rank3 rank4 D
  obtain ⟨r3,gr3,_,x3d,x32d,h3n⟩ := new_clean_clock_h D ha sep
  let x := nodes A r3
  have qd : Q.eval d=0 := by
    simpa only [D.base.node] using clean j D.base.clean D.base.first_h.nonzero
  have h2n : h A r2≠0 := by rw [hr2]; exact mul_ne_zero D.base.origin.a_ne (pow_ne_zero _ D.base.dn)
  have q2d : Q.eval (2*d)=0 := by simpa only [xr2] using clean r2 gr2 h2n
  have qx : Q.eval x=0 := clean r3 gr3 h3n
  have dt : d≠2*d := by intro e; exact D.base.dn (by linear_combination -e)
  have T : ({d,2*d,x}:Finset K).card=3 := by
    simp [dt,show d≠x from Ne.symm x3d,show 2*d≠x from Ne.symm x32d]
  have Q0 : Q=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q
    ({d,2*d,x}:Finset K) (fun z hz => by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl|rfl <;> assumption) (by
      rw [T]
      exact ofFn_natDegree_lt (by decide) _)
  exact Prod.ext (injective_ofFn 6 (rad.trans (ofFn_zero _).symm))
    (Prod.ext b0 (injective_ofFn 3 (Q0.trans (ofFn_zero _).symm)))

omit [CharZero K] in
theorem normal_coeff_rank : finrank K (NormalCoeffs K)=10 := by
  norm_num [NormalCoeffs,Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_self]

def normalTop : NormalCoeffs K→ₗ[K] K where
  toFun w := w.1 5
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem normal_profile_rank_nine (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) :
    9≤finrank K (LinearMap.range (normalProfileMap A)) := by
  let N := normalProfileMap A
  let T := (normalTop (K:=K)).comp (LinearMap.ker N).subtype
  have inj : Function.Injective T :=
    (injective_iff_map_eq_zero T).mpr (fun w h=>Subtype.ext
      (normal_coeff_forced_zero ha ho D w (LinearMap.mem_ker.mp w.property) h))
  have hk := LinearMap.finrank_le_finrank_of_injective inj
  rw [Module.finrank_self] at hk
  have hr := LinearMap.finrank_range_add_finrank_ker N
  rw [normal_coeff_rank] at hr
  change 9≤finrank K (LinearMap.range N)
  omega

theorem normal_profile_range_le (ho : HasOrder 9 A b) :
    LinearMap.range (normalProfileMap A)≤treeSpace A 5 := by
  rintro v ⟨w,rfl⟩
  exact normal_profile_mem ho w

omit [CharZero K] in
theorem common_clock_affine_parameters {u v J slope P Q : K}
    (diff : v≠u) (a0 : J+u*slope=P+u*Q) (a1 : J+v*slope=P+v*Q) :
    P=J ∧ Q=slope := by
  have sq : Q=slope := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr diff)
    linear_combination a0-a1
  rw [sq] at a0
  exact ⟨(add_right_cancel a0).symm,sq⟩

end RKResearch.Certified.Graded.OneOff
