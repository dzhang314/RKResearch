module

public import RKCert.ReviewedNative.OrderNineGradeFive

@[expose] public section

/-! # Defect separation in the actual one-off order-nine chart -/
namespace RKResearch.Certified.Graded.OneOff
open RKResearch Module Polynomial
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}

/-- The dimension argument chooses a genuine coefficient relation with
zero polynomial part. In rank nine spend one additional coefficient;
in rank ten the actual terminal coordinate kills it instead. -/
theorem exists_wide_kernel_with_zero_polynomial (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 9 A b) :
    ∃ w : WideCoeffs K, w≠0 ∧ wideProfileMap A w=0 ∧ ofFn 6 w.1.1=0 := by
  let L := (wideProfileMap A).codRestrict (treeSpace A 5) (wide_profile_mem ho)
  have rank := order9_grade_five_upper ha ho
  by_cases full : finrank K (treeSpace A 5)=10
  · have lt : finrank K (treeSpace A 5) < finrank K (WideCoeffs K) := by
      rw [full,wide_coeff_rank]
      decide
    obtain ⟨w,nz,L0⟩ := nonzero_kernel_of_rank_lt L lt
    have ker : wideProfileMap A w=0 := congrArg Subtype.val L0
    have rad := wide_kernel_poly ha ho w ker
    obtain ⟨_,clock,_,_⟩ := order9_rank_five_full_terminal ha ho full
    have g0 : g A (Fin.last 11)=0 :=
      rank_five_full_terminal_defect ha ho full (zeroSpace_mono A (by decide) (mDef_mem A 1))
    have h0 : h A (Fin.last 11)=0 :=
      rank_five_full_terminal_defect ha ho full (h_in_grade_three A)
    have at1 : (ofFn 6 w.1.1).eval 1=0 := by
      have e := congrFun ((wideProfileMap_apply A w).symm.trans ker) (Fin.last 11)
      simp only [wideDefect,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,diag_apply,
        evalNodes_apply,clock,g0,h0,mul_zero,zero_mul,add_zero,Pi.zero_apply] at e
      exact e
    rw [rad,eval_mul,eval_C,anchorRadau_at_one] at at1
    have c0 : wideTop w=0 := (mul_eq_zero.mp at1).resolve_right (by norm_num)
    refine ⟨w,nz,ker,?_⟩
    rw [rad,c0,map_zero,zero_mul]
  · let LL := L.prod (wideTop (K:=K))
    have lt : finrank K ((treeSpace A 5)×K) < finrank K (WideCoeffs K) := by
      rw [Module.finrank_prod,Module.finrank_self,wide_coeff_rank]
      omega
    obtain ⟨w,nz,e⟩ := nonzero_kernel_of_rank_lt LL lt
    have L0 : L w=0 := congrArg Prod.fst e
    have c0 : wideTop w=0 := congrArg Prod.snd e
    have ker : wideProfileMap A w=0 := congrArg Subtype.val L0
    have rad := wide_kernel_poly ha ho w ker
    refine ⟨w,nz,ker,?_⟩
    rw [rad,c0,map_zero,zero_mul]

/-- Actual pointwise defect separation. A clean copy of the off node is
not ruled out; the product vanishes even at coincident abscissas. -/
theorem order9_defects_separate (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) :
    g A*h A=0 := by
  obtain ⟨w,nw,hw,P0⟩ := exists_wide_kernel_with_zero_polynomial ha ho
  let Q := ofFn 3 w.1.2.2
  let beta := w.1.2.1
  have eq : (beta • g A+diag (h A) (evalNodes A Q))+w.2 • (g A*h A)=0 := by
    have e := (wideProfileMap_apply A w).symm.trans hw
    have z : evalNodes A (0:K[X])=0 := by ext r; simp
    rw [P0,z,zero_add] at e
    exact e
  have b0 : beta=0 := by
    have e := congrFun eq i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,diag_apply,D.base.origin.h_first ha,
      Pi.mul_apply,zero_mul,mul_zero,add_zero,Pi.zero_apply] at e
    exact (mul_eq_zero.mp e).resolve_right D.base.origin.g_ne
  have q_at_clean (r : Fin 12) (g0 : g A r=0) (hn : h A r≠0) : Q.eval (nodes A r)=0 := by
    have e := congrFun eq r
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,diag_apply,evalNodes_apply,g0,
      Pi.mul_apply,mul_zero,zero_mul,add_zero,zero_add,Pi.zero_apply] at e
    exact (mul_eq_zero.mp e).resolve_left hn
  have sep : PolySeparated A 4 :=
    PolySeparated.of_coeff (explicit_coeff_separated ha ho (q:=4) (by decide))
  obtain ⟨_,rank3,rank4,_⟩ := order9_forward_chart ha ho (by decide)
  obtain ⟨r2,gr2,xr2,hr2,_⟩ := first_doubled_clean_clock ha sep rank3 rank4 D
  obtain ⟨r3,gr3,x3n,x3d,x32d,h3n⟩ := new_clean_clock_h D ha sep
  let x := nodes A r3
  have qd : Q.eval d=0 := by
    simpa only [D.base.node] using q_at_clean j D.base.clean D.base.first_h.nonzero
  have h2n : h A r2≠0 := by rw [hr2]; exact mul_ne_zero D.base.origin.a_ne (pow_ne_zero _ D.base.dn)
  have q2d : Q.eval (2*d)=0 := by simpa only [xr2] using q_at_clean r2 gr2 h2n
  have qx : Q.eval x=0 := q_at_clean r3 gr3 h3n
  have dt : d≠2*d := by intro e; exact D.base.dn (by linear_combination -e)
  have T : ({d,2*d,x}:Finset K).card=3 := by
    simp [dt,show d≠x from Ne.symm x3d,show 2*d≠x from Ne.symm x32d]
  have Q0 : Q=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q
    ({d,2*d,x}:Finset K) (fun z hz => by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl|rfl <;> assumption) (by
      rw [T]
      exact ofFn_natDegree_lt (by decide) _)
  have p0 : w.1.1=0 := injective_ofFn 6 (P0.trans (ofFn_zero _).symm)
  have q0 : w.1.2.2=0 := injective_ofFn 3 (Q0.trans (ofFn_zero _).symm)
  have tau : w.2≠0 := by
    intro e
    apply nw
    exact Prod.ext (Prod.ext p0 (Prod.ext b0 q0)) e
  have v0 : w.2 • (g A*h A)=0 := by
    have ez : evalNodes A (0:K[X])=0 := by ext r; simp
    simpa only [b0,Q0,ez,map_zero,zero_smul,zero_add] using eq
  ext r
  have e := congrFun v0 r
  simp only [Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at e
  exact (mul_eq_zero.mp e).resolve_left tau

end RKResearch.Certified.Graded.OneOff
