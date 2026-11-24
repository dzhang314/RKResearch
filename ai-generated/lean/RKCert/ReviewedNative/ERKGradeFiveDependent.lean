module

public import RKCert.ReviewedNative.ERKGradeFiveProfiles
import RKCert.ReviewedNative.OneOffFifth

@[expose] public section

/-! # Closing the eigenvector branch of the native grade-five surplus
The proof keeps every original stage, including repeated clocks and
identical prior rows. A calibrated A(CAg) forces zero inlet along the
first doubled clock, and two low-degree identities forbid a new
amplitude there. This is not a replay of the old finite five-row packet. -/
namespace RKResearch.Certified.Graded
open RKResearch Polynomial Module OneOff
open scoped Matrix Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}

omit [CharZero K] in
private theorem preliminary_h_zero {a : K} {i : Fin s}
    (ha : ∀ j k,j ≤ k → A j k=0) (O : Origin A a i) :
    ∀ l, l ≤ i → h A l=0 :=
  fun l li => causal_mat ha l _ (fun m ml => O.earlier_defect m (ml.trans_le li))

/-- Minimal rank makes the first two genuine defect columns disjoint,
with no requirement that any individual output weight is positive. -/
theorem OneOff.GlobalNormal.disjoint_defects_of_minimal_five {a d : K} {i j : Fin s}
    (D : GlobalNormal A a d i j) (ha : ∀ i k,i ≤ k → A i k=0)
    (sep : PolySeparated A 5) (cap : finrank K (zeroSpace A 5)≤4) :
    g A*h A=0 := by
  obtain ⟨_,r3,r4,_⟩ := minimal_grade_five_ranks ha sep cap
  have sep4 := sep.mono (by decide : 4≤5)
  have hm := zeroSpace_mul (m:=2) (n:=3) (mDef_mem A 1) (h_in_grade_three A)
  obtain ⟨α,P,pd,e⟩ := D.five_defect_of_minrank ha sep cap hm
  obtain ⟨t,gt,nt,ht,_⟩ := first_doubled_clean_clock ha sep4 r3 r4 D
  obtain ⟨r,gr,_,rd,rt,hr⟩ := new_clean_clock_h D ha sep4
  have root (l : Fin s) (gl : g A l=0) (hl : h A l≠0) :
      P.eval (nodes A l)=0 := by
    have z:=e l
    change g A l*h A l = _ at z
    rw [gl,zero_mul,mul_zero,zero_add] at z
    exact (mul_eq_zero.mp z.symm).resolve_right hl
  have p₁ := root j D.base.clean D.base.first_h.nonzero
  have atd : P.eval d=0 := by simpa only [D.base.node] using p₁
  have p₂ := root t gt (ht ▸ mul_ne_zero D.base.origin.a_ne (pow_ne_zero _ D.base.dn))
  have at2d : P.eval (2*d)=0 := by simpa only [nt] using p₂
  have atx := root r gr hr
  have dt : d≠2*d := by
    intro h
    apply D.base.dn
    linear_combination -h
  let sites : Finset K := {d,2*d,nodes A r}
  have sz : sites.card=3 := by
    simp [sites,dt,Ne.symm rd,Ne.symm rt]
  have pz : P=0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P sites
    · intro x hx
      simp only [sites,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl
      · exact atd
      · exact at2d
      · exact atx
    · omega
  have a0 : α=0 := by
    have z := e i
    change g A i*h A i = _ at z
    rw [D.base.origin.h_first ha,mul_zero,pz,eval_zero,zero_mul,add_zero] at z
    exact (mul_eq_zero.mp z.symm).resolve_right D.base.origin.g_ne
  ext l
  change g A l*h A l=0
  simpa only [g,Pi.mul_apply,a0,pz,eval_zero,zero_mul,add_zero] using e l

private theorem matrix_delta_zero_on_doubled {a d : K} {i j : Fin s}
    (D : GlobalNormal A a d i j) (ha : ∀ i k,i ≤ k → A i k=0)
    (sep : PolySeparated A 5) (cap : finrank K (zeroSpace A 5)≤4) :
    ∀ l, nodes A l=2*d → mat A (deltaH A d) l=0 := by
  obtain ⟨_,r3,r4,_⟩ := minimal_grade_five_ranks ha sep cap
  let v := mat A (diag (nodes A) (h A))
  have vm : v∈zeroSpace A 5 := mat_zeroSpace_charZero A 4 (diag_zeroSpace A 3 (h_in_grade_three A))
  obtain ⟨α,P,_,e⟩ := D.five_defect_of_minrank ha sep cap vm
  have vi : v i=0 := by
    apply causal_mat ha i
    intro k ki
    simp [preliminary_h_zero ha D.base.origin k ki.le]
  have a0 : α=0 := by
    have eq := e i
    rw [vi,D.base.origin.h_first ha,mul_zero,add_zero] at eq
    exact (mul_eq_zero.mp eq.symm).resolve_right D.base.origin.g_ne
  obtain ⟨t,_,tc,th,pre⟩ := first_doubled_clean_clock ha (sep.mono (by decide)) r3 r4 D
  have hAt : mat A (deltaH A d) t=0 := by
    apply causal_mat ha t
    intro l lt
    rw [deltaH_apply]
    rcases pre l lt with f|f|f
    · rw [f.2.2,mul_zero]
    · rw [f.2.2,mul_zero]
    · rw [f.1,sub_self,zero_mul]
  have value (l : Fin s) (lc : nodes A l=2*d) :
      mat A (deltaH A d) l=(P.eval (2*d)+d^2)*h A l := by
    have z := e l
    rw [a0,zero_mul,zero_add,lc] at z
    have kl := congrFun D.hk l
    change mat A (h A) l = _ at kl
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply,lc] at kl
    rw [deltaH,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    change v l-d*mat A (h A) l=_
    rw [z,kl]
    ring
  have hn : h A t≠0 := th ▸ mul_ne_zero D.base.origin.a_ne (pow_ne_zero _ D.base.dn)
  have root : P.eval (2*d)+d^2=0 :=
    (mul_eq_zero.mp ((value t tc).symm.trans hAt)).resolve_right hn
  intro l lc
  rw [value l lc,root,zero_mul]

/-- At a doubled clock the third and fourth clock primitives already
pin down the amplitude, once the genuinely calibrated input is zero. -/
private theorem doubled_amplitude_from_prefix {a d : K} {i j r : Fin s}
    (D : GlobalNormal A a d i j) (ha : ∀ i k,i ≤ k → A i k=0)
    (pre : ∀ l, l < r → NormalFour a d (2*d) (twoHd a d) (normHe a d (2*d))
      (nodes A l) (g A l) (h A l))
    (cr : nodes A r=2*d) (gr : g A r=0) (tap : mat A (deltaH A d) r=0) :
    h A r=a*d^2 := by
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  let c := nodes A
  let U : Fin s→K := (a*d^2) • (c^2)
  let V : Fin s→K := (a^2*d^2) • c + (4*d*(a-d)) • h A + (8*d-6*a) • deltaH A d
  let U' : Fin s→K := (a*d^2) • (c^3)
  let V' : Fin s→K := (a^3*d^2) • c + (4*d*(a^2-d^2)) • h A + (12*d^2-6*a^2) • deltaH A d
  have fit (l : Fin s) (lr : l < r) : U l=V l ∧ U' l=V' l := by
    have f := pre l lr
    rw [normHe_doubled a d dn] at f
    rcases f with (e|e|e)|e <;> rcases e with ⟨cx,_,hx⟩ <;>
      constructor <;>
      simp only [U,V,U',V',c,Pi.smul_apply,smul_eq_mul,Pi.add_apply,Pi.pow_apply,
        deltaH_apply,cx,hx,twoHd] <;> ring
  have e₂ := causal_action_eq ha r U V (fun l lr => (fit l lr).1)
  have e₃ := causal_action_eq ha r U' V' (fun l lr => (fit l lr).2)
  simp only [U,V,U',V',map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,tap,mul_zero,add_zero] at e₂ e₃
  have k₀ := congrFun D.hk r
  change mat A (h A) r=_ at k₀
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply,cr] at k₀
  have m₁:=m1_relation A r
  have m₂:=m2_relation D.base.q2 r
  have m₃:=congrFun D.q3 r
  simp only [mDef_apply,Nat.reduceAdd,Nat.cast_ofNat,Pi.add_apply,Pi.smul_apply,Pi.sub_apply,
    smul_eq_mul,diag_apply,cr,gr,mul_zero,zero_add] at m₃
  simp only [cr,gr,twoLam,mul_zero,add_zero] at m₁ m₂
  change mat A c r=_ at m₁
  change mat A (c^2) r=_ at m₂
  rw [m₁,m₂,k₀] at e₂
  rw [m₁,k₀] at e₃
  have q₂ : (3*a-4*d)*(h A r-a*d^2)=0 := by
    field_simp [an] at e₂
    linear_combination (1/2:K)*e₂
  have q₃ : (a^2-2*d^2)*(h A r-a*d^2)=0 := by
    have id : mat A (c^3) r=(4:K)*d^4-2*a*h A r := by
      calc
        _ = (2*d)^4/4 + ((2*d^2-2*a^2)/a*h A r - d/a*(2*d*h A r)) := by
          change mat A (c^3) r - (2*d)^4/4 = _ at m₃
          linear_combination m₃
        _ = _ := by field_simp [an]; ring
    rw [id] at e₃
    apply mul_left_cancel₀ (pow_ne_zero 2 dn)
    linear_combination (1/2:K)*e₃
  by_contra mismatch
  have e := (mul_eq_zero.mp q₂).resolve_right (sub_ne_zero.mpr mismatch)
  have e' := (mul_eq_zero.mp q₃).resolve_right (sub_ne_zero.mpr mismatch)
  apply (pow_ne_zero 2 dn)
  linear_combination ((3*a+4*d)/2)*e-(9/2:K)*e'

/-- Genuine separation alone excludes the one-clock quadratic
eigenline in a four-dimensional grade-five defect flag. -/
theorem grade_five_surplus_of_dependent_quadratic
    (ha : ∀ i j,i ≤ j → A i j=0) (sep : PolySeparated A 5)
    (dep : diag (nodes A) (g A)∈Submodule.span K {g A}) :
    5≤finrank K (zeroSpace A 5) := by
  by_contra! bad
  have cap : finrank K (zeroSpace A 5)≤4 := by omega
  obtain ⟨_,r3,r4,_⟩ := minimal_grade_five_ranks ha sep cap
  have sep4 := sep.mono (by decide : 4≤5)
  obtain ⟨a,d,i,j,B⟩ := constant_amplitude_of_grade_five_dependence ha sep cap dep
  let D := global_normal_from_amplitude ha sep4 r3 r4 B
  have dis := D.disjoint_defects_of_minimal_five ha sep cap
  have taps := matrix_delta_zero_on_doubled D ha sep cap
  obtain ⟨x,C⟩ := normal_clock_calibration ha sep4 r3 r4 D.base
  have eq := normal_clock_doubles ha sep4 D.base C
  subst x
  have all (r : Fin s) : NormalFour a d (2*d) (twoHd a d) (normHe a d (2*d))
      (nodes A r) (g A r) (h A r) := by
    refine wellFounded_lt.induction (C:=fun l : Fin s =>
      NormalFour a d (2*d) (twoHd a d) (normHe a d (2*d)) (nodes A l) (g A l) (h A l)) r ?_
    intro r ih
    by_cases go : g A r=0
    · obtain ⟨u,v⟩ := four_feature_residuals ha D.base C r ih
      rw [go] at u v
      rcases normal_clean_clocks a d (2*d) _ _ B.origin.a_ne B.dn C.dNorm u v with cx|cx|cx
      · rw [cx] at u v
        exact Or.inl (Or.inl ⟨cx,go,normal_clean_at_zero _ _ _ _ B.dn C.en u v⟩)
      · rw [cx] at u v
        exact Or.inl (Or.inr (Or.inr ⟨cx,go,normal_clean_at_d _ _ _ _ B.dn C.dNorm u v⟩))
      · have h0 := doubled_amplitude_from_prefix D ha ih cx go (taps _ cx)
        rw [normHe_doubled a d B.dn]
        exact Or.inr ⟨cx,go,h0⟩
    · have z := congrFun dis r
      change g A r*h A r=0 at z
      exact Or.inl (Or.inr (Or.inl ⟨B.origin.off_support r go,
        amplitude_value B.amplitude go,(mul_eq_zero.mp z).resolve_left go⟩))
  apply sep4.knots_not_cover ({0,a,d,2*d}:Finset K)
  · exact (Finset.card_insert_le ..).trans (Nat.succ_le_succ ((Finset.card_insert_le ..).trans
      (Nat.succ_le_succ ((Finset.card_insert_le ..).trans (by simp)))))
  · intro r
    rcases all r with (x|x|x)|x <;> simp [x.1]

end RKResearch.Certified.Graded
