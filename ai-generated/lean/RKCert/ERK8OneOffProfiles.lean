module

public import RKCert.ERK8OneOffMomentInterfaces
public import Mathlib.Algebra.Polynomial.OfFn

@[expose] public section

/-! Source-only p8 range and rank calculation. The degree-four profile
uses **nine** actual columns; no order-nine dimension theorem is used. -/
namespace RKResearch.Certified.Graded.OneOff.Eight

open RKResearch Polynomial Module Reverse
open scoped Classical Matrix

section GenericCoefficientPorts
variable {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}

omit [CharZero K] in
theorem evalNodes_ofFn (A : Matrix (Fin s) (Fin s) K) (q : ℕ) (v : Fin (q+1) → K) :
    evalNodes A (ofFn (q+1) v) = coeffEval A q v := by
  rw [evalNodes_eq_coeffEval A _ (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) v))]
  congr 1
  ext i
  exact ofFn_coeff_eq_val_of_lt _ i.isLt

abbrev NormalCoeffs (K : Type*) := (Fin 6→K) × (K × (Fin 3→K))
abbrev WideCoeffs (K : Type*) := NormalCoeffs K × K

noncomputable def normalProfileMap (A : Matrix (Fin s) (Fin s) K) :
    NormalCoeffs K →ₗ[K] Fin s → K :=
  (coeffEval A 5).coprod (((LinearMap.id : K →ₗ[K] K).smulRight (g A)).coprod
    ((diag (h A)).comp (coeffEval A 2)))

noncomputable def wideProfileMap (A : Matrix (Fin s) (Fin s) K) :
    WideCoeffs K →ₗ[K] Fin s → K :=
  (normalProfileMap A).coprod ((LinearMap.id : K →ₗ[K] K).smulRight (g A*h A))

noncomputable def wideDefect (A : Matrix (Fin s) (Fin s) K) (w : WideCoeffs K) : Fin s → K :=
  (w.1.2.1 • g A+diag (h A) (evalNodes A (ofFn 3 w.1.2.2)))+w.2 • (g A*h A)

omit [CharZero K] in
theorem normalProfileMap_apply (A : Matrix (Fin s) (Fin s) K) (w : NormalCoeffs K) :
    normalProfileMap A w=evalNodes A (ofFn 6 w.1)+
      (w.2.1 • g A+diag (h A) (evalNodes A (ofFn 3 w.2.2))) := by
  rw [evalNodes_ofFn A 5,evalNodes_ofFn A 2]
  rfl

omit [CharZero K] in
theorem wideProfileMap_apply (A : Matrix (Fin s) (Fin s) K) (w : WideCoeffs K) :
    wideProfileMap A w=evalNodes A (ofFn 6 w.1.1)+wideDefect A w := by
  change normalProfileMap A w.1+w.2 • (g A*h A)=_
  rw [normalProfileMap_apply,wideDefect,add_assoc]

/-- The top coefficient projection is genuinely linear; no degree
computation is taken as a linear operation. -/
def wideTop : WideCoeffs K →ₗ[K] K where
  toFun w := w.1.1 5
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CharZero K] in
theorem wideTop_coeff (w : WideCoeffs K) : (ofFn 6 w.1.1).coeff 5=wideTop w := by
  exact ofFn_coeff_eq_val_of_lt _ (by decide)

omit [CharZero K] in
theorem wide_coeff_rank : finrank K (WideCoeffs K)=11 := by
  norm_num [WideCoeffs,NormalCoeffs,Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_self]

omit [CharZero K] in
theorem nonzero_kernel_of_rank_lt {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (L : V →ₗ[K] W) (lt : finrank K W < finrank K V) : ∃ w, w≠0 ∧ L w=0 := by
  obtain ⟨w,hw,hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f:=L) lt)
  exact ⟨w,hn,LinearMap.mem_ker.mp hw⟩

end GenericCoefficientPorts

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem lastClock (mid : ERKEvenHorizon A b 4) :
    nodes A (Fin.last 9)=1 ∧ coordinate (K:=K) (Fin.last 9)∈treeSpace A 4 := by
  obtain ⟨t,all,_,c,mem⟩ := mid.terminal
  have eq : t=Fin.last 9 := le_antisymm (Fin.le_last t) (all _)
  subst t
  exact ⟨c,mem⟩

theorem frontRanks (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (mid : ERKEvenHorizon A b 4) :
    PolySeparated A 4 ∧ finrank K (zeroSpace A 3)=2 ∧ finrank K (zeroSpace A 4)=3 := by
  have cap : finrank K (treeSpace A 4)≤8 := by simpa only [mid.treeRank] using (le_rfl : 8≤8)
  obtain ⟨r3,r4,_,_⟩ := forward_minimal_ranks ha ho (by decide) cap
  exact ⟨PolySeparated.of_coeff (explicit_coeff_separated ha ho (q:=4) (by decide)),r3,r4⟩

theorem poly_three_roots_zero {Q : K[X]} {x y z : K}
    (qd : Q.natDegree≤2) (xy : x≠y) (xz : x≠z) (yz : y≠z)
    (qx : Q.eval x=0) (qy : Q.eval y=0) (qz : Q.eval z=0) : Q=0 := by
  have T : ({x,y,z}:Finset K).card=3 := by simp [xy,xz,yz]
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q
    ({x,y,z}:Finset K) (fun w hw=>by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl|rfl|rfl <;> assumption) (by rw [T]; omega)

noncomputable def defectPart (A : Matrix (Fin 10) (Fin 10) K) (β : K) (Q : K[X]) :
    Fin 10 → K :=
  β • g A+diag (h A) (evalNodes A Q)

theorem defectPart_mem (ho : HasOrder 8 A b) (β : K) {Q : K[X]} (qd : Q.natDegree≤2) :
    defectPart A β Q∈zeroSpace A 5 := by
  refine (zeroSpace A 5).add_mem
    ((zeroSpace A 5).smul_mem _ (zeroSpace_mono A (by decide : 2≤5) (mDef_mem A 1))) ?_
  exact zeroSpace_mul_treeSpace ho (by decide : 2+1≤8) (h_in_grade_three A)
    (evalNodes_mem_treeSpace A _ qd)

theorem wide_mem_eight (ho : HasOrder 8 A b) (w : WideCoeffs K) :
    wideProfileMap A w∈treeSpace A 5 := by
  rw [wideProfileMap_apply]
  refine (treeSpace A 5).add_mem
    (evalNodes_mem_treeSpace A _ (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _))) ?_
  apply zeroSpace_le_treeSpace A 5
  change defectPart A w.1.2.1 (ofFn 3 w.1.2.2)+w.2 • (g A*h A)∈zeroSpace A 5
  exact (zeroSpace A 5).add_mem
    (defectPart_mem ho _ (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)))
    ((zeroSpace A 5).smul_mem _ (zeroSpace_mul (mDef_mem A 1) (h_in_grade_three A)))

/-- All low polynomial/normal digits vanish, irrespective of the
coefficient of the extra product column. -/
theorem low_relation_zero (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (mid : ERKEvenHorizon A b 4) {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j)
    {P Q : K[X]} {β η : K} (pd : P.natDegree≤4) (qd : Q.natDegree≤2)
    (kn : evalNodes A P+(defectPart A β Q+η • (g A*h A))=0) :
    P=0 ∧ β=0 ∧ Q=0 := by
  let U := defectPart A β Q+η • (g A*h A)
  have um : U∈zeroSpace A 5 :=
    (zeroSpace A 5).add_mem (defectPart_mem ho β qd)
      ((zeroSpace A 5).smul_mem _ (zeroSpace_mul (mDef_mem A 1) (h_in_grade_three A)))
  have pm : evalNodes A P∈zeroSpace A 5 := by
    have e : evalNodes A P= -U := by
      apply add_right_cancel (b:=U)
      rw [show evalNodes A P+U=0 from kn,neg_add_cancel]
    rw [e]
    exact (zeroSpace A 5).neg_mem um
  have gt : g A (Fin.last 9)=0 := terminalDefectZero ho mid
    (zeroSpace_mono A (by decide : 2≤3) (mDef_mem A 1))
  have ht : h A (Fin.last 9)=0 := terminalDefectZero ho mid (h_in_grade_three A)
  have p1 : P.eval 1=0 := by
    have e := congrFun kn (Fin.last 9)
    simpa only [defectPart,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,
      evalNodes_apply,diag_apply,(lastClock mid).1,gt,ht,zero_mul,mul_zero,add_zero,Pi.zero_apply]
      using e
  have p0 := zero_F5_low_top_kernel ha ho pd pm p1
  have b0 : β=0 := by
    have e := congrFun kn i
    simp only [defectPart,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,
      evalNodes_apply,p0,eval_zero,diag_apply,D.base.origin.h_first ha,zero_mul,mul_zero,
      add_zero,zero_add,Pi.zero_apply] at e
    exact (mul_eq_zero.mp e).resolve_right D.base.origin.g_ne
  have clean (r : Fin 10) (g0 : g A r=0) (hn : h A r≠0) : Q.eval (nodes A r)=0 := by
    have e := congrFun kn r
    simp only [defectPart,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,
      evalNodes_apply,p0,eval_zero,diag_apply,g0,mul_zero,zero_mul,
      add_zero,zero_add,Pi.zero_apply] at e
    exact (mul_eq_zero.mp e).resolve_left hn
  obtain ⟨sep,rk3,rk4⟩ := frontRanks ha ho mid
  obtain ⟨r2,gr2,cr2,hr2,_⟩ := first_doubled_clean_clock ha sep rk3 rk4 D
  obtain ⟨r3,gr3,_,xd,xD,hr3⟩ := new_clean_clock_h D ha sep
  have dt : d≠2*d := by intro e; exact D.base.dn (by linear_combination -e)
  have h2n : h A r2≠0 := by rw [hr2]; exact mul_ne_zero D.base.origin.a_ne (pow_ne_zero _ D.base.dn)
  have qd0 : Q.eval d=0 := by simpa only [D.base.node] using clean j D.base.clean D.base.first_h.nonzero
  have qD0 : Q.eval (2*d)=0 := by simpa only [cr2] using clean r2 gr2 h2n
  exact ⟨p0,b0,poly_three_roots_zero qd dt (Ne.symm xd) (Ne.symm xD) qd0 qD0 (clean r3 gr3 hr3)⟩

theorem defectsSeparate (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (mid : ERKEvenHorizon A b 4) {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j) :
    g A*h A=0 := by
  let L := (wideProfileMap A).codRestrict (treeSpace A 5) (wide_mem_eight ho)
  let LL := L.prod (wideTop (K:=K))
  have lt : finrank K ((treeSpace A 5) × K) < finrank K (WideCoeffs K) := by
    rw [Module.finrank_prod,Module.finrank_self,wide_coeff_rank]
    have cap := gradeFiveCap ha ho
    omega
  obtain ⟨w,nw,e⟩ := nonzero_kernel_of_rank_lt LL lt
  have L0 : L w=0 := congrArg Prod.fst e
  have t0 : wideTop w=0 := congrArg Prod.snd e
  have ker : wideProfileMap A w=0 := congrArg Subtype.val L0
  let P := ofFn 6 w.1.1
  let Q := ofFn 3 w.1.2.2
  have pd5 : P.natDegree<6 := ofFn_natDegree_lt (by decide) _
  have pd : P.natDegree≤4 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n n4
    by_cases eq : n=5
    · rw [eq]
      exact (wideTop_coeff w).trans t0
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have kn : evalNodes A P+(defectPart A w.1.2.1 Q+w.2 • (g A*h A))=0 :=
    (wideProfileMap_apply A w).symm.trans ker
  obtain ⟨p0,b0,q0⟩ := low_relation_zero ha ho mid D pd
    (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)) kn
  have nz : w.2≠0 := by
    intro last
    apply nw
    exact Prod.ext (Prod.ext (injective_ofFn 6 (p0.trans (ofFn_zero _).symm))
      (Prod.ext b0 (injective_ofFn 3 (q0.trans (ofFn_zero _).symm)))) last
  ext l
  have val := congrFun kn l
  rw [show Q=0 from q0] at val
  simp only [defectPart,Pi.add_apply,Pi.smul_apply,smul_eq_mul,evalNodes_apply,
    diag_apply,p0,b0,eval_zero,mul_zero,zero_mul,zero_add,Pi.zero_apply] at val
  exact (mul_eq_zero.mp val).resolve_left nz

abbrev ShortCoeffs (K : Type*) := (Fin 5→K) × (K × (Fin 3→K))

noncomputable def shortProfileMap (A : Matrix (Fin 10) (Fin 10) K) :
    ShortCoeffs K →ₗ[K] Fin 10 → K :=
  (coeffEval A 4).coprod (((LinearMap.id : K →ₗ[K] K).smulRight (g A)).coprod
    ((diag (h A)).comp (coeffEval A 2)))

theorem shortProfile_apply (w : ShortCoeffs K) :
    shortProfileMap A w=evalNodes A (ofFn 5 w.1)+defectPart A w.2.1 (ofFn 3 w.2.2) := by
  rw [evalNodes_ofFn A 4,defectPart,evalNodes_ofFn A 2]
  rfl

theorem shortProfile_value (w : ShortCoeffs K) (r : Fin 10) :
    shortProfileMap A w r=(ofFn 5 w.1).eval (nodes A r)+
      (w.2.1*g A r+h A r*(ofFn 3 w.2.2).eval (nodes A r)) := by
  rw [shortProfile_apply,defectPart]
  rfl

/-- Show the nine low columns are independent, not just that a larger
family maps onto an assumed rank-nine space. -/
theorem shortProfileFull (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (mid : ERKEvenHorizon A b 4) {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j) :
    finrank K (treeSpace A 5)=9 ∧ LinearMap.range (shortProfileMap A)=treeSpace A 5 := by
  have inj : Function.Injective (shortProfileMap A) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro w ker
    have kn : evalNodes A (ofFn 5 w.1)+(defectPart A w.2.1 (ofFn 3 w.2.2)+
        (0:K) • (g A*h A))=0 := by
      rw [zero_smul,add_zero,←shortProfile_apply (A:=A) w]
      exact ker
    obtain ⟨p,b0,q⟩ := low_relation_zero ha ho mid D
      (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _))
      (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)) kn
    exact Prod.ext (injective_ofFn 5 (p.trans (ofFn_zero _).symm))
      (Prod.ext b0 (injective_ofFn 3 (q.trans (ofFn_zero _).symm)))
  have bound : LinearMap.range (shortProfileMap A)≤treeSpace A 5 := by
    rintro v ⟨w,rfl⟩
    rw [shortProfile_apply]
    have pd : (ofFn 5 w.1).natDegree≤4 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
    have qd : (ofFn 3 w.2.2).natDegree≤2 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
    exact (treeSpace A 5).add_mem (evalNodes_mem_treeSpace A _ (pd.trans (by decide)))
      (zeroSpace_le_treeSpace A 5 (defectPart_mem ho _ qd))
  have rr := LinearMap.finrank_range_of_inj inj
  have dim : finrank K (ShortCoeffs K)=9 := by
    norm_num [ShortCoeffs,Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_self]
  rw [dim] at rr
  have eq := Submodule.eq_of_le_of_finrank_le bound ((gradeFiveCap ha ho).trans rr.symm.le)
  rw [eq] at rr
  exact ⟨rr,eq⟩

/-- Degree-four polynomial part of a real defect, with no claim that
such a part vanishes at clock one. -/
theorem defectProfile (ho : HasOrder 8 A b)
    (range_eq : LinearMap.range (shortProfileMap A)=treeSpace A 5)
    {a : K} (an : a≠0) {v : Fin 10 → K} (vm : v∈zeroSpace A 5) :
    ∃ (P Q : K[X]) (β : K), P.natDegree≤4 ∧ Q.natDegree≤2 ∧ evalNodes A P∈zeroSpace A 5 ∧
      ∀ r, v r=P.eval (nodes A r)+β*g A r+(h A r/a)*Q.eval (nodes A r) := by
  have vR : v∈LinearMap.range (shortProfileMap A) := range_eq.symm ▸ zeroSpace_le_treeSpace A 5 vm
  obtain ⟨w,hw⟩ := vR
  let P := ofFn 5 w.1
  let Q := ofFn 3 w.2.2
  have Pdeg : P.natDegree≤4 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have Qdeg : Q.natDegree≤2 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have hP : evalNodes A P∈zeroSpace A 5 := by
    have mem : shortProfileMap A w∈zeroSpace A 5 := by rw [hw]; exact vm
    rw [shortProfile_apply] at mem
    change evalNodes A P+defectPart A w.2.1 Q∈zeroSpace A 5 at mem
    simpa only [add_sub_cancel_right] using
      (zeroSpace A 5).sub_mem mem (defectPart_mem ho w.2.1 Qdeg)
  refine ⟨P,C a*Q,w.2.1,Pdeg,(natDegree_C_mul_le _ _).trans Qdeg,hP,?_⟩
  intro r
  rw [←hw,shortProfile_value,eval_mul,eval_C]
  dsimp only [P,Q]
  field_simp [an] <;> ring

/-- The one-dimensionality actually needed later: two polynomial parts
with the paid degree-four defect conditions are proportional. -/
theorem proportional_eval {P Q : K[X]} (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 8 A b) (pd : P.natDegree≤4) (qd : Q.natDegree≤4)
    (pm : evalNodes A P∈zeroSpace A 5) (qm : evalNodes A Q∈zeroSpace A 5)
    {x : K} (px : P.eval x≠0) (qx : Q.eval x=0) : Q=0 := by
  have Ptop : P.coeff 4≠0 := by
    intro top
    have d3 : P.natDegree≤3 := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n nb
      by_cases e : n=4
      · simpa only [e] using top
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    exact px (by rw [zero_F5_poly_le_three ha ho d3 pm,eval_zero])
  let t := Q.coeff 4/P.coeff 4
  let R := Q-t • P
  have rd4 : R.natDegree≤4 := (natDegree_sub_le _ _).trans
    (max_le qd ((natDegree_smul_le _ _).trans pd))
  have r4 : R.coeff 4=0 := by
    rw [show R=Q-t • P from rfl,coeff_sub,Polynomial.coeff_smul,smul_eq_mul]
    change Q.coeff 4-(Q.coeff 4/P.coeff 4)*P.coeff 4=0
    rw [div_mul_cancel₀ _ Ptop,sub_self]
  have rd : R.natDegree≤3 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n nb
    by_cases e : n=4
    · simpa only [e] using r4
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have rm : evalNodes A R∈zeroSpace A 5 := by
    rw [show R=Q-t • P from rfl,map_sub,map_smul]
    exact (zeroSpace A 5).sub_mem qm ((zeroSpace A 5).smul_mem _ pm)
  have r0 := zero_F5_poly_le_three ha ho rd rm
  change Q-t • P=0 at r0
  have qq := sub_eq_zero.mp r0
  have val := congrArg (fun U : K[X] => U.eval x) qq
  rw [qx,eval_smul,smul_eq_mul] at val
  have tz := (mul_eq_zero.mp val.symm).resolve_right px
  simpa only [tz,zero_smul] using qq

end RKResearch.Certified.Graded.OneOff.Eight
