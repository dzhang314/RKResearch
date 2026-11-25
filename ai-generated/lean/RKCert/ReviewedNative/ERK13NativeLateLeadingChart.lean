module

public import RKCert.ReviewedNative.ERK13NativeLateClassCensus
public import RKCert.ReviewedNative.ERK13NativeLateCleanHead
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Produce the leading late square chart from the physical radius-two staircase

There are no assumptions on the true grade-nine or grade-ten ranks, phase
counts, observer masks, or signed masses. The true grade-eight equality is
proved, not assumed: a true terminal there would force every F4 column
zero at the last row, contradicting the literal nonvanishing paid mesh.
At grades nine and ten only the marked ranks are used. -/
namespace RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold

open RKResearch Polynomial Module Reverse PhysicalCensus ERK13OrdinarySquare ERK13NativeFirst
open RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w w₀ : Fin 19 → K}
variable {G P R Q : K[X]}
set_option maxHeartbeats 1300000
set_option maxRecDepth 2100

private theorem strip_absent_line {E W : Submodule K (Fin 19 → K)} {z v : Fin 19 → K}
    (WE : W≤E) (out : z∉E) (hE : v∈E) (hz : v∈W⊔K∙z) : v∈W := by
  obtain ⟨d,hd,t,ht,rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp ht
  by_cases az : a=0
  · simpa only [az,zero_smul,add_zero] using hd
  · have diff := E.sub_mem hE (WE hd)
    have eq : (d+a • z)-d=a • z := by abel
    rw [eq] at diff
    exact (out ((E.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr az)).mp diff)).elim

private theorem band_size_cap (n : ℕ) :
    finrank K (escapeHeadBand A U w n)≤finrank K U+n := by
  induction n with
  | zero =>
    change finrank K U≤finrank K U+0
    omega
  | succ n ih =>
    by_cases mem : (diag (nodes A)^n) w∈escapeHeadBand A U w n
    · have eq : escapeHeadBand A U w (n+1)=escapeHeadBand A U w n :=
        sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr mem)
      rw [eq]
      omega
    · change finrank K (↥(escapeHeadBand A U w n ⊔
          (K ∙ ((diag (nodes A)^n) w)) : Submodule K (Fin 19 → K))) ≤ _
      rw [Submodule.finrank_sup_span_singleton mem]
      omega

private theorem section_size_cap (n : ℕ) (ur : finrank K U=3) :
    finrank K (lateSection A U w n)≤10+n := by
  let V := (coeffEval A 6).range
  let B := escapeHeadBand A U w n
  have vp : finrank K V≤7 :=
    (LinearMap.finrank_range_le (coeffEval A 6)).trans_eq (Module.finrank_fin_fun K)
  have bp : finrank K B≤3+n := by
    have h := band_size_cap (A:=A) (U:=U) (w:=w) n
    rwa [ur] at h
  have dim := Submodule.finrank_sup_add_finrank_inf_eq V B
  change finrank K (↥(V⊔B : Submodule K (Fin 19 → K)))≤10+n
  omega

private theorem rank_before_line {V : Submodule K (Fin 19 → K)} {z : Fin 19 → K} {n : ℕ}
    (cap : finrank K V≤n)
    (total : finrank K (↥(V⊔K∙z : Submodule K (Fin 19 → K)))=n+1) :
    finrank K V=n ∧ z∉V := by
  have out : z∉V := by
    intro vz
    have eq : V⊔K∙z=V := sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr vz)
    rw [eq] at total
    omega
  rw [Submodule.finrank_sup_span_singleton out] at total
  exact ⟨by omega,out⟩

private theorem late_seven_value_one_ne (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (degree : G.natDegree=7) (paid : evalNodes A G∈zeroSpace A 7) : G.eval 1≠0 := by
  apply HyperplaneTerminal.seven_paid_not_one degree
  · have orig := origin_zeroSpace ha 7 paid
    have c0 : nodes A (0:Fin 19)=0 := by
      change (∑ j,A 0 j*1)=0
      exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le _),zero_mul]
    change G.eval (nodes A (0:Fin 19))=0 at orig
    rwa [c0] at orig
  · intro i
    have hi := i.isLt
    exact (probe_evalNodes ho G i.val (by omega)).symm.trans
      (probe_zeroSpace (k:=i.val) ho (by omega) paid)

private theorem terminal_in_eight_kills_four (ho : HasOrder 13 A b)
    (L : LastActive b (Fin.last 18))
    (term : coordinate (K:=K) (Fin.last 18)∈treeSpace A 8)
    {x : Fin 19 → K} (hx : x∈zeroSpace A 4) : x (Fin.last 18)=0 := by
  have prod := zeroSpace_mul_treeSpace ho (m:=4) (n:=8) (by decide) hx term
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

/-- Earned data before splitting the two possible leading coefficients.
Grades nine and ten have only an unmarked *subspace* inside the true
space. Their dimensions come from adjoining the literal marked line. -/
structure LateSquareSections (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K) (G : K[X]) : Prop where
  coreStable : U.map (diag (nodes A))≤U
  coreClosed : ∀ x∈U, ∀ y∈U,x*y∈U
  clean : ∀ i,LiveCore.live U i → w i=0
  coreFour : U≤zeroSpace A 4
  headFour : w∈zeroSpace A 4
  coreRank : finrank K U=3
  degree : G.natDegree=7
  meshFour : evalNodes A G∈escapeHeadBand A U w 4
  fivePaid : escapeHeadBand A U w 5≤zeroSpace A 8
  eight : treeSpace A 8=lateSection A U w 5
  ninePaid : lateSection A U w 6≤treeSpace A 9
  nineRank : finrank K (lateSection A U w 6)=16
  tenPaid : lateSection A U w 7≤treeSpace A 10
  tenRank : finrank K (lateSection A U w 7)=17
  tenOut : coordinate (K:=K) (Fin.last 18)∉lateSection A U w 7

theorem late_square_sections_of_staircase
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativeMarkedEscapeChart A b 6 G 2 U w₀)
    (late : coordinate (K:=K) (Fin.last 18)∉treeSpace A 7)
    (four : finrank K (zeroSpace A 4)=4) :
    ∃ w : Fin 19 → K, LateSquareSections A U w G := by
  obtain ⟨w,coreFour,ur,wFour,closed,clean,common⟩ := late_clean_radius_two_head ha ho H four
  let L := Fin.last 18
  let z := coordinate (K:=K) L
  have gd : G.natDegree=7 := H.first.degree
  have old (m : ℕ) : escapeHeadBand A U w (4+m)=escapeHeadBand A U w₀ (4+m) := by
    rw [show 4+m=(m+2)+2 by omega]
    exact common (m+2)
  have headPay (m : ℕ) : escapeHeadBand A U w (4+m)≤zeroSpace A (7+m) := by
    rw [old m]
    exact escapeHeadBand_paid_from_seven H.head m
  have coeffPay : (coeffEval A 6).range≤treeSpace A 6 := by
    rintro _ ⟨a,rfl⟩
    exact coeffEval_mem_treeSpace A 6 a
  have sectionPay (m : ℕ) : lateSection A U w (4+m)≤treeSpace A (7+m) :=
    sup_le (coeffPay.trans (treeSpace_mono A (by omega)))
      ((headPay m).trans (zeroSpace_le_treeSpace A (7+m)))
  have marked (m : ℕ) (hm : 7+m≤10) :
      markedTreeSpace A b (7+m)=lateSection A U w (4+m)⊔K∙z := by
    have e := H.chart m hm
    change markedTreeSpace A b (7+m)=(coeffEval A 6).range⊔
      (escapeHeadBand A U w₀ (4+m)⊔terminalMark A b) at e
    rw [←old m,terminalMark,if_pos H.seed,←sup_assoc] at e
    exact e
  have rks := (marked_staircase_ranks13 ha ho H.head H.seed).1
  have measured (m : ℕ) (hm : 7+m≤10) :
      finrank K (lateSection A U w (4+m))=14+m ∧ z∉lateSection A U w (4+m) := by
    apply rank_before_line
    · have cap := section_size_cap (A:=A) (U:=U) (w:=w) (4+m) ur
      omega
    · rw [←marked m hm,rks (7+m) (by omega) hm]
      omega
  have gMark : evalNodes A G∈escapeHeadBand A U w 4⊔K∙z := by
    have e := H.first.paid
    rw [H.head.escapeShape,terminalMark,if_pos H.seed] at e
    have common4 : escapeHeadBand A U w 4=escapeHeadBand A U w₀ 4 := old 0
    rw [common4]
    exact e
  have g4 : evalNodes A G∈escapeHeadBand A U w 4 :=
    strip_absent_line ((headPay 0).trans (zeroSpace_le_treeSpace A 7)) late
      (evalNodes_mem_treeSpace A G gd.le) gMark
  have gOne := late_seven_value_one_ne ha ho gd (headPay 0 g4)
  have notEight : z∉treeSpace A 8 := by
    intro term
    have w0 : w L=0 := terminal_in_eight_kills_four ho H.head.paidRanks.lastActive term wFour
    obtain ⟨t,ht,J,_,shape⟩ := HeadFiber.exists_poly g4
    have t0 : t L=0 := terminal_in_eight_kills_four ho H.head.paidRanks.lastActive term (coreFour ht)
    have val := congrFun shape L
    have cOne : nodes A L=1 := H.head.paidRanks.lastActive.node_eq_one ha H.seed
    apply gOne
    simpa only [evalNodes_apply,Pi.add_apply,weightedEval_apply,cOne,w0,t0,mul_zero,add_zero] using val
  have eight : treeSpace A 8=lateSection A U w 5 := by
    refine le_antisymm ?_ (sectionPay 1)
    intro v hv
    have e : v∈markedTreeSpace A b (7+1) := Submodule.mem_sup_left hv
    rw [marked 1 (by decide)] at e
    exact strip_absent_line (sectionPay 1) notEight hv e
  exact ⟨w,H.head.head.coreStable,closed,clean,coreFour,wFour,ur,gd,g4,headPay 1,
    eight,sectionPay 2,(measured 2 (by decide)).1,sectionPay 3,
    (measured 3 (by decide)).1,(measured 3 (by decide)).2⟩

theorem LateSquareSections.massChart_of_leading (S : LateSquareSections A U w G)
    {u v : Fin 19 → K} (hu : u∈U) (hv : v∈U)
    (square : w*w=evalNodes A P+weightedEval (nodes A) w R+u)
    (mesh : evalNodes A G=weightedEval (nodes A) w Q+v)
    (pd : P.natDegree≤6) (rd : R.natDegree≤4) (qd : Q.natDegree≤3)
    (top : (G-R*Q).coeff 7≠0) : MassClassChart A U w P R Q G := by
  obtain ⟨eq,count⟩ := late_section_full_of_leading S.coreStable S.coreClosed S.clean
    S.coreRank S.tenRank hu hv square mesh S.degree pd rd qd top
  have lower : treeSpace A 8≤unmarkedClasses A U w := by
    rw [S.eight]
    exact (late_phase_census S.coreStable S.coreClosed S.clean 5).1
  exact ⟨S.coreStable,S.coreClosed,S.clean,S.coreFour,S.headFour,lower,
    (late_phase_census S.coreStable S.coreClosed S.clean 6).1,S.ninePaid,S.nineRank,
    eq ▸ S.tenPaid,eq ▸ S.tenRank,eq ▸ S.tenOut,count,⟨u,hu,square⟩,⟨v,hv,mesh⟩,
    pd,rd,qd,S.degree,top⟩

/-- Produce the canonical square and mesh first, then the actual consumer chart
if their transported leading coefficient survives. All inputs are on the true
tableau and its measured marked first-escape chart, not on class weights. -/
theorem mass_chart_producer (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativeMarkedEscapeChart A b 6 G 2 U w₀)
    (late : coordinate (K:=K) (Fin.last 18)∉treeSpace A 7)
    (four : finrank K (zeroSpace A 4)=4) :
    ∃ w : Fin 19 → K, ∃ P R Q : K[X], ∃ u∈U, ∃ v∈U,
      LateSquareSections A U w G ∧ P.natDegree≤6 ∧ R.natDegree≤4 ∧ Q.natDegree≤3 ∧
      evalNodes A P∈zeroSpace A 8 ∧
      w*w=evalNodes A P+weightedEval (nodes A) w R+u ∧
      evalNodes A G=weightedEval (nodes A) w Q+v ∧
      ((G-R*Q).coeff 7≠0 → MassClassChart A U w P R Q G) := by
  obtain ⟨w,S⟩ := late_square_sections_of_staircase ha ho H late four
  obtain ⟨P,R,Q,u,v,hu,hv,pd,rd,qd,pp,sq,me⟩ := charts_of_paid_square
    S.eight S.fivePaid (zeroSpace_mul S.headFour S.headFour) S.meshFour
  exact ⟨w,P,R,Q,u,hu,v,hv,S,pd,rd,qd,pp,sq,me,S.massChart_of_leading hu hv sq me pd rd qd⟩

end
end RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold
