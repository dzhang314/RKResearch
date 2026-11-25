module

public import RKCert.ReviewedNative.ERK13NativeLateLeadingChart
public import RKCert.ReviewedNative.ERK13NativeLateMassRatios
public import RKCert.ReviewedNative.ERK13NativeRadiusTwoRanks
import RKCert.ReviewedNative.ERK13OrdinaryFirstPortCubic
import RKCert.ReviewedNative.BufferedClockLeakage
import RKCert.ReviewedNative.OddForwardBudget
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exclude both leading coefficients for the genuine late radius-two chart

The cancelled branch pays the primitive, exact coprimality and first-port
tests on the original tableau. Seven physical head clocks suffice, using the
measured jump of unmarked subspaces, not any claim that E9 and E10 equal
those subspaces. In the surviving-leading branch the produced class chart
feeds the original signed transpose adapter. -/
namespace RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold

open RKResearch Polynomial Module Reverse PhysicalCensus ERK13OrdinarySquare ERK13NativeFirst
open RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w w₀ : Fin 19 → K}
variable {G P R Q : K[X]}
set_option maxHeartbeats 1200000
set_option maxRecDepth 2100

private theorem section_step_room (n : ℕ) :
    finrank K (lateSection A U w (n+1))≤finrank K (lateSection A U w n)+1 := by
  have eq : lateSection A U w (n+1) =
      lateSection A U w n ⊔ K∙((diag (nodes A)^n) w) := by
    change (coeffEval A 6).range⊔(escapeHeadBand A U w n⊔K∙((diag (nodes A)^n) w))=_
    exact (sup_assoc _ _ _).symm
  rw [eq]
  exact single_span_rank_cap _ _

private theorem wband_step_room (n : ℕ) :
    finrank K (escapeHeadBand A U w n)≤finrank K U+n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have h : finrank K (escapeHeadBand A U w (n+1))≤finrank K (escapeHeadBand A U w n)+1 :=
      single_span_rank_cap _ _
    omega

private theorem late_four_head_pay (S : LateSquareSections A U w G) (m : ℕ) :
    escapeHeadBand A U w (m+1)≤zeroSpace A (4+m) := by
  induction m with
  | zero =>
    apply (clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) 1).mpr
    refine ⟨S.coreFour,?_⟩
    intro k hk
    have e : k=0 := by omega
    simpa only [e,pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using S.headFour
  | succ m ih =>
    change chain (diag (nodes A)) U w ((m+1)+1) ≤ zeroSpace A (4+(m+1))
    rw [←clock_chain_next (w:=w) (n:=m+1) S.coreStable (by omega)]
    apply sup_le
    · exact ih.trans (zeroSpace_mono A (by omega))
    · rintro _ ⟨x,hx,rfl⟩
      exact diag_zeroSpace A (4+m) (ih hx)

private theorem late_four_head_cover (S : LateSquareSections A U w G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (sevenRank : finrank K (treeSpace A 7)=14) :
    zeroSpace A 7≤escapeHeadBand A U w 4 := by
  have D4 : escapeHeadBand A U w 4≤zeroSpace A 7 := late_four_head_pay S 3
  have W4 : lateSection A U w 4≤treeSpace A 7 := by
    apply sup_le _ (D4.trans (zeroSpace_le_treeSpace A 7))
    rintro _ ⟨a,rfl⟩
    exact treeSpace_mono A (by decide : 6≤7) (coeffEval_mem_treeSpace A 6 a)
  have s4 : finrank K (lateSection A U w 5) ≤ finrank K (lateSection A U w 4) + 1 :=
    section_step_room (A:=A) (U:=U) (w:=w) 4
  have s5 : finrank K (lateSection A U w 6) ≤ finrank K (lateSection A U w 5) + 1 :=
    section_step_room (A:=A) (U:=U) (w:=w) 5
  have rank6 := S.nineRank
  have eq : lateSection A U w 4=treeSpace A 7 :=
    Submodule.eq_of_le_of_finrank_le W4 (by omega)
  intro x hx
  have h : x∈lateSection A U w 4 := eq.symm ▸ zeroSpace_le_treeSpace A 7 hx
  obtain ⟨v,⟨a,rfl⟩,d,hd,expr⟩ := Submodule.mem_sup.mp h
  have pv : coeffEval A 6 a∈zeroSpace A 7 := by
    have t := (zeroSpace A 7).sub_mem hx (D4 hd)
    rwa [←expr,add_sub_cancel_right] at t
  have az := coeff_separated_next (q:=6) ha ho (by decide) a pv
  rw [az,map_zero,zero_add] at expr
  exact expr ▸ hd

private theorem late_head_sites (S : LateSquareSections A U w G) :
    7≤(HeadFiber.physicalSites (nodes A) w).card := by
  have move : ¬(escapeHeadBand A U w 6).map (diag (nodes A))≤escapeHeadBand A U w 6 := by
    intro inv
    have same : escapeHeadBand A U w 7=escapeHeadBand A U w 6 :=
      (clock_chain_next (w:=w) S.coreStable (by decide : 0<6)).symm.trans (sup_eq_left.mpr inv)
    have eq : lateSection A U w 7=lateSection A U w 6 :=
      congrArg (fun V : Submodule K (Fin 19 → K)=>(coeffEval A 6).range⊔V) same
    have rank := congrArg (fun V : Submodule K (Fin 19 → K)=>finrank K V) eq
    rw [S.tenRank,S.nineRank] at rank
    omega
  have many := HeadFiber.more_escape_sites (n:=6) S.coreStable (by decide) move
  exact (Nat.succ_le_of_lt many).trans (Finset.card_le_card HeadFiber.escape_le_physical)

/-- The same two physical factor ports used for an ordinary clean head
have no nonzero-first-seed assumption. We explicitly earn all their inputs. -/
theorem LateSquareSections.cancelled_impossible (S : LateSquareSections A U w G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (sevenRank : finrank K (treeSpace A 7)=14)
    {u v : Fin 19 → K} (hu : u∈U) (hv : v∈U)
    (pd : P.natDegree≤6) (rd : R.natDegree≤4) (qd : Q.natDegree≤3)
    (pPay : evalNodes A P∈zeroSpace A 8)
    (sq : w*w=evalNodes A P+weightedEval (nodes A) w R+u)
    (me : evalNodes A G=weightedEval (nodes A) w Q+v)
    (top : (G-R*Q).coeff 7=0) : False := by
  have cap : finrank K (escapeHeadBand A U w 7)≤10 := by
    have c := wband_step_room (A:=A) (U:=U) (w:=w) 7
    rw [S.coreRank] at c
    exact c
  have direct (Z : K[X]) (zd : Z.natDegree≤6) (hm : evalNodes A Z∈escapeHeadBand A U w 7) :
      Z=0 := polynomial_buffer_separated ha ho (q:=6) (h:=10) (by decide) cap S.tenRank zd hm
  have law := transport S.coreStable S.clean hu hv sq me
  have divide := mesh_dvd_square_times_q S.coreStable direct S.meshFour S.degree pd qd rd law top
  have gn : G≠0 := by
    intro e
    have gd := S.degree
    rw [e,natDegree_zero] at gd
    omega
  have gTop : G.coeff 7≠0 := by
    rw [←S.degree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr gn
  have qn : Q≠0 := fun q0=>gTop (by simpa only [q0,mul_zero,sub_zero] using top)
  have gPay := late_four_head_pay S 3 S.meshFour
  have p0 := zero_projection_of_divides (m:=18) ha ho pPay gPay S.degree pd qd qn divide
  have pure : w*w=weightedEval (nodes A) w R+u := by
    simpa only [p0,map_zero,zero_add] using sq
  obtain ⟨dr,dq,factor,amp⟩ := factor_on_seven S.clean hu hv pure me S.degree qd rd top
    (late_head_sites S)
  have packet : ERK13OrdinaryFirstPort.CleanHead A U w G R Q :=
    ⟨S.coreFour,S.coreStable,S.coreClosed,S.headFour,S.clean,amp,
      late_four_head_cover S ha ho sevenRank,gPay,S.degree,dr,dq,factor⟩
  exact packet.impossible ha ho

/-- One native radius-two marked late chart at the true nineteen rows is
already impossible. The grade-four rank is a consequence, not an input. -/
theorem late_radius_two_impossible (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativeMarkedEscapeChart A b 6 G 2 U w₀)
    (late : coordinate (K:=K) (Fin.last 18)∉treeSpace A 7) : False := by
  have four := radius_two_rank_four ha ho H.head
  have rank := (marked_staircase_ranks13 ha ho H.head H.seed).1 7 (by decide) (by decide)
  change finrank K (↥(treeSpace A 7⊔terminalMark A b : Submodule K (Fin 19 → K)))=15 at rank
  have mark : terminalMark A b = K ∙ coordinate (K:=K) (Fin.last 18) := by
    unfold terminalMark
    split
    · rfl
    · exact False.elim (‹firstSeed A b ≠ 0› H.seed)
  rw [mark] at rank
  have full : finrank K (treeSpace A 7) + 1 = 15 :=
    (Submodule.finrank_sup_span_singleton late).symm.trans rank
  have seven : finrank K (treeSpace A 7)=14 := by omega
  obtain ⟨w,P,R,Q,u,hu,v,hv,S,pd,rd,qd,pp,sq,me,build⟩ :=
    mass_chart_producer ha ho H late four
  by_cases top : (G-R*Q).coeff 7=0
  · exact S.cancelled_impossible ha ho seven hu hv pd rd qd pp sq me top
  · exact leading_class_chart_impossible (build top) ha ho H.seed H.head

/-- The declared first escape and radial head are the original paid data.
No separately supplied marked propagation, class chart, or grade rank is required. -/
theorem late_paid_radius_two_impossible (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (zeroSeed : firstSeed A b=0) (H : NativePaidHead A b 2 U w₀)
    (F : FirstEscape A b 6 G) (late : coordinate (K:=K) (Fin.last 18)∉treeSpace A 7) : False :=
  late_radius_two_impossible ha ho (native_marked_escape_chart ha ho zeroSeed H F) late

/-- In the actual late chart, the marked first-alias width need not be
given either: the alternative width would put the terminal in true E7. -/
theorem late_radius_two_ruled_out (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (zeroSeed : firstSeed A b=0) (H : NativePaidHead A b 2 U w₀)
    (late : coordinate (K:=K) (Fin.last 18)∉treeSpace A 7) : False := by
  obtain ⟨a,G,F⟩ := firstEscape_of_paid_rank ha ho H.paidRanks
  rcases F.width with eq | ⟨eq,_⟩
  · subst a
    exact late_paid_radius_two_impossible ha ho zeroSeed H F late
  · subst a
    exact late (terminal_enters_seven_of_first_degree_six13 ha ho zeroSeed F)

end
end RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold
