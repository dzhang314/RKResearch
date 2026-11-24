module

public import RKCert.RadauMissingRoot
public import RKCert.Dirk15NativePivots

@[expose] public section

/-! # Ordinary quartic payment from three missing true non-C(2) ports
The remaining count of missing ports is a separate rank question.
This module proves what the three actual missing ports imply. -/
namespace RKCert.Paired
open RKCert.Endpoint RKCert.OneEscape Polynomial Signature
open RKCert.FixedPolynomial.Radau77569
open scoped Classical

noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

theorem left_three_affine_cut (u a b c : K) (hu : u≠0)
    (distinct : Function.Injective (![u,a,b,c] : Fin 4→K))
    (ports : ∀ i : Fin 4, IsLeftRadauPort ((![u,a,b,c] : Fin 4→K) i))
    (Q : K[X]) (dQ : Q.natDegree≤4) (aQ : Q.eval a=0) (bQ : Q.eval b=0) (cQ : Q.eval c=0)
    (h₁ : paidMoment Q u 1=0) (h₂ : paidMoment Q u 2=0) : Q=0 := by
  by_contra hQ
  have ab : a≠b := fun e => (by decide : (1:Fin 4)≠2) (distinct e)
  have ac : a≠c := fun e => (by decide : (1:Fin 4)≠3) (distinct e)
  have bc : b≠c := fun e => (by decide : (2:Fin 4)≠3) (distinct e)
  let T := cubicFactor a b c
  have hT : T≠0 := mul_ne_zero (mul_ne_zero (monic_X_sub_C a).ne_zero (monic_X_sub_C b).ne_zero)
    (monic_X_sub_C c).ne_zero
  have div : T∣Q := by
    have ab' := isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ab).isUnit
    have ac' := isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ac).isUnit
    have bc' := isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr bc).isUnit
    exact (ac'.mul_left bc').mul_dvd
      (ab'.mul_dvd (dvd_iff_isRoot.mpr aQ) (dvd_iff_isRoot.mpr bQ)) (dvd_iff_isRoot.mpr cQ)
  obtain ⟨S,e⟩ := div
  have hS : S≠0 := fun hz => hQ (by rw [e,hz,mul_zero])
  have dT : T.natDegree=3 := by
    unfold T cubicFactor
    rw [natDegree_mul (mul_ne_zero (monic_X_sub_C a).ne_zero (monic_X_sub_C b).ne_zero)
      (monic_X_sub_C c).ne_zero,natDegree_mul (monic_X_sub_C a).ne_zero (monic_X_sub_C b).ne_zero,
      natDegree_X_sub_C,natDegree_X_sub_C,natDegree_X_sub_C]
  have dS : S.natDegree≤1 := by
    rw [e,natDegree_mul hT hS,dT] at dQ
    omega
  have he : Q=S*T := e.trans (mul_comm _ _)
  have impossible := left_three_primitive_gram_ne u a b c hu distinct ports
  apply impossible
  exact affine_gram_zero S T hS dS u 1 (by rwa [←he]) (by rwa [←he])

private theorem native_nonC2_quartic_trace (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15NonC2Chart A b) {v : Vec K 20} (hv : v∈zeroSpace A 4) :
    ∃ Q : K[X], Q.natDegree≤4 ∧
      (∀ i, reverseCubic A b i≠0 → v i=Q.eval (mirror A i)) ∧
      (∀ i, b i≠0 → reverseCubic A b i=0 → v i=0) := by
  have hτ : reverseCubic A b∈marked A 15 3 := seed3_marked ho (by decide)
  have hp : reverseCubic A b*v∈marked A 15 7 :=
    marked_mul_tree (j:=3) (k:=4) (by decide) hτ (zeroSpace_le_treeSpace A 4 hv)
  rw [order15_nonC2_reverse_orbit ha ho h 7 (by decide) (by decide)] at hp
  obtain ⟨u,hu,Q,hQ,eQ⟩ := Clock.exists_head_poly hp
  have u0 : u=0 := by simpa using hu
  have dQ : Q.natDegree≤4 := by
    by_cases h0 : Q=0
    · simp [h0]
    · have := (natDegree_lt_iff_degree_lt h0).mpr hQ
      omega
  have hbv := weights_mul_zeroSpace ho (by decide : 4+1≤15) hv
  rw [order15_nonC2_reverse_orbit ha ho h 4 (by decide) (by decide)] at hbv
  obtain ⟨r,hr,R,_,eR⟩ := Clock.exists_head_poly hbv
  have r0 : r=0 := by simpa using hr
  refine ⟨Q,dQ,?_,?_⟩
  · intro i hi
    apply mul_left_cancel₀ hi
    simpa only [Pi.mul_apply,u0,Pi.zero_apply,zero_add,mul_comm (Q.eval _)] using eQ i
  · intro i bi ti
    have e : b i*v i=0 := by
      simpa only [Pi.mul_apply,r0,Pi.zero_apply,zero_add,ti,mul_zero] using eR i
    exact (mul_eq_zero.mp e).resolve_left bi

set_option maxHeartbeats 600000 in
/-- In a non-C(2) twenty-stage order-fifteen array, three distinct true
missing ports already force all grade-four columns to vanish on both
physical channels. This theorem neither assumes the grade-four rank nor
obtains the three missing ports from the stage count. -/
theorem order15_nonC2_quartics_of_three_missing (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) (hq : q₂ (mat A) (nodes A) 1≠0)
    (a d e : K) (ad : a≠d) (ae : a≠e) (de : d≠e)
    (ha' : IsLeftRadauPort a) (hd' : IsLeftRadauPort d) (he' : IsLeftRadauPort e)
    (missing : ∀ i, b i≠0 → reverseCubic A b i=0 →
      mirror A i≠a ∧ mirror A i≠d ∧ mirror A i≠e)
    {v : Vec K 20} (hv : v∈zeroSpace A 4) :
    ∀ i,b i≠0 ∨ reverseCubic A b i≠0 → v i=0 := by
  have h := order15_nonC2_rank_chart ha ho hq
  obtain ⟨Q,dQ,mDirty,mClean⟩ := native_nonC2_quartic_trace ha ho h hv
  let θ := weightedEval (mirror A) b Q-b*v
  have trace : ReverseTrace A b 15 4 θ Q :=
    (ReverseTrace.scalar A b dQ).sub_pure (weights_mul_zeroSpace ho (by decide : 4+1≤15) hv)
  have support (i : Fin 20) (hi : θ i≠0) :
      b i≠0 ∧ reverseCubic A b i=0 ∧ IsLeftRadauPort (mirror A i) := by
    have bne : b i≠0 := fun e => hi (by simp [θ,e])
    have ti : reverseCubic A b i=0 := by
      by_contra tne
      exact hi (by simp [θ,mDirty i tne,mul_comm])
    exact ⟨bne,ti,order15_nonC2_tau_clean_radau ha ho hq i bne ti⟩
  have hQ : Q=0 := by
    by_contra hn
    have aQ := trace.missing_radau_port ho (by decide) (dQ.trans (by decide)) ha'
      (fun i hi => ⟨(support i hi).2.2,(missing i (support i hi).1 (support i hi).2.1).1⟩)
    have dQ' := trace.missing_radau_port ho (by decide) (dQ.trans (by decide)) hd'
      (fun i hi => ⟨(support i hi).2.2,(missing i (support i hi).1 (support i hi).2.1).2.1⟩)
    have eQ := trace.missing_radau_port ho (by decide) (dQ.trans (by decide)) he'
      (fun i hi => ⟨(support i hi).2.2,(missing i (support i hi).1 (support i hi).2.1).2.2⟩)
    obtain ⟨i,hi,pref⟩ := exists_last_coordinate (trace.clock_witness ho hn dQ (by decide))
    have hiθ : θ i≠0 := fun e => hi (by simp [e])
    have ui : mirror A i≠0 := fun e => hi (by simp [e])
    obtain ⟨bi,ti,pi⟩ := support i hiθ
    obtain ⟨nA,nD,nE⟩ := missing i bi ti
    have clean (w : Vec K 20) (hw : w∈markedTerminalZero (s:=19) A 15 7) : w i=0 := by
      rw [←h.marked_terminal_zero ha ho 7 (by decide) (by decide),
        order15_nonC2_reverse_orbit ha ho h 7 (by decide) (by decide)] at hw
      obtain ⟨r,hr,R,_,eR⟩ := Clock.exists_head_poly hw
      have r0 : r=0 := by simpa using hr
      simpa only [r0,Pi.zero_apply,ti,mul_zero,add_zero] using eR i
    obtain ⟨_,mom1,mom2⟩ := (trace.clock (by decide : 4+2≤15)).two_primitive_last_pivot
      ha ho h.terminal (H:=7) (by decide) (by decide) hi pref bi clean
    have na' : a≠mirror A i := nA.symm
    have nd' : d≠mirror A i := nD.symm
    have ne' : e≠mirror A i := nE.symm
    have hDistinct : Function.Injective (![mirror A i,a,d,e] : Fin 4→K) := by
      intro x y h
      fin_cases x <;> fin_cases y <;> simp_all
    have hPorts : ∀ j : Fin 4, IsLeftRadauPort ((![mirror A i,a,d,e] : Fin 4→K) j) := by
      intro j
      fin_cases j
      · exact pi
      · exact ha'
      · exact hd'
      · exact he'
    exact hn (left_three_affine_cut _ _ _ _ ui hDistinct hPorts Q dQ aQ dQ' eQ mom1 mom2)
  intro i hh
  by_cases ti : reverseCubic A b i=0
  · exact mClean i (hh.resolve_right (not_not_intro ti)) ti
  · simpa only [hQ,eval_zero] using mDirty i ti

end
end RKCert.Paired
