module
public import RKCert.DirkWeightedFourComplete
public import RKCert.DirkWeightedFourData
public import RKCert.DirkJointHidden
@[expose] public section
namespace RKCert.Paired.Terminal
open Module
variable {K:Type*} [Field K] [CharZero K] {s m:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b v:Vec K (s+1)}

/-- At any attainable native even boundary the physical cubic reverse line
is nonlocal. No adjoint method, sign, or nonzero component is assumed. -/
theorem even_reverse_nonlocal (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) :
    ¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1 := by
  intro localc
  obtain ⟨D⟩:=LocalProjection.weighted_four_of_local hm ha ho he localc
  exact D.impossible

theorem even_cubic_hidden (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) (hv:v∈zeroSpace A 3) :
    b*v=0 ∧ tau A b*v=0 :=
  nonlocal_cubic_hidden hm ha ho he (even_reverse_nonlocal hm ha ho he) hv

theorem even_grade_hidden (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m)
    {j:ℕ} (lo:4≤j) (hi:2*j+1≤m) (hv:v∈zeroSpace A j) : b*v=0 ∧ tau A b*v=0 :=
  nonlocal_grade_hidden hm ha ho he (even_reverse_nonlocal hm ha ho he) lo hi hv

/-- Every physical grade-four residual is jointly invisible on both actual
ports of the unrestricted 21-stage order-16 boundary. This is not a
stage-removal claim or a numerical nonexistence conclusion. -/
theorem order16_quartic_hidden {T:Fin 21→Fin 21→K} {β f:Vec K 21}
    (ha:LowerArray T) (ho:HasTreeOrderAtLeast T β 16) (hf:f∈zeroSpace T 4) :
    β*f=0 ∧ tau T β*f=0 :=
  order16_nonlocal_quartic_hidden ha ho (even_reverse_nonlocal (s:=20) (m:=8) (by decide) ha ho (by decide)) hf

/-- A vector killed coordinatewise by the two ports and vanishing at the
origin belongs to the actual preceding defect space (not merely its rank
shadow or its terminal extension). -/
theorem joint_kernel_in_defect (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) (v0:v 0=0)
    (hb:b*v=0) (ht:tau A b*v=0) : v∈zeroSpace A (m-1) := by
  apply hidden_port hm ha ho he v0 (fun i=>congrFun hb i)
  apply mem_annih.mpr
  intro w hw
  obtain ⟨P,_,eqn⟩:=word_polynomial hm ha ho he (even_reverse_nonlocal hm ha ho he) (by omega) (by omega) hw
  rw [row_apply]
  apply Finset.sum_eq_zero
  intro i _
  change v i*w i=0
  have h:tau A b i*v i=0:=congrFun ht i
  rw [eqn,mul_left_comm,mul_comm (v i),h,mul_zero]

theorem exists_hidden_stage (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) :
    ∃ i:Fin (s+1),i≠0 ∧ b i=0 ∧ tau A b i=0 ∧ Pi.single i (1:K)∈zeroSpace A (m-1) := by
  classical
  obtain ⟨first,r3,_⟩:=even_boundary hm ha ho he
  have hn:zeroSpace A 3≠⊥ := by intro e;rw [e,finrank_bot] at r3;omega
  obtain ⟨v,hv,vn⟩:=Submodule.exists_mem_ne_zero_of_ne_bot hn
  obtain ⟨hb,ht⟩:=even_cubic_hidden hm ha ho he hv
  obtain ⟨i,vi⟩:=Function.ne_iff.mp vn
  have vi':v i≠0:=vi
  have bi:b i=0:=(mul_eq_zero.mp (congrFun hb i)).resolve_right vi'
  have ti:tau A b i=0:=(mul_eq_zero.mp (congrFun ht i)).resolve_right vi'
  have iz:i≠0:=by rintro rfl; exact vi' (zeroSpace_first_of_row first 3 hv)
  refine ⟨i,iz,bi,ti,joint_kernel_in_defect hm ha ho he (Pi.single_eq_of_ne iz.symm _) ?_ ?_⟩
  · ext j
    by_cases e:j=i
    · simp [e,bi]
    · simp [Pi.single_eq_of_ne e]
  · ext j
    by_cases e:j=i
    · simp [e,ti]
    · simp [Pi.single_eq_of_ne e]
end RKCert.Paired.Terminal
