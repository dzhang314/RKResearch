module

public import RKCert.ReviewedNative.DIRKC2OuterRefund

@[expose] public section

/-! # True prefix compatibility with a single cubic core clock
One scalar kills the entire cubic core, including repetitions of the
same core clock. Outside equal-clock collisions still have to match
simultaneously on every physical prefix row. -/
namespace RKResearch.Certified.Graded.OuterHead

open Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix

variable {K : Type*} [Field K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}
variable {U : Submodule K (Fin s → K)} {w : Fin s → K}

/-- A single fixed subspace of input and output head-polynomial multipliers. -/
def CoreMask.compatible (C : CoreMask A U) (w : Fin s → K) (i : Fin s) : Submodule K (K[X]) where
  carrier := {P | ∃ F : K → K, F 0=0 ∧ ∃ a : K, ∀ j < i,
    weightedEval (nodes A) w P j=F (nodes A j)+a*C.mask j}
  zero_mem' := ⟨0,rfl,0,by simp⟩
  add_mem' := by
    rintro P Q ⟨F,hF,a,eqF⟩ ⟨G,hG,b,eqG⟩
    refine ⟨F+G,by simp [hF,hG],a+b,fun j hj => ?_⟩
    rw [map_add,Pi.add_apply,eqF j hj,eqG j hj,Pi.add_apply]
    ring
  smul_mem' := by
    rintro r P ⟨F,hF,a,eqF⟩
    refine ⟨fun x=>r*F x,by change r*F 0=0; rw [hF,mul_zero],r*a,fun j hj => ?_⟩
    rw [map_smul,Pi.smul_apply,smul_eq_mul,eqF j hj]
    ring

theorem weighted_mem_chain {c : Fin s → K} {n : ℕ} {Q : K[X]}
    (deg : Q.degree < (n : WithBot ℕ)) :
    weightedEval c w Q∈chain (diag c) U w n := by
  by_cases z : Q=0
  · simp [z]
  have h := (natDegree_lt_iff_degree_lt z).mpr deg
  have hs := ((clock_chain_le_iff (T:=diag c) (U:=U) (w:=w) n).mp le_rfl).2
  let V := chain (diag c) U w n
  have eq (j : ℕ) (a : K) : weightedEval c w (monomial j a)=a • (diag c^j) w := by
    ext i
    simp [mul_assoc]
  rw [Q.as_sum_range' n h,map_sum]
  exact V.sum_mem fun j hj => (eq j (Q.coeff j)).symm ▸ V.smul_mem _ (hs j (Finset.mem_range.mp hj))

/-- A single genuine cubic coefficient corrects the head on the entire
prefix once the outside scalar readings agree at the preceding clocks. -/
theorem ExteriorStep.fit_full_prefix {C : CoreMask A U} {m : ℕ} (D : ExteriorStep C m)
    {P Q : K[X]} (P0 : P.eval 0=0) (Qok : Q∈C.compatible w D.next)
    (observed : ∀ j, P.eval (nodes A (D.old j))=weightedEval (nodes A) w Q (D.old j)) :
    ∃ a : K, ∀ i < D.next, evalNodes A P i-weightedEval (nodes A) w Q i-a*C.mask i=0 := by
  obtain ⟨F,F0,r,eq⟩ := Qok
  have hx (j : Fin m) : P.eval (nodes A (D.old j))=F (nodes A (D.old j)) := by
    rw [observed j,eq _ (D.earlier j),D.old_out j,mul_zero,add_zero]
  refine ⟨P.eval C.clock-F C.clock-r,fun i hi => ?_⟩
  rw [evalNodes_apply,eq i hi]
  by_cases mask : C.mask i=0
  · have same : P.eval (nodes A i)=F (nodes A i) := by
      by_cases a : nodes A i=0
      · rw [a,P0,F0]
      · obtain ⟨l,le⟩ := D.cover i hi mask a
        rw [le,hx]
    simp [mask,same]
  · rw [C.clock_on_mask i mask,(C.binary i).resolve_left mask]
    ring

variable [CharZero K]

/-- At a refunded chronological cut, the output meets the same prefix
compatibility as the input. On every exterior row through the cut, its
head value is the true primitive of the original scalar. -/
theorem ExteriorStep.primitive_output {C : CoreMask A U} {m j n : ℕ}
    (D : ExteriorStep C m) (ha : A.IsLowerTriangular)
    (flag : zeroSpace A (j+1)≤chain (diag (nodes A)) U w n)
    {P : K[X]} {v : Fin s → K}
    (Pd : P.natDegree≤j) (pure : v-evalNodes A P∈zeroSpace A j)
    (pre : ∀ i < D.next, v i=0) (diag0 : A D.next D.next=0) :
    ∃ Q : K[X], Q.degree < (n : WithBot ℕ) ∧ Q∈C.compatible w D.next ∧
      ∀ i ≤ D.next, C.mask i=0 → (primitive P).eval (nodes A i)=weightedEval (nodes A) w Q i := by
  obtain ⟨u,hu,Q,d,eq⟩ := HeadFiber.exists_poly (flag (primitive_residual_native Pd pure))
  rw [C.span_eq] at hu
  obtain ⟨a,eu⟩ := Submodule.mem_span_singleton.mp hu
  have h (i : Fin s) (hi : i≤D.next) :
      (primitive P).eval (nodes A i)=a*C.mask i+weightedEval (nodes A) w Q i := by
    have r := congrFun eq i
    rw [Pi.sub_apply,Pi.add_apply,evalNodes_apply,prefix_zero_mulVec_through ha pre diag0 hi,sub_zero,
      ←eu,Pi.smul_apply,smul_eq_mul] at r
    exact r
  refine ⟨Q,d,⟨(primitive P).eval,by change (primitive P).eval 0=0; rw [←coeff_zero_eq_eval_zero,primitive_coeff_zero],-a,?_⟩,?_⟩
  · intro i hi
    change weightedEval (nodes A) w Q i=(primitive P).eval (nodes A i)+(-a)*C.mask i
    rw [h i hi.le]
    ring
  · intro i hi mask
    rw [h i hi,mask,mul_zero,zero_add]

/-- A scalar whose roots mask the earlier exterior clocks gives the
paid primitive observations without imposing a head input. -/
theorem ExteriorStep.masked_primitive {C : CoreMask A U} {m j n : ℕ}
    (D : ExteriorStep C m) (ha : A.IsLowerTriangular)
    (inside : U≤zeroSpace A j) (flag : zeroSpace A (j+1)≤chain (diag (nodes A)) U w n)
    (diag0 : A D.next D.next=0) {P : K[X]}
    (Pd : P.natDegree≤j) (P0 : P.eval 0=0) (roots : ∀ l, P.eval (nodes A (D.old l))=0) :
    ∃ Q : K[X], Q.degree < (n : WithBot ℕ) ∧
      ∀ i ≤ D.next, C.mask i=0 → (primitive P).eval (nodes A i)=weightedEval (nodes A) w Q i := by
  obtain ⟨Q,d,_,vals⟩ := D.primitive_output ha flag Pd (inside (C.scalar_defect P))
    (D.scalar_prefix P0 roots) diag0
  exact ⟨Q,d,vals⟩

end RKResearch.Certified.Graded.OuterHead
