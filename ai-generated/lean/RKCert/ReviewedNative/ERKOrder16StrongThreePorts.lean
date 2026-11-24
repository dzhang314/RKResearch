module

public import RKCert.ReviewedNative.ERKOrder16StrongCover
public import RKCert.ReviewedNative.NativeHiddenCarrier
public import RKCert.ReviewedNative.ReversePhysicalPorts
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! # Paid chronology on all three original full-seventh contrast rows

The mask is a reflected polynomial minus an actual grade-five defect
and an invariant grade-seven correction. Forward chronology pays 3+2+1;
the exact terminal-deleted E7 cover pays 2+1 in reverse order. If the
original first row were absent, its zero clock would supply a factor X
and the first two forward windows would exclude the remaining quartic. -/
namespace RKResearch.Certified.ERK16

open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open scoped Classical Matrix

noncomputable section
variable {K : Type*} [Field K] {A : Matrix (Fin 24) (Fin 24) K} {b w g : Fin 24 → K}
variable {Q P : K[X]}

abbrev strongThreeRows (A : Matrix (Fin 24) (Fin 24) K) (b : Fin 24 → K) (Q P : K[X]) :=
  Hidden.activeRows (reverseContrast A b Q P)

abbrev strongThreeMask (A : Matrix (Fin 24) (Fin 24) K) (Q : K[X]) (w g : Fin 24 → K) :=
  evalNodes A (Q.comp (1-X))-(w+g)

/-- The exact remaining forward data. No paid primitive is assumed.
Only the true three-row census, support and grade of the source of
the mask are premises. -/
structure StrongThreeActualMask (A : Matrix (Fin 24) (Fin 24) K)
    (b w g : Fin 24 → K) (Q P : K[X]) : Prop where
  headGrade : w∈zeroSpace A 5
  correction : ∃ U : Submodule K (Fin 24 → K),
    U≤zeroSpace A 7 ∧ U.map (diag (nodes A))≤U ∧ g∈U
  qDegree : Q.natDegree≤5
  pDegree : P.natDegree≤4
  qFit : ∀ i, quadraticSeed A b i*w i=Q.eval (reflectedClock A i)*quadraticSeed A b i
  pFit : ∀ i, reflectedClock A i*b i*w i=P.eval (reflectedClock A i)*quadraticSeed A b i
  outside : ∀ i,i∉strongThreeRows A b Q P→i≠Fin.last 23→strongThreeMask A Q w g i=0
  defectZero : ∀ x∈zeroSpace A 8,∀ i∈strongThreeRows A b Q P,x i=0
  count : (strongThreeRows A b Q P).card=3
  simple : Set.InjOn (nodes A) (strongThreeRows A b Q P : Set (Fin 24))

theorem StrongThreeActualMask.active (M : StrongThreeActualMask A b w g Q P) {i : Fin 24}
    (hi : i∈strongThreeRows A b Q P) :
    quadraticSeed A b i=0 ∧ reflectedClock A i≠0 ∧ b i≠0 ∧
      Q.eval (reflectedClock A i)≠0 :=
  let h := reverse_contrast_true_support M.qFit M.pFit i ((Hidden.mem_activeRows i).mp hi)
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

private theorem strong_reflect_degree (d : Q.natDegree≤5) : (Q.comp (1-X)).natDegree≤5 := by
  exact natDegree_comp_le.trans (by rw [Thin.one_sub_X_natDegree,mul_one]; exact d)

theorem StrongThreeActualMask.forward [CharZero K]
    (ho : HasOrder 16 A b) (M : StrongThreeActualMask A b w g Q P)
    (R : K[X]) (rd : R.natDegree≤2) {i : Fin 24} (hi : i∈strongThreeRows A b Q P) :
    mat A (weightedEval (nodes A) (strongThreeMask A Q w g) R) i =
      (primitive (R*(Q.comp (1-X)))).eval (nodes A i) := by
  let q := Q.comp (1-X)
  let c := nodes A
  have eq : weightedEval c (strongThreeMask A Q w g) R =
      evalNodes A (R*q)-(weightedEval c w R+weightedEval c g R) := by
    ext j
    simp only [strongThreeMask,weightedEval_apply,evalNodes_apply,Pi.sub_apply,Pi.add_apply,eval_mul,q,c]
    ring
  have d : (R*q).natDegree≤7 := natDegree_mul_le_of_le rd (strong_reflect_degree M.qDegree)
  have prim := M.defectZero _ (primitive_defect A (R*q) d) i hi
  change mat A (evalNodes A (R*q)) i-(primitive (R*q)).eval (c i)=0 at prim
  have hw : weightedEval c w R∈zeroSpace A 7 := by
    have h : weightedEval c w R=w*evalNodes A R := by ext j;simp [c,mul_comm]
    rw [h]
    exact zeroSpace_mul_treeSpace ho (n:=2) (by decide) M.headGrade (evalNodes_mem_treeSpace A R rd)
  obtain ⟨U,sub,inv,hg⟩ := M.correction
  have hg7 : weightedEval c g R∈zeroSpace A 7 := by
    have he : weightedEval c g R=(fun j=>R.eval (c j)*g j) := by ext j;rw [weightedEval_apply]
    rw [he]
    exact sub (clock_function_mem (c:=c) (fun _ h=>inv (Submodule.mem_map_of_mem h)) (fun a=>R.eval a) hg)
  have move := M.defectZero _ (mat_zeroSpace_charZero A 7 ((zeroSpace A 7).add_mem hw hg7)) i hi
  change mat A (weightedEval c (strongThreeMask A Q w g) R) i=_
  rw [eq,map_sub,Pi.sub_apply,move,sub_zero,sub_eq_zero.mp prim]

theorem StrongThreeActualMask.forward_prefix [CharZero K]
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b) (M : StrongThreeActualMask A b w g Q P)
    (R : K[X]) (rd : R.natDegree≤2) {i : Fin 24} (hi : i∈strongThreeRows A b Q P)
    (pre : ∀ j < i, j∈strongThreeRows A b Q P→R.eval (nodes A j)=0) :
    (primitive (R*(Q.comp (1-X)))).eval (nodes A i)=0 := by
  have z : mat A (weightedEval (nodes A) (strongThreeMask A Q w g) R) i=0 := by
    apply causal_mat ha
    intro j hj
    by_cases h:j∈strongThreeRows A b Q P
    · simp only [weightedEval_apply,pre j hj h,zero_mul]
    · have nt:j≠Fin.last 23 := fun e=>not_lt_of_ge (Fin.le_last i) (e ▸ hj)
      simp only [weightedEval_apply,M.outside j h nt,mul_zero]
  exact (M.forward ho R rd hi).symm.trans z

structure StrongThreePhysicalPorts (A : Matrix (Fin 24) (Fin 24) K) (b : Fin 24 → K)
    (Q P : K[X]) (ι : Fin 3 → Fin 24) : Prop where
  increasing : StrictMono ι
  rows : ∀ i,i∈strongThreeRows A b Q P ↔ ∃ k,ι k=i
  simple : Function.Injective (fun k=>nodes A (ι k))
  forwardFirst : ∀ R : K[X], R.natDegree≤2 →
    (primitive (R*(Q.comp (1-X)))).eval (nodes A (ι 0))=0
  forwardSecond : ∀ R : K[X], R.natDegree≤1 →
    (primitive ((R*(X-C (nodes A (ι 0))))*(Q.comp (1-X)))).eval (nodes A (ι 1))=0
  forwardThird :
    (primitive (((X-C (nodes A (ι 0)))*(X-C (nodes A (ι 1))))*(Q.comp (1-X)))).eval
      (nodes A (ι 2))=0
  reverseLast : ∀ R : K[X], R.natDegree≤1 →
    (primitive (R*(X*Q))).eval (reflectedClock A (ι 2))=0
  reverseMiddle :
    (primitive ((X-C (reflectedClock A (ι 2)))*(X*Q))).eval (reflectedClock A (ι 1))=0

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- The exact degree budgets on the two orientations, on the very same
three original physical row indices. The backward budget is m=7,
not the weak-four or weak-five m=8 cut. -/
theorem strong_three_physical_ports
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b)
    (C0 : Width24StrongCover A b) (M : StrongThreeActualMask A b w g Q P) :
    ∃ ι : Fin 3 → Fin 24, StrongThreePhysicalPorts A b Q P ι := by
  let S := strongThreeRows A b Q P
  let E := S.orderEmbOfFin M.count
  let c := nodes A
  let y := reflectedClock A
  have mem (k : Fin 3) : E k∈S := S.orderEmbOfFin_mem M.count k
  have range (i : Fin 24) : i∈S ↔ ∃ k,E k=i := by
    change i∈(S : Set (Fin 24)) ↔ i∈Set.range E
    rw [S.range_orderEmbOfFin M.count]
  have inj : Function.Injective (fun k : Fin 3=>c (E k)) :=
    fun i j eq=>E.injective (M.simple (mem i) (mem j) eq)
  have fwd (k : Fin 3) (R : K[X]) (rd : R.natDegree≤2)
      (pre : ∀ j<k,R.eval (c (E j))=0) :
      (primitive (R*(Q.comp (1-X)))).eval (c (E k))=0 :=
    M.forward_prefix ha ho R rd (mem k) (fun j hj hm=>by
      obtain ⟨l,rfl⟩ := (range j).mp hm
      exact pre l (E.lt_iff_lt.mp hj))
  have back (k : Fin 3) (R : K[X]) (rd : R.natDegree≤1)
      (post : ∀ j,k<j→R.eval (y (E j))=0) :
      (primitive (R*(X*Q))).eval (y (E k))=0 := by
    have y0 : y (Fin.last 23)=0 := by
      change 1-nodes A (Fin.last 23)=0
      rw [C0.quadratic.frame.lastClock,sub_self]
    have nzcol (j : Fin 24) : A j (Fin.last 23)=0 := ha j _ (Fin.le_last j)
    have test := true_port_eval ho y0 nzcol C0.supports Q P R
      (by have := M.qDegree; omega) (by have := M.pDegree; omega) (M.active (mem k)).1
    have z : mat A.transpose (weightedEval y (reverseContrast A b Q P) R) (E k)=0 := by
      apply causal_transpose ha
      intro j hj
      by_cases h : reverseContrast A b Q P j=0
      · simp only [weightedEval_apply,h,mul_zero]
      · obtain ⟨l,rfl⟩ := (range j).mp ((Hidden.mem_activeRows j).mpr h)
        have lt : k<l := E.lt_iff_lt.mp (Fin.rev_lt_rev.mp hj)
        simp only [weightedEval_apply,post l lt,zero_mul]
    change mat A.transpose (weightedEval y (reverseContrast A b Q P) R) (E k)=_ at test
    rw [z] at test
    exact (mul_eq_zero.mp test.symm).resolve_right (M.active (mem k)).2.2.1
  refine ⟨E,⟨E.strictMono,range,inj,?_,?_,?_,?_,?_⟩⟩
  · exact fun R rd=>fwd 0 R rd (fun j hj=>(not_lt_of_ge (Fin.zero_le j) hj).elim)
  · intro R rd
    apply fwd 1 (R*(X-C (c (E 0)))) (natDegree_mul_le_of_le rd (natDegree_X_sub_C (c (E 0))).le)
    intro j hj
    have h : j=0 := Fin.ext (by change j.val<1 at hj; omega)
    simp [h]
  · apply fwd 2 ((X-C (c (E 0)))*(X-C (c (E 1))))
      (natDegree_mul_le_of_le (natDegree_X_sub_C (c (E 0))).le (natDegree_X_sub_C (c (E 1))).le)
    intro j hj
    change j.val<2 at hj
    rcases (show j.val=0∨j.val=1 by omega) with h|h
    · have e : j=0 := Fin.ext h
      simp [e]
    · have e : j=1 := Fin.ext h
      simp [e]
  · exact fun R rd=>back 2 R rd (fun j hj=>(not_lt_of_ge (Fin.le_last j) hj).elim)
  · apply back 1 (X-C (y (E 2))) (by rw [natDegree_X_sub_C])
    intro j hj
    have e : j=2 := Fin.ext (by change 1<j.val at hj; have := j.isLt; omega)
    simp [e]

/-- The free non-origin case of the strong mask is excluded without
its norm. Nonzeroness of each of the two forward clocks uses the true
fitted contrast, and their difference uses physical clock simplicity. -/
theorem strong_three_origin_of_ports
    (ha : ∀ i j,i≤j → A i j=0) (M : StrongThreeActualMask A b w g Q P)
    {ι : Fin 3 → Fin 24} (B : StrongThreePhysicalPorts A b Q P ι) :
    ι 0=0 := by
  have c0 : nodes A (0:Fin 24)=0 := by
    change (∑ j,A 0 j*(1:K))=0
    exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le j),zero_mul]
  let q := Q.comp (1-X)
  have live (k : Fin 3) : q.eval (nodes A (ι k))≠0 := by
    have hi := (B.rows (ι k)).mpr ⟨k,rfl⟩
    simpa only [q,eval_comp,eval_sub,eval_one,eval_X,reflectedClock,Pi.sub_apply,Pi.one_apply]
      using (M.active hi).2.2.2
  suffices h0 : (0:Fin 24)∈strongThreeRows A b Q P by
    obtain ⟨k,hk⟩ := (B.rows 0).mp h0
    exact le_antisymm (hk ▸ B.increasing.monotone (Fin.zero_le k)) (Fin.zero_le _)
  by_contra absent
  have hw0 : w 0=0 := origin_zeroSpace ha 5 M.headGrade
  obtain ⟨U,inc,_,hg⟩ := M.correction
  have hg0 : g 0=0 := origin_zeroSpace ha 7 (inc hg)
  have q0 : q.eval 0=0 := by
    have z := M.outside 0 absent (by decide)
    change q.eval (nodes A 0)-(w 0+g 0)=0 at z
    rwa [c0,hw0,hg0,add_zero,sub_zero] at z
  obtain ⟨L,eq⟩ : (X:K[X])∣q := by rwa [X_dvd_iff,coeff_zero_eq_eval_zero]
  have qn : q≠0 := fun h=>live 0 (by rw [h,eval_zero])
  have ln : L≠0 := fun h=>qn (by rw [eq,h,mul_zero])
  have ld : L.natDegree≤4 := by
    have d : q.natDegree≤5 := strong_reflect_degree M.qDegree
    rw [eq,natDegree_X_mul ln] at d
    omega
  have nn (k : Fin 3) : nodes A (ι k)≠0 := fun h=>live k (by rw [h,q0])
  have apart : nodes A (ι 1)≠nodes A (ι 0) :=
    fun e=>(by decide : (1:Fin 3)≠0) (B.simple e)
  apply ln (RKCert.EndpointPhysical.ordered_quartic_eq_zero_of_primitives ld (nn 0) (nn 1) apart
    ⟨?_,?_⟩)
  · intro R rd
    rw [formalPrimitive_eq_native,←eq]
    exact B.forwardFirst R rd
  · intro R rd
    rw [formalPrimitive_eq_native,show R*(X*(X-C (nodes A (ι 0)))*L)=
        (R*(X-C (nodes A (ι 0))))*q by rw [eq];ring]
    exact B.forwardSecond R rd

theorem width24_strong_three_ports_and_origin
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b)
    (f7 : finrank K (zeroSpace A 7)=8) (M : StrongThreeActualMask A b w g Q P) :
    ∃ ι : Fin 3 → Fin 24, StrongThreePhysicalPorts A b Q P ι ∧ ι 0=0 := by
  obtain ⟨ι,B⟩ := strong_three_physical_ports ha ho (width24_strong_reverse_cover ha ho f7) M
  exact ⟨ι,B,strong_three_origin_of_ports ha M B⟩

end
end RKResearch.Certified.ERK16
