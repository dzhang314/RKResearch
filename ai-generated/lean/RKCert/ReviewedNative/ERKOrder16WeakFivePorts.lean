module
public import RKCert.ReviewedNative.ERKOrder16ReverseCover
public import RKCert.ReviewedNative.ReversePhysicalPorts
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! # Additional true interior ports in the order-sixteen weak-five chart
The forward row is the second genuinely nonzero clock, and the reverse
row is the penultimate contrast row in the original forward index order.
The weak-five native chart is a hypothesis, not inferred from order alone. -/
namespace RKResearch.Certified.ERK16

open RKResearch Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24→K}
variable {q Q P : K[X]} {θ : Fin 24→K}

abbrev weakFiveRows (A : Matrix (Fin 24) (Fin 24) K) (b : Fin 24→K) (Q P : K[X]) :
    Finset (Fin 24) := Finset.univ.filter (fun i=>reverseContrast A b Q P i≠0)

@[simp] theorem mem_weakFiveRows (i : Fin 24) :
    i∈weakFiveRows A b Q P ↔ reverseContrast A b Q P i≠0 := by
  simp [weakFiveRows]

/-- Exact native inputs used at the simple-five boundary. The paid
mask is a degree-four clock polynomial minus an actual grade-four
defect (not a collapsed or reindexed tableau). -/
structure WeakFivePaidMask (A : Matrix (Fin 24) (Fin 24) K) (b : Fin 24→K)
    (q Q P : K[X]) (θ : Fin 24→K) : Prop where
  forwardDegree : q.natDegree≤4
  reverseDegree : Q.natDegree≤4
  otherDegree : P.natDegree≤3
  reflected : ∀ x,q.eval x=Q.eval (1-x)
  maskSource : ∃ x∈zeroSpace A 4, θ=evalNodes A q-x
  maskOutside : ∀ i,i∉weakFiveRows A b Q P→i≠Fin.last 23→θ i=0
  defectZero : ∀ x∈zeroSpace A 7,∀ i∈weakFiveRows A b Q P,x i=0
  traces : ∃ f : Fin 24→K,
    (∀ i,quadraticSeed A b i*f i=Q.eval (reflectedClock A i)*quadraticSeed A b i) ∧
    (∀ i,reflectedClock A i*b i*f i=P.eval (reflectedClock A i)*quadraticSeed A b i)
  clockSimple : Set.InjOn (nodes A) (weakFiveRows A b Q P : Set (Fin 24))
  count : (weakFiveRows A b Q P).card=5
  origin : (0:Fin 24)∈weakFiveRows A b Q P

theorem WeakFivePaidMask.active (W : WeakFivePaidMask A b q Q P θ) {i : Fin 24}
    (h : i∈weakFiveRows A b Q P) :
    quadraticSeed A b i=0 ∧ reflectedClock A i≠0 ∧ b i≠0 ∧ Q.eval (reflectedClock A i)≠0 := by
  obtain ⟨f,hq,hp⟩ := W.traces
  obtain ⟨d,y,bi,v,_⟩ := reverse_contrast_true_support hq hp i ((mem_weakFiveRows i).mp h)
  exact ⟨d,y,bi,v⟩

theorem WeakFivePaidMask.forward_primitive [CharZero K] (ho : HasOrder 16 A b)
    (W : WeakFivePaidMask A b q Q P θ) (R : K[X]) (rd : R.natDegree≤2)
    {i : Fin 24} (hi : i∈weakFiveRows A b Q P) :
    mat A (weightedEval (nodes A) θ R) i=(primitive (R*q)).eval (nodes A i) := by
  obtain ⟨x,hx,rep⟩ := W.maskSource
  have ev : weightedEval (nodes A) θ R=evalNodes A (R*q)-weightedEval (nodes A) x R := by
    rw [rep]
    funext j
    simp only [weightedEval_apply,evalNodes_apply,Pi.sub_apply,eval_mul]
    ring
  have gd : (R*q).natDegree≤6 := natDegree_mul_le.trans (by have := W.forwardDegree;omega)
  have h1 := W.defectZero _ (primitive_defect A (R*q) gd) i hi
  have px : weightedEval (nodes A) x R∈zeroSpace A 6 := by
    have eq : weightedEval (nodes A) x R=x*evalNodes A R := by ext j;simp [mul_comm]
    rw [eq]
    exact zeroSpace_mul_treeSpace ho (n:=2) (by decide) hx (evalNodes_mem_treeSpace A R rd)
  have h2 := W.defectZero _ (mat_zeroSpace_charZero A 6 px) i hi
  change mat A (evalNodes A (R*q)) i-(primitive (R*q)).eval (nodes A i)=0 at h1
  rw [ev,map_sub,Pi.sub_apply,h2,sub_zero,sub_eq_zero.mp h1]

theorem WeakFivePaidMask.forward_prefix [CharZero K]
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b)
    (W : WeakFivePaidMask A b q Q P θ) (R : K[X]) (rd : R.natDegree≤2)
    {i : Fin 24} (hi : i∈weakFiveRows A b Q P)
    (pre : ∀ k < i,k∈weakFiveRows A b Q P→R.eval (nodes A k)=0) :
    (primitive (R*q)).eval (nodes A i)=0 := by
  have lin : mat A (weightedEval (nodes A) θ R) i=0 := by
    apply causal_mat ha
    intro k hk
    by_cases h : k∈weakFiveRows A b Q P
    · simp only [weightedEval_apply,pre k hk h,zero_mul]
    · have ne : k≠Fin.last 23 := fun eq=>not_lt_of_ge (Fin.le_last i) (eq ▸ hk)
      simp only [weightedEval_apply,W.maskOutside k h ne,mul_zero]
  exact (W.forward_primitive ho R rd hi).symm.trans lin

theorem WeakFivePaidMask.reverse_suffix [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b)
    (W : WeakFivePaidMask A b q Q P θ) (F : Width24PaidFrame A b)
    (cover : SupportsComplement A b 8 (Fin.last 23))
    (R : K[X]) (rd : R.natDegree≤1)
    {i : Fin 24} (hi : i∈weakFiveRows A b Q P)
    (post : ∀ k,i<k→k∈weakFiveRows A b Q P→R.eval (reflectedClock A k)=0) :
    (primitive (R*(X*Q))).eval (reflectedClock A i)=0 := by
  let t := Fin.last 23
  have y0 : reflectedClock A t=0 := by change 1-nodes A t=0;rw [F.lastClock,sub_self]
  have col (j : Fin 24) : A j t=0 := ha j t (Fin.le_last j)
  obtain ⟨off,_,bi,_⟩ := W.active hi
  have pay := true_port_eval ho y0 col cover Q P R
    (by have := W.reverseDegree;omega) (by have := W.otherDegree;omega) off
  have z : mat A.transpose (weightedEval (reflectedClock A) (reverseContrast A b Q P) R) i=0 := by
    apply causal_transpose ha
    intro j hj
    have ord := Fin.rev_lt_rev.mp hj
    by_cases h : j∈weakFiveRows A b Q P
    · simp only [weightedEval_apply,post j ord h,zero_mul]
    · have v : reverseContrast A b Q P j=0 := by
        rwa [mem_weakFiveRows,not_ne_iff] at h
      simp only [weightedEval_apply,v,mul_zero]
  rw [z] at pay
  exact (mul_eq_zero.mp pay.symm).resolve_right bi

/-- The middle two clocks are labelled by the original row chronology,
and are the distinct roots of the monic quadratic left after removing
the origin and two extreme nonzero contrast clocks. -/
structure WeakFiveInnerPorts (A : Matrix (Fin 24) (Fin 24) K) (b : Fin 24→K)
    (q Q P Z : K[X]) (ι : Fin 5→Fin 24) : Prop where
  increasing : StrictMono ι
  origin : ι 0=0
  rows : ∀ j,j∈weakFiveRows A b Q P ↔ ∃ k,ι k=j
  different : nodes A (ι 2)≠nodes A (ι 3)
  middleRoots : ∀ x,Z.eval x=0↔x=nodes A (ι 2)∨x=nodes A (ι 3)
  degree : Z.natDegree=2
  monic : Z.Monic
  supportFactor : nodalHull ((weakFiveRows A b Q P).image (nodes A))=
    X*(X-C (nodes A (ι 1)))*(X-C (nodes A (ι 4)))*Z
  forwardInner :
    (primitive ((X*(X-C (nodes A (ι 1))))*q)).eval (nodes A (ι 2))=0
  reverseInner :
    (primitive ((X-C (reflectedClock A (ι 4)))*(X*Q))).eval (reflectedClock A (ι 3))=0

/-- Both extra payments are on the same five original stage rows as the
quadratic support factor. The degree bounds are exactly two forward
and one reverse; no higher shifted primitive is assumed. -/
theorem weak_five_true_inner_ports [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b)
    (W : WeakFivePaidMask A b q Q P θ)
    (cover : SupportsComplement A b 8 (Fin.last 23)) :
    ∃ (ι : Fin 5→Fin 24) (Z : K[X]),WeakFiveInnerPorts A b q Q P Z ι := by
  let : DecidableEq K := fun a b => Classical.propDecidable (a = b)
  let S := weakFiveRows A b Q P
  let E := S.orderEmbOfFin W.count
  let ι : Fin 5→Fin 24 := E
  let c := nodes A
  have mem (k : Fin 5) : ι k∈S := S.orderEmbOfFin_mem W.count k
  have range (i : Fin 24) : i∈S ↔ ∃ k,ι k=i := by
    have eq := S.range_orderEmbOfFin W.count
    change i∈(S:Set (Fin 24)) ↔ i∈Set.range E
    rw [eq]
  have first : ι 0=0 := by
    obtain ⟨j,j0⟩ := (range (0:Fin 24)).mp W.origin
    exact le_antisymm (j0 ▸ E.monotone (Fin.zero_le j)) (Fin.zero_le _)
  have c0 : c (ι 0)=0 := by
    rw [first]
    change (∑ j,A 0 j*1)=0
    exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le _),zero_mul]
  have inj : Function.Injective (fun k : Fin 5=>c (ι k)) :=
    fun i j eq=>E.injective (W.clockSimple (mem i) (mem j) eq)
  have ns (i j : Fin 5) (ne : i≠j) : c (ι i)≠c (ι j) := fun h=>ne (inj h)
  have pre : ∀ k,k<ι 2→k∈S→(X*(X-C (c (ι 1))):K[X]).eval (c k)=0 := by
    intro k hk h
    obtain ⟨j,rfl⟩ := (range k).mp h
    have hj := E.lt_iff_lt.mp hk
    change j.val<2 at hj
    rcases (show j.val=0∨j.val=1 by omega) with hz|ho'
    · have j0 : j=(0:Fin 5) := Fin.ext hz
      simp only [j0,eval_mul,eval_X,c0,zero_mul]
    · have j1 : j=(1:Fin 5) := Fin.ext ho'
      simp only [j1,eval_mul,eval_X,eval_sub,eval_C,sub_self,mul_zero]
  have post : ∀ k,ι 3<k→k∈S→
      (X-C (reflectedClock A (ι 4)):K[X]).eval (reflectedClock A k)=0 := by
    intro k hk h
    obtain ⟨j,rfl⟩ := (range k).mp h
    have hj := E.lt_iff_lt.mp hk
    change 3<j.val at hj
    have j4 : j=(4:Fin 5) := Fin.ext (by have := j.isLt;omega)
    simp only [j4,eval_sub,eval_X,eval_C,sub_self]
  have fw := W.forward_prefix ha ho (X*(X-C (c (ι 1)))) (by
      rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero _),natDegree_X,natDegree_X_sub_C])
    (mem 2) pre
  have bw := W.reverse_suffix ha ho (width24_paid_frame ha ho) cover
    (X-C (reflectedClock A (ι 4))) (by rw [natDegree_X_sub_C]) (mem 3) post
  let Z := (X-C (c (ι 2)))*(X-C (c (ι 3)))
  have zd : Z.natDegree=2 := by
    dsimp [Z]
    rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),natDegree_X_sub_C,natDegree_X_sub_C]
  have zmon : Z.Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have roots (x : K) : Z.eval x=0↔x=c (ι 2)∨x=c (ι 3) := by
    simp [Z,mul_eq_zero,sub_eq_zero]
  have image : S.image c={0,c (ι 1),c (ι 4),c (ι 2),c (ι 3)} := by
    ext x
    constructor
    · intro hx
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨k,rfl⟩ := (range j).mp hj
      fin_cases k <;> simp [c0]
    · intro hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl
      · exact Finset.mem_image.mpr ⟨ι 0,mem 0,c0⟩
      · exact Finset.mem_image_of_mem c (mem 1)
      · exact Finset.mem_image_of_mem c (mem 4)
      · exact Finset.mem_image_of_mem c (mem 2)
      · exact Finset.mem_image_of_mem c (mem 3)
  have z0 (k : Fin 5) (kn : k≠0) : c (ι k)≠0 := by
    rw [←c0]
    exact ns k 0 kn
  have factor : nodalHull (S.image c)=X*(X-C (c (ι 1)))*(X-C (c (ι 4)))*Z := by
    have d0 : (0:K) ∉ ({c (ι 1),c (ι 4),c (ι 2),c (ι 3)}:Finset K) := by
      simp [(z0 1 (by decide)).symm,(z0 4 (by decide)).symm,
        (z0 2 (by decide)).symm,(z0 3 (by decide)).symm]
    have d1 : c (ι 1) ∉ ({c (ι 4),c (ι 2),c (ι 3)}:Finset K) := by
      simp [ns (1:Fin 5) 4 (by decide),ns (1:Fin 5) 2 (by decide),ns (1:Fin 5) 3 (by decide)]
    have d4 : c (ι 4) ∉ ({c (ι 2),c (ι 3)}:Finset K) := by
      simp [ns (4:Fin 5) 2 (by decide),ns (4:Fin 5) 3 (by decide)]
    have d2 : c (ι 2) ∉ ({c (ι 3)}:Finset K) := by simp [ns (2:Fin 5) 3 (by decide)]
    rw [image,nodalHull,Finset.prod_insert d0,Finset.prod_insert d1,Finset.prod_insert d4,
      Finset.prod_insert d2,Finset.prod_singleton,map_zero,sub_zero]
    dsimp [Z]
    ring
  exact ⟨ι,Z,⟨E.strictMono,first,range,ns _ _ (by decide),roots,zd,zmon,factor,fw,bw⟩⟩

/-- At width 24 the true reverse cover follows from native reviewed
order. Only the exact weak-five mask chart remains an input. -/
theorem width24_weak_five_true_inner_ports [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b)
    (W : WeakFivePaidMask A b q Q P θ) :
    ∃ (ι : Fin 5→Fin 24) (Z : K[X]),WeakFiveInnerPorts A b q Q P Z ι :=
  weak_five_true_inner_ports ha ho W (width24_quadratic_cover ha ho).supports

end
end RKResearch.Certified.ERK16
