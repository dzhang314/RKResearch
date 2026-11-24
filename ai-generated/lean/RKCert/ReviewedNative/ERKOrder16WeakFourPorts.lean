module

public import RKCert.ReviewedNative.ERKOrder16ReverseCover
public import RKCert.ReviewedNative.ReverseChronologicalHull

@[expose] public section

/-! # One real extra primitive payment at the second distinct weak-four clock -/
namespace RKResearch.Certified.ERK16

open RKResearch Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open scoped Classical Matrix

noncomputable section
variable {K : Type*} [Field K]

/-- The ordinary two first-clock tests and the extra degree-one
chronological mask at a second distinct nonzero root of the actual hull. -/
structure WeakFourChronologicalPorts (Q Z : K[X]) (a c : K) : Prop where
  Q_ne : Q≠0
  Q_deg : Q.natDegree≤4
  Z_monic : Z.Monic
  Z_deg : Z.natDegree=4
  firstRoot : Z.eval a=0
  secondRoot : Z.eval c=0
  firstOutside : Q.eval a≠0
  secondOutside : Q.eval c≠0
  firstNonzero : a≠0
  secondNonzero : c≠0
  different : c≠a
  firstConstant : (primitive (X*Q)).eval a=0
  firstLinear : (primitive (X*(X*Q))).eval a=0
  secondMasked : (primitive ((X-Polynomial.C a)*(X*Q))).eval c=0
  weighted : ∀ H : K[X], H.natDegree≤6 → (primitive (H*(X*(Q*Z)))).eval 1=0

/-- Degree at most two is incompatible with the paid X-moments alone.
The remaining weak-four head is genuinely cubic or quartic. -/
theorem WeakFourChronologicalPorts.degree_ge_three [CharZero K]
    {Q Z : K[X]} {a c : K} (B : WeakFourChronologicalPorts Q Z a c) :
    3≤Q.natDegree := by
  by_contra! h
  have d : (Q*Z).natDegree≤6 :=
    (natDegree_mul_le (p:=Q) (q:=Z)).trans (by have := B.Z_deg;omega)
  apply mul_ne_zero B.Q_ne B.Z_monic.ne_zero
  apply NativeMoments.x_moments_detect d
  intro i
  exact B.weighted ((X:K[X])^i.val) (by rw [natDegree_X_pow]; have := i.isLt;omega)

variable [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b f : Fin 24 → K} {Q P : K[X]}

/-- For an actual four-site contrast, both witnesses are original
physical rows. Their numerical clocks need not occur in the same order
as the rows, and may be repeated elsewhere. No scalar exclusion is
asserted. -/
theorem width24_weak_four_extra_port (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 16 A b) (C : Width24QuadraticCover A b)
    (qd : Q.natDegree≤4) (pd : P.natDegree≤3)
    (qfit : ∀ i,quadraticSeed A b i*f i=Q.eval (reflectedClock A i)*quadraticSeed A b i)
    (pfit : ∀ i,reflectedClock A i*b i*f i=P.eval (reflectedClock A i)*quadraticSeed A b i)
    (four : (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card=4) :
    ∃ (Z : K[X]) (i j : Fin 24), j < i ∧ reverseContrast A b Q P i≠0 ∧
      reverseContrast A b Q P j≠0 ∧
      WeakFourChronologicalPorts Q Z (reflectedClock A i) (reflectedClock A j) := by
  classical
  let y := reflectedClock A
  let w := reverseContrast A b Q P
  let S := weightedSites y w
  let Z := nodalHull S
  have bound : S.card=4 := four
  have pos : 0<S.card := by omega
  obtain ⟨z,zS⟩ := Finset.card_pos.mp pos
  obtain ⟨r,ract,_⟩ := mem_weightedSites.mp zS
  have initial : ∃ k : Fin 24,w k≠0 ∧ y k∉(∅:Finset K) :=
    ⟨r,ract,by simp⟩
  have y0 : reflectedClock A (Fin.last 23)=0 := by
    change 1-nodes A (Fin.last 23)=0
    rw [C.frame.lastClock,sub_self]
  have col (k : Fin 24) : A k (Fin.last 23)=0 := ha k _ (Fin.le_last k)
  obtain ⟨i,iw,_,ia,iq,ilater,ip⟩ := true_port_at_last_new_clock ha ho y0 col C.supports
    qfit pfit (∅:Finset K) initial
  let a := y i
  have qne : Q≠0 := fun e=>iq (by rw [e,eval_zero])
  have fresh : ∃ k : Fin 24,w k≠0 ∧ y k∉({a}:Finset K) := by
    obtain ⟨k,kw,ka⟩ := reverse_contrast_many ho Q P qne (by omega) (by omega) a
    exact ⟨k,kw,fun h=>ka (Finset.mem_singleton.mp h)⟩
  obtain ⟨j,jw,ja,jc,jq,_,jp⟩ := true_port_at_last_new_clock ha ho y0 col C.supports
    qfit pfit ({a}:Finset K) fresh
  have apart : y j≠a := fun e=>ja (Finset.mem_singleton.mpr e)
  have time : j < i := by
    have j_le : j ≤ i := by
      apply le_of_not_gt
      intro late
      simpa using ilater j late jw
    exact lt_of_le_of_ne j_le (fun eq => apart (congrArg y eq))
  have roota : Z.eval a=0 := nodalHull_eval_of_mem (mem_weightedSites.mpr ⟨i,iw,rfl⟩)
  have rootc : Z.eval (y j)=0 := nodalHull_eval_of_mem (mem_weightedSites.mpr ⟨j,jw,rfl⟩)
  have first0 : (primitive (X*Q)).eval a=0 := by
    have h := ip (1:K[X]) (by simp;omega) (by simp;omega)
    simpa [nodalHull,a,y] using h
  have first1 : (primitive (X*(X*Q))).eval a=0 := by
    have h := ip (X:K[X]) (by simp;omega) (by simp;omega)
    simpa [nodalHull,a,y] using h
  have next : (primitive ((X-Polynomial.C a)*(X*Q))).eval (y j)=0 := by
    have h := jp (1:K[X]) (by simp;omega) (by simp;omega)
    simpa [nodalHull,y] using h
  refine ⟨Z,i,j,time,iw,jw,⟨qne,qd,monic_nodalHull S,(natDegree_nodalHull S).trans bound,
    roota,rootc,iq,jq,ia,jc,apart,first0,first1,next,?_⟩⟩
  intro H Hdegree
  have cap : (H*Z).natDegree≤10 := by
    have n := natDegree_mul_le (p:=H) (q:=Z)
    have zd : Z.natDegree=4 := (natDegree_nodalHull S).trans bound
    omega
  have zero : (∑ k,weightedEval y w (H*Z) k)=0 := by
    apply reverse_contrast_vanishes
    intro x hx
    rw [eval_mul,nodalHull_eval_of_mem hx,mul_zero]
  have e := reverse_contrast_moment ho Q P (H*Z) (by omega) (by omega)
  change (∑ k,weightedEval y w (H*Z) k)=(primitive ((H*Z)*(X*Q))).eval 1 at e
  rw [zero,show (H*Z)*(X*Q)=H*(X*(Q*Z)) by ring] at e
  exact e.symm

/-- Same payment opened directly on the checked width-24 paid frame. -/
theorem native_width24_weak_four_extra_port (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 16 A b)
    (qd : Q.natDegree≤4) (pd : P.natDegree≤3)
    (qfit : ∀ i,quadraticSeed A b i*f i=Q.eval (reflectedClock A i)*quadraticSeed A b i)
    (pfit : ∀ i,reflectedClock A i*b i*f i=P.eval (reflectedClock A i)*quadraticSeed A b i)
    (four : (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card=4) :
    ∃ (Z : K[X]) (i j : Fin 24), j < i ∧ reverseContrast A b Q P i≠0 ∧
      reverseContrast A b Q P j≠0 ∧
      WeakFourChronologicalPorts Q Z (reflectedClock A i) (reflectedClock A j) :=
  width24_weak_four_extra_port ha ho (width24_quadratic_cover ha ho) qd pd qfit pfit four

end
end RKResearch.Certified.ERK16
