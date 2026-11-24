module

public import RKCert.ReviewedNative.ERK19ZeroHead

public section

/-! # Actual ordered three-two-one reverse ports at the width-29 zero branch

Every masked port is paid at the original transpose row. A mask kills
all later physical rows carrying one of the previous distinct clocks,
so duplicate clocks and zero weights do not create fictitious pivots.
-/
namespace RKResearch.Certified.ERK19

open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open scoped Classical

noncomputable section
variable {K : Type*} [Field K] {s : ℕ}

private theorem latest_active_avoiding (y W : Fin s → K) (T : Finset K)
    (enough : T.card<(weightedSites y W).card) :
    ∃ i, W i≠0 ∧ y i∉T ∧ ∀ j, i < j → W j≠0 → y j∈T := by
  let L := Finset.univ.filter (fun i : Fin s => W i≠0 ∧ y i∉T)
  have ne : L.Nonempty := by
    by_contra no
    have sub : weightedSites y W ⊆ T := by
      intro x hx
      obtain ⟨i,wi,rfl⟩ := mem_weightedSites.mp hx
      by_contra hi
      exact no ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,wi,hi⟩⟩
    exact (not_le_of_gt enough) (Finset.card_le_card sub)
  obtain ⟨i,hi,last⟩ := Finset.exists_max_image L id ne
  obtain ⟨wi,yi⟩ := (Finset.mem_filter.mp hi).2
  refine ⟨i,wi,yi,fun j ji wj => ?_⟩
  by_contra yj
  exact (not_le_of_gt ji) (last j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,wj,yj⟩))

variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29 → K}

/-- Every nonzero contrast coordinate is an actual paid physical port. -/
theorem Width29ZeroHead.active
    {h : Fin 29 → K} {Q E : K[X]} (H : Width29ZeroHead A b h Q E)
    {i : Fin 29} (wi : reverseContrast A b Q E i≠0) :
    quadraticSeed A b i=0 ∧ reflectedClock A i≠0 ∧ b i≠0 ∧
      Q.eval (reflectedClock A i)≠0 ∧ h i=0 :=
  reverse_contrast_true_support H.traceQ H.traceE i wi

/-- Exact paid polynomial primitive windows on three original rows in
decreasing chronological order. The row labels are not invented nodes. -/
structure Width29ReversePortSequence (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29 → K)
    (Q E : K[X]) (i j k : Fin 29) : Prop where
  chron : k < j ∧ j < i
  live : reverseContrast A b Q E i≠0 ∧ reverseContrast A b Q E j≠0 ∧ reverseContrast A b Q E k≠0
  nonzeroClock : reflectedClock A i≠0 ∧ reflectedClock A j≠0 ∧ reflectedClock A k≠0
  distinct : reflectedClock A j≠reflectedClock A i ∧
    reflectedClock A k≠reflectedClock A i ∧ reflectedClock A k≠reflectedClock A j
  first : ∀ R : K[X], R.natDegree≤2 → (primitive (R*(X*Q))).eval (reflectedClock A i)=0
  second : ∀ R : K[X], R.natDegree≤1 →
    (primitive ((R*(X-C (reflectedClock A i)))*(X*Q))).eval (reflectedClock A j)=0
  third : (primitive (((X-C (reflectedClock A i))*(X-C (reflectedClock A j)))*(X*Q))).eval
    (reflectedClock A k)=0

variable [CharZero K]

/-- A true later-tail vanishing test exposes the native primitive
at a nonzero contrast row. The degree-two cap is the actual paid
order-19 grade-nine annihilator budget. -/
theorem Width29ZeroHead.port_of_later_mask (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 19 A b) {h : Fin 29 → K} {Q E : K[X]} (H : Width29ZeroHead A b h Q E)
    (Z : Width29ZeroCover A b) {i : Fin 29} (wi : reverseContrast A b Q E i≠0)
    (R : K[X]) (dR : R.natDegree≤2)
    (late : ∀ j, i<j → R.eval (reflectedClock A j)*reverseContrast A b Q E j=0) :
    (primitive (R*(X*Q))).eval (reflectedClock A i)=0 := by
  let t := Fin.last 28
  have y0 : reflectedClock A t=0 := by change 1-nodes A t=0; rw [Z.lastClock,sub_self]
  have col (j : Fin 29) : A j t=0 := ha j t (Fin.le_last j)
  have cov : SupportsComplement A b 9 t := supportsComplement_of_cover Z.pointwise
  have qd := H.quintic
  have ed := H.auxDegree
  have eq := true_port_eval ho y0 col cov Q E R (by omega) (by omega) (H.active wi).1
  have z : mat A.transpose (weightedEval (reflectedClock A) (reverseContrast A b Q E) R) i=0 := by
    apply causal_transpose ha
    intro j hj
    simp only [weightedEval_apply]
    exact late j (Fin.rev_lt_rev.mp hj)
  rw [z] at eq
  exact (mul_eq_zero.mp eq.symm).resolve_right (H.active wi).2.2.1

theorem Width29ZeroHead.reverse_ports (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 19 A b)
    {h : Fin 29 → K} {Q E : K[X]} (H : Width29ZeroHead A b h Q E)
    (Z : Width29ZeroCover A b) :
    ∃ i j k, Width29ReversePortSequence A b Q E i j k := by
  let W := reverseContrast A b Q E
  let Y := reflectedClock A
  have four : 4≤(weightedSites Y W).card := H.fourSites
  obtain ⟨i,wi,_,late1⟩ := latest_active_avoiding Y W ∅ (by simp only [Finset.card_empty]; omega)
  let u := Y i
  obtain ⟨j,wj,jn,late2⟩ := latest_active_avoiding Y W {u} (by simp only [Finset.card_singleton]; omega)
  let v := Y j
  have c2 : ({u,v}:Finset K).card≤2 := (Finset.card_insert_le _ _).trans (by simp)
  obtain ⟨k,wk,kn,late3⟩ := latest_active_avoiding Y W {u,v} (by omega)
  have vu : v≠u := by simpa only [Finset.mem_singleton] using jn
  have ku : Y k≠u := fun e => kn (by simp [e])
  have kv : Y k≠v := fun e => kn (by simp [e])
  have ji : j < i := by
    by_contra! e
    have neq : i≠j := fun e => vu (congrArg Y e.symm)
    exact (Finset.notMem_empty (Y j)) (late1 j (lt_of_le_of_ne e neq) wj)
  have kj : k < j := by
    by_contra! e
    have neq : j≠k := fun e => kv (congrArg Y e.symm)
    exact ku (Finset.mem_singleton.mp (late2 k (lt_of_le_of_ne e neq) wk))
  refine ⟨i,j,k,⟨⟨kj,ji⟩,⟨wi,wj,wk⟩,⟨(H.active wi).2.1,(H.active wj).2.1,(H.active wk).2.1⟩,
    ⟨vu,ku,kv⟩,?_,?_,?_⟩⟩
  · intro R dR
    apply H.port_of_later_mask ha ho Z wi R dR
    intro a gt
    by_cases z : W a=0
    · change R.eval (Y a)*W a=0
      rw [z,mul_zero]
    · exact False.elim ((Finset.notMem_empty (Y a)) (late1 a gt z))
  · intro R dR
    let P : K[X] := R*(X-C u)
    have dp : P.natDegree≤2 :=
      natDegree_mul_le_of_le dR (natDegree_X_sub_C u).le
    apply H.port_of_later_mask ha ho Z wj P dp
    intro a gt
    by_cases z : W a=0
    · change P.eval (Y a)*W a=0
      rw [z,mul_zero]
    have c : Y a=u := Finset.mem_singleton.mp (late2 a gt z)
    change P.eval (Y a)*W a=0
    simp [P,c]
  · let P : K[X] := (X-C u)*(X-C v)
    have dp : P.natDegree≤2 :=
      natDegree_mul_le_of_le (natDegree_X_sub_C u).le (natDegree_X_sub_C v).le
    apply H.port_of_later_mask ha ho Z wk P dp
    intro a gt
    by_cases z : W a=0
    · change P.eval (Y a)*W a=0
      rw [z,mul_zero]
    have c := late3 a gt z
    simp only [Finset.mem_insert,Finset.mem_singleton] at c
    change P.eval (Y a)*W a=0
    rcases c with c|c <;> simp [P,c]

end
end RKResearch.Certified.ERK19

namespace RKResearch.Certified.ERK19
open RKResearch Polynomial RKResearch.Certified.Graded.Reverse

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29 → K}

/-- A zero actual first seed at width 29 forces the physical reverse
ports and the forced quintic/row-budget frame without another premise. -/
theorem width29_zero_reverse_ports (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 19 A b)
    (zero : firstSeed A b=0) :
    ∃ (h : Fin 29 → K) (Q E : K[X]) (i j k : Fin 29),
      Width29ZeroHead A b h Q E ∧ Width29ReversePortSequence A b Q E i j k := by
  obtain ⟨h,Q,E,H⟩ := width29_zero_head ha ho zero
  obtain ⟨i,j,k,P⟩ := H.reverse_ports ha ho (width29_zero_cover_data ha ho zero)
  exact ⟨h,Q,E,i,j,k,H,P⟩

end RKResearch.Certified.ERK19

