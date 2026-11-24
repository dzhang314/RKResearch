module

public import RKCert.ReviewedNative.ERK19BroadHead
public import RKCert.ReviewedNative.NativeQuinticPorts

@[expose] public section

/-! # All broad nonzero first-seed supports are impossible at width 29

The same grade-eight head provides two physical chronological ports.
Only the small exact native 4+3 quintic identity is needed at the end. -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

structure WideContrast (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29→K)
    (P : K[X]) (θ : Fin 29→K) : Prop where
  supported : ∀ i, θ i≠0 → firstSeed A b i=0 ∧ b i≠0
  masked : ∀ Q : K[X], Q.natDegree≤4 →
    evalNodes A (Q*P)-weightedEval (nodes A) θ Q∈zeroSpace A 9

set_option maxHeartbeats 500000 in
omit [IsStrictOrderedRing K] in
theorem wide_contrast_of_head {r : ℕ} {w : Fin 29→K} {P : K[X]}
    (H : WideQuinticHead A b r w P) : ∃ θ, WideContrast A b P θ := by
  let c := nodes A
  let d := firstSeed A b
  let g (i : Fin 29) : K :=
    if d i=0 ∧ b i=0 then P.eval (c i)-w i else 0
  let θ := evalNodes A P-w-g
  refine ⟨θ,?_,?_⟩
  · intro i live
    have base : θ i=P.eval (c i)-w i-g i := by simp [θ,c]
    have charge (di : d i≠0) : θ i=0 := by
      have eq := congrFun H.trueTrace i
      simp only [weightedEval_apply,Pi.mul_apply] at eq
      have a : P.eval (c i)*d i=d i*w i := eq
      have e : P.eval (c i)=w i := (mul_left_inj' di).mp (a.trans (mul_comm (d i) (w i)))
      rw [base,e,sub_self]
      simp [g,di]
    have off : d i=0 := by by_contra z; exact live (charge z)
    refine ⟨off,fun bz=>live ?_⟩
    rw [base]
    simp [g,off,bz]
  · intro Q q
    have e : evalNodes A (Q*P)-weightedEval c θ Q =
        weightedEval c w Q+weightedEval c g Q := by
      ext i
      simp only [Pi.sub_apply,Pi.add_apply,weightedEval_apply,evalNodes_apply,c,eval_mul,θ]
      ring
    rw [e]
    have a : weightedEval c w Q∈zeroSpace A 9 := by
      rw [H.nine]
      exact weighted_mem_paid_chain Q (by have :=H.fourPaid;omega)
    have gMem : weightedEval c g Q∈jointInactive A b := by
      apply mem_jointInactive.mpr
      exact ⟨fun i di=>by simp [weightedEval_apply,g,d,di],
        fun i hi=>by simp [weightedEval_apply,g,hi]⟩
    exact (zeroSpace A 9).add_mem a (zeroSpace_mono A (by decide : 8≤9) (H.carrier gMem))

private theorem wide_contrast_primitive
    (ha : ∀i j,i ≤ j → A i j=0) (ho : HasOrder 19 A b) (nz : firstSeed A b≠0)
    (band : FullFirstBand A b) {P Q : K[X]} {θ : Fin 29→K}
    (H : WideContrast A b P θ) (dP : P.natDegree≤5) (dQ : Q.natDegree≤4)
    (i : Fin 29) (live : θ i≠0)
    (pre : ∀ j < i, weightedEval (nodes A) θ Q j=0) :
    (primitive (Q*P)).eval (nodes A i)=0 := by
  obtain ⟨di,bi⟩ := H.supported i live
  have clean := off_seed_live_ten_clean ha ho nz band i di bi
  have h : (Q*P).natDegree≤9 := natDegree_mul_le.trans (by omega)
  have defect := clean _ (primitive_defect A (Q*P) (q:=9) h)
  have remove := clean _ (mat_zeroSpace_charZero A 9 (H.masked Q dQ))
  have cause := causal_mat ha i (weightedEval (nodes A) θ Q) pre
  change mat A (weightedEval (nodes A) θ Q) i=0 at cause
  rw [map_sub,Pi.sub_apply,cause,sub_zero] at remove
  change mat A (evalNodes A (Q*P)) i-(primitive (Q*P)).eval (nodes A i)=0 at defect
  exact (sub_eq_zero.mp defect).symm.trans remove

set_option maxHeartbeats 950000 in
theorem width29_no_very_wide_first_seed
    (ha : ∀i j,i ≤ j → A i j=0) (ho : HasOrder 19 A b) (nz : firstSeed A b≠0)
    (band : FullFirstBand A b) (wide : 19≤(weightedSites (nodes A) (firstSeed A b)).card) :
    False := by
  obtain ⟨r,w,P,H⟩ := width29_very_wide_quintic_head ha ho nz band wide
  obtain ⟨θ,T⟩ := wide_contrast_of_head H
  let c := nodes A
  have four := H.fourPaid
  have deg := H.degree
  have p5 : P.natDegree≤5 := by omega
  have sep : PolySeparated A 9 := PolySeparated.of_coeff (coeff_separated ho (by decide))
  have existsLive (Q : K[X]) (q4 : Q.natDegree≤4) (qn : Q≠0) :
      ∃ i, weightedEval c θ Q i≠0 := by
    by_contra! z
    have e : weightedEval c θ Q=0 := funext z
    have h := T.masked Q q4
    rw [e,sub_zero] at h
    exact (mul_ne_zero qn H.live) (sep (Q*P) (natDegree_mul_le.trans (by omega)) h)
  let I := Finset.univ.filter (fun i : Fin 29 => θ i≠0 ∧ c i≠0)
  have iex : I.Nonempty := by
    obtain ⟨i,hi⟩ := existsLive X (by simp) X_ne_zero
    simp only [weightedEval_apply,eval_X] at hi
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun z=>hi (by rw [z,mul_zero]),
      fun z=>hi (by rw [z,zero_mul])⟩⟩
  let i := I.min' iex
  have im : i∈I := Finset.min'_mem _ _
  obtain ⟨il,iu⟩ := (Finset.mem_filter.mp im).2
  let u := c i
  let J := Finset.univ.filter (fun j : Fin 29 => θ j≠0 ∧ c j≠0 ∧ c j≠u)
  have jex : J.Nonempty := by
    let M := (X:K[X])*(X-C u)
    have mn : M≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero u)
    have mdeg : M.natDegree≤4 := by
      have m : (X-C u : K[X]).natDegree=1 := natDegree_X_sub_C u
      exact natDegree_mul_le.trans (by rw [natDegree_X,m];decide)
    obtain ⟨j,live⟩ := existsLive M mdeg mn
    simp only [M,weightedEval_apply,eval_mul,eval_sub,eval_X,eval_C] at live
    refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_,?_⟩⟩
    · exact fun z=>live (by rw [z,mul_zero])
    · exact fun z=>live (by rw [z,zero_mul,zero_mul])
    · exact fun z=>live (by rw [z,sub_self,mul_zero,zero_mul])
  let j := J.min' jex
  have jm : j∈J := Finset.min'_mem _ _
  obtain ⟨jl,jv,jd⟩ := (Finset.mem_filter.mp jm).2
  apply H.live (RKCert.ReviewedNative.Quintic.quintic_four_three P p5 iu jv jd ?_ ?_)
  · intro k
    let Q : K[X] := X^(k.val+1)
    have dq : Q.natDegree≤4 := by
      change ((X:K[X])^(k.val+1)).natDegree≤4
      rw [natDegree_X_pow]
      have :=k.isLt
      omega
    apply wide_contrast_primitive ha ho nz band T p5 dq i il
    intro z before
    by_cases hθ : θ z=0
    · simp [weightedEval_apply,hθ]
    · have hz : c z=0 := by
        by_contra cZ
        have row : z∈I := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hθ,cZ⟩
        exact (not_le_of_gt before) (Finset.min'_le _ _ row)
      rw [weightedEval_apply]
      change Q.eval (c z)*θ z=0
      simp [Q,hz]
  · intro k
    rw [←mul_assoc]
    let Q : K[X] := X^(k.val+1)*(X-C u)
    have dq : Q.natDegree≤4 := by
      apply natDegree_mul_le.trans
      rw [natDegree_X_pow,natDegree_X_sub_C]
      have :=k.isLt
      omega
    apply wide_contrast_primitive ha ho nz band T p5 dq j jl
    intro z pre
    by_cases th : θ z=0
    · simp [weightedEval_apply,th]
    · by_cases cz : c z=0
      · rw [weightedEval_apply]
        change Q.eval (c z)*θ z=0
        simp [Q,cz]
      · have cu : c z=u := by
          by_contra cu
          have row : z∈J := Finset.mem_filter.mpr ⟨Finset.mem_univ _,th,cz,cu⟩
          exact (not_le_of_gt pre) (Finset.min'_le _ _ row)
        rw [weightedEval_apply]
        change Q.eval (c z)*θ z=0
        simp [Q,cu]

/-- The previously balanced-band exclusion and the wide physical
quintic ports together leave only one or two clocks on the nonzero
first-seed branch. There is no claim about a zero first seed. -/
theorem width29_nonzero_first_seed_at_most_two
    (ha : ∀i j,i ≤ j → A i j=0) (ho : HasOrder 19 A b) (nz : firstSeed A b≠0) :
    (weightedSites (reflectedClock A) (firstSeed A b)).card≤2 := by
  rcases width29_nonzero_broad_or_local ha ho nz with h | ⟨w,band⟩
  · exact h
  exfalso
  have wc : 19≤(weightedSites (nodes A) (firstSeed A b)).card := by
    have e := first_seed_site_card_eq (A:=A) (b:=b)
    rcases width29_first_seed_local_or_ge_nineteen ha ho nz with loc | many <;> omega
  exact width29_no_very_wide_first_seed ha ho nz band wc

end
end RKResearch.Certified.ERK19
