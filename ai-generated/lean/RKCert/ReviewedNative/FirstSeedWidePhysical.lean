module

public import RKCert.ReviewedNative.FirstSeedWideTrace
public import RKCert.ReviewedNative.NativePrimitiveMoments
public import RKCert.ReviewedNative.PhysicalEndpointMomentPorts

@[expose] public section

/-! # Native signed first-seed contrast and physical quartic port -/
namespace RKResearch.Certified.Graded.Reverse.FirstWide
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open NativeMoments
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] {s p m h : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b f : Fin s→K}
set_option maxRecDepth 3500
set_option maxHeartbeats 850000

private theorem weighted_monomial (k : ℕ) (a : K) :
    weightedEval (reflectedClock A) b (monomial k a)=a • reflectedStageWeight A b k := by
  ext i
  simp only [weightedEval_apply,eval_monomial,Pi.smul_apply,smul_eq_mul,reflectedStageWeight]
  ring

/-- The reflected primitive residual with constant degree zero belongs
to the genuine initial flag, with no borrowed next-grade budget. -/
theorem reverse_primitive_mem [CharZero K] {P : K[X]} {n : ℕ} (pay : P.natDegree≤n) :
    mat A.transpose (weightedEval (reflectedClock A) b P)-
      weightedEval (reflectedClock A) b (primitive P)∈primitiveBack A b n := by
  by_cases z : n=0
  · subst n
    rw [eq_C_of_natDegree_eq_zero (show P.natDegree=0 by omega),show C (P.coeff 0)=monomial 0 (P.coeff 0) by simp,
      primitive_monomial,weighted_monomial,weighted_monomial]
    simp only [Nat.zero_add,Nat.cast_one,div_one,map_smul,←smul_sub]
    have e : mat A.transpose (reflectedStageWeight A b 0)-reflectedStageWeight A b 1=
        firstSeed A b := by
      change _=reflectedStageRow A b 0
      simp only [reflectedStageRow,Nat.zero_add,Nat.cast_one,one_smul,mat_apply]
    rw [e]
    exact (primitiveBack A b 0).smul_mem _ (Submodule.mem_span_singleton_self _)
  · have pos : n-1+1=n := by omega
    have e := reverse_primitive_next (A:=A) (b:=b) (n-1) P (by omega)
    rwa [pos] at e

theorem linear_contrast_moment (ho : HasOrder p A b) (Q P R : K[X])
    (qd : Q.natDegree+R.natDegree+1≤p) (pd : P.natDegree+R.natDegree+2≤p) :
    (∑ i, weightedEval (reflectedClock A) (linearContrast A b Q P) R i)=
      (primitive (R*Q)).eval 1 := by
  have e := natDegree_mul_le (p:=R) (q:=Q)
  have f := natDegree_mul_le (p:=R) (q:=P)
  rw [linear_contrast_filter]
  simp only [Pi.sub_apply,Finset.sum_sub_distrib,reflected_polynomial_mass ho (R*Q) (by omega),
    seed_eval_mass ho (R*P) (by omega),sub_zero]

theorem physical_port [CharZero K] (ho : HasOrder p A b) (B : Cover A b m h)
    (Q P R : K[X]) (qb : m+Q.natDegree+R.natDegree+2≤p)
    (pb : m+P.natDegree+R.natDegree+3≤p) {i : Fin s} (off : firstSeed A b i=0) :
    mat A.transpose (weightedEval (reflectedClock A) (linearContrast A b Q P) R) i=
      (primitive (R*Q)).eval (reflectedClock A i)*b i := by
  let y := reflectedClock A
  let d := firstSeed A b
  let S := R*Q
  let T := R*P
  have ds : S.natDegree≤R.natDegree+Q.natDegree := natDegree_mul_le
  have dt : T.natDegree≤R.natDegree+P.natDegree := natDegree_mul_le
  have one : mat A.transpose (weightedEval y b S)-weightedEval y b (primitive S)∈annih (treeSpace A m) :=
    primitiveBack_annih ho m _ (by omega) (reverse_primitive_mem ds)
  have two : mat A.transpose (weightedEval y d T)∈annih (treeSpace A m) := by
    apply mem_annih.mpr
    intro v hv
    rw [row_mat_transpose]
    exact mem_annih.mp (seed_eval_annih (m:=m+1) ho T (by omega)) _ (mat_treeSpace A m hv)
  have z1 := B.support one off
  have z2 := B.support two off
  rw [linear_contrast_filter,map_sub,Pi.sub_apply]
  change mat A.transpose (weightedEval y b S) i-mat A.transpose (weightedEval y d T) i=_
  change mat A.transpose (weightedEval y b S) i-weightedEval y b (primitive S) i=0 at z1
  rw [z2,sub_zero,sub_eq_zero.mp z1,weightedEval_apply]

variable [CharZero K]

/-- At least two distinct nonzero physical contrast clocks are forced
by the native signed moments, independent of positivity of stage weights. -/
theorem two_nonzero_clocks (ho : HasOrder p A b) (Q P : K[X]) (qn : Q≠0)
    (qd : 2*Q.natDegree+4≤p) (pd : Q.natDegree+P.natDegree+5≤p) :
    ∀ u : K,∃ i,linearContrast A b Q P i≠0 ∧ reflectedClock A i≠0 ∧ reflectedClock A i≠u := by
  intro u
  by_contra! no
  let y := reflectedClock A
  let W := linearContrast A b Q P
  let H : K[X] := (X-C u)*Q
  let n := Q.natDegree+1
  have hD : H.natDegree≤n := by
    have h := natDegree_mul_le (p:=X-C u) (q:=Q)
    rw [natDegree_X_sub_C] at h
    dsimp [H,n]
    omega
  have tests (k : Fin (n+1)) : (primitive (X^k.val*(X*H))).eval 1=0 := by
    let R : K[X] := X^k.val*(X*(X-C u))
    have dR : R.natDegree ≤ k.val+2 := by
      have a := natDegree_mul_le (p:=X) (q:=X-C u)
      rw [natDegree_X,natDegree_X_sub_C] at a
      apply natDegree_mul_le_of_le (natDegree_X_pow _).le a
    have noMass : ∑ i,weightedEval y W R i=0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases wi : W i=0
      · simp [wi]
      · by_cases zi : y i=0
        · simp [R,zi]
        · have eq : y i=u := no i wi zi
          simp [R,eq]
    have e : (primitive (X^k.val*(X*H))).eval 1=(primitive (R*Q)).eval 1 := by
      rw [show X^k.val*(X*H)=R*Q by dsimp [R,H]; ring]
    have kk := k.isLt
    dsimp [n] at kk
    rw [e,←linear_contrast_moment ho Q P R (by omega) (by omega)]
    exact noMass
  exact (mul_ne_zero (X_sub_C_ne_zero u) qn) (x_moments_detect hD tests)

omit [CharZero K] in
theorem fit_invisible {Q P : K[X]} (fit : LinearFits A b f Q P) (qz : Q=0) :
    ∀ i, (firstSeed A b i≠0∨b i≠0) → f i=0 := by
  intro i vis
  have q := fit.1 i
  rw [qz,eval_zero,zero_mul] at q
  rcases vis with nz|bz
  · exact (mul_eq_zero.mp q).resolve_left nz
  by_cases d : firstSeed A b i=0
  · have e := fit.2 i
    rw [d,mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_left bz
  · exact (mul_eq_zero.mp q).resolve_left d

end
end RKResearch.Certified.Graded.Reverse.FirstWide

namespace RKResearch.Certified.Graded.Reverse.FirstWide
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s p m h : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b f : Fin s→K}
set_option maxRecDepth 3500
set_option maxHeartbeats 850000

theorem ordered_invisible_given_reps (ha : ∀ i j,i≤j → A i j=0)(ho:HasOrder p A b)
    (B:Cover A b m h) (Q P:K[X]) (dQ:Q.natDegree≤4)
    (qm:2*Q.natDegree+4≤p)(pm:Q.natDegree+P.natDegree+5≤p)
    (qb:m+Q.natDegree+5≤p)(pb:m+P.natDegree+6≤p)(fit:LinearFits A b f Q P):
    ∀i,firstSeed A b i*f i=0 ∧ b i*f i=0:=by
  have vanish:Q=0:=by
    by_contra nz
    classical
    let y:=reflectedClock A
    let W:=linearContrast A b Q P
    have two:=two_nonzero_clocks ho Q P nz qm pm
    let D:Finset (Fin s):=Finset.univ.filter (fun i=>W i≠0 ∧ y i≠0)
    have ne:D.Nonempty:=by
      obtain ⟨i,wi,yi,_⟩:=two 0
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,wi,yi⟩⟩
    let i:=D.max' ne
    let u:=y i
    have iD:W i≠0 ∧ u≠0:=(Finset.mem_filter.mp (D.max'_mem ne)).2
    let E:=D.filter (fun i=>y i≠u)
    have En:E.Nonempty:=by
      obtain ⟨j,wj,yj,uj⟩:=two u
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,wj,yj⟩,uj⟩⟩
    let j:=E.max' En
    have jE:=Finset.mem_filter.mp (E.max'_mem En)
    have jD:W j≠0 ∧ y j≠0:=(Finset.mem_filter.mp jE.1).2
    have zero (k:Fin s)(wk:W k≠0)(R:K[X])(dr:R.natDegree≤3)
        (off:∀l:Fin s,k<l→W l≠0→R.eval (y l)=0):
        (primitive (R*Q)).eval (y k)=0:=by
      have e:mat A.transpose (weightedEval y W R) k=0:=by
        apply causal_transpose ha
        intro l kl
        rw [weightedEval_apply]
        by_cases wl:W l=0
        · rw [wl,mul_zero]
        · rw [off l (Fin.rev_lt_rev.mp kl) wl,zero_mul]
      have sp:=fit.contrast_support wk
      have zz:=physical_port ho B Q P R (by omega) (by omega) sp.1
      change mat A.transpose (weightedEval y W R) k=_ at zz
      rw [e] at zz
      exact (mul_eq_zero.mp zz.symm).resolve_right sp.2.1
    apply nz (RKCert.EndpointPhysical.ordered_quartic_eq_zero_of_primitives dQ iD.2 jD.2 jE.2 ⟨?_,?_⟩)
    · intro R dr
      rw [formalPrimitive_eq_native]
      rw [show R*(X*Q)=(R*X)*Q by ring]
      apply zero i iD.1 (R*X) (natDegree_mul_le.trans (by rw [natDegree_X];omega))
      intro l lt wl
      have z:y l=0:=by
        by_contra h
        exact (not_le_of_gt lt) (D.le_max' _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,wl,h⟩))
      simp [z]
    · intro R dr
      rw [formalPrimitive_eq_native]
      let S:K[X]:=R*(X*(X-C u))
      rw [show R*(X*(X-C u)*Q)=S*Q by dsimp [S];ring]
      apply zero j jD.1 S
      · have a:=natDegree_mul_le (p:=R) (q:=X*(X-C u))
        have e:=natDegree_mul_le (p:=X) (q:=X-C u)
        rw [natDegree_X,natDegree_X_sub_C] at e
        dsimp only [S];omega
      · intro l lt wl
        by_cases z:y l=0
        · simp [S,z]
        have n:y l=u:=by
          by_contra neq
          exact (not_le_of_gt lt) (E.le_max' _ (Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,wl,z⟩,neq⟩))
        simp [S,n]
  intro i
  have q:=fit.1 i
  rw [vanish,eval_zero,zero_mul] at q
  refine ⟨q,?_⟩
  by_cases h:firstSeed A b i=0
  · simpa only [h,mul_zero] using fit.2 i
  · rw [(mul_eq_zero.mp q).resolve_left h,mul_zero]

end
end RKResearch.Certified.Graded.Reverse.FirstWide
