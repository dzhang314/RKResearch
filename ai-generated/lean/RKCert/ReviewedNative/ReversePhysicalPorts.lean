module

public import RKCert.ReviewedNative.ReversePaidTraces
public import RKCert.ReviewedNative.NativePrimitiveMoments
public import RKCert.ReviewedNative.PhysicalEndpointMomentPorts

@[expose] public section

/-! # Signed physical transpose probes on the thin reverse complement

The quadratic seed vanishes at the true contrast rows. Exact native
duality makes the actual transpose action there equal a primitive
probe, and chronology selects the first two distinct nonzero clocks.
The two-clock supply uses the all-field finite Cauchy moment test. -/
namespace RKResearch.Certified.Graded.Reverse.Thin
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open NativeMoments
open scoped Classical Matrix

noncomputable section
variable {K : Type*} [Field K] {s p m : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b f : Fin s→K}
set_option maxRecDepth 3500
set_option maxHeartbeats 800000

def reverseContrast (A:Matrix (Fin s) (Fin s) K) (b:(Fin s→K)) (Q P:K[X]) : (Fin s→K) :=
  weightedEval (reflectedClock A) b (X*Q)-weightedEval (reflectedClock A) (quadraticSeed A b) P

theorem reverseContrast_weighted (Q P R:K[X]) :
    weightedEval (reflectedClock A) (reverseContrast A b Q P) R =
      weightedEval (reflectedClock A) b (R*(X*Q))-weightedEval (reflectedClock A) (quadraticSeed A b) (R*P) := by
  ext i
  simp only [reverseContrast,weightedEval_apply,Pi.sub_apply,eval_mul]
  ring

theorem reverse_contrast_moment (ho : HasOrder p A b) (Q P H : K[X])
    (qpay : Q.natDegree+H.natDegree+2≤p) (ppay : P.natDegree+H.natDegree+3≤p) :
    (∑ i,weightedEval (reflectedClock A) (reverseContrast A b Q P) H i)=
      (primitive (H*(X*Q))).eval 1 := by
  have dP : (H*P).natDegree+3≤p := by
    have h := natDegree_mul_le (p:=H) (q:=P)
    omega
  have dQ : (H*(X*Q)).natDegree+1≤p := by
    have h := natDegree_mul_le (p:=H) (q:=X*Q)
    have i := natDegree_mul_le (p:=X) (q:=Q)
    rw [natDegree_X] at i
    omega
  rw [reverseContrast_weighted]
  simp only [Pi.sub_apply,Finset.sum_sub_distrib,reflected_polynomial_mass ho _ dQ,
    seed_eval_mass ho _ dP,sub_zero]

theorem reverse_contrast_true_support {Q P : K[X]}
    (qfit : ∀ i,quadraticSeed A b i*f i=Q.eval (reflectedClock A i)*quadraticSeed A b i)
    (pfit : ∀ i,reflectedClock A i*b i*f i=P.eval (reflectedClock A i)*quadraticSeed A b i)
    (i : Fin s) (act : reverseContrast A b Q P i≠0) :
    quadraticSeed A b i=0 ∧ reflectedClock A i≠0 ∧ b i≠0 ∧
      Q.eval (reflectedClock A i)≠0 ∧ f i=0 := by
  have off : quadraticSeed A b i=0 := by
    by_contra z
    have he := qfit i
    rw [mul_comm (Q.eval _)] at he
    have e := mul_left_cancel₀ z he
    have ph := pfit i
    rw [e] at ph
    apply act
    simp only [reverseContrast,Pi.sub_apply,weightedEval_apply,eval_mul,eval_X]
    change (reflectedClock A i*Q.eval (reflectedClock A i))*b i-
      P.eval (reflectedClock A i)*quadraticSeed A b i=0
    linear_combination ph
  have pf := pfit i
  rw [off,mul_zero] at pf
  have wt : reflectedClock A i*(Q.eval (reflectedClock A i))*b i≠0 := by
    simpa only [reverseContrast,Pi.sub_apply,weightedEval_apply,eval_mul,eval_X,
      off,mul_zero,sub_zero] using act
  obtain ⟨yq,bi⟩ := mul_ne_zero_iff.mp wt
  obtain ⟨y,q⟩ := mul_ne_zero_iff.mp yq
  exact ⟨off,y,bi,q,(mul_eq_zero.mp pf).resolve_left (mul_ne_zero y bi)⟩

theorem reverse_contrast_vanishes (W : Fin s→K) (H : K[X])
    (h : ∀ a∈weightedSites (reflectedClock A) W,H.eval a=0) :
    (∑i,weightedEval (reflectedClock A) W H i)=0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases e : W i=0
  · simp [e]
  · rw [weightedEval_apply,h _ (mem_weightedSites.mpr ⟨i,e,rfl⟩),zero_mul]

private theorem transpose_zero_column (t : Fin s) (col : ∀ k,A k t=0) (v : Fin s→K) :
    mat A.transpose v t=0 := by
  change (∑ k,A k t*v k)=0
  exact Finset.sum_eq_zero fun k _ => by rw [col k,zero_mul]

variable [CharZero K]

theorem true_port_eval (ho:HasOrder p A b) {t:Fin s}
    (y0:reflectedClock A t=0) (col:∀k,A k t=0) (cover:SupportsComplement A b m t)
    (Q P R:K[X]) (qb:m+Q.natDegree+R.natDegree+3≤p)
    (pb:m+P.natDegree+R.natDegree+4≤p)
    {i:Fin s} (off:quadraticSeed A b i=0) :
    mat A.transpose (weightedEval (reflectedClock A) (reverseContrast A b Q P) R) i =
      (primitive (R*(X*Q))).eval (reflectedClock A i)*b i := by
  let y:=reflectedClock A
  let S:=R*(X*Q)
  let T:=R*P
  let d:=quadraticSeed A b
  have dg:S.natDegree≤R.natDegree+1+Q.natDegree:=by
    have h:=natDegree_mul_le (p:=R) (q:=X*Q)
    have k:=natDegree_mul_le (p:=X) (q:=Q)
    rw [natDegree_X] at k
    dsimp [S];omega
  have dt:T.natDegree≤R.natDegree+P.natDegree:=natDegree_mul_le
  have d1:mat A.transpose (weightedEval y b S)-weightedEval y b (primitive S)∈
      zeroAt (annih (treeSpace A m)) t:=by
    refine mem_zeroAt.mpr ⟨?_,?_⟩
    · exact primitiveBack_annih ho m (R.natDegree+Q.natDegree+1) (by omega)
        (reverse_primitive_next _ S (by omega))
    ·
      change mat A.transpose (weightedEval y b S) t-weightedEval y b (primitive S) t=0
      rw [transpose_zero_column t col]
      simp [y,y0,←coeff_zero_eq_eval_zero]
  have d2:mat A.transpose (weightedEval y d T)∈
      zeroAt (annih (treeSpace A m)) t:=by
    refine mem_zeroAt.mpr ⟨mem_annih.mpr ?_,transpose_zero_column t col _⟩
    intro x hx
    rw [row_mat_transpose]
    exact mem_annih.mp (seed_eval_annih (m:=m+1) ho T (by omega)) _ (mat_treeSpace A m hx)
  have z1:=cover _ d1 i off
  have z2:=cover _ d2 i off
  rw [reverseContrast_weighted,map_sub,Pi.sub_apply]
  change mat A.transpose (weightedEval y b S) i-mat A.transpose (weightedEval y d T) i=_
  change mat A.transpose (weightedEval y b S) i-weightedEval y b (primitive S) i=0 at z1
  rw [z2,sub_zero,sub_eq_zero.mp z1,weightedEval_apply]

structure ReverseThreeTwo (A:Matrix (Fin s) (Fin s) K) (Q:K[X]) (u v:K) : Prop where
  u_ne : u≠0
  v_ne : v≠0
  different : v≠u
  left : ∀R:K[X],R.natDegree≤2→(primitive (R*(X*Q))).eval u=0
  right : ∀R:K[X],R.natDegree≤1→(primitive (R*(X*(X-C u)*Q))).eval v=0

/-- For two distinct active numerical ports on the actual contrast, each
chronological pivot receives exactly the required strict prefix mask. -/
theorem actual_reverse_three_two (ha : ∀ i j, i≤j → A i j=0) (ho:HasOrder p A b) {t:Fin s}
    (y0:reflectedClock A t=0) (col:∀k,A k t=0) (cover:SupportsComplement A b m t)
    (Q P:K[X]) (qb:m+Q.natDegree+5≤p) (pb:m+P.natDegree+6≤p)
    (off:∀i,reverseContrast A b Q P i≠0→quadraticSeed A b i=0)
    (two:∀a:K,∃i,reverseContrast A b Q P i≠0 ∧ reflectedClock A i≠a) :
    ∃u v,ReverseThreeTwo A Q u v := by
  classical
  let y:=reflectedClock A
  let w:=reverseContrast A b Q P
  let L:=Finset.univ.filter (fun i:Fin s =>w i≠0)
  obtain ⟨i,hi,imax⟩:=Finset.exists_max_image L id (by
    obtain ⟨k,kw,_⟩:=two 0
    exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,kw⟩⟩)
  have iw:w i≠0:=(Finset.mem_filter.mp hi).2
  let u:=y i
  let M:=L.filter (fun k=>y k≠u)
  obtain ⟨j,hj,jmax⟩:=Finset.exists_max_image M id (by
    obtain ⟨k,kw,ku⟩:=two u
    exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,kw⟩,ku⟩⟩)
  have jw:w j≠0:=(Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  have jv:y j≠u:=(Finset.mem_filter.mp hj).2
  have active (k:Fin s)(hk:w k≠0):y k≠0 ∧ b k≠0:=by
    have zz:=off k hk
    refine ⟨?_,?_⟩
    · intro yk
      apply hk
      simp [w,reverseContrast,y,yk,zz]
    · intro bk
      apply hk
      simp [w,reverseContrast,bk,zz]
  refine ⟨u,y j,⟨(active i iw).1,(active j jw).1,jv,?_,?_⟩⟩
  · intro R hr
    have z:mat A.transpose (weightedEval y w R) i=0:=by
      apply causal_transpose ha
      intro k hk
      have lt:=Fin.rev_lt_rev.mp hk
      have no:w k=0:=by
        by_contra kn
        exact (not_le_of_gt lt) (imax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,kn⟩))
      simp [no]
    have eq:=true_port_eval ho y0 col cover Q P R (by omega) (by omega) (off i iw)
    change mat A.transpose (weightedEval y w R) i=_ at eq
    rw [z] at eq
    exact (mul_eq_zero.mp eq.symm).resolve_right (active i iw).2
  · intro R hr
    let H:=R*(X-C u)
    have hd:H.natDegree≤2:=by
      have e:=natDegree_mul_le (p:=R) (q:=X-C u)
      rw [natDegree_X_sub_C] at e
      dsimp [H];omega
    have z:mat A.transpose (weightedEval y w H) j=0:=by
      apply causal_transpose ha
      intro k hk
      have lt:=Fin.rev_lt_rev.mp hk
      by_cases no:w k=0
      · simp [no]
      have ky:y k=u:=by
        by_contra ne
        exact (not_le_of_gt lt) (jmax k (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,no⟩,ne⟩))
      simp [H,ky]
    have eq:=true_port_eval ho y0 col cover Q P H (by omega) (by omega) (off j jw)
    change mat A.transpose (weightedEval y w H) j=_ at eq
    rw [z] at eq
    have van: (primitive (H*(X*Q))).eval (y j)=0:=
      (mul_eq_zero.mp eq.symm).resolve_right (active j jw).2
    rwa [show H*(X*Q)=R*(X*(X-C u)*Q) by dsimp [H];ring] at van

/-- If a nonzero profile supported only a single contrast clock a,
consecutive paid tests would annihilate (X−a)Q in the exact X-moment
system. This proves the two-clock supply without a numerical Gram test. -/
theorem reverse_contrast_many (ho : HasOrder p A b) (Q P : K[X]) (qn : Q≠0)
    (qpay : 2*Q.natDegree+4≤p) (ppay : Q.natDegree+P.natDegree+5≤p) :
    ∀ a : K,∃ i,reverseContrast A b Q P i≠0 ∧ reflectedClock A i≠a := by
  intro a
  by_contra! onlySite
  let H : K[X] := (X-C a)*Q
  let n := Q.natDegree+1
  have hd : H.natDegree≤n := by
    have h := natDegree_mul_le (p:=X-C a) (q:=Q)
    rw [natDegree_X_sub_C] at h
    dsimp [H,n]
    omega
  have tst (i : Fin (n+1)) : (primitive (X^i.val*(X*H))).eval 1=0 := by
    let R : K[X] := X^i.val*(X-C a)
    have rd : R.natDegree ≤ i.val+1 := by
      exact natDegree_mul_le_of_le (show (X^i.val:K[X]).natDegree ≤ i.val from natDegree_X_pow i.val |>.le)
        (show (X-C a : K[X]).natDegree≤1 from (natDegree_X_sub_C a).le)
    have z : (∑ k,weightedEval (reflectedClock A) (reverseContrast A b Q P) R k)=0 := by
      apply reverse_contrast_vanishes
      intro x hx
      obtain ⟨k,nz,rfl⟩ := mem_weightedSites.mp hx
      simp [R,onlySite k nz]
    have hi := i.isLt
    dsimp [n] at hi
    have eq := reverse_contrast_moment ho Q P R (by omega) (by omega)
    rw [z] at eq
    rw [show X^i.val*(X*H)=R*(X*Q) by dsimp [H,R];ring]
    exact eq.symm
  exact (mul_ne_zero (X_sub_C_ne_zero a) qn) (x_moments_detect hd tst)

section Ordered
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {T : Matrix (Fin s) (Fin s) F} {w v : Fin s→F}

theorem ordered_thin_invisible_given_reps
    (ha : ∀ i j,i≤j → T i j=0) (ho : HasOrder p T w)
    {t : Fin s} (y0 : reflectedClock T t=0) (col : ∀ k,T k t=0)
    (cover : SupportsComplement T w m t) (Q P : F[X]) (deg : Q.natDegree≤4)
    (qm : 2*Q.natDegree+4≤p) (pm : Q.natDegree+P.natDegree+5≤p)
    (qport : m+Q.natDegree+5≤p) (pport : m+P.natDegree+6≤p)
    (qfit : ∀ i,quadraticSeed T w i*v i=Q.eval (reflectedClock T i)*quadraticSeed T w i)
    (pfit : ∀ i,reflectedClock T i*w i*v i=P.eval (reflectedClock T i)*quadraticSeed T w i) :
    ∀ i,quadraticSeed T w i*v i=0 ∧ reflectedClock T i*w i*v i=0 := by
  have Qz : Q=0 := by
    by_contra qn
    have off (i : Fin s) (hi : reverseContrast T w Q P i≠0) : quadraticSeed T w i=0 :=
      (reverse_contrast_true_support qfit pfit i hi).1
    obtain ⟨u,v,B⟩ := actual_reverse_three_two ha ho y0 col cover Q P qport pport off
      (reverse_contrast_many ho Q P qn qm pm)
    exact qn (RKCert.EndpointPhysical.ordered_quartic_eq_zero_of_primitives deg B.u_ne B.v_ne
      B.different ⟨by simpa only [formalPrimitive_eq_native] using B.left,
        by simpa only [formalPrimitive_eq_native] using B.right⟩)
  intro i
  have q := qfit i
  rw [Qz,eval_zero,zero_mul] at q
  refine ⟨q,?_⟩
  by_cases d : quadraticSeed T w i=0
  · simpa only [d,mul_zero] using pfit i
  · rw [(mul_eq_zero.mp q).resolve_left d,mul_zero]

end Ordered
end
end RKResearch.Certified.Graded.Reverse.Thin
