module
public import RKCert.ERKOddReverseHorizon
public import RKCert.ERKThinReverseInvisibility

@[expose] public section
/-! # Full thin reverse traces when the linear adjoint has broad support -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [CharZero K] {s p m j h:ℕ}
variable {A:Fin s→Fin s→K} {b f:Vec K s}
noncomputable section

omit [CharZero K] in
theorem linear_seed_annih (ho:HasTreeOrderAtLeast A b p) (P:K[X])
    (pay:m+P.natDegree+2≤p) :
    weightedEval (mirror A) (backSeed1 A b) P∈annih (treeSpace A m):=by
  apply mem_annih.mpr
  intro u hu
  let R:=reflectPolynomial P
  have dR:R.natDegree≤P.natDegree:=reflectPolynomial_degree P
  have ug:=treeSpace_mul hu (evalNodes_mem_treeSpace A R dR)
  have z:=mem_annih.mp (backSeed1_annih ho (by omega:m+P.natDegree+2≤p)) _ ug
  rw [row_apply] at z ⊢
  convert z using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedEval_apply,Pi.mul_apply,evalNodes_apply]
  have e:R.eval (nodes A i)=P.eval (mirror A i):=by simp [R,reflectPolynomial,mirror,eval_comp]
  rw [e]
  ring

omit [CharZero K] in
theorem linear_seed_mass (ho:HasTreeOrderAtLeast A b p) (P:K[X]) (pay:P.natDegree+2≤p) :
    (∑i,weightedEval (mirror A) (backSeed1 A b) P i)=0:=by
  have z:=mem_annih.mp (linear_seed_annih (m:=0) ho P (by omega)) (1:Vec K s)
    (stageWeight_mem_space A .leaf (by decide))
  simpa only [row_apply,Pi.one_apply,mul_one] using z

structure BroadLinearCover (A:Fin s→Fin s→K) (b:Vec K s) (m h:ℕ) : Prop where
  sites:h+1<(headSites (mirror A) (backSeed1 A b)).card
  cover:∀u∈annih (treeSpace A m),∃P:K[X],P.natDegree≤h ∧ weightedEval (mirror A) (backSeed1 A b) P=u

omit [CharZero K] in
theorem broad_linear_cover_of_orbit (h0:0<h+1)
    (sites:h+1<(headSites (mirror A) (backSeed1 A b)).card)
    (orb:annih (treeSpace A m)=orbitBand (mirror A) (backSeed1 A b) (h+1)) :
    BroadLinearCover A b m h:=by
  let : DecidableEq K:=Classical.decEq K
  refine ⟨sites,?_⟩
  intro u hu
  rw [orb] at hu
  obtain ⟨a,eq⟩:=hu
  let P:K[X]:=ofFn (h+1) a
  exact ⟨P,by have t:=ofFn_natDegree_lt h0 a;change P.natDegree<h+1 at t;omega,
    by rwa [LinearMap.comp_apply] at eq⟩

omit [CharZero K] in
theorem BroadLinearCover.support (B:BroadLinearCover A b m h)
    {u:Vec K s} (uM:u∈annih (treeSpace A m)) {i:Fin s} (di:backSeed1 A b i=0) : u i=0:=by
  obtain ⟨P,_,e⟩:=B.cover _ uM
  rw [←e,weightedEval_apply,di,mul_zero]

def LinearFits (A:Fin s→Fin s→K) (b f:Vec K s) (Q P:K[X]) : Prop:=
    (∀i,backSeed1 A b i*f i=Q.eval (mirror A i)*backSeed1 A b i) ∧
    (∀i,b i*f i=P.eval (mirror A i)*backSeed1 A b i)

omit [CharZero K] in
theorem broad_linear_two_traces (ho:HasTreeOrderAtLeast A b p)
    (B:BroadLinearCover A b m h) (hf:f∈zeroSpace A j)
    (one:1≤j)(pay:m+h+2≤p)(hj:j≤h):
    ∃Q P:K[X],Q.natDegree≤j ∧ P.natDegree≤j-1 ∧ LinearFits A b f Q P:=by
  let y:=mirror A
  let d:=backSeed1 A b
  have seed(a:ℕ)(ap:a≤h-j):
      (fun i=>y i^a*(d i*f i))∈annih (treeSpace A m):=by
    apply mem_annih.mpr
    intro v hv
    let H:K[X]:=X^a
    have hd:H.natDegree=a:=natDegree_X_pow a
    have E:=treeSpace_mul hv (zeroSpace_le_treeSpace A j hf)
    have z:=mem_annih.mp (linear_seed_annih (m:=m+j) ho H (by omega)) _ E
    rw [row_apply] at z ⊢
    convert z using 1
    apply Finset.sum_congr rfl
    intro i _
    simp [H,y,d]
    ring
  have weight(a:ℕ)(ap:a≤h+1-j):
      (fun i=>y i^a*(b i*f i))∈annih (treeSpace A m):=by
    apply mem_annih.mpr
    intro v hv
    have Z := zeroSpace_mul_treeSpace ho (by omega:a+1≤p)
      (zeroSpace_mul_treeSpace ho (by omega:m+1≤p) hf hv)
      (mirror_power_tree (A:=A) (k:=a))
    have e:=probe_zeroSpace ho (k:=0) (by omega:0+(j+m+a)+1≤p) Z
    change probe A b 0 _=0 at e
    have EE:row b (f*v*(fun i=>y i^a))=0:=by simpa only [probe,pow_zero,mul_one] using e
    rw [row_apply] at EE ⊢
    convert EE using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.mul_apply]
    ring
  obtain ⟨Q,dQ,q⟩:=trace_degree_from_shifts B.sites
    (k:=h-j) (v:=fun i=>d i*f i) (fun a ha=>B.cover _ (seed a ha))
  obtain ⟨P,dP,r⟩:=trace_degree_from_shifts B.sites
    (k:=h+1-j) (v:=fun i=>b i*f i) (fun a ha=>B.cover _ (weight a ha))
  refine ⟨Q,P,?_,?_,fun i=>?_,fun i=>?_⟩
  · rcases dQ with e|e
    · simp [e]
    · -- Use the actual witness promised through the largest seed shift.
      omega
  · rcases dP with e|e
    · simp [e]
    · omega
  · simpa only [weightedEval_apply] using (congrFun q i).symm
  · simpa only [weightedEval_apply] using (congrFun r i).symm

def linearContrast (A:Fin s→Fin s→K) (b:Vec K s) (Q P:K[X]):Vec K s:=
  weightedEval (mirror A) b Q-weightedEval (mirror A) (backSeed1 A b) P

omit [CharZero K] in
theorem linear_contrast_filter (Q P R:K[X]):
    weightedEval (mirror A) (linearContrast A b Q P) R=
      weightedEval (mirror A) b (R*Q)-weightedEval (mirror A) (backSeed1 A b) (R*P):=by
  ext i
  simp only [linearContrast,weightedEval_apply,Pi.sub_apply,eval_mul]
  ring

omit [CharZero K] in
theorem LinearFits.contrast_support {Q P:K[X]} (fit:LinearFits A b f Q P)
    {i:Fin s}(wi:linearContrast A b Q P i≠0):
    backSeed1 A b i=0 ∧ b i≠0 ∧ Q.eval (mirror A i)≠0 ∧ f i=0:=by
  have d0:backSeed1 A b i=0:=by
    by_contra d
    have fQ:f i=Q.eval (mirror A i):=by
      apply mul_left_cancel₀ d
      simpa only [mul_comm (backSeed1 A b i) (Q.eval _)] using fit.1 i
    have E:=fit.2 i
    rw [fQ] at E
    apply wi
    simp only [linearContrast,Pi.sub_apply,weightedEval_apply]
    linear_combination E
  have e:Q.eval (mirror A i)*b i≠0:=by
    simpa [linearContrast,d0] using wi
  have bn:b i≠0:=(mul_ne_zero_iff.mp e).2
  have z:=fit.2 i
  rw [d0,mul_zero] at z
  exact ⟨d0,bn,(mul_ne_zero_iff.mp e).1,(mul_eq_zero.mp z).resolve_left bn⟩

theorem broad_linear_port (ho:HasTreeOrderAtLeast A b p) (B:BroadLinearCover A b m h)
    (Q P R:K[X]) (qb:m+Q.natDegree+R.natDegree+2≤p)
    (pb:m+P.natDegree+R.natDegree+3≤p)
    {i:Fin s}(off:backSeed1 A b i=0) :
    transMat A (weightedEval (mirror A) (linearContrast A b Q P) R) i=
      (Paired.primitive (R*Q)).eval (mirror A i)*b i:=by
  let y:=mirror A
  let d:=backSeed1 A b
  let S:=R*Q
  let T:=R*P
  have degS:S.natDegree≤R.natDegree+Q.natDegree:=natDegree_mul_le
  have degT:T.natDegree≤R.natDegree+P.natDegree:=natDegree_mul_le
  have d1:transMat A (weightedEval y b S)-weightedEval y b (formalPrimitive S)∈
      annih (treeSpace A m):=primitive_annihilator_paid ho S (by omega)
  have d2:transMat A (weightedEval y d T)∈annih (treeSpace A m):=by
    apply mem_annih.mpr
    intro v hv
    rw [row_flip_mat]
    exact mem_annih.mp (linear_seed_annih (m:=m+1) ho T (by omega)) _ (mat_treeSpace A m hv)
  have z1:=B.support d1 off
  have z2:=B.support d2 off
  rw [linear_contrast_filter,map_sub,Pi.sub_apply]
  change transMat A (weightedEval y b S) i-transMat A (weightedEval y d T) i=_
  change transMat A (weightedEval y b S) i-weightedEval y b (formalPrimitive S) i=0 at z1
  rw [z2,sub_zero,sub_eq_zero.mp z1,weightedEval_apply,formalPrimitive_eq_treePrimitive]

end
end RKCert.Paired.ReverseHull

