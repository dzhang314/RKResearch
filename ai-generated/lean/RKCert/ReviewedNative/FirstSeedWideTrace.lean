module

public import RKCert.ReviewedNative.ReversePaidTraces

@[expose] public section

/-! # Paid polynomial traces on the full, nonzero first-seed cover

The generic geometry uses ordinary native product order and the full
reverse annihilator. The nonzero-first-seed case does not mark or remove
the last coordinate and does not use a reversed method's order. -/
namespace RKResearch.Certified.Graded.Reverse.FirstWide
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] {s p m h j : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b f : Fin s→K}

set_option maxRecDepth 3500
set_option maxHeartbeats 750000

/-- Full actual homogeneous complement with a finite first-seed
polynomial band and at least one unused numerical site. -/
structure Cover (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) (m h : ℕ) : Prop where
  sites : h+1<(weightedSites (reflectedClock A) (firstSeed A b)).card
  represent : ∀ v∈annih (treeSpace A m), ∃ P : K[X], P.natDegree≤h ∧
    weightedEval (reflectedClock A) (firstSeed A b) P=v

theorem Cover.of_band
    (big : h+1<(weightedSites (reflectedClock A) (firstSeed A b)).card)
    (eq : annih (treeSpace A m)=weightedBand (reflectedClock A) (firstSeed A b) (h+1)) :
    Cover A b m h := by
  refine ⟨big,fun v hv => ?_⟩
  rw [eq] at hv
  obtain ⟨P,d,e⟩ := mem_weightedBand.mp hv
  refine ⟨P,?_,e⟩
  by_cases z : P=0
  · simp [z]
  · have lo := (natDegree_lt_iff_degree_lt z).mpr d
    omega

theorem Cover.support (B : Cover A b m h) {v : Fin s→K}
    (hv : v∈annih (treeSpace A m)) {i : Fin s} (off : firstSeed A b i=0) : v i=0 := by
  obtain ⟨P,_,e⟩ := B.represent v hv
  rw [←e,weightedEval_apply,off,mul_zero]

theorem seed_eval_annih (ho : HasOrder p A b) (P : K[X])
    (pay : m+P.natDegree+2≤p) :
    weightedEval (reflectedClock A) (firstSeed A b) P∈annih (treeSpace A m) := by
  have seed : firstSeed A b∈primitiveBack A b 0 := Submodule.mem_span_singleton_self _
  have row : weightedEval (reflectedClock A) (firstSeed A b) P∈
      weightedBand (reflectedClock A) (firstSeed A b) (P.natDegree+1) :=
    mem_weightedBand.mpr ⟨P,P.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self _),rfl⟩
  have v := weighted_band_of_primitive_seed seed P.natDegree row
  exact primitiveBack_annih ho m P.natDegree pay (by simpa only [zero_add] using v)

theorem seed_eval_mass (ho : HasOrder p A b) (P : K[X]) (pay : P.natDegree+2≤p) :
    (∑ i,weightedEval (reflectedClock A) (firstSeed A b) P i)=0 := by
  have unit : (1:Fin s→K)∈treeSpace A 0 := by
    have z := evalNodes_mem_treeSpace A (1:K[X]) (q:=0) (by simp)
    have e : evalNodes A (1:K[X])=1 := by ext i; simp
    rwa [e] at z
  simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using
    mem_annih.mp (seed_eval_annih (m:=0) ho P (by omega)) _ unit

theorem seed_times_tree_annih (ho : HasOrder p A b) {q : ℕ}
    (pay : j+q+2≤p) {v : Fin s→K} (hv : v∈treeSpace A j) :
    firstSeed A b*v∈annih (treeSpace A q) := by
  refine mem_annih.mpr fun w hw => ?_
  have s : firstSeed A b∈primitiveBack A b 0 := Submodule.mem_span_singleton_self _
  have a := mem_annih.mp (primitiveBack_annih ho (j+q) 0 (by omega) s) _ (treeSpace_mul hv hw)
  simpa only [row_apply,dotProduct,Pi.mul_apply,mul_assoc] using a

theorem weight_times_defect_annih (ho : HasOrder p A b) {q : ℕ}
    (pay : j+q+1≤p) {v : Fin s→K} (hv : v∈zeroSpace A j) :
    b*v∈annih (treeSpace A q) := by
  refine mem_annih.mpr fun w hw => ?_
  have a := probe_zeroSpace (k:=0) ho (by omega) (zeroSpace_mul_treeSpace ho (by omega) hv hw)
  have e : probe A b 0 (v*w)=0 := a
  simpa only [probe,row_apply,dotProduct,Pi.mul_apply,pow_zero,mul_one,mul_assoc] using e

def LinearFits (A:Matrix (Fin s) (Fin s) K) (b f:(Fin s→K)) (Q P:K[X]) : Prop:=
    (∀i,firstSeed A b i*f i=Q.eval (reflectedClock A i)*firstSeed A b i) ∧
    (∀i,b i*f i=P.eval (reflectedClock A i)*firstSeed A b i)

theorem two_traces (ho:HasOrder p A b)
    (B:Cover A b m h) (hf:f∈zeroSpace A j)
    (one:1≤j)(pay:m+h+2≤p)(hj:j≤h):
    ∃Q P:K[X],Q.natDegree≤j ∧ P.natDegree≤j-1 ∧ LinearFits A b f Q P:=by
  let y:=reflectedClock A
  let d:=firstSeed A b
  have seed(a:ℕ)(ap:a≤h-j):
      (fun i=>y i^a*(d i*f i))∈annih (treeSpace A m):=by
    apply mem_annih.mpr
    intro v hv
    let H:K[X]:=X^a
    have hd:H.natDegree=a:=natDegree_X_pow a
    have E:=treeSpace_mul hv (zeroSpace_le_treeSpace A j hf)
    have z:=mem_annih.mp (seed_eval_annih (m:=m+j) ho H (by omega)) _ E
    rw [row_apply,dotProduct] at z ⊢
    convert z using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [H,y,d,weightedEval_apply,Pi.mul_apply,eval_pow,eval_X]
    ring
  have weight(a:ℕ)(ap:a≤h+1-j):
      (fun i=>y i^a*(b i*f i))∈annih (treeSpace A m):=by
    apply mem_annih.mpr
    intro v hv
    have Z := zeroSpace_mul_treeSpace ho (by omega:a+1≤p)
      (zeroSpace_mul_treeSpace ho (by omega:m+1≤p) hf hv)
      (Thin.mirror_power_tree (A:=A) (k:=a))
    have e:=probe_zeroSpace ho (k:=0) (by omega:0+(j+m+a)+1≤p) Z
    change probe A b 0 _=0 at e
    have EE:row b (f*v*(fun i=>y i^a))=0:=by simpa only [probe,pow_zero,mul_one] using e
    rw [row_apply,dotProduct] at EE ⊢
    convert EE using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.mul_apply]
    ring
  obtain ⟨Q,dQ,q⟩:=Thin.trace_degree_from_shifts B.sites
    (k:=h-j) (v:=fun i=>d i*f i) (fun a ha=>B.represent _ (seed a ha))
  obtain ⟨P,dP,r⟩:=Thin.trace_degree_from_shifts B.sites
    (k:=h+1-j) (v:=fun i=>b i*f i) (fun a ha=>B.represent _ (weight a ha))
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

/-- Same-grade powers only need to agree on the true first-seed or
output support. Hidden rows may carry arbitrary corrections. -/
theorem traces_same_grade_drop (ho : HasOrder p A b) (B : Cover A b m h)
    (one : 1≤j) (jh : j≤h) (pay : m+h+2≤p)
    {k : ℕ} (family : ℕ→Fin s→K) (graded : ∀ a≤k,family a∈zeroSpace A j)
    (agree : ∀ a≤k,∀ i,firstSeed A b i≠0∨b i≠0 →
      family a i=(nodes A i)^a*f i) :
    ∃ Q P : K[X], Q.natDegree≤j-k ∧ P.natDegree≤j-1-k ∧ LinearFits A b f Q P := by
  let y := reflectedClock A
  let d := firstSeed A b
  let L : K[X] := 1-X
  have le (i : Fin s) : L.eval (y i)=nodes A i := by simp [L,y,reflectedClock]
  have big : h+1<(weightedSites y d).card := B.sites
  have fits (a : ℕ) (ha : a≤k) := two_traces ho B (graded a ha) one pay jh
  obtain ⟨Q,qd,qe⟩ := Thin.trace_degree_from_affine_shifts (c:=y) (d:=d) L Thin.one_sub_X_natDegree
    (h:=j) (k:=k) (by omega) (v:=fun i=>d i*f i) (by
      intro a ha
      obtain ⟨Q,P,qD,pD,eQ,eP⟩ := fits a ha
      refine ⟨Q,qD,?_⟩
      ext i
      rw [weightedEval_apply,←eQ i,le]
      by_cases off : d i=0
      · simp [d,show firstSeed A b i=0 from off]
      · rw [agree a ha i (Or.inl off)]
        change d i*((nodes A i)^a*f i)=_
        ring)
  obtain ⟨P,pd,pe⟩ := Thin.trace_degree_from_affine_shifts (c:=y) (d:=d) L Thin.one_sub_X_natDegree
    (h:=j-1) (k:=k) (by omega) (v:=fun i=>b i*f i) (by
      intro a ha
      obtain ⟨Q,P,qD,pD,eQ,eP⟩ := fits a ha
      refine ⟨P,pD,?_⟩
      ext i
      rw [weightedEval_apply,←eP i,le]
      by_cases off : b i=0
      · simp [off]
      · rw [agree a ha i (Or.inr off)]
        ring)
  refine ⟨Q,P,?_,?_,fun i=>?_,fun i=>?_⟩
  · rcases qd with z|lo
    · simp [z]
    · omega
  · rcases pd with z|lo
    · simp [z]
    · omega
  · simpa only [weightedEval_apply] using (congrFun qe i).symm
  · simpa only [weightedEval_apply] using (congrFun pe i).symm

def linearContrast (A:Matrix (Fin s) (Fin s) K) (b:(Fin s→K)) (Q P:K[X]):(Fin s→K):=
  weightedEval (reflectedClock A) b Q-weightedEval (reflectedClock A) (firstSeed A b) P

theorem linear_contrast_filter (Q P R:K[X]):
    weightedEval (reflectedClock A) (linearContrast A b Q P) R=
      weightedEval (reflectedClock A) b (R*Q)-weightedEval (reflectedClock A) (firstSeed A b) (R*P):=by
  ext i
  simp only [linearContrast,weightedEval_apply,Pi.sub_apply,eval_mul]
  ring

theorem LinearFits.contrast_support {Q P:K[X]} (fit:LinearFits A b f Q P)
    {i:Fin s}(wi:linearContrast A b Q P i≠0):
    firstSeed A b i=0 ∧ b i≠0 ∧ Q.eval (reflectedClock A i)≠0 ∧ f i=0:=by
  have d0:firstSeed A b i=0:=by
    by_contra d
    have fQ:f i=Q.eval (reflectedClock A i):=by
      apply mul_left_cancel₀ d
      simpa only [mul_comm (firstSeed A b i) (Q.eval _)] using fit.1 i
    have E:=fit.2 i
    rw [fQ] at E
    apply wi
    simp only [linearContrast,Pi.sub_apply,weightedEval_apply]
    change Q.eval (reflectedClock A i)*b i-P.eval (reflectedClock A i)*firstSeed A b i=0
    linear_combination E
  have e:Q.eval (reflectedClock A i)*b i≠0:=by
    simpa [linearContrast,d0] using wi
  have bn:b i≠0:=(mul_ne_zero_iff.mp e).2
  have z:=fit.2 i
  rw [d0,mul_zero] at z
  exact ⟨d0,bn,(mul_ne_zero_iff.mp e).1,(mul_eq_zero.mp z).resolve_left bn⟩

end
end RKResearch.Certified.Graded.Reverse.FirstWide
