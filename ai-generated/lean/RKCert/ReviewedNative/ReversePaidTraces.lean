module

public import RKCert.ReviewedNative.ERK17ReverseSupport
public import RKCert.ReviewedNative.GradedProducts

@[expose] public section

/-! # Paid two-trace polynomial recovery on the original reverse support

A terminal-deleted polynomial cover controls the two genuinely paid
pointwise traces of every native defect. Affordable shifted traces
refund degree, including shifts agreeing only on the paid visible rows.
No order bound for a reversed tableau is assumed. -/
namespace RKResearch.Certified.Graded.Reverse.Thin
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix

noncomputable section
variable {K : Type*} [Field K] {s p m j h : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b f : Fin s→K}

set_option maxRecDepth 3500
set_option maxHeartbeats 900000

def SupportsComplement (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) (m : ℕ)
    (t : Fin s) : Prop :=
  ∀ w∈zeroAt (annih (treeSpace A m)) t, ∀ i, quadraticSeed A b i=0 → w i=0

theorem supportsComplement_of_cover {t : Fin s}
    (cover : ∀ v∈zeroAt (annih (treeSpace A m)) t,
      ∃ P : K[X], P.natDegree≤h ∧ weightedEval (reflectedClock A) (quadraticSeed A b) P=v) :
    SupportsComplement A b m t := by
  intro v hv i zero
  obtain ⟨P,_,rfl⟩ := cover v hv
  simp [zero]

/-- Multiplication by a genuine clock polynomial has its exact reverse
flag cost, measured on the actual quadratic seed. -/
theorem seed_eval_annih (ho : HasOrder p A b) (P : K[X])
    (pay : m+P.natDegree+3≤p) :
    weightedEval (reflectedClock A) (quadraticSeed A b) P ∈ annih (treeSpace A m) := by
  have d : quadraticSeed A b ∈ primitiveBack A b 1 :=
    adjointFlag_credit (monomialCredit A b) 0 (monomial_mem_credit 0 1 (by decide))
  have h : weightedEval (reflectedClock A) (quadraticSeed A b) P ∈
      weightedBand (reflectedClock A) (quadraticSeed A b) (P.natDegree+1) :=
    mem_weightedBand.mpr ⟨P,P.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self _),rfl⟩
  exact primitiveBack_annih ho m (1+P.natDegree) (by omega)
    (weighted_band_of_primitive_seed d _ h)

theorem seed_eval_mass (ho : HasOrder p A b) (P : K[X]) (pay : P.natDegree+3≤p) :
    (∑ i, weightedEval (reflectedClock A) (quadraticSeed A b) P i)=0 := by
  have unit : (1 : Fin s→K)∈treeSpace A 0 := by
    have z := evalNodes_mem_treeSpace A (1 : K[X]) (q:=0) (by simp)
    have e : evalNodes A (1 : K[X])=1 := by ext i; simp
    rwa [e] at z
  simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using
    mem_annih.mp (seed_eval_annih (m:=0) ho P (by omega)) _ unit

/-- Polynomial coefficient recovery applies to the entire physical head,
not just a list of selected representatives of repeated clocks. -/
theorem weightedEval_inj_below {c d:(Fin s→K)} {P Q:K[X]}
    (hp:P.degree<((weightedSites c d).card:WithBot ℕ))
    (hq:Q.degree<((weightedSites c d).card:WithBot ℕ))
    (eq:weightedEval c d P=weightedEval c d Q) : P=Q := by
  classical
  apply eq_of_degrees_lt_of_eval_finset_eq (weightedSites c d) hp hq
  intro x hx
  obtain ⟨i,hn,e⟩:=mem_weightedSites.mp hx
  have u:=congrFun eq i
  rw [weightedEval_apply,weightedEval_apply,e] at u
  exact mul_right_cancel₀ hn u

/-- A common degree budget for consecutive complete clock traces deducts
one polynomial degree for each further affordable shift. -/
theorem trace_degree_from_affine_shifts {c d v:(Fin s→K)} {h k:ℕ}
    (L:K[X]) (degL:L.natDegree=1) (big:h+1<(weightedSites c d).card) (paid:∀a≤k,
      ∃P:K[X],P.natDegree≤h ∧ weightedEval c d P=(fun i=>(L.eval (c i))^a*v i)) :
    ∃P:K[X],(P=0∨P.natDegree+k≤h) ∧ weightedEval c d P=v := by
  classical
  choose get dg eq using paid
  let Q (a:ℕ) : K[X] := if ha:a≤k then get a ha else 0
  have Qd (a:ℕ) (ha:a≤k) : (Q a).natDegree≤h := by
    simpa only [Q,dite_eq_left ha] using dg a ha
  have Qeq (a:ℕ) (ha:a≤k) : weightedEval c d (Q a)=fun i=>(L.eval (c i))^a*v i := by
    simpa only [Q,dite_eq_left ha] using eq a ha
  have next (a:ℕ) (ha:a+1≤k) : Q (a+1)=L*Q a := by
    apply weightedEval_inj_below (c:=c) (d:=d)
    · have aa:((Q (a+1)).natDegree:WithBot ℕ)≤(h:WithBot ℕ) := by exact_mod_cast Qd _ ha
      have bb:(h:WithBot ℕ)<((weightedSites c d).card:WithBot ℕ) := by
        exact_mod_cast (show h < (weightedSites c d).card by omega)
      exact (degree_le_natDegree.trans aa).trans_lt bb
    · have hx:(L*Q a).natDegree≤h+1 := by
        have z:=natDegree_mul_le (p:=L) (q:=Q a)
        rw [degL] at z
        have :=Qd a (by omega)
        omega
      have aa:((L*Q a).natDegree:WithBot ℕ)≤((h+1:ℕ):WithBot ℕ) := by exact_mod_cast hx
      exact (degree_le_natDegree.trans aa).trans_lt (by exact_mod_cast big)
    · ext i
      have e1:=congrFun (Qeq (a+1) ha) i
      have e0:=congrFun (Qeq a (by omega)) i
      simp only [weightedEval_apply,eval_mul] at e0 e1 ⊢
      rw [pow_succ',mul_assoc,←e0] at e1
      simpa only [mul_assoc] using e1
  have pow (a:ℕ) (ha:a≤k) : Q a=L^a*Q 0 := by
    induction a with
    | zero => simp
    | succ a ih => rw [next a ha,ih (by omega),pow_succ',mul_assoc]
  refine ⟨Q 0,?_,by simpa only [pow_zero,one_mul] using Qeq 0 (by omega : 0≤k)⟩
  by_cases hz:Q 0=0
  · exact Or.inl hz
  · right
    have h := Qd k le_rfl
    have L0:L≠0 := by intro eq;rw [eq,natDegree_zero] at degL;omega
    rw [pow k le_rfl,natDegree_mul (pow_ne_zero _ L0) hz,natDegree_pow,degL,mul_one] at h
    omega

theorem trace_degree_from_shifts {c d v:(Fin s→K)} {h k:ℕ}
    (big:h+1<(weightedSites c d).card) (paid:∀a≤k,
      ∃P:K[X],P.natDegree≤h ∧ weightedEval c d P=(fun i=>c i^a*v i)) :
    ∃P:K[X],(P=0∨P.natDegree+k≤h) ∧ weightedEval c d P=v :=
  trace_degree_from_affine_shifts X natDegree_X big (by simpa only [eval_X] using paid)

theorem one_sub_X_natDegree : (1-(X:K[X])).natDegree=1 := by
  rw [show (1-(X:K[X]))=-(X-C (1:K)) by simp, natDegree_neg,natDegree_X_sub_C]

theorem mirror_power_tree {k:ℕ} :
    (fun i=>reflectedClock A i^k)∈treeSpace A k := by
  have eq : (fun i=>reflectedClock A i^k)=evalNodes A ((1-X)^k) := by
    ext i
    simp [reflectedClock]
  rw [eq]
  apply evalNodes_mem_treeSpace A _
  apply natDegree_pow_le.trans
  rw [one_sub_X_natDegree,mul_one]

theorem seed_times_defect_shift (ho:HasOrder p A b) (hf:f∈zeroSpace A j)
    (k:ℕ) (pay:m+j+k+3≤p) :
    (fun i=>reflectedClock A i^k*(quadraticSeed A b i*f i))∈annih (treeSpace A m) := by
  apply mem_annih.mpr
  intro v hv
  have E:=treeSpace_mul (treeSpace_mul hv (zeroSpace_le_treeSpace A j hf))
    (mirror_power_tree (A:=A) (k:=k))
  have seed : quadraticSeed A b ∈ primitiveBack A b 1 :=
    adjointFlag_credit (monomialCredit A b) 0 (monomial_mem_credit 0 1 (by decide))
  have Z:=mem_annih.mp (primitiveBack_annih ho (m+j+k) 1 (by omega) seed) _ E
  rw [row_apply,dotProduct] at Z ⊢
  convert Z using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply]
  ring

theorem weight_times_defect_shift (ho:HasOrder p A b) (hf:f∈zeroSpace A j)
    (k:ℕ) (pay:m+j+k+2≤p) :
    (fun i=>reflectedClock A i^k*(reflectedClock A i*b i*f i))∈annih (treeSpace A m) := by
  apply mem_annih.mpr
  intro v hv
  have Z := zeroSpace_mul_treeSpace ho (by omega : k+1+1≤p)
    (zeroSpace_mul_treeSpace ho (by omega : m+1≤p) hf hv)
    (mirror_power_tree (A:=A) (k:=k+1))
  have e:=probe_zeroSpace ho (k:=0) (by omega : 0+(j+m+(k+1))+1≤p) Z
  change probe A b 0 _=0 at e
  have ee : row b (f*v*(fun i=>reflectedClock A i^(k+1)))=0 := by simpa only [probe,pow_zero,mul_one] using e
  rw [row_apply,dotProduct] at ee ⊢
  convert ee using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply,pow_succ]
  ring

/-- If the actual complementary flag has a one-head degree-h cover, its
two pointwise traces have respective degree caps j and j-1.  Take (m,h)=(8,7)
for the order-18 thin nine-flag and (9,8) at order 20. -/
theorem thin_reverse_two_traces (ho:HasOrder p A b) (hf:f∈zeroSpace A j)
    (one:1≤j) (jh:j≤h) (pay:m+h+3≤p)
    (t:Fin s) (y0:reflectedClock A t=0) (d0:quadraticSeed A b t=0)
    (big:h+1<(weightedSites (reflectedClock A) (quadraticSeed A b)).card)
    (cover:∀v∈zeroAt (annih (treeSpace A m)) t,
      ∃P:K[X],P.natDegree≤h ∧ weightedEval (reflectedClock A) (quadraticSeed A b) P=v) :
    ∃Q P:K[X],Q.natDegree≤j ∧ P.natDegree≤j-1 ∧
      (∀i,quadraticSeed A b i*f i=Q.eval (reflectedClock A i)*quadraticSeed A b i) ∧
      (∀i,reflectedClock A i*b i*f i=P.eval (reflectedClock A i)*quadraticSeed A b i) := by
  obtain ⟨Q,qd,qe⟩:=trace_degree_from_shifts (h:=h) (k:=h-j) big
    (v:=fun i=>quadraticSeed A b i*f i) (fun a ha=>cover _ (mem_zeroAt.mpr ⟨
      seed_times_defect_shift ho hf a (by omega),by
        simp [d0]⟩))
  obtain ⟨P,pd,pe⟩:=trace_degree_from_shifts (h:=h) (k:=h+1-j) big
    (v:=fun i=>reflectedClock A i*b i*f i) (fun a ha=>cover _ (mem_zeroAt.mpr ⟨
      weight_times_defect_shift ho hf a (by omega),by
        simp [y0]⟩))
  refine ⟨Q,P,?_,?_,fun i=>?_,fun i=>?_⟩
  · rcases qd with e|bound
    · simp [e]
    · omega
  · rcases pd with e|bound
    · simp [e]
    · omega
  · simpa only [weightedEval_apply] using (congrFun qe i).symm
  · simpa only [weightedEval_apply] using (congrFun pe i).symm

/-- The same-grade shifts need agree only on the two actually visible
backward supports. They may differ arbitrarily at hidden physical rows. -/
theorem thin_reverse_traces_same_grade_drop (ho:HasOrder p A b)
    (one:1≤j) (jh:j≤h) (pay:m+h+3≤p)
    (t:Fin s) (y0:reflectedClock A t=0) (d0:quadraticSeed A b t=0)
    (big:h+1<(weightedSites (reflectedClock A) (quadraticSeed A b)).card)
    (cover:∀v∈zeroAt (annih (treeSpace A m)) t,
      ∃P:K[X],P.natDegree≤h ∧ weightedEval (reflectedClock A) (quadraticSeed A b) P=v)
    {k:ℕ} (family:ℕ→(Fin s→K)) (graded:∀a≤k,family a∈zeroSpace A j)
    (agree:∀a≤k,∀i,quadraticSeed A b i≠0∨reflectedClock A i*b i≠0→
      family a i=nodes A i^a*f i) :
    ∃Q P:K[X],Q.natDegree≤j-k ∧ P.natDegree≤j-1-k ∧
      (∀i,quadraticSeed A b i*f i=Q.eval (reflectedClock A i)*quadraticSeed A b i) ∧
      (∀i,reflectedClock A i*b i*f i=P.eval (reflectedClock A i)*quadraticSeed A b i) := by
  let c:=reflectedClock A
  let d:=quadraticSeed A b
  let L:K[X]:=1-X
  have Le (i:Fin s) : L.eval (c i)=nodes A i := by
    simp [L,c,reflectedClock]
  have big' : h+1<(weightedSites c d).card := big
  have bQ : j+1<(weightedSites c d).card := by omega
  have bP : j-1+1<(weightedSites c d).card := by omega
  have tr (a:ℕ) (ha:a≤k) :=
    thin_reverse_two_traces ho (graded a ha) one jh pay t y0 d0 big cover
  obtain ⟨Q,qd,qe⟩:=trace_degree_from_affine_shifts L one_sub_X_natDegree bQ
    (k:=k) (v:=fun i=>d i*f i) (by
      intro a ha
      obtain ⟨Q,P,dQ,dP,eQ,eP⟩:=tr a ha
      refine ⟨Q,dQ,?_⟩
      ext i
      rw [weightedEval_apply,←eQ i,Le]
      by_cases hd:d i=0
      · simp [d,show quadraticSeed A b i=0 from hd]
      · rw [agree a ha i (Or.inl hd)]
        change d i*(nodes A i^a*f i)=_
        ring)
  obtain ⟨P,pd,pe⟩:=trace_degree_from_affine_shifts L one_sub_X_natDegree bP
    (k:=k) (v:=fun i=>c i*b i*f i) (by
      intro a ha
      obtain ⟨Q,P,dQ,dP,eQ,eP⟩:=tr a ha
      refine ⟨P,dP,?_⟩
      ext i
      rw [weightedEval_apply,←eP i,Le]
      by_cases hy:c i*b i=0
      · change (c i*b i)*family a i=nodes A i^a*((c i*b i)*f i)
        simp [hy]
      · rw [agree a ha i (Or.inr hy)]
        change (c i*b i)*(nodes A i^a*f i)=_
        ring)
  refine ⟨Q,P,?_,?_,fun i=>?_,fun i=>?_⟩
  · rcases qd with z|le
    · simp [z]
    · omega
  · rcases pd with z|le
    · simp [z]
    · omega
  · simpa only [weightedEval_apply] using (congrFun qe i).symm
  · simpa only [weightedEval_apply] using (congrFun pe i).symm

end
end RKResearch.Certified.Graded.Reverse.Thin
