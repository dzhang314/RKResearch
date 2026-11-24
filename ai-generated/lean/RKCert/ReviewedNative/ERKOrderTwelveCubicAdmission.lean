module

public import RKCert.ReviewedNative.ERKOrderTwelveCubicProfile
public import RKCert.OrderTwelveGhost

public section

/-! # Every genuine cubic defect is inside the order-12 clock core

Two observed chronological first failures give different nonzero eligible
physical clocks. The actual primitive tests and their one legal leakage
scalar then instantiate the existing tree-free five-row scalar certificate.
-/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Polynomial Module Reverse RKCert.OneEscape RKCert.Endpoint
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

omit [CharZero K] in
/-- Weighting a defect column by the actual degree-n clock costs n. -/
theorem weighted_clock_mem_grade (ho : HasOrder A b 12)
    {v : Fin (s+1) → K} {m n : ℕ} (hv : v∈zeroSpace A m) (pay : n+1≤12)
    (R : K[X]) (deg : R.natDegree≤n) :
    weightedEval (nodes A) v R∈zeroSpace A (m+n) := by
  have e : weightedEval (nodes A) v R=v*evalNodes A R := by ext i; simp [mul_comm]
  rw [e]
  exact zeroSpace_mul_treeSpace ho pay hv (evalNodes_mem_treeSpace A R deg)

/-- Linear primitive contrast for the actual tableau and multiplier. -/
@[expose] noncomputable def multiplierPrimitiveResidual (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (v : Fin (s+1) → K) (P : K[X]) : K[X] →ₗ[K] (Fin (s+1) → K) :=
  let F : K[X] →ₗ[K] K[X] :=
    { toFun := fun R => R*P
      map_add' := fun R S => add_mul R S P
      map_smul' := fun a R => smul_mul_assoc a R P }
  (evalNodes A).comp (primitive.comp F) -
    (mat A).comp ((evalNodes A).comp F-weightedEval (nodes A) v)

omit [CharZero K] in
theorem multiplierPrimitiveResidual_apply (v : Fin (s+1) → K) (P R : K[X]) :
    multiplierPrimitiveResidual A v P R =
      evalNodes A (primitive (R*P))-mat A (evalNodes A (R*P)-weightedEval (nodes A) v R) := rfl

private theorem residual_grade (v : Fin (s+1) → K) (P R : K[X]) {n : ℕ}
    (prod : (R*P).natDegree≤n) (pay : weightedEval (nodes A) v R∈zeroSpace A n) :
    multiplierPrimitiveResidual A v P R∈zeroSpace A (n+1) := by
  rw [multiplierPrimitiveResidual_apply,map_sub]
  have eq : evalNodes A (primitive (R*P))-
      (mat A (evalNodes A (R*P))-mat A (weightedEval (nodes A) v R)) =
      -(mat A (evalNodes A (R*P))-evalNodes A (primitive (R*P)))+
        mat A (weightedEval (nodes A) v R) := by abel
  rw [eq]
  exact (zeroSpace A (n+1)).add_mem ((zeroSpace A (n+1)).neg_mem (primitive_defect A _ prod))
    (mat_zeroSpace_charZero A n pay)

/-- Only the cubic part of the tested polynomial can leak, and the
same scalar is used for all tests and both detected physical clocks. -/
theorem cubic_residual_single_leak (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b 12) (T : TerminalBand A b) {v : Fin (s+1) → K} {P : K[X]}
    (dP : P.natDegree≤3)
    (cheap : ∀ R : K[X], R.natDegree≤2 → weightedEval (nodes A) v R∈zeroSpace A 5)
    (high : weightedEval (nodes A) v (X^3)∈zeroSpace A 6) :
    ∃ α : K, ∀ R : K[X], R.natDegree≤3 →
      multiplierPrimitiveResidual A v P R-(α*R.coeff 3) • evalNodes A terminalLeak7∈escape7 A := by
  let F := multiplierPrimitiveResidual A v P
  have residual : F (X^3)∈zeroSpace A 7 :=
    residual_grade v P (X^3) (natDegree_mul_le.trans (by rw [natDegree_X_pow];omega)) high
  obtain ⟨α,leak⟩ := grade_seven_single_leak ha ho T residual
  refine ⟨α,fun R dR => ?_⟩
  let a := R.coeff 3
  let L := R-a • X^3
  have deg : L.natDegree≤2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    simp only [L,coeff_sub,Polynomial.smul_eq_C_mul,Polynomial.coeff_C_mul,coeff_X_pow]
    by_cases h : n=3
    · subst n
      simp [a]
    · have pz : R.coeff n=0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [pz,h]
  have low : F L∈zeroSpace A 6 :=
    residual_grade v P L (natDegree_mul_le.trans (by omega)) (cheap L deg)
  have all : F L+a • (F (X^3)-α • evalNodes A terminalLeak7)∈escape7 A :=
    (escape7 A).add_mem ((show zeroSpace A 6≤escape7 A from le_sup_left) low)
      ((escape7 A).smul_mem a leak)
  have e : F L+a • (F (X^3)-α • evalNodes A terminalLeak7) =
      F R-(α*a) • evalNodes A terminalLeak7 := by
    simp only [L,map_sub,map_smul,smul_sub,smul_smul,mul_comm a α]
    abel
  exact e ▸ all

omit [CharZero K] in
private theorem mesh_eligible {x : K} (nx : x≠0)
    (h : x=1 ∨ (terminalMesh6 : K[X]).eval x=0) :
    RKCert.OrderTwelve.endpoint x=0 := by
  rcases h with rfl|h
  · simp [RKCert.OrderTwelve.endpoint]
  · rw [terminalMesh6_value] at h
    unfold RKCert.OrderTwelve.endpoint
    change (x-1)*(132*x^5-330*x^4+300*x^3-120*x^2+20*x-1)=0
    rw [(mul_eq_zero.mp h).resolve_left nx,mul_zero]

/-- At the first actual joint-prefix mismatch, each paid primitive
contrast gives its scalar test. The row is physically terminal or its
clock is a zero of the actual mesh. -/
theorem cubic_chronological_tests (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b 12) (S : Saturation A b)
    {r : ℕ} {U : Submodule K (Fin (s+1) → K)} {w v : Fin (s+1) → K}
    (H : ForwardStaircase A r U w) (stable : U.map (diag v)≤U)
    {P Q : K[X]} (p0 : P≠0) (q0 : Q≠0) (dP : P.natDegree≤3) (dQ : Q.natDegree≤2)
    (pay : weightedEval (nodes A) v Q∈zeroSpace A 5)
    (fit : v*w-weightedEval (nodes A) w P∈U) (α : K)
    (leak : ∀ R : K[X], R.natDegree≤3 →
      multiplierPrimitiveResidual A v P R-(α*R.coeff 3) • evalNodes A terminalLeak7∈escape7 A) :
    ∃ k : Fin (s+1), Q.eval (nodes A k)≠0 ∧
      (nodes A k=1 ∨ (terminalMesh6 : K[X]).eval (nodes A k)=0) ∧
      ∀ R : K[X], (R*Q).natDegree≤3 →
        (primitive ((R*Q)*P)).eval (nodes A k) =
          (α*(R*Q).coeff 3)*(terminalLeak7 : K[X]).eval (nodes A k) := by
  classical
  let c := nodes A
  let z := evalNodes A (Q*P)-weightedEval c v Q
  have val (i : Fin (s+1)) : z i=Q.eval (c i)*(P.eval (c i)-v i) := by
    simp [z,c,mul_sub]
  have z0 : z∉U := by
    intro hz
    have sep : PolySeparated A 6 := PolySeparated.of_coeff
      (explicit_coeff_separated ha ho (q:=6) (by decide))
    change weightedEval c v Q∈zeroSpace A 5 at pay
    have mem := (zeroSpace A 6).add_mem
      (zeroSpace_mono A (by decide : 5≤6) (H.initial.coreInside hz))
      (zeroSpace_mono A (by decide : 5≤6) pay)
    exact (mul_ne_zero q0 p0) (sep _ (natDegree_mul_le.trans (by omega))
      (by simpa only [z,sub_add_cancel] using mem))
  have cmask : MaskInvariant c U :=
    clock_mask_invariant (fun u hu => H.initial.coreStable (Submodule.mem_map_of_mem hu))
  have vmask : MaskInvariant v U :=
    clock_mask_invariant (fun u hu => stable (Submodule.mem_map_of_mem hu))
  obtain ⟨k,g,gu,before,live,detect⟩ :=
    HeadFiber.joint_prefix_detector cmask vmask P Q fit val z0
  refine ⟨k,live,?_,?_⟩
  · by_cases last : k=Fin.last s
    · exact Or.inl (last ▸ S.terminalClock)
    right
    let f := coordinate (K:=K) (Fin.last s)-evalNodes A terminalMesh6
    have f7 : f∈escape7 A :=
      (show zeroSpace A 6≤escape7 A from le_sup_left) (physical_terminal_mesh ha ho S)
    have fhead : f∈chain (diag c) U w (r+2) := H.cut ▸ f7
    apply neg_eq_zero.mp (detect fhead (-(terminalMesh6 : K[X]).eval (c k)) ?_)
    intro i hi same _
    have ne : i≠Fin.last s := by
      intro it
      have lt : k.val<s := by
        have kn : k.val≠s := fun e => last (Fin.ext e)
        have ks := k.isLt
        omega
      subst i
      change s < k.val+1 at hi
      omega
    have zf : coordinate (K:=K) (Fin.last s) i=0 := by simp [coordinate,ne]
    change coordinate (K:=K) (Fin.last s) i-(terminalMesh6 : K[X]).eval (c i)=_
    rw [zf,zero_sub,same]
  · intro R dr
    let L := R*Q
    let B := L*P
    let a := α*L.coeff 3
    let G := weightedEval c g R
    let Y := multiplierPrimitiveResidual A v P L+mat A G-a • evalNodes A terminalLeak7
    have gcore : G∈U := by
      have e : G=fun i => R.eval (c i)*g i := by ext i; simp [G]
      rw [e]
      exact mulByBlock_mem c cmask (fun x=>R.eval x) gu
    have hg6 : mat A G∈zeroSpace A 6 := mat_zeroSpace_charZero A 5 (H.initial.coreInside gcore)
    have y : Y∈escape7 A := by
      have h := (escape7 A).add_mem (leak L dr)
        ((show zeroSpace A 6≤escape7 A from le_sup_left) hg6)
      simpa only [Y,a,sub_add_eq_add_sub] using h
    have yhead : Y∈chain (diag c) U w (r+2) := H.cut ▸ y
    have res : (primitive B).eval (c k)-a*(terminalLeak7 : K[X]).eval (c k)=0 := by
      apply detect yhead _
      intro i hi same _
      have e : mat A (evalNodes A B-weightedEval c v L) i=mat A G i := by
        have h := causal_mat ha i ((evalNodes A B-weightedEval c v L)-G) (by
          intro l hl
          change l.val < i.val at hl
          have lk : l<k := by change l.val<k.val; omega
          simp only [Pi.sub_apply,evalNodes_apply,weightedEval_apply,G,before l lk,val,B,L,eval_mul]
          ring)
        simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using h
      rw [show Y=multiplierPrimitiveResidual A v P L+mat A G-a • evalNodes A terminalLeak7 from rfl,
        Pi.sub_apply,Pi.add_apply,multiplierPrimitiveResidual_apply,Pi.sub_apply]
      change (primitive B).eval (c i)-mat A (evalNodes A B-weightedEval c v L) i+
        mat A G i-a*(terminalLeak7 : K[X]).eval (c i)=_
      rw [e,sub_add_cancel,same]
    exact sub_eq_zero.mp res

/-- A paid cubic multiplier profile is impossible once its two actual
chronological rows supply the previously certified scalar tests. This
uses paid weighted columns, not a grade assignment for the multiplier. -/
theorem exclude_paid_cubic_profile (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder A b 12)
    (S : Saturation A b) (T : TerminalBand A b)
    {r : ℕ} {U : Submodule K (Fin (s+1) → K)} {w v : Fin (s+1) → K}
    (H : ForwardStaircase A r U w) (stable : U.map (diag v)≤U)
    {P : K[X]} (p0 : P≠0) (dP : P.natDegree≤3)
    (fit : v*w-weightedEval (nodes A) w P∈U)
    (cheap : ∀ R : K[X], R.natDegree≤2 → weightedEval (nodes A) v R∈zeroSpace A 5)
    (high : weightedEval (nodes A) v (X^3)∈zeroSpace A 6) : False := by
  classical
  obtain ⟨α,leak⟩ := cubic_residual_single_leak ha ho T dP cheap high
  have detect (Q : K[X]) (q0 : Q≠0) (dQ : Q.natDegree≤2) :=
    cubic_chronological_tests ha ho S H stable p0 q0 dP dQ (cheap Q dQ) fit α leak
  obtain ⟨i,live,mi,ai⟩ := detect X X_ne_zero (by simp)
  let u := nodes A i
  have nu : u≠0 := by simpa only [eval_X] using live
  let Q : K[X] := X*(X-C u)
  have q0 : Q≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero _)
  have dq : Q.natDegree=2 := by
    unfold Q
    rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero _),natDegree_X,natDegree_X_sub_C]
  obtain ⟨j,live',mj,aj⟩ := detect Q q0 dq.le
  let x := nodes A j
  have xne : x≠0 ∧ x≠u := by
    change Q.eval x≠0 at live'
    have e : x*(x-u)≠0 := by simpa [Q] using live'
    simpa only [mul_ne_zero_iff,sub_ne_zero] using e
  let a : Fin 4 → K := fun j => P.coeff j.val
  have rep : ofFn 4 a=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have value (z : K) (k : ℕ) :
      (primitive (X^k*P)).eval z=RKCert.OrderTwelve.cubicMoment z k a := by
    rw [←rep,HeadContrast.primitive_monomial_moment]
    rfl
  change ∀ R : K[X], (R*X).natDegree≤3 →
    (primitive ((R*X)*P)).eval u= (α*(R*X).coeff 3)*(terminalLeak7 : K[X]).eval u at ai
  change ∀ R : K[X], (R*Q).natDegree≤3 →
    (primitive ((R*Q)*P)).eval x= (α*(R*Q).coeff 3)*(terminalLeak7 : K[X]).eval x at aj
  have h1 := ai (1:K[X]) (by simp)
  have h2 := ai X (by rw [←pow_two,natDegree_X_pow];decide)
  have h3 := ai (X^2) (by rw [←pow_succ,natDegree_X_pow])
  have E1 : RKCert.OrderTwelve.cubicMoment u 1 a=0 := by
    rw [one_mul] at h1
    have e := value u 1
    rw [pow_one] at e
    have z : (X:K[X]).coeff 3=0 := coeff_eq_zero_of_natDegree_lt (by rw [natDegree_X];decide)
    rwa [e,z,mul_zero,zero_mul] at h1
  have E2 : RKCert.OrderTwelve.cubicMoment u 2 a=0 := by
    rw [←pow_two,value,coeff_X_pow] at h2
    simpa using h2
  have ghost (z : K) : (terminalLeak7 : K[X]).eval z=RKCert.OrderTwelve.leakSeven z :=
    terminalLeak7_value z
  have E3 : RKCert.OrderTwelve.cubicMoment u 3 a+(-α)*RKCert.OrderTwelve.leakSeven u=0 := by
    rw [←pow_succ,value,coeff_X_pow,ite_eq_left rfl,mul_one,ghost] at h3
    linear_combination h3
  have qr : (1:K[X])*Q=X^2-u • X := by
    rw [one_mul,Polynomial.smul_eq_C_mul]
    dsimp [Q]
    ring
  have sqr : X*Q=X^3-u • X^2 := by
    rw [Polynomial.smul_eq_C_mul]
    dsimp [Q]
    ring
  have h4 := aj (1:K[X]) (by rw [one_mul,dq];decide)
  have h5 := aj X (natDegree_mul_le.trans (by rw [natDegree_X,dq]))
  have E4 : RKCert.OrderTwelve.cubicMoment x 2 a-u*RKCert.OrderTwelve.cubicMoment x 1 a=0 := by
    have cf : ((1:K[X])*Q).coeff 3=0 := coeff_eq_zero_of_natDegree_lt
      (by rw [one_mul,dq];decide)
    rw [cf,mul_zero,zero_mul,qr,sub_mul,smul_mul_assoc,map_sub,map_smul,eval_sub,eval_smul,value,
      ←pow_one (X:K[X]),value,smul_eq_mul] at h4
    exact h4
  have E5 : RKCert.OrderTwelve.cubicMoment x 3 a-u*RKCert.OrderTwelve.cubicMoment x 2 a+
      (-α)*RKCert.OrderTwelve.leakSeven x=0 := by
    have cf : (X*Q).coeff 3=1 := by
      rw [sqr,coeff_sub,Polynomial.smul_eq_C_mul,Polynomial.coeff_C_mul,coeff_X_pow,coeff_X_pow]
      norm_num
    rw [cf,mul_one,ghost,sqr,sub_mul,smul_mul_assoc,map_sub,map_smul,eval_sub,eval_smul,value,value,
      smul_eq_mul] at h5
    linear_combination h5
  have z := (RKCert.OrderTwelve.ghost_five_tests_zero u x
    (mesh_eligible nu mi) (mesh_eligible xne.1 mj) xne.2 a (-α) E1 E2 E3 E4 E5).1
  exact p0 (by rw [←rep,z,map_zero])

/-- Admission of the actual cubic defect grade has no hypothesis on the
head length or the dimension of grade four beyond the measured staircase. -/
theorem grade_three_in_core (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder A b 12)
    (S : Saturation A b) (T : TerminalBand A b)
    {r : ℕ} {U : Submodule K (Fin (s+1) → K)} {w : Fin (s+1) → K}
    (H : ForwardStaircase A r U w) : zeroSpace A 3≤U := by
  intro v hv
  by_contra out
  have stable := grade_three_multiplier_stable ha ho S T H hv
  obtain ⟨P,p0,dP,fit⟩ := grade_three_multiplier_profile ha ho S T H hv out
  exact exclude_paid_cubic_profile ha ho S T H stable p0 dP fit
    (fun R dR => weighted_clock_mem_grade ho hv (n:=2) (by decide) R dR)
    (weighted_clock_mem_grade ho hv (n:=3) (by decide) _ (by rw [natDegree_X_pow]))

end RKResearch.Certified.Graded.ERK12

