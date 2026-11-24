module

public import RKCert.ReviewedNative.BufferedClockLeakage
public import RKCert.ReviewedNative.ERKOrderTwelveCoreAdmission
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

public section

/-! # Actual endpoint coefficients and paid cubic clock products at order 12

The endpoint and legal leakage polynomials are identified from the native
paid row probes. The cubic multiplier then preserves the true core because
its consecutive products lie in the grade-eight terminal-zero space.
-/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Polynomial Module Reverse RKCert.OneEscape RKCert.Endpoint
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

private def meshCoeffs : Fin 7 → K := ![0,-1,20,-120,300,-330,132]
private def leakCoeffs : Fin 7 → K := ![0,-6,105,-560,1260,-1260,462]

noncomputable def terminalMesh6 : K[X] := by classical exact ofFn 7 meshCoeffs
noncomputable def terminalLeak7 : K[X] := by classical exact ofFn 7 leakCoeffs

omit [CharZero K] in
theorem terminalMesh6_degree : (terminalMesh6 : K[X]).natDegree≤6 := by
  classical
  exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)

omit [CharZero K] in
theorem terminalLeak7_degree : (terminalLeak7 : K[X]).natDegree≤6 := by
  classical
  exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)

omit [CharZero K] in
private theorem terminalMesh6_coeff (i : Fin 7) :
    (terminalMesh6 : K[X]).coeff i.val=meshCoeffs i := by
  classical
  exact ofFn_coeff_eq_val_of_lt _ i.isLt

omit [CharZero K] in
private theorem terminalLeak7_coeff (i : Fin 7) :
    (terminalLeak7 : K[X]).coeff i.val=leakCoeffs i := by
  classical
  exact ofFn_coeff_eq_val_of_lt _ i.isLt

omit [CharZero K] in
theorem terminalMesh6_value (x : K) :
    (terminalMesh6 : K[X]).eval x=x*(132*x^5-330*x^4+300*x^3-120*x^2+20*x-1) := by
  classical
  unfold terminalMesh6
  rw [ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [meshCoeffs,Fin.sum_univ_succ]
  ring

omit [CharZero K] in
theorem terminalLeak7_value (x : K) :
    (terminalLeak7 : K[X]).eval x=462*x^6-1260*x^5+1260*x^4-560*x^3+105*x^2-6*x := by
  classical
  unfold terminalLeak7
  rw [ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [leakCoeffs,Fin.sum_univ_succ]
  ring

private theorem mesh_probe (ho : HasOrder A b 12) {k : ℕ} (hk : k<6) :
    probe A b k (evalNodes A terminalMesh6)=(1:K)/42 := by
  have scalar (j : Fin 6) :
      (∑ i : Fin 7, (meshCoeffs i : K)/((j.val+i.val+1:ℕ):K))=(1:K)/42 := by
    fin_cases j <;> norm_num [meshCoeffs,Fin.sum_univ_succ]
  rw [evalNodes_eq_coeffEval A _ terminalMesh6_degree,probe_coeffEval ho (by omega)]
  simp only [terminalMesh6_coeff]
  exact scalar ⟨k,hk⟩

private theorem leak_probe (ho : HasOrder A b 12) {k : ℕ} (hk : k<5) :
    probe A b k (evalNodes A terminalLeak7)=0 := by
  have scalar (j : Fin 5) :
      (∑ i : Fin 7, (leakCoeffs i : K)/((j.val+i.val+1:ℕ):K))=0 := by
    fin_cases j <;> norm_num [leakCoeffs,Fin.sum_univ_succ]
  rw [evalNodes_eq_coeffEval A _ terminalLeak7_degree,probe_coeffEval ho (by omega)]
  simp only [terminalLeak7_coeff]
  exact scalar ⟨k,hk⟩

omit [CharZero K] in
private theorem first_clock_zero (ha : ∀ i k, i ≤ k → A i k=0) :
    nodes A 0=0 := by
  simp only [nodes,Matrix.mulVec,dotProduct]
  exact Finset.sum_eq_zero (fun i _ => by rw [ha 0 i (Fin.zero_le i),zero_mul])

/-- The real terminal unit has this exact degree-six clock representative
modulo the genuine sixth defect grade. -/
theorem physical_terminal_mesh (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b 12) (S : Saturation A b) :
    coordinate (K:=K) (Fin.last s)-evalNodes A terminalMesh6∈zeroSpace A 6 := by
  classical
  let t := Fin.last s
  have ht : coordinate (K:=K) t∈treeSpace A 6 := S.terminalColumn
  rw [treeSpace_coeff_sup ho (by decide : 6+1≤12)] at ht
  obtain ⟨u,hu,f,hf,e⟩ := Submodule.mem_sup.mp ht
  obtain ⟨P,dp,rfl⟩ := exists_polynomial_of_coeff_range hu
  have t0 : (0:Fin (s+1))≠t := by
    intro et
    exact zero_ne_one ((first_clock_zero ha).symm.trans (et.symm ▸ S.terminalClock))
  have p0 : evalNodes A P 0=0 := by
    have c := congrFun e 0
    change evalNodes A P 0+f 0=coordinate (K:=K) t 0 at c
    have f0 : f 0=0 := origin_zeroSpace ha 6 hf
    have e0 : coordinate (K:=K) t 0=0 := by simp [coordinate,t0]
    rwa [f0,add_zero,e0] at c
  have p1 : evalNodes A P t=1 := by
    have c := congrFun e t
    change evalNodes A P t+f t=coordinate (K:=K) t t at c
    have f1 : f t=0 := grade_six_zero_at_terminal ha ho S hf
    have e1 : coordinate (K:=K) t t=1 := by simp [coordinate]
    rwa [f1,add_zero,e1] at c
  have tests (k : ℕ) (hk : k<6) : probe A b k (evalNodes A P)=b t := by
    have c := congrArg (probe A b k) e
    have z : probe A b k f=0 := probe_zeroSpace ho (by omega) hf
    rw [map_add,z,add_zero] at c
    change _=row (fun i => b i*(nodes A i)^k) (coordinate t) at c
    rwa [row_coordinate,S.terminalClock,one_pow,mul_one] at c
  let a := b t/((1:K)/42)
  have z : P-a • terminalMesh6=0 := by
    apply polynomial_zero_of_origin_probes ha ho (q:=6) (by decide)
    · exact (natDegree_sub_le _ _).trans (max_le dp
        ((natDegree_smul_le ..).trans terminalMesh6_degree))
    · have mesh0 : evalNodes A terminalMesh6 0=0 := by
        rw [evalNodes_apply,first_clock_zero ha,terminalMesh6_value,zero_mul]
      rw [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,p0,mesh0,mul_zero,sub_zero]
    · intro k hk
      rw [map_sub,map_smul,map_sub,map_smul,tests k hk,mesh_probe ho hk,smul_eq_mul]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ (by norm_num : (1:K)/42≠0)).symm
  have pe := sub_eq_zero.mp z
  have a1 : a=1 := by
    have u := congrArg (fun P : K[X] => P.eval (nodes A t)) pe
    change P.eval (nodes A t) = _ at p1
    rw [p1,eval_smul,S.terminalClock,terminalMesh6_value] at u
    norm_num at u
    exact u.symm
  have e' : evalNodes A terminalMesh6+f=coordinate t := by simpa only [pe,a1,one_smul] using e
  rwa [←e',add_sub_cancel_left]

/-- Its vanishing-at-one clock shift is actually paid in the seventh cut,
and the adjacent fourth and fifth ordinary row probes cancel on it. -/
theorem physical_terminal_absorber (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b 12) (S : Saturation A b) :
    let M : K[X] := (X-1)*terminalMesh6
    M.natDegree≤7 ∧ M.coeff 7≠0 ∧ evalNodes A M∈escape7 A ∧
      probe A b 3 (evalNodes A M)=0 := by
  dsimp only
  let t := Fin.last s
  let f := coordinate (K:=K) t-evalNodes A terminalMesh6
  have ff : f∈zeroSpace A 6 := physical_terminal_mesh ha ho S
  have cc : diag (nodes A) (coordinate (K:=K) t)=coordinate t := by
    classical
    ext i
    by_cases hit : i=t
    · subst i; simp [S.terminalClock,t]
    · simp [coordinate,hit]
  have swap : evalNodes A ((X-1)*terminalMesh6)=f-diag (nodes A) f := by
    rw [sub_mul,one_mul,map_sub,evalNodes_X_mul]
    simp only [f,map_sub,cc]
    abel
  have deg : ((X-1 : K[X])*terminalMesh6).natDegree≤7 :=
    natDegree_mul_le.trans (Nat.add_le_add ((natDegree_sub_le _ _).trans (by simp))
      terminalMesh6_degree)
  have cf := terminalMesh6_coeff (K:=K) (6:Fin 7)
  change (terminalMesh6 : K[X]).coeff 6=132 at cf
  refine ⟨deg,?_,?_,?_⟩
  · rw [sub_mul,one_mul,coeff_sub,coeff_X_mul,cf,
      coeff_eq_zero_of_natDegree_lt (terminalMesh6_degree (K:=K).trans_lt (by decide : 6<7)),
      sub_zero]
    norm_num
  · rw [swap]
    exact (escape7 A).sub_mem ((show zeroSpace A 6≤escape7 A from le_sup_left) ff)
      ((show (zeroSpace A 6).map (diag (nodes A))≤escape7 A from le_sup_right)
        (Submodule.mem_map_of_mem ff))
  · rw [sub_mul,one_mul,map_sub,evalNodes_X_mul,map_sub,probe_clock_shift,
      mesh_probe ho (by decide : 3+1<6),mesh_probe ho (by decide : 3<6),sub_self]

/-- Any genuine seventh defect has at most the one indicated degree-six
polynomial leak across the physical terminal cut. -/
theorem grade_seven_single_leak (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b 12) (T : TerminalBand A b)
    {v : Fin (s+1) → K} (hv : v∈zeroSpace A 7) :
    ∃ a : K, v-a • evalNodes A terminalLeak7∈escape7 A := by
  have mem := zeroSpace_le_treeSpace A 7 hv
  rw [T.e7] at mem
  obtain ⟨y,hy,z,hz,e⟩ := Submodule.mem_sup.mp mem
  obtain ⟨P,dp,rfl⟩ := exists_polynomial_of_coeff_range hy
  have zf : z∈zeroSpace A 7 := (mem_zeroAt.mp (T.cut ▸ hz)).1
  have ph : evalNodes A P∈zeroSpace A 7 := by
    simpa only [←e,add_sub_cancel_right] using (zeroSpace A 7).sub_mem hv zf
  let a := P.coeff 6/(462:K)
  have cf := terminalLeak7_coeff (K:=K) (6:Fin 7)
  change (terminalLeak7 : K[X]).coeff 6=462 at cf
  have deg : (P-a • terminalLeak7).natDegree≤5 := by
    have cap := (natDegree_sub_le P (a • terminalLeak7)).trans
      (max_le dp ((natDegree_smul_le ..).trans terminalLeak7_degree))
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rcases (show n=6 ∨ 6<n by omega) with rfl|high
    · rw [coeff_sub,Polynomial.smul_eq_C_mul,Polynomial.coeff_C_mul,cf]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ (by norm_num : (462:K)≠0)).symm
    · exact coeff_eq_zero_of_natDegree_lt (cap.trans_lt high)
  have out : P-a • terminalLeak7=0 := by
    apply polynomial_zero_of_origin_probes ha ho (q:=5) (by decide) deg
    · have leak0 : evalNodes A terminalLeak7 0=0 := by
        rw [evalNodes_apply,first_clock_zero ha,terminalLeak7_value]
        ring
      have p0 : evalNodes A P 0=0 := origin_zeroSpace ha 7 ph
      rw [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
        p0,leak0,mul_zero,sub_zero]
    · intro k hk
      have t : probe A b k (evalNodes A P)=0 := probe_zeroSpace ho (by omega) ph
      rw [map_sub,map_smul,map_sub,map_smul,t,leak_probe ho hk,smul_zero,sub_zero]
  refine ⟨a,?_⟩
  rw [←e,sub_eq_zero.mp out,map_smul,add_sub_cancel_left]
  exact hz

/-- The native T8→T9 chart admits no double leakage across its actual
terminal-zero cut. The only absorber used is its paid terminal mesh. -/
theorem grade_eight_no_double_leak (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b 12) (S : Saturation A b) (T : TerminalBand A b)
    {r : ℕ} {U : Submodule K (Fin (s+1) → K)} {w v : Fin (s+1) → K}
    (H : ForwardStaircase A r U w) (hv : v∈zeroAt (zeroSpace A 8) (Fin.last s))
    (hc : diag (nodes A) v∈zeroAt (zeroSpace A 8) (Fin.last s)) :
    v∈chain (diag (nodes A)) U w (r+3) ∧
      diag (nodes A) v∈chain (diag (nodes A)) U w (r+3) := by
  let D := diag (nodes A)
  let Z (k : ℕ) := chain D U w (r+k)
  have step7 : Z 2⊔(Z 2).map D=Z 3 := by
    simpa only [Z,show r+2+1=r+3 by omega] using
      clock_chain_next H.initial.coreStable (n:=r+2) (w:=w) (by omega)
  have step8 : Z 3⊔(Z 3).map D=Z 4 := by
    simpa only [Z,show r+3+1=r+4 by omega] using
      clock_chain_next H.initial.coreStable (n:=r+3) (w:=w) (by omega)
  have z7 : Z 2=zeroAt (zeroSpace A 7) (Fin.last s) := H.cut.symm.trans T.cut
  have z8 : Z 3≤zeroAt (zeroSpace A 8) (Fin.last s) := by
    rw [←step7,z7]
    exact zeroAt_clock_next A 7 _
  have jump (n : ℕ) : finrank K (chain D U w (n+1))≤finrank K (chain D U w n)+1 := by
    classical
    rw [chain]
    have l : finrank K (K ∙ (D^n) w)≤1 :=
      (finrank_span_le_card ({(D^n) w}:Set (Fin (s+1) → K))).trans (by simp)
    have h := Submodule.finrank_add_le_finrank_add_finrank (chain D U w n) (K ∙ (D^n) w)
    omega
  have cap : finrank K (Z 4)≤9 := by
    have base := T.cutRank
    rw [H.cut] at base
    change finrank K (chain D U w (r+2))=7 at base
    have h := jump (r+2)
    have g := jump (r+3)
    change finrank K (chain D U w (r+4))≤9
    rw [show r+2+1=r+3 by omega] at h
    rw [show r+3+1=r+4 by omega] at g
    omega
  have b8 : treeSpace A 8=clockBand6 A⊔Z 3 := by
    simpa only [Z,Nat.reduceAdd,show r+2+1=r+3 by omega] using (H.bands 1 (by decide)).1
  have b9 : finrank K ↥(clockBand6 A⊔Z 4)=7+9 := by
    obtain ⟨shape,dim⟩ := H.bands 2 (by decide)
    change treeSpace A 9=clockBand6 A⊔Z 4 at shape
    rw [←shape]
    exact dim
  have sep (P : K[X]) (d : P.natDegree≤6) (m : evalNodes A P∈Z 4) : P=0 :=
    polynomial_buffer_separated ha ho (by decide) cap b9 d m
  obtain ⟨deg,nz,mem,pr⟩ := physical_terminal_absorber ha ho S
  have e : escape7 A≤Z 4 := by
    rw [H.cut]
    exact (le_sup_left.trans step7.le).trans (le_sup_left.trans step8.le)
  exact buffered_two_leaks ha ho (d:=4) (j:=8) (by decide) (by decide) (by decide)
    S.terminalClock b8 z8 step8.le sep deg nz (e mem) pr hv hc

/-- Multiplication preserves the measured core whenever the grade sum
is paid in its genuine eighth defect space. -/
theorem grade_eight_multiplier_stable (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b 12) (S : Saturation A b) (T : TerminalBand A b)
    {r j k : ℕ} {U : Submodule K (Fin (s+1) → K)} {w v : Fin (s+1) → K}
    (H : ForwardStaircase A r U w) (inside : U≤zeroSpace A j) (budget : j+k≤8)
    (hv : v∈zeroSpace A k) : U.map (diag v)≤U := by
  rintro _ ⟨u,hu,rfl⟩
  let D := diag (nodes A)
  have mask := clock_mask_invariant
    (fun x (hx : x∈U) => H.initial.coreStable (Submodule.mem_map_of_mem hx))
  have slices (a : K) :
      blockMask (nodes A) a u*v∈chain D U w (r+3) := by
    let z := blockMask (nodes A) a u
    have z0 : z∈U := mask a _ hu
    have z1 : D z∈U := H.initial.coreStable (Submodule.mem_map_of_mem z0)
    have pay {x : Fin (s+1) → K} (hx : x∈U) :
        x*v∈zeroAt (zeroSpace A 8) (Fin.last s) := by
      have f := H.initial.coreInside hx
      exact mem_zeroAt.mpr ⟨zeroSpace_mono A budget (zeroSpace_mul (inside hx) hv),
        by rw [Pi.mul_apply,grade_five_zero_at_terminal ho S f,zero_mul]⟩
    have eq : D (z*v)=D z*v := by ext i; simp [D,mul_assoc]
    exact (grade_eight_no_double_leak ha ho S T H (pay z0)
      (eq.symm ▸ pay z1)).1
  have many := H.many
  have product := HeadFiber.core_product_of_clock_slices H.initial.coreStable (by omega) slices
  have eq : diag v u=u*v := by ext i; simp [mul_comm]
  exact eq ▸ product


/-- All grade-three multipliers preserve the same actual grade-five core. -/
theorem grade_three_multiplier_stable (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b 12) (S : Saturation A b) (T : TerminalBand A b)
    {r : ℕ} {U : Submodule K (Fin (s+1) → K)} {w v : Fin (s+1) → K}
    (H : ForwardStaircase A r U w) (hv : v∈zeroSpace A 3) :
    U.map (diag v)≤U :=
  grade_eight_multiplier_stable ha ho S T H H.initial.coreInside (by decide) hv

/-- Every outside grade-three vector has a nonzero multiplier of degree
at most three on the actual single head. -/
theorem grade_three_multiplier_profile (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b 12) (S : Saturation A b) (T : TerminalBand A b)
    {r : ℕ} {U : Submodule K (Fin (s+1) → K)} {w v : Fin (s+1) → K}
    (H : ForwardStaircase A r U w) (hv : v∈zeroSpace A 3) (out : v∉U) :
    ∃ P : K[X], P≠0 ∧ P.natDegree≤3 ∧ v*w-weightedEval (nodes A) w P∈U := by
  let D := diag (nodes A)
  have first : zeroSpace A 5=chain D U w r := by
    simpa only [Nat.add_zero] using H.initial.flags 0 (by decide)
  have paid := ((clock_chain_le_iff (T:=D) (U:=U) (w:=w) r).mp first.ge).2
  have pay (k : ℕ) (hk : k<r) :
      v*((D^k) w)∈zeroAt (zeroSpace A 8) (Fin.last s) := by
    have p := paid k hk
    exact mem_zeroAt.mpr ⟨zeroSpace_mul hv p,
      by rw [Pi.mul_apply,grade_five_zero_at_terminal ho S p,mul_zero]⟩
  have turn (k : ℕ) : D (v*((D^k) w))=v*((D^(k+1)) w) := by
    rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
    ext i
    simp [D]
    ring
  have pair (k : ℕ) (hk : k+1<r) :
      v*((D^k) w)∈chain D U w (r+3) ∧ v*((D^(k+1)) w)∈chain D U w (r+3) := by
    have h := grade_eight_no_double_leak ha ho S T H (pay k (by omega))
      ((turn k).symm ▸ pay (k+1) hk)
    exact ⟨h.1,turn k ▸ h.2⟩
  have band (k : ℕ) (hk : k<r) : v*((D^k) w)∈chain D U w (r+3) := by
    by_cases i : k+1<r
    · exact (pair k i).1
    · have r2 := H.length
      have j : k-1+1=k := by omega
      rw [←j]
      exact (pair (k-1) (by omega)).2
  have many := H.many
  obtain ⟨P,pnz,deg,fit⟩ := HeadFiber.multiplier_profile_of_chart H.initial.coreStable
    (grade_three_multiplier_stable ha ho S T H hv) (by omega) H.initial.positive band
    (first ▸ zeroSpace_mono A (by decide : 3≤5) hv) out
  exact ⟨P,pnz,by omega,fit⟩

end RKResearch.Certified.Graded.ERK12


