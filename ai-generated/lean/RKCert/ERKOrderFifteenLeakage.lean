module
public import RKCert.ERKOrderFifteenBand

@[expose] public section

/-! # Grade-ten ghost shifts by exact moment propagation, not a fitted ghost basis. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s d a r : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {G : K[X]}

noncomputable def balancedMoment (d : ℕ) (P : K[X]) (k : ℕ) : K :=
  if d=0 then scalarMoment P k else scalarMoment P k-scalarMoment P (k+1)

theorem scalarMoment_sub (P Q : K[X]) (k : ℕ) :
    scalarMoment (P-Q) k=scalarMoment P k-scalarMoment Q k := by
  simp [scalarMoment,mul_sub,map_sub,eval_sub]

theorem scalarMoment_smul (t : K) (P : K[X]) (k : ℕ) :
    scalarMoment (t • P) k=t*scalarMoment P k := by
  simp [scalarMoment,map_smul,eval_smul,smul_eq_mul]

theorem scalarMoment_clock (P : K[X]) (k : ℕ) :
    scalarMoment (X*P) k=scalarMoment P (k+1) := by
  simp only [scalarMoment,pow_succ,mul_assoc]

theorem balancedMoment_sub (d k : ℕ) (P Q : K[X]) :
    balancedMoment d (P-Q) k=balancedMoment d P k-balancedMoment d Q k := by
  by_cases e:d=0 <;> simp [balancedMoment,e,scalarMoment_sub] <;> ring

theorem balancedMoment_smul (d k : ℕ) (t : K) (P : K[X]) :
    balancedMoment d (t • P) k=t*balancedMoment d P k := by
  by_cases e:d=0 <;> simp [balancedMoment,e,scalarMoment_smul] <;> ring

theorem balancedMoment_clock (d k : ℕ) (P : K[X]) :
    balancedMoment d (X*P) k=balancedMoment d P (k+1) := by
  simp [balancedMoment,scalarMoment_clock]

theorem moment_shift_step {P Q G : K[X]} {t : K} {k : ℕ}
    (hp : X*P-Q=t • G) (mg : balancedMoment d G k=0) :
    balancedMoment d P (k+1)=balancedMoment d Q k := by
  have h := congrArg (fun R : K[X]=>balancedMoment d R k) hp
  rwa [balancedMoment_sub,balancedMoment_clock,balancedMoment_smul,mg,mul_zero,
    sub_eq_zero] at h

theorem consecutive_moments (E : ℕ→K[X]) (G : K[X]) (B n : ℕ)
    (base : ∀ i≤n,∀ k≤B,balancedMoment d (E i) k=0)
    (step : ∀ i<n,∃t : K,X*E i-E (i+1)=t • G)
    (gm : ∀ k<B+n,balancedMoment d G k=0) :
    ∀ k≤B+n,balancedMoment d (E 0) k=0 := by
  induction n generalizing E with
  | zero =>
    intro k hk
    exact base 0 le_rfl k (by omega)
  | succ n ih =>
    intro k hk
    by_cases small:k≤B
    · exact base 0 (by omega) k small
    have k0 : k-1+1=k := by omega
    have sub := ih (fun i=>E (i+1)) (fun i hi j hj=>base _ (by omega) _ hj)
      (fun i hi=>step _ (by omega)) (fun j hj=>gm _ (by omega)) (k-1) (by omega)
    obtain ⟨t,fit⟩:=step 0 (by omega)
    rw [←k0,moment_shift_step fit (gm _ (by omega))]
    exact sub

theorem OddSevenChart.mesh_moment (ho : HasTreeOrderAtLeast A b 15)
    (M : Margin A b 7 1 d) (C : OddSevenChart A d a r U w G) (k : ℕ)
    (hk : k≤(if d=0 then 6 else 5)) : balancedMoment d G k=0 := by
  have pd : G.natDegree≤8 := by have :=C.meshDegree; have :=C.aLe;omega
  have h := firstEscape_defect C.meshPaid
  by_cases z:d=0
  · subst d
    simp [balancedMoment] at hk ⊢
    exact marked_moment_zero ho G h pd (by omega)
  · simp only [balancedMoment,ite_eq_right z] at hk ⊢
    exact marked_moment_difference ho G h pd M.atOne (by omega)

omit [CharZero K] in
theorem OddSevenChart.next_poly {P:K[X]} (S:Saturated A b 7 1) (M:Margin A b 7 1 d)
    (C:OddSevenChart A d a r U w G) (hj:a+1≤11) (hmax:11≤12)
    (hp:P.natDegree≤a+1) (hP:evalNodes A P∈forwardBand A 7 a r U w 11) :
    ∃ τ:K,P=τ•G := by
  have GL : G.coeff (a+1)≠0 := by
    rw [←C.meshDegree,coeff_natDegree,leadingCoeff_ne_zero]
    intro h
    have dg := C.meshDegree
    rw [h,natDegree_zero] at dg
    omega
  let τ := P.coeff (a+1)/G.coeff (a+1)
  let T := P-τ•G
  have dh:T.natDegree≤a := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    change (P-τ•G).coeff i=0
    rw [coeff_sub,AddMonoidAlgebra.coeff_smul_apply,smul_eq_mul]
    by_cases h:i=a+1
    · subst i
      unfold τ
      rw [div_mul_cancel₀ _ GL,sub_self]
    · have P0 := coeff_eq_zero_of_natDegree_lt (p:=P) (n:=i) (by omega)
      have G0 := coeff_eq_zero_of_natDegree_lt (p:=G) (n:=i) (by have :=C.meshDegree;omega)
      rw [P0,G0,mul_zero,sub_self]
  have hG := C.band_first hj C.meshPaid
  have ht : evalNodes A T∈forwardBand A 7 a r U w 11 := by
    have e:evalNodes A T=evalNodes A P-τ•evalNodes A G := by ext i; simp [T,evalNodes,eval_smul]
    rw [e]
    exact Submodule.sub_mem _ hP (Submodule.smul_mem _ _ hG)
  refine ⟨τ,?_⟩
  exact sub_eq_zero.mp (C.band_sep S M hj hmax T dh ht)

omit [CharZero K] in
theorem OddSevenChart.shift_poly {P Q:K[X]} (S:Saturated A b 7 1) (M:Margin A b 7 1 d)
    (C:OddSevenChart A d a r U w G) (hj:a+1≤10) (hmax:11≤12)
    {v:Vec K (s+1)} (dp:P.natDegree≤a) (dq:Q.natDegree≤a)
    (hp:v-evalNodes A P∈forwardBand A 7 a r U w 10)
    (hq:diag (nodes A) v-evalNodes A Q∈forwardBand A 7 a r U w 10) :
    ∃ τ:K,X*P-Q=τ•G := by
  let D:=diag (nodes A)
  let B:=forwardBand A 7 a r U w 10
  let W:=forwardBand A 7 a r U w 11
  have he:B⊔B.map D=W := C.band_next hj
  have m1 : D (v-evalNodes A P)∈W := by
    rw [←he]
    exact (show B.map D≤B⊔B.map D from le_sup_right) (Submodule.mem_map_of_mem hp)
  have m2 : D v-evalNodes A Q∈W := by
    rw [←he]
    exact (show B≤B⊔B.map D from le_sup_left) hq
  have hmem := W.sub_mem m2 m1
  rw [map_sub,show D v-evalNodes A Q-(D v-D (evalNodes A P))=
        D (evalNodes A P)-evalNodes A Q by abel] at hmem
  have e : evalNodes A (X*P-Q)=D (evalNodes A P)-evalNodes A Q := by ext i; simp [D,evalNodes]
  apply C.next_poly S M (by omega) hmax (diff_clock_degree P Q a dp dq)
  rw [e]
  exact hmem

theorem OddSevenChart.grade_ten_decompose (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1) (M : Margin A b 7 1 d) (C : OddSevenChart A d a r U w G)
    {v : Vec K (s+1)} (hv : v∈defectPlus A d 10) :
    ∃ P : K[X],P.natDegree≤a ∧ P.coeff 0=0 ∧
      v-evalNodes A P∈forwardBand A 7 a r U w 10 ∧
      ∀ k≤(if d=0 then 4 else a-4),balancedMoment d P k=0 := by
  classical
  have alo:=C.aLo
  have ale:=C.aLe
  have hE : v∈treePlus A d 10 := (sup_le_sup (zeroSpace_le_treeSpace A 10) (show tailPlane K s d≤_ from le_rfl)) hv
  rw [C.chart 10 (by omega) (by decide)] at hE
  obtain ⟨u,⟨c,rfl⟩,z,hz,eq⟩:=Submodule.mem_sup.mp hE
  let P:=ofFn (a+1) c
  have pd:P.natDegree≤a := Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
  have ev:evalNodes A P=polyEval A a c := evalNodes_ofFn A a c
  have hPd : evalNodes A P∈defectPlus A d (10+(7-a)) := by
    rw [ev,show polyEval A a c=v-z by rw [←eq];abel]
    exact Submodule.sub_mem _ (Fplus_mono A d (by omega) hv) (C.band_paid (by omega) hz)
  have pdegree : P.natDegree≤10+(7-a) := by omega
  refine ⟨P,pd,marked_eval_origin ha (by have := S.size;omega) P hPd,?_,?_⟩
  · rw [ev,←eq]
    simpa only [add_sub_cancel_left] using hz
  · intro k hk
    by_cases d0:d=0
    · have a7 : a=7 := C.chartType.resolve_right (by omega)
      subst d
      simp [balancedMoment] at hk ⊢
      exact marked_moment_zero ho P hPd pdegree (by omega)
    · simp only [balancedMoment,ite_eq_right d0] at hk ⊢
      exact marked_moment_difference ho P hPd pdegree M.atOne (by omega)

theorem dx6_marked_six :
    balancedMoment 1 (dx6 : K[X]) 6=(1/6435:K) := by
  have h : (dx6:K[X]).natDegree≤10 := by rw [dx6_degree];decide
  unfold balancedMoment
  rw [ite_eq_right (by decide : (1:ℕ)≠0),scalarMoment_11 _ h,scalarMoment_11 _ h]
  norm_num [moment,Fin.sum_univ_succ,dx6_coeff]

theorem odd_seven_ghost_rigid (C : OddSevenChart A d a r U w G)
    (P : K[X]) (pd : P.natDegree≤a) (p0 : P.coeff 0=0)
    (mom : ∀ k≤(if d=0 then 6 else a-1),balancedMoment d P k=0) : P=0 := by
  have ale:=C.aLe
  by_contra pn
  by_cases dz:d=0
  · subst d
    have h := meshOddFull7_decode P (by omega) p0 (fun k=>by
      have m := mom k.val (by have :=k.isLt;simp;omega)
      simpa [balancedMoment] using m)
    obtain ⟨t,e⟩:=h
    have r := (mesh_line_degree e pn).trans odd7_degree
    omega
  · have alo:=C.aLo
    have h := meshOddPrefix7_decode P (by omega) p0 (fun k=>by
      have m := mom k.val (by have :=k.isLt;simp only [ite_eq_right dz];omega)
      simpa [balancedMoment,dz] using m)
    obtain ⟨t,u,e⟩:=h
    obtain ⟨_,deg,t',tn,E⟩:=odd_seven_alias_form (.marked t u e) (by omega) pn
    have eq:a=7 := by omega
    have zero := mom 6 (by rw [ite_eq_right dz,eq])
    rw [E,balancedMoment_smul] at zero
    have v : balancedMoment d (dx6 : K[X]) 6=(1/6435:K) := by
      simpa only [balancedMoment,ite_eq_right dz,ite_eq_right (by decide : (1:ℕ)≠0)] using (dx6_marked_six (K:=K))
    exact mul_ne_zero tn (by norm_num : (1/6435:K)≠0) (v ▸ zero)

theorem OddSevenChart.leak_free_ten_all (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1) (M : Margin A b 7 1 d) (C : OddSevenChart A d a r U w G)
    {v : Vec K (s+1)}
    (hv : ∀ i≤(if d=0 then 2 else 3),(diag (nodes A)^i) v∈defectPlus A d 10) :
    ∀i≤(if d=0 then 2 else 3),(diag (nodes A)^i) v∈forwardBand A 7 a r U w 10 := by
  classical
  let n := if d=0 then 2 else 3
  let B := if d=0 then 4 else a-4
  let D := diag (nodes A)
  have alo:=C.aLo
  have ale:=C.aLe
  have ex (i : ℕ) : ∃P : K[X], i≤n → P.natDegree≤a ∧ P.coeff 0=0 ∧
      (D^i) v-evalNodes A P∈forwardBand A 7 a r U w 10 ∧
      ∀ k≤B,balancedMoment d P k=0 := by
    by_cases hi:i≤n
    · obtain ⟨P,h⟩:=C.grade_ten_decompose ha ho S M (hv i hi)
      exact ⟨P,fun _=>h⟩
    · exact ⟨0,fun bad=>(hi bad).elim⟩
  choose P good using ex
  have shift (i : ℕ) (hi:i<n) : ∃τ : K,X*P i-P (i+1)=τ • G := by
    obtain ⟨di,_,mi,_⟩:=good i hi.le
    obtain ⟨dii,_,mii,_⟩:=good (i+1) (by omega)
    rw [pow_succ',mul_apply_eq_comp] at mii
    exact C.shift_poly S M (by omega) (by decide) di dii mi mii
  have gm : ∀k<B+n,balancedMoment d G k=0 := by
    intro k hk
    apply C.mesh_moment ho M
    by_cases dz:d=0 <;> simp [n,B,dz] at hk ⊢ <;> omega
  have mom := consecutive_moments P G B n (fun i hi=>(good i hi).2.2.2) shift gm
  obtain ⟨pd,p0,e,_⟩:=good 0 (Nat.zero_le n)
  have h : P 0=0 := odd_seven_ghost_rigid C _ pd p0 (fun k hk=>mom k (by
    by_cases dz:d=0 <;> simp [B,n,dz] at hk ⊢ <;> omega))
  have all0 (i : ℕ) (hi : i≤n) : P i=0 := by
    induction i with
    | zero => exact h
    | succ i ih =>
      obtain ⟨t,fit⟩:=shift i (by omega)
      rw [ih (by omega),mul_zero,zero_sub] at fit
      by_cases z:t=0
      · simpa only [z,zero_smul,neg_eq_zero] using fit
      · have hdeg := congrArg Polynomial.natDegree fit
        rw [natDegree_neg,natDegree_smul G z,C.meshDegree] at hdeg
        have deg := (good (i+1) hi).1
        omega
  intro i hi
  have hP := (good i hi).2.2.1
  have evz : evalNodes A (0:K[X])=0 := by ext i;simp [evalNodes]
  rwa [all0 i hi,evz,sub_zero] at hP

theorem OddSevenChart.leak_free_ten (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1) (M : Margin A b 7 1 d) (C : OddSevenChart A d a r U w G)
    {v : Vec K (s+1)}
    (hv : ∀ i≤(if d=0 then 2 else 3),(diag (nodes A)^i) v∈defectPlus A d 10) :
    v∈forwardBand A 7 a r U w 10 := by
  simpa only [pow_zero,one_apply_eq_self] using C.leak_free_ten_all ha ho S M hv 0 (Nat.zero_le _)

end RKCert.Paired.FiniteMidpoint
