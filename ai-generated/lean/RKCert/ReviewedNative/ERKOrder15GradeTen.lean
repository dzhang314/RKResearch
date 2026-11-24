module

public import RKCert.ReviewedNative.ERKOrder15BandIsolation
public import RKCert.ReviewedNative.MarkedClockProbes

@[expose] public section

/-! # No polynomial leakage from the actual paid grade-ten shifts
A polynomial correction after one clock multiplication changes by a
scalar multiple of the same physical mesh. This extends a native
moment window. The constant Cauchy kernel then removes the correction;
no fitted Jacobi ghost, hand-coded coefficient list or replay is used. -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Polynomial Module
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s a r : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

private theorem clock_eval_X (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (P : K[X]) :
    diag (nodes A) (evalNodes A P)=evalNodes A (X*P) := by ext i; simp

private theorem paid_poly_line {j : ℕ} (S : Order15PaidStaircase A b a G r U w)
    (ho : HasOrder 15 A b) (lo : a+1≤j) (hi : j≤12) (P : K[X]) (pd : P.natDegree≤a+1)
    (hp : evalNodes A P∈order15HeadBand A a r j U w) :
    ∃ t : K, P=Polynomial.C t*G := by
  have gn : G≠0 := by
    intro z
    have e:=S.first.degree
    rw [z,natDegree_zero] at e
    omega
  have lg : G.coeff (a+1)≠0 := by
    rw [←S.first.degree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr gn
  let t := P.coeff (a+1)/G.coeff (a+1)
  let Q := P-Polynomial.C t*G
  have qd : Q.natDegree≤a := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    change (P-Polynomial.C t*G).coeff i=0
    rw [coeff_sub,coeff_C_mul]
    by_cases e : i=a+1
    · subst i
      simp [t,div_mul_cancel₀ _ lg]
    · have gd := S.first.degree
      rw [coeff_eq_zero_of_natDegree_lt (show P.natDegree < i by omega),
        coeff_eq_zero_of_natDegree_lt (show G.natDegree < i by omega),mul_zero,sub_zero]
  have ev : evalNodes A (Polynomial.C t*G)=t•evalNodes A G := by ext i; simp
  have qm : evalNodes A Q∈order15HeadBand A a r j U w := by
    change evalNodes A (P-Polynomial.C t*G)∈_
    rw [map_sub,ev]
    exact (order15HeadBand A a r j U w).sub_mem hp
      ((order15HeadBand A a r j U w).smul_mem _ (S.mesh_in_band j))
  exact ⟨t,sub_eq_zero.mp (S.band_separated ho lo hi Q qd qm)⟩

private theorem grade_ten_mesh_shift (S : Order15PaidStaircase A b a G r U w)
    (ho : HasOrder 15 A b) {P Q : K[X]} {v : Fin (s+1)→K}
    (p : P.natDegree≤a) (q : Q.natDegree≤a)
    (hv : v-evalNodes A P∈order15HeadBand A a r 10 U w)
    (hd : diag (nodes A) v-evalNodes A Q∈order15HeadBand A a r 10 U w) :
    ∃ t : K, X*P-Q=Polynomial.C t*G := by
  have al := S.base_degree
  let B := order15HeadBand A a r 10 U w
  let H := order15HeadBand A a r 11 U w
  let D := diag (nodes A)
  have e : B⊔B.map D=H := S.band_next (by omega)
  have h1 : D (v-evalNodes A P)∈H :=
    (show B.map D≤H from le_sup_right.trans (le_of_eq e)) (Submodule.mem_map_of_mem hv)
  have h2 : D v-evalNodes A Q∈H := (show B≤H from le_sup_left.trans (le_of_eq e)) hd
  have f := H.sub_mem h2 h1
  rw [map_sub,show D v-evalNodes A Q-(D v-D (evalNodes A P))=D (evalNodes A P)-evalNodes A Q by abel] at f
  change diag (nodes A) (evalNodes A P)-evalNodes A Q∈H at f
  rw [clock_eval_X,←map_sub] at f
  have xp : (X*P).natDegree≤a+1 := (natDegree_mul_le (p:=X) (q:=P)).trans (by simp;omega)
  have deg : (X*P-Q).natDegree≤a+1 := by
    simpa only [max_self] using natDegree_sub_le_of_le xp (show Q.natDegree≤a+1 by omega)
  exact paid_poly_line S ho (j:=11) (by omega) (by decide) _ deg f

/-- The grade-ten physical column has a bounded polynomial correction.
Only the available charged moments are asserted, not the eventual
full Cauchy window. -/
theorem Order15PaidStaircase.ten_poly_decompose (S : Order15PaidStaircase A b a G r U w)
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 15 A b)
    {v : Fin (s+1)→K} (hv : v∈markedDefectSpace A b 10) :
    ∃ P : K[X], P.natDegree≤a ∧ P.coeff 0=0 ∧
      v-evalNodes A P∈order15HeadBand A a r 10 U w ∧
      ∀ k≤a-3-terminalDebit A b,chargedProbe A b k (evalNodes A P)=0 := by
  have size := S.frame.size
  have aa := S.base_degree
  have debit := terminalDebit_balance A b
  have h : v∈markedTreeSpace A b 10 := sup_le_sup (zeroSpace_le_treeSpace A 10) le_rfl hv
  rw [(S.full 10 (by omega) (by decide)).1] at h
  obtain ⟨_,⟨x,rfl⟩,u,hu,e⟩:=Submodule.mem_sup.mp h
  let P := ofFn (a+1) x
  have pdeg : P.natDegree≤a := Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) x)
  have pe : evalNodes A P=coeffEval A a x := OneOff.evalNodes_ofFn A a x
  have m : evalNodes A P∈markedDefectSpace A b (10+(7-a)) := by
    rw [pe,show coeffEval A a x=v-u by rw [←e]; abel]
    exact (markedDefectSpace A b (10+(7-a))).sub_mem
      (sup_le_sup (zeroSpace_mono A (by omega)) le_rfl hv) (S.band_paid (by omega) hu)
  have p0 : P.coeff 0=0 := by
    have q := origin_marked_defect ha (by omega : 0<s) m
    rw [evalNodes_eq_coeffEval A P pdeg,coeffEval_origin ha] at q
    exact q
  refine ⟨P,pdeg,p0,?_,?_⟩
  · rw [pe,←e,add_sub_cancel_left]
    exact hu
  · intro k hk
    exact chargedProbe_paid ha ho S.frame.lastActive k m (by omega)

/-- The required finite shift budget kills every grade-ten polynomial
correction on the actual chart. Two shifts suffice unmarked, and
three suffice on the marked branch. -/
theorem Order15PaidStaircase.ten_leak_free_all (S : Order15PaidStaircase A b a G r U w)
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 15 A b)
    {v : Fin (s+1)→K}
    (hv : ∀ i≤2+terminalDebit A b, (diag (nodes A)^i) v∈markedDefectSpace A b 10) :
    ∀ i≤2+terminalDebit A b, (diag (nodes A)^i) v∈order15HeadBand A a r 10 U w := by
  let N := 2+terminalDebit A b
  let B := a-3-terminalDebit A b
  let D := diag (nodes A)
  have aa := S.base_degree
  have dd := terminalDebit_balance A b
  have ex (i : ℕ) : ∃ P : K[X], i≤N → P.natDegree≤a ∧ P.coeff 0=0 ∧
      (D^i) v-evalNodes A P∈order15HeadBand A a r 10 U w ∧
      ∀ k≤B,chargedProbe A b k (evalNodes A P)=0 := by
    by_cases h : i≤N
    · obtain ⟨P,hP⟩:=S.ten_poly_decompose ha ho (hv i h)
      exact ⟨P,fun _=>hP⟩
    · exact ⟨0,fun ni => (h ni).elim⟩
  choose P good using ex
  have shift (i : ℕ) (h : i < N) : ∃ t : K, X*P i-P (i+1)=Polynomial.C t*G := by
    obtain ⟨d₀,_,e₀,_⟩:=good i h.le
    obtain ⟨d₁,_,e₁,_⟩:=good (i+1) (by omega)
    rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply] at e₁
    exact grade_ten_mesh_shift S ho d₀ d₁ e₀ e₁
  have conv (i : ℕ) (h : i < N) :
      ∃ t : K, D (evalNodes A (P i))-evalNodes A (P (i+1))=t•evalNodes A G := by
    obtain ⟨t,h⟩ := shift i h
    refine ⟨t,?_⟩
    calc
      _ = evalNodes A (X*P i-P (i+1)) := by rw [map_sub,←clock_eval_X]
      _ = _ := by rw [h]; ext j; simp
  have gm (k : ℕ) (h : k < B+N) : chargedProbe A b k (evalNodes A G)=0 := by
    dsimp [B,N] at h
    exact chargedProbe_paid ha ho S.frame.lastActive k (S.frame.escapePaid S.first.paid) (by omega)
  have extra := extend_charged_probe_window (A:=A) (b:=b)
    (fun i=>evalNodes A (P i)) (evalNodes A G) B N (fun i h=> (good i h).2.2.2) conv gm
  obtain ⟨p0,origin,_,_⟩ := good 0 (Nat.zero_le N)
  have z : P 0=0 := charged_polynomial_separated ho (by omega) (P 0) p0 origin (fun i h =>
    extra i (by dsimp [B,N];omega))
  have every (i : ℕ) (h : i≤N) : P i=0 := by
    induction i with
    | zero => exact z
    | succ i ih =>
      obtain ⟨t,fit⟩:=shift i (by omega)
      rw [ih (by omega),mul_zero,zero_sub] at fit
      by_cases nt : t=0
      · simpa [nt] using fit
      · have gd := congrArg Polynomial.natDegree fit
        rw [natDegree_neg,natDegree_C_mul nt,S.first.degree] at gd
        have d := (good (i+1) h).1
        omega
  intro i hi
  have e := (good i hi).2.2.1
  rwa [every i hi,map_zero,sub_zero] at e

theorem Order15PaidStaircase.ten_leak_free (S : Order15PaidStaircase A b a G r U w)
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 15 A b)
    {v : Fin (s+1)→K}
    (hv : ∀ i≤2+terminalDebit A b, (diag (nodes A)^i) v∈markedDefectSpace A b 10) :
    v∈order15HeadBand A a r 10 U w := by
  simpa using S.ten_leak_free_all ha ho hv 0 (Nat.zero_le _)

end
end RKResearch.Certified.Graded
