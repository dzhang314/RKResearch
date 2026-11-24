module

public import RKCert.ReviewedNative.TwoEndpointClockSeparation
public import RKCert.ReviewedNative.PolynomialStageSeparation
public import Mathlib.Algebra.Polynomial.OfFn

public section

/-! # Two consecutive endpoint-zero defects cannot leak through one clock buffer

Rather than decoding the possible leaks into specific rational polynomials,
shift one paid probe through the physical clock. A true absorber kills the
top degree and preserves the probe. The extra equation separates the
first polynomial by the two actual endpoints. -/
namespace RKResearch.Certified.Graded

open RKResearch Polynomial Module Reverse
open scoped Matrix

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

/-- The physical clock moves an ordinary row probe by one. -/
theorem probe_clock_shift (v : Fin (s+1) → K) (k : ℕ) :
    probe A b k (diag (nodes A) v)=probe A b (k+1) v := by
  simp only [probe,row_apply,dotProduct,diag_apply,pow_succ]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem evalNodes_X_mul (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (P : K[X]) :
    evalNodes A (X*P)=diag (nodes A) (evalNodes A P) := by
  ext i
  simp

/-- The terminal-zero filtration retains inclusion and advances under
multiplication by the actual clock. -/
theorem zeroAt_clock_next (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (j : ℕ) (t : Fin (s+1)) :
    zeroAt (zeroSpace A j) t ⊔ (zeroAt (zeroSpace A j) t).map (diag (nodes A)) ≤
      zeroAt (zeroSpace A (j+1)) t := by
  apply sup_le
  · intro v hv
    obtain ⟨f,e⟩ := mem_zeroAt.mp hv
    exact mem_zeroAt.mpr ⟨zeroSpace_mono A (Nat.le_succ j) f,e⟩
  · rintro _ ⟨v,hv,rfl⟩
    obtain ⟨f,e⟩ := mem_zeroAt.mp hv
    exact mem_zeroAt.mpr ⟨diag_zeroSpace A j f,by rw [diag_apply,e,mul_zero]⟩

/-- Coefficient range membership is an actual polynomial of bounded
degree, with no interpolation on stage values. -/
theorem exists_polynomial_of_coeff_range {q : ℕ} {v : Fin (s+1) → K}
    (mem : v∈(coeffEval A q).range) :
    ∃ P : K[X], P.natDegree≤q ∧ evalNodes A P=v := by
  classical
  obtain ⟨a,rfl⟩ := mem
  let P := ofFn (q+1) a
  have d : P.natDegree≤q := Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) a)
  exact ⟨P,d,by rw [evalNodes_eq_coeffEval A P d]; congr 1; ext i; exact ofFn_coeff_eq_val_of_lt _ i.isLt⟩

/-- Two actual endpoint zeros and a complete paid set of ordinary
moments determine a bounded polynomial independently of a defect grade. -/
theorem polynomial_zero_of_endpoint_probes (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b p) {n : ℕ} (pay : 2*n+1≤p)
    {t : Fin (s+1)} (one : nodes A t=1)
    {P : K[X]} (deg : P.natDegree≤n+1) (origin : evalNodes A P 0=0)
    (terminal : evalNodes A P t=0)
    (tests : ∀ k<n, probe A b k (evalNodes A P)=0) : P=0 := by
  let a : Fin (n+2) → K := fun i => P.coeff i.val
  have rep : evalNodes A P = coeffEval A (n+1) a := evalNodes_eq_coeffEval A P deg
  rw [rep,coeffEval_origin ha] at origin
  rw [rep,coeffEval_apply] at terminal
  have sum : (∑ i : Fin (n+2),a i)=0 := by
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,normTree_clockTree,
      Pi.pow_apply,one,one_pow,mul_one] using terminal
  rw [Fin.sum_univ_succ,origin,zero_add] at sum
  have eq (i : Fin n) : (∑ k : Fin (n+1),a k.succ/((i.val+k.val+2:ℕ):K))=0 := by
    have u := tests i i.isLt
    rw [rep,probe_coeffEval ho (by have := i.isLt; omega),Fin.sum_univ_succ,origin,
      zero_div,zero_add] at u
    simpa only [Fin.val_succ,Nat.add_assoc] using u
  have out := paid_sum_cauchy ho pay (fun k : Fin (n+1) => a k.succ) sum eq
  ext i
  rw [coeff_zero]
  by_cases hi : i<n+2
  · have az (i : Fin (n+2)) : a i=0 :=
      Fin.cases (motive := fun j => a j=0) origin (fun k => congrFun out k) i
    exact az ⟨i,hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The zero first physical stage saves the zeroth coefficient in
the ordinary square Cauchy system. -/
theorem polynomial_zero_of_origin_probes (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b p) {q : ℕ} (pay : 2*q≤p)
    {P : K[X]} (deg : P.natDegree≤q) (origin : evalNodes A P 0=0)
    (tests : ∀ k<q, probe A b k (evalNodes A P)=0) : P=0 := by
  let a : Fin (q+1) → K := fun i => P.coeff i.val
  have rep : evalNodes A P = coeffEval A q a := evalNodes_eq_coeffEval A P deg
  rw [rep,coeffEval_origin ha] at origin
  have eq (i : Fin q) : (∑ k : Fin q,a k.succ/((i.val+k.val+2:ℕ):K))=0 := by
    have u := tests i i.isLt
    rw [rep,probe_coeffEval ho (by have := i.isLt; omega),Fin.sum_univ_succ,origin,
      zero_div,zero_add] at u
    simpa only [Fin.val_succ,Nat.add_assoc] using u
  have out := moments_detect ho (d:=2) (by decide) (by omega)
    (fun i j : Fin q => by have := i.isLt; have := j.isLt; omega)
    (fun k : Fin q => a k.succ) eq
  ext i
  rw [coeff_zero]
  by_cases hi : i<q+1
  · have az (i : Fin (q+1)) : a i=0 :=
      Fin.cases (motive := fun j => a j=0) origin out i
    exact az ⟨i,hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Exact rank saturation separates all degree-q clock polynomials from
an available head band. The clock range is measured on the true tableau. -/
theorem polynomial_buffer_separated (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b p) {q h : ℕ} (paid : 2*q≤p)
    {Z : Submodule K (Fin (s+1) → K)} (cap : finrank K Z≤h)
    (dim : finrank K ↥((coeffEval A q).range⊔Z)=q+1+h)
    {P : K[X]} (deg : P.natDegree≤q) (m : evalNodes A P∈Z) : P=0 := by
  have sep := explicit_coeff_separated ha ho paid
  have inj : Function.Injective (coeffEval A q) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro a h
    exact sep a (h ▸ (zeroSpace A q).zero_mem)
  have rank : finrank K (coeffEval A q).range=q+1 :=
    (LinearMap.finrank_range_of_inj inj).trans (Module.finrank_fin_fun K)
  have g := Submodule.finrank_sup_add_finrank_inf_eq (coeffEval A q).range Z
  rw [dim,rank] at g
  have dis : (coeffEval A q).range⊓Z=⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  have mm : evalNodes A P∈(coeffEval A q).range⊓Z :=
    ⟨⟨_,(evalNodes_eq_coeffEval A P deg).symm⟩,m⟩
  have z := (Submodule.mem_bot K).mp (dis ▸ mm)
  exact (PolySeparated.of_coeff sep) _ deg (z ▸ (zeroSpace A q).zero_mem)

/-- A next-band absorber with a paid moment prevents simultaneous leaks
for a vector and its clock shift. The argument is uniform in the buffer
size, actual stage count and coefficient field. -/
theorem buffered_two_leaks (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder A b p) {d j : ℕ} (pos : 0<d)
    (ordinary : d+j≤p) (paid : 2*d+3≤p)
    {t : Fin (s+1)} (one : nodes A t=1)
    {Z W : Submodule K (Fin (s+1) → K)}
    (split : treeSpace A j=(coeffEval A (d+2)).range⊔Z)
    (atEnd : Z≤zeroAt (zeroSpace A j) t)
    (next : Z⊔Z.map (diag (nodes A))≤W)
    (separated : ∀ P : K[X], P.natDegree≤d+2 → evalNodes A P∈W → P=0)
    {M : K[X]} (md : M.natDegree≤d+3) (mn : M.coeff (d+3)≠0)
    (memM : evalNodes A M∈W) (probeM : probe A b (d-1) (evalNodes A M)=0)
    {v : Fin (s+1) → K} (hv : v∈zeroAt (zeroSpace A j) t)
    (hcv : diag (nodes A) v∈zeroAt (zeroSpace A j) t) :
    v∈Z ∧ diag (nodes A) v∈Z := by
  let D := diag (nodes A)
  have decompose {u : Fin (s+1) → K} (hu : u∈zeroAt (zeroSpace A j) t) :
      ∃ P : K[X], P.natDegree≤d+2 ∧ evalNodes A P∈zeroAt (zeroSpace A j) t ∧
        ∃ z∈Z, evalNodes A P+z=u := by
    have tr := zeroSpace_le_treeSpace A j (mem_zeroAt.mp hu).1
    rw [split] at tr
    obtain ⟨v,hv,z,hz,e⟩ := Submodule.mem_sup.mp tr
    obtain ⟨P,dp,rfl⟩ := exists_polynomial_of_coeff_range hv
    refine ⟨P,dp,?_,z,hz,e⟩
    simpa only [←e,add_sub_cancel_right] using
      (zeroAt (zeroSpace A j) t).sub_mem hu (atEnd hz)
  obtain ⟨P,dp,pe,x,hx,ex⟩ := decompose hv
  obtain ⟨Q,dq,qe,y,hy,ey⟩ := decompose hcv
  let a := P.coeff (d+2)/M.coeff (d+3)
  let R := X*P-Q-a • M
  have rmem : evalNodes A R∈W := by
    have step : D (evalNodes A P)-evalNodes A Q=y-D x := by
      change evalNodes A Q+y=D v at ey
      rw [←ex,map_add] at ey
      calc
        _ = (D (evalNodes A P)+D x)-evalNodes A Q-D x := by abel
        _ = _ := by rw [←ey]; abel
    rw [show evalNodes A R=D (evalNodes A P)-evalNodes A Q-a • evalNodes A M by
      simp only [R,map_sub,map_smul,evalNodes_X_mul,D], step]
    exact W.sub_mem (W.sub_mem (next ((show Z≤Z⊔Z.map D from le_sup_left) hy))
      (next ((show Z.map D≤Z⊔Z.map D from le_sup_right) (Submodule.mem_map_of_mem hx)))) (W.smul_mem _ memM)
  have degree : R.natDegree≤d+2 := by
    have dX : (X*P).natDegree≤d+3 := natDegree_mul_le.trans (by rw [natDegree_X]; omega)
    have cap : R.natDegree≤d+3 := by
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · exact (natDegree_sub_le _ _).trans (max_le dX (dq.trans (by omega)))
      · exact (natDegree_smul_le ..).trans md
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rcases Nat.eq_or_lt_of_le (show d+3≤k by omega) with e|e
    · rw [←e]
      have qz : Q.coeff (d+3)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp only [R,coeff_sub,show d+3=d+2+1 by omega,coeff_X_mul,qz,sub_zero,
        Polynomial.smul_eq_C_mul,Polynomial.coeff_C_mul]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ mn).symm
    · exact coeff_eq_zero_of_natDegree_lt (cap.trans_lt e)
  have zR := separated R degree rmem
  have small {S : K[X]} (inF : evalNodes A S∈zeroAt (zeroSpace A j) t) {k : ℕ} (hk : k<d) :
      probe A b k (evalNodes A S)=0 :=
    probe_zeroSpace ho (by omega) (mem_zeroAt.mp inF).1
  have extra := congrArg (fun S : K[X] => probe A b (d-1) (evalNodes A S)) zR
  change probe A b (d-1) (evalNodes A R)=probe A b (d-1) (evalNodes A (0:K[X])) at extra
  simp only [R,map_sub,map_smul,map_zero,smul_zero,evalNodes_X_mul,probe_clock_shift,
    small qe (show d-1<d by omega),probeM,sub_zero,show d-1+1=d by omega] at extra
  have zp : P=0 := polynomial_zero_of_endpoint_probes ha ho (n:=d+1) (by omega)
    one dp (origin_zeroSpace ha j (mem_zeroAt.mp pe).1) (mem_zeroAt.mp pe).2 (by
      intro k hk
      by_cases e : k=d
      · simpa only [e] using extra
      · exact small pe (by omega))
  have zq : Q=0 := by
    have z : -Q=0 := by simpa [R,a,zp] using zR
    exact neg_eq_zero.mp z
  have xx : x=v := by simpa only [zp,map_zero,zero_add] using ex
  have yy : y=D v := by simpa only [zq,map_zero,zero_add] using ey
  exact ⟨xx ▸ hx,yy ▸ hy⟩

end RKResearch.Certified.Graded

