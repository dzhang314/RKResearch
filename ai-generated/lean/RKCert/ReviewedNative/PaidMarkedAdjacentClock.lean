module

public import RKCert.ReviewedNative.BufferedClockLeakage
public import RKCert.ReviewedNative.OptionalTerminalMark
public import RKCert.ReviewedNative.NativePrimitiveMoments

import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Actual marked adjacent clock transport

The literal terminal mark contributes a constant primitive moment, removed
by the endpoint difference. An absorbed clock relation propagates a fixed
paid window by one per adjacent shift. Once the first polynomial projection
vanishes, the same relations kill every projection in the given shift window.
No scalar mesh decoder or prior row-equivalence is imported. -/
namespace RKResearch.Certified.Graded.MarkedAdjacent

open RKResearch Polynomial Module Reverse
open scoped Matrix Classical
noncomputable section

variable {K : Type*} [Field K]

/-- The unit-interval primitive moment according to the native primitive. -/
def unitMoment (K : Type*) [Field K] (k : ℕ) : K[X] →ₗ[K] K :=
  (Polynomial.leval 1).comp (primitive.comp (LinearMap.mulLeft K (X^k : K[X])))

def endpointMoment (K : Type*) [Field K] (k : ℕ) : K[X] →ₗ[K] K :=
  unitMoment K k - unitMoment K (k+1)

theorem unitMoment_apply (k : ℕ) (P : K[X]) :
    unitMoment K k P = (primitive (X^k*P)).eval 1 := rfl

theorem unitMoment_clock (k : ℕ) (P : K[X]) :
    unitMoment K k (X*P) = unitMoment K (k+1) P := by
  rw [unitMoment_apply,unitMoment_apply,pow_succ,mul_assoc]

theorem endpointMoment_apply (k : ℕ) (P : K[X]) :
    endpointMoment K k P = (primitive (X^k*((1-X)*P))).eval 1 := by
  have e : (X^k*((1-X)*P):K[X]) = X^k*P-X^(k+1)*P := by
    rw [sub_mul,one_mul,mul_sub,pow_succ,mul_assoc]
  rw [e,map_sub,eval_sub] <;> rfl

theorem endpointMoment_clock (k : ℕ) (P : K[X]) :
    endpointMoment K k (X*P) = endpointMoment K (k+1) P := by
  simp only [endpointMoment,LinearMap.sub_apply,unitMoment_clock]

/-- Quotient by a single actual adjacent_eq of the next degree. -/
theorem reduction_by_next_degree {a : ℕ} {T G : K[X]}
    (top : T.natDegree≤a+1) (mesh : G.natDegree=a+1) :
    ∃ z : K, (T-z • G).natDegree≤a := by
  have nz : G≠0 := by
    intro z
    rw [z,natDegree_zero] at mesh
    omega
  have gn : G.coeff (a+1)≠0 := by
    rw [←mesh,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr nz
  let z := T.coeff (a+1)/G.coeff (a+1)
  refine ⟨z,natDegree_le_iff_coeff_eq_zero.mpr ?_⟩
  intro k hk
  by_cases e : k=a+1
  · subst k
    rw [coeff_sub,Polynomial.coeff_smul,smul_eq_mul,sub_eq_zero]
    exact (div_mul_cancel₀ _ gn).symm
  · have h : a+1<k := by omega
    rw [coeff_sub,Polynomial.coeff_smul,coeff_eq_zero_of_natDegree_lt (top.trans_lt h),
      coeff_eq_zero_of_natDegree_lt (mesh.trans_lt h),smul_zero,sub_zero]

/-- A run of `m` true adjacent polynomial equations earns `m` extra
consecutive endpoint differences on the first polynomial. The mesh is
used only at indices strictly below the last earned index. -/
theorem endpointMoment_chain {G : K[X]} (P : ℕ → K[X]) {n m : ℕ} (pos : 0<n)
    (paid : ∀ i≤m, ∀ k<n, endpointMoment K k (P i)=0)
    (steps : ∀ i<m, ∃ u : K, X*P i-P (i+1)=u • G)
    (mesh : ∀ k<n+m-1, endpointMoment K k G=0) :
    ∀ k<n+m, endpointMoment K k (P 0)=0 := by
  have advance (d : ℕ) : ∀ i, i+d≤m → ∀ k<n+d, endpointMoment K k (P i)=0 := by
    induction d with
    | zero =>
      intro i hi k hk
      exact paid i (by omega) k (by omega)
    | succ d ih =>
      intro i hi k hk
      by_cases short : k<n+d
      · exact ih i (by omega) k short
      · obtain ⟨u,e⟩ := steps i (by omega)
        have e' : X*P i=P (i+1)+u • G := by rw [←e]; abel
        have test := congrArg (endpointMoment K (k-1)) e'
        rw [endpointMoment_clock,map_add,map_smul,ih (i+1) (by omega) (k-1) (by omega),
          mesh (k-1) (by omega),smul_zero,add_zero,show k-1+1=k by omega] at test
        exact test
  exact advance m 0 (by omega)

variable {s p j h : ℕ} {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
variable {b : Fin (s+1) → K}

/-- Convert the actual marked paid probe to equality of scalar moments. -/
theorem unitMoment_eq_initial_of_marked_defect
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder p A b)
    (L : LastActive b (Fin.last s)) {P : K[X]} {k : ℕ}
    (paid : k+j+1≤p) (degreePaid : k+P.natDegree+1≤p)
    (hP : evalNodes A P∈markedDefectSpace A b j) :
    unitMoment K k P=unitMoment K 0 P := by
  have eq := paid_probe_marked_defect ha ho L hP k paid
  rw [probe_evalNodes ho P k degreePaid,probe_evalNodes ho P 0 (by omega)] at eq
  exact eq

theorem endpointMoment_zero_of_marked_defect
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder p A b)
    (L : LastActive b (Fin.last s)) {P : K[X]} {k : ℕ}
    (paid : k+1+j+1≤p) (degreePaid : k+1+P.natDegree+1≤p)
    (hP : evalNodes A P∈markedDefectSpace A b j) : endpointMoment K k P=0 := by
  change unitMoment K k P-unitMoment K (k+1) P=0
  rw [unitMoment_eq_initial_of_marked_defect ha ho L (by omega) (by omega) hP,
    unitMoment_eq_initial_of_marked_defect ha ho L paid degreePaid hP,sub_self]

theorem origin_of_marked_defect_polynomial
    (ha : ∀ i k, i≤k → A i k=0) (size : 0<s)
    {P : K[X]} (hP : evalNodes A P∈markedDefectSpace A b j) : P.eval 0=0 := by
  have hz := origin_marked_defect ha size hP
  have h0 : nodes A (0 : Fin (s+1))=0 := by
    change (∑ i,A 0 i*1)=0
    exact Finset.sum_eq_zero (fun i _=>by rw [ha 0 i (Fin.zero_le _),zero_mul])
  simpa only [evalNodes_apply,h0] using hz

variable [CharZero K]

/-- Common marked locality lemma. The lower chart is where the columns
actually live; the next chart is used only for separation of the trimmed
adjacent difference. All members of the given window are pure, not just
its first member. The exact budget is `h+n+1 ≤ p`, with `a ≤ h`. -/
theorem pure_of_paid_marked_adjacent_clocks
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder p A b)
    (L : LastActive b (Fin.last s)) (size : 0<s)
    {a n m : ℕ} (pos : 0<n) (count : a≤n+m)
    (jh : j≤h) (ah : a≤h) (nPaid : h+n+1≤p)
    {Z W : Submodule K (Fin (s+1)→K)}
    (cover : markedDefectSpace A b j ≤ (coeffEval A a).range⊔Z)
    (bandPaid : Z≤markedDefectSpace A b h)
    (next : Z⊔Z.map (diag (nodes A))≤W)
    (separated : ∀ P : K[X], P.natDegree≤a → evalNodes A P∈W → P=0)
    {G : K[X]} (gd : G.natDegree=a+1) (gW : evalNodes A G∈W)
    (gMom : ∀ k<n+m-1, endpointMoment K k G=0)
    {x : Fin (s+1)→K}
    (shift : ∀ i≤m, ((diag (nodes A))^i) x∈markedDefectSpace A b j) :
    ∀ i≤m, ((diag (nodes A))^i) x∈Z := by
  let D := diag (nodes A)
  have existsDec (i : ℕ) : ∃ P : K[X], ∃ z : Fin (s+1)→K,
      P.natDegree≤a ∧ z∈Z ∧ (i≤m → evalNodes A P+z=(D^i) x) := by
    by_cases hi : i≤m
    · obtain ⟨v,hv,z,hz,e⟩ := Submodule.mem_sup.mp (cover (shift i hi))
      obtain ⟨P,pd,rfl⟩ := exists_polynomial_of_coeff_range hv
      exact ⟨P,z,pd,hz,fun _=>e⟩
    · exact ⟨0,0,by simp,Z.zero_mem,fun bad=>(hi bad).elim⟩
  choose P z pdeg hz dec using existsDec
  have marked (i : ℕ) (hi : i≤m) : evalNodes A (P i)∈markedDefectSpace A b h := by
    have e := (markedDefectSpace A b h).sub_mem
      ((sup_le_sup (zeroSpace_mono A jh) le_rfl) (shift i hi)) (bandPaid (hz i))
    rwa [←dec i hi,add_sub_cancel_right] at e
  have mom (i : ℕ) (hi : i≤m) (k : ℕ) (hk : k<n) : endpointMoment K k (P i)=0 :=
    endpointMoment_zero_of_marked_defect ha ho L (by omega) (by have := pdeg i; omega) (marked i hi)
  have succShift (i : ℕ) : D ((D^i) x)=(D^(i+1)) x := by
    rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
  have adjacent_eq (i : ℕ) (hi : i<m) : ∃ u : K, X*P i-P (i+1)=u • G := by
    let T := X*P i-P (i+1)
    have td : T.natDegree≤a+1 := by
      change (X*P i-P (i+1)).natDegree ≤ a+1
      have td₁ : (X*P i).natDegree≤a+1 := natDegree_mul_le.trans
        (by rw [natDegree_X]; have := pdeg i; omega)
      simpa only [Nat.succ_eq_add_one, max_self] using natDegree_sub_le_of_le td₁ ((pdeg (i+1)).trans (Nat.le_succ a))
    have te : evalNodes A T=z (i+1)-D (z i) := by
      have e := congrArg D (dec i (by omega))
      rw [map_add,←evalNodes_X_mul A (P i),succShift i,←dec (i+1) (by omega)] at e
      simp only [T,map_sub]
      calc
        _ = (evalNodes A (X*P i)+D (z i))-evalNodes A (P (i+1))-D (z i) := by abel
        _ = _ := by rw [e]; abel
    have tW : evalNodes A T∈W := by
      rw [te]
      exact W.sub_mem (next (Submodule.mem_sup_left (hz (i+1))))
        (next (Submodule.mem_sup_right (Submodule.mem_map_of_mem (hz i))))
    obtain ⟨u,ud⟩ := reduction_by_next_degree td gd
    have e := separated (T-u • G) ud (by
      rw [map_sub,map_smul]
      exact W.sub_mem tW (W.smul_mem _ gW))
    exact ⟨u,sub_eq_zero.mp e⟩
  have p0 : P 0=0 := by
    apply NativeMoments.endpoint_moments_detect (pdeg 0)
      (origin_of_marked_defect_polynomial ha size (marked 0 (by omega)))
    intro k
    rw [←endpointMoment_apply]
    exact endpointMoment_chain P pos mom adjacent_eq gMom k (by have := k.isLt; omega)
  have gn : G.coeff (a+1)≠0 := by
    have nz : G≠0 := by intro h; rw [h,natDegree_zero] at gd; omega
    rw [←gd,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr nz
  have zero (i : ℕ) : i≤m → P i=0 := by
    induction i with
    | zero => exact fun _=>p0
    | succ i ih =>
      intro hi
      obtain ⟨u,e⟩ := adjacent_eq i (by omega)
      rw [ih (by omega),mul_zero,zero_sub] at e
      have co := congrArg (fun Q : K[X]=>Q.coeff (a+1)) e
      have pc : (P (i+1)).coeff (a+1)=0 := coeff_eq_zero_of_natDegree_lt
        ((pdeg (i+1)).trans_lt (Nat.lt_succ_self a))
      rw [coeff_neg,pc,neg_zero,Polynomial.coeff_smul,smul_eq_mul] at co
      have uz : u=0 := (mul_eq_zero.mp co.symm).resolve_right gn
      rw [uz,zero_smul] at e
      exact neg_eq_zero.mp e
  intro i hi
  have e := dec i hi
  rw [zero i hi,map_zero,zero_add] at e
  exact e ▸ hz i

end
end RKResearch.Certified.Graded.MarkedAdjacent
