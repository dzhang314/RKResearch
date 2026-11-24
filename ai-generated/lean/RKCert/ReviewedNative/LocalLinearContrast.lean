module

public import RKCert.ReviewedNative.ReverseJointMatch
public import RKCert.ReviewedNative.ReverseClockGain

@[expose] public section

/-! # Geometry and moment budget of a local linear contrast -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

def contrast (c b f : Fin s→K) (Q : K[X]) (i : Fin s) : K :=
  if f i=0 then b i*Q.eval (c i) else 0

theorem contrast_decompose {r j : ℕ} {U : Submodule K (Fin s→K)} {τ f : Fin s→K} {P Q : K[X]}
    (fit : LocalLinearTraces A b U τ f r j P Q)
    (inv : U.map (diag (reflectedClock A))≤U) :
    ∃ u∈U, contrast (reflectedClock A) b f Q=
      weightedEval (reflectedClock A) b Q-weightedEval (reflectedClock A) τ P-u := by
  let y := reflectedClock A
  let v := b*f-weightedEval y τ P
  have vU : v∈U := fit.weightTrace
  let t (i : Fin s) := (f i)⁻¹*v i
  let l (i : Fin s) := (if f i=0 then 0 else 1)*v i
  have tU : t∈U := clock_function_mem
    (fun _ hu=>fit.preserves (Submodule.mem_map_of_mem hu)) Inv.inv vU
  have lU : l∈U := clock_function_mem
    (fun _ hu=>fit.preserves (Submodule.mem_map_of_mem hu)) (fun x=>if x=0 then 0 else 1) vU
  let q (i : Fin s) := Q.eval (y i)*t i
  have qU : q∈U := clock_function_mem
    (fun _ hu=>inv (Submodule.mem_map_of_mem hu)) (fun x=>Q.eval x) tU
  refine ⟨v+q-l,U.sub_mem (U.add_mem vU qU) lU,?_⟩
  ext i
  have eq := congrFun fit.tauTrace i
  simp only [Pi.mul_apply,weightedEval_apply] at eq
  change τ i*f i=Q.eval (y i)*τ i at eq
  by_cases z : f i=0
  · simp [contrast,y,z,weightedEval_apply,v,q,t,l]
    ring
  · by_cases e : Q.eval (y i)=f i
    · have vz : q i=v i := by
        change Q.eval (y i)*((f i)⁻¹*v i)=v i
        rw [e,←mul_assoc,mul_inv_cancel₀ z,one_mul]
      simp only [Pi.sub_apply,Pi.add_apply,vz,weightedEval_apply]
      change contrast y b f Q i=Q.eval (y i)*b i-P.eval (y i)*τ i-(v i+v i-l i)
      have lv : l i=v i := by simp [l,z]
      rw [contrast,ite_eq_right z,lv,e]
      simp only [v,Pi.sub_apply,Pi.mul_apply,weightedEval_apply]
      ring
    · have a : τ i*(f i-Q.eval (y i))=0 := by linear_combination eq
      have τz : τ i=0 := (mul_eq_zero.mp a).resolve_right (sub_ne_zero.mpr (fun h=>e h.symm))
      have vv : v i=b i*f i := by simp [v,weightedEval_apply,τz]
      have tq : t i=b i := by
        change (f i)⁻¹*v i=b i
        rw [vv,mul_comm (b i),←mul_assoc,inv_mul_cancel₀ z,one_mul]
      have lv : l i=v i := by simp [l,z]
      have qv : q i=Q.eval (y i)*b i := by rw [show q i=Q.eval (y i)*t i from rfl,tq]
      change contrast y b f Q i=_
      simp only [contrast,ite_eq_right z,Pi.sub_apply,Pi.add_apply,weightedEval_apply,τz,mul_zero,
        sub_zero,lv,qv]
      change 0 = Q.eval (y i)*b i-(v i+Q.eval (y i)*b i-v i)
      ring

theorem weighted_primitive_band {v : Fin s→K} {j k : ℕ}
    (raw : v∈primitiveBack A b j) (P : K[X]) (d : P.natDegree≤k) :
    weightedEval (reflectedClock A) v P∈primitiveBack A b (j+k) := by
  apply weighted_band_of_primitive_seed raw k
  apply mem_weightedBand.mpr
  refine ⟨P,?_,rfl⟩
  by_cases z : P=0
  · simp [z]
  · exact (natDegree_lt_iff_degree_lt z).mp (Nat.lt_succ_of_le d)

theorem reflected_primitive_of_polynomial [CharZero K] {h : ℕ} (pos : 1≤h)
    (M : K[X]) (hM : M.natDegree≤h) :
    mat A.transpose (weightedEval (reflectedClock A) b M)-
      weightedEval (reflectedClock A) b (primitive M)∈primitiveBack A b h := by
  have e := reverse_primitive_next (A:=A) (b:=b) (h-1) M (by omega)
  rwa [show h-1+1=h by omega] at e

theorem reflected_clock_weighted_core {c u : Fin s→K}
    {U : Submodule K (Fin s→K)} (inv : U.map (diag c)≤U) (hu : u∈U) (M : K[X]) :
    weightedEval c u M∈U := by
  have eq : weightedEval c u M=(fun i=>M.eval (c i)*u i) := by ext i; simp
  rw [eq]
  exact clock_function_mem (fun _ hv=>inv (Submodule.mem_map_of_mem hv)) (fun x=>M.eval x) hu

theorem scaled_contrast_decomposition {c b τ W u : Fin s→K} {P Q M : K[X]}
    (e : W=weightedEval c b Q-weightedEval c τ P-u) :
    weightedEval c W M=
      weightedEval c b (M*Q)-weightedEval c τ (M*P)-weightedEval c u M := by
  ext i
  rw [weightedEval_apply,congrFun e i]
  simp only [Pi.sub_apply,weightedEval_apply,eval_mul]
  ring

set_option maxHeartbeats 550000 in
theorem weighted_reflected_annihilation_zero (ho : HasOrder p A b) {M : K[X]} {d g : ℕ}
    (degree : M.natDegree≤d) (e : d≤g) (budget : 2*d+1≤p)
    (zero : weightedEval (reflectedClock A) b M∈annih (treeSpace A g)) : M=0 := by
  let S := (1-X : K[X])
  let R := M.comp S
  have sb : S.natDegree≤1 := by
    change (1-X : K[X]).natDegree≤1
    exact (natDegree_sub_le _ _).trans (by simp)
  have rd : R.natDegree≤d := natDegree_comp_le.trans ((Nat.mul_le_mul degree sb).trans_eq (Nat.mul_one d))
  let a : Fin (d+1)→K := fun j=>R.coeff j.val
  have eval : evalNodes A R=coeffEval A d a := evalNodes_eq_coeffEval A R rd
  have tests (k : Fin (d+1)) :
      (∑ j : Fin (d+1), a j/((k.val+j.val+1:ℕ):K))=0 := by
    have deg : (X^k.val : K[X]).natDegree≤g := by rw [natDegree_X_pow]; have :=k.isLt;omega
    have w := mem_annih.mp zero _ (evalNodes_mem_treeSpace A (X^k.val) deg)
    have wTest : row (weightedEval (reflectedClock A) b M) (evalNodes A (X^k.val)) =
        probe A b k.val (evalNodes A R) := by
      simp only [row_apply,dotProduct,weightedEval_apply,evalNodes_apply,eval_pow,eval_X,
        R,eval_comp,S,eval_sub,eval_one,reflectedClock,Pi.sub_apply,Pi.one_apply]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [wTest,eval,probe_coeffEval ho (by have :=k.isLt;omega)] at w
    exact w
  have decode := moments_detect ho (n:=d+1) (d:=1) (by decide) (by omega)
    (fun j k=>by have :=j.isLt;have :=k.isLt;omega) a tests
  have zeroR : R=0 := by
    ext i
    rw [coeff_zero]
    by_cases h : i≤d
    · exact decode ⟨i,by omega⟩
    · exact coeff_eq_zero_of_natDegree_lt (rd.trans_lt (Nat.lt_of_not_ge h))
  have inv : S.comp S=X := by
    change ((1-X : K[X]).comp (1-X))=X
    rw [sub_comp,one_comp,X_comp]
    ring
  have q := congrArg (fun T : K[X]=>T.comp S) zeroR
  simpa only [R,comp_assoc,inv,comp_X,zero_comp] using q

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
