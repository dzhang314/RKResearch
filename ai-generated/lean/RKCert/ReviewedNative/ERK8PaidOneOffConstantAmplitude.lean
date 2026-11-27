module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffDependentSquare
public import RKCert.ReviewedNative.ERK8PaidOneOffCaseTwo
public import RKCert.ReviewedNative.ERK8PaidOneOffCaseThree

@[expose] public section

/-! # Constant-amplitude normal form of the reviewed physical one-off chart -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof
open RKResearch Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [EightUnits K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- The global amplitude and the actual first clean nonzero receiver.
No stage number or numerical ordering is imposed on the clocks. -/
structure ConstantAmplitude (A : Matrix (Fin s) (Fin s) K) (a d : K) (i j : Fin s) : Prop where
  origin : Origin A a i
  node : nodes A j = d
  clean : g A j = 0
  dn : d ≠ 0
  hj : h A j = twoHd a d
  first_h : FirstH A a (twoLam a d) j
  amplitude : (g A)^2 = baseAmp a • g A
  span_three : zeroSpace A 3 = Submodule.span K {g A, h A}
  q2 : mDef A 2 = (2*a/3) • g A + twoLam a d • h A

omit [EightUnits K] in
theorem amplitude_value {a : K} (eq : (g A)^2 = baseAmp a • g A)
    {i : Fin s} (hn : g A i ≠ 0) : g A i = baseAmp a := by
  have e := congrFun eq i
  simp only [Pi.pow_apply,Pi.smul_apply,smul_eq_mul] at e
  apply mul_right_cancel₀ hn
  simpa only [pow_two] using e

/-- The three square branches are decided on the original reviewed
tableau. Only the grade-four reverse capacity, not any feature relation,
is taken as an additional premise. -/
theorem constant_amplitude_of_single_off_of_capacity
    {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) K} {b : Fin (n+1) → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b) (hp : 8 ≤ p)
    (off : (offKnots A).card = 1) (cap : finrank K (treeSpace A 4) ≤ 8) :
    ∃ (a d : K) (i j : Fin (n+1)), ConstantAmplitude A a d i j := by
  obtain ⟨r3,r4,_,_⟩ := forward_minimal_ranks ha ho hp cap
  obtain ⟨a,i,lam,j,O,span3,q2,F⟩ := first_h_of_actual ha ho off (by omega) r3
  have sep : PolySeparated A 4 :=
    PolySeparated.of_coeff (explicit_coeff_separated ha ho (q:=4) (by omega))
  have amp : (g A)^2 = baseAmp a • g A := by
    by_cases sq : (g A)^2 ∈ zeroSpace A 3
    · exact constant_amplitude_of_dependent_square ha sep r3 r4 O span3 q2 F sq
    · have ind := independent_square_shape ha r3 r4 O F span3 sq
      by_cases on : g A j = 0
      · exact False.elim (independent_square_on_first_impossible ha sep O F q2 ind on)
      · exact False.elim (independent_square_off_first_impossible ha sep O F q2 ind on)
  rcases F.alternative with ⟨on,dn,hw,e⟩ | ⟨off,ne,_,_,_⟩
  · change lam = twoLam a (nodes A j) at e
    subst lam
    exact ⟨a,nodes A j,i,j,O,rfl,on,dn,hw,F,amp,span3,q2⟩
  · exact False.elim (ne (amplitude_value amp off))
/-- Only the sum of actual output coefficients of the off rows cancels.
No individual weight, and no weight of an on copy of the clock, is assumed zero. -/
theorem ConstantAmplitude.off_weight_cancel {a d : K} {i j : Fin s}
    (D : ConstantAmplitude A a d i j) (ho : HasOrder p A b) (paid : 3 ≤ p) :
    ∑ l ∈ Finset.univ.filter (fun l => g A l ≠ 0), b l = 0 := by
  classical
  have pay : probe A b 0 (g A) = 0 :=
    probe_zeroSpace ho (by omega : 0+2+1 ≤ p) (mDef_mem A 1)
  have amp : baseAmp a ≠ 0 := div_ne_zero
    (neg_ne_zero.mpr (pow_ne_zero 2 D.origin.a_ne)) (by eight_num)
  apply (mul_eq_zero.mp ?_).resolve_right amp
  rw [Finset.sum_mul]
  calc
    _ = ∑ l ∈ Finset.univ.filter (fun l => g A l ≠ 0), b l * g A l := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [amplitude_value D.amplitude (Finset.mem_filter.mp hl).2]
    _ = ∑ l, b l * g A l := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l _
      by_cases e : g A l = 0 <;> simp [e]
    _ = 0 := by
      simpa only [probe,row_apply,dotProduct,pow_zero,mul_one] using pay

end RKResearch.Certified.Graded.OneOff.PaidProof
