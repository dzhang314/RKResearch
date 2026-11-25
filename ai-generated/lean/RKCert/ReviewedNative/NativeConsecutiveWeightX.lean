module

public import RKCert.ReviewedNative.NativePrimitiveMoments
public import RKCert.ReviewedNative.NativePrimitiveRootTransport
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Consecutive weight-X orthogonal bands have coprime representatives.
Only the native formal primitive and its finite Cauchy detector are used;
no fixed scalar table, positivity, or order predicate on a field extension. -/
namespace RKResearch.Certified.Graded.NativeConsecutiveWeightX
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- The actual weight-X moment, as a linear form in its polynomial argument. -/
def moment {F : Type*} [Field F] (k : ℕ) : F[X] →ₗ[F] F :=
  (leval 1).comp (primitive.comp (LinearMap.mulLeft F ((X:F[X])^k*X)))

private theorem detect {P : K[X]} {n : ℕ} (d : P.natDegree≤n)
    (zero : ∀ i : Fin (n+1), moment i.val P=0) : P=0 := by
  apply NativeMoments.x_moments_detect d
  intro i
  have t := zero i
  change (primitive (((X:K[X])^i.val*X)*P)).eval 1=0 at t
  simpa only [mul_assoc] using t

private theorem mul_root_step (a : K) (k : ℕ) (P : K[X])
    (paid : moment k ((X-C a)*P)=0) : moment (k+1) P=a*moment k P := by
  have shift : moment (k+1) P=moment k (X*P) := by
    change (primitive (((X:K[X])^(k+1)*X)*P)).eval 1 =
      (primitive (((X:K[X])^k*X)*(X*P))).eval 1
    rw [show ((X:K[X])^(k+1)*X)*P=(X^k*X)*(X*P) by rw [pow_succ,mul_assoc]]
  rw [sub_mul, C_mul', map_sub, map_smul, smul_eq_mul, sub_eq_zero] at paid
  exact shift.trans paid

private theorem propagated {n : ℕ} {P : K[X]} {a : K}
    (paid : ∀ k<n, moment k ((X-C a)*P)=0) :
    ∀ k≤n, moment k P=a^k*moment 0 P := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hk
    rw [mul_root_step a k P (paid k (by omega)),ih (by omega),pow_succ']
    ring

/-- A common physical root is impossible even over an extension where
the two native orthogonal polynomials have been transported. -/
theorem no_common_root {n : ℕ} (pos : 0<n) (V W : K[X])
    (dv : V.natDegree=n) (dw : W.natDegree=n+1)
    (vPaid : ∀ k<n, moment k V=0) (wPaid : ∀ k<n+1, moment k W=0)
    (a : K) (va : V.IsRoot a) (wa : W.IsRoot a) : False := by
  have nv : V≠0 := by intro z; rw [z,natDegree_zero] at dv; omega
  have nw : W≠0 := by intro z; rw [z,natDegree_zero] at dw; omega
  obtain ⟨v,ev⟩ := (dvd_iff_isRoot.mpr va : X-C a ∣ V)
  obtain ⟨w,ew⟩ := (dvd_iff_isRoot.mpr wa : X-C a ∣ W)
  have vn : v≠0 := fun z => nv (by rw [ev,z,mul_zero])
  have wn : w≠0 := fun z => nw (by rw [ew,z,mul_zero])
  rw [ev,natDegree_mul (X_sub_C_ne_zero _) vn,natDegree_X_sub_C] at dv
  rw [ew,natDegree_mul (X_sub_C_ne_zero _) wn,natDegree_X_sub_C] at dw
  rw [ev] at vPaid
  rw [ew] at wPaid
  have vp := propagated vPaid
  have wp := propagated wPaid
  have vz : moment 0 v≠0 := by
    intro z
    apply vn
    apply detect (n:=n-1) (by omega)
    intro i
    rw [vp i.val (by have := i.isLt; omega),z,mul_zero]
  let T : K[X] := moment 0 v • w - moment 0 w • v
  have td : T.natDegree≤n := by
    have lw : (moment 0 v • w).natDegree≤n := (natDegree_smul_le _ _).trans (by omega)
    have lv : (moment 0 w • v).natDegree≤n := (natDegree_smul_le _ _).trans (by omega)
    simpa only [T,max_self] using natDegree_sub_le_of_le lw lv
  have tz : T=0 := by
    apply detect td
    intro i
    change moment i.val (moment 0 v • w - moment 0 w • v)=0
    have hi := i.isLt
    rw [map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul,
      wp i.val (by omega),vp i.val (by omega)]
    ring
  have eq : moment 0 v • w = moment 0 w • v := sub_eq_zero.mp tz
  have degrees := congrArg natDegree eq
  rw [natDegree_smul w vz] at degrees
  have small := natDegree_smul_le (moment 0 w) v
  omega

private theorem mapped_moment {E : Type*} [Field E] (f : K →+* E)
    (P : K[X]) (k : ℕ) (paid : moment k P=0) :
    moment k (P.map f)=0 := by
  have z : ((primitive (((X:K[X])^k*X)*P)).map f).eval (f 1)=0 := by
    rw [Polynomial.eval_map_apply]
    change f (moment k P)=0
    rw [paid,map_zero]
  change (primitive (((X:E[X])^k*X)*(P.map f))).eval 1=0
  simpa only [NativeRootTransport.primitive_map,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_X,map_one] using z

/-- The formal coprimality result holds over the original field, including
non-real fields. No normalized coefficient data are required. -/
theorem consecutive_coprime {n : ℕ} (pos : 0<n) (V W : K[X])
    (dv : V.natDegree=n) (dw : W.natDegree=n+1)
    (vPaid : ∀ k<n, moment k V=0) (wPaid : ∀ k<n+1, moment k W=0) :
    IsCoprime V W := by
  let E := AlgebraicClosure K
  let f := algebraMap K E
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K E V W).mpr
  intro a
  by_contra! h
  have vr : (V.map f).IsRoot a := by
    change (V.map (algebraMap K E)).eval a=0
    simpa only [eval_map_algebraMap] using h.1
  have wr : (W.map f).IsRoot a := by
    change (W.map (algebraMap K E)).eval a=0
    simpa only [eval_map_algebraMap] using h.2
  exact no_common_root pos (V.map f) (W.map f) (by simpa using dv) (by simpa using dw)
    (fun k hk => mapped_moment f V k (vPaid k hk))
    (fun k hk => mapped_moment f W k (wPaid k hk)) a vr wr

/-- The degree-six ordinary square obstruction, after cancelling the common X.
The G residue is W, the projected-square residue is V, and the paid mesh
coefficient is the nonzero low-degree multiplier Q. -/
theorem square_divisor_impossible (V W Q : K[X]) (dv : V.natDegree=5)
    (dw : W.natDegree=6) (dq : Q.natDegree≤3) (qn : Q≠0)
    (vPaid : ∀ k<5, moment k V=0) (wPaid : ∀ k<6, moment k W=0)
    (divide : W ∣ V*Q) : False := by
  have c := (consecutive_coprime (n:=5) (by decide) V W dv dw vPaid wPaid).symm
  have sm := natDegree_le_of_dvd (c.dvd_of_dvd_mul_left divide) qn
  omega

end
end RKResearch.Certified.Graded.NativeConsecutiveWeightX
