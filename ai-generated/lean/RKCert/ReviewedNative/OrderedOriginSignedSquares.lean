module

public import RKCert.ReviewedNative.FiniteOrderedSignWindows
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # An exact signed-square cut for three chronological clocks

No tableau, determinant, or fixed Jacobi data enters. The boundary
polynomials encode the apparent poles at zero and u algebraically. -/
namespace RKCert.ReviewedNative.OriginSignedSquares

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def threeHull (u v w : K) : K[X] := (X-C u)*(X-C v)*(X-C w)

structure ThreeClockMoments (P : K[X]) (u v w : K) : Prop where
  live : P ≠ 0
  degree : P.natDegree ≤ 5
  uNe : u ≠ 0
  vNe : v ≠ 0
  wNe : w ≠ 0
  vuNe : v ≠ u
  wuNe : w ≠ u
  wvNe : w ≠ v
  knotLive : P.eval u ≠ 0 ∧ P.eval v ≠ 0 ∧ P.eval w ≠ 0
  mesh : ∀ R : K[X], R.natDegree ≤ 6 →
    integral 0 1 (X*(1-X)*P*threeHull u v w*R) = 0
  first : integral 0 u (X*P) = 0
  second : integral 0 u (X^2*P) = 0
  next : integral 0 v (X*(X-C u)*P) = 0

private theorem integral_derivative_exact (T : K[X]) :
    integral 0 1 T.derivative = T.eval 1-T.eval 0 := by
  have eq : formalPrimitive T.derivative = T-C (T.eval 0) := by
    apply eq_of_derivative_and_eval_zero
    · simp
    · simp
  rw [integral_zero_left,eq,eval_sub,eval_C]

private theorem square_integral_pos {Q : K[X]} (qn : Q ≠ 0) (qd : Q.natDegree ≤ 8) :
    0 < integral 0 1 (Q^2) := by
  have dt : (Q^2).natDegree < 19 := (natDegree_pow_le_of_le 2 qd).trans_lt (by decide)
  obtain ⟨i,li⟩ := exists_nonzero_grid_sample zero_lt_one (pow_ne_zero 2 qn) dt
  have nonneg (j : Fin 19) : 0 ≤ (Q^2).eval (intervalPoint 0 1 j) := by
    rw [eval_pow]
    exact sq_nonneg _
  exact integral_pos_of_grid_samples zero_lt_one dt.le nonneg
    ⟨i,lt_of_le_of_ne (nonneg i) li.symm⟩

set_option maxRecDepth 4000
set_option maxHeartbeats 1500000

/-- Exact positive-square certificates apply before any sign assumption
on the intermediate chronological clock. In particular the first and
last numerical labels need not be ordered. -/
theorem ThreeClockMoments.signed_cut {P : K[X]} {u v w : K}
    (H : ThreeClockMoments P u v w) : 0 < w ∧ (0 < u → (1-u)*(u-w)<0) := by
  let a : K[X] := X*(C u-X)
  let b : K[X] := (1-X)*(X-C w)
  let F := formalPrimitive (a*P)
  have dF : F.derivative = a*P := derivative_formalPrimitive _
  have f0 : F.eval 0=0 := formalPrimitive_eval_zero _
  have fn : F ≠ 0 := by
    intro z
    rw [z,derivative_zero] at dF
    have a0 : a ≠ 0 :=
      mul_ne_zero X_ne_zero (by simpa only [neg_sub] using neg_ne_zero.mpr (X_sub_C_ne_zero u))
    exact (mul_ne_zero a0 H.live) dF.symm
  have ad : a.natDegree ≤ 2 :=
    natDegree_mul_le_of_le natDegree_X.le (natDegree_sub_le_of_le (p := C u) (q := X) (by simp : (C u).natDegree ≤ 1) natDegree_X.le)
  have fd : F.natDegree ≤ 8 := (natDegree_formalPrimitive_le _).trans
    (Nat.succ_le_succ (natDegree_mul_le_of_le ad H.degree))
  have fu : F.eval u=0 := by
    change (formalPrimitive (a*P)).eval u=0
    rw [←integral_zero_left]
    have e : a*P=u • (X*P)-X^2*P := by dsimp only [a]; rw [smul_eq_C_mul]; ring
    rw [e,map_sub,map_smul,H.first,H.second,smul_zero,sub_zero]
  have fv : F.eval v=0 := by
    change (formalPrimitive (a*P)).eval v=0
    rw [←integral_zero_left]
    have e : a*P=-(X*(X-C u)*P) := by dsimp only [a]; ring
    rw [e,map_neg,H.next,neg_zero]
  have xd : (X : K[X]) ∣ F := by rwa [X_dvd_iff,coeff_zero_eq_eval_zero]
  obtain ⟨A,fa⟩ := xd
  have an : A ≠ 0 := fun z => fn (by rw [fa,z,mul_zero])
  have atU : A.eval u=0 := by
    rw [fa,eval_mul,eval_X] at fu
    exact (mul_eq_zero.mp fu).resolve_left H.uNe
  obtain ⟨T,ft⟩ := (dvd_iff_isRoot.mpr (show IsRoot A u from atU))
  have tn : T ≠ 0 := fun z => an (by rw [ft,z,mul_zero])
  have atV : T.eval v=0 := by
    rw [fa,ft] at fv
    simp only [eval_mul,eval_X,eval_sub,eval_C] at fv
    exact (mul_eq_zero.mp ((mul_eq_zero.mp fv).resolve_left H.vNe)).resolve_left
      (sub_ne_zero.mpr H.vuNe)
  obtain ⟨J,fj⟩ := (dvd_iff_isRoot.mpr (show IsRoot T v from atV))
  have jn : J ≠ 0 := fun z => tn (by rw [fj,z,mul_zero])
  let B : K[X] := -(X*T)
  have fb : F=(C u-X)*B := by rw [fa,ft]; dsimp only [B]; ring
  have bn : B ≠ 0 := fun z => fn (by rw [fb,z,mul_zero])
  have da : A.natDegree ≤ 7 := by rw [fa,natDegree_X_mul an] at fd; omega
  have dt : T.natDegree ≤ 6 := by
    rw [ft, natDegree_mul (X_sub_C_ne_zero u) tn, natDegree_X_sub_C] at da
    omega
  have dj : J.natDegree ≤ 5 := by
    rw [fj, natDegree_mul (X_sub_C_ne_zero v) jn, natDegree_X_sub_C] at dt
    omega
  have db : B.natDegree ≤ 7 := by
    simp only [B,natDegree_neg,natDegree_X_mul tn]
    omega
  have moment (L : K[X]) (ld : L.natDegree ≤ 1) : integral 0 1 (b*P*F*L)=0 := by
    have eq : b*P*F*L = X*(1-X)*P*threeHull u v w*(J*L) := by
      rw [fa,ft,fj]
      dsimp only [b,threeHull]
      ring
    rw [eq]
    exact H.mesh (J*L) (natDegree_mul_le_of_le dj ld)
  let α := w/u
  let β := (1-u)*(u-w)/u
  let E₀ := F^2-C α*(X*A^2)+C β*((C u-X)*B^2)
  let E₁ := b*(X*A^2)
  have αu : α*u=w := by dsimp only [α]; field_simp [H.uNe]
  have cap : u+α+β=1+w := by dsimp only [α,β]; field_simp [H.uNe]; ring
  have poly : a-C α*(C u-X)+C β*X=b := by
    calc
      _ = -(X^2)+C (u+α+β)*X-C (α*u) := by
        dsimp only [a]
        simp only [map_add,map_mul]
        ring
      _ = b := by rw [αu,cap]; simp only [b,map_add,map_one]; ring
  have mf : (F-C α*A+C β*B)*a=b*F := by
    have eqA : A*a=(C u-X)*F := by rw [fa]; dsimp only [a]; ring
    have eqB : B*a=X*F := by rw [fb]; dsimp only [a]; ring
    calc
      _ = a*F-C α*(A*a)+C β*(B*a) := by ring
      _ = (a-C α*(C u-X)+C β*X)*F := by rw [eqA,eqB]; ring
      _ = _ := by rw [poly]
  have dXA : (X*A^2).derivative=C (2:K)*A*F.derivative-A^2 := by
    rw [fa]
    simp only [pow_two,derivative_mul,derivative_X,one_mul,map_ofNat]
    ring
  have dUB : ((C u-X)*B^2).derivative=C (2:K)*B*F.derivative+B^2 := by
    rw [fb]
    simp only [pow_two,derivative_mul,derivative_sub,derivative_C,derivative_X,zero_sub,map_ofNat]
    ring
  have dE₀ : E₀.derivative=C (2:K)*(b*P*F)+C α*A^2+C β*B^2 := by
    have dc (r : K) (R : K[X]) : (C r*R).derivative = C r*R.derivative := by
      rw [derivative_mul,derivative_C,zero_mul,zero_add]
    have dff : (F^2).derivative=F.derivative*F+F*F.derivative := by
      rw [pow_two,derivative_mul]
    calc
      _ = C (2:K)*((F-C α*A+C β*B)*F.derivative)+C α*A^2+C β*B^2 := by
        dsimp only [E₀]
        rw [derivative_add,derivative_sub,dc,dc,dXA,dUB,dff]
        simp only [map_ofNat]
        ring
      _ = _ := by
        rw [dF,show (F-C α*A+C β*B)*(a*P)=(b*F)*P by rw [←mul_assoc,mf]]
        ring
  have dbX : b.derivative*X-b=C w-X^2 := by
    simp only [b,derivative_mul,derivative_sub,derivative_one,derivative_X,derivative_C,
      zero_sub,sub_zero]
    ring
  have dE₁ : E₁.derivative=C (2:K)*(b*P*F*(C u-X))+C w*A^2-F^2 := by
    calc
      _ = C (2:K)*b*A*F.derivative+(b.derivative*X-b)*A^2 := by
        dsimp only [E₁]
        rw [derivative_mul,dXA]
        ring
      _ = _ := by rw [dF,dbX,fa]; dsimp only [a]; ring
  have a1 : F.eval 1=A.eval 1 := by rw [fa,eval_mul,eval_X,one_mul]
  have b1 : F.eval 1=(u-1)*B.eval 1 := by rw [fb,eval_mul,eval_sub,eval_C,eval_X]
  have bl : B.eval 0=0 := by
    rw [fb,eval_mul,eval_sub,eval_C,eval_X,sub_zero] at f0
    exact (mul_eq_zero.mp f0).resolve_left H.uNe
  have el : E₀.eval 0=0 := by simp [E₀,f0,bl]
  have er : E₀.eval 1=0 := by
    by_cases eu : u=1
    · have hF : F.eval 1=0 := by rw [←eu]; exact fu
      have hA : A.eval 1=0 := a1.symm.trans hF
      have beta0 : β=0 := by simp [β,eu]
      simp [E₀,hF,hA,beta0]
    have prod : (u-1)*E₀.eval 1=((u-1)*(1-α)+β)*(F.eval 1)^2 := by
      simp only [E₀,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow,one_mul]
      rw [←a1,b1]
      ring
    have z : (u-1)*(1-α)+β=0 := by
      dsimp only [α,β]
      field_simp [H.uNe]
      ring
    rw [z,zero_mul] at prod
    exact (mul_eq_zero.mp prod).resolve_left (sub_ne_zero.mpr eu)
  have l₁ : E₁.eval 0=0 := by simp [E₁]
  have r₁ : E₁.eval 1=0 := by simp [E₁,b]
  have mom0 : integral 0 1 (b*P*F)=0 := by
    simpa only [mul_one] using moment 1 (by simp)
  have mom1 := moment (C u-X) (natDegree_sub_le_of_le (p := C u) (q := X) (by simp : (C u).natDegree ≤ 1) natDegree_X.le)
  have i0 := integral_derivative_exact E₀
  rw [el,er,sub_zero,dE₀] at i0
  simp only [←smul_eq_C_mul,map_add,map_smul,mom0,smul_zero,zero_add] at i0
  have i1 := integral_derivative_exact E₁
  rw [l₁,r₁,sub_zero,dE₁] at i1
  simp only [←smul_eq_C_mul,map_sub,map_add,map_smul,mom1,smul_zero,zero_add] at i1
  have pA := square_integral_pos an (by omega : A.natDegree≤8)
  have pB := square_integral_pos bn (by omega : B.natDegree≤8)
  have pF := square_integral_pos fn fd
  change α*integral 0 1 (A^2)+β*integral 0 1 (B^2)=0 at i0
  change w*integral 0 1 (A^2)-integral 0 1 (F^2)=0 at i1
  have wp : 0<w := by
    rcases mul_pos_iff.mp ((sub_eq_zero.mp i1).symm ▸ pF) with ⟨pos,_⟩ | ⟨_,neg⟩
    · exact pos
    · exact ((not_lt_of_ge pA.le) neg).elim
  refine ⟨wp,fun up => ?_⟩
  have alphap : 0<α := div_pos wp up
  have neg : β<0 := by
    by_contra! nonneg
    exact (add_pos_of_pos_of_nonneg (mul_pos alphap pA) (mul_nonneg nonneg pB.le)).ne' i0
  have eq : β*u=(1-u)*(u-w) := by dsimp only [β]; field_simp [H.uNe]
  rw [←eq]
  exact mul_neg_of_neg_of_pos neg up

end
end RKCert.ReviewedNative.OriginSignedSquares
