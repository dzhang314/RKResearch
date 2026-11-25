module

public import RKCert.ReviewedNative.OrderedPreorderExtension
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.FieldDivision
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Interval preorder and a degree-lowering certificate

Draft. A failure to order an adjoined root in a sign gap produces a
positive-on-the-gap polynomial multiple with a strictly smaller
quotient. This is for arbitrary polynomials and uses no resultant.
-/
namespace RKCert.ReviewedNative.OrderedIntervalSquareCertificate

open Polynomial

noncomputable section
universe u
variable {K F : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

section Ring
variable [CommRing F]

/-- Finite sums of squares with nonnegative coefficients from the
ordered base, without any a priori order on the target ring. -/
inductive CoeffSOS (e : K →+* F) : F → Prop where
  | zero : CoeffSOS e 0
  | step (c : K) (cn : 0≤c) (x z : F) (rest : CoeffSOS e z) :
      CoeffSOS e (e c*x^2+z)

namespace CoeffSOS

variable {e : K →+* F} {a b : F}

theorem add (ha : CoeffSOS e a) (hb : CoeffSOS e b) : CoeffSOS e (a+b) := by
  induction ha with
  | zero => simpa only [zero_add] using hb
  | step c cn x z rest ih =>
      rw [add_assoc]
      exact .step c cn x _ ih

theorem image (c : K) (cn : 0≤c) : CoeffSOS e (e c) := by
  simpa only [one_pow,mul_one,add_zero] using
    (CoeffSOS.step c cn (1:F) 0 (CoeffSOS.zero (e := e)))

theorem one : CoeffSOS e (1:F) := by
  simpa only [map_one] using (image (e := e) (1:K) zero_le_one)

theorem square (x : F) : CoeffSOS e (x^2) := by
  simpa only [map_one,one_mul,add_zero] using
    (CoeffSOS.step (1:K) zero_le_one x 0 (CoeffSOS.zero (e := e)))

theorem scaleSquare (ha : CoeffSOS e a) (x : F) : CoeffSOS e (x^2*a) := by
  induction ha with
  | zero => simpa only [mul_zero] using (CoeffSOS.zero (e := e))
  | step c cn y z rest ih =>
      have h := CoeffSOS.step c cn (x*y) (x^2*z) ih
      convert h using 1 <;> ring

theorem scaleCoefficient (ha : CoeffSOS e a) (c : K) (cn : 0≤c) :
    CoeffSOS e (e c*a) := by
  induction ha with
  | zero => simpa only [mul_zero] using (CoeffSOS.zero (e := e))
  | step d dn y z rest ih =>
      have h := CoeffSOS.step (c*d) (mul_nonneg cn dn) y (e c*z) ih
      simpa only [map_mul,mul_add,mul_assoc] using h

theorem mul (ha : CoeffSOS e a) (hb : CoeffSOS e b) : CoeffSOS e (a*b) := by
  induction ha with
  | zero => simpa only [zero_mul] using (CoeffSOS.zero (e := e))
  | step c cn x z rest ih =>
      have first := (hb.scaleSquare x).scaleCoefficient c cn
      simpa only [add_mul,mul_assoc] using first.add ih

end CoeffSOS

end Ring

section Interval

variable [Field F]

/-- When u+v is the image of a positive width, sums of the three
shapes A+uB+vC are already a subsemiring. -/
def widthPreorder (e : K →+* F) (u v : F) (d : K) (dp : 0<d) (width : u+v=e d) :
    Subsemiring F where
  carrier := { x | ∃ A B C : F, CoeffSOS e A ∧ CoeffSOS e B ∧ CoeffSOS e C ∧
    x=A+u*B+v*C }
  zero_mem' := ⟨0,0,0,.zero,.zero,.zero,by ring⟩
  one_mem' := ⟨1,0,0,.one,.zero,.zero,by ring⟩
  add_mem' := by
    rintro x y ⟨A,B,C,ha,hb,hc,rfl⟩ ⟨D,E,G,hd,he,hg,rfl⟩
    exact ⟨A+D,B+E,C+G,ha.add hd,hb.add he,hc.add hg,by ring⟩
  mul_mem' := by
    rintro x y ⟨A,B,C,ha,hb,hc,rfl⟩ ⟨D,E,G,hd,he,hg,rfl⟩
    let k := e (d⁻¹)
    have h1 : k*e d = 1 := by
      dsimp only [k]
      rw [← map_mul,inv_mul_cancel₀ dp.ne',map_one]
    have huv : u*v=u*(k*v^2)+v*(k*u^2) := by
      calc
        u*v = (k*e d)*(u*v) := by rw [h1,one_mul]
        _ = k*(u+v)*(u*v) := by rw [width]
        _ = _ := by ring
    have Xs : CoeffSOS e (B*G+C*E) := (hb.mul hg).add (hc.mul he)
    have addU : CoeffSOS e (k*(v^2*(B*G+C*E))) :=
      (Xs.scaleSquare v).scaleCoefficient (d⁻¹) (inv_nonneg.mpr dp.le)
    have addV : CoeffSOS e (k*(u^2*(B*G+C*E))) :=
      (Xs.scaleSquare u).scaleCoefficient (d⁻¹) (inv_nonneg.mpr dp.le)
    refine ⟨A*D+u^2*(B*E)+v^2*(C*G),A*E+B*D+k*(v^2*(B*G+C*E)),
      A*G+C*D+k*(u^2*(B*G+C*E)),
      ((ha.mul hd).add ((hb.mul he).scaleSquare u)).add ((hc.mul hg).scaleSquare v),
      ((ha.mul he).add (hb.mul hd)).add addU,
      ((ha.mul hg).add (hc.mul hd)).add addV,?_⟩
    calc
      (A+u*B+v*C)*(D+u*E+v*G) =
        A*D+u^2*(B*E)+v^2*(C*G)+u*(A*E+B*D)+v*(A*G+C*D)+(u*v)*(B*G+C*E) := by ring
      _ = _ := by rw [huv]; ring

def gapPreorder (e : K →+* F) (a b : K) (ab : a<b) (α : F) : Subsemiring F :=
  widthPreorder e (α-e a) (e b-α) (b-a) (sub_pos.mpr ab) (by rw [map_sub]; ring)

theorem gapPreorder_square (e : K →+* F) (a b : K) (ab : a<b) (α x : F) :
    x^2∈gapPreorder e a b ab α :=
  ⟨x^2,0,0,CoeffSOS.square _,.zero,.zero,by ring⟩

theorem gapPreorder_base (e : K →+* F) (a b : K) (ab : a<b) (α : F)
    (c : K) (cn : 0≤c) : e c∈gapPreorder e a b ab α :=
  ⟨e c,0,0,CoeffSOS.image c cn,.zero,.zero,by ring⟩

theorem gapPreorder_left (e : K →+* F) (a b : K) (ab : a<b) (α : F) :
    α-e a∈gapPreorder e a b ab α :=
  ⟨0,1,0,.zero,.one,.zero,by ring⟩

theorem gapPreorder_right (e : K →+* F) (a b : K) (ab : a<b) (α : F) :
    e b-α∈gapPreorder e a b ab α :=
  ⟨0,0,1,.zero,.zero,.one,by ring⟩

end Interval

variable [Field F] [LinearOrder F] [IsStrictOrderedRing F]

theorem sos_eval_nonneg {P : K[X]} (hs : CoeffSOS (Polynomial.C : K →+* K[X]) P)
    (e : K →+* F) (ord : StrictMono e) (x : F) :
    0≤(P.map e).eval x := by
  induction hs with
  | zero => simp
  | step c cn Q z rest ih =>
      simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,map_C,
        eval_add,eval_mul,eval_pow,eval_C]
      have pos : 0≤e c := by simpa only [map_zero] using ord.monotone cn
      exact add_nonneg (mul_nonneg pos (sq_nonneg _)) ih

/-- Every square used in the field quotient has its own representative of
degree strictly less than the monic modulus. Normalize the representatives
before summing; the degree estimate is then uniform. -/
theorem lift_sos {g : K[X]} (monic : g.Monic) (pos : 0<g.natDegree)
    {x : AdjoinRoot g} (hs : CoeffSOS (AdjoinRoot.of g) x) :
    ∃ P : K[X], CoeffSOS (Polynomial.C : K →+* K[X]) P ∧
      P.natDegree ≤ 2*(g.natDegree-1) ∧ AdjoinRoot.mk g P=x := by
  have g1 : g≠1 := by
    intro he
    rw [he,natDegree_one] at pos
    exact (Nat.lt_irrefl 0) pos
  induction hs with
  | zero => exact ⟨0,.zero,by simp,by simp⟩
  | step c cn y z rest ih =>
      obtain ⟨Q,qSOS,qd,qval⟩ := ih
      let Y := AdjoinRoot.modByMonicHom monic y
      have yd : Y.natDegree ≤ g.natDegree-1 := by
        obtain ⟨A,rfl⟩ := AdjoinRoot.mk_surjective y
        have hh : Y.natDegree < g.natDegree := by
          simpa only [Y,AdjoinRoot.modByMonicHom_mk] using natDegree_modByMonic_lt A monic g1
        omega
      have yv : AdjoinRoot.mk g Y=y := AdjoinRoot.mk_leftInverse monic y
      refine ⟨C c*Y^2+Q,.step c cn Y Q qSOS,?_,?_⟩
      · have dY : (C c * Y^2).natDegree ≤ 2*(g.natDegree-1) := by
          exact (natDegree_C_mul_le _ _).trans (by simpa only [Nat.mul_comm] using natDegree_pow_le_of_le 2 yd)
        simpa only [max_self] using natDegree_add_le_of_le dY qd
      · rw [map_add,map_mul,map_pow,yv,qval] <;> rfl

/-- A failure of the interval preorder to be proper produces a nonzero
strictly positive multiple, with degree less than twice the modulus.
Positivity holds at **every** ordered transport of a point in the gap. -/
theorem improper_gap_certificate {g : K[X]} [Fact (Irreducible g)] (monic : g.Monic) (pos : 0<g.natDegree)
    {a b : K} (ab : a<b)
    (bad : (-1 : AdjoinRoot g) ∈ gapPreorder (AdjoinRoot.of g) a b ab (AdjoinRoot.root g)) :
    ∃ P : K[X], g∣P ∧ P.natDegree < 2*g.natDegree ∧
      ∀ (L : Type u) [Field L] [LinearOrder L] [IsStrictOrderedRing L]
        (e : K →+* L), StrictMono e → ∀ x : L, e a≤x → x≤e b → 0<(P.map e).eval x := by
  obtain ⟨U,V,W,hu,hv,hw,sum⟩ := bad
  obtain ⟨A,asq,ad,av⟩ := lift_sos monic pos hu
  obtain ⟨B,bsq,bd,bv⟩ := lift_sos monic pos hv
  obtain ⟨C',csq,cd,cv⟩ := lift_sos monic pos hw
  let P : K[X] := 1+A+(X-C a)*B+(C b-X)*C'
  have mkzero : AdjoinRoot.mk g P=0 := by
    simp only [P,map_add,map_sub,map_one,map_mul,AdjoinRoot.mk_X,av,bv,cv]
    change 1+U+(AdjoinRoot.root g-(AdjoinRoot.of g) a)*V+
      ((AdjoinRoot.of g) b-AdjoinRoot.root g)*W=0
    rw [show 1+U+(AdjoinRoot.root g-(AdjoinRoot.of g) a)*V+
        ((AdjoinRoot.of g) b-AdjoinRoot.root g)*W =
      1+(U+(AdjoinRoot.root g-(AdjoinRoot.of g) a)*V+
        ((AdjoinRoot.of g) b-AdjoinRoot.root g)*W) by ring,← sum,add_neg_cancel]
  have db : ((X-C a)*B).natDegree ≤ 1+2*(g.natDegree-1) :=
    natDegree_mul_le_of_le (by simp) bd
  have dc : ((C b-X)*C').natDegree ≤ 1+2*(g.natDegree-1) :=
    natDegree_mul_le_of_le ((natDegree_sub_le _ _).trans (by simp)) cd
  have d₁ : (1 : K[X]).natDegree ≤ 1+2*(g.natDegree-1) := by simp
  have dA : A.natDegree ≤ 1+2*(g.natDegree-1) := ad.trans (by omega)
  have dp : P.natDegree ≤ 1+2*(g.natDegree-1) := by
    simpa only [P, max_self] using natDegree_add_le_of_le (natDegree_add_le_of_le (natDegree_add_le_of_le d₁ dA) db) dc
  refine ⟨P,AdjoinRoot.mk_eq_zero.mp mkzero,dp.trans_lt (by omega),?_⟩
  intro L _ _ _ e ord x ax xb
  simp only [P,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_one,Polynomial.map_sub,
    map_X,map_C,eval_add,eval_mul,eval_one,eval_sub,eval_X,eval_C]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg zero_lt_one (sos_eval_nonneg asq e ord x))
      (mul_nonneg (sub_nonneg.mpr ax) (sos_eval_nonneg bsq e ord x)))
    (mul_nonneg (sub_nonneg.mpr xb) (sos_eval_nonneg csq e ord x))

end
end RKCert.ReviewedNative.OrderedIntervalSquareCertificate
