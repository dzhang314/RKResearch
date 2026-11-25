module

public import RKCert.ReviewedNative.PolynomialCertificateAllWordCageRule
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact separated coefficients for the all-word sign verifier

For n=4,5, separate the common-stop kernel from the monic product
of the factor coordinates. No new numerical assumptions, positivity
tests, field semantics, or audit equality are introduced. -/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells.SeparatedCheck

open RKCert.ReviewedNative.PolynomialCertificate

structure Root4 (R : Type*) where
  a0 : R
  a1 : R
  a2 : R
  a3 : R

structure Root5 (R : Type*) where
  a0 : R
  a1 : R
  a2 : R
  a3 : R
  a4 : R

structure Weight4 (R : Type*) where
  w0 : R
  w1 : R
  w2 : R
  w3 : R
  w4 : R

structure Weight5 (R : Type*) where
  w0 : R
  w1 : R
  w2 : R
  w3 : R
  w4 : R
  w5 : R

/-- Ascending coefficients of (X-a)(X-b)(X-c)(X-d), with leading 1 omitted. -/
def roots4 {R : Type*} [CommRing R] (a b c d : R) : Root4 R :=
  let x := a*b
  let y := -(a+b)
  let z := c*d
  let w := -(c+d)
  ⟨x*z, x*w+y*z, x+y*w+z, y+w⟩

/-- Multiply the monic quartic by (X-a), still omitting the leading 1. -/
def extend5 {R : Type*} [CommRing R] (a : R) (s : Root4 R) : Root5 R :=
  ⟨-a*s.a0, s.a0-a*s.a1, s.a1-a*s.a2, s.a2-a*s.a3, s.a3-a⟩

def dot4 {R : Type*} [CommRing R] (s : Root4 R) (w : Weight4 R) : R :=
  s.a0*w.w0+s.a1*w.w1+s.a2*w.w2+s.a3*w.w3+w.w4

def dot5 {R : Type*} [CommRing R] (s : Root5 R) (w : Weight5 R) : R :=
  s.a0*w.w0+s.a1*w.w1+s.a2*w.w2+s.a3*w.w3+s.a4*w.w4+w.w5

-- If k is the factor-product degree, its column is the j coefficient of
-- (l+uY)^k(1+Y)^(n-k), times mu(e+k).
/-- The stop basis row at j, already multiplied by the shifted moments. -/
def stopKernel4 {R : Type*} [CommRing R] (mu : ℕ → R) (l u : R) (e : ℕ) : ℕ → Weight4 R
  | 0 => ⟨mu e, l*mu (e+1), l^2*mu (e+2), l^3*mu (e+3), l^4*mu (e+4)⟩
  | 1 => ⟨4*mu e, (3*l+u)*mu (e+1), (2*l^2+2*l*u)*mu (e+2), (l^3+3*l^2*u)*mu (e+3), 4*l^3*u*mu (e+4)⟩
  | 2 => ⟨6*mu e, (3*l+3*u)*mu (e+1), (l^2+4*l*u+u^2)*mu (e+2), (3*l^2*u+3*l*u^2)*mu (e+3), 6*l^2*u^2*mu (e+4)⟩
  | 3 => ⟨4*mu e, (l+3*u)*mu (e+1), (2*l*u+2*u^2)*mu (e+2), (3*l*u^2+u^3)*mu (e+3), 4*l*u^3*mu (e+4)⟩
  | 4 => ⟨mu e, u*mu (e+1), u^2*mu (e+2), u^3*mu (e+3), u^4*mu (e+4)⟩
  | _ => ⟨0, 0, 0, 0, 0⟩

/-- The stop basis row at j, already multiplied by the shifted moments. -/
def stopKernel5 {R : Type*} [CommRing R] (mu : ℕ → R) (l u : R) (e : ℕ) : ℕ → Weight5 R
  | 0 => ⟨mu e, l*mu (e+1), l^2*mu (e+2), l^3*mu (e+3), l^4*mu (e+4), l^5*mu (e+5)⟩
  | 1 => ⟨5*mu e, (4*l+u)*mu (e+1), (3*l^2+2*l*u)*mu (e+2), (2*l^3+3*l^2*u)*mu (e+3), (l^4+4*l^3*u)*mu (e+4), 5*l^4*u*mu (e+5)⟩
  | 2 => ⟨10*mu e, (6*l+4*u)*mu (e+1), (3*l^2+6*l*u+u^2)*mu (e+2), (l^3+6*l^2*u+3*l*u^2)*mu (e+3), (4*l^3*u+6*l^2*u^2)*mu (e+4), 10*l^3*u^2*mu (e+5)⟩
  | 3 => ⟨10*mu e, (4*l+6*u)*mu (e+1), (l^2+6*l*u+3*u^2)*mu (e+2), (3*l^2*u+6*l*u^2+u^3)*mu (e+3), (6*l^2*u^2+4*l*u^3)*mu (e+4), 10*l^2*u^3*mu (e+5)⟩
  | 4 => ⟨5*mu e, (l+4*u)*mu (e+1), (2*l*u+3*u^2)*mu (e+2), (3*l*u^2+2*u^3)*mu (e+3), (4*l*u^3+u^4)*mu (e+4), 5*l*u^4*mu (e+5)⟩
  | 5 => ⟨mu e, u*mu (e+1), u^2*mu (e+2), u^3*mu (e+3), u^4*mu (e+4), u^5*mu (e+5)⟩
  | _ => ⟨0, 0, 0, 0, 0, 0⟩

set_option maxHeartbeats 16000000 in
private theorem diag4_eq {R : Type*} [CommRing R] (mu : ℕ → R) (l u a b c d : R)
    (e j : ℕ) (hj : j ≤ 5) :
    diagonalCoeff mu l u [a,b,c,d] e j =
      dot4 (roots4 a b c d) (stopKernel4 mu l u e j) := by
  interval_cases j <;>
    simp [diagonalCoeff, shiftCoeff, dot4, roots4, stopKernel4, Nat.add_assoc] <;> ring

-- Use the quartic theorem at the four subcalls, then treat its four
-- coefficients as unrelated variables in the extension identity.
set_option maxHeartbeats 16000000 in
private theorem diag5_eq {R : Type*} [CommRing R] (mu : ℕ → R) (l u a b c d f : R)
    (e j : ℕ) (hj : j ≤ 5) :
    diagonalCoeff mu l u [a,b,c,d,f] e j =
      dot5 (extend5 a (roots4 b c d f)) (stopKernel5 mu l u e j) := by
  rw [diagonalCoeff]
  interval_cases j <;>
    simp (disch := omega) only [shiftCoeff, diag4_eq] <;>
    generalize h : roots4 b c d f = v <;>
    simp [dot4, dot5, extend5, stopKernel4, stopKernel5, Nat.add_assoc] <;> ring

def prepared4 (e : ℕ) (l u : ℤ) : List (Weight4 ℤ) :=
  (List.range 5).map (stopKernel4 (intMoment (e+5).factorial) l u e)

def prepared5 (e : ℕ) (l u : ℤ) : List (Weight5 ℤ) :=
  (List.range 6).map (stopKernel5 (intMoment (e+6).factorial) l u e)

def checkSign (positive : Bool) (z : ℤ) : Bool :=
  if positive then decide (0 < z) else decide (z < 0)

/-- The matrices depend only on stop, moment and factor count. One value
can be reused for every endpoint vector, not reconstructed per coefficient. -/
def vertexPrepared (positive : Bool) (e : ℕ) (l u : ℤ)
    (pre4 : List (Weight4 ℤ)) (pre5 : List (Weight5 ℤ)) : List ℤ → Bool
  | [a,b,c,d] =>
      let coeff := roots4 a b c d
      pre4.all (fun w => checkSign positive (dot4 coeff w))
  | [a,b,c,d,f] =>
      let coeff := extend5 a (roots4 b c d f)
      pre5.all (fun w => checkSign positive (dot5 coeff w))
  | rs => vertexPortOK positive e l u rs

private theorem all_congr_mem {X : Type*} (xs : List X) {g h : X → Bool}
    (he : ∀ x ∈ xs, g x = h x) : xs.all g = xs.all h := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.all_cons]
      rw [he x (List.mem_cons_self), ih (fun y hy => he y (List.mem_cons_of_mem x hy))]

theorem vertexPrepared_eq (positive : Bool) (e : ℕ) (l u : ℤ) :
    ∀ rs : List ℤ,
      vertexPrepared positive e l u (prepared4 e l u) (prepared5 e l u) rs =
        vertexPortOK positive e l u rs
  | [] => rfl
  | [a] => rfl
  | [a,b] => rfl
  | [a,b,c] => rfl
  | [a,b,c,d] => by
      change ((List.range 5).map (stopKernel4 (intMoment (e+5).factorial) l u e)).all
          (fun w => checkSign positive (dot4 (roots4 a b c d) w)) =
        (List.range 5).all (fun j => checkSign positive
          (diagonalCoeff (intMoment (e+5).factorial) l u [a,b,c,d] e j))
      rw [List.all_map]
      apply all_congr_mem
      intro j hj
      change checkSign positive (dot4 (roots4 a b c d)
          (stopKernel4 (intMoment (e+5).factorial) l u e j)) = _
      rw [← diag4_eq _ _ _ _ _ _ _ _ _ (Nat.le_of_lt (List.mem_range.mp hj))]
  | [a,b,c,d,f] => by
      change ((List.range 6).map (stopKernel5 (intMoment (e+6).factorial) l u e)).all
          (fun w => checkSign positive (dot5 (extend5 a (roots4 b c d f)) w)) =
        (List.range 6).all (fun j => checkSign positive
          (diagonalCoeff (intMoment (e+6).factorial) l u [a,b,c,d,f] e j))
      rw [List.all_map]
      apply all_congr_mem
      intro j hj
      change checkSign positive (dot5 (extend5 a (roots4 b c d f))
          (stopKernel5 (intMoment (e+6).factorial) l u e j)) = _
      rw [← diag5_eq _ _ _ _ _ _ _ _ _ _ (Nat.le_of_lt_succ (List.mem_range.mp hj))]
  | a::b::c::d::f::g::rs => rfl

/-- An optional explicit cache is accepted only with equality proofs for
its full ordered matrices. This can replace repeated reduction of a
literal stop kernel, but is not used as an external oracle. -/
theorem boxOfPrepared_eq (positive : Bool) (e : ℕ) (l u : ℤ)
    (boxes : List (ℤ × ℤ)) (pre4 : List (Weight4 ℤ)) (pre5 : List (Weight5 ℤ))
    (h4 : pre4 = prepared4 e l u) (h5 : pre5 = prepared5 e l u) :
    (factorCorners boxes).all (vertexPrepared positive e l u pre4 pre5) =
      boxPortOK positive e l u boxes := by
  rw [h4,h5]
  unfold boxPortOK
  exact List.all_congr rfl (vertexPrepared_eq positive e l u)

def boxOK (positive : Bool) (e : ℕ) (l u : ℤ) (boxes : List (ℤ × ℤ)) : Bool :=
  let pre4 := prepared4 e l u
  let pre5 := prepared5 e l u
  (factorCorners boxes).all (vertexPrepared positive e l u pre4 pre5)

theorem boxOK_eq (positive : Bool) (e : ℕ) (l u : ℤ) (boxes : List (ℤ × ℤ)) :
    boxOK positive e l u boxes = boxPortOK positive e l u boxes :=
  boxOfPrepared_eq positive e l u boxes _ _ rfl rfl

def signedOK (r : CageRow) (p : SignedPort) : Bool :=
  let f := gridInterval r p.port.reflected
  let stop := f p.port.stop
  boxOK p.positive p.port.e stop.1 stop.2 (p.port.factors.map f)

theorem signedOK_eq (r : CageRow) (p : SignedPort) : signedOK r p = p.ok r := by
  simp only [signedOK, SignedPort.ok, boxOK_eq]

def planCheck (words : List PortWord) (r : CageRow) (plan : List SignedPort) : Bool :=
  plan.all (signedOK r) &&
    words.all (fun w => plan.any (fun p => decide (p.port ∈ w.six)))

theorem planCheck_eq (words : List PortWord) (r : CageRow) (plan : List SignedPort) :
    planCheck words r plan = planOK words r plan := by
  have h := List.all_congr (rfl : plan = plan) (signedOK_eq r)
  rw [planCheck, planOK, h]

def groupCheck (r : CageRow) (plan : GroupPortPlan) : Bool :=
  plan.all (fun p => planCheck p.1 r p.2)

theorem groupCheck_eq (r : CageRow) (plan : GroupPortPlan) :
    groupCheck r plan = groupChecks r plan := by
  unfold groupCheck groupChecks
  exact List.all_congr rfl (fun p => planCheck_eq p.1 r p.2)

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells.SeparatedCheck
