module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicWordInput

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical.HeadBi
open Packed Nonlinear Polynomial
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 400000

/-- Reduced Horner pair, with a constant and a first head-root part.
Each part is an exact guarded decic form, not a modular residue. -/
structure Bi where
  lo : Form
  hi : Form

def lift (f : Form) : Bi := ⟨f,0⟩
def A : Bi := ⟨0,1⟩
def B : Bi := ⟨Form.slot repS,-1⟩
def C0 : Bi := lift cForm

instance : Add Bi := ⟨fun p q => ⟨p.lo+q.lo,p.hi+q.hi⟩⟩
instance : Neg Bi := ⟨fun p => ⟨-p.lo,-p.hi⟩⟩
instance : Sub Bi := ⟨fun p q => p+(-q)⟩
instance (n : ℕ) : OfNat Bi n := ⟨lift (.const n)⟩
instance : Mul Bi := ⟨fun p q =>
  ⟨p.lo*q.lo-Form.slot repQ*(p.hi*q.hi),
    p.lo*q.hi+p.hi*q.lo+Form.slot repS*(p.hi*q.hi)⟩⟩

/-- Efficient Horner step at the first root of the monic quadratic. -/
def shiftA (p : Bi) : Bi :=
  ⟨- (Form.slot repQ*p.hi),p.lo+Form.slot repS*p.hi⟩
/-- At the other root, use (s-a)a=q once before expanding any powers. -/
def shiftB (p : Bi) : Bi :=
  ⟨Form.slot repS*p.lo+Form.slot repQ*p.hi,-p.lo⟩

def composeAt (step : Bi→Bi) : List Form→Bi
  | [] => 0
  | f::fs => lift f+step (composeAt step fs)

def muCoeffs : List Form := List.ofFn (fun i : Fin 7 => Form.slot (repMu i.val))
def pMuA : Bi := composeAt shiftA muCoeffs
def pMuB : Bi := composeAt shiftB muCoeffs

def scale (f : Form) (p : Bi) : Bi := ⟨f*p.lo,f*p.hi⟩
def shiftDiffB (t : Form) (p : Bi) : Bi := shiftB p-scale t p
def sForm := Form.slot repS
def qForm := Form.slot repQ
def headN0 : Form := 2*qForm*cForm
def headN1 : Form := 2*((-2)*qForm+cForm*sForm-cForm*cForm)

-- Reduce (a−1)(2ab−ac) and a(a−15) before expanding the moment degrees.
def firstFactor : Bi := ⟨2*(cForm-2)*qForm, 2*(2*qForm+cForm-cForm*sForm)⟩
def muFactor : Bi := ⟨-qForm,sForm-15⟩*pMuA
def ratioOne (y : Form) : Bi :=
  scale (muF y*y*(y-15)*(y-cForm)) firstFactor +
    scale ((y-1)*(headN0+headN1*y)) muFactor

def ratioB : Bi :=
  firstFactor * shiftDiffB cForm (shiftDiffB 15 (shiftB pMuB)) +
  scale headN0 (shiftDiffB 1 muFactor) + scale headN1 (shiftB (shiftDiffB 1 muFactor))
def ratioD : Bi := ratioOne 26
def ratioE : Bi := ratioOne (Form.slot repE)

def baseDen : ℕ :=
  ([repS.den,repQ.den,repE.den]++List.ofFn (fun i : Fin 7 => (repMu i.val).den)).foldl Nat.lcm 1

def guardedZero (p : Bi) : Bool :=
  Form.check baseDen (9*p.lo.degree+11) p.lo repZero &&
  Form.check baseDen (9*p.hi.degree+11) p.hi repZero

section Eval
variable {R : Type*} [CommRing R]

def Bi.val (p : Bi) (c a : R) : R := p.lo.val c+a*p.hi.val c

@[simp] theorem val_lift (c a : R) (f : Form) : (lift f).val c a=f.val c := by
  unfold lift Bi.val
  simp [Form.val]

@[simp] theorem val_A (c a : R) : A.val c a=a := by unfold A Bi.val; simp [Form.val]
@[simp] theorem val_B (c a : R) : B.val c a=repS.val c-a := by
  unfold B Bi.val; simp [Form.val,sub_eq_add_neg]
@[simp] theorem val_C0 (c a : R) : C0.val c a=c := by simp [C0]

@[simp] theorem val_nat (c a : R) (n : ℕ) :
    (OfNat.ofNat n : Bi).val c a=(n:R) := by
  change (lift (.const n)).val c a=_
  simp
@[simp] theorem val_add (c a : R) (p q : Bi) :
    (p+q).val c a=p.val c a+q.val c a := by
  change (p.lo+q.lo).val c+a*(p.hi+q.hi).val c =
    (p.lo.val c+a*p.hi.val c)+(q.lo.val c+a*q.hi.val c)
  simp only [Form.val_add]
  ring
@[simp] theorem val_zero (c a : R) : (0:Bi).val c a=0 := by
  simpa using val_nat c a 0

@[simp] theorem val_neg (c a : R) (p : Bi) :
    (-p).val c a=-(p.val c a) := by
  dsimp [Bi.val,instNegBi,Neg.neg]; ring
@[simp] theorem val_sub (c a : R) (p q : Bi) :
    (p-q).val c a=p.val c a-q.val c a := by
  change (p+(-q)).val c a=_
  simp [sub_eq_add_neg]

variable (c a : R)
variable (hquad : a^2-repS.val c*a+repQ.val c=0)
include hquad

theorem val_mul (p q : Bi) :
    (p*q).val c a=p.val c a*q.val c a := by
  change (p.lo*q.lo-Form.slot repQ*(p.hi*q.hi)).val c+
    a*(p.lo*q.hi+p.hi*q.lo+Form.slot repS*(p.hi*q.hi)).val c=_
  simp only [Bi.val,Form.val_sub,Form.val]
  linear_combination -(p.hi.val c)*(q.hi.val c)*hquad

theorem val_shiftA (p : Bi) : (shiftA p).val c a=a*p.val c a := by
  simp only [shiftA,Bi.val,Form.val_neg,Form.val_add,Form.val]
  linear_combination -(p.hi.val c)*hquad

theorem val_shiftB (p : Bi) : (shiftB p).val c a=(repS.val c-a)*p.val c a := by
  simp only [shiftB,Bi.val,Form.val_neg,Form.val_add,Form.val]
  linear_combination (p.hi.val c)*hquad

open RKCert.ReviewedNative.IntegerHornerCertificate

def evalList (x y : R) : List Form→R
  | [] => 0
  | f::fs => f.val x+y*evalList x y fs

omit hquad in
theorem compose_val (step : Bi→Bi) (y : R) (hs : ∀ p, (step p).val c a=y*p.val c a)
    (l : List Form) : (composeAt step l).val c a=evalList c y l := by
  induction l with
  | nil => simp [composeAt,evalList]
  | cons f fs h => simp [composeAt,evalList,hs,h]

omit hquad in
theorem mu_list (ρ : R→+*F) [IsLocalHom ρ]
    (hp : (decic R).eval c=0) (hc : ρ c=2) (y : R) :
    evalList c y muCoeffs=muValue c y := by
  simp only [muCoeffs,muValue,List.ofFn_succ,List.ofFn_zero,evalList,Form.val,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ]
  rw [exactMu ρ c hp hc 0 (by decide),exactMu ρ c hp hc 1 (by decide),
    exactMu ρ c hp hc 2 (by decide),exactMu ρ c hp hc 3 (by decide),exactMu ρ c hp hc 4 (by decide),
    exactMu ρ c hp hc 5 (by decide),exactMu ρ c hp hc 6 (by decide)]
  ring

theorem muA_val (ρ : R→+*F) [IsLocalHom ρ]
    (hp : (decic R).eval c=0) (hc : ρ c=2) :
    pMuA.val c a=(actualMu c).eval a := by
  rw [pMuA,compose_val c a shiftA a (val_shiftA c a hquad),mu_list c ρ hp hc,actualMu_eval]

theorem muB_val (ρ : R→+*F) [IsLocalHom ρ]
    (hp : (decic R).eval c=0) (hc : ρ c=2) :
    pMuB.val c a=(actualMu c).eval (repS.val c-a) := by
  rw [pMuB,compose_val c a shiftB (repS.val c-a) (val_shiftB c a hquad),
    mu_list c ρ hp hc,actualMu_eval]

omit hquad in
theorem guarded_sound (ρ : R→+*F) [IsLocalHom ρ]
    (hp : (decic R).eval c=0) {p : Bi} (hh : guardedZero p=true) :
    p.val c a=0 := by
  obtain ⟨hu,hv⟩ := Bool.and_eq_true_iff.mp hh
  have hL := (Form.check_sound ρ hp hu).symm
  have hH := (Form.check_sound ρ hp hv).symm
  rw [Bi.val,hL,hH,repZero_val,mul_zero,add_zero]

end Eval
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical.HeadBi
