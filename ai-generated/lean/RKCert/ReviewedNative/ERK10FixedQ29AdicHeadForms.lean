module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadData

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed
open scoped Ring BigOperators

abbrev fr := Form.slot
def cForm : Form := fr ⟨[0,1],1⟩
def avgI : Rep := ⟨[1],avgDen⟩
def avgForm (f : Form → Form) : Form := fr avgI * Form.sumFin 10
  (fun i => Form.const (avgNumerator i.val) * f (Form.const i.val))

section
variable {R : Type*} [CommRing R]
open RKCert.ReviewedNative.IntegerHornerCertificate

@[simp] theorem cForm_val (x : R) : cForm.val x = x := by
  simp [cForm, Rep.val, coeval_cons, coeval, horner]

@[simp] theorem repZero_val (x : R) : repZero.val x = 0 := by
  simp [repZero, Rep.val, coeval, horner]

@[simp] theorem avgForm_val (x : R) (f : Form → Form) (g : R → R)
    (hh : ∀ y, (f y).val x = g (y.val x)) : (avgForm f).val x = avg g := by
  simp [avgForm, avgI, Rep.val, coeval_cons, coeval, horner, hh, avg, avgRaw]

end

def tThreeF (y : Form) : Form := (y-fr repF)*(y-6)*(y-fr repH)
def bPolyF (y : Form) : Form := (y-cForm)*(y-26)*(y-fr repE)*tThreeF y

def vCubicF (y : Form) : Form :=
  (75*cForm^3-108*cForm^2+45*cForm-5)
    -3*(175*cForm^3-244*cForm^2+97*cForm-10)*y
    +3*(350*cForm^3-476*cForm^2+183*cForm-18)*y^2
    -15*(42*cForm^3-56*cForm^2+21*cForm-2)*y^3

def phiF (y : Form) : Form :=
  (y-1)*(y-cForm)*(y-26)*(y-fr repE)*(vCubicF y-fr repBeta*tThreeF y)

def exprH : Form :=
  (8980-31725*cForm+32120*cForm^2)*fr repH-(6686-22450*cForm+21150*cForm^2)
def exprF : Form :=
  (2102470-14896392*cForm+42748688*cForm^2-61086000*cForm^3+36040380*cForm^4)*fr repF-
      (1051235*cForm-4965464*cForm^2+5011025*cForm^3)
def exprE : Form :=
  (cForm+cForm*(210*cForm^3-336*cForm^2+168*cForm-28)*26)*fr repE-cForm*(cForm-26)
def exprK : Form := avgForm (fun y => y*(y-1)*(y-cForm)^2*(y-15)*tThreeF y)
def exprQC : Form := fr repE*26*fr repK
def exprE0 : Form := avgForm (fun y => y*(y-1)*bPolyF y)
def exprE1 : Form := avgForm (fun y => y^2*(y-1)*bPolyF y)
def exprBeta : Form := tThreeF 0 * fr repBeta - vCubicF 0
def exprUU : Form := -(avgForm (fun y => y*phiF y))
def exprVV : Form := avgForm (fun y => phiF y)
def exprWW : Form := avgForm (fun y => y^2*phiF y)
def exprU : Form := fr repE0*15*cForm^2-2*fr repQC*cForm
def exprV : Form :=
  -(fr repE0*15*cForm)-fr repE0*cForm^2+fr repE1*cForm+2*fr repQC+fr repQC*cForm
def exprW : Form := -(fr repE1*15*cForm^2)+fr repQC*cForm^2
def exprDet : Form := fr repU*fr repVV-fr repV*fr repUU
def exprS : Form := fr repDet*fr repS-(fr repV*fr repWW-fr repW*fr repVV)
def exprQ : Form := fr repDet*fr repQ-(fr repW*fr repUU-fr repU*fr repWW)

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
