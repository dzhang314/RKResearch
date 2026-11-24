module

public import RKCert.ERKOrderNineOneOffEndpointData

@[expose] public section

namespace RKCert.Paired.OneOff
open RKCert.GoodPrimeDense

/-- Signed coefficient grid, ascending powers of the inner variable d
then ascending powers of the outer variable z. -/
def readGrid {R : Type*} [CommRing R] (d z : R) (G : List (List Int)) : R :=
  GoodPrimeDense.read (GoodPrimeDense.read (Int.castRingHom R) d) z G

private abbrev io := dense (scalar Int)

private theorem grid_add {R : Type*} [CommRing R] (d z : R) (a b : List (List Int)) :
    readGrid d z (plus io a b) = readGrid d z a + readGrid d z b :=
  read_plus ((Sound.scalar (Int.castRingHom R)).dense d) z a b

private theorem grid_mul {R : Type*} [CommRing R] (d z : R) (a b : List (List Int)) :
    readGrid d z (times io a b) = readGrid d z a * readGrid d z b :=
  read_times ((Sound.scalar (Int.castRingHom R)).dense d) z a b

private theorem grid_neg {R : Type*} [CommRing R] (d z : R) (a : List (List Int)) :
    readGrid d z (opposite io a) = -readGrid d z a :=
  read_opposite ((Sound.scalar (Int.castRingHom R)).dense d) z a

def endpointE {R : Type*} [CommRing R] (d : R) : R := readGrid d 0 endpointEData

def endpointF {R : Type*} [CommRing R] (d z : R) : R := readGrid d z endpointFData

def endpointG {R : Type*} [CommRing R] (d z : R) : R := readGrid d z endpointGData

set_option maxRecDepth 4000 in
theorem endpointE_formula {R : Type*} [CommRing R] (d : R) :
    endpointE d = 4704*d^6-10584*d^5+9212*d^4-3990*d^3+910*d^2-105*d+5 := by
  simp [endpointE,readGrid,endpointEData,GoodPrimeDense.read]
  ring

set_option maxRecDepth 4000 in
theorem endpointG_formula {R : Type*} [CommRing R] (d z : R) :
    endpointG d z =
      4*d^3+(2*d^2-48*d^3)*z+(-9*d+216*d^2-1512*d^3+4480*d^4-4032*d^5)*z^2+
         (3-72*d+504*d^2-1344*d^3+1008*d^4)*z^3 := by
  simp [endpointG,readGrid,endpointGData,GoodPrimeDense.read]
  ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem checked_division :
    times io [[0,-1],[1]] endpointBData = plus io endpointFData (opposite io endpointEData) :=
  of_decide_eq_true rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem checked_bezout :
    plus io (plus io (times io endpointBData endpointUData) (times io endpointGData endpointVData))
      (times io endpointEData endpointWData) = [[631060]] :=
  of_decide_eq_true rfl

theorem endpointF_sub_diagonal {R : Type*} [CommRing R] (d z : R) :
    (z-d)*readGrid d z endpointBData = endpointF d z-endpointE d := by
  have h := congrArg (readGrid d z) checked_division
  rw [grid_mul,grid_add,grid_neg] at h
  have h1 : readGrid d z [[0,-1],[1]] = z-d := by
    simp [readGrid,GoodPrimeDense.read,sub_eq_add_neg]
    ring
  have h2 : readGrid d z endpointEData = endpointE d := by
    simp [endpointE,readGrid,GoodPrimeDense.read,endpointEData]
  exact (by simpa only [h1,h2,endpointF,sub_eq_add_neg] using h)

theorem endpointF_diagonal {R : Type*} [CommRing R] (d : R) :
    endpointF d d = endpointE d := by
  have h := endpointF_sub_diagonal d d
  rw [sub_self,zero_mul,eq_comm,sub_eq_zero] at h
  exact h

/-- Exact characteristic-zero exclusion of the rank-zero endpoint
coefficient in the one-off chart; no sign or analytic root assumption. -/
theorem endpoint_nonzero {K : Type*} [Field K] [CharZero K] {d z : K}
    (hne : z ≠ d) (hd : endpointF d d = 0) (hz : endpointF d z = 0)
    (hg : endpointG d z = 0) : False := by
  have he : endpointE d = 0 := (endpointF_diagonal d).symm.trans hd
  have hb : readGrid d z endpointBData = 0 := by
    have h := endpointF_sub_diagonal d z
    rw [hz,he,sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)
  have hc := congrArg (readGrid d z) checked_bezout
  rw [grid_add,grid_add,grid_mul,grid_mul,grid_mul,hb] at hc
  have he' : readGrid d z endpointEData=0 := by
    have e : readGrid d z endpointEData=endpointE d := by
      simp [endpointE,readGrid,GoodPrimeDense.read,endpointEData]
    rwa [e]
  change readGrid d z endpointGData=0 at hg
  rw [hg,he',zero_mul,zero_mul,zero_mul,zero_add,zero_add] at hc
  have zero : (0:K)=631060 := by
    simp [readGrid,GoodPrimeDense.read] at hc
  exact (by norm_num : (631060:K)≠0) zero.symm

end RKCert.Paired.OneOff
