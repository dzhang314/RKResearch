#!/usr/bin/env python3
"""Two independently factored and packed Q36 gates for the literal row at t."""
from fractions import Fraction
from math import lcm
from pathlib import Path
import json
import sys

import flint as fl
import sympy as S

field = json.loads(Path(sys.argv[1]).read_text())
out = Path(sys.argv[2])
X, Y, T = S.symbols('x y t')

def q(s):
    return s*(s-1)*(33*s**4-132*s**3+168*s**2-72*s+8)

def c(s):
    return s*(429*s**6-2574*s**5+5940*s**4-6600*s**3+3600*s**2-864*s+64)

def j(n, s):
    assert all(420 % (n+i) == 0 for i in (2,3,4,5))
    return ((420//(5+n))*s**(5+n)
        -(420//(4+n))*(1+X+Y)*s**(4+n)
        +(420//(3+n))*(X+Y+X*Y)*s**(3+n)
        -(420//(2+n))*X*Y*s**(2+n))

db = 5*X**2-5*X+1
dc = 2*X*Y-X-3*Y**2+2*Y
i0, i1 = j(0,1), j(1,1)
rn = X**3*(15*X**3-49*X**2+55*X-20)
kn = -30*X**3*(X-1)**3
ux = i0*(5*rn+db*c(X))+5*i1*kn
uy = 5*j(0,Y)+i0*c(Y)
G0 = db*q(X)*q(Y)*(Y-X)*(5*j(0,T)+i0*c(T))-q(T)*((Y-T)*q(Y)*ux+(T-X)*db*q(X)*uy)
G1 = q(X)*(i0*j(1,T)-i1*j(0,T))-490*dc*X**3*(X-1)**3*q(T)
d0 = 105*X*(X-1)*Y*(Y-1)*T*(T-1)*(Y-X)*(T-X)*(T-Y)*db
d1 = 490*X*(X-1)*T*(T-1)*(T-X)
to_poly = lambda a: S.Poly(a, X, Y, T, domain=S.ZZ)

def cleared(values):
    coeffs = [Fraction(*r) for r in values]
    d = lcm(*(r.denominator for r in coeffs))
    return d, fl.fmpz_poly([int(d*r) for r in coeffs])

dx, px = 1,fl.fmpz_poly([0,1])
dy, py = cleared(field["y"])
dt, pt = cleared(field["t"])
Q = fl.fmpz_poly(field["x"])
norm = lambda p:sum(abs(int(a)) for a in p)

for n, (full, factor) in enumerate(((G0,d0),(G1,d1))):
    reduced = to_poly(full).exquo(to_poly(factor))
    assert reduced*to_poly(factor)==to_poly(full)
    terms = [(i,j,k,int(c)) for (i,j,k),c in reduced.terms()]
    maxx,maxy,maxt = map(int, reduced.degree_list())
    ax=[px**i for i in range(maxx+1)]
    by=[py**j*dy**(maxy-j) for j in range(maxy+1)]
    ct=[pt**k*dt**(maxt-k) for k in range(maxt+1)]
    P=sum((c*ax[i]*by[j]*ct[k] for i,j,k,c in terms),fl.fmpz_poly())
    quo,rem=divmod(fl.fmpq_poly(P),fl.fmpq_poly(Q))
    assert not rem and all(x.denominator==1 for x in quo)
    quo=fl.fmpz_poly([int(a) for a in quo])
    assert P==Q*quo
    scale_bits=(sum(abs(c)*norm(by[j])*norm(ct[k]) for i,j,k,c in terms)+norm(Q)*norm(quo)).bit_length()+1
    terms_str=','.join(f'⟨{i},{j},{k},{c}⟩' for i,j,k,c in terms)
    quot_str=','.join(str(a) for a in quo)
    target=out/f'DIRK12MidpointOpeningTGate{n}.lean'
    target.write_text(f'''module

public import RKCert.ReviewedNative.IntegerPolyTrivarReplay
public import RKCert.ReviewedNative.DIRK12Q36RealMomentDataBridge

@[expose] public section

/-! Generated exact reduced gate {n} for the fourth live row. -/
namespace RKResearch.Certified.DIRK12MidpointForward.Opening

open IntegerPolyRootReplay IntegerPolyRootReplay.Packing
open DIRK12Q36Moments DIRK12MidpointRealInterval DirectedRatBox

def tTerms{n} : List TrivarTerm := [{terms_str}]
def tQuot{n} : ZP := [{quot_str}]
def tPackBase{n} : Nat := 2^{scale_bits}
def tPackExpr{n} : Expr := trivarClear dy dt {maxy} {maxt} tTerms{n} Y T

set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem tDegrees{n} :
    ∀ a∈tTerms{n}, a.j≤{maxy} ∧ a.k≤{maxt} := by
  have e : tTerms{n}.all (fun a => decide (a.j≤{maxy} ∧ a.k≤{maxt})) = true := by decide +kernel
  intro a ha
  exact of_decide_eq_true (List.all_eq_true.mp e a ha)

theorem tPack{n} :
    Packing.read (tPackBase{n}:Int) tPackExpr{n} =
      eval Q (tPackBase{n}:Int)*eval tQuot{n} (tPackBase{n}:Int) := by
  decide +kernel

theorem tBound{n} : bound tPackExpr{n}+norm Q*norm tQuot{n}<tPackBase{n} := by
  decide +kernel

theorem tGate{n}_zero {{x : ℝ}} (hx : realX x=0) :
    trivar tTerms{n} x (ratHorner yCoeffs x) (ratHorner tCoeffs x)=0 := by
  have e := quotient_from_packed x (q_at_real_root hx) tPack{n} tBound{n}
  have hy : eval Y x=(dy:ℝ)*ratHorner yCoeffs x := by
    rw [y_clear]
    exact eval_clearDen dy _ _ (denomOK_correct y_ok)
  have ht : eval T x=(dt:ℝ)*ratHorner tCoeffs x := by
    rw [t_clear]
    exact eval_clearDen dt _ _ (denomOK_correct t_ok)
  rw [tPackExpr{n},read_trivarClear x _ _ dy dt {maxy} {maxt} tTerms{n} Y T hy ht tDegrees{n}] at e
  have Dy : (dy:ℝ)≠0 := Nat.cast_ne_zero.mpr (by decide +kernel)
  have Dt : (dt:ℝ)≠0 := Nat.cast_ne_zero.mpr (by decide +kernel)
  exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero (pow_ne_zero _ Dy) (pow_ne_zero _ Dt))

end RKResearch.Certified.DIRK12MidpointForward.Opening

#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.tGate{n}_zero
''')
    print(n,"terms",len(terms),"degrees",(maxx,maxy,maxt),"substituted",P.degree(),
        "quotient",quo.degree(),"packing bits",scale_bits,"source bytes",target.stat().st_size)
