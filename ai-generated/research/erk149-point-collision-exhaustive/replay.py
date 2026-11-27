#!/usr/bin/env python3
"""Replay the all-live point-collision census' exact scalar identities."""
import sympy as S

a,b,c,t,z,k,ell,m,uc,ua,ub = S.symbols("a b c t z k ell m uc ua ub")
def check(lhs,rhs=0):
    assert S.cancel(lhs-rhs)==0, (lhs,rhs)

def card(t,x,v,w):
    return (t**4/4-(v+w)*t**3/3+v*w*t**2/2)/(x*(x-v)*(x-w))

ws = [card(t,c,a,b),card(t,a,b,c),card(t,b,c,a)]
for j in range(1,4):
    check(sum(w*x**j for w,x in zip(ws,[c,a,b])),t**(j+1)/(j+1))

D_c = S.Matrix([-c**2/2,-c**3/2,-c**3/3,0])
D_a = S.Matrix([k*c-a**2/2,a*(k*c-a**2/2),k*c**2-a**3/3,-k*c**2/2])
D_b = S.Matrix([ell*c+m*a-b**2/2,b*(ell*c+m*a-b**2/2),
                ell*c**2+m*a**2-b**3/3,-ell*c**2/2+m*(k*c-a**2/2)])
U,V = ws[1]*k+ws[2]*ell,ws[2]*m
r = ws[0]*D_c+ws[1]*D_a+ws[2]*D_b
check(r[0], c*U+a*V-t**3/6)
check(r[2], c**2*U+a**2*V-t**4/12)
check(r[3], -(c**2*U+a**2*V)/2+V*k*c)
check(r[1]-b*r[0], (a-b)*ws[1]*k*c-t**3*(3*t-4*b)/24)
deducedV = t**3*(t-2*c)/(12*a*(a-c))
deducedU = (t**3/6-a*deducedV)/c
check(c*deducedU+a*deducedV,t**3/6)
check(c**2*deducedU+a**2*deducedV,t**4/12)
deducedKC = (a-c)*a*t/(2*(t-2*c))
check(deducedV*deducedKC,t**4/24)
check((a-b)*ws[1]*deducedKC-t**3*(3*t-4*b)/24,
      c*t**3*(t-b)/(12*(t-2*c)))
check(card(z,c,a,b)*card(b,a,b,c)-card(z,a,b,c)*card(b,c,a,b),
      -b**3*z**2*(z-b)**2/(24*a*c*(a-b)*(a-c)*(b-c)))

nu,lam = t**2*(3*b-2*t)/(6*a*(b-a)), t**2*(2*t-3*a)/(6*b*(b-a))
check(nu*a+lam*b,t**2/2)
check(nu*a**2+lam*b**2,t**3/3)
K=6*a*b-4*(a+b)*t+3*t**2
check(nu*a**3+lam*b**3-t**4/4,-t**2*K/12)
check(nu*a**3+lam*b**2*(3*a-2*b),t**2*(3*a*b+a*t-2*b*t)/3)
X,Y=-lam*b**2/(2*a), t**3/(6*b)
check(-a**2*X/2-lam*a*b**2/4)
check(-nu*a**2/2+a*X+b*Y)
check(-nu*a**3/3+a**2*X+b**2*Y+lam*b**2*(3*a-2*b)/6,
      -t**2*(-3*a*b+2*a*t-b*t)/18)
for d,elim in [(2*b-a,9*a**2*b*(2*a-b)), (2*a-b,-9*a*b**2*(a-2*b))]:
    check(6*a*b*d**2-12*a*b*(a+b)*d+27*a**2*b**2,elim)
check(K.subs(b,2*a),3*(t-2*a)**2)
check(K.subs(a,2*b),3*(t-2*b)**2)
check((-t**2*K/12).subs(b,2*a),-t**2*(t-2*a)**2/4)
print("Exact singleton/paired anchor identities, rank-two cardinal minor and both resonance factors verified.")
