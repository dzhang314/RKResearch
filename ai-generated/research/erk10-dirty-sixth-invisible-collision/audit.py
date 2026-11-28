#!/usr/bin/env python3
"""Exact determinant and resultant for 0 and w collisions of the dirty relay."""
import sympy as S
import sys

X,y,t,h0,h1,h2=S.symbols('X y t h0 h1 h2')
Q=S.Rational
F=S.factor
w=Q(2,3)
root=X*(X-1)*(X-w)
I=lambda p,lo=0,hi=1:S.integrate(p,(X,lo,hi))
def solve(v):
    x=2*v-1
    V=X**3+h2*X**2+h1*X+h0
    U=(X-y)*V
    H=root*(X-x)*U
    mu_x=I(root*U)
    mu_y=I(root*(X-x)*V)
    q2=(X-x)*(X-v)
    M0=I((X-v)**2,x,1)
    assert F(M0-(1-x)**3/12)==0
    assert F(I(X*(X-v)**2,x,1)-v*M0)==0
    eq=[I(H),I(X*H),I(q2,y,1)*mu_y-M0*mu_x]
    M,N=S.linear_eq_to_matrix(eq,(h0,h1,h2))
    det=F(M.det())
    assert set(S.ground_roots(S.fraction(det)[0],y))=={x}
    sub={a:F(b)for a,b in zip((h0,h1,h2),M.inv()*N)}
    V1=F(V.subs(sub))
    lam=F((-M0*mu_x).subs(sub))
    dx=3*v*lam
    dy=(x+v)*lam-I(X*q2,y,1)*F(mu_y.subs(sub))
    qt=S.div(U,X-t,X)[0]
    mt=F(I(root*(X-x)*qt).subs(sub))
    dt=(y+x+v)*lam-mt*I((X-y)*(X-x)*(X-v),t,1)
    pressure=F((y-x)*(dt-dx)-(t-x)*(dy-dx))
    remainder=F(S.rem(pressure,V1.subs(X,t),t))
    res=F(S.resultant(V1.subs(X,t),remainder,t))
    assert set(S.ground_roots(S.fraction(res)[0],y))=={x}
    print("collision",v,"latest visible",x)
    print("nodal and D3 matrix determinant",det)
    print("resultant numerator",F(S.fraction(res)[0]))
    print("sole rational determinant/resultant root (excluded)",x)
    polys=[]
    for p in (det,res):
        for f,k in S.factor_list(S.fraction(p)[0])[1]:
            if S.degree(f,y)>1 and f not in polys:polys.append(f)
    receipts=[]
    for f in polys:
        cs=[int(v)for v in reversed(S.Poly(f,y).all_coeffs())]
        prime=next(p for p in S.primerange(2,10000)if cs[-1]%p and
          all(sum(a*pow(j,i,p)for i,a in enumerate(cs))%p for j in range(p)))
        vals=[sum(a*pow(j,i,prime)for i,a in enumerate(cs))%prime for j in range(prime)]
        print("projective local receipt",len(cs)-1,prime,cs,vals)
        receipts.append((prime,cs))
    return receipts

receipts=solve(Q(0))+solve(w)
if len(sys.argv)>1:
    from pathlib import Path
    data=',\n  '.join(f'({p}, ['+','.join(str(c)for c in a)+'])'for p,a in receipts)
    head='''namespace RKResearch.Certified.ERK10DirtySixthInvisibleCollisionMod

/-- Each pair gives a prime and ascending coefficients of a nonlinear
factor in the exact invisible-collision determinant/resultant computation. -/
def receipts : List (Int × List Int) := [
  '''
    foot=''']

def horner (p x : Int) (a : List Int) : Int :=
  a.foldr (fun c v => (c+x*v)%p) 0

def projectiveRootless (p : Int) (a : List Int) : Bool :=
  decide (a.getLast! % p ≠ 0) &&
  (List.range p.toNat).all (fun x => decide (horner p x a ≠ 0))

theorem all_projective_receipts :
    receipts.all (fun r => projectiveRootless r.1 r.2) = true := by
  decide +kernel

end RKResearch.Certified.ERK10DirtySixthInvisibleCollisionMod

#print axioms RKResearch.Certified.ERK10DirtySixthInvisibleCollisionMod.all_projective_receipts
'''
    Path(sys.argv[1]).write_text(head+data+foot)
