#!/usr/bin/env python3
"""Three exhaustive constant-seed paired clock chronologies, exact."""
import sympy as S
from flint import fmpz_mpoly_ctx,fmpz_poly,nmod_poly
import sys
from math import prod
r,q,d,x = S.symbols('r q d x')
a,b,c=S.Rational(1,7),S.Rational(1,5),S.Rational(1,3)
R,U=r*r,q*q
den=b-(R+U)*c+R*U
num=a-(R+U)*b+R*U*c
H=35*q**3*r**3+70*q**3*r**2+35*q**3*r+70*q**2*r**4+70*q**2*r**3+5*q**2*r**2+3*q**2-70*q*r**5+95*q*r**3-39*q*r-6*q-3*r**2-6*r-3
h=(x-r)*(x-q)
k=-((1+x)**2-4*(r+1)*(1+x)+2*(r+1)**2)
def I(f):
    return S.expand(sum(v/(j+1) for (j,),v in S.Poly(f,x).terms() if not j%2))
def T(f):
    return S.integrate(f,(x,-1,x))-(r+1)*f
def fresh_rel(mode):
    Y1=-r
    Y2,Y3 = [(-q,d),(d,-q),(d,-d)][mode]
    F2=(x-Y1)*(x-Y2)
    f=F2*(x+Y1+Y2+9*r+6)
    P=I(T(h)*f);Q=I(T(k)*f)
    W=k*P-h*Q
    return S.expand(I(W*F2*(x-Y3)))
def mod_squares(F):
    a=b=0
    D=(S.degree(F,d)//2)
    for (j,),v in S.Poly(F,d).terms():
        term=v*num**(j//2)*den**(D-j//2)
        if j%2:a+=term
        else:b+=term
    return S.Poly(S.expand(a),r,q),S.Poly(S.expand(b),r,q)
def rational_mod_cert(pol):
    for p in S.primerange(2,500):
        f=nmod_poly(pol.coeffs(),p)
        if f.degree()==pol.degree() and not f.roots():
            return p

def proj(mode):
    F=fresh_rel(mode)
    A,B=mod_squares(F)
    K=S.Poly(S.expand(den*B.as_expr()**2-num*A.as_expr()**2),r,q)
    print('before resultant',mode,K.degree_list(),flush=True)
    co,K=K.clear_denoms()
    content,K=K.primitive()
    P,fac=K.factor_list()
    assert K==P*prod(g**e for g,e in fac)
    print('factors before',[(g.degree_list(),e) for g,e in fac],flush=True)
    C=fmpz_mpoly_ctx.get(('r','q'),'lex')
    F=C.from_dict({ij:int(v) for ij,v in S.Poly(H,r,q).terms()})
    for p,e in fac:
        G=C.from_dict({ij:int(v) for ij,v in p.terms()})
        out=F.resultant(G,1)
        assert out
        L=out.to_dict()
        res=fmpz_poly([int(L.get((i,0),0)) for i in range(int(out.degrees()[0])+1)])
        z,raw=res.factor()
        assert res==z*prod(g**k for g,k in raw)
        receipts=[]
        for g,e in raw:
            if g.degree()==1:
                assert g[0] in (0,g[1])
                receipts.append((1,e,str(g)))
            else:
                prime=rational_mod_cert(g)
                assert prime
                receipts.append((g.degree(),e,prime))
        print('resultant factor grades',p.degree_list(),receipts,flush=True)

if __name__=='__main__':
    for mode in (0,1,2): proj(mode)
