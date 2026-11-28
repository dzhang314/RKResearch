#!/usr/bin/env python3
"""Exact multiplication-matrix inverse plus denominator-free Lean certificates."""
import sympy as S
from itertools import product
from math import lcm
# Horner form keeps Lean elaboration depth independent of the number of terms.
def fmt(e,vs):
    if not vs:return str(int(e))
    if e==0:return '0'
    v,*rest=vs
    P=S.Poly(e,v)
    idx=int(P.degree())
    out=fmt(P.nth(idx),rest)
    for k in range(idx-1,-1,-1):
        q=fmt(P.nth(k),rest)
        out='('+out+')*'+str(v) if q=='0' else '('+out+')*'+str(v)+' + ('+q+')'
    return out

v,y,z=S.symbols('v y z')
Q=4*v**3-12*v*v+3*v+2
L=35*y**4-30*y*y+3
E=7*(z*z+y*y)-6
A=(1+z)*(1+2*v)
B=1+y
G=S.expand((2*v*v-4*v-1)*A**3+(-18*v*v+30*v+9)*A*A*B+
           (48*v*v-60*v-21)*A*B*B+(-24*v*v+24*v+9)*B**3)
for mode in ('mirror','oppositeSites'):
    if mode=='mirror':
        f=G.subs(z,-y);gs=[L,Q];vs=(y,v);ds=[4,3]
        labels=['centeredGauss y','gapCubic v']
        form='homGate v y (-y)'
    else:
        f=G;gs=[E,L,Q];vs=(z,y,v);ds=[2,4,3]
        labels=['mateSquares y z','centeredGauss y','gapCubic v']
        form='homGate v y z'
    def split(P):
        out=[]
        for w,g in zip(vs,gs):
            q,P=S.div(P,g,w)
            out.append(q)
        return out,S.expand(P)
    one=S.Poly(1,*vs)
    basis=[S.prod(x**n for x,n in zip(vs,k)) for k in product(*(range(d) for d in ds))]
    mat=[]
    for b in basis:
        top=S.Poly(split(b*f)[1],*vs)
        mat.append([top.coeff_monomial(x) for x in basis])
    coeff=S.Matrix(mat).T.inv()*S.Matrix([one.coeff_monomial(x) for x in basis])
    h=sum(c*b for c,b in zip(coeff,basis))
    ps,res=split(1-S.expand(h*f))
    assert res==0
    n=lcm(*(int(S.denom(c)) for e in [h,*ps] for c in S.Poly(e,*vs).coeffs()))
    hh=S.expand(n*h);cs=[S.expand(n*x) for x in ps]
    assert S.expand(hh*f+sum(a*b for a,b in zip(cs,gs))-n)==0
    print('set_option maxHeartbeats 4000000 in')
    print('set_option maxRecDepth 4096 in')
    print(f'theorem {mode}Bézout {{R : Type*}} [CommRing R] ('+' '.join(str(x) for x in vs)+' : R) :')
    print('    ('+fmt(hh,vs)+')*('+form+') +')
    for i,(a,q) in enumerate(zip(cs,labels)):
        print('    ('+fmt(a,vs)+')*('+q+')'+(' +' if i+1<len(cs) else ' = ('+str(n)+' : R) := by'))
    print('  unfold homGate '+' '.join(w.split()[0] for w in labels))
    print('  ring\n')
