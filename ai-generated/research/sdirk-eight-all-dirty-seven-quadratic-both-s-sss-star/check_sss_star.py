"""Exact SSS star vs necessarily SDD opposite opening at both singleton endpoints."""
import sympy as S
from sympy.polys.rings import ring
X=S.Symbol('h')
D=S.Poly(X**4-2*X**3+4*X**2+2*X-9,X,domain=S.QQ)
assert D.is_irreducible
T,w,h=ring('w,h',S.QQ)
m=h+2
L4=(w-h)**4-6*m*m*(w-h)**2/7+3*m**4/35
W=w*w-2
R=L4%W
a=T({(0,j):v for (i,j),v in R.items() if i==0})
b=T({(0,j):v for (i,j),v in R.items() if i==1})
assert -2*h*a-(1-2*h)*b==-16*h*(h**4-2*h**3+4*h*h+2*h-9)/35
for d in (0,4):
    K=S.QQ if d==0 else S.QQ.algebraic_field((D,X))
    T,w=ring('w',K)
    h=T(K.zero if d==0 else K.unit)
    m=h+2
    W=w*w-2
    L3=(w-h)**3-3*m*m*(w-h)/5
    L4=(w-h)**4-6*m*m*(w-h)**2/7+3*m**4/35
    ginv,j,g=(L4%W).gcdex(W)
    assert g==T.one and ((L4%W)*ginv)%W==T.one
    F=(L3*ginv)%W
    P=(L3-F*L4).exquo(W)
    assert F.degree()==1 and P.degree()==3
    if d==0:assert P==-w*(7*w*w-36)/26
    for phase,V in [('arith',2*w-(2*h+1)),('star',4*h-w)]:
        Dread=(P.compose(w,V)-P).exquo(V-w)
        g=P.gcd(Dread)
        if d==0 and phase=='star':
            assert g==w*w-S.QQ(36,7)
            r=lambda x:(1+2*x-x*x)/2
            assert r(1-w)==(2-w*w)/2
            print('h=0, rear star: literal paid D defect equals singleton graph',flush=True)
        else:
            assert g==T.one
            print('h field degree',1 if d==0 else d,phase,'unit divided-difference gcd',flush=True)
print('both-singleton SSS star excluded over characteristic-zero fields',flush=True)
