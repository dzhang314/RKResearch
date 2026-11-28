#!/usr/bin/env python3
"""Generate integer polynomial Bezout identities; arithmetic outputs are Lean-checkable."""
import sympy as S
from sympy.polys.rings import ring
from math import lcm
x,y,z,v=S.symbols('x y z v')
def L(x):return 70*x**4-140*x**3+90*x*x-20*x+1
def D(x,y):return 70*y**3+(70*x-140)*y*y+(70*x*x-140*x+90)*y+70*x**3-140*x*x+90*x-20
def B(x,y,z):return 70*(z*z+z*y+y*y)+(70*x-140)*(z+y)+(70*x*x-140*x+90)
def gh(x,y):
    h=y-x
    return -2*x**3+h*x*x+4*x*h*h-h**3
def K(x,v,A):
    return sum(S.Poly(D(x,y),y).nth(i)*(x*A)**i*(1+v)**(3-i) for i in range(4))
def bez(base,axis,mod,f,g):
    K=S.QQ.algebraic_field((S.Poly(mod,base),base));R,Y=ring(str(axis),K)
    def inp(P):
        return sum((Y**j*(K.unit**i*K.convert(c)) for (i,j),c in S.Poly(P,base,axis).terms()),R.zero)
    def out(P):
        return S.expand(sum(K.to_sympy(c)*axis**i for (i,),c in P.items()))
    u,w,h=inp(f).gcdex(inp(g))
    assert h==R.one
    a,b=out(u),out(w)
    c,r=S.div(S.expand(1-a*f-b*g),mod,base)
    assert r==0
    n=lcm(*(int(S.denom(co)) for P in (a,b,c) for co in S.Poly(P,base,axis).coeffs()))
    aa,bb,cc=[S.expand(n*P) for P in (a,b,c)]
    assert S.expand(aa*f+bb*g+cc*mod-n)==0
    return n,aa,bb,cc
def fmt(e,s,t):
    vals=[]
    for (i,j),c in S.Poly(e,s,t).terms():
        c=int(c)
        if not c:continue
        a=[str(abs(c))]
        for p,z in ((s,i),(t,j)):
            if z==1:a.append(str(p))
            if z>1:a.append(str(p)+'^'+str(z))
        vals.append((c,'*'.join(a)))
    out=[]
    for i,(c,z) in enumerate(vals):
        if i==0:out.append(('-' if c<0 else '')+z)
        else:out.append((' - ' if c<0 else ' + ')+z)
    if not out:return "0"
    return ''.join(out)
cases=[
    ('silent',x,y,L(x),D(x,y),gh(x,y),'gauss x','pairDD x y','silentNumerator x y'),
    ('arithmetic',x,y,L(x),D(x,y),B(x,y,2*y-x),'gauss x','pairDD x y','tripleDD x y (2*y-x)'),
    ('star',x,y,L(x),D(x,y),B(x,y,4*x-y),'gauss x','pairDD x y','tripleDD x y (4*x-y)'),
    ('canceledArithmetic',v,x,v*v-2*v-1,L(x),K(x,v,1+2*v),'gapZero v','gauss x','canceledNumerator x v (1+2*v)'),
    ('canceledStar',v,x,v*v-2*v-1,L(x),K(x,v,3-v),'gapZero v','gauss x','canceledNumerator x v (3-v)')]
for name,s,t,mod,f,g,mstr,fstr,gstr in cases:
    n,a,b,c=bez(s,t,mod,f,g)
    print(f"theorem {name}Identity {{R : Type*}} [CommRing R] ({s} {t} : R) :")
    print(f"    ({fmt(a,s,t)})*({fstr}) +")
    print(f"    ({fmt(b,s,t)})*({gstr}) +")
    print(f"    ({fmt(c,s,t)})*({mstr}) = ({n} : R) := by")
    print("  unfold "+' '.join(dict.fromkeys(w.split()[0] for w in (fstr,gstr,mstr))))
    print("  ring")
    print()
