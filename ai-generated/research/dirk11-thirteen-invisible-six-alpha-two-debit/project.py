#!/usr/bin/env python3
"""Old-only exact projection for the nonzero fourth ordinary diagonal."""
import sympy as S
Y,V,B,c0,c1,c2,s=S.symbols('Y V B c0 c1 c2 s')
R=Y**3+c2*Y**2+c1*Y+c0
J4=lambda y:42*y**4-84*y**3+56*y*y-14*y+1
J5=lambda y:(2*y-1)*(66*y**4-132*y**3+84*y*y-18*y+1)
def v(p):
    f=S.Poly(S.rem(p,R,Y),Y)
    return S.Matrix([f.nth(i)for i in range(3)])
I=lambda p:S.Poly(p,Y).integrate().as_expr()
D0=S.factor(S.det(S.Matrix.hstack(v(I(Y*R)/Y),v(I(Y**2*R)/Y),v(J4(Y)))))
print('universal old determinant',D0,flush=True)
U=(S.Poly(J5(Y)*J4(V)-J5(V)*J4(Y),Y).exquo(S.Poly(Y-V,Y)))
L=U.LC()
Fc=S.Poly(U.as_expr().subs(Y,B),B)
C2=U.nth(3)+B*L
C1=U.nth(2)+B*C2
C0=U.nth(1)+B*C1
Fndef=-c0*c1*c1+(-12*c0*c1+12*c0*c2*c2-c1*c1*c2)*s+(-36*c0-4*c1*c2)*s*s+12*c2*s*s*s
projs=[]
for F,e in S.factor_list(D0)[1]:
    print('factor',F,'power',e,flush=True)
    if F==c0:continue
    f=S.Poly(F,c0,c1,c2)
    d=max(i+j+k for (i,j,k),q in f.terms())
    sc=sum(q*C0**i*C1**j*C2**k*L**(d-i-j-k)for (i,j,k),q in f.terms())
    pend=S.Poly(S.expand(sc),B).prem(Fc)
    co,low=pend.primitive()
    print('old clock content',S.factor(co),'B deg',low.degree(),flush=True)
    fa=S.Poly(S.resultant(Fc,low,B),V)
    factors=S.factor_list(fa)[1]
    print('base factors',[(e.degree(),i,str(e.as_expr()) if e.degree()<=12 else '') for e,i in factors],flush=True)
    projs.append((F,co,low,factors))

assert len(projs)==1
F,content,low,factors=projs[0]
assert S.Poly(content,V).monic()==S.Poly((V-1)**2*J4(V)**7,V).monic()
assert low.degree()==3
assert sorted((q.degree(),e)for q,e in factors)==[(4,2),(4,9),(8,2)]
F4,FJ,F8=(
    next(q for q,i in factors if q.degree()==4 and i==2),
    next(q for q,i in factors if q.degree()==4 and i==9),
    next(q for q,i in factors if q.degree()==8))
assert FJ.monic()==S.Poly(J4(V),V).monic()
assert S.expand(J5(V)-J4(V)-2*(V-1)*F4.as_expr())==0
assert S.expand(S.diff(J5(V),V)*J4(V)-J5(V)*S.diff(J4(V),V)-2*F8.as_expr())==0
print('All old determinant factors are incompatible with distinct ordinary nonendpoints',flush=True)
