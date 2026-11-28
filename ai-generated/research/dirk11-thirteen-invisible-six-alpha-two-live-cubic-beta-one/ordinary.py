#!/usr/bin/env python3
"""Exact parameter-free alpha-two ordinary determinant and elimination."""
import sympy as S
Y,V,B,c0,c1,c2=S.symbols('Y V B c0 c1 c2')
R=Y**3+c2*Y**2+c1*Y+c0
D=(Y-V)*R
J4=lambda x:42*x**4-84*x**3+56*x*x-14*x+1
J5=lambda x:132*x**5-330*x**4+300*x**3-120*x*x+20*x-1
L0=30*c0*Y+20*c1*Y**2+15*c2*Y**3+12*Y**4 # 60 L0
L1=20*c0*Y**2+15*c1*Y**3+12*c2*Y**4+10*Y**5 # 60 L1
def vec(p,B=D,n=4):
 f=S.Poly(S.rem(p,B,Y),Y)
 return [f.nth(i)for i in range(n)]
def d3(a,b,c):return S.det(S.Matrix.hstack(*(S.Matrix(x)for x in (a,b,c))))
f=S.factor(S.det(S.Matrix.hstack(*(S.Matrix(vec(q))for q in (J4(Y),L0,Y*L0,L1)))))
print('ordinary determinant factor degrees',[(S.Poly(g,V,c0,c1,c2).total_degree(),e)for g,e in S.factor_list(f)[1]],flush=True)
U=S.Poly(J5(Y)*J4(V)-J5(V)*J4(Y),Y).exquo(S.Poly(Y-V,Y))
L=U.LC()
F=S.Poly(U.as_expr().subs(Y,B),B)
C2=U.nth(3)+B*L
C1=U.nth(2)+B*C2
C0=U.nth(1)+B*C1
def projection():
 pp=S.Poly(f,c0,c1,c2)
 n=max(sum(i)for i,q in pp.terms())
 raw=sum(q*C0**i*C1**j*C2**k*L**(n-i-j-k)for (i,j,k),q in pp.terms())
 res=S.Poly(raw,B).prem(F)
 co,G=res.primitive()
 print('primitive ordinary content',S.factor(co),'B-degree',G.degree(),flush=True)
 seq=S.subresultants(F,G,B)
 fac=S.Poly(seq[-1],V)
 fs=S.factor_list(fac)[1]
 print('ordinary factors',[(u.degree(),e,str(u.as_expr()) if u.degree()<=12 else '')for u,e in fs],flush=True)
 return G,seq,fs
if __name__=='__main__': projection()
