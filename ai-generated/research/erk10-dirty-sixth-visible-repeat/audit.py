#!/usr/bin/env python3
"""Exact two-resultant and local-prime audit of the visible repeat."""
import sympy as S
import sys
X,v,y,t,a,b=S.symbols('X v y t a b')
F=S.factor;Q=S.Rational
x=2*v-1
w=Q(2,3)
Q0=X*(X-1)*(X-w)
E=(X-x)*(X-v)*(X-y)
V=X**2+a*X+b
H=Q0*E*V
I=lambda p,lo=0,hi=1:S.integrate(p,(X,lo,hi))
L=lambda p:S.fraction(F(p))[0]
hyp=S.Poly(y-x,y,v).as_expr()
ev=[I(H),I(X*H)]
M,N=S.linear_eq_to_matrix(ev,(a,b))
d=F(M.det())
da=F(N[0]*M[1,1]-N[1]*M[0,1]);db=F(M[0,0]*N[1]-M[1,0]*N[0])
bad=[F(S.resultant(d,s,y))for s in (da,db)]
assert all(f and not S.ground_roots(f,v)for f in bad)
print("singular-pivot resultants in v",bad,flush=True)
sub={a:F(da/d),b:F(db/d)}
U=F(V.subs(sub))
mu_x=F(I(Q0*(X-v)*(X-y)*V).subs(sub))
mu_y=F(I(Q0*(X-x)*(X-v)*V).subs(sub))
q2=(X-x)*(X-v)
Ix=I((X-v)**2,x,1)
D2=F(I(q2,y,1)*mu_y-Ix*mu_x)
lam=F(-Ix*mu_x)
Dx=3*v*lam
Dy=(x+v)*lam-mu_y*I(X*q2,y,1)
mu_t=I(Q0*E*(X+a+t)).subs(sub)
Dt=(y+x+v)*lam-mu_t*I((X-y)*(X-x)*(X-v),t,1)
R=F(S.rem(F((y-x)*(Dt-Dx)-(t-x)*(Dy-Dx)),U.subs(X,t),t))
D3=F(S.resultant(U.subs(X,t),R,t))
A0=S.factor_list(L(D2))[1]
A1=S.factor_list(L(D3))[1]
assert A0[0]==(hyp,1) and A1[0]==(hyp,2)
assert [(S.degree(f,v),S.degree(f,y),m)for f,m in A0[1:]]==[(7,2,1)]
assert [(S.degree(f,v),S.degree(f,y),m)for f,m in A1[1:]]==[(6,2,1),(14,8,1)]
new=[F(S.resultant(A0[1][0],g,y))for g,n in A1[1:]]
assert all(f and not S.ground_roots(f,v)for f in new)
print("regular D3 gate remaining bidegree",[(S.degree(f,v),S.degree(f,y))for f,m in A0[1:]],flush=True)
print("D4 t-resultant remaining bidegrees",[(S.degree(f,v),S.degree(f,y))for f,m in A1[1:]],flush=True)
print("final two v-resultant factor degrees",[[S.degree(f,v)for f,m in S.factor_list(R)[1]]for R in new],flush=True)
print("all four rational v-root sets empty",flush=True)
polys={f for R in bad+new for f,k in S.factor_list(L(R))[1]}
receipts=[]
for f in sorted(polys,key=lambda p:(S.degree(p,v),str(p))):
    full=[int(u)for u in reversed(S.Poly(f,v).all_coeffs())]
    p=next(p for p in S.primerange(2,10000)if full[-1]%p and
           all(sum(a*pow(x,i,p)for i,a in enumerate(full))%p for x in range(p)))
    a=[c%p for c in full]
    vals=[sum(c*pow(x,i,p)for i,c in enumerate(a))%p for x in range(p)]
    print("projective receipt",len(a)-1,p,a,vals,flush=True)
    receipts.append((p,a))
