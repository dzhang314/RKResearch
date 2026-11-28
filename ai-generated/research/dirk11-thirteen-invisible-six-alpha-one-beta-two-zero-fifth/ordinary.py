"""Pure ordinary determinant for beta two with nonzero fifth diagonal."""
import sympy as S
Y,V,B,c0,c1,c2=S.symbols('Y V B c0 c1 c2')
R=Y**3+c2*Y**2+c1*Y+c0
J4=lambda x:42*x**4-84*x**3+56*x*x-14*x+1
J5=lambda x:132*x**5-330*x**4+300*x**3-120*x*x+20*x-1
L0=30*c0*Y+20*c1*Y**2+15*c2*Y**3+12*Y**4
L1=20*c0*Y**2+15*c1*Y**3+12*c2*Y**4+10*Y**5
D=L1-V*L0
N=J4(V)*D-D.subs(Y,V)*J4(Y)
ND=S.Poly(N,Y).exquo(S.Poly(Y-V,Y)).as_expr()
def vec(p):
 q=S.Poly(S.rem(p,R,Y),Y)
 return S.Matrix([q.nth(i)for i in range(3)])
f=S.factor(S.det(S.Matrix.hstack(vec(ND),vec(Y*ND),vec(J4(Y)))))
print('pure determinant factors',[(S.Poly(g,V,c0,c1,c2).total_degree(),e)for g,e in S.factor_list(f)[1]],flush=True)
U=S.Poly(J5(Y)*J4(V)-J5(V)*J4(Y),Y).exquo(S.Poly(Y-V,Y))
L=U.LC()
assert S.Poly(S.gcd(J4(Y),J5(Y)),Y).degree()==0
F=S.Poly(U.as_expr().subs(Y,B),B)
C2=U.nth(3)+B*L
C1=U.nth(2)+B*C2
C0=U.nth(1)+B*C1
def projection():
 q=S.Poly(f,c0,c1,c2)
 m=max(sum(i)for i,a in q.terms())
 poly=sum(a*C0**i*C1**j*C2**k*L**(m-i-j-k)for (i,j,k),a in q.terms())
 co,G=S.Poly(poly,B).prem(F).primitive()
 assert S.Poly(co,V).monic()==S.Poly(J4(V)**11,V).monic()
 assert G.degree()==3 and F.degree()==4
 print('content',S.factor(co),'B-degree',G.degree(),flush=True)
 res=S.subresultants(F,G,B)
 fs=S.factor_list(S.Poly(res[-1],V))[1]
 print('pure ordinary factors',[(h.degree(),e,int(h.nth(0)),str(h.as_expr()) if h.degree()<=12 else '')for h,e in fs],flush=True)
 assert S.Poly(S.resultant(F,G,B),V).monic()==S.Poly(res[-1],V).monic()
 assert sorted((h.degree(),e)for h,e in fs)==[(4,6),(4,12)]
 assert next(h for h,e in fs if e==12).monic()==S.Poly(J4(V),V).monic()
 em=S.Poly(S.cancel((J5(V)-J4(V))/(2*(V-1))),V).monic()
 assert next(h for h,e in fs if e==6).monic()==em
 print('Only the two forbidden ordinary factors survive over QQ.',flush=True)
 return G,res,fs
if __name__=='__main__':projection()
