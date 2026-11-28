"""Exact ordinary projections for the simple direct-Fn contacts."""
import sympy as S
Y,V,B=S.symbols('Y V B')
J4=lambda x:42*x**4-84*x**3+56*x*x-14*x+1
J5=lambda x:132*x**5-330*x**4+300*x**3-120*x*x+20*x-1
U=S.Poly(J5(Y)*J4(V)-J5(V)*J4(Y),Y).exquo(S.Poly(Y-V,Y))
L=U.LC()
F=S.Poly(U.as_expr().subs(Y,B),B)
C2=U.nth(3)+B*L
C1=U.nth(2)+B*C2
C0=U.nth(1)+B*C1
def project(f):
    content,G=S.Poly(f,B).prem(F).primitive()
    assert content==144
    ls=S.subresultants(F,G,B)
    facs=S.factor_list(S.Poly(ls[-1],V))[1]
    print('reduced gate',G.degree(),'subresultant degrees',[h.degree()for h in ls],flush=True)
    print('factors',[(u.degree(),e,str(u.as_expr())if u.degree()<=16 else u.nth(0))for u,e in facs],flush=True)
    return G,ls,facs
if __name__=='__main__':
    project(8*C1*L-3*C2*C2)
