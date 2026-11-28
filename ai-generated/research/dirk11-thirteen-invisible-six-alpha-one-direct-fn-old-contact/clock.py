"""Exact two-layer eliminants for an early ghost/old clean collision."""
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
r,c0,c1,c2=S.symbols('r c0 c1 c2')
H=5*r*r-5*c2*r+4*c1
F_r=100*r**3-75*c2*r*r+216*c0
W=5832*c0**2-3240*c0*c1*c2+675*c0*c2**3+640*c1**3-150*c1*c1*c2*c2
assert S.expand(S.resultant(H,F_r,r)-1000*W)==0
assert S.Poly(S.subresultants(H,F_r,r)[-2],r)==S.Poly(5400*c0-500*c1*c2+r*(-2000*c1+625*c2*c2),r)
def cs(f):
    q=S.Poly(f,c0,c1,c2);m=q.total_degree()
    return sum(a*C0**i*C1**j*C2**k*L**(m-i-j-k)for (i,j,k),a in q.terms())
def coeff(q):
    return S.Poly(q,V)
def gatecontents(name,f):
    raw=S.Poly(cs(f),B)
    content,g=raw.prem(F).primitive()
    print(name,'content',S.factor(content),'deg',g.degree(),flush=True)
    ls=S.subresultants(F,g,B)
    fs=S.factor_list(S.Poly(ls[-1],V))[1]
    print(name,'subresultant degrees',[len(u.all_coeffs())-1 for u in ls],
          'factors',[(q.degree(),j,q.nth(0))for q,j in fs],flush=True)
    return content,g,ls,fs

if __name__=='__main__':
    gatecontents('old z collision',W)
