"""Exact two-stage ordinary projection for the direct-Fn slope contact."""
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
Z,s,c0,c1,c2=S.symbols('Z s c0 c1 c2')
H=2*c2*s*s+(30*c0-5*c1*c2)*s+5*c0*c1
Fn=-c0*(c1+6*s)**2+c2*s*(12*c0*c2-(c1+6*s)*(c1-2*s))
W=24300*c0**3-7560*c0*c0*c1*c2+90*c0*c0*c2**3+864*c0*c1**3+465*c0*c1*c1*c2*c2-80*c1**4*c2
assert S.expand(S.resultant(Fn,H,s)-32*c0*c1*c2**3*W)==0
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
def main():
    gatecontents('c1',c1)
    gatecontents('270c0+c2^3',270*c0+c2**3)
    gatecontents('main',W)
if __name__=='__main__': main()
