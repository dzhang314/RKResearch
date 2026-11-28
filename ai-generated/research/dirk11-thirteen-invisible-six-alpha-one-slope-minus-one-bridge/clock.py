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
c0,c1,c2=S.symbols('c0 c1 c2')
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

def check():
    d1,g1,l1,h1=gatecontents('c2',c2)
    d2,g2,l2,h2=gatecontents('225c0²+8c1³',225*c0*c0+8*c1**3)
    assert d1==12
    assert S.Poly(d2,V).monic()==S.Poly(J4(V)**3,V).monic()
    assert sorted((a.degree(),j)for a,j in h1)==[(4,2),(12,1)]
    assert sorted((a.degree(),j)for a,j in h2)==[(4,6),(36,1)]
    for seq in (h1,h2):
        assert next(h for h,j in seq if h.degree()==4).monic()==S.Poly(J4(V),V).monic()
    c=next(h for h,j in h1 if h.degree()==12)
    d=next(h for h,j in h2 if h.degree()==36)
    assert c.nth(0)==54123 and d.nth(0)==122268219830204443
    assert c.gcd(d).degree()==0
    print('The two ordinary denominator-loss conditions are exactly incompatible.',flush=True)
if __name__=='__main__':check()
