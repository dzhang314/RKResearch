"""Ordered-root norm for the mixed affine S,D,D vs two-singleton opener."""
import sympy as S
from itertools import product
from time import monotonic
from sympy.polys.rings import ring
from sympy.polys.fields import field
from exact_scalars import kk,l3

F0,s0=field('s',S.QQ)
F=F0.to_domain()
RR,Y,X=ring('beta,alpha',F)
AA,V=ring('V',F)
s=S.Symbol('s')
K=kk(X,s0,F0.one)
L=K[(0,3)]
K=K/RR(L)
S0=-K[(0,2)];T0=K[(0,1)]
Ug=RR(S0)-X
Vg=RR(T0)-X*Ug
Q=Y*Y-Ug*Y+Vg
assert K.LM==(0,3) and Q.LM==(2,0)

def ep(a,b,mode):return b-2*a if mode=='A' else (2-a-b)/4
def rev_rel(e,rr,s,mode):
    w=e-rr
    d=1-e
    z=s-e
    if mode=='A':return z*(w-4*d)+2*d*d
    if mode=='S':return z*w-d*d
    return 2*z*(w-2*d)*(w**3-3*w*w*d+d**3)-d*d*(-2*d**3+w*d*d+4*w*w*d-w**3)
def nrm(md,mr,j):
    roots=[X,Y,RR(S0)-X-Y]
    e=ep(X,Y,md)
    phi=rev_rel(e,roots[j],RR(s0),mr).rem([Q,K])
    a0=RR.from_dict({(0,ii):c for (jj,ii),c in phi.items() if jj==0})
    a1=RR.from_dict({(0,ii):c for (jj,ii),c in phi.items() if jj==1})
    A=(a0*a0+Ug*a0*a1+Vg*a1*a1)%K
    def uni(p):return AA.from_dict({(i,):c for (j,i),c in p.items()})
    n=uni(K).resultant(uni(A))
    assert n
    return phi,n
def resultants():
  for md,mr,j in product(('A','S'),('A','S','T'),range(3)):
    ti=monotonic()
    phi,n=nrm(md,mr,j)
    def hpoly(p):return S.Poly.from_dict(p.to_dict(),s,domain=S.QQ)
    f=hpoly(n.numer)
    g=hpoly(n.denom)
    g3=S.Poly(l3(s,1),s,domain=S.QQ)
    while (d:=g.gcd(g3)).degree()>0:g=g.exquo(d)
    assert g.degree()==0
    fs=f.factor_list()[1]
    print(md,mr,j,'norm factors',[(g.degree(),p) for g,p in fs],flush=True)
    yield md,mr,j,phi,n,fs

if __name__=='__main__':
    list(resultants())
