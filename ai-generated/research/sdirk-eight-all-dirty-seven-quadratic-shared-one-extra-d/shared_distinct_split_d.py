"""Shared clock endpoints and distinct extra doubled labels, split quadratic graph."""
from shared_match_d import shape
from sympy.polys.fields import field
import sympy as S
from itertools import combinations_with_replacement
from flint import fmpz_mpoly_ctx as MC
from math import lcm
from time import monotonic

FF,d,e=field('d,e',S.QQ)
C=MC.get(('d','e'),'lex')
DD,EE=C.gens()
Theta=35*DD*DD*EE*EE-21*(DD*DD+EE*EE)+15
def integer(p):
    if not p:return C.constant(0)
    lc=lcm(*(int(S.Rational(c).q) for c in p.values()))
    return C.from_dict({tuple(map(int,k)):int(c*lc) for k,c in p.items()})
def strip(p,guards):
    assert p
    for n in guards:
        while (g:=p.gcd(n)).total_degree()>0:
            p,r=divmod(p,g);assert not r
    return p
def install(f,r):
    fd,sf,fs,ga=shape(d,f)
    rd,sr,rs,gb=shape(-e,r);sr=-sr
    L=lambda t:t**4-FF(6)*t*t/7+FF(3)/35
    W=lambda t:(t+d)*(t+e)
    r0=fs/W(sf);lam=r0*W(sr)/rs
    guard=ga+gb+[d,e,d-e,d+e,5*d*d-3,5*e*e-3,L(d),L(e),sf,sr,sf-d,sf-e,sr-d,sr-e,
                 sf-sr,W(sf),W(sr),lam,lam-1]
    if not all(guard):return None
    B=-4*L(0)/lam
    A0=-B*(1+lam)/2
    Ad=L(d)/fd-B*fd
    Ae=L(e)/(lam*rd)-B*lam*rd
    def q(t):
        return A0*(t-d)*(t-e)/(d*e)+Ad*t*(t-e)/(d*(d-e))+Ae*t*(t-d)/(e*(e-d))+B*r0*W(t)
    p,q=L(sf)-fs*q(sf),L(sr)-lam*rs*q(sr)
    gs=[integer(t.numer) for t in guard]
    ds=[integer(t.denom) for t in guard]
    for u in (p,q):
       assert strip(integer(u.denom),gs+ds).total_degree()==0
    p,q=strip(integer(p.numer),gs),strip(integer(q.numer),gs)
    return p,q,gs

def run():
 for f,r in combinations_with_replacement(('A2','A3','S'),2):
    start=monotonic()
    rr=install(f,r)
    if rr is None:
        print(f,r,'identical guard',flush=True);continue
    p,q,gs=rr
    print(f,r,'ingress',(p.degrees(),q.degrees()),round(monotonic()-start,2),flush=True)
    G=Theta.resultant(p,'e').gcd(Theta.resultant(q,'e'))
    assert G
    # Any h-only known nonzero factor can be removed now.
    G=strip(G,[s for s in gs if s.degrees()[1]==0])
    assert G.total_degree()==0
    print(f,r,'guarded projection gcd 1',round(monotonic()-start,2),flush=True)
 print('all shared distinct-extra split arithmetic/star phases excluded')
if __name__=='__main__':run()
