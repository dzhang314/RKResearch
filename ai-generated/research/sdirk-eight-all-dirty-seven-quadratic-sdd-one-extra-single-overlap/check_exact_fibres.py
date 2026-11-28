"""Exact fields of every irreducible one-overlap H projection."""
import sympy as S
from sympy.polys.rings import ring
from collections import Counter
from projection import project

def field(f):
    X=S.Symbol('H')
    p=S.Poly.from_dict({(int(i[0]),):int(a) for i,a in f.to_dict().items()},X,domain=S.QQ)
    assert p.is_irreducible
    if p.degree()==1:return S.QQ,S.QQ.convert(-p.nth(0)/p.nth(1))
    K=S.QQ.algebraic_field((p,X))
    return K,K.unit
def specialize(f,R,h):
    K=R.domain
    p={}
    for (i,j),a in f.to_dict().items():
        b=(int(j),)
        p[b]=p.get(b,K.zero)+K.convert(int(a))*(h**int(i) if i else K.one)
    return R.from_dict({i:a for i,a in p.items() if a})
def gcd(p,q):
    while q:p,q=q,p%q
    return p.monic() if p else p
def strip(p,guards):
    ret=[]
    for label,g in guards:
        while p and (a:=gcd(p,g)).degree()>0:
            p=p.exquo(a);ret.append((label,a.degree()))
    return p,ret
def run():
    count=Counter()
    for mo,fo,ro,ff,data in project():
      gi,E,X,Y=data
      for hp,n in ff:
        K,H=field(hp);R,d=ring('d',K)
        q=lambda p:specialize(p,R,H)
        G=gcd(gcd(q(E),q(X)),q(Y))
        assert G
        T,s=strip(G,[(key,q(z)) for key,z in gi])
        assert T.degree()==0
        assert sum(v for _,v in s)==G.degree()
        count[hp.total_degree(),G.degree()]+=1
        print(mo,fo,ro,'H degree',hp.total_degree(),'d gcd',G.degree(),
              'removed by',s,flush=True)
    assert count=={(1,1):2,(1,2):1,(2,0):9,(4,1):17,(8,1):7,(9,1):3},count
    print('all fifteen literal phase charts excluded; geometric census',count)
if __name__=='__main__':run()
