"""Exact terminal/extra single-overlap fields."""
from projection import project
import sympy as S
def K_h(f):
    X=S.Symbol('h')
    p=S.Poly.from_dict({(int(ix[0]),):int(c) for ix,c in f.to_dict().items()},X,domain=S.QQ)
    assert p.is_irreducible
    if p.degree()==1:return S.QQ,S.QQ.convert(-p.nth(0)/p.nth(1))
    K=S.QQ.algebraic_field((p,X))
    return K,K.unit
def value(p,x):
    K=p.ring.domain
    acc=K.zero
    for c in p.to_dense():acc=acc*x+c
    return acc
def gcd(p,q):
    while q:p,q=q,p%q
    return p.monic() if p else p
def strip(p,gs):
    for g in gs:
        while p and (q:=gcd(p,g)).degree()>0:p=p.exquo(q)
    return p
def specialize(f,R,xs):
    # None means leave one coordinate as R's variable.
    K=R.domain
    powers={}
    for i,a in enumerate(xs):
       if a is not None:powers[i]=[a**j if j else K.one for j in range(f.degrees()[i]+1)]
    terms={}
    for ix,c in f.to_dict().items():
      g=K.convert(int(c));m=0
      for i,e in enumerate(ix):
        if xs[i] is None:m+=int(e)
        else:g*=powers[i][e]
      terms[(m,)]=terms.get((m,),K.zero)+g
    return R.from_dict({i:c for i,c in terms.items() if c})

from sympy.polys.rings import ring
from flint import fmpq_poly
def spec_H(P,R,h):
    K=R.domain
    mod=fmpq_poly(list(reversed(K.mod.to_list()))) if hasattr(K,'mod') else fmpq_poly([-h,1])
    cs={}
    for (i,j),a in P.to_dict().items():cs.setdefault(int(j),{})[int(i)]=int(a)
    ans={}
    for j,q in cs.items():
        a=[0]*(1+max(q))
        for i,c in q.items():a[i]=c
        b=fmpq_poly(a)%mod
        if b:
           ans[(j,)]=K.new(list(reversed(b.coeffs()))) if hasattr(K,'mod') else K.convert(b[0])
    return R.from_dict(ans)
def ggcd(a,b):
    if b:b=b.monic()
    while b:a,b=b,(a%b)
    return a.monic() if a else a
def run():
    hits=0;seen=set()
    for w,fo,ro,ff,rows,gs,dta in project():
       assert w=='terminal'
       seen.add((fo,ro))
       for f,n in ff:
          K,H=K_h(f);S,d=ring('d',K)
          q=lambda P:spec_H(P,S,H)
          E,A,B=map(q,rows)
          if E:E=E.monic();A%=E;B%=E
          G=ggcd(ggcd(E,A),B)
          assert G and G.degree()==1
          Z=strip(G,[q(g) for g in gs])
          assert Z.degree()==0
          print(w,fo,ro,'exact H degree',f.total_degree(),'d gcd',G.degree(),Z.degree(),flush=True)
          hits+=1
    assert len(seen)==9 and hits==8
    print('all nine literal terminal-overlap phase charts excluded')
if __name__=='__main__':run()
