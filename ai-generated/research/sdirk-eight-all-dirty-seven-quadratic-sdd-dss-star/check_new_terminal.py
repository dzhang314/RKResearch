"""Exact reconstructed mesh fields for the terminal-new D,S,S star."""
from new_projection import project
from star_scalars import audit

from sympy.polys.rings import ring
import sympy as S0
import sympy as S
from sympy.polys.agca.extensions import MonogenicFiniteExtension
class Tower(MonogenicFiniteExtension):
    def exquo(self,x,y):return x/y
    quo=exquo
    def convert(self,x,base=None):
        if getattr(x,'ext',None)==self:return x
        return super().convert(x,base)
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


def ev(p,L,h,u):
    from sympy import Rational
    def e(q):
      return sum((L.convert(Rational(a))*(h**i if i else L.one)*(u**j if j else L.one)
                  for (i,j),a in q.items()),L.zero)
    s=e(p.denom)
    assert s
    return e(p.numer)/s
def roots(f):
    K=f.ring.domain
    factors=f.factor_list()[1]
    print('u genuine factor degrees',[(p.degree(),n) for p,n in factors],flush=True)
    for g,n in factors:
        g=g.monic()
        if g.degree()==1:
            yield K,-g.get((0,),K.zero),lambda z:z
        else:
            P=S0.Poly.from_dict(g.to_dict(),S0.Symbol('u'),domain=K)
            E=Tower(P)
            yield E,E.generator,lambda z:E.convert(z,K)
def check():
 saw=set();fits=[]
 for mo,fs,ps,gg,g,datas in project():
    for f,n in fs:
        K,H=K_h(f);S,v=ring('u',K)
        gp=lambda h:specialize(h,S,[H,None])
        raw=gcd(*(gp(x) for x in ps));assert raw
        ftr=strip(raw,[gp(a) for a in gg])
        k=mo,f.total_degree()
        assert k not in saw
        saw.add(k)
        exponent={('A',24):1,('A',2):0,('S',2):4}[k]
        assert raw.degree()==ftr.degree()==exponent
        assert [(q.degree(),v) for q,v in ftr.factor_list()[1]]==([(exponent,1)] if exponent else [])
        print(mo,f.total_degree(),'raw/guarded u degree',raw.degree(),ftr.degree(),flush=True)
        for E,u,em in roots(ftr):
            h=em(H)
            ep=lambda p:ev(p,E,h,u)
            assert all(ep(q) for q in g)
            H0,a,b,fa,fb,M=datas
            T,y=ring('y',E)
            Mz=T.from_dict({ix:ep(j) for ix,j in M.items()})
            W=Mz.exquo(y-T(ep(b))).monic()
            z=audit(E,h,ep(a),ep(b),None,W,ep(fa),ep(fb))
            print(mo,f.total_degree(),'post full fit',z,flush=True)
            fits.append((k,z))
 assert saw=={('A',24),('A',2),('S',2)}
 assert fits==[(('A',24),'excluded'),(('S',2),'excluded')]
 print('all terminal-new phase families excluded')
if __name__=='__main__':check()
