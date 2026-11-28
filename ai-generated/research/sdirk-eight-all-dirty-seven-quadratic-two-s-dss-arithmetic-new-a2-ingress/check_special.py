"""Exact A2 special subcharts, no precomputed data."""
from ingress import ingress
from v2_axis import project
from flint import fmpq_poly
from sympy.polys.rings import ring
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
fstrip=strip
def specialize_D(f,hR):
    K=hR.domain
    mod=fmpq_poly(list(reversed(K.mod.to_list())))
    cs={}
    for (i,j,k),a in f.to_dict().items():
        assert not k
        c=cs.setdefault(int(i),{})
        c[int(j)]=int(a)
    dt={}
    for i,c in cs.items():
        p=[0]*(max(c)+1)
        for j,a in c.items():p[j]=a
        q=fmpq_poly(p)%mod
        if q:dt[(i,)]=K.new(list(reversed(q.coeffs())))
    return hR.from_dict(dt)
def half(rows,gs,Q):
    x=S.Symbol('x')
    pol=S.Poly(x**3-3*x*x+1,x,domain=S.QQ)
    assert pol.is_irreducible
    K=S.QQ.algebraic_field((pol,x));R,h=ring('H',K)
    a=specialize_D(rows[0],R);q=specialize_D(Q,R)
    gg=[specialize_D(z,R) for z in gs if not z.degrees()[2]]
    L=gcd(a,q)
    out=fstrip(L,gg)
    assert a.degree()==15 and q.degree()==65 and L.degree()==out.degree()==0
    print('A2 front half amplitude: E and Q degree in H',a.degree(),q.degree(),
          'common and guarded',L.degree(),out.degree(),flush=True)

def v2():
    ff,gg,rows=project()
    seen=set()
    for f,n in ff:
        K,H=K_h(f);U,d=ring('d',K)
        ev=lambda r:specialize(r,U,[H,None])
        a,b,c=map(ev,rows)
        D=gcd(gcd(a,b),c)
        G=strip(D,[ev(r) for r in gg])
        assert D.degree()==1 and G.degree()==0
        x=-D.get((0,),K.zero)
        assert x==H-3
        i=f.total_degree()
        if i==1:
            assert H==5 and x==2
        else:
            assert i==3 and x**3-3*x*x+1==K.zero
        print('rear v=2 exact H degree',i,'excluded',flush=True)
        seen.add(i)
    assert seen=={1,3}
if __name__=='__main__':
    half(*ingress())
    v2()
    print('both A2 special charts excluded; general A2 remains open')
