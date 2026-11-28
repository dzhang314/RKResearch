"""Exact v fibres, and surviving rank-zero curvature audit."""
from projection import project_zero,project_regular,prepare
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
from sympy.polys.fields import field
import sympy as S

def evalf(p,K,h,v):
    def e(q):
        out=K.zero
        for (i,j),a in q.items():out+=K.convert(S.Rational(a))*(h**i if i else K.one)*(v**j if j else K.one)
        return out
    dn=e(p.denom);assert dn
    return e(p.numer)/dn
def curvature(K,h,s,v,fd,fs):
    F,b=field('b',K)
    U,y=ring('y',F.to_domain())
    one=K.one;m=(h+2)/2;p=h-v;q=h-2*v
    k=1+2*v-v*v
    t=y-U(F(h/2))
    L3=t**3-U(F(3*m*m/5))*t
    L4=t**4-U(F(6*m*m/7))*t*t+U(F(3*m**4/35))
    R=U(F(one/2))+U(F((fs-one/2)/s))*y+U(b)*y*(y-U(F(s)))
    W=R.exquo(U(b))
    w0,w1=[W.get((i,),F.zero) for i in range(2)]
    S4=y*(y-U(F(s)))*(y-U(F(p)))*(y-U(F(q)))
    l=L4%W;j=L3%W;z=S4%W
    l0,l1=[l.get((i,),F.zero) for i in range(2)]
    j0,j1=[j.get((i,),F.zero) for i in range(2)]
    z0,z1=[z.get((i,),F.zero) for i in range(2)]
    det=l0*l0-w1*l0*l1+w0*l1*l1
    aa=(j0*(l0-w1*l1)+w0*l1*j1)/det;bb=(l0*j1-l1*j0)/det
    P=(L3-(U(aa)+U(bb)*y)*L4).exquo(W)
    e=P.evaluate(y,F(h))
    nod=l0*z1-l1*z0
    rp=R.evaluate(y,F(p));rq=R.evaluate(y,F(q));rH=R.evaluate(y,F(h))
    mu=2*rp;lh=L4.evaluate(y,F(h))
    beta=-2*lh/F(fd)
    cf=F(fd)*(F(fd)-rH)
    pp=[]
    for zi,li in [(z0,l0),(z1,l1)]:
        C=(U(zi)*L4-U(li)*S4).div(R)[0].evaluate(y,F(h))
        pp.append(mu*(zi*lh-F(fd)*C)-zi*beta*F(k)*cf)
    gs=[b,det,bb,rp,rq,cf,P.get((0,),F.zero),mu-2*F(k*fd)]
    assert all(gs)
    assert strip(det.denom,[b.numer]).degree()==0
    assert all(strip(z.denom,[b.numer,det.numer]).degree()==0 for z in gs)
    den=[z.numer for z in gs]+[z.denom for z in gs]
    assert all(strip(z.denom,den).degree()==0 for z in [e,nod]+pp)
    ans=F.ring.zero
    for z in [e,nod]+pp:ans=gcd(ans,z.numer)
    rr=strip(ans,den)
    print('rank-zero curvature row degrees',[p.numer.degree() for p in [e,nod]+pp],
          'gcd before/after',ans.degree(),rr.degree(),flush=True)
    assert ans.degree()==rr.degree()==0
    return rr.degree()
def run():
 out=[]
 for mode,pr in [('regular',project_regular),('rank zero',project_zero)]:
  for fo,ff,rows,gs in pr():
    for hp,n in ff:
        K,H=K_h(hp);U,v=ring('v',K)
        sp=lambda q:specialize(q,U,[H,None])
        p=U.zero
        for z in rows:p=gcd(p,sp(z))
        assert p and p.degree()==1
        h=strip(p,[sp(z) for z in gs])
        print(mode,fo,hp.total_degree(),'v gcd',p.degree(),h.degree(),flush=True)
        if mode=='regular':assert h.degree()==0
        else:
            assert h.degree()==1
            V=-h.get((0,),K.zero)
            ep=lambda z:evalf(z,K,H,V)
            s,fd,fs,g,a,b,w,rr=prepare(fo)
            assert all(ep(z) for z in g)
            assert not ep(b) and not ep(w) and not ep(rr)
            a=curvature(K,H,ep(s),V,ep(fd),ep(fs))
            print(mode,fo,hp.total_degree(),'curvature survivor degree',a,flush=True)
            out.append((fo,hp.total_degree(),a))
 assert out==[('A2',15,0),('A3',5,0),('S',9,0)]
 print('all reused-terminal regular and rank-zero charts excluded')
 return out
if __name__=='__main__':run()
