"""Exact trace and field reconstruction of the mutual-reuse two-sided D chart."""
from distinct_mutual_reuse import *
from sympy.polys.agca.extensions import MonogenicFiniteExtension
class Tower(MonogenicFiniteExtension):
    def exquo(self,x,y):return x/y
    quo=exquo
    def convert(self,x,base=None):
        if getattr(x,'ext',None)==self:return x
        return super().convert(x,base)
def inv(R,p,g):
    k,now=g,p%g
    a,b=R.zero,R.one
    while now:
        q,r=k.div(now)
        k,now=now,r
        a,b=b,a-q*b
    assert k.degree()==0
    return (a/R(k.LC))%g
def egcd(p,q):
    while q:p,q=q,p%q
    return p.monic()
def value(p,t,x):
    return sum((c*x**j if j else c for (j,),c in p.items()),p.ring.domain.zero)
def ip(R,t,vals):
    out=R.zero
    for j,(a,c) in enumerate(vals):
        f=R(c)
        for k,(b,_) in enumerate(vals):
            if k!=j:f*= (t-b)/R(a-b)
        out+=f
    return out
def audit_trace(K,R,t,m,L,Q0,W,ds):
    one,zero=K.one,K.zero
    c0=K.convert(S.Rational(6,7))*m*m
    C=(inv(R,Q0,L**2)*(4*m**6/175))%(L**2)
    def wid(p):return ((p*C)%(L**2)).get((7,),zero)
    w1=W.get((1,),zero)
    def tw(p):
        q=p%W
        return 2*q.get((0,),zero)-w1*q.get((1,),zero)
    if not w1:
        # Works also for a double zero of W=t²: derivative of H'/H.
        s=-W.get((0,),zero)
        vj=s*s-c0*s+L.get((0,),zero)
        uu=-2*(2*s-c0)/vj
    else:
        assert egcd(W,W.diff(t)).degree()==0
        uu=-tw(L.diff(t)*inv(R,L*W.diff(t),W))
    ce=2*uu-2*m*wid(L*inv(R,W,L**2))
    LL=inv(R,L,W)
    def tr(p):
        return 2*(tw(p*LL)+sum((value(p,t,x)/value(L,t,x) for x in ds),zero))-2*m*wid(p)
    return ce,tr
def symbolic_trace(seq):
    rel,gs,gu,vals,r,lam,beta,W,ds,l,q,gf,gr=seq
    K=F.to_domain();R,t=ring('t',K)
    LP=t**4-t*t*(F(6)*m*m/7)+F(3)*m**4/35
    L3=t**3-t*(F(3)*m*m/5)
    W_=W(t)
    Q=L3-t*LP*((h*h-F(3)*m*m/5)/L(h))
    A=ip(R,t,vals)/R(lam)-W_*R(beta*r/lam)
    z,T=audit_trace(K,R,t,m,LP,Q,W_,ds)
    out=z/r+T(A)
    assert out
    dn=integer(out.denom)
    assert strip(dn,gs+[integer(g.denom) for g in gu]).total_degree()==0
    ans=strip(integer(out.numer),gs)
    print('symbolic even trace factors',[(j.total_degree(),k) for j,k in ans.factor()[1]],flush=True)
    return ans
def reconstruct(kind,pol,seq):
    rel,gs,gu,vals,r,lam,beta,W,ds,l,q,gf,gr=seq
    for f0,ex in pol.factor()[1]:
        p=S.Poly.from_dict({(int(i),):int(c) for (i,j),c in f0.to_dict().items()},X,domain=S.QQ)
        assert p.is_irreducible
        if p.degree()==1:
            K=S.QQ;a=K.convert(-p.nth(0)/p.nth(1))
        else:
            K=S.QQ.algebraic_field((p,X));a=K.unit
        R,Y=ring('y',K)
        def sp(Q):
            return sum(RR for RR in [R(K.convert(int(c))*a**int(i))*Y**int(j) for (i,j),c in Q.to_dict().items()])
        if kind=='split':
            g=sp(Th).gcd(sp(integer(rel.numer)))
        else:g=Y
        for b in gs:
            c=sp(b)
            if not c:g=R.one;break
            while (j:=g.gcd(c)).degree()>0:g=g.exquo(j)
        print('degree',p.degree(),'geometric fiber degree',g.degree(),flush=True)
        for qq,ee in g.factor_list()[1]:
            assert qq.degree() in (1,2)
            if qq.degree()==1:
                E=K;emb=lambda z:z;bb=[-qq.get((0,),K.zero)/qq[(1,)]]
            else:
                Q=S.Poly.from_dict(qq.to_dict(),S.Symbol('y'),domain=K)
                E=Tower(Q);emb=lambda z:E.convert(z,K)
                b=E.generator;bb=[b,-emb(qq.get((1,),K.zero)/qq[(2,)])-b]
            for b in bb:
                def ev(z):
                    def evp(f):
                        return sum((E.convert(S.Rational(c))*emb(a)**int(i)*b**int(j) for (i,j),c in f.items()),E.zero)
                    x,y=evp(z.numer),evp(z.denom)
                    assert y
                    return x/y
                if not all(ev(g) for g in gu):continue
                assert not ev(rel)
                yield E,ev(m),tuple(map(ev,ds)),ev(l),ev(q),ev(gf),ev(gr),ev(r),ev(lam),ev(beta),tuple((ev(x),ev(y)) for x,y in vals),kind,p.degree(),ev(S0) if kind=='even' else b

from sympy import Rational as S0R
def fourth(E,R,t,m,L,A,W,ds,l,rev,gf,rg,lam,beta):
    zero,one=E.zero,E.one
    h=m-1
    k=1+4*h-4*h*h
    TT=ip(R,t,[(-h,one/2),(h,k/2),(l,gf)])
    S=TT.compose(t,t-m)
    J=R.from_dict({(i+1,):v/(i+1) for (i,),v in S.items()})
    b,c=S.get((1,),zero),S.get((2,),zero)
    D4=b+c*E.convert(S0R(4,3))+(t+m-1)*(-one/k+2*c*(k+1)/(3*k))
    N4=TT-J.compose(t,t+m)
    B0=beta/lam
    Rg=W*rg
    H=L-Rg*(A+Rg*B0)
    assert H.degree()==4
    Hs=H.exquo((t-l)*(t-rev))
    assert Hs.degree()==2
    S_result=egcd(Hs,D4*Rg-N4)
    x=ds[2]
    U=R(value(L,t,x))-t*(value(A,t,x)+t*B0)
    D_result=egcd(U,t*value(D4,t,x)-value(N4,t,x))
    print('actual fourth D/S gcd degrees',D_result.degree(),S_result.degree(),flush=True)
    return D_result.degree(),S_result.degree()
def run():
 for kind in ('even','split'):
  for f,r in combinations_with_replacement(('A','S'),2):
    seq=case(f,r,kind)
    assert seq
    rel,gs,*_=seq
    if not rel:
        assert kind=='even'
        ch=symbolic_trace(seq)
    else:
        eq=strip(integer(rel.numer),gs)
        ch=eq if kind=='even' else Th.resultant(eq,'d')
        ch=strip(ch,[v for v in gs if v.degrees()[-1]==0])
    n=0
    for E,m0,ds,l0,q0,gf,gr,rg,lam,beta,vals,ki,deg,z0 in reconstruct(kind,ch,seq):
        R,t=ring('t',E)
        m=m0;h=m-1
        L=t**4-t*t*(E.convert(S.Rational(6,7))*m*m)+E.convert(S.Rational(3,35))*m**4
        L3=t**3-t*(E.convert(S.Rational(3,5))*m*m)
        Q0=L3-t*L*((h*h-E.convert(S.Rational(3,5))*m*m)/value(L,t,h))
        W=t*t-z0 if kind=='even' else t*(t+z0)
        pp=R.one
        for d in ds:pp*=t-d
        assert not Q0.rem(pp*W)
        A=ip(R,t,vals)/R(lam)-W*R(beta*rg/lam)
        c,T=audit_trace(E,R,t,m,L,Q0,W,ds)
        tc=c/rg+T(A)
        print(kind,f,r,deg,'trace fails?',bool(tc),flush=True)
        if not tc:
            n+=1
            dsf,ssf=fourth(E,R,t,m,L,A,W,ds,l0,q0,gf,rg,lam,beta)
            assert dsf==0 and ssf==0
    assert n==int(kind=='even' and f==r)
    print(kind,f,r,'trace fibres checked by fourth read',n,flush=True)
 print('all distinct mutual-reuse cases excluded')

if __name__=='__main__':run()
