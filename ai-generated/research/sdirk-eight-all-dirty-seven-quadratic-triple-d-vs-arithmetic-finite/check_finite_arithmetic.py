"""True arithmetic singleton pair opposite forward D,D,D on every finite mesh."""
import sympy as S
from sympy.polys.rings import ring
from itertools import combinations
from forward_mesh_spec import f_specs,x,k,H,num,g,phaseguards,Q,l4

def cases():
  for la,pf,m,ds,u,F in f_specs():
    if la=='AM':
        continue
    h=m-1
    guards=phaseguards(u,pf)+[m]
    if la.startswith('C'):
        guards+=[ds[1]**2-ds[2]**2,ds[1]**2-Q(S.Rational(3,5))]
    else:guards += [h,h*h-Q(S.Rational(3,5))*m*m]
    guards += [ds[i]-ds[j] for i in range(3) for j in range(i+1,3)]
    guards += [l4(z,m) for z in ds]
    f=F.numer
    for gg in guards:
        while (s:=f.gcd(gg.numer)).degree()>0:f=f.exquo(s)
    for ff,_ in f.factor_list()[1]:
      lab=(la,ff.degree())
      P=S.Poly.from_dict(ff.to_dict(),x,domain=S.QQ)
      assert P.is_irreducible
      if P.degree()==1:
          E=S.QQ; xx=E.convert(-P.nth(0)/P.nth(1))
      else:
          E=S.QQ.algebraic_field((P,x)); xx=E.unit
      def ev(v):
          e=lambda p:sum((E.convert(a)*xx**i for (i,),a in p.items()),E.zero)
          n,d=e(v.numer),e(v.denom)
          assert d
          return n/d
      assert all(ev(z) for z in guards)
      yield lab,E,ev(m),list(map(ev,ds)),[E.one/2,ev(k(u))/2,ev(g(u,pf))]

def exact_trace(K,R,t,P,W,L,Q0,m):
    """Return normalized c/r + T(A2), with repeated-root branch retained."""
    one,zero=K.one,K.zero
    def inv(f,v):
        a,b,g=f.gcdex(v)
        assert g==R.one
        return a%v
    W1=W.get((1,),zero)
    def tw(f):
        r=f%W
        return 2*r.get((0,),zero)-W1*r.get((1,),zero)
    P1,P2=(P.get((i,),zero) for i in (1,2))
    def tp(f):
        r=f%P
        return 3*r.get((0,),zero)-P2*r.get((1,),zero)+(P2*P2-2*P1)*r.get((2,),zero)
    dL=L.diff(t)
    if W.gcd(W.diff(t)).degree()==0:
        uc=-tw(dL*inv(L*W.diff(t),W))
    else:
        h=-W1/2;l=L.evaluate(t,h)
        assert W==(t-h)**2 and l
        uc=(dL.evaluate(t,h)/l)**2-dL.diff(t).evaluate(t,h)/l
    N=(inv(Q0,L**2)*(4*m**6/175))%(L**2)
    wid=lambda f:((f*N)%(L**2)).get((7,),zero)
    ce=2*uc-2*m*wid(L*inv(W,L**2))
    Li,Lp=inv(L,W),inv(L,P)
    return ce, lambda f: 2*(tw(f*Li)+tp(f*Lp))-2*m*wid(f)

def check(lab,K,m,ds,G):
    h=m-1
    R,t=ring('t',K)
    one,zero=K.one,K.zero
    L=t**4-t*t*(K.convert(S.Rational(6,7))*m*m)+K.convert(S.Rational(3,35))*m**4
    L3=t**3-t*(K.convert(S.Rational(3,5))*m*m)
    P=R.one
    for a in ds:P*=t-a
    d=next(y for y in ds if y)
    mu=L3.evaluate(t,d)/(d*L.evaluate(t,d))
    Q0=L3-mu*t*L
    W=Q0.exquo(P).monic()
    assert Q0==-mu*P*W and W.degree()==2
    beta=-2*L.evaluate(t,h)/G[ds.index(h)]
    assert beta
    def ip(values):
      out=R.zero
      for j,q in enumerate(values):
        y=R(q)
        for k,x in enumerate(ds):
            if k!=j:y*=(t-x)/R(ds[j]-x)
        out+=y
      return out
    T,A0=ip(G),ip([L.evaluate(t,x)/q for x,q in zip(ds,G)])
    assert not ((T*A0-L)%P)
    ce,trace=exact_trace(K,R,t,P,W,L,Q0,m)
    v=t
    ti=[-v+h,-2*v+h]
    w1,w2=(W.compose(t,a) for a in ti)
    rd=num(v)*w1-k(v)*H(v)*w2
    assert rd
    forms=[]
    for x,n,d in zip(ti,(k(v),num(v)),(R(2),2*H(v))):
        # The row is multiplied by d² with d the actual nonzero residual denominator.
        forms.append((-n*(d*A0.compose(t,x)+beta*n),
                       d*d*L.compose(t,x)+beta*n*d*T.compose(t,x)))
    forms.append((k(v)*trace(A0),2*ce*w1-beta*trace(T)*k(v)))
    g=rd
    for (a,b),(c,d) in combinations(forms,2):g=g.gcd(a*d-b*c)
    assert g.monic()==(v*k(v)).monic()
    before=g.degree()
    for z in [v,k(v),H(v),num(v),3*v-2,w1,w2]+[x-y for x in ti for y in ds]:
        while (q:=g.gcd(z)).degree()>0:g=g.exquo(q)
    print(lab,'ratio deg',rd.degree(),'gcd pre/post guards',before,g.degree(),flush=True)
    assert g.degree()==0

if __name__=='__main__':
  aa=list(cases());assert len(aa)==7
  print('finite mesh count',len(aa),flush=True)
  for s in aa:check(*s)
  print('verified seven finite actual reverse-arithmetic meshes')
