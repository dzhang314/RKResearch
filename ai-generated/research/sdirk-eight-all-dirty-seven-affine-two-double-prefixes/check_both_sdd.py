"""Two singleton endpoints with a doubled second and third at each end."""
from itertools import permutations
import sympy as S
from sympy.polys.rings import ring
from exact_support import kk,l3,l4,kap,phase,affine_two,ExactTower
s,x=S.symbols('s x')
P=S.Poly(kk(x,s,1),x,s,domain=S.QQ)
L=S.Poly(P.as_expr(),x).nth(3)
M=-S.Poly(P.as_expr(),x).nth(2)
T=S.Poly(P.as_expr(),x).nth(1)
directions=list(permutations(range(3),2))

def pattern(mf,mr,j,k):
    c0=2*(int(mf=='S')-int(mr=='S'))
    w=[-8,4,0] if mf=='A' else [-1,-1,0]
    qa,qb=(-8,4) if mr=='A' else (-1,-1)
    w[j]+=qa;w[k]+=qb
    a,b=w[0]-w[2],w[1]-w[2]
    return c0,w,a,b

def norms():
  for mf,mr in [('A','A'),('A','S'),('S','S')]:
    for j,k in directions:
      if mf==mr and set((j,k))=={0,1}:
        print(mf,mr,j,k,'excluded by endpoint distinction or opposite D labels')
        continue
      c,w,a,b=pattern(mf,mr,j,k)
      uu=L*(a*x+c)+w[2]*M
      Inner=S.Poly(uu*uu+b*uu*(M-L*x)+b*b*L*(T-M*x+L*x*x),x,s,domain=S.QQ)
      N=P.resultant(Inner)
      assert not N.is_zero
      fac=N.factor_list()[1]
      print(mf,mr,j,k,'linear',c,w,a,b,'degs',[(d.degree(),m) for d,m in fac],flush=True)
      yield mf,mr,j,k,c,w,a,b,Inner,fac

def roots_two(E,Q):
    """Yield a field, embedding, and each root of a separable quadratic or linear."""
    assert Q.degree() in (1,2)
    V=S.Symbol('v')
    for gg,ex in Q.factor_list()[1]:
        assert ex==1
        if gg.degree()==1:
            yield E,lambda x:x,-gg[(0,)]/gg[(1,)]
        else:
            assert gg.degree()==2
            F=ExactTower(S.Poly.from_dict(gg.to_dict(),V,domain=E))
            emb=lambda x:F.convert(x,E)
            z=F.generator
            yield F,emb,z
            yield F,emb,-emb(gg[(1,)]/gg[(2,)])-z

def inner_roots(F,p,inr,b):
    RR,X=ring('x',F)
    rho=F.unit
    def ev(f):return sum(RR(F(c)*rho**j)*X**i for (i,j),c in f.terms())
    Q,I=ev(p).monic(),ev(inr)
    G=Q.gcd(I).monic()
    assert G.degree() in (1,2)
    if not b:assert G.degree()==1
    return RR,X,Q,G

def readoff(E,sm,zs,e,mf,mr,j,k):
    one=E.one
    if not all((e,e-one,e+sm,e-sm,l3(sm,one),l4(sm,one),kk(-e,sm,one),kk(e,sm,one))):
        return 'guard'
    ell=2*one/(one-e)
    a=-(e+sm)/(one-e);b=(sm-e)/(one-e)
    lam=-b/a
    assert lam
    lp=lambda x:ell*(1+x)/2
    c1,c2=lp(zs[0]),lp(zs[1])
    xr1,xr2=lp(-zs[j]),lp(-zs[k])
    f=phase(E,c1-1,mf);r=phase(E,xr1-1,mr)
    if f is None or r is None:
        return 'guard'
    assert f[0]==c2 and r[0]==xr2
    R=lambda x:(x-1+a)*(one/(2*a))
    L4=lambda x:((2*x-ell)**4*35-(2*x-ell)**2*(30*ell**2)+3*ell**4)/560
    assert R(one)==one/2 and R(ell-1)==lam/2
    fwd=[(c1,kap(c1-1)/2),(c2,f[1])]
    rev=[(lp(zs[j]),lam*kap(xr1-1)/2),(lp(zs[k]),lam*r[1])]
    if any(g==R(x) for x,g in fwd+rev):
        return 'guard'
    if any(p==q for p in fwd for q in rev):
        return 'guard'
    c0,c1=L4(one)/R(one),L4(ell-1)/R(ell-1)
    slope=(c1-c0)/(ell-2)
    C=lambda x:(x-1)*slope+c0
    N=lambda x:(x-1)*(x-(ell-1))
    fits=[(g*(g-R(x)),g*N(x),L4(x)-g*C(x)) for x,g in fwd+rev]
    return 'rank' if affine_two(fits,E) is None else 'survive'

def check():
  records=[]
  for mf,mr,j,k,c,w,a,b,I,fac in norms():
    outcomes=[]
    for pp,ex in fac:
      if pp.monic().as_expr() in (s,s*s-S.Rational(3,5)):
        continue
      E=S.QQ.algebraic_field((pp,s)); s0=E.unit
      assert l3(s0,E.one) and l4(s0,E.one)
      RR,X,P0,G=inner_roots(E,P,I,b)
      S0=-P0[(2,)]
      assert G.degree() in (1,2)
      for F,emb,alpha in roots_two(E,G):
        if b:
          ss=emb(S0)
          beta=-(a*alpha+c+w[2]*ss)/b
          # A nonzero norm yields this relation at one of the other
          # two roots; audit actual splitting and simple labels.
          chi=ss-alpha-beta
          tt=emb(s0)
          choices=[(F,tt,alpha,beta,chi)]
        else:
          assert F==E
          Q=P0.exquo(X-alpha)
          choices=[]
          for Z,eta,beta in roots_two(E,Q):
            aa=eta(alpha);ss=eta(S0)
            choices.append((Z,eta(s0),aa,beta,ss-aa-beta))
        for Z,ss,al,be,ch in choices:
          zs=(al,be,ch)
          assert all(not kk(x,ss,Z.one) for x in zs)
          assert len(set(zs))==3
          assert not (c+sum((w1*x for w1,x in zip(w,zs)),Z.zero))
          e=be-2*al if mf=='A' else (2-al-be)/4
          er=2*zs[j]-zs[k] if mr=='A' else (2+zs[j]+zs[k])/4
          assert e==er
          ans=readoff(Z,ss,zs,e,mf,mr,j,k)
          outcomes.append((pp.degree(),ans))
    print('literal phase',mf,mr,(j,k),'outcomes',outcomes,flush=True)
    assert outcomes and all(x=='rank' for _,x in outcomes)
    records+=outcomes
  assert len(records)==20
  print('verified all both-singleton endpoint S,D,D / S,D,D phases',len(records),flush=True)

if __name__=='__main__':
    check()
