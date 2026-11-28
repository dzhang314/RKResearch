"""One-extra D opposite true arithmetic D,S,S, with common D endpoint."""
from prefix_scalars import shape,kap,H,qnum
from sympy.polys.fields import field
from sympy.polys.rings import ring
import sympy as S
from flint import fmpz_mpoly_ctx as MC
from math import lcm
from time import monotonic
from itertools import combinations

FF,d,e,v=field('d,e,v',S.QQ)
C=MC.get(('d','e','v'),'lex')
DD,EE,VV=C.gens()
Theta=35*DD*DD*EE*EE-21*(DD*DD+EE*EE)+15
L=lambda x:x**4-FF(6)*x*x/7+FF(3)/35
X=S.Symbol('d')
be=-4*L(0)
def ip(t,vals):
    b=FF.zero
    for j,(a,h) in enumerate(vals):
        for k,(o,z) in enumerate(vals):
            if k!=j:h=h*(t-o)/(a-o)
        b+=h
    return b
def integer(p):
    if not p:return C.constant(0)
    lc=lcm(*(int(S.Rational(c).q) for c in p.values()))
    return C.from_dict({tuple(map(int,k)):int(c*lc) for k,c in p.items()})
def strip(p,guards):
    if not p:return p
    for n in guards:
        assert n
        while (g:=p.gcd(n)).total_degree()>0:
            p,r=divmod(p,g);assert not r
    return p
def setup(lab,kind):
    gd,sf,gf,gu=shape(d,lab)
    sqr=(21*d*d-15)/(35*d*d-21)
    if kind=='even':
        W=lambda t:t*t-sqr
        b=FF.zero
        de=[d,-d]
    else:
        W=lambda t:(t+d)*(t+e)
        b=d+e
        de=[d,e]
    r=gf/W(sf)
    vs=-v;ws=-2*v
    kv=kap(v)
    qbar=H(v)-v*(v-2)*(3*v-2)
    assert kv*qbar==qnum(v)
    mu=2*r*W(vs)  # κ(v) * λ
    vals=[(FF.zero, -be*(kv+mu)/2+be*r*kv*W(0)),
          (d, mu*L(d)/gd-be*kv*gd+be*r*kv*W(d)),
          (sf,mu*L(sf)/gf)]
    bs=H(v)*(b-3*v)-(v-2)*(3*v-2)*W(vs)
    assert v*kv*bs==qnum(v)*W(vs)-kv*H(v)*W(ws)
    b1=2*L(vs)-ip(vs,vals)
    b2=2*H(v)*L(ws)-qbar*ip(ws,vals)
    gs=gu+[d,5*d*d-3,L(d),sf,W(sf),v,v-2,3*v-2,H(v),kv,qbar,
           W(vs),W(ws),mu-kv,sf-vs,sf-ws]
    if kind!='even':
        gs+=[e,d-e,d+e,5*e*e-3,L(e)]
    gs += [x-y for x in [sf,vs,ws] for y in [FF.zero]+de]
    if not all(gs):
        print('identical actual guard',lab,kind)
        return None
    gg=[integer(p.numer) for p in gs]
    dd=[integer(p.denom) for p in gs]
    for u in [bs,b1,b2]:
        assert strip(integer(u.denom),gg+dd).total_degree()==0
    return [strip(integer(u.numer),gg) for u in [bs,b1,b2]],gg

def run():
 for kind in ('even','split'):
  for lab in ('A2','A3','S'):
    start=monotonic()
    rr=setup(lab,kind)
    if rr is None:continue
    pp,gs=rr
    gg=C.constant(0)
    R0=[]
    for a,b in combinations(pp,2):
        if not a or not b:continue
        prod=a.resultant(b,'v')
        if not prod:continue
        if kind=='split':
            prod=strip(prod,[g for g in gs if not g.degrees()[-1]])
            prod=Theta.resultant(prod,'e')
            if not prod:continue
        R0.append(prod.total_degree())
        gg=gg.gcd(prod)
        gg=strip(gg,[g for g in gs if g.degrees()[1:]==(0,0)])
    assert gg
    print(kind,lab,'projection deg',R0,'common factors',[(a.total_degree(),b) for a,b in gg.factor()[1]],'t',round(monotonic()-start,2),flush=True)
    expected={('even','A2'):[22,33,50],('even','A3'):[31,42,74],('even','S'):[13,24,26],
              ('split','A2'):[44,66,100],('split','A3'):[62,78,124],('split','S'):[26,48,52]}
    assert R0==expected[kind,lab]
    if (kind,lab)!=('even','S'):
        assert gg.total_degree()==0
    else:
        h=gg.factor()[1]
        assert len(h)==1 and h[0][1]==1
        P=S.Poly(7*X*X-5,X,domain=S.QQ)
        gg0=S.Poly.from_dict({(int(i),):int(c) for (i,j,n),c in h[0][0].to_dict().items()},X,domain=S.QQ)
        assert gg0.monic()==P.monic() and P.is_irreducible
        K=S.QQ.algebraic_field((P,X));d0=K.unit
        assert (21*d0*d0-15)/(35*d0*d0-21)==K.zero
        RR,t=ring('v',K)
        def at(a):
            return sum(RR(K.convert(int(c))*d0**int(i))*t**int(n)
                       for (i,j,n),c in a.to_dict().items())
        T=RR.zero
        for p in pp:
            T=T.gcd(at(p))
        assert T.monic()==t
        print('retained genuine Hermite W=t²; exact fibre gcd v',flush=True)
 print('all shared-clock mixed arithmetic cases excluded')
if __name__=='__main__':run()
