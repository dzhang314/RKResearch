"""One extra D vs D,S,S star at shared D endpoints."""
import sympy as S
from sympy.polys.rings import ring
from prefix_scalars import X,shape,d
f=S.Poly(35*X**4-140*X**3+98*X*X+84*X-69,X,domain=S.QQ)
assert S.expand(f.as_expr()-(35*(X*(2-X))**2+42*X*(2-X)-69))==0
assert f.is_irreducible
K=S.QQ.algebraic_field((f,X));d0=K.unit;e=2-d0
one,z=K.one,K.zero
S0=(d0-1)**2
assert S0 and len({z,d0,e})==3 and d0!=-e
L=lambda t:t**4-t*t*K.convert(S.Rational(6,7))+K.convert(S.Rational(3,35))
W=lambda t:(t+d0)*(t+e)
def ev(a):
    def e(p):return sum((K.convert(x)*d0**i for (i,),x in p.items()),z)
    n,q=e(a.numer),e(a.denom)
    assert q
    return n/q
RR,X0=ring('X0',K)
tau=(2-X0)/2
beta=-4*L(z)
for lab in ('A2','A3'):
    gd,sf,gf,gu=shape(d,lab)
    gd,sf,gf=map(ev,(gd,sf,gf)); assert all(ev(g) for g in gu)
    assert sf not in (z,d0,e) and W(sf)
    r=gf/W(sf)
    # M = tau*lambda*C, at each known literal D/S label.
    mu=(X0-S0)*r
    vals=[(z, -(tau+mu)*beta/2+tau*(beta*r*W(z))),
          (d0,mu*(L(d0)/gd)+tau*(beta*(r*W(d0)-gd))),
          (sf,mu*(L(sf)/gf))]
    YY,Y=ring('Y',RR.to_domain() if hasattr(RR,'to_domain') else RR.to_ring())
    # Work via direct polynomial expansion in Y=t+1, then Y²->X0.
    D=Y-1
    sub=D**4-D**2*YY(RR(K.convert(S.Rational(6,7))))+YY(RR(K.convert(S.Rational(3,35))))
    for j,(a,b) in enumerate(vals):
        val=YY(b)
        for i,(c,_) in enumerate(vals):
            if i!=j:val=val*(D-YY(RR(c)))/YY(RR(a-c))
        sub-=val
    v0,v1=RR.zero,RR.zero
    for (j,),a in sub.items():
        if j%2:v1+=a*X0**((j-1)//2)
        else:v0+=a*X0**(j//2)
    gg=v0.gcd(v1)
    assert gg.degree()==0
    print(lab,'degree and raw gcd',v0.degree(),v1.degree(),gg.degree(),flush=True)
    for g in [X0,X0-1,X0-2,X0-S0,mu-tau]+[X0-(r+1)**2 for r in (z,d0,e,sf)]:
        while (h:=gg.gcd(g)).degree()>0:gg=gg.exquo(h)
    print(lab,'guarded',gg.degree(),flush=True)
    assert gg.degree()==0
