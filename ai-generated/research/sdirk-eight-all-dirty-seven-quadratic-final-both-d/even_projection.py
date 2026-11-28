"""Both D endpoints, arithmetic D,S,S / D,S,S; even quadratic graph."""
import sympy as S
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_mpoly_ctx as MC
from math import lcm
from scalar_geometry import D,k,N,exact_trace
F,h,u=field('h,u',S.QQ)
C=MC.get(('h','u'),'lex')
hh,uu=C.gens()
m=h+1; den=35*h*h-21*m*m
s=(21*m*m*h*h-15*m**4)/den
a=6*m*m/7;b=3*m**4/35
L=lambda t:t**4-a*t*t+b
W=lambda t:t*t-s
rel=lambda u:D(u)*(2*h-3*u)-(u-2)*(3*u-2)*W(u-h)
def intp(p):
    if not p:return C.constant(0)
    lc=lcm(*(int(S.Rational(c).q) for c in p.values()))
    return C.from_dict({tuple(map(int,i)):int(c*lc) for i,c in p.items()})
def strip(p,gs):
    for g in gs:
        while p and (q:=p.gcd(g)).total_degree()>0:
            p,r=divmod(p,q);assert not r
    return p
def num(x):return intp(x.numer)
gs=[m,h,den,L(h),s*s-a*s+b]
hs=[num(g) for g in gs]
def trace():
    E,H=field('h',S.QQ)
    K=E.to_domain()
    M=1+H
    ss=(21*M*M*H*H-15*M**4)/(35*H*H-21*M*M)
    R,t=ring('t',K)
    l=t**4-R(6*M*M/7)*t*t+R(3*M**4/35)
    ll=t**3-R(3*M*M/5)*t
    mu=(H*H-3*M*M/5)/(H**4-6*M*M*H*H/7+3*M**4/35)
    qq=ll-R(mu)*t*l
    ww=t*t-R(ss)
    p=t*(t*t-R(H*H))
    ce,T=exact_trace(K,R,t,p,ww,l,qq,M)
    def emb(z):
      return F.from_expr(z.as_expr().subs(H.as_expr(),h.as_expr()))
    return list(map(emb,[ce,T(R.one),T(t*t)]))
def equal():
    # u=v: two pairs of reflected distinct nodes.  Nodal leading scalar is nonzero.
    x,y=u-h,2*u-h
    rr=k(u)/(2*W(x))
    H4=(s*s-a*s+b)/(W(x)*W(y))
    c2=1-H4;c0=-a+H4*(x*x+y*y)+s*c2
    Cw=c0+c2*h*h
    dif=1-2*rr*W(h)
    ce,t0,t2=trace()
    z=(ce+t0*c0+t2*c2)*dif-2*rr*(2*rr*L(h)-Cw)*(t2-s*t0)
    gg=gs+[u,k(u),D(u),N(u),3*u-2,W(x),W(y),x,y,x-y,x+y,dif]
    gi=[num(g) for g in gg]; gd=[intp(g.denom) for g in gg]
    assert all(gg) and strip(intp(z.denom),gi+gd).total_degree()==0
    assert strip(intp(rel(u).denom),gi+gd).total_degree()==0
    R,T=[strip(num(f),gi) for f in [rel(u),z]]
    print('equal polynomials',R.degrees(),T.degrees(),flush=True)
    pp=strip(R.resultant(T,'u'),hs)
    print('equal projected factors',[(f.degrees(),e) for f,e in pp.factor()[1]],flush=True)
    return pp,(R,T),gg,hs
def distinct():
    # u is alpha=u_open+v_open in this section only.
    e1=u;e2=(3*s-3*h*h+4*h*e1)/6
    R,t=ring('t',F.to_domain())
    def rf(z):
      return D(z)*(2*h-3*z)-(z-2)*(3*z-2)*(z*z-2*h*z+R(h*h-s))
    Z=rf(t)%(t*t-R(e1)*t+R(e2))
    z0=Z.get((0,),F.zero);z1=Z.get((1,),F.zero)
    assert z0 and z1
    pp=[strip(num(z),hs) for z in [z0,z1]]
    for z in (z0,z1):assert strip(intp(z.denom),hs).total_degree()==0
    out=strip(pp[0].resultant(pp[1],'u'),hs)
    print('distinct sum polynomials',[p.degrees() for p in pp],'projection',[(f.degrees(),e) for f,e in out.factor()[1]],flush=True)
    return out,pp,e2
if __name__=='__main__':
 equal()
 distinct()
