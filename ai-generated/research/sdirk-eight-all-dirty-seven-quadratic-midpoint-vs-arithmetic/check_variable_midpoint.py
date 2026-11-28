"""Variable distinct midpoint D,D,D opposite an arithmetic D,S,S."""
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.fields import field
from itertools import combinations
from flint import fmpz_mpoly_ctx as MC
from math import lcm
HH,h=field('h',S.QQ)
K=HH.to_domain()
R,t=ring('v',K)

def kk(u):return 1+2*u-u*u
def DD(u):return -2+u+4*u*u-u**3
def num(u):return (1+4*u-4*u*u)*DD(u)+4*u*u*(3*u-2)
f=lambda p,q:HH(p)/q
m=h+1;k=kk(h);q=num(h)/DD(h)
a=f(6,7)*m*m;b=f(3,35)*m**4;c=f(3,5)*m*m
L=t**4-a*t*t+b
L3=t**3-c*t
Lh=h**4-a*h*h+b
mu=(h*h-c)/Lh
S0=(f(3,5)*m*m*h*h-f(3,7)*m**4)/(h*h-c)
W=t*t-S0
P=t*(t*t-h*h)
Q=L3-mu*t*L
assert Q==-mu*P*W
Ls=S0*S0-a*S0+b
beta=-4*Lh/q
T=(k/2)+(q-1)/(4*h)*t+(q+1-2*k)/(4*h*h)*t*t
A0=2*b/k+(Lh*(1/q-1)/h)*t+(Lh*(1+1/q)-2*b/k)/(h*h)*t*t
assert not ((T*A0-L)%P)
# Even trace works through S=0: the double-root derivative gives
# the exact same constant -2*(2*S-a)/L4(sqrt(S)).
def inv(p,n):
    A,B,d=p.gcdex(n)
    assert d==R.one
    return A%n
NL=(inv(Q,L**2)*(4*m**6/175))%(L**2)
wi=inv(W,L**2)
def width(p):return ((p*NL)%(L**2)).get((7,),K.zero)
ct=-4*(2*S0-a)/Ls-2*m*width(L*wi)
def trace(p):
    sw=2*(p%W).get((0,),K.zero)/Ls
    sp=p.get((0,),K.zero)/b+(p.evaluate(t,h)+p.evaluate(t,-h))/Lh
    return 2*(sw+sp)-2*m*width(p)
ta,tt=trace(A0),trace(T)
print('symbolic trace built',[(z.numer.degree(),z.denom.degree()) for z in [ct,ta,tt]],flush=True)

v=t
x2=-v+h;x3=-2*v+h
w2=W.compose(t,x2);w3=W.compose(t,x3)
ratio=DD(v)*(2*h-3*v)-(v-2)*(3*v-2)*w2
assert num(v)*w2-kk(v)*DD(v)*w3==v*kk(v)*ratio
rows=[]
for x,n,d in [(x2,kk(v),R(2)),(x3,num(v),2*DD(v))]:
    rows.append((-n*(d*A0.compose(t,x)+beta*n),
                 d*d*L.compose(t,x)+beta*d*n*T.compose(t,x)))
rows.append((kk(v)*ta,2*ct*w2-beta*tt*kk(v)))
minors=[p*s-q*r for (p,q),(r,s) in combinations(rows,2)]

# Exact integer ingress for direct resultants. The required denominators
# are covered by these genuine nonzero h-only quantities.
hguards=[h,m,k,q,DD(h),3*h-2,Lh,h*h-c,Ls]
kguards=[v,kk(v),DD(v),num(v),3*v-2,w2,w3]+[x-y for x in [x2,x3] for y in [-h,HH.zero,h]]
fguards=[e.numer for e in hguards]+[e.denom for e in hguards]
def no_unknown_den(p):
    for value in p.values():
        d=value.denom
        for old in fguards:
            while (g:=d.gcd(old)).degree()>0:d=d.exquo(g)
        assert d.degree()==0
def numer(p):
    if not p:return Ctx.constant(0)
    no_unknown_den(p)
    den=HH.ring.one
    for r in p.values():den=den.lcm(r.denom)
    coeff={}
    for (i,),q in p.items():
        r=q*HH(den)
        assert r.denom.degree()==0
        d=r.denom[(0,)]
        for (j,),c in r.numer.items():coeff[int(j),int(i)]=S.Rational(c)/S.Rational(d)
    cd=lcm(*(int(c.q) for c in coeff.values()))
    return Ctx.from_dict({s:int(v*cd) for s,v in coeff.items()})
for expr in (R(mu),L,L3,Q,W,T,A0,NL,wi,R(ct),R(ta),R(tt)):
    no_unknown_den(expr)
Ctx=MC.get(('h','v'),'lex')
def nude(a):
    return Ctx.from_dict({(int(i),0):int(c*lcm(*(int(S.Rational(c).q) for c in a.values()))) for (i,),c in a.items()})
ge=[numer(p) for p in kguards]+[nude(a) for a in fguards]
def strip(p,gs):
    if not p:return p
    for g in gs:
      assert g
      while (f:=p.gcd(g)).total_degree()>0:
        p,r=divmod(p,f)
        assert not r
    return p
ratio0=strip(numer(ratio),ge)
ms=[strip(numer(p),ge) for p in minors]
print('ingress bidegrees',[(d.degrees(),d.total_degree()) for d in [ratio0]+ms],flush=True)
if __name__=='__main__':
    P0=Ctx.constant(0)
    gd=[]
    td=[]
    for minor in ms:
        assert minor
        rp=ratio0.resultant(minor,'v')
        assert rp
        td.append(rp.total_degree())
        P0=strip(P0.gcd(rp),[nude(a) for a in fguards])
        gd.append(P0.total_degree())
        print('resultant degree',rp.total_degree(),'guarded gcd degree',P0.total_degree(),flush=True)
    assert td==[74,66,96] and gd==[62,0,0]
    print('all genuine midpoint reverse-arithmetic fibres excluded')
