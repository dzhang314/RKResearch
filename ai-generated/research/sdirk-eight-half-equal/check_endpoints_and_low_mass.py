"""Exact algebraic checks used in the common half-chart and low-mass cases."""
from itertools import product
import sympy as S

X,x,t,v,z=S.symbols("X x t v z")
Q=t*t-S.Rational(1,2)
gamma=S.Rational(1,2)
L=lambda y:70*y**4-140*y**3+90*y*y-20*y+1
red=lambda P:S.rem(S.expand(P),Q,t)
def inv(c):
    r=S.invert(red(c),Q,t)
    assert red(c*r)==1
    return r

def gcd(f,g):
    f,g=red(f),red(g)
    while g:
        G=S.Poly(g,x)
        w=inv(G.LC())
        while f and (m:=S.Poly(f,x).degree())>=G.degree():
            f=red(f-x**(m-G.degree())*red(S.Poly(f,x).LC()*w)*g)
        f,g=g,f
    return red(f*inv(S.Poly(f,x).LC()))

def moment(P,j):
    return red(sum(c/S.Integer(k+j+1) for (k,),c in S.Poly(P,X).terms()))

def endpoint(sign,star):
    u=1+2*sign*t
    w=2-u if star else 2*u
    r=0 if star else 3*u/2-1
    return tuple(map(red,(gamma*(1+u),gamma*(1+w),u,w-r)))

for U in (2-v,3+2*v):
    h=S.fraction(S.cancel(L(z*U/(2+v))))[0]
    assert S.degree(S.gcd(v*v-2,S.resultant(L(z),h,z),v),v)==0

data=[endpoint(s,st) for s,st in product((1,-1),(True,False))]
xis=[]
for a,b,ha,hb in data:
    inv(ha)
    inv(hb)
    inv(L(a))
    inv(L(b))
    d=red(ha*L(b)-hb*L(a))
    xi=red((a*ha*L(b)-b*hb*L(a))*inv(d))
    xis.append(xi)
    assert inv((gamma-a)*(gamma-b)-S.Rational(1,12))
    inv(L(1-xi))
for f,g in product(xis,repeat=2):
    inv(f+g-1)
print("Rear ratio, local moment matrices and reflected poles passed")

for (a,b,ha,hb),(c,e,_,_) in product(data,repeat=2):
    P=(X-gamma)*(X-a)*(X-b)*(X-1+c)*(X-1+e)
    inv(S.Matrix(2,2,lambda i,j:moment(P,i+j)).det())
    F=red(x**3/3-x*x/2-(a+b)*(x*x/2-x/2)+a*b*(x-gamma))
    P=(X-x)*(X-1+c)*(X-1+e)
    H=red(S.Matrix(3,3,lambda i,j:moment(P,i+j)).det())
    assert gcd(F,H)==1
print("All four-pegged nodal and five-site early-front gates passed")

def J(p):
    x=S.integrate(p,X)
    return x-x.subs(X,0)
for a,b,ha,hb in data:
    F=red(x**3/3-x*x/2-(a+b)*(x*x/2-x/2)+a*b*(x-gamma))
    assert gcd(F,L(x))==1
    pol=[]
    for p in ((X-x)*(X-a)*(X-b), (X-x)*(ha*(b-x)*(b-X)+hb*(a-x)*(X-a))):
        P=red(gamma*p-J(p))
        G,R=S.div(red(P*L(x)-P.subs(X,x)*L(X)),X-x,X)
        assert red(R)==0
        pol.append(red(G))
    assert gcd(F,red(S.resultant(*pol,X)))==1
print("Six active zero clocks with a silent cubic defect excluded")
