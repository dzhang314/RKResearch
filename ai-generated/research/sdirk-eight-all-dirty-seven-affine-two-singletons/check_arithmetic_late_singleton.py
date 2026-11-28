"""Exact guard-only resultants when an affine opener uses a late singleton."""
import sympy as S
from exact_interp import project_resultant
from sympy.polys.rings import ring
from time import monotonic
from itertools import combinations_with_replacement

R,u,v=ring('u,v',S.QQ)
U,V=S.symbols('u v')
def H(u):return -2+u+4*u*u-u**3
def L4(z,d):return 35*z**4-30*d*d*z*z+3*d**4
def side(u,md):
    if md=='T':
        q=2*(u-2)*(u**3-3*u*u+1)
        return H(u),q,2*u*q,2*u*q
    return u*u,u,2*u-1,8*u-4 if md=='A' else R(2)
def k(y,z,d):
    return -9*d**6+15*d**4*y**2-75*d**4*y*z+15*d**4*z**2+105*d**2*y**3*z-45*d**2*y**2*z**2+105*d**2*y*z**3-175*y**3*z**3
def polys(f,r):
    an,ad,aw,ap=side(u,f)
    bn,bd,bw,bp=side(v,r)
    a,b=an*bd,bn*ad
    d=2*ad*bd-a-b
    z=b-a
    wa,wb=aw*bd,bw*ad
    y,yR=a+b+ap*bd,a+b+bp*ad
    f0=k(y,z,d)
    r0=k(yR,-z,d)
    h0=L4(z,d)-560*a*(a+wa)*b*(b+wb)
    dd=[a1 for vn in (ad,bd) for a1,_ in vn.factor_list()[1]]
    def p(x):
        # Remove declared nonzero factors from the fully cleared inputs.
        for xh in dd:
            while not x.rem(xh):x=x.exquo(xh)
        return S.Poly.from_dict(x.to_dict(),U,V,domain=S.QQ)
    return p(f0),p(r0),p(h0)
for f,r in combinations_with_replacement(('A','S','T'),2):
    if r!='T': continue
    t=monotonic()
    f0,r0,h0=polys(f,r)
    print(f,r,'bidegrees',[ (p.degree(U),p.degree(V)) for p in [f0,r0,h0]],'prep',monotonic()-t,flush=True)
    fs=project_resultant(f0,h0,U,V)
    rs=project_resultant(r0,h0,U,V)
    g0=fs.gcd(rs)
    R0=S.Poly.from_list([int(x) for x in g0.coeffs()[::-1]],V)
    assert R0.monic()==S.Poly(((V-2)*(V**3-3*V**2+1))**(111 if f==r else 27),V).monic()
    print(f,r,'only guarded denominator power',111 if f==r else 27,'elapsed',monotonic()-t,flush=True)
print('verified every arithmetic-late-singleton phase pair')
