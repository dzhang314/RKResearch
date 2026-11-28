"""True rank-drop shared-center quadratic split opener."""
import sympy as S
from sympy.polys.rings import ring
from shared_split_fullrank import N,J,E,p,DD

u=S.Symbol('u')
A=lambda u:(-4*u**3-7*u*u+6*u)/(3*u*u-8*u+4)
Bnum=lambda u:2*u**3-4*u*u+5*u-2
v0=S.Poly(Bnum(u),u)
print('same gap B factors',[(g.degree(),i) for g,i in v0.factor_list()[1]])
assert v0.is_irreducible
for f,j in v0.factor_list()[1]:
    K=S.QQ.algebraic_field((f,u));t=K.unit
    aa=K.convert(S.Rational(6,7));c=K.convert(S.Rational(3,35))
    w=A(t);p0=t*t
    delta=-(5*w*w/3+K.convert(S.Rational(5,7)))
    U,V=-5*p0-delta,4*p0*p0-w*w
    T,S0=-aa-delta,c-w*w
    assert U*S0-V*T
print('same gap rank drop excluded by even quartic mask')
g=N.resultant(J,'p')
from shared_split_fullrank import m
assert g==256*m*m*(3*m-8)*(16*m-7) or g==-256*m*m*(3*m-8)*(16*m-7)
print('unequal gap projection',g.factor())
for m0 in (0,S.Rational(8,3),S.Rational(7,16)):
    t=S.Symbol('t')
    def im(f):
        return S.Poly(sum(int(c)*m0**int(i)*t**int(j) for (i,j),c in f.to_dict().items()),t)
    F=im(N).gcd(im(J)).monic()
    print('rank drop m',m0,'raw',S.factor(F.as_expr()),flush=True)
    for h in (p,E,DD):
        while (d:=F.gcd(im(h))).degree()>0:F=F.exquo(d)
    print('  after known head guards',S.factor(F.as_expr()),flush=True)
    assert F.as_expr()=={0:t*t-S.Rational(9,2)*t-2,S.Rational(8,3):S.Integer(1),S.Rational(7,16):t+S.Rational(1,8)}[m0]
# m=7/16 is the sole geometric rank-drop pair not already forbidden.
m0,p0=S.Rational(7,16),-S.Rational(1,8)
d,z=S.symbols('d Z')
E0=m0*m0-4*p0
Md=S.Poly(d*d-E0,d,domain=S.QQ)
def mod(f):
    u0,v0=S.fraction(S.cancel(f))
    return S.rem(u0*S.invert(v0,Md.as_expr(),d),Md.as_expr(),d)
uu=(m0+d)/2;vv=(m0-d)/2
B=lambda u:(2*u**3-4*u*u+5*u-2)/(3*u*u-8*u+4)
w0,w1=mod(A(uu)),mod(d*B(uu))
assert w0==mod(A(vv)) and w1==mod(-d*B(vv))
assert not (w0.free_symbols|w1.free_symbols)
w=w0+w1*z
assert w==S.Rational(59,128)*z-S.Rational(1,4)
C0=35*w*w+42*w+15-21*E0*z*z
S0=w*w-w*(E0*(z*z-3*z+2)-5*p0)+4*p0*p0
S1=E0*z*(z-1)*(z-2)+w*(3-2*z)+p0*(6-5*z)
F0=5*z*S0+(5*w+3)*S1
g=S.Poly(C0,z).gcd(S.Poly(F0,z))
print('rank drop w',w,'mask gcd',g.as_expr())
assert g.degree()==0
