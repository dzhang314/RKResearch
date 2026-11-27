"""Exact scalar incompatibility of the logged two ports with a 7-site AP-start rule."""
from fractions import Fraction
import sys
from pathlib import Path
port_dir=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'real-sdirk13-forward-ports'
sys.path.insert(0,str(port_dir))
from check_two_ports import I,ev,cert_roots,cert_ports,solve
import sympy as s

g,d,x=s.symbols('g d x')
Q={k:s.Poly(s.legendre(k,2*x-1),x)for k in range(5,9)}
P6,P7=(Q[k].as_expr()for k in (6,7))
F=P7*P6.subs(x,g)-P6*P7.subs(x,g)
fq,rem=s.div(s.expand(F),x-g,x)
assert rem==0
U=s.Poly(fq.subs(x,g+d),d)
V=s.Poly(s.cancel((fq.subs(x,g+2*d)-U.as_expr())/d),d)
R=s.Poly(s.resultant(U.as_expr(),V.as_expr(),d),g)
assert not R.is_zero
P6g=s.Poly(P6.subs(x,g),g)
assert Q[6].gcd(Q[7]).degree()==0
R0=s.Poly(1,g)
for f,m in R.factor_list()[1]:
    if f.gcd(P6g).degree()==0 and f.nth(0):
        R0*=f
assert R0.degree()==90 and R0.gcd(R0.diff()).degree()==0
boxes=R0.intervals(eps=s.Rational(1,10**30))
assert len(boxes)==R0.count_roots()
for k,((a,b),m) in enumerate(boxes):
    assert m==1 and R0.count_roots(a,b)==1
    assert not k or boxes[k-1][0][1]<a
[U,[z,v,w],coeff]=cert_ports(cert_roots())
P=[list(reversed(Q[i].all_coeffs()))for i in (6,7)]
def E(p,x):return ev([I.val(Fraction(u))for u in p],x)
def patch(l,r):
    return I(I.val(Fraction(l)).lo,I.val(Fraction(r)).hi)
best={}
for port,name in [(v,'v'),(w,'w')]:
    minima=[]
    for (a,b),m in boxes:
        G=patch(a,b)
        # Full cross polynomial includes possible coincident labels.
        y=1-G*port
        e=E(P[1],y)*E(P[0],G)-E(P[1],G)*E(P[0],y)
        assert e.sign(),f'not separated {name} {a} {b}'
        minima.append(e.inf())
    best[name]=min(minima).bit_length()-1-256
print(f'{len(boxes)} exact real common-diagonal boxes; ports separated by cross-polynomial magnitudes >= 2^({best["v"]}), 2^({best["w"]})')
# The separate no-edge first-three seed at the two quadratic Laguerre roots.
U2=s.Poly(fq.subs(x,(2+s.sqrt(2))*g),g,extension=s.sqrt(2))
V2=s.Poly(fq.subs(x,(2-s.sqrt(2))*g),g,extension=s.sqrt(2))
assert U2.gcd(V2).degree()==0
print('Both unit-diagonal quadratic Laguerre roots plus the first site are impossible on any 7-site precision-12 grid.')
