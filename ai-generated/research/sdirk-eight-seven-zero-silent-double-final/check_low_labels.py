"""No low-label reflected-zero chart for the silent constant double."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
assert Q.is_irreducible
K=S.QQ.algebraic_field((Q,u_));u=K.unit
R,b=ring('b',K)
Bb=b*b-(2*u+4)*b+1+2*u
F=S.Poly(S.resultant(Q,(b_**2-(2*u_+4)*b_+1+2*u_).subs(b_,w_-u_),u_),w_).monic()
assert F.degree()==6 and F.is_irreducible
def recover(K,R,t,mod,f,aa,bb,n,m):
    def vec(p):
        return S.Matrix([S.Rational(str((p.get((j,),K.zero).to_list()[::-1]+[0]*n)[i]))
                         for j in range(m) for i in range(n)])
    C=S.Matrix.hstack(*(vec(t**i%mod) for i in range(n*m)))
    C=C.inv()
    a=C*vec(aa);b=C*vec(bb)
    def eval(z):
        return sum((R(K.convert(x))*t**i%mod for i,x in enumerate(z)),R.zero)%mod
    assert eval(a)==aa and eval(b)==bb and not eval(f.all_coeffs()[::-1])
    return a,b
u_w,b_w=recover(K,R,R(u)+b,Bb,F,R(u),b,3,2)
E=S.QQ.algebraic_field((F,w_));w=E.unit
S0,v=ring('v',E)



def ev(K,P,y):
    return sum((K.convert(x)*y**i for i,x in enumerate(P)),K.zero)
ue=ev(E,u_w,w);be=ev(E,b_w,w)
V0=v*v+(ue-3)*v+ue*ue-3*ue+E.convert(S.Rational(3,4))
total=S.Poly(S.resultant(Q.as_expr().subs(u_,v_),F.as_expr().subs(w_,z_-2*v_),v_),z_).monic()
diagonal=total.gcd(S.Poly(S.resultant(Q,(b_**2-(2*u_+4)*b_+1+2*u_).subs(b_,z_-3*u_),u_),z_).monic())
assert diagonal.degree()==6 and diagonal.is_irreducible
G=total.exquo(diagonal)
assert G.degree()==12 and G.is_irreducible
w_z,v_z=recover(E,S0,S0(w)+2*v,V0,G,S0(w),v,6,2)
L=S.QQ.algebraic_field((G,z_));z=L.unit
wl=ev(L,w_z,z);vl=ev(L,v_z,z)
ul=ev(L,u_w,wl);bl=ev(L,b_w,wl)
assert wl+2*vl==z and vl!=ul
assert not (vl**3-3*vl**2+L.convert(S.Rational(3,4))*vl+L.convert(S.Rational(1,2)))
assert not (vl*vl+(ul-3)*vl+ul*ul-3*ul+L.convert(S.Rational(3,4)))
# The terminal three clocks cannot be three distinct fourth-Gauss nodes.
x,y=S.symbols('x y')
L4=lambda t:70*t**4-140*t**3+90*t*t-20*t+1
diff=S.cancel((L4(y)-L4(x))/(y-x))
for z3 in (2*y-x,4*x-y):
    proj=S.resultant(diff,L4(z3),y)
    assert S.Poly(proj,x).gcd(S.Poly(L4(x),x)).degree()==0
print("both distinct Gaussian rear triples excluded",flush=True)

def test(K,u,b,v,index):
    C=lambda a,b=1:K.convert(S.Rational(a,b))
    a=1+2*u
    assert a!=b and v and all(b-a!=i*v for i in (-2,-1,1,2))
    R,D,X=ring('D,X',K)
    sp=[D-1-i*v for i in range(3)]
    p=(X-a)*(X-b)
    for si in sp:p*=X-si
    def I(P):
        return sum((c*C(1,j+1)*D**(i+j) for (i,j),c in P.items()),R.zero)
    g=I(p).gcd(I(X*p)).gcd(I(X**2*p)).monic()
    deg=g.degree(D)
    print(index,'generic five nodal gcd degree',deg,flush=True)
    assert deg==0 and g==R.one
    for f in (a,b):
      for i in range(3):
        d=1+f+i*v
        if not d:continue
        arr=list(dict.fromkeys([a,b]+[d-1-j*v for j in range(3)]))
        assert len(arr)==4
        P=R.one
        for c0 in arr:P*=X-c0
        vals=[I(X**j*P).evaluate(D,d) for j in range(3)]
        assert vals[0]*vals[2]!=vals[1]**2
    print(index,'six one-overlap determinants nonzero',flush=True)
test(E,ue,be,ue,'equal v')
test(L,ul,bl,vl,'other v')
