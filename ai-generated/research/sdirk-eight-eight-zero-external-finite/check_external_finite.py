"""Fixed exact guarded projections for external affine roots in both finite-gap phases."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
from sys import argv
kind=argv[1]
assert kind in ('ghost','arith')
vdegree=3 if kind=='ghost' else 6
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
Hv=(v_**3-4*v_**2-v_+2 if kind=='ghost' else
    (8*v_**6-44*v_**5+22*v_**4+97*v_**3-55*v_**2-13*v_+6))
H=S.Poly(Hv,v_).monic()
assert Q.is_irreducible and H.is_irreducible
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
def ev(field,P,y):
    return sum((field.convert(x)*y**i for i,x in enumerate(P)),field.zero)
G=S.Poly(S.resultant(H,F.as_expr().subs(w_,z_-2*v_),v_),z_).monic()
assert G.degree()==6*vdegree and G.is_irreducible
S0,v=ring('v',E)
VH=sum((E.convert(x)*v**j for j,x in enumerate(H.all_coeffs()[::-1])),S0.zero)
w_z,v_z=recover(E,S0,S0(w)+2*v,VH,G,S0(w),v,6,vdegree)
K=S.QQ.algebraic_field((G,z_));z=K.unit
w=ev(K,w_z,z);v=ev(K,v_z,z);u=ev(K,u_w,w);b=ev(K,b_w,w)
assert u+b+2*v==z and not ev(K,H.all_coeffs()[::-1],v)
a=1+2*u
assert a and b and a!=b
assert not (4*u**3-12*u*u+3*u+2) and not (b*b-(2*u+4)*b+1+2*u)
now('primitive degree',G.degree())

C=lambda q,r=1:K.convert(S.Rational(q,r))
R,D,X=ring('D X',K)
I=lambda p:sum((q*C(1,j+1)*D**(i+j) for (i,j),q in p.items()),R.zero)

Z2=(X-a)*(X-b); Z3=X*Z2
J=lambda P:sum((c*C(1,j+1)*D**i*X**(j+1) for (i,j),c in P.items()),R.zero)
J2,J3=J(Z2),J(Z3)
def ex(p,x):return sum((c*x**j for (i,j),c in p.items()),K.zero)
J2a,J2b=ex(J2,a),ex(J2,b);J3a,J3b=ex(J3,a),ex(J3,b)
dj=J2a*J3b-J2b*J3a
assert dj==a*a*b*b*(a-b)**3*C(1,24) and dj
L=lambda x:70*x**4-140*D*x**3+90*D**2*x*x-20*D**3*x+D**4
ap=(-L(a)*J3b+L(b)*J3a)/R(dj)
bp=(-J2a*L(b)+J2b*L(a))/R(dj)
CC,rem=divmod(ap*(Z2-J2)+bp*(Z3-J3)-L(X),Z2)
assert not rem and CC.degree(X)==2
def evX(p,y):return sum((c*D**i*y**j for (i,j),c in p.items()),R.zero)
D1,DD=ring('q',K)
def ccollect(G,j):
 return D1.from_dict({(i,):z for (i,d),z in G.items() if d==j})
l0,l1,l2=[ccollect(CC,i) for i in range(3)]
def pair_times(x,y):
 a,b=x;c,d=y
 return a*c-b*d*l2*l0,a*d+b*c-b*d*l1
def nrm(poly):
 j=poly.degree(X)
 ps=[(D1.one,D1.zero)]
 for i in range(j):
  ps.append(pair_times(ps[-1],(D1.zero,D1.one)))
 a,b=D1.zero,D1.zero
 for i in range(j+1):
   z=ccollect(poly,i)*l2**(j-i)
   a+=z*ps[i][0];b+=z*ps[i][1]
 return a*a-a*b*l1+b*b*l2*l0

# Field inverses are done with FLINT polynomial extended gcd, once per divisor.
# Repeated SymPy ANP inversions of the same leading coefficient can blow up.
from flint import fmpq_poly, fmpq
from functools import lru_cache
fld=fmpq_poly([fmpq(str(x)) for x in reversed(G.all_coeffs())])
@lru_cache(None)
def inv_coeff(vals):
    raw=fmpq_poly([fmpq(str(x)) for x in vals[::-1]])
    g,s,t=raw.xgcd(fld)
    assert g.degree()==0
    v=s/g[0]
    return K.dtype(list(reversed(v.coeffs())),K.mod,K.dom)
def div_safe(f,g):
    assert g and f.ring==D1 and g.ring==D1
    m,n=f.degree(),g.degree()
    if m<n:return D1.zero,f
    leading=inv_coeff(tuple(g.LC.to_list()))
    gg=[g.get((i,),K.zero)*leading for i in range(n+1)]
    assert gg[-1]==K.one and leading*g.LC==K.one
    front=[f.get((i,),K.zero) for i in range(m+1)]
    qu=[K.zero]*(m-n+1)
    for j in range(m-n,-1,-1):
        z=front[j+n]
        qu[j]=z*leading
        for i,k in enumerate(gg[:-1]):front[j+i]-=z*k
    return (D1.from_dict({(i,):z for i,z in enumerate(qu) if z}),
            D1.from_dict({(i,):z for i,z in enumerate(front[:n]) if z}))
def small_gcd(f,g):
    while g:
        _,r=div_safe(f,g)
        f,g=g,r
    return f
def stripC2(poly):
    if not poly:return poly
    while poly.degree()>0:
        d=small_gcd(poly,l2)
        if d.degree()==0:break
        poly,rem=div_safe(poly,d)
        assert not rem
    return poly


# Work out the phase weights over the small rear field before lifting.
Vdom=S.QQ.algebraic_field((H,v_))
vsmall=Vdom.unit
kap=1+2*vsmall-vsmall*vsmall
hh=vsmall**3-4*vsmall*vsmall-vsmall+2
qq=4*vsmall**3-12*vsmall*vsmall+3*vsmall+2
assert vsmall and kap
if kind=='ghost':
 aa,bb,cc=kap,Vdom.convert(-2),Vdom.zero
else:
 assert hh and qq
 aa,bb,cc=kap*qq,-2*qq,-hh
pp0,pp1,pp2=aa+bb+cc,vsmall*(aa-cc),vsmall**2*(aa+cc)
pp3=vsmall**2*pp1
delta=pp0*pp2-pp1*pp1
assert delta
h1=(pp1*pp2-pp0*pp3)/delta
h0=(pp1*pp3-pp2*pp2)/delta
def lift(c):
    return ev(K,c.to_list()[::-1],v)
p0,p1,p2=map(lift,(pp0,pp1,pp2))
s0,s1=map(lift,(h0,h1))
if kind=='ghost':assert not s0 and s1==-v
now('nonzero phase Hankel pivot')

P,T=ring('T',R.to_domain())
co=lambda z:P(R(z))
sig=(T-co(a))*(T-co(b))*(T-co(X))
m=D-1-v
Y=T-co(m)
def I1(P):
    return sum((x*D**j*C(1,j+1) for (j,),x in P.items()),R.zero)
def J1(P):
    return P.ring.from_dict({(j+1,):x*C(1,j+1) for (j,),x in P.items()})
S2=Y**2+co(s1)*Y+co(s0)
e=sig-J1(sig)
M=[I1(Y**j*sig) for j in range(5)]
E=[I1(Y**j*e) for j in range(4)]
r=[M[j+2]+s1*M[j+1]+s0*M[j] for j in (0,1,2)]
L0=E[2]+s1*E[1]+s0*E[0]
Ld=I1(S2*(Y*sig-J1(Y*sig)))
Le=E[3]+s1*E[2]+s0*E[1]
F=[(M[j+1]*p2-M[j+2]*p1)*E[0]+(M[j+2]*p0-M[j]*p2)*E[1]+(M[j]*p1-M[j+1]*p0)*E[2] for j in (0,1)]
A0=L0**2*r[2]-L0*(Ld+Le)*r[1]+Ld*Le*r[0]
A1=L0*F[1]-Ld*F[0]
now('biv degrees',[(v.degree(D),v.degree(X)) for v in (L0,Ld,Le,A0,A1)])

def nrm_pair(poly):
    j=poly.degree(X)
    pp,qq=D1.zero,D1.zero
    z,w=D1.one,D1.zero
    for i in range(j+1):
        f=ccollect(poly,i)*l2**(j-i)
        pp+=f*z;qq+=f*w
        z,w=pair_times((z,w),(D1.zero,D1.one))
    return pp,qq
def norm(f):
    p,q=nrm_pair(f)
    n=p*p-p*q*l1+q*q*l2*l0
    n1,r=div_safe(n,l2**f.degree(X))
    assert not r
    j=min(i[0] for i in n1)
    n2=D1.from_dict({(i[0]-j,):f for i,f in n1.items()})
    now('norm degrees',n.degree(),n1.degree(),n2.degree(),j)
    return n2
piv=[norm(k) for k in (L0,Ld,Le)]
nA=[norm(k) for k in (A0,A1)]
assert tuple(x.degree() for x in piv)==(16,18,18)
assert tuple(x.degree() for x in nA)==(46,42)

def rr(a,p):
    s=S.Rational(str(a));return int(s.p)*pow(int(s.q),-1,p)%p
def evk(a,z0,p):
    n=0
    for k in a.to_list():n=(n*z0+rr(k,p))%p
    return n
def specialize(pol,p,z0,degree=True):
    if not pol:return nmod_poly([],p)
    q=nmod_poly([evk(pol.get((i,),K.zero),z0,p) for i in range(pol.degree()+1)],p)
    if degree and q.degree()!=pol.degree(): raise ValueError('lead drops')
    return q
def on_fiber(p,z0):
    gp=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
    if gp(z0)!=0 or gp.derivative()(z0)==0:return
    try:
        pivp=list(map(lambda h:specialize(h,p,z0),piv))
        nap=list(map(lambda h:specialize(h,p,z0),nA))
        l2p=specialize(l2,p,z0); l1p,l0p=(specialize(k,p,z0,False) for k in (l1,l0))
        dlp=l2p.gcd(l1p)
        if dlp.degree():print('bad lin pivot',dlp.degree());return
        def lin(f):
            deg=f.degree(X)
            vals=[specialize(ccollect(f,j),p,z0,False)%l2p for j in range(deg+1)]
            return sum((vals[j]*(-l0p).pow_mod(j,l2p)*l1p.pow_mod(deg-j,l2p) for j in range(deg+1)),nmod_poly([],p))%l2p
        v1=pivp[0].gcd(pivp[1]).gcd(pivp[2]);v2=nap[0].gcd(nap[1])
        lA=l2p.gcd(lin(A0)).gcd(lin(A1))
        lP=l2p.gcd(lin(L0)).gcd(lin(Ld)).gcd(lin(Le))
        print('exact degree-preserving gcd degrees',v1.degree(),v2.degree(),lA.degree(),lP.degree(),flush=True)
        if not any(q.degree() for q in (v1,v2,lA,lP)):return (p,z0)
    except ValueError:return

p,z0={'ghost':(59,1),'arith':(103,65)}[kind]
assert p>7 and S.isprime(p)
assert on_fiber(p,z0)==(p,z0)
print("verified",kind,p,z0,flush=True)
