"""Fixed number-field fibres for the eight-distinct simultaneous b,z-zero root."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from sys import argv
kind=argv[1]
assert kind in ('ghost','star')
vdegree=3
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
Hv=v_**3-4*v_**2-v_+2
H=S.Poly(Hv,v_).monic()
assert Q.is_irreducible and (kind=='star' or H.is_irreducible)
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
    I=C.inv()
    a=I*vec(aa);b=I*vec(bb)
    def ev0(z):
        return sum((R(K.convert(x))*t**i%mod for i,x in enumerate(z)),R.zero)%mod
    assert ev0(a)==aa and ev0(b)==bb and not ev0(f.all_coeffs()[::-1])
    return a,b
u_w,b_w=recover(K,R,R(u)+b,Bb,F,R(u),b,3,2)
E=S.QQ.algebraic_field((F,w_));w=E.unit
if kind=='star':
    G=F
else:
    G=S.Poly(S.resultant(H,F.as_expr().subs(w_,z_-2*v_),v_),z_).monic()
    assert G.degree()==6*vdegree and G.is_irreducible
    S0,v=ring('v',E)
    VH=sum((E.convert(x)*v**j for j,x in enumerate(H.all_coeffs()[::-1])),S0.zero)
    w_z,v_z=recover(E,S0,S0(w)+2*v,VH,G,S0(w),v,6,vdegree)
def rr(a,p):
    s=S.Rational(str(a));return int(s.p)*pow(int(s.q),-1,p)%p
def ev(coords,y,p):
    return sum(rr(co,p)*pow(y,i,p) for i,co in enumerate(coords))%p

if kind=='star':
    w_z,v_z=None,None

def test(p,u,b,v,side):
    a=(1+2*u)%p
    beta=(a,b)[side]; ell=(b,a)[side]
    if not a or not b or a==b:return
    kap=(1+2*v-v*v)%p
    if kind=='ghost' and (not kap or not v):return
    zero,one=nmod_poly([],p),nmod_poly([1],p)
    X=D=nmod_poly([0,1],p)
    Z2=(X-a)*(X-b); Z3=X*Z2
    J=lambda S:nmod_poly([0]+[int(S[i])*pow(i+1,-1,p)%p for i in range(S.degree()+1)],p)
    J2,J3=J(Z2),J(Z3)
    e=lambda f,x:int(f(x))
    dj=(e(J2,a)*e(J3,b)-e(J2,b)*e(J3,a))%p
    assert dj
    F=e(J3,ell)*Z2-e(J2,ell)*Z3
    tail,rem=divmod(F-J(F), X-ell)
    assert not rem
    if tail.degree()!=3:return
    cs=tail.roots()
    if len(cs)!=3 or any(m!=1 for _,m in cs):return
    L=lambda x:70*x**4-140*D*x**3+90*D**2*x**2-20*D**3*x+D**4
    al=(-L(a)*e(J3,b)+L(b)*e(J3,a))*pow(dj,-1,p)
    be=(-e(J2,a)*L(b)+e(J2,b)*L(a))*pow(dj,-1,p)
    yes=[]
    for C,_ in cs:
        C=int(C)
        z=e(Z2,C)
        if not z:return
        Dp=(al*(z-e(J2,C))+be*(e(Z3,C)-e(J3,C))-L(C))*pow(z,-1,p)
        if Dp.degree()!=4:return
        # Ordinary polynomials in T with coefficients in Fp[D].
        def mask(*roots):
            P=[one]
            for t in roots:
                P=[-t*P[0]]+[P[k-1]-t*P[k] for k in range(1,len(P))]+[P[-1]]
            return P
        s,t,r=D-1,D-1-v,D-1-2*v
        if kind=='ghost':
            f=mask(ell,C,s,t,r)
            f0=mask(ell,C,s,r)
            f1=mask(ell,C,t,r)
            B=[f,[kap*x-y for x,y in zip(f0,f1)],mask(ell,C,s,t)]
        else:
            m=D-2
            B=[mask(ell,C,s),mask(ell,C,s,m,m), [x-2*y for x,y in zip(mask(ell,C,m,m),mask(ell,C)+[zero,zero])]]
        I=lambda q,k:sum((z*D**(k+j)*pow(k+j+1,-1,p) for j,z in enumerate(q)),zero)
        aa,bb,cc=[[I(M,k)%Dp for k in range(3)] for M in B]
        pp=aa[0]*(bb[1]*cc[2]-bb[2]*cc[1])-aa[1]*(bb[0]*cc[2]-bb[2]*cc[0])+aa[2]*(bb[0]*cc[1]-bb[1]*cc[0])
        if pp.gcd(Dp).degree():return
        yes.append((C,list(map(int,Dp.coeffs()))))
    return yes

def on_fiber(p,z0,side):
    gp=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
    if gp(z0)!=0 or gp.derivative()(z0)==0:return
    try:
        W,v=(z0,0) if kind=='star' else [ev(x,z0,p) for x in (w_z,v_z)]
        u,b=[ev(x,W,p) for x in (u_w,b_w)]
    except ValueError:return
    ans=test(p,u,b,v,side)
    if ans:return (p,z0,u,b,v,ans)

if __name__=='__main__':
    rows={'ghost': ((139,80),(83,26)), 'star': ((79,36),(103,73))}
    for side,(p,z0) in enumerate(rows[kind]):
        assert p>7 and S.isprime(p)
        ans=on_fiber(p,z0,side)
        assert ans is not None
        print(kind,side,ans)
