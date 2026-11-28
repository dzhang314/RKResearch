"""Exact ghost and arithmetic receipts for a live early affine numerator root."""
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

P,T=ring('T',R.to_domain())
co=lambda z:P(R(z))
slot=int(argv[2])
assert slot in (0,1,2)
q=[a,b,X][slot]
s=D-1;m=D-2
Z3T=(T-co(a))*(T-co(b))*(T-co(X))
t=s-v;r=s-2*v
k=1+2*v-v*v
H0=v**3-4*v*v-v+2
Q0=4*v**3-12*v*v+3*v+2
rear=[s,t,r]
U5T=Z3T*(T-co(s))*(T-co(t))*(T-co(r))
F_s=U5T//(T-co(s)); F_t=U5T//(T-co(t)); F_r=U5T//(T-co(r))
masks=[co(k*(s-q))*F_t-co(t-q)*F_s,
       F_r if kind=='ghost' else -co(k*Q0*(s-q))*F_r-co(H0*(r-q))*F_s]
U3T=U5T//(T-co(q))
baseguards=[x-y for x in rear for y in (a,b)]
def I1(P):
    return sum((x*D**j*C(1,j+1) for (j,),x in P.items()),R.zero)
def red_field(L,t):
    return sum((q*D**i*t**j for (i,j),q in L.items()),R.zero)
def det3(M):
    a,b,c=M
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
uT=((Z3-J3)*J2b-(Z2-J2)*J3b)/R(dj)
vT=((Z2-J2)*J3a-(Z3-J3)*J2a)/R(dj)
assert red_field(uT,a)==R.one and not red_field(uT,b)
assert not red_field(vT,a) and red_field(vT,b)==R.one
L0,L1,L2,L3=R.one,2*X-D,6*X**2-6*D*X+D**2,20*X**3-30*D*X**2+12*D**2*X-D**3
L4=L(X)
LL=[L0,L1,L2,L3]
def K_at(t):
    return sum(((2*j+1)*D**(6-2*j)*red_field(L,q)*red_field(L,t)
                for j,L in enumerate(LL)),R.zero)
EK=K_at(X)-uT*K_at(a)-vT*K_at(b)
H1,rr1=divmod(EK,Z2)
assert not rr1
wq=(-uT,-vT,R.one)[slot]
u3q=R.one
for x in rear:u3q*=q-x
for i,t in enumerate([a,b,X]):
    if i!=slot: u3q *= q-t
H2,rr2=divmod(wq*u3q,Z2)
assert not rr2
now('shape degrees',[(g.degree(D),g.degree(X)) for g in (H1,H2)])
M=[[I1(M*T**j) for j in range(3)] for M in masks]
mat3=[I1(U3T*T**j) for j in range(3)]
M += [[H1*mat3[j]-D**6*H2*q**j for j in range(3)]]
A0=det3(M)
now('A0 degrees',A0.degree(D),A0.degree(X))
def asD(p):
    return D1.from_dict({(i,):z for (i,j),z in p.items()})
def strip_linear(p,s):
    n=0
    while p.degree()>0:
        a,b=div_safe(p,s)
        if b:break
        p=a;n+=1
    return p,n
def nrm_pair(poly):
    j=poly.degree(X)
    pp,qq=D1.zero,D1.zero
    z,w=D1.one,D1.zero
    for i in range(j+1):
        f=ccollect(poly,i)*l2**(j-i)
        pp+=f*z;qq+=f*w
        z,w=pair_times((z,w),(D1.zero,D1.one))
    return pp,qq
def pairnorm(a,b):
    return a*a-a*b*l1+b*b*l2*l0
an,bn=nrm_pair(A0)
now('projection pair',an.degree(),bn.degree())
nr0=pairnorm(an,bn)
now('unstripped norm',nr0.degree())
assert nr0.degree()==({'ghost': (86,86,110), 'arith': (88,88,120)}[kind][slot])
Nr,rr=div_safe(nr0,l2**A0.degree(X))
now("safe leading-factor division complete",Nr.degree())
assert not rr
now('degree after l2 factors',Nr.degree())
for g in [DD]+list(map(asD,baseguards)):
    if not g:continue
    Nr,n=strip_linear(Nr,g)
    print('linear guard multiplicity',n,flush=True)
now('guarded norm degree',Nr.degree())
assert Nr.degree()==({'ghost': (48,48,66), 'arith': (48,48,72)}[kind][slot])

collision=[]
if slot==2:
    for rear_number,rear_expression in enumerate(rear):
        test=rear_expression
        H=asD(red_field(CC,test))
        assert H.degree()==6
        Nr,multiplicity=strip_linear(Nr,H)
        now("collision exact division",rear_number,H.degree(),multiplicity)
        assert multiplicity==(2 if kind=='arith' and rear_number==0 else 1)
        tt=asD(test)
        ht=div_safe(an+bn*l2*tt,H)[1]
        now("collision branch remainder",ht.degree(),not ht)
        assert not ht
        collision.append(H)
# Exact rank intersection on the two early labels other than q.
if slot==0:
    Ec=red_field(L4,b)*K_at(X)-L4*K_at(b)
    E,rm=divmod(Ec,X-b)
    assert not rm
elif slot==1:
    Ec=L4*K_at(a)-red_field(L4,a)*K_at(X)
    E,rm=divmod(Ec,X-a)
    assert not rm
else:
    E=red_field(L4,a)*K_at(b)-red_field(L4,b)*K_at(a)
e1,e2=nrm_pair(E)
E_nr=e1*e1-e1*e2*l1+e2*e2*l2*l0
Hrank,pr=div_safe(E_nr,l2**E.degree(X))
assert not pr
Hrank,eta=strip_linear(Hrank,DD)
now('rank guard degree',Hrank.degree(),E_nr.degree(),eta)
def H_rem(v):return div_safe(v,Hrank)[1]
rrank=H_rem(H_rem(e1)*H_rem(bn)-H_rem(e2)*H_rem(an))
now('rank exact branch remainder',rrank.degree(),not rrank)
assert not rrank
u0,u1=nrm_pair(wq)
WN=u0*u0-u0*u1*l1+u1*u1*l2*l0
Nr,rem=div_safe(Nr,Hrank)
now('after exact saturation',Nr.degree())
assert not rem and Hrank.degree()==30 and Nr.degree()==18
def rr(a,p):
    s=S.Rational(str(a));return int(s.p)*pow(int(s.q),-1,p)%p
def evk(a,z0,p):
    n=0
    for k in a.to_list():n=(n*z0+rr(k,p))%p
    return n
def specialize(pol,p,z0,degree=True):
    q=nmod_poly([evk(pol.get((i,),K.zero),z0,p) for i in range(pol.degree()+1)],p)
    if degree and q.degree()!=pol.degree(): raise ValueError('lead drops')
    return q
def expoly(pol,p,z0):
    if not pol:return []
    return [specialize(ccollect(pol,j),p,z0,False) for j in range(pol.degree(X)+1)]
def on_fiber(p,z0,debug=False):
    gp=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
    if gp(z0)!=0 or gp.derivative()(z0)==0:return
    zero,one=nmod_poly([],p),nmod_poly([1],p)
    d=nmod_poly([0,1],p)
    try:
        ff=specialize(Nr,p,z0); l2p=specialize(l2,p,z0)
        l0p,l1p,ap,bp=[specialize(q,p,z0,False) for q in (l0,l1,an,bn)]
        cp=[specialize(h,p,z0) for h in collision]
        hp=specialize(Hrank,p,z0); wp=specialize(WN,p,z0,False)
        if any(h.gcd(g).degree() for h in cp for g in (l2p,bp)):
            if debug: print('collision branch pivot issue',flush=True)
            return
        if any(hp.gcd(g).degree() for g in (l2p,bp,wp)):
            if debug: print('rank branch pivot issue',flush=True)
            return
        def R_eval(f,c,F):
            e=zero
            for z in expoly(f,p,z0)[::-1]:e=(e*c+z)%F
            return e
        def unit(a,F):
            g,u,v=a.xgcd(F)
            if g.degree()!=0:return
            return u*pow(int(g[0]),-1,p)%F
        # Leading-drop check, independent of the regular quotient.
        ls=unit(l1p,l2p)
        if ls is None:return
        chdrop=-l0p*ls%l2p
        a0drop=R_eval(A0,chdrop,l2p)
        ldrop=l2p.gcd(a0drop)
        if ldrop.degree():
            if debug:print('leading drop cases',ldrop.degree(),flush=True)
            return
        p2=unit(l2p,ff)
        if p2 is None:
            if debug:print('regular leading coefficient collision',l2p.gcd(ff).degree(),flush=True)
            return
        bp0=unit(bp,ff)
        if bp0 is None:
            if debug:print('regular linear c pivot collision',ap.gcd(bp).gcd(ff).degree(),bp.gcd(ff).degree(),flush=True)
            return
        ch=-ap*bp0%ff; c=ch*p2%ff
        assert not ((l2p*c*c+l1p*c+l0p)%ff)
        assert not R_eval(A0,c,ff)
        diag=unit(d,ff)
        if diag is None:
            if debug:print('diagonal issue',flush=True)
            return
        a0=evk(a,z0,p);b0=evk(b,z0,p);q0=[a0*one,b0*one,c][slot]
        xx=[a0*one,b0*one,c]
        rc=[[R_eval(j,c,ff) for j in row] for row in M]
        mb0=[R_eval(q,c,ff) for q in mat3]
        (f0,f1,f2),(g0,g1,g2),_ = rc
        delta=(f0*g1-f1*g0)%ff
        adi=unit(delta,ff)
        if adi is None:
            if debug:print('Ordinary pivot',delta.gcd(ff).degree(),flush=True)
            return
        p0=(f1*g2-f2*g1)*adi%ff
        p1=(f2*g0-f0*g2)*adi%ff
        assert all(not ((a*p0+b*p1+e)%ff) for a,b,e in rc)
        mean3=(mb0[2]+p1*mb0[1]+p0*mb0[0])%ff
        me3=unit(mean3,ff)
        if me3 is None:
            if debug:print('cardinal jump pivot',mean3.gcd(ff).degree(),flush=True)
            return
        u3q1=R_eval(u3q,c,ff)
        jump=-u3q1*(q0*q0+p1*q0+p0)*d**6*me3%ff

        def prod(A,B):
            C=[zero]*(len(A)+len(B)-1)
            for i,x in enumerate(A):
                for j,y in enumerate(B): C[i+j]=(C[i+j]+x*y)%ff
            return C
        def scl(A,x):
            return [q*x%ff for q in A]
        def add(A,B):
            n=max(len(A),len(B))
            return [((A[i] if i<len(A) else zero)+(B[i] if i<len(B) else zero))%ff for i in range(n)]
        def evR(A,t):
            y=zero
            for a in A[::-1]:y=(y*t+a)%ff
            return y
        L0,L1,L2,L3=[one],[-d,one*2],[d**2,-6*d,one*6],[-d**3,12*d**2,-30*d,one*20]
        L4=[d**4,-20*d**3,90*d**2,-140*d,one*70]
        K_t=[zero]
        for j,L in enumerate([L0,L1,L2,L3]):
            K_t=add(K_t,scl(L,(2*j+1)*d**(6-2*j)*evR(L,q0)))
        ee=[[evR(L4,t),(evR(K_t,t)+(jump if i==slot else zero))%ff] for i,t in enumerate(xx[:2])]
        (h0,k0),(h1,k1)=ee; dv=(h0*k1-h1*k0)%ff
        if unit(dv,ff) is None:
            if debug:print('forward first-two pivot',dv.gcd(ff).degree(),flush=True)
            return
        def poly_nodes(nodes):
            r=[one]
            for x in nodes:r=prod(r,[-x,one])
            return r
        Z=poly_nodes(xx)
        JZ=[zero]+[z*pow(j+1,-1,p)%ff for j,z in enumerate(Z)]
        ba,bb=(-evR(JZ,j) for j in (a0,b0))
        f4=(ba*k1-bb*k0)%ff; f5=(h0*bb-h1*ba)%ff
        h=add(scl(add(Z,scl(JZ,-1)),dv),add(scl(L4,-f4),scl(K_t,-f5)))
        ZX=poly_nodes([v for i,v in enumerate(xx) if i!=slot])
        # Divide the cleared fourth gate by the two previous singleton nodes.
        assert ZX[-1]==one
        KK=[zero]*(len(h)-len(ZX)+1)
        for j in range(len(KK)-1,-1,-1):
            KK[j]=h[j+len(ZX)-1]
            for i,x in enumerate(ZX): h[i+j]=(h[i+j]-KK[j]*x)%ff
        assert not any(h)
        r0=(KK[0]-p0*KK[2])%ff; r1=(KK[1]-p1*KK[2])%ff
        n4=(r0*r0-p1*r0*r1+p0*r1*r1)%ff
        if n4.gcd(ff).degree():
            if debug:print('fourth failed',n4.gcd(ff).degree(),flush=True)
            return
        return ff.degree(),p,z0
    except ValueError:return

p,z0=({'ghost':((17,6),)*3, 'arith':((59,28),(59,28),(103,65))}[kind][slot])
assert S.isprime(p) and p>7
cert=on_fiber(p,z0,True)
assert cert==(18,p,z0)
print("verified",kind,slot,cert,flush=True)
