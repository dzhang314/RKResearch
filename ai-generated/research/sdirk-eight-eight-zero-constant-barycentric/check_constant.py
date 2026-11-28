"""Constant reverse barycentric numerator: exact exclusions of all three rear phases."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
from sys import argv
kind=argv[1]
assert kind in ('ghost','arith','star')
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
if kind=='star':
    K=E;z=w;G=F
    u=ev(K,u_w,w);b=ev(K,b_w,w)
    assert u+b==z
else:
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
def stripC2(poly):
 while poly.degree()>0:
  d=poly.gcd(l2)
  if d.degree()==0:break
  poly=poly//d
 return poly


P,T=ring('T',R.to_domain())
co=lambda z:P(R(z))
F=(T-co(a))*(T-co(b))*(T-co(X))
s=D-1
if kind=='star':
    m=D-2
    masks=[F*(T-co(s)),F*((T-co(m))**2-2)]
    P8eff=F*(T-co(s))*(T-co(m))**2
    baseguards=[s-a,s-b]
else:
    t=s-v;r=s-2*v
    k=1+2*v-v*v
    U0=F*(T-co(s))*(T-co(t))*(T-co(r))
    Fs=U0//(T-co(s));Ft=U0//(T-co(t));Fr=U0//(T-co(r))
    H0=v**3-4*v*v-v+2
    Q0=4*v**3-12*v*v+3*v+2
    masks=[co(k)*Ft-Fs, Fr if kind=='ghost' else -co(k*Q0)*Fr-co(H0)*Fs]
    P8eff=U0
    baseguards=[x-y for x in (s,t,r) for y in (a,b)]
def I1(P):
    return sum((x*D**j*C(1,j+1) for (j,),x in P.items()),R.zero)
def red_field(L,t):
    return sum((q*D**i*t**j for (i,j),q in L.items()),R.zero)
def det3(M):
    a,b,c=M
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
uT=((Z3-J3)*J2b-(Z2-J2)*J3b)/R(dj)
vT=((Z2-J2)*J3a-(Z3-J3)*J2a)/R(dj)
# uT,vT express any grade-four pure value at clock X in terms of its first two reads.
assert red_field(uT,a)==R.one and not red_field(uT,b)
assert not red_field(vT,a) and red_field(vT,b)==R.one
L3=20*X**3-30*D*X**2+12*D**2*X-D**3
L4=L(X)
L5=252*X**5-630*D*X**4+560*D**2*X**3-210*D**3*X**2+30*D**4*X-D**5
def de(L):
    pol,rm=divmod(L-uT*red_field(L,a)-vT*red_field(L,b),Z2)
    assert not rm
    return pol
g3,g5=de(L3),de(L5)
assert de(L4)==-CC
now('shape degrees',[(g.degree(D),g.degree(X)) for g in (g3,g5)])
M=[[I1(M*T**j) for j in range(3)] for M in masks]
bint=[I1(P8eff*T**j) for j in range(3)]
M += [[35280*g3*bint[0],35280*g3*bint[1],D**6*g5+35280*g3*bint[2]]]
now('moments built',[(k[0].degree(D),k[0].degree(X)) for k in M])
A0=det3(M)
now('A0 degrees',A0.degree(D),A0.degree(X))
def asD(p):
    return D1.from_dict({(i,):z for (i,j),z in p.items()})
def strip_linear(p,s):
    n=0
    while p.degree()>0:
        a,b=divmod(p,s)
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
an,bn=nrm_pair(A0)
now('projection pair',an.degree(),bn.degree())
nr0=an*an-an*bn*l1+bn*bn*l2*l0
now('unstripped norm',nr0.degree())
Nr=stripC2(nr0)
now('degree after l2 factors',Nr.degree())
for g in [DD]+list(map(asD,baseguards)):
    Nr,n=strip_linear(Nr,g)
    print('linear multiplicity',n,flush=True)
now('guarded norm degree',Nr.degree())
assert Nr.degree()==48 and nr0.degree()==80
# The extra 30-degree branch is removed only by exact divisibility and
# its first-two read rank contradiction, not by rank loss in a residue.
p43=red_field(L4,a)*red_field(L3,b)-red_field(L4,b)*red_field(L3,a)
p45=red_field(L4,a)*red_field(L5,b)-red_field(L4,b)*red_field(L5,a)
e1,e2=nrm_pair(p45*g3-p43*g5)
nE=e1*e1-e1*e2*l1+e2*e2*l2*l0
HE=stripC2(nE)
assert nE.degree()==42 and HE.degree()==30
N1,rem=divmod(Nr,HE)
assert not rem and N1.degree()==18
assert not (((e1%HE)*(bn%HE)-(e2%HE)*(an%HE))%HE)
u3,v3=nrm_pair(g3)
N3=u3*u3-u3*v3*l1+v3*v3*l2*l0
now('exact rank branch removed',HE.degree(),N1.degree())

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
    return [specialize(ccollect(pol,j),p,z0,False) for j in range(pol.degree(X)+1)]
def on_fiber(p,z0,debug=False):
    gp=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
    if gp(z0)!=0 or gp.derivative()(z0)==0:return
    zero,one=nmod_poly([],p),nmod_poly([1],p)
    d=nmod_poly([0,1],p)
    try:
        ff=specialize(N1,p,z0); l2p=specialize(l2,p,z0)
        hp=specialize(HE,p,z0); n3=specialize(N3,p,z0,False)
        l0p,l1p,ap,bp=[specialize(q,p,z0,False) for q in (l0,l1,an,bn)]
        assert all(hp.gcd(t).degree()==0 for t in (l2p,bp,n3))
        def R_eval(f,c,F):
            e=zero
            for z in ex_poly(f)[::-1]:e=(e*c+z)%F
            return e
        ex_poly=lambda f: expoly(f,p,z0)
        def unit(a,F):
            g,u,v=a.xgcd(F)
            if g.degree()!=0:return
            return u*pow(int(g[0]),-1,p)%F
        p2=unit(l2p,ff); bp0=unit(bp,ff)
        if p2 is None or bp0 is None:
            if debug:print('rank l2/bn',l2p.gcd(ff).degree(),bp.gcd(ff).degree(),flush=True)
            return
        ch=-ap*bp0%ff; c=ch*p2%ff
        assert not ((l2p*c*c+l1p*c+l0p)%ff)
        assert not R_eval(A0,c,ff)
        diag=unit(d,ff)
        if diag is None:
            if debug:print('diagonal issue',flush=True)
            return
        ls=unit(l1p,l2p)
        if ls is None:return
        chdrop=-l0p*ls%l2p
        a0drop=R_eval(A0,chdrop,l2p)
        ldrop=l2p.gcd(a0drop)
        if ldrop.degree():
            if debug:print('leading drop cases',ldrop.degree(),flush=True)
            return
        rc=[[R_eval(j,c,ff) for j in row] for row in M]
        mb0=[R_eval(q,c,ff) for q in bint]
        (f0,f1,f2),(g0,g1,g2),_ = rc
        delta=(f0*g1-f1*g0)%ff
        adi=unit(delta,ff)
        if adi is None:
            if debug:print('Ordinary pivot',delta.gcd(ff).degree(),flush=True)
            return
        p0=(f1*g2-f2*g1)*adi%ff
        p1=(f2*g0-f0*g2)*adi%ff
        assert all(not ((a*p0+b*p1+e)%ff) for a,b,e in rc)
        sigma=35280*(mb0[2]+p1*mb0[1]+p0*mb0[0])*diag.pow_mod(6,ff)%ff

        a0=evk(a,z0,p);b0=evk(b,z0,p)
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
        L3=[-d**3,12*d**2,-30*d,one*20]
        L4=[d**4,-20*d**3,90*d**2,-140*d,one*70]
        L5=add([-d**5,30*d**4,-210*d**3,560*d**2,-630*d,one*252],scl(L3,sigma))
        ee=[[evR(F,t) for F in (L4,L5)] for t in (a0,b0)]
        (h0,k0),(h1,k1)=ee; dv=(h0*k1-h1*k0)%ff
        if unit(dv,ff) is None:
            if debug:print('forward first-two pivot',dv.gcd(ff).degree(),flush=True)
            return
        Z=prod(prod([-a0*one,one],[-b0*one,one]),[-c,one])
        JZ=[zero]+[z*pow(j+1,-1,p)%ff for j,z in enumerate(Z)]
        ba,bb=(-evR(JZ,j) for j in (a0,b0))
        f4=(ba*k1-bb*k0)%ff; f5=(h0*bb-h1*ba)%ff
        h=add(scl(add(Z,scl(JZ,-1)),dv),add(scl(L4,-f4),scl(L5,-f5)))
        # Divide the cleared fourth gate by the three distinct earlier nodes.
        assert Z[-1]==one
        KK=[zero]*(len(h)-len(Z)+1)
        for j in range(len(KK)-1,-1,-1):
            KK[j]=h[j+len(Z)-1]
            for i,x in enumerate(Z): h[i+j]=(h[i+j]-KK[j]*x)%ff
        assert not any(h)
        r0=(KK[0]-p0*KK[2])%ff; r1=(KK[1]-p1*KK[2])%ff
        n4=(r0*r0-p1*r0*r1+p0*r1*r1)%ff
        if n4.gcd(ff).degree():
            if debug:print('fourth failed',n4.gcd(ff).degree(),flush=True)
            return
        return ff.degree(),p,z0
    except ValueError:return


p,z0={'star':(13,9),'ghost':(59,1),'arith':(59,28)}[kind]
assert p>7 and S.isprime(p)
cert=on_fiber(p,z0,True)
assert cert==(18,p,z0)
print('verified',kind,cert,flush=True)
