"""Final seven-distinct chart with the cubic first forward zero: exact star/ghost checks."""
from itertools import combinations, permutations
from flint import nmod_poly, fq_default_ctx, fq_default_poly_ctx
import sympy as S
from sympy.polys.rings import ring
from sys import argv
mode=argv[1]
assert mode in ('star','ghost')
u0,v0,z0=S.symbols('u v z')
U=S.Poly(4*u0**3-12*u0*u0+3*u0+2,u0).monic()
assert U.is_irreducible
KK=S.QQ.algebraic_field((U,u0));uu=KK.unit
if mode=='star':
    K=KK; u=uu; G=U
else:
    V=S.Poly(v0**3-4*v0*v0-v0+2,v0)
    G=S.Poly(S.resultant(U,V.as_expr().subs(v0,(z0-u0)/2),u0),z0).monic()
    assert V.is_irreducible and G.degree()==9 and G.is_irreducible
    B,vv=ring('V',KK)
    Vq=vv**3-4*vv**2-vv+2
    def enc(p):
        return S.Matrix([S.Rational(str((p.get((j,),KK.zero).to_list()[::-1]+[0]*3)[i]))
                         for j in range(3) for i in range(3)])
    th=B(uu)+2*vv
    inv=S.Matrix.hstack(*(enc(th**j%Vq) for j in range(9))).inv()
    uc=inv*enc(B(uu));vc=inv*enc(vv)
    def evs(p):
        return sum((B(KK.convert(x))*th**i for i,x in enumerate(p)),B.zero)%Vq
    assert evs(uc)==B(uu) and evs(vc)==vv and not evs(G.all_coeffs()[::-1])
    K=S.QQ.algebraic_field((G,z0)); z=K.unit
    def evk(p,x):
        return sum((K.convert(j)*x**i for i,j in enumerate(p)),K.zero)
    u=evk(uc,z);v=evk(vc,z)
    assert u+2*v==z and not evk(U.all_coeffs()[::-1],u) and not evk(V.all_coeffs()[::-1],v)
C=lambda i,j=1:K.convert(S.Rational(i,j))
D0,D=ring('D',K)
P,X=ring('X',D0.to_domain())
co=lambda x:P(D0(x))
a=1+2*u;s=D-1
I=lambda f:sum((z*D**i*C(1,i+1) for (i,),z in f.items()),D0.zero)
J=lambda f:sum((co(z*C(1,i+1))*X**(i+1) for (i,),z in f.items()),P.zero)
def det(M):
    (a,b,c),(d,e,f),(g,h,j)=M
    return a*(e*j-f*h)-b*(d*j-f*g)+c*(d*h-e*g)

if mode=='star':
    Y=X-co(D-2)
    f0=(X-co(a))*(X-co(s))
    masks=[f0,f0*Y**2,(X-co(a))*(Y**2-2)]
else:
    t=s-v;r=s-2*v
    k=1+2*v-v*v
    assert v and k
    F=(X-co(a))*(X-co(s))*(X-co(t))*(X-co(r))
    Ft=F//(X-co(t)); Fs=F//(X-co(s)); Fr=F//(X-co(r))
    assert Ft*(X-co(t))==F and Fs*(X-co(s))==F and Fr*(X-co(r))==F
    masks=[F,co(k)*Ft-Fs,Fr]
rows=[[I(f*X**i) for i in range(4)] for f in masks]
M=[r[:3] for r in rows]; rhs=[-r[3] for r in rows]
delta=det(M); nums=[]
for j in range(3):
    W=[r[:] for r in M]
    for i in range(3):W[i][j]=rhs[i]
    nums.append(det(W))
assert delta.degree()==12 and [n.degree() for n in nums]==[15,14,13]
g=delta
for n in nums:g=g.gcd(n)
assert g.monic()==D**6
delta=delta//g;nums=[n//g for n in nums]
assert all(sum((M[i][j]*nums[j] for j in range(3)),D0.zero)==delta*rhs[i] for i in range(3))
T=co(delta)*X**3+sum((co(n)*X**i for i,n in enumerate(nums)),P.zero)

def divided_mean(f):
    return sum((co(c*D**(j-i-1)*C(1,j-i))*X**i
                for (j,),c in f.items() for i in range(j)),P.zero)
La=D**4-20*a*D**3+90*a*a*D**2-140*a**3*D+70*a**4
guards=[D,delta,s-D0(a),T.evaluate(X,D0(a)),T.evaluate(X,s),La]
if mode=='star':
    early=(X-co(a))*T
    H0=I(early)
    cb=divided_mean(early)
    ff=co(C(2,3))+2*Y-Y**2-co(C(1,3))*Y**3
    rootG=co(H0)*(ff-1-co(C(1,3))*Y)+(Y-1)*cb*ff
    guards.append(H0)
else:
    BB=divided_mean(F*T)
    R=(X-co(s))*(X-co(t))
    jp=J(R); jr=co(jp.evaluate(X,D))-jp
    Bs=BB.evaluate(X,s); Bt=BB.evaluate(X,t)
    Js=jr.evaluate(X,s); Jt=jr.evaluate(X,t)
    rootG=co(t-s)*((R-jr)*BB+co(Bs*Js))+(X-co(s))*co(Bt*Jt-Bs*Js)
    guards += [t-D0(a),r-D0(a),T.evaluate(X,t),T.evaluate(X,r)]

norm=T.resultant(rootG)
expected=14 if mode=='star' else 18
assert norm.degree()==(81 if mode=='star' else 99)
for guard in guards:
    while True:
        h=norm.gcd(guard)
        if h.degree()==0:break
        norm=norm//h
assert norm.degree()==expected
print('exact projected diagonal degree',expected,flush=True)

def rr(a,p):
    x=S.Rational(str(a));return int(x.p)*pow(int(x.q),-1,p)%p
def evp(x,u,p):
    n=0
    for c in x.to_list():n=(n*u+rr(c,p))%p
    return n

def fiber(u,v,D,Fq,P,q,G,deb):
    zero=Fq(0)
    def evd(pol):
        n=zero
        for c in reversed(pol):n=n*D+c
        return n
    de=evd(deb)
    assert D!=zero and de!=zero
    x=P([0,1]); R=P([evd(c)/de for c in q]); T=P([evd(c) for c in G])
    rr=R.roots()
    assert len(rr)==3 and all(e==1 for _,e in rr)
    a=1+2*u;s=D-1
    qs=[x for x,e in rr]
    allsites=([a,s]+qs) if mode=='star' else ([a,s,s-v,s-2*v]+qs)
    assert all(y!=x for y,x in combinations(allsites,2))
    es=[t for t in qs if T(t)==zero]
    assert es
    P0=2*x-1-x*x/Fq(2); R0=(x-1)*(x-1-u)
    L=lambda t:70*t**4-140*D*t**3+90*D*D*t*t-20*D**3*t+D**4
    La=L(a)
    assert La!=zero
    J=lambda p:sum((p[j]*x**(j+1)/Fq(j+1) for j in range(p.degree()+1)),P([]))
    def Gap(P,b):
        return La*((b-a)*P(b)+a*J(P)(b)-J(x*P)(b))-L(b)*(a*P(a)-J(x*P)(a))
    pairs=0
    for e in es:
        for b,c in permutations([p for p in qs if p!=e]):
            assert Gap(P0,b)!=zero # front-star
            g=Gap(R0,b)
            assert g!=zero
            P1=P0-Gap(P0,b)*R0/g
            pa,pb=P1(a),P1(b)
            assert pa!=zero
            J1=J(P1); JT=J(x*P1)
            theta=(J1(b)-pb)/pa
            def H(S):
                Z=S-J(S)
                return La*(Z(b)+theta*S(a))-L(b)*Z(a)
            gd=H(R0)
            assert gd!=zero
            d=H(x*R0)/gd
            R3=(x-d)*R0; JR=J(R3)
            f0=J1(c)-P1(c)
            f1=JT(c)-c*P1(c)+(a*pa-JT(a))*L(c)/La
            f2=JR(c)-R3(c)+(R3(a)-JR(a))*L(c)/La
            assert det([[pa,pb,f0],[a*pa,b*pb,f1],[R3(a),R3(b),f2]])!=zero # first zero row3
            pairs+=1
    return pairs

p,zr,degs=(13,4,[1,3,4,6]) if mode=='star' else (127,91,[1,4,5,8])
assert S.isprime(p)
gh=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
assert gh(zr)==0 and gh.derivative()(zr)!=0
def dx(pol):
    return [evp(pol.get((i,),K.zero),zr,p) for i in range(pol.degree()+1)]
df=nmod_poly(dx(norm),p)
assert df.degree()==expected
factors=df.factor()[1]
assert sorted(f.degree() for f,e in factors)==degs and all(e==1 for f,e in factors)
qco=[dx(T.get((i,),D0.zero)) for i in range(4)]
gco=[dx(rootG.get((i,),D0.zero)) for i in range(rootG.degree()+1)]
dco=dx(delta)
uu=evp(u,zr,p); vv=evp(v,zr,p) if mode=='ghost' else 0
assert (uu,vv)==((4,0) if mode=='star' else (28,95))
n=0;pairs=0
for f,_ in factors:
    d=f.degree()
    Fq=fq_default_ctx(p,6*d,var='a')
    assert Fq.modulus().is_irreducible()
    Fpoly=fq_default_poly_ctx(Fq)
    roots=Fpoly([int(c) for c in f.coeffs()]).roots()
    assert len(roots)==d and all(e==1 for _,e in roots)
    for de,_ in roots:
        pairs+=fiber(Fq(uu),Fq(vv),de,Fq,Fpoly,qco,gco,dco)
        n+=1
assert n==expected and pairs>=2*n
print('fixed residue',mode,p,zr,'all diagonal roots',n,'directed forward pairs',pairs,flush=True)
