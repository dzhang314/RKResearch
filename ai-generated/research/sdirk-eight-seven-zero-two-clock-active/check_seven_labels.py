"""Active pair, two constant-residual clocks, seven distinct literal zero nodes."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
H=S.Poly(v_**2-2*v_-1,v_)
assert Q.is_irreducible and H.is_irreducible
K=S.QQ.algebraic_field((Q,u_));u=K.unit
R,b=ring('b',K)
Bb=b*b-(2*u+4)*b+1+2*u
F=S.Poly(S.resultant(Q,(b_**2-(2*u_+4)*b_+1+2*u_).subs(b_,w_-u_),u_),w_).monic()
assert F.degree()==6 and F.is_irreducible
G=S.Poly(S.resultant(H,F.as_expr().subs(w_,z_-2*v_),v_),z_).monic()
assert G.degree()==12 and G.is_irreducible

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
w_z,v_z=recover(E,S0,S0(w)+2*v,v*v-2*v-1,G,S0(w),v,6,2)
K=S.QQ.algebraic_field((G,z_));z=K.unit
def ev(P,y):
    return sum((K.convert(x)*y**i for i,x in enumerate(P)),K.zero)
w=ev(w_z,z);v=ev(v_z,z);u=ev(u_w,w);b=ev(b_w,w)
assert u+b+2*v==z
assert not (4*u**3-12*u*u+3*u+2) and not (v*v-2*v-1) and not (b*b-(2*u+4)*b+1+2*u)
a=1+2*u
assert a and b and a!=b
P0=-b*b/2+2*b-1
assert P0 != 0 or (b-1)*(b-1-u) != 0
now('primitive degree',G.degree())

R,X=ring('X',K)
C=lambda p,q=1:K.convert(S.Rational(p,q))
Z2=(X-a)*(X-b);Z3=X*Z2
J=lambda P:sum((p*X**(i+1)*C(1,i+1) for (i,),p in P.items()),R.zero)
p0=-X*X*C(1,2)+2*X-1
off=(X-1)*(X-1-u)
split=p0.evaluate(X,a)*off-off.evaluate(X,a)*p0
new2=X*X-(2*u+4)*X+1+2*u
coef=-u*u/3+2*u/3+C(1,6)
assert coef and J(split)-split==coef*(X-a)*new2
assert not new2.evaluate(X,b) and split.evaluate(X,b)
assert p0.gcd(off).degree()==0
J2,J3=J(Z2),J(Z3)
J2a,J2b=J2.evaluate(X,a),J2.evaluate(X,b)
J3a,J3b=J3.evaluate(X,a),J3.evaluate(X,b)
delta=J2a*J3b-J2b*J3a
assert delta==a*a*b*b*(a-b)**3*C(1,24) and delta
def circ(side):
    D=2+side*u
    L=lambda y:70*y**4-140*D*y**3+90*D*D*y*y-20*D**3*y+D**4
    al=(-L(a)*J3b+L(b)*J3a)/delta
    be=(-J2a*L(b)+J2b*L(a))/delta
    P=al*(Z2-J2)+be*(Z3-J3)-L(X)
    P0,rem=divmod(P,Z2)
    assert not rem and P0.degree()==2
    now('side',side,'third-zero degrees',[(f.degree(),e) for f,e in P0.factor_list()[1]])
    return D,P0
Dside=[circ(i) for i in (0,1)]
for w0 in (2*v,2-v):
    ys,yt=1+w0,1+v
    prim=J((X-ys)*(X-yt))
    pn=2*w0*v+1+2*w0-w0*w0
    assert v and pn and ys!=yt
    assert pn*prim.evaluate(X,yt)==2*v*v*prim.evaluate(X,ys)

def rr(a,p):
    s=S.Rational(str(a));return int(s.p)*pow(int(s.q),-1,p)%p
def evk(a,z0,p):
    n=0
    for k in a.to_list():
        n=(n*z0+rr(k,p))%p
    return n

def test(p,u,b,v,D,c,phase):
    a=(1+2*u)%p
    w=(2*v if phase=='arith' else 2-v)%p
    s=(D-1-w)%p;t=(D-1-v)%p
    if not D or not v or len({a,b,c,s,t})!=5:return None
    pR=(2*w*v+1+2*w-w*w)*pow(2*v,-1,p)%p
    if not pR:return None
    X=nmod_poly([0,1],p)
    q=nmod_poly([1],p)
    for x in (a,b,c,s,t):q=q*(X-x)
    def I(P,k=0):
        return sum(int(P[i])*pow(D,i+k,p)*pow(i+k+1,-1,p)
                   for i in range(P.degree()+1))%p
    def JD(P):
        J=nmod_poly([0]+[int(P[i])*pow(i+1,-1,p)%p for i in range(P.degree()+1)],p)
        return int(J(D))-J

    m0,m1,m2=[I(q,i) for i in range(3)]
    delta=(m0*m2-m1*m1)%p
    if not delta:return None
    A=(X*m0-m1);B=(X*m1-m2)
    def C_num(x):
        mask=q//(X-x)
        f2,f1,f0=[I(mask,i) for i in (2,1,0)]
        return A*f2-(A*X+B)*f1+B*X*f0
    Bs=C_num(s);Bt=C_num(t)
    R2=(X-s)*(X-t);JR=JD(R2)
    jr=int(JR(t));js=int(JR(s))
    assert (pR*jr-v*js)%p==0
    R3=(R2-JR)*(v*(s-t)*delta)+jr*(v*(s-t)*Bt+(X-t)*(pR*Bs-v*Bt))
    Rr,rem=divmod(R3,R2)
    assert not rem
    if Rr.degree()!=1:return None
    r=-int(Rr[0])*pow(int(Rr[1]),-1,p)%p
    inv=int(A(r))
    if not inv:return None
    e=int(B(r))*pow(inv,-1,p)%p
    nodes=[a,b,c,e,r,s,t]
    if len(set(nodes))!=7:return None
    P7=q*(X-r)*(X-e)
    assert not I(P7)
    sigma=(X-r)*(X-s)*(X-t)
    Jsig=JD(sigma)
    BT=nmod_poly([],p)
    for j in range(1,8):
      for i in range(j):
         BT += int(P7[j])*pow(D,j-i-1,p)*pow(j-i,-1,p)*X**i
    R4=(X-e)*sigma
    proof=(int(BT(e))-int(((BT*Jsig)%R4)[3]))%p
    if proof:return (r,e,proof)
    return None

CERTS = (
  (0,'star',113,0, (6,94,63,2), ((31,(56,5,110)), (86,(30,55,73)))),
  (0,'arith',79,10, (54,51,71,2), ((43,(15,49,41)), (71,(55,31,6)))),
  (1,'star',127,19, (28,21,112,30), ((18,(119,81,106)), (72,(14,59,99)))),
  (1,'arith',79,10, (54,51,71,56), ((40,(32,65,55)), (53,(36,29,30)))),
)

if __name__=='__main__':
 for side,phase,p,z0,expected_field,expected_fibers in CERTS:
    assert p>7 and S.isprime(p)
    Dpol,c_poly=Dside[side]
    fp=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
    assert fp.degree()==12 and fp(z0)==0 and fp.derivative()(z0)!=0
    uu,bb,vv,DD=[evk(x,z0,p) for x in (u,b,v,Dpol)]
    assert (uu,bb,vv,DD)==expected_field
    cc=nmod_poly([evk(c_poly.get((i,),K.zero),z0,p) for i in range(3)],p)
    assert cc.degree()==2
    roots=cc.roots()
    assert len(roots)==2 and all(n==1 for _,n in roots)
    fibers=tuple(sorted((int(cc0),test(p,uu,bb,vv,DD,int(cc0),phase)) for cc0,_ in roots))
    assert fibers==expected_fibers
    now(side,phase,'simple good reduction',p,z0,expected_field,fibers)
