"""Two constant off clocks, silent off stage eight, exact forward and rear receipts."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
H=S.Poly(v_**3-4*v_**2-v_+2,v_)
assert Q.is_irreducible and H.is_irreducible
K=S.QQ.algebraic_field((Q,u_));u=K.unit
R,b=ring('b',K)
Bb=b*b-(2*u+4)*b+1+2*u
F=S.Poly(S.resultant(Q,(b_**2-(2*u_+4)*b_+1+2*u_).subs(b_,w_-u_),u_),w_).monic()
assert F.degree()==6 and F.is_irreducible
G=S.Poly(S.resultant(H,F.as_expr().subs(w_,z_-2*v_),v_),z_).monic()
assert G.degree()==18 and G.is_irreducible

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
w_z,v_z=recover(E,S0,S0(w)+2*v,v**3-4*v*v-v+2,G,S0(w),v,6,3)
K=S.QQ.algebraic_field((G,z_));z=K.unit
def ev(P,y):
    return sum((K.convert(x)*y**i for i,x in enumerate(P)),K.zero)
w=ev(w_z,z);v=ev(v_z,z);u=ev(u_w,w);b=ev(b_w,w)
assert u+b+2*v==z
assert not (4*u**3-12*u*u+3*u+2) and not (v**3-4*v*v-v+2) and not (b*b-(2*u+4)*b+1+2*u)
a=1+2*u
assert a and b and a!=b
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
    d=1+side*u
    D=d+1+2*v
    L=lambda y:70*y**4-140*D*y**3+90*D*D*y*y-20*D**3*y+D**4
    al=(-L(a)*J3b+L(b)*J3a)/delta
    be=(-J2a*L(b)+J2b*L(a))/delta
    P=al*(Z2-J2)+be*(Z3-J3)-L(X)
    P0,rem=divmod(P,Z2)
    assert not rem and P0.degree()==2
    now('side',side,'third-zero degrees',[(f.degree(),e) for f,e in P0.factor_list()[1]])
    return d,D,P0

Dside=[circ(i) for i in (0,1)]

def low():
 for i,(d,D,C3) in enumerate(Dside):
    s=d+2*v;t=d+v
    assert D and len({a,b,s,t})==4
    def I(P):return sum((c*D**j*C(1,j+1) for (j,),c in P.items()),K.zero)
    P3=(X-a)*(X-s)*(X-t)
    m=[I(P3*X**j) for j in range(5)]
    mat=[[m[j+k] for k in range(3)] for j in range(3)]
    (pa,pb,pc),(pd,pe,pf),(pg,ph,pi)=mat
    H3=pa*(pe*pi-pf*ph)-pb*(pd*pi-pf*pg)+pc*(pd*ph-pe*pg)
    assert H3
    P4=P3*(X-b)
    m=[I(P4*X**j) for j in range(4)]
    det=m[0]*m[2]-m[1]*m[1]
    assert det
    o=(m[1]*m[3]-m[2]*m[2])/det
    p=(m[1]*m[2]-m[0]*m[3])/det
    P2=X*X+p*X+o
    assert not I(P4*P2) and not I(X*P4*P2)
    assert C3.evaluate(X,s) and C3.evaluate(X,t)
    assert P2.gcd(C3).degree()==0
    now(i,'all <=6 label counts fail')

def rr(a,p):
    s=S.Rational(str(a));return int(s.p)*pow(int(s.q),-1,p)%p
def evk(a,z0,p):
    n=0
    for k in a.to_list():
        n=(n*z0+rr(k,p))%p
    return n

def test(p,u,b,v,d,D,c):
    a=(1+2*u)%p;s=(d+2*v)%p;t=(d+v)%p
    gk=(1+2*v-v*v)%p
    if not D or not v or not gk or len({a,b,c,s,t})!=5:return None
    X=nmod_poly([0,1],p)
    q=nmod_poly([1],p)
    for x in (a,b,c,s,t):q=q*(X-x)
    def I(P,k=0):
        return sum(int(P[i])*pow(D,i+k,p)*pow(i+k+1,-1,p)
                   for i in range(P.degree()+1))%p
    def JD(P):
        J=nmod_poly([0]+[int(P[i])*pow(i+1,-1,p)%p for i in range(P.degree()+1)],p)
        return int(J(D))-J
    L=gk*(q//(X-t))-(q//(X-s))
    m0,m1,m2=[I(q,i) for i in range(3)]
    l0,l1,l2=[I(L,i) for i in range(3)]
    det=(m0*l1-m1*l0)%p
    if not det:return None
    o=(m1*l2-m2*l1)*pow(det,-1,p)%p
    j=(m2*l0-m0*l2)*pow(det,-1,p)%p
    Q2=X*X+j*X+o
    assert not I(q*Q2) and not I(L*Q2)
    P7=q*Q2
    BT=nmod_poly([],p)
    for j0 in range(1,8):
      for i in range(j0):
         BT+=int(P7[j0])*pow(D,j0-i-1,p)*pow(j0-i,-1,p)*X**i
    R2=(X-s)*(X-t);JR=JD(R2)
    assert (gk*int(BT(t))-int(BT(s)))%p==0
    G3=(t-d)*(R2-JR)*BT + (X-d)*(int(JR(t))*int(BT(t)))
    if Q2.gcd(G3).degree()==0:
        return int(Q2[1]),int(Q2[0]),det,tuple(int(x) for x in (G3%Q2).coeffs())
    return None

CERTS = (
 (0,(10,4,23,1,48), ((13,(19,58,38,(0,31))), (37,(34,0,53,(46,42))))),
 (1,(10,4,23,11,58), ((5,(8,50,18,(9,46))), (41,(34,18,56,(27,21))))),
)

if __name__=='__main__':
  low()
  p,z0=59,1
  assert S.isprime(p)
  fp=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
  assert fp.degree()==18 and fp(z0)==0 and fp.derivative()(z0)!=0
  for side,expected_field,expected_fibers in CERTS:
    dpol,Dpol,c_poly=Dside[side]
    uu,bb,vv,dd,DD=[evk(x,z0,p) for x in (u,b,v,dpol,Dpol)]
    assert (uu,bb,vv,dd,DD)==expected_field
    cc=nmod_poly([evk(c_poly.get((i,),K.zero),z0,p) for i in range(3)],p)
    assert cc.degree()==2
    roots=cc.roots()
    assert len(roots)==2 and all(n==1 for _,n in roots)
    fibers=tuple(sorted((int(cc0),test(p,uu,bb,vv,dd,DD,int(cc0))) for cc0,_ in roots))
    assert fibers==expected_fibers
    now(side,'simple good reduction',p,z0,expected_field,fibers)
