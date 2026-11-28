"""Exact ordinary and fourth-reverse projections in the eight-zero zero-ratio chart."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
from sys import argv
kind=argv[1]
assert kind in ('zero-star','zero-arith')
vdegree={'ghost':3,'arith':6,'zero-star':2,'zero-arith':2}[kind]
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
Hv={2:v_**2-2*v_-1,3:v_**3-4*v_**2-v_+2,
    6:8*v_**6-44*v_**5+22*v_**4+97*v_**3-55*v_**2-13*v_+6}[vdegree]
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


from itertools import permutations
C=lambda q,r=1:K.convert(S.Rational(q,r))
R,D,X=ring('D X',K)
w=2-v if kind=='zero-star' else 2*v
offset=(K.zero,v,w)
assert len(set(offset))==3
assert all(a-b!=x-y for x,y in permutations(offset,2))
s,t,r=(D-1-x for x in offset)
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

# X is the prospective third new zero c; use a separate polynomial for all reads.
P,T=ring('T',R.to_domain())
co=lambda f:P(R(f))
A,B,C=co(a),co(b),co(X)
S0,R0,T0=co(s),co(r),co(t)
F=(T-A)*(T-B)*(T-C)*(T-R0)*(T-T0)
def I0(P0):
 return sum((c*D**j*Cst(1,j+1) for (j,),c in P0.items()),R.zero)
Cst=lambda x,y=1:K.convert(S.Rational(x,y))
def J0(P0):
 return sum((co(c*Cst(1,j+1))*T**(j+1) for (j,),c in P0.items()),P.zero)
m0,m1,m2=[I0(F*T**j) for j in range(3)]
k=s*m0-m1;n=s*m1-m2
P6=F*(T-S0);P7=P6*(co(k)*T-co(n))
B7=sum((co(c*D**(j-i-1)*Cst(1,j-i))*T**i for (j,),c in P7.items() for i in range(j)),P.zero)
R2=(T-R0)*(T-T0)
Jr0=J0(R2);JR=co(Jr0.evaluate(T,D))-Jr0
F3=R2-JR
Jt,Jr=JR.evaluate(T,t),JR.evaluate(T,r)
Bt,Br,Bs=[B7.evaluate(T,coT) for coT in (t,r,s)]
pR=(2*w*v+1+2*w-w*w)/(2*v)
assert pR and pR*Jt==v*Jr
F4s=v*(r-t)*F3.evaluate(T,s)*Bs+Jt*(v*(r-t)*Bt+(s-t)*(pR*Br-v*Bt))
Nf=sum((z*n**j*k**(3-j) for (j,),z in F3.items()),R.zero)
F4y=-v*(r-t)*Nf+Jt*(k*v*(r-t)*Bt+(n-k*t)*(pR*Br-v*Bt))

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
N4s=stripC2(nrm(F4s));N4y=stripC2(nrm(F4y));Nk=stripC2(nrm(k))
assert [f.degree() for f in (N4s,N4y,Nk)]==[32,54,16]
print('guarded exact projection degrees',*[p.degree() for p in (N4s,N4y,Nk)],flush=True)
print('leading C2 degree',l2.degree(),'C1 gcd',l2.gcd(l1).degree(),'leading factors',[(p.degree(),m) for p,m in l2.factor_list()[1]],flush=True)
def rr(a,p):
 t=S.Rational(str(a));return int(t.p)*pow(int(t.q),-1,p)%p
def evp(a,z,p):
 n=0
 for c in a.to_list():
   n=(n*z+rr(c,p))%p
 return n
def red(P,z,p):
 return nmod_poly([evp(P.get((i,),K.zero),z,p) for i in range(P.degree()+1)],p)
def check_finite(p,u,b,v,D,c):
 from flint import nmod_poly
 V=nmod_poly([0,1],p);a=(1+2*u)%p
 w=(2*v if phase=='arith' else 2-v)%p
 s=(D-1)%p;r=(s-w)%p;t=(s-v)%p
 known=[a,b,c,s,r,t]
 if not D or not v or len(set(known))!=6:return None
 pR=(2*w*v+1+2*w-w*w)*pow(2*v,-1,p)%p
 if not pR:return None
 def I(P):
    return sum(int(P[i])*pow(D,i,p)*pow(i+1,-1,p) for i in range(P.degree()+1))%p
 def J(P):
    q=nmod_poly([0]+[int(P[i])*pow(i+1,-1,p)%p for i in range(P.degree()+1)],p)
    return int(q(D))-q
 P6=nmod_poly([1],p)
 for node in known:P6*=V-node
 m0,m1=I(P6),I(V*P6)
 if not m0:return None
 y=m1*pow(m0,-1,p)%p
 if y in known:return None
 P7=P6*(V-y)
 B=nmod_poly([],p)
 for j in range(1,8):
   for i in range(j):
     B+=int(P7[j])*pow(D,j-i-1,p)*pow(j-i,-1,p)*V**i
 R=(V-r)*(V-t);JR=J(R)
 bt,br,jt=[int(a0(b0)) for a0,b0 in ((B,t),(B,r),(JR,t))]
 assert (pR*jt-v*int(JR(r)))%p==0
 tests=[]
 for e,f in ((s,y),(y,s)):
    Q1=(v*(r-t)*int((R-JR)(f))*int(B(f))+jt*(v*(r-t)*bt+(f-t)*(pR*br-v*bt)))%p
    S3=(V-f)*R
    re=(B*J(S3))%((V-e)*S3)
    Q2=(int(B(e))-int(re[3]))%p
    if not(Q1 or Q2):return None
    tests.append((Q1,Q2))
 return (y,tests)
def test_early(p,u,b,v,D,c,phase):
    a=(1+2*u)%p
    w=(2*v if phase=='arith' else 2-v)%p
    s=(D-1-w)%p;t=(D-1-v)%p
    if not D or not v or len({a,b,c,s,t})!=5:return None
    pR=(2*w*v+1+2*w-w*w)*pow(2*v,-1,p)%p
    if not pR:return None
    X=nmod_poly([0,1],p)
    q=N=nmod_poly([1],p)
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

def modular_phase(p,u,b,v,phase,n4s,n4y,nk):
    def Q(c=None):
     return nmod_poly([] if c is None else c if isinstance(c,list) else [int(c)%p],p)
    D=Q([0,1]);a=(1+2*u)%p;w=(2*v if phase=='arith' else 2-v)%p
    s=D-1;t=s-v;r=s-w
    pR=(2*w*v+1+2*w-w*w)*pow(2*v,-1,p)%p
    Dsd=D
    def trim(P):
     while P and not P[-1]:P.pop()
     return P
    def ev(P,X):return sum((c*X**i for i,c in enumerate(P)),X*0)
    def mul(P,Q):
     out=[P[0]*0 for _ in range(len(P)+len(Q)-1)]
     for i,a in enumerate(P):
      for j,b in enumerate(Q):
       out[i+j]+=a*b
     return out
    def md(P,Q):
     out=P[:]; qt=[P[0]*0 for _ in range(len(P)-len(Q)+1)]
     for k in range(len(P)-len(Q),-1,-1):
       x=out[k+len(Q)-1];qt[k]=x
       for j,y in enumerate(Q):out[k+j]-=x*y
     return qt,out[:len(Q)-1]
    def J(P):return [P[0]*0]+[f*pow(i+1,-1,p) for i,f in enumerate(P)]
    def Jstar(P,D):
     out=J(P);out=[-x for x in out];out[0]=-ev(out,D)
     return out
    def I(P,D):return sum((c*D**i*pow(i+1,-1,p) for i,c in enumerate(P)),D*0)
    def nodal(nodes):
     out=[nodes[0]**0]
     for x in nodes:out=mul(out,[-x,x**0])
     return out
    def CD(P,D):
     out=[D*0 for _ in range(len(P)-1)]
     for j in range(1,len(P)):
      for i in range(j):out[i]+=P[j]*D**(j-i-1)*pow(j-i,-1,p)
     return out

    def sub(A,B):
     z=A[0]*0
     return [(A[i] if i<len(A) else z)-(B[i] if i<len(B) else z) for i in range(max(len(A),len(B)))]
    def add(A,B):
     z=A[0]*0
     return [(A[i] if i<len(A) else z)+(B[i] if i<len(B) else z) for i in range(max(len(A),len(B)))]
    L4=[D**4,-20*D**3,90*D*D,-140*D,Q(70)]
    Z2=nodal([Q(a),Q(b)]);Z3=mul(Z2,[Q(),Q(1)])
    J2,J3=J(Z2),J(Z3)
    J2a,J2b=ev(J2,Q(a)),ev(J2,Q(b));J3a,J3b=ev(J3,Q(a)),ev(J3,Q(b))
    j0=J2a*J3b-J2b*J3a;assert j0
    La,Lb=ev(L4,Q(a)),ev(L4,Q(b))
    al=(-La*J3b+Lb*J3a)/j0;be=(J2b*La-J2a*Lb)/j0
    C3,rem=md(sub(add([al*x for x in sub(Z2,J2)],[be*x for x in sub(Z3,J3)]),L4),Z2)
    assert not any(rem)
    C0,C1,C2=C3
    assert C2
    class Pair:
     def __init__(self,a=0,b=0):self.a=a if isinstance(a,nmod_poly) else Q(a);self.b=b if isinstance(b,nmod_poly) else Q(b)
     @staticmethod
     def co(x):return x if isinstance(x,Pair) else Pair(x)
     def __add__(x,y):
       y=Pair.co(y);return Pair(x.a+y.a,x.b+y.b)
     __radd__=__add__
     def __neg__(x):return Pair(-x.a,-x.b)
     def __sub__(x,y):return x+-Pair.co(y)
     def __rsub__(x,y):return Pair.co(y)+-x
     def __mul__(x,y):
       y=Pair.co(y);u=x.b*y.b
       return Pair(x.a*y.a-u*C2*C0,x.b*y.a+x.a*y.b-u*C1)
     __rmul__=__mul__
     def __pow__(x,j):
       z=Pair(1)
       while j:
         if j&1:z=z*x
         j>>=1
         if j:x=x*x
       return z
     def norm(x):
       return x.a*x.a-x.a*x.b*C1+x.b*x.b*C2*C0
     def __bool__(x):return bool(x.a) or bool(x.b)
    T=Pair(D)*Pair(C2)
    a,b,c=Pair(C2*a),Pair(C2*b),Pair(0,1)
    s,r,t=Pair(C2*s),Pair(C2*r),Pair(C2*t)
    F=nodal([a,b,c,r,t])
    m0,m1,m2=[I([Pair()]*i+F,T) for i in range(3)]
    kk=s*m0-m1;ll=s*m1-m2

    # Keep the C3 scale but use only one ordinary fraction-free pole.
    P6=mul(F,[-s,Pair(1)])
    P7=mul(P6,[-ll,kk])
    B7=CD(P7,T)
    R2=nodal([r,t]);JR=Jstar(R2,T)
    F3=sub([Pair(C2)*y for y in R2],JR)
    Bt,Br,Bs=[ev(B7,X) for X in (t,r,s)]
    Jt,Jr=ev(JR,t),ev(JR,r)
    assert not (pR*Jt-v*Jr)
    Q4=mul(nodal([r,t,s]),[-ll,kk])
    def pseudo(P,Q):
     assert len(P)==11 and len(Q)==5
     out=P[:]
     for k in range(6,-1,-1):
       z=out[k+4];out=[kk*x for x in out]
       for j,q in enumerate(Q):out[k+j]-=z*q
     return out[:4]
    def check(f_is_s):
     if f_is_s:
       F4=v*(r-t)*ev(F3,s)*Bs+Jt*(v*(r-t)*Bt+(s-t)*(pR*Br-v*Bt))
       R3=nodal([r,t,s])
       left=-Pair(C2)*kk**9
     else:
       fn=sum((c*ll**j*kk**(3-j) for j,c in enumerate(F3)),Pair())
       F4=-v*(r-t)*fn+Jt*(kk*v*(r-t)*Bt+(ll-kk*t)*(pR*Br-v*Bt))
       R3=mul(nodal([r,t]),[-ll,kk])
       left=Pair(C2)*kk**8*Bs
     JR3=Jstar(R3,T)
     F5=left-pseudo(mul(B7,JR3),Q4)[3]
     n4,n5=(n4s if f_is_s else n4y),F5.norm()
     assert n5.degree()==(550 if f_is_s else 610)
     common=n4.gcd(n5)
     print('norms and gcd degrees',n4.degree(),n5.degree(),common.degree(),flush=True)
     assert common.degree()==0
    check(False);check(True)
    assert nk.gcd(ll.norm()).degree()==0
    print('ordinary singular norm gcd zero',flush=True)

phase='star' if kind=='zero-star' else 'arith'
def FF(p,z0):
    gen=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
    assert gen.degree()==12 and gen(z0)==0 and gen.derivative()(z0)!=0
    return tuple(evp(x,z0,p) for x in (u,b,v))
p,z0=(79,10) if phase=='star' else (31,8)
uu,bb,vv=FF(p,z0)
n4s,n4y,nk=[red(f,z0,p) for f in (N4s,N4y,Nk)]
assert [x.degree() for x in (n4s,n4y,nk)]==[32,54,16]
modular_phase(p,uu,bb,vv,phase,n4s,n4y,nk)

AB={
 ('star','a'):(79,10,31,((6,(4,37,58)),(24,(71,77,16)))),
 ('star','b'):(79,10,52,((7,(1,4,33)),(40,(35,55,29)))),
 ('arith','a'):(31,8,12,((14,(28,1,18)),(24,(30,8,10)))),
 ('arith','b'):(31,9,18,((5,(13,18,2)),(29,(2,16,6)))),
}
for loc in ('a','b'):
  p,z0,D0,cert=AB[(phase,loc)]
  uu,bb,vv=FF(p,z0)
  assert D0==(1+((1+2*uu) if loc=='a' else bb))%p
  pol=nmod_poly([int(red(f,z0,p)(D0)) for f in (l0,l1,l2)],p)
  roots=pol.roots()
  assert pol.degree()==2 and len(roots)==2 and all(e==1 for _,e in roots)
  result=tuple(sorted((int(x),test_early(p,uu,bb,vv,D0,int(x),phase)) for x,_ in roots))
  assert result==cert
  print('early duplicate',loc,p,z0,D0,result,flush=True)

# Terminal duplicate at the third forward zero.
F_s=D1.from_dict({(i,):q for (i,j),q in evX(CC,s).items()})
assert F_s.degree()==6 and [(f.degree(),e) for f,e in F_s.factor_list()[1]]==[(6,1)]
p,z0,D0,expected=(17,3,2,(14,3,13)) if phase=='star' else (17,8,15,(9,2,5))
uu,bb,vv=FF(p,z0)
Dp=red(F_s,z0,p)
assert Dp.degree()==6 and Dp(D0)==0 and Dp.derivative()(D0)!=0
assert test_early(p,uu,bb,vv,D0,(D0-1)%p,phase)==expected
print('third early duplicate',p,z0,D0,expected,flush=True)

# The first-new quadratic leading-drop branch with no early overlap.
assert l2.degree()==4 and l2.gcd(l1).degree()==0
assert [(f.degree(),e) for f,e in l2.factor_list()[1]]==[(4,1)]
p,z0,D0,c0=31,20,20,7
uu,bb,vv=FF(p,z0)
ll0,ll1,ll2=[red(f,z0,p) for f in (l0,l1,l2)]
assert ll2.degree()==4 and ll2(D0)==0 and ll2.derivative()(D0)!=0
assert ll1(D0)!=0 and (ll1(D0)*c0+ll0(D0))==0
want=(16,[(27,6),(2,6)]) if phase=='star' else (13,[(24,7),(18,28)])
assert check_finite(p,uu,bb,vv,D0,c0)==want
print('leading degree drop',p,z0,D0,c0,want,flush=True)
