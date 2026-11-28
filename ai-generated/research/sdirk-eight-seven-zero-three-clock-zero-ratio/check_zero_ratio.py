"""Zero ratio: unconditional fourth reverse read's exact diagonal projections."""
from itertools import permutations,combinations
from flint import nmod_poly, fq_default_ctx, fq_default_poly_ctx
import sympy as S
from sympy.polys.rings import ring
from time import monotonic
from sys import argv
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)
mode, which=argv[1:3]
assert mode in ('star','arith') and which in ('s','new')
v0=S.symbols('v')
H=S.Poly(v0*v0-2*v0-1,v0)
assert H.is_irreducible
K=S.QQ.algebraic_field((H,v0));v=K.unit
C=lambda x,y=1:K.convert(S.Rational(x,y))
D0,D=ring('D',K)
R,X=ring('X',D0.to_domain())
co=lambda q:R(D0(q))
w=2*v if mode=='arith' else 2-v
s=D-1;t=s-v;r=s-w
vp=(2*w*v+1+2*w-w*w)/(2*v)
assert v and w and w!=v and vp
P3=(X-co(s))*(X-co(t))*(X-co(r))
I=lambda P:sum((c*D**j*C(1,j+1) for (j,),c in P.items()),D0.zero)
J=lambda P:sum((co(c*C(1,j+1))*X**(j+1) for (j,),c in P.items()),R.zero)
def det(M):
 (a,b,c),(d,e,f),(g,h,j)=M
 return a*(e*j-f*h)-b*(d*j-f*g)+c*(d*h-e*g)
Lm=co(vp)*(P3//(X-co(r)))-co(v)*(P3//(X-co(t)))
m=[I(P3*X**i) for i in range(5)];l=[I(Lm*X**i) for i in range(4)]
M=[[m[i+j] for j in range(3)] for i in range(2)]+[l[:3]]
rhs=[-m[3],-m[4],-l[3]]
delta=det(M)
N=[]
for k in range(3):
    W=[r[:] for r in M]
    for i in range(3):W[i][k]=rhs[i]
    N.append(det(W))
g=delta
for n in N:g=g.gcd(n)
now('det and numerator degrees',delta.degree(),[n.degree() for n in N],'common',[(x.degree(),e) for x,e in g.factor_list()[1]])
assert g.degree()==6 and g.monic()==D**6
delta=delta//g;N=[n//g for n in N]
assert delta and all(sum((M[i][j]*N[j] for j in range(3)),D0.zero)==delta*rhs[i] for i in range(3))
Q=co(delta)*X**3+sum((co(n)*X**j for j,n in enumerate(N)),R.zero)
P6=P3*Q
B=R.zero
for (j,),z in P6.items():
  for i in range(j):
    B+=co(z*D**(j-i-1)*C(1,j-i))*X**i
R2=(X-co(t))*(X-co(r))
jr=J(R2);JR=co(jr.evaluate(X,D))-jr
eq=(R2-JR)*B+co(JR.evaluate(X,t)*B.evaluate(X,t))
AtS=eq.evaluate(X,s)
now('primitive polynomial degrees',delta.degree(),[n.degree() for n in N],AtS.degree(),eq.degree())
Ns=Q.resultant(eq)
now('raw norm degree',Ns.degree())
colls=[D,delta]+[Q.evaluate(X,e) for e in (s,t,r)]
def strip(p):
 for guard in colls:
    k=0
    while True:
      h=p.gcd(guard)
      if h.degree()==0:break
      p=p//h
      k+=1
    if k:now('removed guard',colls.index(guard),k)
 return p
AtS=strip(AtS);Ns=strip(Ns)
now('guarded projections',AtS.degree(),Ns.degree())
assert [(f.degree(),e) for f,e in AtS.factor_list()[1]]==[(4,1)]
assert [(f.degree(),e) for f,e in Ns.factor_list()[1]]==[(18,1)]
F=AtS if which=='s' else Ns
def rr(a,p):
 t=S.Rational(str(a));return int(t.p)*pow(int(t.q),-1,p)%p
def evp(k,v,p):
 n=0
 for c in k.to_list():n=(n*v+rr(c,p))%p
 return n

def test(v,D,Fq,P,dbase,Qco,Gco):
  # dx: evaluate in actual finite Diag field; xc: construction polynomial over that field
  b0=Fq(0)
  def DX(pol):
    out=b0
    for c in reversed(pol):
      out=out*D+c
    return out
  d=DX(dbase)
  if D==b0 or d==b0:return None
  x=P([0,1]);q=P([DX(c)/d for c in Qco]);E=P([DX(c) for c in Gco])
  roots=q.roots()
  if len(roots)!=3 or any(n!=1 for _,n in roots):return None
  s=D-1;t=s-v;r=s-(2*v if mode=='arith' else 2-v)
  roots=[a for a,_ in roots]
  if any(a==b for a,b in combinations(roots+[s,t,r],2)):return None
  options=[s] if which=='s' else [a for a in roots if E(a)==b0]
  if not options or (which=='s' and E(s)!=b0):return None
  P0=2*x-1-x*x/Fq(2)
  R0=(x-1)**2;R1=-(x-1)
  J=lambda p:sum((p[j]*x**(j+1)/Fq(j+1) for j in range(p.degree()+1)),P([]))
  L=lambda y:70*y**4-140*D*y**3+90*D*D*y*y-20*D**3*y+D**4
  U=x;Hu=-2+U+4*U**2-U**3
  z0,z1,z2=P0,R0,R1
  pl=[(z,J(z),J(x*z)) for z in (z0,z1,z2)]
  bad=[]
  fr=0
  for e in options:
    nodes=[a for a in roots+[s] if a!=e]
    assert len(nodes)==3
    for a,b in permutations(nodes,2):
      fr+=1
      j0,j1,j2=[j(a)-z(a) for z,j,jx in pl]
      F0=Hu*j0+(3*U-2)*(j1+j2*U)
      def GC(z,j,jx):
        return L(a)*((b-a)*z(b)+a*j(b)-jx(b))-L(b)*(a*z(a)-jx(a))
      k0,k1,k2=[GC(z,j,jx) for z,j,jx in pl]
      F1=Hu*k0+(3*U-2)*(k1+k2*U)
      if max(F0.degree(),F1.degree())<3:return None
      g=F0.gcd(F1)
      if g.degree():bad.append(('arith',str(a),str(b),str(e),str(g)))
      if j0==b0:
         bad.append(('front cubic',str(a),str(b),str(e)))
  return fr,bad


primes={
    ('star','s'):(17,12,[1,3]),
    ('arith','s'):(17,12,[1,3]),
    ('star','new'):(23,6,[1,1,2,4,5,5]),
    ('arith','new'):(239,100,[2,4,5,7]),
}
p,v,pdegrees=primes[(mode,which)]
assert S.isprime(p)
vh=nmod_poly([rr(c,p) for c in reversed(H.all_coeffs())],p)
assert vh(v)==0 and vh.derivative()(v)!=0
def dx(poly):
 return [evp(poly.get((i,),K.zero),v,p) for i in range(poly.degree()+1)]

df=nmod_poly(dx(F),p)
db=dx(delta)
Qco=[dx(Q.get((i,),D0.zero)) for i in range(4)]
Gco=[dx(eq.get((i,),D0.zero)) for i in range(9)]
assert df.degree()==F.degree()
facts=df.factor()[1]
assert sorted(fa.degree() for fa,e in facts)==pdegrees and all(e==1 for _,e in facts)
n=0
checks=0
FqP={}
for fa,_ in facts:
  d=fa.degree()
  if d not in FqP:
    Fq=fq_default_ctx(p,6*d,var='a')
    assert Fq.modulus().is_irreducible()
    FqP[d]=Fq,fq_default_poly_ctx(Fq)
  Fq,P=FqP[d]
  ds=P([int(c) for c in fa.coeffs()]).roots()
  assert len(ds)==d and all(e==1 for _,e in ds)
  for de,e in ds:
    out=test(Fq(v),de,Fq,P,db,Qco,Gco)
    assert out is not None
    count,bad=out
    assert count and not bad
    checks+=count
    n+=1
assert n==F.degree()
now('fixed geometric replay',mode,which,p,v,'diagonal roots',n,'directed forward pairs',checks)
