"""Live-third ordinary and reverse moment minors in the varying-triple chart."""
import sympy as S
from itertools import combinations
from sympy.polys.rings import ring
from time import monotonic
import sys
phase=sys.argv[1];j0=int(sys.argv[2])
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),phase,j0,*a,flush=True)
u=S.symbols('u')
f=S.Poly(4*u**3-12*u*u+3*u+2,u)
assert f.is_irreducible
K=S.QQ.algebraic_field((f,u));u=K.unit
C=lambda a,b=1:K.convert(S.Rational(a,b))
R,v,g=ring("v,g",K)
T,X=ring("X",R.to_domain())
x=lambda c:T(R(c))
def I(P):return sum((z*C(1,j+1) for (j,),z in P.items()),R.zero)
def det(M):
 x,y,z=M
 return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])
a=(1+2*u)*g;d=(1+j0*u)*g;s=1-g
if phase=='star':
     # v represents the squared reverse displacement parameter here.
     m=1-2*g
     PH=(X-x(m))**2-x(g*g*v)
     Pf=(X-x(a))*(X-x(s))
     P4=Pf*PH
     A2=Pf*(X-x(d))
     A3=x(2-v)*Pf*(x(d-m)*(X-x(m))-x(g*g*v))-x(d-s)*(X-x(a))*PH
     guards=[g,v,v-1,v-2,d-s,a-s,(m-d)**2-g*g*v,(m-a)**2-g*g*v]
else:
     t=s-g*v;r=s-2*g*v
     H=v**3-4*v*v-v+2
     Q=4*v**3-12*v*v+3*v+2
     k=1+2*v-v*v
     P4=(X-x(a))*(X-x(s))*(X-x(t))*(X-x(r))
     A2=x(k*(d-t))*(P4//(X-x(t)))-x(d-s)*(P4//(X-x(s)))
     A3=-x(Q*(d-r))*(P4//(X-x(r)))-x(H*(d-t))*(P4//(X-x(t)))
     guards=[g,v,H,Q,k,d-s,a-s,d-t,d-r,a-t,a-r]
rows=[[I(P*X**i) for i in range(3)] for P in (P4,P4*X,A2,A3)]
def strip(p):
     if not p:return p
     for z in guards:
       while True:
        h=p.gcd(z)
        if h.degree(v)==0 and h.degree(g)==0:break
        p=p//h
     return p
polys=[]
for idxs in combinations(range(4),3):
    F=strip(det([rows[i] for i in idxs]))
    print('minor',idxs,F.degree(v),F.degree(g),len(F),flush=True)
    assert F
    polys.append(F)
answer=None
for i,j in ((0,1),(0,2),(1,2),(0,3),(1,3),(2,3)):
    n=polys[i].resultant(polys[j])
    print('resultant pair',i,j,'degree g', n.degree(),flush=True)
    if n:
        answer=n if answer is None else answer.gcd(n)
        print('projection running gcd degree',answer.degree(),flush=True)
        if answer.degree()==0:break
assert answer
factors=answer.factor_list()[1]
print('projected factors',[(p.degree(),k) for p,k in factors],flush=True)
assert answer.degree()==(11 if phase=='star' else 82)
assert sorted((p.degree(),k) for p,k in factors)==([(1,2),(9,1)] if phase=='star' else [(1,1),(1,8),(4,1),(69,1)])
for z,e in factors:
    if z.degree()<=2: print(z.as_expr(),e,flush=True)
from flint import nmod_poly
from sympy import primerange
def mod_large(PHI):
    """Find one simple good reduction at which all necessary v gates are coprime."""
    def rc(c,p):
        c=S.Rational(str(c))
        return int(c.p)*pow(int(c.q),-1,p)%p
    def ck(c,z,p):
        h=0
        for b in c.to_list():h=(z*h+rc(b,p))%p
        return h
    min_polys=polys
    def pmod(a,uu,gg,pp):
        co=[0]*(1+a.degree(v)) if a else []
        for (i,j),c in a.items():co[i]=(co[i]+ck(c,uu,pp)*pow(gg,j,pp))%pp
        return nmod_poly(co,pp)
    for p in primerange(11,400):
      qU=nmod_poly([2,3,-12,4],p)
      for x0,e0 in qU.roots():
        if e0!=1:continue
        uu=int(x0)
        try:
          pg=nmod_poly([ck(PHI.get((i,),K.zero),uu,p) for i in range(PHI.degree()+1)],p)
        except ValueError:
          continue
        if pg.degree()!=PHI.degree():continue
        for y0,e0 in pg.roots():
          if e0!=1:continue
          gg=int(y0)
          try:
            fm=[pmod(q,uu,gg,p) for q in min_polys]
            rows_mod=[[pmod(t,uu,gg,p) for t in q] for q in rows]
          except ValueError:
            continue
          if fm[0].degree()!=min_polys[0].degree(v):continue
          hh=fm[0]
          for z in fm[1:]:hh=hh.gcd(z)
          if hh.degree()==0:
            now("good reduction certifies no common v",p,uu,gg)
            return (p,uu,gg,[])
          Z=nmod_poly([0,1],p)
          # Forward second-supported gate as a polynomial in the actual
          # physical next zero clock, at the fixed reduction (u,gamma).
          a0=(1+2*uu)*gg%p
          def LL(X):return 70*X**4-140*X**3+90*X*X-20*X+1
          pc=[gg*gg*(1+uu)%p,-gg*(2+uu)%p,1]
          def ev(t):return sum(c*t**i for i,c in enumerate(pc))
          def J(j,t):return sum(c*t**(i+j+1)*pow(i+j+1,-1,p) for i,c in enumerate(pc))
          Gpoly=LL(a0)*(a0*(J(0,Z)-gg*ev(Z))+gg*Z*ev(Z)-J(1,Z))-LL(Z)*(gg*a0*ev(a0)-J(1,a0))
          tested=[]
          for i,j in combinations(range(4),2):
            a0,a1,a2=rows_mod[i];b0,b1,b2=rows_mod[j]
            DD=a0*b1-a1*b0;NK=a2*b0-a0*b2;NQ=a1*b2-a2*b1
            k1=NK;k0=NQ*DD
            def m2(a,b):
                aa,ab=a;ba,bb=b
                return (aa*ba-k0*ab*bb, aa*bb+ab*ba-k1*ab*bb)
            A0=nmod_poly([],p);A1=nmod_poly([],p)
            PP=(nmod_poly([1],p),nmod_poly([],p))
            for k in range(5):
                coeff=int(Gpoly[k])*DD**(4-k)
                A0+=coeff*PP[0];A1+=coeff*PP[1]
                PP=m2(PP,(nmod_poly([],p),nmod_poly([1],p)))
            NN=A0*A0-k1*A0*A1+k0*A1*A1
            hh=hh.gcd(NN);tested.append((i,j))
            if hh.degree()==0:
              now("simple good reduction and forward gd1",p,uu,gg,tested)
              return (p,uu,gg,tested)
    return None

S0=R.drop(0)
gg=S0.gens[0]
for PHI,exponent in factors:
    PHI=PHI.monic()
    now("projected coefficient degree",PHI.degree())
    if PHI.degree()>20:
        expected=(17,16,14,[(0,1)]) if j0==0 else (11,3,2,[(0,1)])
        assert mod_large(PHI)==expected
        continue
    F0=lambda q:S0(q)%PHI
    def inv(q):
        q=q%PHI
        t,z,h=q.gcdex(PHI)
        assert h==S0.one and q*t+PHI*z==h
        return t%PHI
    def tr(l):
        while l and not l[-1]:l.pop()
        return l
    def cs(a):
        if not a:return []
        out=[S0.zero]*(a.degree(v)+1)
        for (i,j),q in a.items():out[i] += q*gg**j
        return tr([k%PHI for k in out])
    def vl(a,b):
        xx=a[:];m=len(b)-1
        hh=inv(b[-1])
        while len(xx)>m:
            n=len(xx)-len(b)
            coeff=(xx[-1]*hh)%PHI
            for j in range(len(b)):xx[j+n]=(xx[j+n]-coeff*b[j])%PHI
            xx=tr(xx)
        return xx
    def vgcd(a,b):
        a=tr(a[:]);b=tr(b[:])
        while b:a,b=b,vl(a,b)
        if not a:return a
        h=inv(a[-1])
        return [(z*h)%PHI for z in a]
    def vquo(a,b):
        h=inv(b[-1]); a=a[:];q=[S0.zero]*(len(a)-len(b)+1)
        assert q
        for n in range(len(q)-1,-1,-1):
            cc=(h*a[n+len(b)-1])%PHI;q[n]=cc
            for k,z in enumerate(b):a[k+n]=(a[k+n]-cc*z)%PHI
        assert not any(a)
        return tr(q)
    guard_cs=[cs(G) for G in guards]
    if not all(guard_cs):
        now("an actual unit guard vanishes identically")
        continue
    h=cs(polys[0])
    for pol in polys[1:]:h=vgcd(h,cs(pol))
    now("four actual minors gap gcd degree",len(h)-1)
    assert h
    for gd in guard_cs:
        while True:
           q=vgcd(h,gd)
           if len(q)<=1:break
           h=vquo(h,q)
    now("guarded gap degree",len(h)-1)
    if len(h)==1:continue
    assert len(h)==2
    v0=(-h[0]*inv(h[1]))%PHI
    def evalv(a):
        s=S0.zero
        for k in reversed(cs(a)):s=(s*v0+k)%PHI
        return s
    G=gg%PHI;A=evalv(a);D=evalv(d)
    M=[[evalv(t) for t in row] for row in rows]
    q=None
    for i,j in combinations(range(4),2):
        x0,x1,x2=M[i];y0,y1,y2=M[j]
        p=(x0*y1-x1*y0)%PHI
        if not p:continue
        j0j=inv(p)
        q=((x1*y2-x2*y1)*j0j%PHI,(x2*y0-x0*y2)*j0j%PHI)
        break
    assert q
    q0,q1=q
    assert all(not ((e*q0+f*q1+h)%PHI) for e,f,h in M)
    if not (q1*q1-4*q0)%PHI:
        now("free ordinary repeated")
        continue
    def E(q0):return E2(q0)
    class E2:
        def __init__(self,a=0,b=0):
            if isinstance(a,E2):self.a,self.b=a.a,a.b;return
            self.a,self.b=F0(a),F0(b)
        def __neg__(self):return E2(-self.a,-self.b)
        def __add__(self,q):
            z=E2(q);return E2(self.a+z.a,self.b+z.b)
        __radd__=__add__
        def __sub__(self,q):return self+-E2(q)
        def __rsub__(self,q):return -self+E2(q)
        def __mul__(self,q):
            z=E2(q);bb=self.b*z.b
            return E2(self.a*z.a-q0*bb,self.a*z.b+self.b*z.a-q1*bb)
        __rmul__=__mul__
        def __pow__(self,n):
            if n==0:return E2(1)
            if n%2==0:return (self*self)**(n//2)
            return self*self**(n-1)
        def norm(self):return (self.a*self.a-q1*self.a*self.b+q0*self.b*self.b)%PHI
    gk=E2(G);aa=E2(A);b=E2(0,1)
    def L(x):return 70*x**4-140*x**3+90*x**2-20*x+1
    if not L(aa).a:
        now("first L4 guard")
        continue
    P=[E2((1+u)*G*G),E2(-(2+u)*G),E2(1)]
    def ev(x):return sum((q*x**i for i,q in enumerate(P)),E2())
    def J(i,x):return sum((q*x**(i+k+1)*C(1,i+k+1) for k,q in enumerate(P)),E2())
    assert not (J(0,aa)-gk*ev(aa)).a
    FF=L(aa)*(aa*(J(0,b)-gk*ev(b))+gk*b*ev(b)-J(1,b))-L(b)*(gk*aa*ev(aa)-J(1,aa))
    nf=FF.norm()
    now("forward norm regular?",bool(nf), 'ordinary principal pivot?',bool((M[0][0]*M[1][1]-M[1][0]*M[0][1])%PHI))
    assert nf
