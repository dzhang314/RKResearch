"""Exact masked moments and graph pencil over Q(v)[g], v^3-4v^2-v+2=0."""
from flint import fmpq, fmpq_poly, fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx
from time import monotonic
t0=monotonic()
def now(*a):print(round(monotonic()-t0,2),*a,flush=True)
def Q(a,b=1):return fmpq(a,b)
CV0=fmpq_poly()
class V:
    """Triples of rational polynomials; v^3=4v^2+v-2."""
    def __init__(self,*f):
        if len(f)==1 and isinstance(f[0],V): self.c=f[0].c; return
        if len(f)==1 and isinstance(f[0],(int,fmpq)): f=(fmpq_poly([f[0]]),)
        self.c=tuple(f)+(CV0,)*(3-len(f))
    def __bool__(self):return any(self.c)
    def __eq__(self,y):return self.c==V(y).c
    def __neg__(self):return V(*(-x for x in self.c))
    def __add__(self,y):
        if "T" in globals() and isinstance(y,T):return NotImplemented
        return V(*(x+z for x,z in zip(self.c,V(y).c)))
    __radd__=__add__
    def __sub__(self,y):return self+-V(y)
    def __rsub__(self,y):return -self+V(y)
    def __mul__(self,y):
        if "T" in globals() and isinstance(y,T):return NotImplemented
        a,b,c=self.c;d,e,f=V(y).c
        h0=a*d;h1=a*e+b*d;h2=a*f+b*e+c*d;h3=b*f+c*e;h4=c*f
        return V(h0-2*h3-8*h4,h1+h3+2*h4,h2+4*h3+17*h4)
    __rmul__=__mul__
    def __pow__(x,n):
        if n==0:return V(1)
        if n%2==0:return (x*x)**(n//2)
        return x*x**(n-1)
    def degree(self):return max(x.degree() for x in self.c)
    def coeff(self,j):return V(*(fmpq_poly([x[j]]) for x in self.c))
    def shift(self,n):return V(*(x.left_shift(n) for x in self.c))
    def adj_norm(self):
        a,b,c=self.c;d,e,f=(self*v).c;g,h,i=(self*v*v).c
        adj=V(e*i-f*h,c*h-b*i,b*f-c*e)
        N=a*adj.c[0]+d*adj.c[1]+g*adj.c[2]
        assert self*adj==V(N)
        return adj,N
    def invconst(self):
        assert self.degree()==0
        adj,N=self.adj_norm()
        return V(*(x/N[0] for x in adj.c))
    def divrem(self,d):
        assert d
        if self.degree()<d.degree():return V(0),self
        adj,N=d.adj_norm()
        q=V(*(x//N for x in (self*adj).c))
        r=self-q*d
        assert r.degree()<d.degree()
        return q,r
    def __mod__(self,d):return self.divrem(d)[1]
    def exact(self,d):
        q,r=self.divrem(d)
        assert not r
        return q
    def monic(self):
        return self*self.coeff(self.degree()).invconst() if self else self
    def gcd(self,d):
        x,y=self,d
        if y.degree()>x.degree():x,y=y,x
        while y:
            x,y=y,x%y
        return x.monic()
    def reduce(self,ctx,p,v):
        assert all(int(x.denominator)%p for pol in self.c for x in pol.coeffs())
        s=ctx.zero()
        for i,pol in enumerate(self.c):
            s+=ctx([int(x.numerator)*pow(int(x.denominator),-1,p)%p*v**i for x in pol.coeffs()])
        return s
    def __repr__(self):return str(self.c)

v=V(CV0,fmpq_poly([1]),CV0)
G=V(fmpq_poly([0,1]))
assert v**3-4*v**2-v+2==0
# All symbolic variable scalars, including g, d, and the basis variables.
t=1-G*(1+v);s=1-G
m=[V(Q(1,k+3))-(t+s)*Q(1,k+2)+t*s*Q(1,k+1) for k in range(6)]
m0,m1,m2,m3,m4,m5=m
def det(M):
    x,y,z=M
    return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])
MM=[[m[i+j] for j in range(3)] for i in range(3)]
Delta=det(MM)
num=[]
for j in (0,1,2):
    X=[row[:] for row in MM]
    for i in range(3):X[i][j]=-m[i+3]
    num.append(det(X))
qnum,lnum,knum=num
# A = Delta*a, B = Delta*b to make the two clock equations monic.
ra=[qnum*Delta**2,lnum*Delta,knum]
AZ=V(0)
ON=V(1)
def amul(x,y):
    out=[AZ]*5
    for i,b in enumerate(x):
        if b:
            for j,c in enumerate(y):
                if c:out[i+j]=out[i+j]+b*c
    for k in range(4,2,-1):
        if out[k]:
            for j in range(3):out[k+j-3]=out[k+j-3]-out[k]*ra[j]
    return tuple(out[:3])
def aplus(x,y): return tuple(a+b for a,b in zip(x,y))
def aneg(x):return tuple(-a for a in x)
def anorm(x):
    y=amul(x,(AZ,ON,AZ));z=amul(x,(AZ,AZ,ON))
    return det([list(i) for i in zip(x,y,z)])
U0=(AZ,)*3
U1=(ON,AZ,AZ)
# B^2 + (A+knum)*B + (A^2+knum*A+lnum*Delta)=0
rb1=(knum,ON,AZ);rb0=(lnum*Delta,knum,ON)
class T:
    def __init__(self,*f):
        if len(f)==1:
            if isinstance(f[0],T):self.c=f[0].c;return
            f=((V(f[0]),AZ,AZ),U0)
        self.c=f
    def __bool__(self):return any(any(y) for y in self.c)
    def __eq__(self,y): return self.c==T(y).c
    def __neg__(self):return T(*(aneg(x) for x in self.c))
    def __add__(self,y):return T(*(aplus(x,z) for x,z in zip(self.c,T(y).c)))
    __radd__=__add__
    def __sub__(self,y):return self+-T(y)
    def __rsub__(self,y):return -self+T(y)
    def __mul__(self,y):
        a,b=self.c;c,d=T(y).c
        bd=amul(b,d)
        return T(aplus(amul(a,c),aneg(amul(bd,rb0))),
                 aplus(aplus(amul(a,d),amul(b,c)),aneg(amul(bd,rb1))))
    __rmul__=__mul__
    def __pow__(x,n):
        if n==0:return T(1)
        if n%2==0:return (x*x)**(n//2)
        return x*x**(n-1)
    def norm(self):
        a,b=self.c
        return anorm(aplus(aplus(amul(a,a),aneg(amul(amul(a,b),rb1))),amul(amul(b,b),rb0)))
    def degree(self):return max(v.degree() for p in self.c for v in p)
    def exact(self,d):return T(*(tuple(v.exact(d) for v in p) for p in self.c))
    def rem(self,d):return T(*(tuple(v%d for v in p) for p in self.c))
    def contents(self,guard):
        for coeff3 in self.c:
            for x in coeff3:
                guard=guard.gcd(x)
                if guard.degree()==0:return guard
        return guard
    def __repr__(self):return str(self.c)

d=T(Delta);g=T(G*Delta);a=T((AZ,ON,AZ),U0);b=T(U0,U1);c=-T(knum)-a-b
assert a**3+knum*a*a+lnum*Delta*a+qnum*Delta**2==0
assert b**2+(a+knum)*b+a*a+knum*a+lnum*Delta==0
def L(t):return 70*t**4-140*d*t**3+90*d*d*t*t-20*d**3*t+d**4
def L3(t):return t**3-Q(3,2)*d*t*t+Q(3,5)*d*d*t-Q(1,20)*d**3
la,lb,lc=L(a),L(b),L(c)
ya,yb,yc=L3(a),L3(b),L3(c)
def ev(P,T0):return sum((z*T0**i for i,z in enumerate(P)),T(0))
def J(P,k,T0):return sum((z*T0**(i+k+1)*Q(1,i+k+1) for i,z in enumerate(P)),T(0))
def gate(P):
    E0=J(P,0,a)-g*ev(P,a)
    eta=g*a*ev(P,a)-J(P,1,a)
    F=la*(a*(J(P,0,b)-g*ev(P,b))+g*b*ev(P,b)-J(P,1,b))-lb*eta
    da=g*a*a*ev(P,a)-J(P,2,a)
    db=g*b*b*ev(P,b)+a*a*(J(P,0,b)-g*ev(P,b))-J(P,2,b)
    dc=(g*c*c*ev(P,c)+(a+b)*(J(P,1,c)-g*c*ev(P,c))-a*b*(J(P,0,c)-g*ev(P,c))-J(P,2,c))*la+lc*(eta*(a+b))
    H=(ya*lb-yb*la)*dc+(yb*lc-yc*lb)*(la*da)+(yc*la-ya*lc)*(la*db)
    return E0,F,H
P0=[-g*g,2*g,T(Q(-1,2))]
R1=[-g*g,g];R2=[g*g,-2*g,T(1)]
def norm_stripp(F):
    F=list(F)
    for guard in [G,Delta]:
        while True:
            op=guard
            for q in F:
                op=q.contents(op)
                if op.degree()==0:break
            if op.degree()==0:break
            F=[q.exact(op) for q in F]
    return F
F0,G0,H0=gate(P0);F1,G1,H1=gate(R1);F2,G2,H2=gate(R2)
for f0 in (F0,F1,F2,G0,G1,G2,H0,H1,H2):
    assert f0
F0,F1,F2=norm_stripp([F0,F1,F2]);G0,G1,G2=norm_stripp([G0,G1,G2]);H0,H1,H2=norm_stripp([H0,H1,H2])
now('three gate rows',[(f.degree()) for f in [F0,F1,F2,G0,G1,G2,H0,H1,H2]])
D=F1*G2-F2*G1
BN=F2*G0-F0*G2;AN=F0*G1-F1*G0
PD=D*H0+BN*H1+AN*H2
AR=-2*AN**3-BN*AN*AN+4*BN*BN*AN+BN**3+(3*BN*AN+2*AN*AN)*D
now('raw substituted polynomial degrees',PD.degree(),AR.degree())
disc=knum*knum*ra[1]**2-4*ra[1]**3-4*knum**3*ra[0]-27*ra[0]**2+18*knum*ra[1]*ra[0]

norms = [norm_stripp([e])[0].norm() for e in [PD,AR,D,AN,BN]]
assert tuple(r.degree() for r in norms) == (654,954,348,348,342)
now("norm degrees", tuple(r.degree() for r in norms))

# Structural guards. All known and unknown ordinary clocks are distinct;
# the scaled cubic is separable and the L4 values at all its roots are nonzero.
disc_part=disc.exact(Delta**2)
legendre_part=la.norm().exact(Delta**16)
assert (Delta.degree(),disc_part.degree(),legendre_part.degree())==(6,24,48)

# The finite arithmetic is a characteristic-zero rank certificate, not
# an enumeration of points. Check irreducibility and all top degrees.
p=19
h=fmpz_mod_poly_ctx(p)([2,-1,-4,1])
factors=h.factor()[1]
assert len(factors)==1 and factors[0][0].degree()==3 and factors[0][1]==1
C=fq_default_ctx(modulus=h,var='v'); F=fq_default_poly_ctx(C); vw=C.gen()
def M(f):
    m=f.reduce(F,p,vw)
    assert m.degree()==f.degree()
    return m
mod_norms=[M(n) for n in norms]
assert (Delta**48*disc_part**3*legendre_part**3).degree()==504
assert (Delta**30*disc_part*legendre_part).degree()==252
checks=[
    (norms[:2], mod_norms[0].gcd(mod_norms[1]), (48,3,3), (150,450)),
    (norms[2:], mod_norms[2].gcd(mod_norms[3]), (30,1,1), (96,96,90)),
]
for group, residue_gcd, exps, degrees in checks:
    mod_divisor=F.one()
    for h,e in zip((Delta,disc_part,legendre_part),exps):
        mod_divisor*=M(h)**e
    assert residue_gcd==mod_divisor.monic()
    for R0,deg in zip(group,degrees):
        for h,e in zip((Delta,disc_part,legendre_part),exps):
            R0=R0.exact(h**e)
        assert R0.degree()==deg
    now("exact divisor and degree-preserving residue gcd",mod_divisor.degree(),
        "quotient degrees",degrees)
print("The regular and singular gcd supports are wholly structurally forbidden.")
