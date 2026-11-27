import sympy as s
from itertools import permutations
import warnings
from sympy.utilities.exceptions import SymPyDeprecationWarning
warnings.filterwarnings('ignore', category=SymPyDeprecationWarning)
class Fp:
    def __init__(self,p,m):
        self.p,self.m,self.d=p,m,len(m)-1
        self.z=(0,)*self.d
        self.o=self.cn(1)
    def cn(self,v):
        return (v%self.p,)+(0,)*(self.d-1)
    def add(self,a,b): return tuple((u+v)%self.p for u,v in zip(a,b))
    def neg(self,a):return tuple(-u%self.p for u in a)
    def sub(self,a,b):return self.add(a,self.neg(b))
    def pk(self,k,a): return self.mul(self.cn(k),a)
    def mul(self,a,b):
        r=[0]*(2*self.d-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                r[i+j]=(r[i+j]+x*y)%self.p
        for i in range(len(r)-1,self.d-1,-1):
            for j,x in enumerate(self.m[:-1]):
                r[i-self.d+j]=(r[i-self.d+j]-r[i]*x)%self.p
        return tuple(r[:self.d])
    def pw(self,a,k):
        r=self.o
        while k:
            if k%2:r=self.mul(r,a)
            k>>=1
            if k:a=self.mul(a,a)
        return r
    def inv(self,a):
        assert a!=self.z,'zero field inverse'
        P=s.Poly(sum(x*t**i for i,x in enumerate(self.m)),t,modulus=self.p)
        q=s.Poly(sum(x*t**i for i,x in enumerate(a)),t,modulus=self.p)
        try: v=s.invert(q,P)
        except Exception: raise ArithmeticError(f'nonunit: {a} gcd {s.gcd(q,P)}')
        iv=tuple(int(v.nth(i))%self.p for i in range(self.d))
        assert self.mul(a,iv)==self.o
        return iv
    def dv(self,a,b):return self.mul(a,self.inv(b))
    def tr(self,a):
        a=list(a)
        while a and a[-1]==self.z:a.pop()
        return a
    def A(self,a,b):
        return self.tr([self.add(a[i] if i<len(a) else self.z,b[i] if i<len(b) else self.z) for i in range(max(len(a),len(b)))])
    def N(self,a):return [self.neg(x) for x in a]
    def S(self,a,b):return self.A(a,self.N(b))
    def M(self,a,b):
        r=[self.z]*max(0,len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                r[i+j]=self.add(r[i+j],self.mul(x,y))
        return self.tr(r)
    def rem(self,a,b):
        assert b
        v=self.inv(b[-1]); r=a[:]
        while len(r)>=len(b):
            q=self.mul(r[-1],v); n=len(r)-len(b)
            for j,t in enumerate(b):r[j+n]=self.sub(r[j+n],self.mul(q,t))
            r=self.tr(r)
        return r
    def gcd(self,a,b):
        while b:a,b=b,self.rem(a,b)
        return [self.mul(x,self.inv(a[-1])) for x in a] if a else a

X,t,u,k,w=s.symbols('X t u k w')
P10=243*t**10-2511*t**9+20839*t**8-201939*t**7+1127457*t**6-3341909*t**5+4387533*t**4-240993*t**3-3165372*t**2+698544*t+1333584
h0=756*t**3*u**4+168*t**3*u**2+28*t**3*u+3*t**3-1008*t**2*u**2-336*t**2*u-45*t**2+1008*t*u+216*t-324
h1=42*t**4*u**4+42*t**3*u**4-84*t**3*u**3-7*t**2*u-t**2+42*t*u+9*t-18
def ep(F,x,vals):
    a=F.z
    for q in s.Poly(x,*vals).terms():
        ex,v=q; v=s.Rational(v)
        z=F.dv(F.cn(int(v.p)),F.cn(int(v.q)))
        for tv,e in zip(vals.values(),ex):z=F.mul(z,F.pw(tv,e))
        a=F.add(a,z)
    return a
def polyx(F,x,var,vals):
    xp=s.Poly(x,var)
    return F.tr([ep(F,xp.nth(j),vals) for j in range(max(0,xp.degree()+1))])
def det(F,a):
    res=[]
    assert len(a)==len(a[0])
    for perm in permutations(range(len(a))):
        x=[F.o]; sign=(-1)**sum(perm[i]>perm[j] for i in range(len(a)) for j in range(i+1,len(a)))
        for i,j in enumerate(perm):x=F.M(x,a[i][j])
        res=F.A(res,x if sign==1 else F.N(x))
    return res
Qbasis=[(1-X)*X**j for j in range(4)]
M=s.Matrix([[s.integrate(X**e*g,(X,0,1)) for g in Qbasis]for e in range(1,5)]).inv()
T0=s.Matrix([[s.cancel(X*g/(1-X)).expand().coeff(X,j) for g in Qbasis[:3]]for j in range(4)])
T1=s.Matrix([[s.cancel(g/(1-X)).expand().coeff(X,j) for g in Qbasis[:3]]for j in range(4)])
T2=s.Matrix([[s.cancel(s.integrate(g,(X,X,1))/(1-X)).expand().coeff(X,j) for g in Qbasis[:3]]for j in range(4)])
# Independent exact source identities.
S=t*u
AB=S*S/(6-t)
P=X**3-S*X**2+AB*X
J=s.integrate(P,X)
H=X-14*X**2+56*X**3-84*X**4+42*X**5
D=(X-u)*P
R=-1/(u*AB)
E=2*(-14-R*(AB+u*S))/AB
err=s.Poly(s.expand(H-E*J-(R+42*X)*D),X)
assert s.cancel(err.nth(3)-h0/(3*t*t*u*u*(t-6)))==0
assert s.cancel(err.nth(4)-h1/(t**3*u**3))==0
assert s.cancel(s.integrate(J,X)-t*X*D/(10*(3-2*t))-S*J/(5*(3-2*t))
                -(3-4*t)*X*J/(5*(3-2*t)))==0
assert s.expand(s.resultant(h0,h1,u)-1037232*t**13*(t-6)**4*(t-3)*P10)==0
assert s.degree(s.gcd(h0.subs(t,3),h1.subs(t,3)),u)==1
assert s.gcd(h0.subs(t,3),h1.subs(t,3)).subs(u,0)==0
assert M==s.Matrix([[300,-2100,4200,-2520],[-2100,16800,-36120,22680],
                    [4200,-36120,81480,-52920],[-2520,22680,-52920,35280]])
assert 12*T2==s.Matrix([[6,2,1],[-6,2,1],[0,-4,1],[0,0,-3]])
print("exact rational coefficient, primitive, Beta, resultant and t=3 checks PASS")
# Denominator clearing: front eq and necessary rank of Q4=(X-w)Q3+k' I*Q3 where k'=(w-y)/d-1.
for pp in [419,719,227,587]:
    fac=[(P10,1)]
    print("prime", pp, "degree-ten coefficient quotient", flush=True)
    # The t=3 branch was excluded over the rationals above.
    Ft=Fp(pp,[0,1]); v3={t:Ft.cn(3)}
    uu=Ft.gcd(polyx(Ft,h0,u,v3),polyx(Ft,h1,u,v3)); assert uu==[Ft.z,Ft.o]
    for f,mm in fac:
        P=s.Poly(f,t,modulus=pp).monic()
        F=Fp(pp,[int(P.nth(j))%pp for j in range(P.degree()+1)])
        tf=F.rem([F.z,F.o],[F.cn(c) for c in F.m]) if F.d==1 else (0,1)+(0,)*(F.d-2)
        tf=tf[0] if F.d==1 and tf else F.z if F.d==1 else tf
        vals={t:tf}
        G=F.gcd(polyx(F,h0,u,vals),polyx(F,h1,u,vals)); print('u-gcd',len(G)-1,flush=True)
        assert len(G)==2 and G[1]==F.o
        uf=F.neg(G[0])
        assert ep(F,h0,{t:tf,u:uf})==F.z and ep(F,h1,{t:tf,u:uf})==F.z
        cf=lambda c:[F.cn(c)]
        ss=F.mul(tf,uf); p=F.dv(F.mul(ss,ss),F.sub(F.cn(6),tf))
        r=F.neg(F.inv(F.mul(uf,p)))
        ell=F.dv(F.pk(2,F.sub(F.cn(-14),F.mul(r,F.add(p,F.mul(uf,ss))))),p)
        den=F.sub(F.cn(3),F.pk(2,tf)); B=F.dv(tf,F.pk(10,den)); C=F.dv(ss,F.pk(5,den)); E=F.dv(F.sub(F.cn(3),F.pk(4,tf)),F.pk(5,den))
        kP=[F.z,F.o]; km1=[F.cn(-1),F.o]; sigN=[F.sub(F.o,E),E]
        lamN=F.S(F.M(kP,F.M(km1,[B])),sigN)
        # w numerator / w denominator: r*lamN / (42*sigN)
        wN=F.M([r],lamN); wD=F.M(cf(42),sigN)
        yN=[ell,F.neg(r)]; yD=[F.z,F.cn(42)]
        dN=F.S(yN,F.M([uf],yD)); dD=F.M(yD,F.N(km1))
        # front=-u+(k-1)C+sig*w*k-Lh*ell; sig*w*k=r lamN/42; Lh=lamN/(42k)
        front=F.A(F.M(yD,F.A([F.neg(uf)],F.M(km1,[C]))),F.M(F.S([F.z,r],[ell]),lamN))
        assert len(front)==4 and F.inv(front[-1])!=F.z
        guards=[len(F.gcd(front,f))-1 for f in [kP,km1,wD,dN,F.S(wN,wD),F.S(F.M(wN,yD),F.M(wD,yN))]]
        assert guards==[0]*6
        print('front is cubic; all six guard gcds are one',flush=True)
        # Q4 moment formula M1..4 modulo F
        F1=F.dv(F.sub(F.mul(ss,ss),F.pk(3,p)),F.mul(p,p)); F2=F.dv(ss,p)
        rr=F.sub(F.cn(3),F.dv(F.pk(2,F.mul(uf,F1)),F2))
        moment=[F.dv(F.mul(F.sub(F.cn(2),rr),F1),uf),F.pk(2,F1),F.pk(3,F2),F.cn(12)]
        Q4=[]
        for i in range(4):
            value=F.z
            for j in range(4):value=F.add(value,F.mul(F.cn(int(M[i,j])),moment[j]))
            Q4.append(value)
        # shared rational denominator wD*yD*dN; k' net=(wN*yD-yN*wD)*dD - wD*yD*dN
        denP=F.M(wD,F.M(yD,dN))
        kpN=F.S(F.M(F.S(F.M(wN,yD),F.M(yN,wD)),dD),denP)
        wNX=F.M(wN,F.M(yD,dN))
        def scale(a,c):
            c=s.Rational(c)
            return F.M(a,[F.dv(F.cn(int(c.p)),F.cn(int(c.q)))])
        R=[[F.A(F.S(scale(denP,T0[i,j]),scale(wNX,T1[i,j])),scale(kpN,T2[i,j])) for j in range(3)]+[[Q4[i]]] for i in range(4)]
        test=det(F,R)
        assert F.gcd(front,test)==[F.o]
        print('cleared rank determinant gcd is one',flush=True)
