"""Exact mod-101 replacement for every rational interval certificate in the RK9 proof.

Usage: python rk9_elementary_certificates.py [ORDER9_SOURCE_DIR]
With no arguments, derive every polynomial from the compact formulas.
An optional original source directory cross-checks the H48 coefficients.
No other input files are needed.
No manuscript code is imported; no root isolation is performed.
Use Python without -O. Requires SymPy only for univariate gcd/resultant.
"""
import json,sys
from fractions import Fraction as F
from itertools import permutations, zip_longest
from pathlib import Path
from math import prod
import sympy as S
P=101
class Ring:
    def __init__(self,base,rel):
        self.base,self.rel=base,tuple(rel)
        self.n=len(rel)
        self.k=0 if base is None else base.k+1
        self.z=0 if base is None else base(0)
        self.one=1 if base is None else base(1)
    def __call__(self,x):
        if isinstance(x,E) and x.R is self: return x
        if self.base is None:
            assert not isinstance(x,E)
            x=F(x)
            return E(self,((x.numerator*pow(x.denominator,-1,P))%P,))
        return E(self,(self.base(x),))
    def gen(self):
        assert self.n>1
        return E(self,(self.z,self.one))

class E:
    __slots__='R','a'
    def __init__(self,R,a):
        self.R=R
        if R.k==0: self.a=tuple(i%P for i in a)
        else:self.a=tuple(a)
        i=len(self.a)
        while i and not self.a[i-1]:i-=1
        self.a=self.a[:i]
    def __bool__(self):return bool(self.a)
    def conv(self,o):
        if isinstance(o,E) and o.R.k>self.R.k:return None
        return self.R(o)
    def __add__(self,o):
        if isinstance(o,E) and o.R.k>self.R.k:return o+self
        o=self.conv(o)
        if o is None:return NotImplemented
        return E(self.R,(a+b for a,b in zip_longest(self.a,o.a,fillvalue=self.R.z)))
    __radd__=__add__
    def __neg__(self):return E(self.R,(-a for a in self.a))
    def __sub__(self,o):return self+-o
    def __rsub__(self,o):return -self+o
    def __mul__(self,o):
        if isinstance(o,E) and o.R.k>self.R.k:return o*self
        o=self.conv(o)
        if o is None:return NotImplemented
        a,b,R=self.a,o.a,self.R
        if not a or not b:return E(R,())
        if len(a)==1:return E(R,(a[0]*j for j in b))
        if len(b)==1:return E(R,(b[0]*i for i in a))
        out=[R.z]*(len(a)+len(b)-1)
        if R.k==0:
            # No carries across packed convolution cells.
            w=(max(len(a),len(b))*(P-1)**2).bit_length()+1
            aa=sum(t<<(w*i) for i,t in enumerate(a));bb=sum(t<<(w*i) for i,t in enumerate(b))
            ab=aa*bb;mask=(1<<w)-1
            for i in range(len(out)):
                out[i]=ab&mask;ab>>=w
            for i in range(len(out)-1,R.n-1,-1):
                t=out[i]%P
                if t:
                    for j,k in enumerate(R.rel):out[i-R.n+j]-=t*k
        else:
            for i,ai in enumerate(a):
                if ai:
                    for j,bj in enumerate(b):
                        if bj:out[i+j]=out[i+j]+ai*bj
            for i in range(len(out)-1,R.n-1,-1):
                t=out[i]
                if t:
                    for j,k in enumerate(R.rel):
                        if k:out[i-R.n+j]=out[i-R.n+j]-t*k
        return E(R,out[:R.n])
    __rmul__=__mul__
    def __pow__(self,n):
        assert n>=0
        a,e=self,R1(self)
        while n:
            if n&1:e=e*a
            n>>=1
            if n:a=a*a
        return e
    def __truediv__(self,n):return self*F(1,n)
def R1(e):return e.R(1)

def quo(co,r):
    """Ascending coefficients of the monic quotient by x-r; no division."""
    q=[co[-1]]
    for a in reversed(co[1:-1]):
        q.append(a+r*q[-1])
    return q[::-1]

def tower(base,q4):
    """Iterated monic ordered-root algebra; dimensions 4,3,2."""
    rh=Ring(base,[base(z) for z in q4[:-1]])
    h=rh.gen()
    q3=quo(q4,h)
    ru=Ring(rh,[rh(z) for z in q3[:-1]])
    u=ru.gen()
    q2=quo(q3,u)
    rv=Ring(ru,[ru(z) for z in q2[:-1]])
    v=rv.gen()
    return (h,u,v),(rv,ru,rh)

def det(columns):
    n=len(columns);out=0
    for t in permutations(range(n)):
        neg=sum(t[i]>t[j] for i in range(n) for j in range(i+1,n))%2
        z=prod(columns[j][t[j]] for j in range(n))
        out=out-z if neg else out+z
    return out

def relative_norm(f,R):
    f=R(f);m=[]
    for j in range(R.n):
        m.append(tuple(f.a)+(R.z,)*(R.n-len(f.a)))
        if j+1<R.n:f=f*R.gen()
    return det(m)

def norm(f,towers):
    for R in towers:
        f=relative_norm(f,R)
    return f

def J3(x):return ((x-F(3,2))*x+F(9,14))*x-F(1,14)
def T3(x):return ((x-F(12,7))*x+F(6,7))*x-F(4,35)
def J4(x):return (((x-2)*x+F(4,3))*x-F(1,3))*x+F(1,42)

def main_atlas(H):
    assert len(H)==49 and H[0]%P
    inv=pow(H[0],-1,P)
    base=Ring(None,[t*inv%P for t in reversed(H[1:])])
    L=base.gen()
    q4=[F(1,42)-L/14,L*F(9,14)-F(1,3),F(4,3)-L*F(3,2),L-2,1]
    (h,u,v),tt=tower(base,q4)
    def P0(x):return 3*h*h-6*x*x
    def P1(x):return 3*h*x-4*x*x
    D=2*u-3*v+1
    def FF(PP):return (1-u)*D*J3(v)*PP(u)-(1-v)**2*J3(u)*PP(v)
    F0,F1=FF(P0),FF(P1)
    p=(3*h*h*F1,-3*h*F0,-6*F1+4*F0)
    aa=3*(u-v);bb=4*u*u-5*u*v+2*v-1
    def linear(co):return list(map(sum,zip([-bb*q for q in co]+[0],[0]+[aa*q for q in co])))
    def prem(q):
        assert len(q)==6
        for k in range(5,1,-1):
            lead=q[k];q=[p[2]*a for a in q[:k]]
            q[k-2]=q[k-2]-lead*p[0]
            q[k-1]=q[k-1]-lead*p[1]
        return q
    a=prem([0]+q4)
    def O(q):
        b=prem(q)
        return b[0]*a[1]-b[1]*a[0]
    W5=linear([0,0,h*h,-2*h,1])
    W6=linear([0,0,p[0]/2,p[1]/3,p[2]/4])
    # Exact moment determinant for R(x)=-x(x-h) P_hat(x).
    R=[0,h*p[0],h*p[1]-p[0],h*p[2]-p[1],-p[2]]
    m=[sum(q*F(2,(j+i+1)*(j+i+2)*(j+i+3)) for j,q in enumerate(R)) for i in range(3)]
    Hc=1058400*(m[0]*m[2]-m[1]*m[1])
    T=p[2]*O(W5)*O(W6)*Hc
    f=norm(T,tt)
    l=S.Symbol('ell')
    poly=S.Poly.from_list(list(reversed(f.a)),l,modulus=P)
    Hpoly=S.Poly.from_list(H,l,modulus=P)
    assert Hpoly.degree()==48
    assert poly.gcd(Hpoly).degree()==0
    print('Six-on: leading coefficient H48 mod 101 =',H[0]%P)
    print('Six-on: relative norm of terminal product, coefficients ascending mod 101:')
    print(list(f.a))
    print('PASS: gcd(H48, relative norm terminal product)=1 mod 101.')
    
def radau():
    q4=[F(5,126),-F(10,21),F(5,3),-F(20,9),1]
    base=Ring(None,[0])
    (h,u,v),tt=tower(base,q4)
    r=F(20,9)-h-u-v
    def P0(x):return 3*h*h-6*x*x
    def P1(x):return 3*h*x-4*x*x
    D=2*u-3*v+1;Dn=3*r*r+(2-4*u-4*v)*r+1-2*u-2*v+6*u*v
    Lr=4*u*u-5*u*v+2*v-1-3*(u-v)*r
    def fg(P):
        return ((1-u)**2*D*T3(v)*P(u)-(1-v)**3*T3(u)*P(v),
                D*(1-r)**2*P(r)*T3(v)*Dn+(1-v)**3*P(v)*T3(r)*Lr)
    F0,G0=fg(P0)
    F1,G1=fg(P1)
    tests=[('F0G1-F1G0',F0*G1-F1*G0),('2h-u',2*h-u),
           ('4h-3u',4*h-3*u),('3h²-4(u+v)h+6uv',3*h*h-4*(u+v)*h+6*u*v)]
    for name,f in tests:
        f=norm(f,tt)
        assert len(f.a)==1 and f.a[0]!=0,(name,P)
        print('Fixed Radau:',name,'norm =',f.a[0],'mod 101')
    print('PASS: fixed Radau compatibility and pair/triple controls.')

def endpoint():
    d,z=S.symbols('d z')
    Fdz=S.cancel(588*(J3(2*d)*J4(z)-J4(2*d)*J3(z))/(z-2*d))
    E=S.expand(Fdz.subs(z,d))
    assert E==4704*d**6-10584*d**5+9212*d**4-3990*d**3+910*d**2-105*d+5
    Fbar=S.cancel((Fdz-E)/(z-d))
    G=4*d**3+(2*d**2-48*d**3)*z+(-9*d+216*d**2-1512*d**3+4480*d**4-4032*d**5)*z**2+(3-72*d+504*d**2-1344*d**3+1008*d**4)*z**3
    rr=S.Poly(S.resultant(Fbar,G,z),d,domain=S.QQ)
    den,RR=rr.clear_denoms()
    assert den%P
    EE=S.Poly(E,d,modulus=P)
    assert EE.degree()==6
    assert EE.gcd(RR.set_modulus(P)).degree()==0
    print('Endpoint: resultant mod E after denominator clearing, descending coefficients:')
    print(RR.set_modulus(P).rem(EE).all_coeffs())
    print('PASS: gcd(E, Res_z(Fbar,G))=1 mod 101.')

def derive_h48():
    x,h,u,v,L=S.symbols('x h u v ell')
    variables=(h,u,v,L)
    P0=lambda x:3*h*h-6*x*x
    P1=lambda x:3*h*x-4*x*x
    D=2*u-3*v+1
    def FF(PP):return (1-u)*D*J3(v)*PP(u)-(1-v)**2*J3(u)*PP(v)
    F0,F1=FF(P0),FF(P1)
    r=2-L-h-u-v
    def G(P):
        dn=3*r*r+(2-4*u-4*v)*r+1-2*u-2*v+6*u*v
        ell=4*u*u-5*u*v+2*v-1-3*(u-v)*r
        return D*(1-r)*P(r)*J3(v)*dn+(1-v)**2*P(v)*J3(r)*ell
    j=14*J3(v)*h*(u-v)*(v-r)*D*(u-r)*S.Rational(3,196)
    K=S.Poly(F0*G(P1)-F1*G(P0),*variables,domain=S.QQ).exquo(S.Poly(j,*variables,domain=S.QQ))
    assert K.total_degree()==8
    q4=J4(x)+L*J3(x)
    q3=S.div(q4,x-h,x)[0]
    q2=S.div(q3,x-u,x)[0]
    rings=[(v,q2.subs(x,v),(h,u,L)),(u,q3.subs(x,u),(h,L)),(h,q4.subs(x,h),(L,))]
    def rem(v,w,a):
        ring=S.QQ.poly_ring(*a)
        return lambda f:S.Poly(f,v,domain=ring).rem(S.Poly(w,v,domain=ring)).as_expr()
    def norm(expr,var,mod,tail):
        rfn=rem(var,mod,tail)
        deg=int(S.degree(mod,var))
        ring=S.QQ.poly_ring(*tail)
        cols=[S.Poly(rfn(expr*var**i),var,domain=ring) for i in range(deg)]
        M=[[ring.from_sympy(cols[j].nth(i)) for j in range(deg)] for i in range(deg)]
        out=ring.zero
        for p in permutations(range(deg)):
            inv=sum(p[i]>p[j] for i in range(deg) for j in range(i+1,deg))
            out+=(-1)**inv*prod((M[i][p[i]] for i in range(deg)),start=ring.one)
        return ring.to_sympy(out)
    f=K.as_expr()
    for i,(v0,m0,r0) in enumerate(rings):
        for j in range(i,len(rings)):
            vj,mj,rj=rings[j]
            others=tuple(p for p in tuple(t[0] for t in rings[i:])+(L,) if p!=vj)
            f=rem(vj,mj,others)(f)
        f=norm(f,v0,m0,r0)
        f=S.Poly(f,*r0,domain=S.QQ).clear_denoms(convert=True)[1].primitive()[1]
        f=(-f if f.LC()<0 else f).as_expr()
    H=S.Poly(f,L).all_coeffs()
    assert len(H)==49
    return [int(k) for k in H]


if __name__=='__main__':
    H=derive_h48()
    if len(sys.argv)>1:
        data=json.loads((Path(sys.argv[1])/'data/real_certificate.json').read_text())
        assert H==data['H48_coefficients_descending']
        print('H48 independently derived and matched original coefficients.')
    main_atlas(H)
    radau()
    endpoint()
