#!/usr/bin/env python3
"""Exact symmetric first carrier projection, with no unordered clock division."""
import sympy as S
from functools import lru_cache
from math import comb
ss,pp,Y=S.symbols("s p Y")
Fpair=2*(2772*pp**4-5544*pp**3*ss+3864*pp**3+3696*pp*pp*ss*ss-4872*pp*pp*ss+1536*pp*pp-924*pp*ss**3+1692*pp*ss*ss-972*pp*ss+172*pp+66*ss**4-144*ss**3+108*ss*ss-32*ss+3)
aa,bb=S.symbols("a b")
J4s=lambda x:42*x**4-84*x**3+56*x*x-14*x+1
J5s=lambda x:(2*x-1)*(66*x**4-132*x**3+84*x*x-18*x+1)
assert S.expand((aa-bb)*Fpair.subs({ss:aa+bb,pp:aa*bb})-J5s(aa)*J4s(bb)+J5s(bb)*J4s(aa))==0
F=S.QQ.frac_field(ss)
poly=lambda x:S.Poly(x,pp,domain=F)
Fp=poly(Fpair).monic()
class E:
    def __init__(self,x=0):
        if isinstance(x,E):self.a=x.a
        elif isinstance(x,S.Poly):self.a=x.rem(Fp)
        else:self.a=poly(x).rem(Fp)
    def __add__(self,x):return E(self.a+E(x).a)
    __radd__=__add__
    def __neg__(self):return E(-self.a)
    def __sub__(self,x):return self+-E(x)
    def __rsub__(self,x):return -self+x
    def __mul__(self,x):return E(self.a*E(x).a)
    __rmul__=__mul__
    def __eq__(self,x):return self.a==E(x).a
    def inv(self):
        out=E(S.invert(self.a,Fp)); assert out*self==1
        return out
    def __truediv__(self,x):return self*E(x).inv()
    def __rtruediv__(self,x):return E(x)*self.inv()
    def __pow__(self,n):
        r=E(1)
        for _ in range(n):r=r*self
        return r
    def __repr__(self):return str(self.a.as_expr())

def trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def add(a,b):
    return trim([(a[i] if i<len(a) else E(0))+(b[i] if i<len(b) else E(0))
        for i in range(max(len(a),len(b)))])
def neg(a):return [-x for x in a]
def scale(a,f):return trim([f*x for x in a])
def mul(a,b):
    r=[E(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x==0:continue
        for j,y in enumerate(b):
            if y!=0:r[i+j]+=x*y
    return trim(r)
def divide(a,b):
    assert b[-1]==1
    a=list(a);n=len(b)-1;m=len(a)-n;out=[E(0)]*max(1,m)
    for j in range(m-1,-1,-1):
        out[j]=a[n+j]
        for k in range(n):a[j+k]-=out[j]*b[k]
    return trim(out),trim(a[:n] or [E(0)])
def rem(a,b):return divide(a,b)[1]
def prim(a):return [E(0),*[z*S.Rational(1,i+1) for i,z in enumerate(a)]]
def refl(a):
    n=len(a)-1
    return [sum(a[k]*(((-1)**(n+j))*comb(k,j))for k in range(j,n+1))
              for j in range(n+1)]
def det(M,plus,times,negative,zero):
    @lru_cache(None)
    def rec(i,mask):
        if i==len(M):return E(1) if isinstance(zero,E) else [E(1)]
        out=zero
        sign=1
        for j in range(len(M)):
            if not (mask>>j)&1:continue
            u=M[i][j]
            if u!=zero:
                w=times(u,rec(i+1,mask^(1<<j)))
                out=plus(out,w if sign==1 else negative(w))
            sign=-sign
        return out
    return rec(0,(1<<len(M))-1)
def sylv(a,b):
    assert len(a)<=4 and len(b)<=4
    a=a+[E(0)]*(4-len(a));b=b+[E(0)]*(4-len(b))
    M=[[E(0)]*3 for _ in range(3)]
    for i in range(1,4):
        for j in range(i):
            c=a[i]*b[j]-a[j]*b[i]
            for k in range(i-j):
                M[i-1-k][j+k]+=c
    return det(M,lambda a,b:a+b,lambda a,b:a*b,lambda a:-a,E(0))

# Pair quadratic, common Jacobi pencil, and the two old monic hulls.
uv=[E(pp),E(-ss),E(1)]
j4=[E(i)for i in (1,-14,56,-84,42)]
j5=[E(i)for i in (-1,20,-120,300,-330,132)]
H=[E(0),*j4]
def invpair(P):
    r=rem(P,uv);r += [E(0)]*(2-len(r));a,b=r
    norm=a*a+a*b*E(ss)+b*b*E(pp)
    Ni=norm.inv()
    return [(a+b*E(ss))*Ni,-b*Ni],norm
j4inv,guardj=invpair(j4)
Hinv,guardH=invpair(H)
lam=scale(rem(mul(j5,j4inv),uv),-1)
assert len(lam)==1
T5=scale(add(j5,scale(j4,lam[0])),S.Rational(1,132))
old,ev=divide(T5,uv)
assert ev==[E(0)]
S6=[E(0),*T5];R=refl(old)
print("old monic quotient built",flush=True)
F0=prim([E(0),E(0),E(pp),E(-ss),E(1)])
F1=neg(prim([E(0),E(pp),E(-ss),E(1)]))
L0=rem(mul(F0,Hinv),uv);L0 += [E(0)]*(2-len(L0))
L1=rem(mul(F1,Hinv),uv);L1 += [E(0)]*(2-len(L1))
ef=add(F0,[E(0),*F1]); ef=add(ef,neg(mul(H,[L0[0],L0[1]+L1[0],L1[1]])))
ef=add(ef,scale(mul([L0[1],L1[1]],S6),42))
AF,ex=divide(ef,[E(0),*uv]);assert ex==[E(0)]
print("F7 degree after clean-contact cancellation",len(AF)-1,flush=True)
A,B,C=S.gcdex(S.Poly(sum(x*Y**i for i,x in enumerate((1,-14,56,-84,42))),Y),
              S.Poly(sum(x*Y**i for i,x in enumerate((-1,20,-120,300,-330,132))),Y))
assert C.as_expr()==1
card=max(A.degree(),B.degree())
Uinv=rem([E(A.nth(i))+lam[0]*E(B.nth(i)) for i in range(card+1)],R)
assert rem(mul(j4,Uinv),R)==[E(1)]
V=[[E(1)+R[2]+R[1],E(1)+R[2],E(1)],[-2-R[2],E(-1),E(0)],[E(1),E(0),E(0)]]
M=[rem(mul(j4,f),R)for f in V]
def processed(P):
    # I P has factor Y; the actual inverse of YJ4 cancels its Y.
    return rem(mul(prim(P)[1:],Uinv),R)
def withPole(seq):
    cols=[]
    for j in range(len(seq)+1):
        f=rem(add(mul([E(1),E(-1)],seq[j] if j<len(seq) else [E(0)]),
                  neg(seq[j-1]) if j else [E(0)]),R)
        cols.append(f+[E(0)]*(3-len(f)))
    return [[v[i] for v in cols] for i in range(3)]
r0=withPole([processed([E(0),*m]) for m in M])
r1=withPole([processed([E(0),*rem([E(0),*m],R)]) for m in M])
w=withPole([processed([E(0),*R])])
affine_coordinate=trim(r0[2])
assert len(affine_coordinate)==4
assert scale(affine_coordinate,AF[-1])==scale(AF,affine_coordinate[-1])
collision=sylv(AF,old)
collision_norm,collision_den=S.cancel(S.resultant(Fp,collision.a)).as_numer_denom()
d0,d1,d2=r1[0],add(r1[1],neg(r0[0])),add(r1[2],neg(r0[1]))
c0,c1,c2=w
ghost=add(mul(add(mul(c2,d0),neg(mul(c0,d2))),add(mul(c2,d0),neg(mul(c0,d2)))),
        neg(mul(add(mul(c2,d1),neg(mul(c1,d2))),add(mul(c1,d0),neg(mul(c0,d1))))))
print("ghost quadratic determinant degree",len(ghost)-1,flush=True)
def clear(rows):
    D=S.Poly(1,ss,domain=S.QQ)
    for a in rows:
        for c in a.a.all_coeffs():
            D=D.lcm(S.Poly(c.as_numer_denom()[1],ss,domain=S.QQ))
    return [a*D.as_expr() for a in rows],D.as_expr()
AF,fa_den=clear(AF);ghost,det_den=clear(ghost)
print("cleared guard factors",S.factor(fa_den),S.factor(det_den),flush=True)
lead=AF[-1]
while len(ghost)>3:
    # Pseudo-reduce after clearing scalar denominators.
    ghost=add(scale(ghost,lead),neg([E(0)]*(len(ghost)-4)+scale(AF,ghost[-1])))

f=sylv(AF,ghost)
s,p=ss,pp
PD=S.QQ[s]
Ps=lambda x:S.Poly(x,s,domain=S.QQ)
Pp=lambda x:S.Poly(x,p,domain=PD)
monic=Pp(Fpair).monic()
def vec(z):return [Ps(z.nth(i))for i in range(4)]
def mat(f):
    return list(map(list,zip(*(vec((f*Pp(p**j)).rem(monic))for j in range(4)))))
from itertools import permutations
def dets(M):
    n=len(M);s0=Ps(0)
    for perm in permutations(range(n)):
        co=(-1)**sum(perm[i]>perm[j] for i in range(n)for j in range(i+1,n))
        a=Ps(co)
        for i,j in enumerate(perm):a*=M[i][j]
        s0+=a
    return s0
EJ=63*s**4-252*s**3+357*s*s-210*s+43
EH=66*s**4-144*s**3+108*s*s-32*s+3
guards0=(s-1)*EJ

assert all(Ps(guards0).rem(Ps(e)).is_zero for d in (fa_den,det_den)
           for e,_ in S.factor_list(d,s)[1])
assert all(Ps(guards0*EH).rem(Ps(e)).is_zero
           for e,_ in S.factor_list(collision_den,s)[1])
nh=Ps(S.cancel(S.resultant(Fp,guardH.a)).as_numer_denom()[0])
assert Ps(S.expand((s-1)**4*EJ**2*EH)).monic()==nh.monic()
ml=mat(Pp(AF[-1].a.as_expr()));nl=dets(ml)
factors=S.factor_list(nl.as_expr(),s)[1]
assert sorted((S.degree(f,s),m)for f,m in factors)==[(1,4),(4,6),(12,1)]
LEAD12=next(f for f,m in factors if S.degree(f,s)==12)
assert nl.monic()==Ps((s-1)**4*EJ**6*LEAD12).monic()
print("Exact clock guards and leader norm passed",flush=True)
adj=[[(-1)**(i+j)*dets([[ml[r][c]for c in range(4)if c!=i]for r in range(4)if r!=j])
      for j in range(4)]for i in range(4)]
v=vec(Pp(f.a.as_expr()))
for _ in range(13):
    v=[sum((a*b for a,b in zip(row,v)),Ps(0)).exquo(nl)for row in adj]
print("Thirteen exact polynomial leader divisions passed",flush=True)
content=v[0]
for a in v[1:]: content=content.gcd(a)
assert content.monic()==Ps(guards0**20).monic()
projected=Pp(sum(a.exquo(content).as_expr()*p**i for i,a in enumerate(v)))
norm=dets(mat(projected))
outside=nl*Ps(guards0*EH)
while True:
    g=norm.gcd(outside)
    if g.degree()==0: break
    norm=norm.exquo(g)
sfactors=S.factor_list(norm.as_expr(),s)[1]
assert sorted((S.degree(f,s),m) for f,m in sfactors)==[(6,6),(30,2),(42,2)]
F30=next(f for f,m in sfactors if S.degree(f,s)==30)
assert Ps(collision_norm).monic()==Ps(F30).monic()
assert Ps(collision_norm).degree()==30 and Ps(F30).gcd(outside).degree()==0
print("Exact regular factors: degrees 6,30,42; the old-clock collision norm is the degree-30 factor.",flush=True)

def sum_one_check():
    """Direct coefficient audit on the symmetry fiber, no generic division."""
    global Fp,poly
    saved=(Fp,poly)
    try:
        Fp=S.Poly(66*p*p-18*p+1,p,domain=S.QQ).monic()
        poly=lambda z:S.Poly(z,p,domain=S.QQ)
        q=[E(p),E(-1),E(1)]
        h4=[E(j)for j in (1,-14,56,-84,42)]
        h=[E(0),*h4]
        j=[E(k)for k in (-1,20,-120,300,-330,132)]
        assert rem(j,q)==[E(0)]
        m,n=rem(h,q)
        k=(m*m+m*n+E(p)*n*n).inv()
        ih=[(m+n)*k,-n*k]
        f0=prim([E(0),E(0),*q])
        f1=neg(prim([E(0),*q]))
        a=rem(mul(f0,ih),q); b=rem(mul(f1,ih),q)
        assert len(a)==len(b)==2
        d=add(f0,[E(0),*f1])
        d=add(d,neg(mul(h,[a[0],a[1]+b[0],b[1]])))
        d=add(d,scale(mul([a[1],b[1]],[E(0),*scale(j,S.Rational(1,132))]),42))
        A,Z=divide(d,[E(0),*q])
        assert Z==[E(0)] and len(A)==4
        A=scale(A,A[-1].inv())
        expected=[E(p)-S.Rational(41,231),E(p)*S.Rational(5,7)+S.Rational(142,231),
                  -E(p)*S.Rational(4,7)-S.Rational(106,77),E(1)]
        assert A==expected
    finally:
        Fp,poly=saved
sum_one_check()
print("Exact sum-one cubic passed",flush=True)
