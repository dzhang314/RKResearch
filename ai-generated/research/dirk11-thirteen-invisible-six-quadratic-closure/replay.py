#!/usr/bin/env python3
"""Exact α=0 quadratic closure. Rational eliminants, then local-ring unit tests."""
from runpy import run_path
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import argparse
import sympy as S

here=Path(__file__).resolve().parent
ap=argparse.ArgumentParser()
ap.add_argument("--quadratic",type=Path,
    default=here.parent/"dirk11-thirteen-invisible-six-quadratic"/"replay.py")
ap.add_argument("--arithmetic",type=Path,
    default=here.parent/"dirk11-thirteen-invisible-six-constant-exclusion"/"replay.py")
args=ap.parse_args()
d=run_path(str(args.quadratic))
c=run_path(str(args.arithmetic))
Ring,quot=c['Ring'],c['quot']
b,q,t,x=[d[v] for v in ('b','q','t','x')]
j4,j5=d['J4'],d['J5']
g,l,carrier=d['RG'],d['ls'],d['pols']
rat,take=d['rat'],d['take']
F7=3150*b**7-11970*b**6+18669*b**5-15429*b**4+7254*b**3-1916*b**2+255*b-12
E=S.Poly(F7,b,domain=S.QQ).monic()
assert E.is_irreducible
assert S.expand(S.Poly(g,q).LC()-2250000*j4(b)**3)==0
strip=lambda z:S.cancel(z/S.gcd(z,b**50*q**50*(10*q+3)**20))
l1=strip(l.nth(1))
cc=S.cancel(S.resultant(g,l1,q)/(b**44*j4(b)**6*F7**2))
assert cc.is_number and cc!=0
la=S.symbols('lambda')
H=x*j4(x); IH=d['If'](H)
assert S.expand(IH-H*(-x/5+7*(1-la)/60)-S.Rational(77,660)*x*(j5(x)+la*j4(x)))==0
K=S.QQ.algebraic_field((E,b))
def numberpoly(f,j):
    return S.Poly.from_list([
        K([S.QQ.from_sympy(a)for a in S.Poly(co,b,domain=S.QQ).rem(E).all_coeffs()])
        for co in S.Poly(f,j).all_coeffs()],j,domain=K)
G,L0,L1=[numberpoly(f,q) for f in (g,l.nth(0),l.nth(1))]
piv=S.gcd(G,S.gcd(L0,L1)).monic()
assert piv.degree()==1
q_pivot=-piv.nth(0)
u0,u1=[numberpoly(f.subs(q,q_pivot),t) for f in carrier]
t_pivot=S.gcd(u0,u1).monic()
assert t_pivot.degree()==2
G7=G.monic()
for _ in range(2):
    cp=S.gcd(G7,L1).monic()
    assert cp==piv
    G7=G7.exquo(cp).monic()
assert G7.degree()==4 and S.gcd(G7,L1).degree()==0

# The new forward split, computed exactly over Q(b)[q]/Gamma.
z=S.symbols('z')
P4=S.Poly(S.cancel((j4(b)*j5(z)-j5(b)*j4(z))/(z-b)),z)
D=S.QQ.frac_field(b)
P=lambda u:S.Poly(u,q,domain=D)
G0=P(g).monic()
mul=lambda a,b:(a*b).rem(G0)
def times(a,n):
    z=P(1)
    for _ in range(n):z=mul(z,a)
    return z
n0,n1=l.nth(0),l.nth(1)
co=S.gcd(n0,n1)
L01=P(S.cancel(n1/co))
Linv=S.invert(L01,G0)
assert mul(Linv,L01)==P(1)
tt=mul(-P(S.cancel(n0/co)),Linv)
qinv=S.invert(P(q),G0)
assert mul(P(q),qinv)==P(1)
ss=mul(mul(tt,tt),P(42*b)*(P(1)+mul(P(S.Rational(3,10)),qinv)))+tt*P(-14+1/b)
def red(coeffs):
    c,d=P(0),P(0)
    for j in reversed(coeffs):
        c,d=P(j)-mul(d,tt),c-mul(d,ss)
    return c,d
a0,a1=red([S.Poly(j4(z),z).nth(i) for i in range(5)])
b0,b1=red([P4.nth(i) for i in range(5)])
gate_rem=mul(a0,b1)-mul(a1,b0)
a2=mul(tt,P(42*b*(S.Rational(1,5)-q))); a3=P(-q)
gate_diag=sum((mul(times(a3,i),times(a2,4-i))*P(P4.nth(i)) for i in range(5)),P(0))
cases=[]
for name,test,expect in [
    ('remainder',gate_rem,[(2,1),(3,2),(3,3),(12,1)]),
    ('zero diagonal',gate_diag,[(60,1)])
]:
    den,num=test.clear_denoms(convert=True)
    assert all(S.rem(b*j4(b)*F7,f,b)==0 for f,_ in S.factor_list(den,b)[1])
    seq=S.subresultants(g,num.as_expr(),q)
    linear=S.Poly(seq[-2],q)
    assert linear.degree()==1
    factors=S.factor_list(seq[-1],b)[1]
    kept=[]
    for f,m in factors:
        if S.rem(b*j4(b)*F7*(2*b-1),f,b)==0:
            continue
        R=S.Poly(f,b,domain=S.QQ)
        data=[S.Poly(linear.nth(i),b,domain=S.QQ).rem(R).as_expr() for i in range(2)]
        assert data[1]!=0
        kept.append((R.degree(),m))
        cases.append((name,R,m,*data))
    assert sorted(kept)==expect
    print(name,"exact non-guard factors (degree,multiplicity):",sorted(kept),flush=True)

def ev(cs,x):
    out=x.r.to(0)
    for a in reversed(cs):out=out*x+a
    return out

def peval(f,x):
    return ev([rat(a) for a in reversed(S.Poly(f,b,domain=S.QQ).all_coeffs())],x)

def reflect_coeff(fs,n):
    return [sum(((-1)**(n+j))*comb(k,j)*fs[k] for k in range(j,n+1)) for j in range(n+1)]

def symmetric_marks(A0,aa,ss,tt,ell,mu,remf):
    old=reflect_coeff(remf,3)
    assert old[-1]==1
    W=Ring("unordered v,u,w",A0,old[:-1])
    Y=W.gen(); A=1-aa
    U=lambda y:y*y+y*y.r.to(ss)+y.r.to(tt)
    m=j4(Y)/U(1-Y)
    k=A*j4(A)/U(aa)
    def qp(M,power):
        K3=[A0.to(0),*M.v]
        Ip=[A0.to(0),*(z/(i+1) for i,z in enumerate(K3))]
        r=(ev(Ip,Y)/ev(K3,Y)).v
        da=ell*aa+mu
        return r, ev(Ip,A)-k*ev(r,A)+da*(A**power*k-ev(K3,A))
    r0,d0=qp(m,0); r1,d1=qp(Y*m,1)
    return (r0[2],d0,d1),W.invs

def algebra(R,f):
    R0=S.Poly(f,b,domain=S.QQ)
    # Form the normalization with a checked residue inverse.
    leading=R.to(rat(R0.LC())).inv()
    return Ring('b',R,[R.to(rat(R0.nth(i)))*leading for i in range(R0.degree())])

def finish(name,bb,qq,tt=None,diag=False):
    B=bb.r
    qq.inv()
    if tt is None:
        (10*qq+3).inv()
        tt=-take(l.nth(0),bb,qq)/take(l.nth(1),bb,qq)
    tt.inv()
    ss=42*bb*tt*tt*(Q(3,10)+qq)/qq-14*tt+tt/bb
    ell=Q(1,5)-qq;mu=qq/(42*bb*tt)
    lam=-j5(bb)/j4(bb)
    p5=[(B.to(j)+lam*k)/132 for k,j in zip(*d['js'])]
    p4=quot(p5,bb)
    if diag:
        A0=B;aa=-mu/ell
    else:
        A0=Ring('second clean a',B,p4[:-1]);aa=A0.gen()
    remf=quot([A0.to(z) for z in p4],aa)
    rows,work=symmetric_marks(A0,aa,A0.to(ss),A0.to(tt),A0.to(ell),A0.to(mu),remf)
    sum(j*u for j,u in zip((1,2,3),rows)).inv()
    R=A0;deg=1;ledger=[work]
    while R is not None:
        if R.d:deg*=R.d
        ledger.append(R.invs); R=R.base
    print(name,"rank",deg,"unit; inverse-product counts base up plus transient",ledger[::-1],flush=True)

# Independently specialized one-sided cubic-leading-degree contacts.
def contact(p,c):
    pols=[S.Poly(f.subs(q,c),t).clear_denoms()[1].primitive()[1].as_expr() for f in carrier]
    steps=S.subresultants(*pols,t)
    degs=[S.degree(f,t) for f in pols]
    n=3 if c==-S.Rational(1,20) else 6
    assert degs==([1,3] if n==3 else [3,2])
    f=S.cancel(steps[-1]/b**(2 if n==3 else 4))
    assert S.degree(f,b)==n
    L=S.Poly(steps[-2],t)
    assert L.degree()==1
    B=algebra(Ring('F',prime=p),f); bb=B.gen()
    tt=-peval(L.nth(0),bb)/peval(L.nth(1),bb)
    finish(f"one-sided contact q={c}",bb,B.to(rat(c)),tt)

p=101
assert all(p%j for j in range(2,11))
for c0 in (S.Rational(-1,20),S.Rational(-2,15)):
    contact(p,c0)
B=algebra(Ring('F',prime=p),F7); bb=B.gen()
qq=peval(q_pivot,bb)
T=Ring('singular pivot t',B,[peval(t_pivot.nth(j),bb) for j in range(2)])
finish('degree-seven singular pivot',T.to(bb),T.to(qq),T.gen())
B=algebra(Ring('F',prime=p),F7); bb=B.gen()
Q7=Ring('regular q over pivot base',B,[peval(G7.nth(j),bb) for j in range(4)])
finish('degree-seven regular carrier',Q7.to(bb),Q7.gen())
for name,f,m,v0,v1 in cases:
    B=algebra(Ring('F',prime=p),f); bb=B.gen()
    qq=-peval(v0,bb)/peval(v1,bb)
    finish(f"{name} base {f.degree()} x{m}",bb,qq,diag=(name=='zero diagonal'))
print("All finite factors and pivot charts excluded. Previous q=-3/10 and b=1/2 packets close the remaining named branches.")
