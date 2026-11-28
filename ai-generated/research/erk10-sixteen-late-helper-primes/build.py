#!/usr/bin/env python3
"""Exact guarded late-helper ERK10 constructor over arbitrary powers of five primes."""
from functools import cache
from fractions import Fraction as Q
from math import prod
from pathlib import Path
from argparse import ArgumentParser
from collections import defaultdict
import json,sys
from rooted import trees,order,tf
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'erk10-late-helper'))
import replay as poly

class R:
    __slots__=('v',)
    p=29
    m=29
    def __init__(self,v):
        if isinstance(v,R):
            self.v=v.v
        else:
            q=Q(v)
            self.v=q.numerator*pow(q.denominator,-1,self.m)%self.m
    def __int__(self):
        return self.v
    def __bool__(self):
        return self.v!=0
    def __eq__(self,n):
        return self.v==R(n).v
    def __hash__(self):
        return hash(self.v)
    def __repr__(self):
        return str(self.v)
    def __neg__(self):
        return R(-self.v)
    def __pow__(self,k):
        return R(pow(self.v,k,self.m))
    def __add__(self,n):
        return R(self.v+R(n).v)
    __radd__=__add__
    def __sub__(self,n):
        return R(self.v-R(n).v)
    def __rsub__(self,n):
        return R(R(n).v-self.v)
    def __mul__(self,n):
        return R(self.v*R(n).v)
    __rmul__=__mul__
    def __truediv__(self,n):
        rhs=R(n)
        assert unit(rhs,R.p),('nonunit divide',self,rhs)
        return R(self.v*pow(rhs.v,-1,self.m))
    def __rtruediv__(self,n):
        return R(n)/self

def red(q,p):
    q=Q(q)
    return q.numerator*pow(q.denominator,-1,p)%p

def unit(a,p):
    if isinstance(a,R):
        return a.v%p!=0
    return red(a,p)!=0

def dot(a,b):
    return sum(u*v for u,v in zip(a,b))

def solve(A,b,n,p,audit,tag):
    coerce=R if any(isinstance(a,R)for rr in A for a in rr) else Q
    rows=[[coerce(v) for v in (*a,c)] for a,c in zip(A,b)]
    piv=[]
    for j in range(n):
        k=next((k for k in range(len(piv),len(rows))if unit(rows[k][j],p)),None)
        if k is None:
            continue
        l=len(piv);rows[l],rows[k]=rows[k],rows[l]
        v=rows[l][j]
        audit[tag].append(int(v)%p if isinstance(v,R)else red(v,p))
        rows[l]=[x/v for x in rows[l]]
        for i in range(l+1,len(rows)):
            t=rows[i][j]
            rows[i]=[a-t*b for a,b in zip(rows[i],rows[l])]
        piv.append(j)
    assert len(piv)==n,(tag,'lost unit rank',p)
    ans=[0]*n
    for i in reversed(range(n)):
        j=piv[i]
        r=rows[i]
        ans[j]=r[n]-dot(r[j+1:n],ans[j+1:n])
    assert all(dot(r,ans)==v for r,v in zip(A,b)),(tag,'inconsistent',p)
    return ans

def prefix(theta,p,audit):
    v=theta*(12*theta**2-45*theta+40)/(15*(theta-2)**2)
    # Literal doubled old donor clocks v,v; the general formulas simplify here.
    A=[[],[Q(2,3)],[Q(1,4),Q(3,4)],[Q(1),Q(-3),Q(4)],[Q(-1),Q(6),Q(-4),Q(1)],
       [v*(4*v*v-13*v+12)/12,-3*v*v*(v-2)/4,v*v*(v-1)/3,
        -v*v*(v-3)*(v-1)/12,v*v*(v-2)*(v-1)/12],
       [(4*v**3-27*v*v+38*v-12)/12,-3*v*(v*v-6*v+4)/4,v*(v*v-6*v+2)/3,
        -v*(v-1)*(v*v-6*v+6)/12,v*(v-4)*(v-1)**2/12,Q(1)]]
    @cache
    def phi(t):
        z=[act(u) for u in t]
        return tuple(prod(v[i] for v in z) for i in range(len(A)))
    @cache
    def act(t):
        return tuple(dot(row,phi(t))for row in A)
    lev=[(t,k,tf(t))for k in range(1,6)for t in trees(k)]
    A.append(solve([phi(t)for t,k,d in lev],[theta**k/d for t,k,d in lev],7,p,audit,'old endpoint'))
    phi.cache_clear();act.cache_clear()
    assert all(phi(t)[7]==Q(k,d)*theta**(k-1)for k in range(1,7)for t in trees(k)for d in (tf(t),))
    mat=[phi(t)for t,k,d in lev]
    Pi=[solve(mat,[Q(k,d)if k==j+1 else Q(0)for t,k,d in lev],8,p,audit,'decoder') for j in range(5)]
    assert Pi[0]==[Q(1)]+[Q(0)]*7
    assert [sum(Pi[j][i]*theta**(j+1)/(j+1)for j in range(5))for i in range(8)]==A[-1]+[Q(0)]
    tails=[[-dot(row,phi(t))for row in Pi]+[Q(6,tf(t))]for t in trees(6)]
    lam=v**3*(3*v*v-15*v+20)/16
    assert all(not r[0]and not poly.ev(r,theta)and poly.ev(r,v)==lam*poly.ev(r,Q(2))for r in tails)
    basis={}
    for r in tails:
        vv=r.copy()
        for j in sorted(basis):
            vv=[x-vv[j]*y for x,y in zip(vv,basis[j])]
        if any(vv):
            k=next((i for i,a in enumerate(vv)if unit(a,p)),None)
            if k is None:
                continue
            t=vv[k]
            audit['degree-six basis'].append(red(t,p))
            basis[k]=[x/t for x in vv]
    assert len(basis)==3
    for r in tails:
        for j in sorted(basis):
            r=[x-r[j]*y for x,y in zip(r,basis[j])]
        assert not any(r),(theta,'rank-six span')
    H=list(basis.values())
    assert all(x.denominator%p for row in A+Pi+H for x in row)
    return A,Pi,H

def quarter(theta,d,e,xi,z,p,n):
    # Hensel for the normalized terminal quadratic in the remaining donor.
    q=[poly.ev(v,theta)for v in poly.quadratic(*map(Q,(d,e,xi)))]
    pol=[red(a,p**n)for a in q]
    val=lambda c:pol[0]+c*(pol[1]+c*pol[2])
    der=(pol[1]+2*z*pol[2])%p
    assert not val(z)%p and der
    for k in range(1,n):
        m=p**k
        assert not val(z)%m
        z+=m*(-(val(z)//m)*pow(der,-1,p)%p)
    assert not val(z)%(p**n)
    return z,der,tuple(red(a,p)for a in q)

def pair(d,e,xi,z,a0,b0,p,n,audit):
    # Exact two nodal moments give the monic early pair when Delta is a unit.
    H=poly.hull(tuple(map(Q,(0,1,d,e,xi))))
    m=[R(poly.mu(H,j+1))-R(z)*R(poly.mu(H,j))for j in range(4)]
    m0,m1,m2,m3=m
    Delta=m0*m2-m1*m1
    assert unit(Delta,p)
    s=(m0*m3-m1*m2)/Delta
    v=(m1*m3-m2*m2)/Delta
    disc=s*s-4*v
    assert unit(disc,p)and disc.v%p==(a0-b0)**2%p
    for j in (0,1):
        assert not (m[j+2]-s*m[j+1]+v*m[j])
    def branch(a0):
        d=(2*a0-s.v)%p
        assert d and not ((a0*a0-s.v*a0+v.v)%p)
        a=a0
        for k in range(1,n):
            P=p**k
            wr=a*a-s.v*a+v.v
            assert not wr%P
            a+=P*(-(wr//P)*pow(d,-1,p)%p)
        a=R(a)
        assert not (a*a-s*a+v)
        return a,d
    a,da=branch(a0)
    b,db=branch(b0)
    assert a+b==s and a*b==v and a!=b and (da+db)%p==0
    audit['Delta, discriminant, two root derivatives']=[Delta.v%p,disc.v%p,da,db]
    return a,b

def ringhull(nodes):
    out=[R(1)]
    for x in nodes:
        r=[R(0)]*(len(out)+1)
        for j,v in enumerate(out):
            r[j]-=x*v
            r[j+1]+=v
        out=r
    return out

def moments(nodes):
    # Eight Lagrange cardinal integrals, validated through precision nine.
    W={};U={}
    for x in nodes:
        remainder=tuple(y for y in nodes if y!=x)
        assert len(remainder)==7 and all(unit(x-y,R.p)for y in remainder)
        M=U[x]=sum(x/(j+1)for j,x in enumerate(ringhull(remainder)))
        W[x]=M/prod(x-y for y in remainder)
        assert unit(W[x],R.p)
    assert all(sum(W[x]*x**j for x in nodes)==R(1)/(j+1)for j in range(10))
    return W,U

def reverse(raw,W,prefix0,theta,p,audit):
    Z=R(0);O=R(1)
    a,b=raw[2:4];q,p0=1-b,1-a
    w=[W.get(x,Z)for x in raw];assert w[4]==0
    y=[1-x for x in raw]
    Md=[[v*x**j for x,v in zip(y,w)]for j in range(5)]
    U=[Z]*9;U[1]=-w[1]/2
    xs=raw[2:]
    V=[Z,Z]+[O/(x*prod(x-v for v in xs if x!=v))for x in xs]
    V=[v/V[2]for v in V]
    for i in range(1,7):
        assert not sum(v*x**i for v,x in zip(V,raw))
    G=[2*u/3+(w[2]*p0**2/2-w[2]*p0**3/3)*v for u,v in zip(U,V)]
    H=[-w[2]*p0**2/4*v for v in V]
    reads=[*Md[:3],U]
    goals=[[Md[1][i],Md[2][i]/2+U[i],Md[3][i]/3+G[i],H[i]]for i in range(9)]
    K=[[Z]*9 for _ in range(9)]
    for i in range(1,9):
        k=min(i,4)
        K[i][:k]=solve([r[:k]for r in reads[:k]],goals[i][:k],k,p,audit,'initial donors')
        assert [dot(K[i],r)for r in reads]==goals[i]
    dd=solve([r[:4]for r in reads],[-r[5]for r in reads],4,p,audit,'compensated donor')+[Z,O,Z,Z,Z]
    amp=dot(dd,Md[3])
    assert unit(amp,p)
    A,Pi,H6=prefix0
    scale=raw[-1]/theta
    A=[[R(x)*scale for x in row]for row in A]
    Pi=[[R(x)/scale**k for x in row]for k,row in enumerate(Pi)]
    H6=[[R(x)/scale**k for k,x in enumerate(row)]for row in H6]
    tests=[[poly.ev(row,x)for x in raw]for row in H6]
    kvec=lambda:[dot(r,Md[3])-Md[4][i]/4 for i,r in enumerate(K)]
    sol=solve([[row[j]*amp for j in (6,7)]for row in tests],
              [-dot(row,kvec())for row in tests],2,p,audit,'terminal cubic')
    for i,t in zip((6,7),sol):
        K[i]=[a+t*b for a,b in zip(K[i],dd)]
    vh=lambda:[dot(r,V)for r in K]
    sol=solve([[row[j]*V[4]for j in (5,6,7)]for row in tests],
              [-dot(row,vh())for row in tests],3,p,audit,'terminal cofactor')
    for i,t in zip((5,6,7),sol):
        K[i][4]+=t
    assert all(not dot(row,kvec())and not dot(row,vh())for row in tests)
    assert all([dot(r,q)for q in reads]==s and not any(r[i:])for i,(r,s) in enumerate(zip(K,goals)))
    return K,A,Pi,w

def make(data,n,do_audit=False):
    p=data['field'];R.p=p;R.m=p**n
    a0,b0,h0,z0,d,e,xi=data['raw'][2:]
    theta=Q(data['theta'])
    audit=defaultdict(list)
    z,der,cfs=quarter(theta,d,e,xi,z0,p,n)
    assert der==data['pressure_simple_derivative']
    audit['pressure coefficients and derivative']=[*cfs,der]
    a,b=pair(d,e,xi,z,a0,b0,p,n,audit)
    Z=R(0);O=R(1)
    z,d,e,xi=map(R,(z,d,e,xi))
    W,mu=moments((Z,O,a,b,z,d,e,xi))
    l0=(1-a)**2*mu[a]
    l1=(1-b)*(3*(1-a)-2*(1-b))*mu[b]
    assert unit(l1-l0,p)
    h=(l1*b-l0*a)/(l1-l0)
    audit['helper denominator']=[int(l1-l0)%p]
    raw=(O,Z,a,b,h,z,d,e,xi)
    assert tuple(int(x)%p for x in raw)==tuple(data['raw'])
    assert len({int(x)%p for x in raw})==9
    P=prefix(theta,p,audit)
    K,A,Pi,w=reverse(raw,W,P,theta,p,audit)
    C=raw[::-1]
    B=[[K[8-j][8-i]if j<i else Z for j in range(9)]for i in range(9)]
    for i,(x,r) in enumerate(zip(C,B)):
        d0=[x**(k+1)/(k+1)-dot(r,[v**k for v in C])for k in range(5)]
        old=[dot(d0,[v[j]for v in Pi])for j in range(8)]
        if i==0:
            assert old==A[7]+[Z]
        else:
            old[7]+=r[0]
            A.append(old+r[1:i])
    b=[W[Z]-w[1]]+[Z]*6+w[::-1]
    assert len(A)==len(b)==16 and all(len(r)==i for i,r in enumerate(A))
    assert tuple(map(sum,A))[8:]==C[1:]
    a,bb=[list(map(int,r))for r in A],list(map(int,b))
    defect=(11*sum(w*pow(sum(r),10,R.m)for r,w in zip(a,bb))-1)%R.m
    assert defect%p==data['next_failure_value']
    if do_audit:
        print(p,'pressure',audit['pressure coefficients and derivative'],'pair',audit['Delta, discriminant, two root derivatives'],
                'helper denominator',audit['helper denominator'],'unit pivots',dict((k,v)for k,v in audit.items()if k in ('old endpoint','degree-six basis','terminal cubic','terminal cofactor')),'bush',defect)
    return {'field':p,'exponent':n,'modulus':R.m,'A':a,'b':bb,
            'raw':list(map(int,raw)),'theta':str(theta),'next_failure_tree':[[]]*10,'next_failure_value':defect}

def main():
    ap=ArgumentParser(description=__doc__)
    ap.add_argument('--emit',type=Path,default=HERE/'literals')
    ap.add_argument('--exponent',type=int,default=3)
    ap.add_argument('--primes',nargs='*',type=int)
    ap.add_argument('--check-inputs',type=Path)
    opt=ap.parse_args()
    opt.emit.mkdir(parents=True,exist_ok=True)
    for d in json.loads((HERE/'seeds.json').read_text()):
        p=d['field']
        if opt.primes and p not in opt.primes:
            continue
        for k in range(1,opt.exponent+1):
            J=make(d,k,k==1)
            if k==1 and opt.check_inputs:
                old=json.loads((opt.check_inputs/f'late-helper-f{p}.json').read_text())
                assert J['A']==old['A'] and J['b']==old['b']
            (opt.emit/f'f{p}-power{k}.json').write_text(json.dumps(J,indent=2)+'\n')
if __name__=='__main__':
    main()
