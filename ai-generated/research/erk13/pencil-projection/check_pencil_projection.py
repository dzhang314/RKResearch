#!/usr/bin/env python3
"""Two fixed-Sylvester ERK13 marked pencil certificates. Python standard library.

Nothing is sampled numerically. Integer resultants use exact interpolation *within
proved degree bounds*; polynomial identities in Fp[z] use a sufficiently large p.
Every determinant, including those at degree-dropping fibers, uses the fixed size.
"""
from math import factorial, gcd
from functools import reduce
import argparse, json

F = (-1, 20, -120, 300, -330, 132, 0)
J = (7, -168, 1260, -4200, 6930, -5544, 1716)


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def add(a, b):
    return trim([(a[i] if i < len(a) else 0)+(b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])


def multiply(a, b):
    if not a or not b: return []
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): c[i+j] += x*y
    return trim(c)


def ev(a, x, p=0):
    y = 0
    for c in reversed(a):
        y = y*x+c
        if p: y %= p
    return y


def interp(vals, p=0):
    """Reconstruct an (integer coefficient, if p=0) polynomial at 0,1,... ."""
    v, out, basis, f, k = list(vals), [], [1], 1, 0
    while v:
        if p:
            lead = v[0] * pow(f, -1, p) % p
        else:
            lead, rem = divmod(v[0], f)
            assert rem == 0, (k, 'nonintegral monomial coefficient')
        if lead:
            out = add(out, [lead * b for b in basis])
            if p: out = trim([b % p for b in out])
        v = [b-a for a,b in zip(v,v[1:])]
        if p: v = [x%p for x in v]
        if not any(v): break
        basis = multiply(basis, [-k,1]); k += 1; f *= k
        if p: basis, f = [x%p for x in basis], f%p
    return out


def det(a, p=0):
    """Gaussian elimination mod p; fraction-free Bareiss over Z."""
    n = len(a)
    if n == 0: return 1
    a = [list(row) for row in a]; sign = last = 1
    if p:
        for i in range(n):
            j=next((j for j in range(i,n) if a[j][i]%p),None)
            if j is None: return 0
            if i != j: a[i], a[j], sign = a[j], a[i], -sign
            pv=a[i][i]%p; inv=pow(pv,-1,p); last=last*pv%p
            for j in range(i+1,n):
                f=a[j][i]*inv%p
                if f:
                    for k in range(i+1,n): a[j][k]=(a[j][k]-f*a[i][k])%p
        return last*sign%p
    for i in range(n-1):
        j=next((j for j in range(i,n) if a[j][i]),None)
        if j is None: return 0
        if i != j: a[i], a[j], sign = a[j], a[i], -sign
        pv = a[i][i]
        for j in range(i+1,n):
            for k in range(i+1,n):
                a[j][k], rem = divmod(pv*a[j][k]-a[j][i]*a[i][k], last)
                assert not rem
        last = pv
    return sign*a[-1][-1]


def res(f,g,m,n,p=0):
    """Transpose of Mathlib's fixed-degree Sylvester (g-columns then f-columns)."""
    f,g=trim(f),trim(g)
    assert len(f)<=m+1 and len(g)<=n+1
    a=[]
    for h, repeats in ((g,m),(f,n)):
        for k in range(repeats): a.append([0]*k+h+[0]*(m+n-k-len(h)))
    return det(a,p)


def reduce_mod(a,b,p):
    a=trim([x%p for x in a]); b=trim([x%p for x in b]); assert b
    bi=pow(b[-1],-1,p)
    while len(a)>=len(b):
        k=len(a)-len(b); q=a[-1]*bi%p
        for j,x in enumerate(b): a[k+j]=(a[k+j]-q*x)%p
        a=trim(a)
    return a


def gcd_mod(a,b,p):
    a,b=trim([x%p for x in a]),trim([x%p for x in b]); degrees=[]
    while b:
        degrees.append(len(b)-1); a,b=b,reduce_mod(a,b,p)
    ai=pow(a[-1],-1,p)
    return trim([x*ai%p for x in a]), degrees


def quot_x_minus_one(h):
    # H(1)=0. The tail sums are the quotient's coefficients.
    assert sum(h)==0
    return trim([sum(h[k+1:]) for k in range(len(h)-1)])


D=multiply([-2,5],[-6,7]); N=[210,-672,819,-460,100]
CIS=[quot_x_minus_one(add([0]*i+D,[0]*3+N)) for i in range(7)]
assert max(map(len,CIS[:6]))-1==6 and max(map(len,CIS))-1==7


def cubic_pair(z):
    ci=[ev(c,z) for c in CIS]
    return [F[i]*ci[i] for i in range(6)], [(J[i]+7*F[i])*ci[i] for i in range(1,7)]


def inner_cubic(t,z,p):
    ft,jt=ev(F,t,p),ev(J,t,p)
    H=[pow(t,i,p)*(J[i]*ft-F[i]*jt)%p for i in range(7)]
    P=[12*z-15*z*z,60*z*z-24*z-18,-10*(5*z*z+4*z-6),15*(4*z-3)]
    return res(H,P,6,3,p)


def quartic_forms(t,z):
    ft,jt=ev(F,t),ev(J,t); h=[J[i]*ft-F[i]*jt for i in range(7)]
    # W = the monic quotient of H(X) by (X-1)(X-z), divided by t².
    w=[0]*7
    for i in range(4,-1,-1): w[i]=t**i*h[i+2]+(1+z)*w[i+1]-z*w[i+2]
    m=sum(t**(i-1)*h[i]*sum(z**j for j in range(i)) for i in range(1,7))
    a=sum(420//(i+2)*w[i] for i in range(5))
    b=ev(F,t*z)*sum(420//(i+3)*w[i] for i in range(5))-ft*sum(
        (420//(i+3)*z**(i+2)-420//(i+2)*z**(i+1))*w[i] for i in range(5))
    return a,m,b


def primitive(a):
    c=reduce(gcd,map(abs,a),0); assert c
    if a[-1]<0: c=-c
    return [x//c for x in a],c


def run(name,p):
    assert p>258 and all(p%k for k in range(2,int(p**.5)+1))
    if name=='cubic':
        # R has degree ≤ 5*6 + 5*7 = 65.  Q has bidegree ≤(33,12).
        # T has z degree ≤ 33*6 + 5*12 = 258.
        vals=[res(*cubic_pair(z),5,5) for z in range(66)]
        raw=interp(vals); assert len(raw)==66 and raw[:15]==[0]*15 and raw[15]
        r,content=primitive(raw[15:]); assert len(r)==51
        def t_at(z):
            q=interp([inner_cubic(t,z,p) for t in range(34)],p)
            return res(cubic_pair(z)[0],q,5,33,p)
        tbound=258
    else:
        # A,M,B have respective t,z bidegree bounds (9,4), (10,5), (14,9).
        # R has z degree ≤85, T ≤137, so interpolation is exact at these bounds.
        vals=[]
        for z in range(86):
            vs=[quartic_forms(t,z) for t in range(11)]
            a=interp([v[0] for v in vs[:10]]); m=interp([v[1] for v in vs]); vals.append(res(a,m,9,10))
        raw=interp(vals); r,content=primitive(raw); assert len(r)==41
        def t_at(z):
            vs=[quartic_forms(t,z) for t in range(15)]
            a=interp([v[0] for v in vs[:10]],p); b=interp([v[2] for v in vs],p)
            return res(a,b,9,14,p)
        tbound=137
    vals=[t_at(i) for i in range(tbound+1)]; tt=interp(vals,p)
    assert all(ev(tt,i,p)==v for i,v in enumerate(vals))
    assert all(t_at(i)==ev(tt,i,p) for i in (p-1,p-2,p-7))
    assert r[-1]%p and gcd_mod(r,tt,p)[0]==[1]
    # Norm / integer-resultant witness, independently evaluated on the smaller remainder.
    rem=reduce_mod(tt,r,p); g,steps=gcd_mod(r,tt,p)
    norm=res([x%p for x in r],rem,len(r)-1,len(rem)-1,p); assert norm
    data=dict(name=name,p=p,R=r,raw_content=content,raw_origin_power=15 if name=='cubic' else 0,
              Tmod=tt,TremR=rem,reduced_resultant=norm,gcd_degrees=steps)
    print(f'{name}: R degree {len(r)-1}, T degree {len(tt)-1} mod {p}, gcd 1, reduced resultant {norm}',flush=True)
    return data


if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--prime',type=int,default=1009); ap.add_argument('--json')
    opts=ap.parse_args(); result=[run(name,opts.prime) for name in ('cubic','quartic')]
    if opts.json:
        with open(opts.json,'w') as f: json.dump(result,f,indent=2); f.write('\n')
