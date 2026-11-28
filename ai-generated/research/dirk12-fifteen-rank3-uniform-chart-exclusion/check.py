#!/usr/bin/env python3
"""Exact scalar/chronological algebra for the terminal-dirty uniform DIRK12 chart."""
import argparse
import json
from functools import reduce
from itertools import combinations, permutations
from math import isqrt
from pathlib import Path
import sympy as S

x,t,s=S.symbols("x t s")
D4=[30,-420,1680,-2520,1260]
D5=[-42,840,-5040,12600,-13860,5544]


def expr(values,var):
    return sum(v*var**i for i,v in enumerate(values))


def integral(poly,a,b):
    return S.Add(*(v*(b**(i+1)-a**(i+1))/(i+1)for(i,),v in S.Poly(poly,x).terms()))


def necessary():
    jd4,jd5=expr(D4,x),expr(D5,x)
    assert S.degree(S.gcd(jd4,jd5),x)==0
    b=x*x-S.Rational(6,5)*t*x+S.Rational(3,10)*t*t
    pencil=jd5*jd4.subs(x,t)-jd4*jd5.subs(x,t)
    remain=S.Poly(S.rem(pencil,b,x),x)
    ra,rb=[S.Poly(z,t,domain='QQ') for z in remain.all_coeffs()]
    assert (ra.degree(),rb.degree())==(8,9) and ra.gcd(rb).degree()==0
    p=x**3+s*x*x-S.Rational(6,5)*(s*t+t*t)*x+S.Rational(3,10)*s*t*t+S.Rational(2,5)*t**3
    assert S.expand(integral(x*p,0,t))==S.expand(integral(x*x*p,0,t))==0

    # J[x(x-t)P]/(x-t) is a polynomial, since the t-evaluation is paid zero.
    jj,left=S.div(integral(x*(x-t)*p,0,x),x-t,x)
    assert S.expand(left)==0
    rmat=[]
    for z in (jj,x*b,x*x*b):
        f=S.Poly(S.rem(z,p,x),x)
        rmat.append([f.nth(i) for i in range(3)])
    assert S.expand(S.det(S.Matrix(rmat))-t**7*(3*s+4*t)*(9*s+16*t)/300000)==0

    c=[]
    for i in range(4):
        z=x**(i+1)*(1-x)*(x-t)*p
        c.append([integral(z*x,0,1),integral(z,0,1),integral(z*x*x,0,1)])
    ms=[S.Poly(S.det(S.Matrix([c[j]for j in opts])),s).as_expr()
        for opts in combinations(range(4),3)]
    assert all(S.degree(a,s)==3 for a in ms)
    rs=[S.Poly(S.resultant(ms[i],ms[j],s),t,domain='QQ')
        for i,j in ((0,1),(0,2),(0,3),(1,2))]
    assert all(a.degree()==54 for a in rs)
    m=reduce(S.polys.polytools.gcd,rs).monic()
    assert m.degree()==36

    # Use actual polynomial Euclidean reductions modulo the necessary m,
    # certifying every inversion there. This directly proves an ideal
    # consequence at all possible candidate roots; no generic pivot is used.
    def qt(z):
        return S.Poly(z,t,domain='QQ').rem(m)
    zero=qt(0)
    one=qt(1)

    def mul(a,b):
        return (a*b).rem(m)

    def inv(a):
        assert a.gcd(m).degree()==0
        return a.invert(m)

    def trim(f):
        while f and f[-1].is_zero:
            f.pop()
        return f

    def remainder(f,g):
        h=f[:]
        unit=inv(g[-1])
        while len(h)>=len(g):
            j=len(h)-len(g)
            z=mul(h[-1],unit)
            for i,a in enumerate(g):
                h[j+i]-=mul(z,a)
            assert h[-1]==zero
            trim(h)
        return h

    fs=[]
    for f in ms[:2]:
        ff=S.Poly(f,s)
        fs.append([qt(ff.nth(i)) for i in range(ff.degree()+1)])
    a,b=fs
    degrees=[]
    while len(b)>2:
        degrees.append(len(b)-1)
        a,b=b,remainder(a,b)
    assert len(b)==2 and b[-1].gcd(m).degree()==0
    ss=-mul(b[0],inv(b[1]))
    linear_lead=b[1]

    def value(f):
        z=zero
        for a in S.Poly(f,s).all_coeffs():
            z=mul(z,ss)+qt(a)
        return z
    cr=[[value(v)for v in row]for row in c]
    a,b,z=cr[0]
    d,e,w=cr[1]
    pivot=mul(a,e)-mul(b,d)
    pp=inv(pivot)
    gg=mul(mul(b,w)-mul(z,e),pp)
    kk=mul(mul(z,d)-mul(a,w),pp)
    assert all(mul(a,gg)+mul(b,kk)+z==zero for a,b,z in cr)
    print("quadratic remainder degrees 8,9; exact rational gcd 1")
    print("cubic four resultants degree 54; exact common monic degree 36")
    print("verified quotient units: two Euclidean steps, linear s pivot, and g,k determinant")
    print("all four cubic hull moments recover exactly in the quotient")
    print("exact same-clock determinant = t^7(3s+4t)(9s+16t)/300000")
    return m,ss,gg,kk,ra,rb,linear_lead,pivot


def gates(m,sv,gv,kv,ra,rb,lead,pivot,p):
    assert all(p % i for i in range(2,isqrt(p)+1))

    def mod(a):
        return int(a.p)%p*pow(int(a.q),-1,p)%p

    def conv(f):
        q=f if isinstance(f,S.Poly) else S.Poly(f,t,domain='QQ')
        return S.Poly.from_list([mod(v) for v in q.all_coeffs()],t,modulus=p)

    m,ss,gg,kk,ra,rb,lead,pivot=map(conv,[m,sv,gv,kv,ra,rb,lead,pivot])
    assert m.degree()==36 and m.LC()==1
    zero,one=conv(0),conv(1)

    def mul(a,b):
        return (a*b).rem(m)

    def pmul(f,g):
        h=[zero]*(len(f)+len(g)-1)
        for i,a in enumerate(f):
            for j,b in enumerate(g):
                h[i+j]+=mul(a,b)
        return h

    def add(f,g):
        h=[zero]*max(len(f),len(g))
        for i,a in enumerate(f):
            h[i]=a
        for i,a in enumerate(g):
            h[i]+=a
        return h

    def scale(f,a):
        return [mul(q,a) for q in f]

    def ints(f):
        return [zero]+[mul(a,conv(S.Rational(1,i+1))) for i,a in enumerate(f)]

    def star(f):
        h=ints(f)
        return add([sum(h,zero)],scale(h,-one))

    def rem(f,g):
        h=list(f)
        assert g[-1]==one
        while len(h)>=len(g):
            n=len(h)-len(g)
            q=h[-1]
            for j,v in enumerate(g):
                h[n+j]-=mul(q,v)
            assert h.pop().is_zero
        return h

    def padded(f,k):
        return (f+[zero]*k)[:k]

    def det(a):
        n=len(a)
        out=zero
        for order in permutations(range(n)):
            h=conv((-1)**sum(order[i]>order[j]for i in range(n)for j in range(i+1,n)))
            for i,j in enumerate(order):
                h=mul(h,a[i][j])
            out+=h
        return out

    v=conv(t)
    p3=[mul(conv(S.Rational(3,10)*t*t),ss)+conv(S.Rational(2,5)*t**3),
        mul(conv(-S.Rational(6,5)*t),ss)-conv(S.Rational(6,5)*t*t),ss,one]
    q=[kk,gg,one]
    D=list(map(conv,D5))
    A=star(pmul([one,-one],p3))
    B=ints([zero]+p3)
    C=ints([zero,zero]+p3)
    h=add(C,scale(B,-v))
    forward5=det([padded(rem(Z,p3),3) for Z in (A,[zero]+A,pmul([one,-one],D))])

    def norm(f):
        a,b=padded(rem(f,q),2)
        return mul(a,a)-mul(gg,mul(a,b))+mul(kk,mul(b,b))

    reverse_gap=add(pmul(pmul([zero,-v,one],p3),add([zero]+B,scale(C,-one))),
                    scale(pmul(h,B),-one))
    # Now work modulo q in y, using y=middle reflected clock,
    # z=-g-y=first forward clean clock in reflected coordinates.
    def qm(f,g):
        return rem(pmul(f,g),q)

    def qa(f,g):
        return rem(add(f,g),q)

    def qn(f):
        return scale(f,-one)

    def ev(f,arg):
        h=[zero]
        for a in reversed(f):
            h=qa(qm(h,arg),[a])
        return h

    y,z=[zero,one],[-gg,-one]
    x1,x2=qa([one],qn(z)),[one,-one]
    th1,th2=qm(x1,ev(p3,z)),qm(x2,ev(p3,y))
    f1,f2=ev(A,z),ev(A,y)
    l1,l2=qm(x1,ev(D,z)),qm(x2,ev(D,y))
    diff=qa(x2,qn(x1))
    up,dn=ev(h,y),qm(qm(y,[-v,one]),ev(p3,y))
    r=qa(qm(qa(qm(diff,th1),qn(f1)),qa(qm(dn,f2),qn(qm(up,th2)))),
         qn(qm(qm(up,f2),th1)))
    forward_gap=qa(qm(r,l1),qm(qm(qm(f1,f1),dn),l2))
    tests={
        "forward_first_diagonal": norm(A),
        "forward_five_dirty": forward5,
        "empty_reverse_gap":norm(reverse_gap),
        "empty_forward_gap":norm(forward_gap),
        "same_clock_factor_one":mul(conv(3),ss)+conv(4*t),
        "same_clock_factor_two":mul(conv(9),ss)+conv(16*t),
        "linear_s_pivot":lead,
        "two_row_clean_hull_pivot":pivot,
    }
    for name,g in tests.items():
        assert m.gcd(g).degree()==0,name
    assert (ra.degree(),rb.degree())==(8,9) and ra.gcd(rb).degree()==0
    print(f"prime {p}: monic degree 36, all {len(tests)} quotient units; quadratic degrees preserved")
    for name,g in tests.items():
        print(f"  {name}: residue degree {g.rem(m).degree()}, gcd 1")

    def coeff(f):
        return [int(a)%p for a in reversed(f.all_coeffs())]
    return {"prime":p,"parameter":coeff(m),
            "units":{key:coeff(g.rem(m))for key,g in tests.items()},
            "quadratic":[coeff(ra),coeff(rb)]}


if __name__=='__main__':
    args=argparse.ArgumentParser()
    args.add_argument('--expanded',type=Path)
    args.add_argument('--sturm',action='store_true')
    a=args.parse_args()
    q=necessary()
    if a.sturm:
        print("real roots of the optional scalar-only parameter polynomial:",
              q[0].count_roots(-S.oo,S.oo))
    rows=[gates(*q,p)for p in (1009,1013)]
    if a.expanded:
        a.expanded.write_text(json.dumps(rows,indent=2,sort_keys=True)+'\n')
