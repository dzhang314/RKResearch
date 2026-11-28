#!/usr/bin/env python3
"""Exact rational instance of the necessary DIRK12/15 high-site 10x5 bridge."""
from fractions import Fraction as Q
from math import comb
import argparse
import json


def conv(a, b):
    c = [Q(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def evalp(c, x):
    out = Q(0)
    for a in reversed(c):
        out = out*x + a
    return out


def legendre_derivative(n, x):
    return evalp([Q(k*(-1)**(n-k)*comb(n,k)*comb(n+k,k))
                  for k in range(1,n+1)], x)


def system(data):
    g = tuple(map(Q, data['ghost_clocks']))
    h = tuple(map(Q, data['ghost_amplitudes']))
    a = tuple(map(Q, data['first_live_clocks']))
    assert len(g) == len(h) == len(a) == len(set(g)) == len(set(a)) == 4
    assert all(h) and all(a)
    ell = []
    for k,z in enumerate(g):
        d = h[k]
        for j,w in enumerate(g):
            if k != j:
                d *= z-w
        ell.append(1/d)

    def L(P):
        return sum(y*evalp(P, z) for y,z in zip(ell,g))

    rows = []
    hull = [Q(0),Q(1)]
    for k,x in enumerate(a,1):
        hull = conv(hull,[-x,Q(1)])
        p5,p6,p7 = (legendre_derivative(n,x) for n in [5,6,7])
        for j in range(5-k):
            P = [Q(0)]*j+hull
            m0,m1 = L(P),L([Q(0)]+P)
            rhs = sum(coef*x**i/(i+1) for i,coef in enumerate(P))
            lc = P[5] if len(P)>5 else Q(0)
            rows.append([p6*m0,p6*m1,p5*m0,p7*m0,-p6*lc,rhs])
    late = data.get('late_ghost_index')
    if late is not None:
        assert isinstance(late,int) and 0 <= late < 4
        x = a[0]
        p5,p6,p7 = (legendre_derivative(n,x) for n in [5,6,7])
        rows.append([p6,g[late]*p6,p5,p7,Q(0),Q(0)])
    x,y = a[:2]
    p5,p6,p7 = (legendre_derivative(n,x) for n in [5,6,7])
    q5,q6,q7 = (legendre_derivative(n,y) for n in [5,6,7])
    guards = ([Q(0),Q(1),Q(0),Q(0),Q(0)],
              [Q(0),Q(0),p6*q5-q6*p5,p6*q7-q6*p7,Q(0)])
    return rows, guards


def reduce_rows(rows):
    cols=len(rows[0])-1
    A=[list(r) for r in rows]
    m=0
    pivots=[]
    for j in range(cols):
        i=next((i for i in range(m,len(A)) if A[i][j]),None)
        if i is None:
            continue
        A[i],A[m]=A[m],A[i]
        p=A[m][j]
        A[m]=[x/p for x in A[m]]
        for i in range(len(A)):
            if i != m and A[i][j]:
                z=A[i][j]
                A[i]=[x-z*y for x,y in zip(A[i],A[m])]
        pivots.append(j)
        m+=1
    if any(r[-1] for r in A[m:]):
        return None, pivots
    free=[j for j in range(cols) if j not in pivots]
    particular=[Q(0)]*cols
    for i,j in enumerate(pivots):
        particular[j]=A[i][-1]
    nullspace=[]
    for f in free:
        v=[Q(0)]*cols
        v[f]=Q(1)
        for i,j in enumerate(pivots):
            v[j]=-A[i][f]
        nullspace.append(v)
    return [particular,*nullspace], pivots


def report(d):
    rows,guards=system(d)
    sol,piv=reduce_rows(rows)
    out={'rows':len(rows),'coefficient_rank':len(piv)}
    if sol is None:
        return dict(out,status='incompatible_linear_system')
    out['solution_dimension']=len(sol)-1
    for name,guard in zip(('incompatible_nu_zero','incompatible_first_pair_rank_one'),guards):
        if all(not sum(x*y for x,y in zip(row,guard)) for row in sol):
            return dict(out,status=name)
    return dict(out,status='necessary_gates_pass_not_a_tableau')


def self_test():
    assert [legendre_derivative(n,Q(1)) for n in (5,6,7)]==[30,42,56]
    a=Q(2,3)
    h=[Q(0),-a,Q(1)]
    q=[Q(0),Q(0),-a/2,Q(1,3)]
    assert evalp(q,a)==-a**3/6
    rows=[[Q(1),Q(3),Q(7)],[Q(0),Q(0),Q(0)]]
    sol,piv=reduce_rows(rows)
    assert sol==[[7,0],[-3,1]] and piv==[0]
    e={'ghost_clocks':['1/8','1/4','3/8','1/2'],
       'ghost_amplitudes':['1/10','-1/7','1/5','-1/3'],
       'first_live_clocks':['1/7','2/5','3/5','5/7'],'late_ghost_index':3}
    assert report(e)=={'rows':11,'coefficient_rank':5,'status':'incompatible_linear_system'}
    return 'exact scalar bridge self-test: passed (synthetic negative control only)'


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input',nargs='?',help='JSON file with four ghosts and four live debuts')
    p.add_argument('--self-test',action='store_true')
    ns=p.parse_args()
    if ns.self_test:
        print(self_test())
    if ns.input:
        with open(ns.input,encoding='utf-8') as fh:
            print(json.dumps(report(json.load(fh)),sort_keys=True))
    if not (ns.input or ns.self_test):
        p.error('provide data or --self-test')


if __name__=='__main__':
    main()
