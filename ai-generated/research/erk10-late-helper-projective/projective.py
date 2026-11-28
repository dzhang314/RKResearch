#!/usr/bin/env python3
"""Exact necessary projective congruences for the late-helper rational chart."""
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from pathlib import Path
from math import factorial,lcm,gcd
from collections import Counter,defaultdict
from functools import cache
from dataclasses import dataclass
import argparse,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'erk10-late-helper'))
import replay
def normalize(rows):
    d=lcm(*(x.denominator for row in rows for x in row))
    rows=[[int(x*d)for x in row]for row in rows]
    g=gcd(*(v for row in rows for v in row))
    return tuple(tuple(v//g for v in row)for row in rows)

# Nodal forms after removing the exact endpoint factor X (X-1).
NODES=tuple(normalize([[Q(-1,(j+k+2)*(j+k+3))for j in range(7)]])[0]for k in range(2))
def int_monomial(j,k):
    return Q(factorial(j)*factorial(k),factorial(j+k+1))
def Ints(j):
    a,b,c=(int_monomial(j,k)for k in (2,3,4))
    # q=(P,-S,1), so the middle entry is minus the coefficient of S.
    return -a/2,b/3-a/2,2*b/3-a/2-c/4
TAPS=normalize(list(zip(*(Ints(j)for j in range(6)))))
ELL=normalize(tuple(replay.pad(poly,10)for poly in replay.R))
def point(t,p):
    return (1,0)if t==p else(t,1)
def poly(t,p):
    a,b=point(t,p);return [-a,b]
def fx(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
      for j,v in enumerate(b):r[i+j]+=u*v
    return [v%p for v in r]
def moment_quad(u,k,p):
    a=NODES[k]
    return tuple(sum(t*a[i+j]for i,t in enumerate(u))%p for j in range(3))
def dot(a,b,p):
    return sum(x*y for x,y in zip(a,b))%p
def cross(a,b,p):
    u,v,w=a;x,y,z=b
    return ((v*z-w*y)%p,(w*x-u*z)%p,(u*y-v*x)%p)
def canonical(q,p):
    d=next((x for x in reversed(q)if x%p),0)
    if not d:return tuple(q)
    u=pow(d,-1,p)
    return tuple(v*u%p for v in q)
def slope(a,b,p):
    if not a%p:return p if b%p else p+1
    return b*pow(a,-1,p)%p
@cache
def pair_dict(p):
    return {canonical(fx(poly(a,p),poly(b,p),p),p):(a,b)
            for a,b in combinations_with_replacement(range(p+1),2)}
@cache
def evals(p):
    return [[sum(c*(pow(t,j,p) if t<p else int(j==9))for j,c in enumerate(r))%p for r in ELL]
             for t in range(p+1)]
@cache
def one_moment_pairs(r,p):
    return tuple(pair for pair in pair_dict(p) if not dot(r,pair,p))
def shape(d,e,xi,p):
    q=fx(poly(d,p),poly(e,p),p)
    h=fx(q,poly(xi,p),p)
    f=[0,*h];g=[0,*f]
    k=(tuple(dot(r,f,p)for r in TAPS),tuple(dot(r,g,p)for r in TAPS))
    a,b=point(xi,p)
    weights=[pow(a,r,p)*pow(b,3-r,p)%p for r in range(4)]
    const=tuple(w*v%p for w,v in zip(weights,q+[0]))
    shift=tuple(w*v%p for w,v in zip(weights,[0,*q]))
    return h,k,const,shift
def chart(d,e,xi,p,return_seeds=False):
    H,(k0,k1),l0,l1=shape(d,e,xi,p)
    pairs=pair_dict(p)
    colors=0
    source=defaultdict(list)if return_seeds else None
    for z in range(p+1):
      u=fx(H,poly(z,p),p)
      a,b=moment_quad(u,0,p),moment_quad(u,1,p)
      q=cross(a,b,p)
      if any(q):
        v=canonical(q,p);qs=(v,)if v in pairs else ()
      else:
        nonzero=a if any(a)else b
        qs=one_moment_pairs(canonical(nonzero,p),p)if any(nonzero)else tuple(pairs)
      for q in qs:
        k=slope(dot(k0,q,p),dot(k1,q,p),p)
        colors|=1<<k
        if return_seeds: source[k].append((z,*pairs[q]))
      if not return_seeds and colors>>(p+1): return (1<<(p+1))-1
    if not colors:return 0 if not return_seeds else (0,())
    out=0;seeds=[]
    zero=bool(colors>>(p+1))
    nums=evals(p)
    for t in range(p+1):
      color=slope(dot(l0,nums[t],p),dot(l1,nums[t],p),p)
      if zero or color==p+1 or (colors>>color)&1:
        out|=1<<t
        if return_seeds:
          candidates=(r for v in source.values()for r in v) if color==p+1 else (*source[color],*source[p+1])
          seeds.extend((t,z,a,b)for z,a,b in candidates)
    return (out,seeds)if return_seeds else out
def reduced(n,p):
    d=n.denominator%p
    return n.numerator*pow(d,-1,p)%p if d else p
@cache
def freeze_prime(p):
    stats=Counter();data={}
    for d,e in combinations_with_replacement(range(p+1),2):
      packed=[]
      for xi in range(p+1):
        chk=chart(d,e,xi,p)
        packed.append(chk)
        regular=len({0,1,d,e,xi,p})==6
        stats['all']+=1
        if regular:stats['distinct finite nonendpoint']+=1
        if chk:
          stats['pass']+=1
          stats['horizon incidences']+=chk.bit_count()
          if regular:stats['distinct finite pass']+=1
      data[d,e]=packed
    return stats,data
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('primes',nargs='+',type=int);ap.add_argument('--emit',type=Path)
    a=ap.parse_args()
    for p in a.primes:
      C,T=freeze_prime(p)
      print('prime',p,dict(C),flush=True)
      if p==29:
        d,e,xi=18,19,22
        assert T[d,e][xi]==0
      if a.emit is not None:
        j={'prime':p,'indices':'0..p-1 affine; p is infinity; unordered (d,e) columns; row mask in θ',
            'stats':dict(C),'rows':[[d,e,*M]for (d,e),M in T.items()]}
        a.emit.mkdir(parents=True,exist_ok=True)
        (a.emit/f'projective-{p}.json').write_text(json.dumps(j,indent=1)+'\n')
if __name__=='__main__':
    main()
