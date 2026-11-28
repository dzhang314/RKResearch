#!/usr/bin/env python3
"""Exhaust all regular one-evaluation alignment branches over Z[1/210]."""
from fractions import Fraction as Q
from math import gcd,prod
from collections import Counter
from itertools import product
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'erk10-sixteen-rational-mirror-family'))
from family import paid,pol
Z,O=Q(0),Q(1)
C=Q(1,2); A=Q(2,3); B=Q(1,3)
Y=[O,-O]
def smooth(limit):
    S={1}
    for p in (2,3,5,7):
       S={v*p**k for v in S for k in range(limit.bit_length())if v*p**k<=limit}
    return S
def candidates():
    S=smooth(5000)
    T={(a,b,a+b)for a in S for b in S if a<=b and a+b in S and gcd(a,b)==1}
    # Completeness uses the published total 63, not the enumeration cutoff.
    assert len(T)==63 and max(c for a,b,c in T)==4375
    U={r for a,b,c in T for r in (Q(a,c),Q(b,c),Q(c,a),Q(c,b),Q(-a,b),Q(-b,a))}
    assert len(U)==375
    return U
def shape(t,case,anchor):
    if t in (0,1,2):return
    v=t*(12*t*t-45*t+40)/(15*(t-2)**2)
    if v in (0,1,2,t,Q(2,3)):return
    a,b=v/t,2/t
    c,e=(b,a)if anchor=='b' else (a,b)
    if c in (0,1)or e in (0,1)or c==e:return
    if case==0:
        xi=C;E=c*C;D=1-E
        V=(2*E-1)**2
    elif case==1:
        xi=C/c;E=C;D=1-xi
        V=(2*xi-1)**2
    else:
        if c==-1:return
        xi=1/(1+c);E=1-xi;D=C
        V=(2*xi-1)**2
    if V in (0,1,Q(1,9))or len({Z,O,A,B,xi,E,D})!=7:return
    r=xi*e
    H=pol.hull((Z,xi,E,r))
    I=2*V/15-Q(2,35);J=2*V/35-Q(2,63)
    assert I
    m=(Q(1,9)-J/I)/8
    W=pol.mul(pol.pw(Y,2),pol.add(pol.scale(Q(-1,4),pol.pw(pol.add(Y,[Q(-2,3)]),2)),[-m]))
    HS=pol.mul(H,W)
    k0,k1=pol.mu(HS),pol.mu(HS,1)
    f4=pol.mul(pol.hull((Z,xi,E,r)),W)
    # If the other evaluation is placed at R=r as well, both values of
    # ell vanish. Then the fused terminal moments themselves must vanish.
    assert (pol.mu(f4),pol.mu(f4,1))==(k0,k1)
    assert k0 or k1,('undetermined free R',case,anchor,t)
    return xi,E,D,r,v,(r if not k0 else k1/k0),k0
def weights(sites):
    ans={}
    for x in sites:
        other=tuple(y for y in sites if y!=x)
        ans[x]=pol.mu(pol.hull(other))/prod(x-y for y in other)
    return ans
def main():
    U=candidates()
    print('63 primitive S-unit triples; 375 distinct first coordinates.')
    for case,mode in product(range(3),('a','b')):
      ts={4*u-2 if (case,mode)==(2,'b') else 2*u for u in U}
      result=Counter()
      for t in sorted(ts):
        z=shape(t,case,mode)
        if z is None:continue
        xi,E,D,r,v,R,k0=z
        # At R=r both evaluations are blind, and the tested F4/F5 moments
        # are the two displayed non-simultaneously-zero integrals.
        result['blind-collision excluded']+=1
        if not k0:continue
        raw=(O,A,B,A,1-R,D,R,E,xi)
        if len({Z,*raw})!=9 or R==r:continue
        result['distinct linear choices']+=1
        sc=xi/t
        if not all(paid(x)for x in (*raw,sc,v*sc)):continue
        result['paid clocks']+=1
        W=weights({Z,*raw})
        if not all(paid(w)for w in W.values()):continue
        result['paid scalar masses']+=1
        # The old pure endpoint exactly integrates the four distinct
        # clock masses 0,1,2,v. The starter's stage defect forces zero
        # endpoint weight there, even if its clock repeats.
        leg=pol.hull((Z,Q(2),v))
        pre=pol.mu(pol.add(*(pol.sh([a*t**(i+1)],i)for i,a in enumerate(leg))))/((1-2)*(1-v))
        fixed_coefficient=sc*pre
        print('paid scalar candidate',case,mode,t,raw,'old clock-1 coefficient',fixed_coefficient)
        assert fixed_coefficient==Q(5875,26112)
        assert not paid(fixed_coefficient)
      print('branch',case,mode,dict(result))
if __name__=='__main__':main()
