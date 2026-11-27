#!/usr/bin/env python3
"""Exhaust all split Gauss pairs in the six exceptional characteristics."""
from gate_scan import ctx,phase,twozero
from rear_gate import rear,values
from itertools import permutations
from collections import Counter

expect={13:(0,0),19:(1,0),107:(0,0),137:(2,0),997:(1,1),3137:(0,0)}
for p,(pre,post) in expect.items():
    F,R,d,xx=ctx(p)
    T=[]
    for a,b in permutations(xx,2):
        out=twozero(F,a,b)
        if not out:continue
        g=out[1]
        k,q,r,J,Jx=values(F,a,b)
        if out[0]=='rim-mass':
            assert a+b==1 and p in (19,137)
            # Front must have a silent among its first three: no all-active
            # actual graph beyond them pays the first-three conditions.
            R0=r(g);P=R0+g*g
            assert R0!=0 and P!=0
            u=(2*R0-g*(2*g+k))/P
            assert not [t for s,w,t,r3 in phase(u) if t!=0 and R0*t==r(g*(1+w))]
        v=rear(F,a,b,g)
        if v:T.append((a,b,out,v))
    assert sum(twozero(F,a,b) is not None for a,b in permutations(xx,2))==pre
    assert len(T)==post
    if p==997:
        a,b,front,back=T[0]
        assert (a,b)==(89,337)
        assert front[0]=='rigid' and front[1]==591 and front[2]==470
        assert front[-1]==[(2,'A',543,89,945)] and back==[('offzero','A',137,274,151)]
    print(p,d,pre,post)
