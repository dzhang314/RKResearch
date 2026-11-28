#!/usr/bin/env python3
"""Literal fixed grid coefficients for the support-one and support-three exclusions."""
from itertools import permutations
from collections import Counter

P=1013
D6=(-42,840,-5040,12600,-13860,5544)
ROOTS=(347,468,507,546,667)
LIVE=(*ROOTS,1)

def frac(n,d): return n*pow(d%P,-1,P)%P

def val(f,x):
    r=0
    for a in reversed(f): r=(r*x+a)%P
    return r

def mul(f,g):
    h=[0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g):h[i+j]=(h[i+j]+a*b)%P
    return h

def hull(nodes):
    f=[1]
    for x in nodes: f=mul(f,[-x,1])
    return f

def J(f,x=1): return val([0]+[frac(t,i+1) for i,t in enumerate(f)],x)

def card(pts,x):
    f=hull(u for u in pts if u!=x)
    return [frac(t,val(f,x)) for t in f]

def err_ratio(z,pts,h,cubic):
    row={}
    for x in pts:
        Q=card(pts,x)
        row[x]=J(Q,z)+(cubic*Q[-1] if cubic else 0)
    return frac(sum(v*x**4 for x,v in row.items())-frac(z**5,5),h)

def localized():
    c=Counter()
    for a,b,d,v,u,w in permutations(LIVE):
        if a==1: continue
        if (2*u-v)%P==0 or (2*v-u)%P==0:
            # The representative of 1/2 is unique among the fixed roots:
            # every one of these is an actual endpoint/center equality,
            # separately impossible by the literal first-u equation.
            assert {v,u}=={1,frac(1,2)}
            c["actual_half_clock_resonance"]+=1
            continue
        g1=frac(d**3,6)
        hv=frac(d*d*v**3,36*(v-d))
        hu=hv*frac(u**3*(2*v-u),v**3*(2*u-v))%P
        lam=frac(3*(v-d)*(v-2*d),d*d)
        assert hv and hu
        phiv=err_ratio(v,(0,d,v),hv,0)
        phiu=err_ratio(u,(0,d,v,u),hu,lam*hu)
        phiw=(phiv+frac((w-v)*(phiu-phiv),u-v))%P
        R=hull((0,v,u,w))
        assert J(R,w)
        delta=(val(R,d)-g1*(phiw-(v+u+w)*lam))%P
        # Never divide by delta in a residue check.
        scaled={v:delta*hv%P,u:delta*hu%P,w:g1*J(R,w)%P}
        assert sum(J(card((0,a,v,u,w),z),a)*amp for z,amp in scaled.items())%P
        c["local_no_spent"]+=1
        if d!=1:  # Only this chronology can complete a live d pair before a.
            assert sum(J(card((0,d,v,u,w),z),d)*amp for z,amp in scaled.items())%P
            c["local_d_spent"]+=1
    assert c=={"actual_half_clock_resonance":48,"local_no_spent":552,"local_d_spent":432}
    return c

def main():
    assert all(P%k for k in range(2,32)) and D6[-1]%P
    assert tuple(z for z in range(P) if val(D6,z)==0)==ROOTS and frac(1,2) in ROOTS
    c=localized()
    for a,u,v in permutations(LIVE,3):
        assert J(hull((0,a,u,v)),a)
        c["first_three_nodal"]+=1
    for a,d,v,u in permutations(LIVE,4):
        assert J(hull((0,d,v,u)),a)
        c["unanchored_four"]+=1
    for k,n in c.items(): print(f"mod 1013, {k}: {n}")

if __name__=="__main__": main()
