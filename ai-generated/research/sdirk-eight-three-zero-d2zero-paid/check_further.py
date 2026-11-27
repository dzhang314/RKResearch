#!/usr/bin/env python3
from gauss import ctx,phase
from itertools import permutations

def gate1(d,z):
    return (1-z*z)/2-d*(1-z)-(1-d)*(z-d)
def gate2(d,z,e,g):
    return (1-z**3)/3-(d+e)*(1-z*z)/2+d*e*(1-z)-g*(z-d)*(z-e)
def phases(F,d):
    return [(1-d,d,1),(1-d,1-d,0),(F.one()/2,F.one()/2,1),
            (4-5*d,1-d,0),(3*d-1,1-d,0),(F.one()/2,1-d,0),
            ((4-d)/5,(1+d)/5,1),((1+d)/3,(2-d)/3,1)]

def fourth(F,u,w,branch,a):
    for f,d,v,r in phase(u):
        if f!=branch or d!=w or v==0:continue
        k=1+2*u-u*u
        h=F.one()/2
        s=(k/2-h)/u;t=(v/2-h)/w
        cc=(t-s)/(w-u);bb=s-cc*(2+u)
        return -(a-1)/k+bb+cc*(4*F.one()/3+2*(k+1)*(a-1)/(3*k))

accepted={13:[],17:[(7,11)],103:[(97,30)],7793:[(6924,2220)]}
one={17:[None,None,None,None],103:[34,31,34,62],7793:[1763,7390,1763,1623]}
for p in accepted:
    F,Q,deg,rs=ctx(p)
    assert len(rs)==4
    ss=[(d,z) for d,z in permutations(rs,2) if gate1(d,z)==0]
    assert len(ss)==len(accepted[p])
    for d,z in ss:
        assert (d,z) in accepted[p]
        assert d not in (4*d-z-2,2*z-d) and 4*d-z-2 not in rs and 2*z-d not in rs
        G=1-d
        x=d/G
        h=x-1
        options=[(h,2-h,'S'),(h,2*h,'A'),(2-h,h,'S'),(h/2,h,'A')]
        cs=[fourth(F,u,w,k,x) for u,w,k in options]
        assert cs==one[p] and all(x is None or x!=0 for x in cs)
        print('one active off-zero clock',p,ss,'fourth coefficients',cs)

two=[]
for p in (103,3517):
    F,Q,deg,rs=ctx(p)
    assert len(rs)==4
    for d in rs:
        for i,(e,g,tail) in enumerate(phases(F,d),1):
            if e==d or g==0:continue
            q,w=(e,d) if tail else (d,e)
            z=2*w-q
            if z not in rs or z in (e,d):continue
            h=(q-w)/g
            if 4*h**3-12*h*h+3*h+2!=0 or gate2(d,z,e,g)!=0:continue
            two.append((p,i,*map(int,(d,z,e,g))))
assert two==[(3517,6,1718,1800,1759,1800)]
p,i,d,z,e,g=two[0]
F,_,_,_=ctx(p)
u=(F(e)-g)/g
assert u==338 and (F(d)-g)/g==2*u
assert phase(u)[1]==('A',676,0,2240)
print('two active off-zero clocks:',two,'force forward g3=0')
