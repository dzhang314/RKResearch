#!/usr/bin/env python3
"""First stage: fraction-free elimination from the five-equation dirty chart."""
from math import comb,prod
from functools import reduce
from flint import fmpq_mpoly_ctx, fmpq, nmod_mpoly_ctx
from time import monotonic
from pathlib import Path
import argparse
import json
parser=argparse.ArgumentParser()
parser.add_argument("--work-dir",type=Path,default=Path(".projection-work"))
args=parser.parse_args()
args.work_dir.mkdir(parents=True,exist_ok=True)
C=fmpq_mpoly_ctx.get(['z','c','s'],'lex')
z,c,s=C.gens()
Z=lambda k=0:C.constant(k)
point=(8,7,5)
cuts=[]
q=19
tick=monotonic()


def mod(t,point=point,p=q):
    v=t(*point)
    return (int(v.numerator)*pow(int(v.denominator)%p,-1,p))%p


def show(name,x,point=point):
    print(name,'degrees',x.degrees(),'total',x.total_degree(),'terms',len(x.to_dict()),
          'mod19',mod(x,point),'seconds',round(monotonic()-tick,2),flush=True)


def mul(a,b):
    h=[Z() for _ in range(len(a)+len(b)-1)]
    for j,x in enumerate(a):
        for k,y in enumerate(b):h[j+k]+=x*y
    return h


def add(a,b):
    return [(a[i] if i<len(a) else Z())+(b[i] if i<len(b) else Z()) for i in range(max(len(a),len(b)))]


def neg(a):
    return [-x for x in a]


def scale(f,k):
    return [x*k for x in f]


def coeff(xs):
    h=[Z(1)]
    for v in xs:
        h=mul(h,[-v,Z(1)])
    return h


def ev(f,v):
    t=Z()
    for u in reversed(f):
        t=t*v+u
    return t


def homogeneous(f,num,den,degree=None):
    if degree is None:degree=len(f)-1
    return sum(a*num**i*den**(degree-i) for i,a in enumerate(f))


def normal(f):
    d=reduce(lambda a,b:a.gcd(b),f)
    if d.is_zero():return d,f
    assert mod(d), "fraction-free scale must be a unit at the selected residue"
    cuts.append(d)
    return d,[x/d for x in f]


def localfactor(P):
    ct,fs=P.factor()
    assert ct*prod((f**n for f,n in fs),start=Z(1))==P
    out=Z(1)
    for f,n in fs:
        zy=mod(f)
        show('  factor ×'+str(n),f)
        if zy==0:out*=f**n
        else:cuts.append(f)
    assert out!=1
    return out


x=0 # coefficient-list variable only
R=coeff([Z(0),Z(1),Z(4),c])
R3=coeff([Z(0),Z(1),Z(4)])
Iz=lambda h,e=0:sum(a*z**(j+e)/(j+e+1) for j,a in enumerate(h))
extra,[g,n]=normal([Iz(R),s*Iz(R,1)-Iz(R,2)])
P=mul(R,[n,-s*g,g])
_,K=normal([sum(P[k]*z**(k-1-j)/(k-j) for k in range(j+1,7)) for j in range(6)])
K0,K1,K4,Kc=[ev(K,j) for j in (0,1,4,c)]
extra,[HN,HD]=normal([4*K4+2*K1,K4+3*K0+2*K1])
W=[-HN*K0,-(HD-HN)*K1/2+HN*K0]
F3=2*(c+3)*ev(W,c)+(c**3-9*c*c+18*c-6)*(c*HD-HN)*Kc
show('F3 raw',F3)
F3=localfactor(F3)
show('F3',F3)


def remq(f,degree=None):
    a=f[:]
    if degree is not None:a.extend([Z()]*(degree+1-len(a)))
    if len(a)==1:return [a[0],Z()]
    for k in reversed(range(2,len(a))):
        t=a.pop()
        a=[g*h for h in a]
        a[k-1]+=s*g*t
        a[k-2]-=n*t
    return a


J2=add(add(scale(coeff([Z(1),Z(4)]),3*HN**2*K0),
           scale(coeff([Z(),Z(4)]),-(HD-HN)**2*K1)),
       scale(coeff([Z(),Z(1)]),(4*HD-HN)**2*K4))
GG=12*Kc*ev(R3,c)
J3=add(scale(J2,GG/12),scale(R3,12*ev(W,c)**2-Kc*ev(J2,c)))
ex,[GG,*J3]=normal([GG,*J3])
Ac,A=normal(remq(mul(K,R),deg:=9))
Bc,B=normal(remq(add(scale(mul(W,W),GG),neg(mul(K,J3))),deg))
for name,p in [('A0',A[0]),('A1',A[1]),('B0',B[0]),('B1',B[1])]:show(name,p,(8,7,5))
F4=A[0]*B[1]-A[1]*B[0]
show('F4 raw',F4)
F4=localfactor(F4)
show('F4',F4)
print('F4 at other root=',mod(F4,(8,7,4)),flush=True)
i=0 if mod(A[0]) else 1
_,[VD,VN]=normal([Ac*A[i],Bc*B[i]])
U=add(scale(J3,VD),scale(R,VN))
ex,[UD,*U]=normal([GG*VD,*U])
UH=homogeneous(U,HN,HD,4)
WH=homogeneous(W,HN,HD)
wN=z*HD-HN
etaN=wN+2*HD
etaD=3*wN-HD
SUM=wN*etaD+etaN*HD
L=[6*wN*etaN,-6*SUM-6*wN*etaN,6*HD*etaD+3*SUM,-2*HD*etaD]
Lback=[sum((-1)**i*comb(j,i)*L[j]*z**(j-i) for j in range(i,4)) for i in range(4)]
JwN=wN**2*(-etaD*wN+3*etaN*HD)
gcd,[LH,TH]=normal([UH,JwN*UD*WH*HD])
F5L=add(scale(mul(Lback,K),LH),scale(W,TH))
scl,[N0,N1]=normal(remq(F5L,8))
show('N0',N0);show('N1',N1)
print('a residue',-mod(N0)*pow(mod(N1),-1,19)%19,flush=True)
F5=g*N0**2+s*g*N0*N1+n*N1**2
show('F5 raw',F5)
# Expensive factorization is optional; saturation can isolate the main component.
def save_polys(name,d):
    print('writing',name,flush=True)
    with open(name,'w') as f:
        json.dump({i:[list(map(int,exp))+[str(v)] for exp,v in p.terms()] for i,p in d.items()},f)
save_polys(args.work_dir/'shape-polys.json',
           dict(F3=F3,F4=F4,F5=F5,N0=N0,N1=N1,g=g,n=n,HN=HN,HD=HD,GG=GG,Kc=Kc,
                A0=A[0],A1=A[1],B0=B[0],B1=B[1],VD=VD,VN=VN,UH=UH,WH=WH,etaD=etaD))
for v0 in (g,HD,GG,VD,UH,WH,etaD,N1):
    assert mod(v0)
    cuts.append(v0)
save_polys(args.work_dir/'chart-cuts.json', {str(i):d for i,d in enumerate(cuts)})
