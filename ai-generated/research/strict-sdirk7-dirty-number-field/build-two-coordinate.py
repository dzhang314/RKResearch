from flint import fmpq_mpoly_ctx,fmpq,nmod_mpoly_ctx,nmod_poly
from functools import reduce
from math import prod
from time import monotonic
import json
from pathlib import Path
import argparse
parser=argparse.ArgumentParser()
parser.add_argument("--work-dir",type=Path,default=Path(".projection-work"))
args=parser.parse_args()
D=args.work_dir
C=fmpq_mpoly_ctx.get(['z','c','s'],'lex')
z,c,s=C.gens();tick=monotonic()
d=json.load(open(D/'shape-polys.json'))
read=lambda x:C.from_dict({tuple(y[:3]):fmpq(y[3]) for y in x})
Fx={k:read(d[k]) for k in ('F3','F4','F5','N0','N1')}
def residue(P,X=(8,7,5),p=19):
    a=P(*X)
    return int(a.numerator)*pow(int(a.denominator),-1,p)%p
def info(P):
 return (P.degrees(),P.total_degree(),len(P.to_dict()),residue(P),round(monotonic()-tick,1))
R34=Fx['F3'].resultant(Fx['F4'],'s')
rc, rf=R34.factor()
assert rc*prod((f**n for f,n in rf),start=C.constant(1))==R34
R=C.constant(1)
cuts=[]
for P,k in rf:
    if residue(P)==0:
        R*=P**k
    else:
        cuts.append(P)
assert R.degrees()==(21,9,0) and R.total_degree()==26
print('first bivariate factor',info(R),flush=True)

def coef_s(P):
    co=[{} for _ in range(int(P.degrees()[2])+1)]
    for (i,j,k),w in P.terms():
        co[int(k)][int(i),int(j),0]=w
    return [C.from_dict(T) for T in co]
f0,f1,f2=coef_s(Fx['F3'])
print('quadratic lead',info(f2),flush=True)
assert residue(f2)
def remquad(H):
    a=coef_s(H)
    u,v,den=a[-1],C.constant(0),C.constant(1)
    for q in a[-2::-1]:
        u,v,den = q*f2*den-f0*v, f2*u-f1*v, f2*den
        d=u.gcd(v).gcd(den)
        u,v,den = u/d, v/d, den/d
    assert residue(den)
    d=u.gcd(v)
    return u/d,v/d,d,den
a,b,g,den=remquad(Fx['F4'])
print('F4 remainder const',info(a),'linear',info(b),'gcd scale',info(g),'den',info(den),flush=True)
assert residue(b) and residue(g)
print("s recovery mod19", -residue(a)*pow(residue(b),-1,19)%19,flush=True)
U,V,g5,d5=remquad(Fx['F5'])
print('F5 remainder',info(U),info(V),'gcd scale',info(g5),'den',info(d5),flush=True)
assert residue(g5)
S=U*b-a*V
print('S raw',info(S),flush=True)
p=lambda P:[[int(i),int(j),int(k),str(v)] for (i,j,k),v in P.terms()]
# Direct specialization avoids inspecting a degree-3691 polynomial just to certify primitivity.
N=nmod_poly
def specialize(P):
    d={}
    for (i,j,k),x in P.terms():
        assert int(k)==0
        j=int(j)
        t=int(x.numerator)*pow(int(x.denominator),-1,19)%19
        d[j]=(d.get(j,0)+t*pow(8,int(i),19))%19
    return N([d.get(j,0) for j in range(max(d)+1)],19)
r0,s0 = specialize(R),specialize(S)
assert r0.degree()==9
assert r0.gcd(s0)==N([12,1],19)
assert r0==N([9,10,17,4,13,5,15,15,9,11],19)
print('primitive specialization gcd: c + 12 over F19',flush=True)
with open(D/'two-polynomials.json','w') as f:
    json.dump({'R':p(R),'S':p(S),'snum':p(-a),'sden':p(b)},f)
with open(D/'projection-cuts.json','w') as f:
    json.dump([p(a) for a in (cuts+[f2,g,den,b,g5,d5])],f)
