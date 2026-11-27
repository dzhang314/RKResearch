#!/usr/bin/env python3
import sympy as s
from sympy.polys.fields import field
from sympy import QQ
from flint import fmpq_poly,fmpq,fmpq_mpoly_ctx
K,m,u=field('m u',QQ)
h=K(1)/2
beta=3-m
t0=1-m;t1=m-1;t2=t1-u;t3=t1-2*u
ht=-2+u+4*u*u-u**3
rt=2*u*(3*u-2)/ht
k=1+2*u-u*u
q=1+4*u-4*u*u+2*rt*u
n=3*m*m/5
L3=lambda t:t*(t*t-n)
L4=lambda t:t**4-6*m*m*t*t/7+3*m**4/35
P3=lambda t:(t-beta)*((t-beta)**2-4)
a2=-6*m*m/7
a0=3*m**4/35
s0=2*(a0+3*beta**4-12*beta*beta)
s1=-16*beta*(beta*beta-1)
s2=2*(a2+6*beta*beta+4)
S=lambda t:s0+s1*t+s2*t*t
U=L4(t2)/k-L4(t1);V=L4(t3)/q-L4(t1)
X=S(t2)-S(t1);Y=S(t3)-S(t1)
delta=X*(q-1)-Y*(k-1)
H=(U*(q-1)-V*(k-1))/delta
J=(X*V-Y*U)/delta
B=J/(H*H)
f=L4(t1)-H*S(t1)-J*(1-h/H)
g4=-2*L4(t0)/B
C0=-L3(t0)/(h*g4)
def row(t,g):
    w=g*(g-h)
    return [g/h*P3(t), -w*(t-t0), -(1-g/h)*L3(t)+w*C0]
r1,r2,r3=[row(a,b) for a,b in zip((t1,t2,t3),(H,H*k,H*q))]
det=sum((r1[j]*(r2[(j+1)%3]*r3[(j+2)%3]-r2[(j+2)%3]*r3[(j+1)%3]) for j in range(3)),start=K.zero)
def ff(p):return [(q,e) for q,e in s.factor_list(p.as_expr())[1]]
guards=delta*H*B*(g4-h)*g4*u*k*q*(3*u-2)*ht*m
def keep(p):
    return [i for i,j in ff(p) if not K(i).numer.gcd(guards.numer*guards.denom).degree()>0]
fs,gs=keep(f.numer),keep(det.numer)
assert [s.degree(f,s.Symbol('u')) for f in fs]==[15]
assert [s.degree(g,s.Symbol('u')) for g in gs]==[0,1,27]


def residue_factors():
    P=fmpq_mpoly_ctx.get(('m','u'),'lex')
    F=[P.from_dict({ds:fmpq(str(c)) for ds,c in K(a).numer.items()}) for a in fs]
    V=[P.from_dict({ds:fmpq(str(c)) for ds,c in K(a).numer.items()}) for a in gs]
    for j,e in enumerate(F):
        for k,d in enumerate(V):
            R=e.resultant(d,1).to_dict()
            pp=fmpq_poly([R.get((i,0),fmpq(0)) for i in range(1+max(x for x,y in R))])
            yield j,k,pp.factor()[1]

if __name__=='__main__':
    import json
    from pathlib import Path
    def normalized(ls):
        return sorted( (tuple(str(f/p[-1]) for f in p),e) for p,e in ls )
    out=[(j,k,normalized([(p.coeffs(),e) for p,e in R])) for j,k,R in residue_factors()]
    base=Path(__file__).with_name('resultant_factors.json')
    expected=[(j,k,normalized([([fmpq(c) for c in cs],e) for cs,e in rows]))
              for j,k,rows in json.loads(base.read_text())]
    assert out==expected
    print('all regular characteristic-zero projection factors match the literal archive')
