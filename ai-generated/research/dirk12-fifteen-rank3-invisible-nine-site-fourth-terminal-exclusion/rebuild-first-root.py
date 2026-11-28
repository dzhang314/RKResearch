#!/usr/bin/env python3
"""Characteristic-zero first-root e=1 projection over Q and a quartic."""
import json
from pathlib import Path
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

aa=S.Symbol('a')
H=66*aa**4-132*aa**3+84*aa*aa-18*aa+1
K=QQ.alg_field_from_poly(S.Poly(H,aa),alias='aa')
def L(t):
    return 5544*t**5-13860*t**4+12600*t**3-5040*t*t+840*t-42
def coefficient(v):
    cs=v.to_list()[::-1] if hasattr(v,'to_list') else [v]
    return [[int(c.numerator),int(c.denominator)] for c in cs]
def packet(F,a):
    R,y,x=ring('y,x',F)
    D=2*x*y-x-3*y*y+2*y
    S0=3*x*x-2*x*y-2*x+y
    t=F.one/a
    P=[0,-x*y,x+y+x*y,-(1+x+y),1]
    J=lambda j,z:sum(c*z**(i+j+1)/(i+j+1) for i,c in enumerate(P))
    I0=J(0,F.one);I1=J(1,F.one)
    raw=x*x*(x-1)**3*D*L(a*y)+y*y*(y-1)**3*S0*L(a*x)
    g=raw.exquo((y-1)*(y-x))
    e=60*a*L(a*x)*(I0*J(1,t)-I1*J(0,t))-7*x*x*(x-1)**3*D
    assert g.degrees()==(5,6) and e.degrees()==(2,7)
    sr=g.subresultants(e)
    n,ab=sr[-1],sr[-2]
    assert n.degrees()==(0,47) and ab.degrees()==(1,34)
    A=R.from_dict({(0,k):c for (j,k),c in ab.items() if j==1})
    B=R.from_dict({(0,k):c for (j,k),c in ab.items() if j==0})
    guard=(5*x*x-5*x+1)*(x-1)*(x-t)*L(a*x)
    keep=[];counts=[]
    for f,m in n.factor_list()[1]:
        if f.degree(x)==20:
            assert m==1
            keep.append(f)
        elif f.gcd(guard).degree(x)==f.degree(x):
            counts.append([f.degree(x),m])
        else:
            assert f.degree(x)==5 and m==1 and A.gcd(f)==R.one and not (A*t+B).rem(f)
            counts.append(["actual y=t"])
    assert len(keep)==1
    print("first-root field",F,": degree20 retained; exact discarded factors",counts)
    def coeff(p):
        assert all(j==0 for j,i in p)
        return [coefficient(p.get((0,i),F.zero)) for i in range(p.degree(1)+1)]
    return {"base":coeff(keep[0]),"lead":coeff(A),"constant":coeff(B)}

def main():
    assert S.expand(L(aa)-42*(2*aa-1)*H)==0
    data=dict(half=packet(QQ,QQ(1,2)),quartic=packet(K,K.unit))
    dest=Path(__file__).with_name('first-root-projection.json')
    out=json.dumps(data,separators=(',',':'))+'\n'
    if dest.exists():assert dest.read_text()==out
    else:dest.write_text(out)
if __name__=="__main__":main()
