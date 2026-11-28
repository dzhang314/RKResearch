#!/usr/bin/env python3
"""Tie the characteristic-zero formulas to the selected literal order-13 defect."""
from fractions import Fraction as Q
from pathlib import Path
import sys,json
from construct import construct,ghost_checks,ev,support

P=17
class E:
    def __init__(self,z):
        if isinstance(z,E): self.a=z.a;return
        if isinstance(z,(list,tuple)):
            assert len(z)==3 and all(0<=v<P for v in z)
            self.a=tuple(z);return
        q=Q(z);self.a=(q.numerator*pow(q.denominator,-1,P)%P,0,0)
    def __eq__(self,z):return self.a==E(z).a
    def __bool__(self):return any(self.a)
    def __add__(self,z):return E(tuple((a+b)%P for a,b in zip(self.a,E(z).a)))
    __radd__=__add__
    def __neg__(self):return E(tuple((-a)%P for a in self.a))
    def __sub__(self,z):return self+-E(z)
    def __rsub__(self,z):return E(z)+-self
    def __mul__(self,z):
        a0,a1,a2=self.a;b0,b1,b2=E(z).a
        c0=a0*b0;c1=a0*b1+a1*b0;c2=a0*b2+a1*b1+a2*b0
        c3=a1*b2+a2*b1;c4=a2*b2
        c1-=10*c4;c2-=3*c4;c3-=7*c4
        c0-=10*c3;c1-=3*c3;c2-=7*c3
        return E((c0%P,c1%P,c2%P))
    __rmul__=__mul__
    def __pow__(self,k):
        if k<0:
            assert self
            k%=P**3-1
        r=E(1);p=self
        while k:
            if k%2:r*=p
            k//=2
            if k:p*=p
        return r
    def __truediv__(self,z):return self*(E(z)**(-1))
    def __rtruediv__(self,z):return E(z)*(self**(-1))

def main():
    directory=Path(__file__).parent.parent
    fpath=(Path(sys.argv[1]) if len(sys.argv)>1 else directory/
           'dirk12-fifteen-rank3-invisible-midpoint-zero-fourth-projection'/'field.json')
    lpath=(Path(sys.argv[2]) if len(sys.argv)>2 else directory/
           'dirk12-fifteen-f17-cubic-midpoint-upper'/'tableau.json')
    F=json.loads(fpath.read_text());lit=json.loads(lpath.read_text())
    assert lit['base']==[10,3,7,1] and not lit['orientation']
    assert all((x**3+7*x*x+3*x+10)%P for x in range(P))
    assert F['x'][-1]%P
    a,x,y,t,f_norm,d,v=map(E,lit['midpoint']);f=a*f_norm
    assert a==Q(1,2) and x==E([0,1,0])
    assert not ev(F['x'],x)
    def exact(r):return ev([Q(*row) for row in r],x)
    assert y==exact(F['y']) and t==exact(F['t'])
    assert not ev([exact(row) for row in F['f']],f)
    _s,s,p,u=support(a,x,y,t,f)
    assert d+v==s and d*v==p and d!=v
    ghost_checks()
    A,b,c=construct(a,x,y,t,f,d,E)
    assert [[list(x.a) for x in row] for row in A]==lit['A']
    assert [list(x.a) for x in b]==lit['b'] and [list(x.a) for x in c]==lit['c']
    h=13*sum(m*z**12 for m,z in zip(b,c))-1
    assert h and list(h.a)==lit['scaled_order13_star']==[11,7,12]
    print("real construction formulas reduce to all 225 literal F17^3 entries, with exact order-13 bush defect 11+7z+12z^2")
if __name__=='__main__':main()
