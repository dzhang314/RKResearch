#!/usr/bin/env python3
"""Directed exact rational bound for the real midpoint method's next bush."""
from fractions import Fraction as Q
from pathlib import Path
import json,runpy,sys

def check(D):
    W=D/'dirk12-fifteen-midpoint-degree216-field'
    F=json.loads((D/'dirk12-fifteen-rank3-invisible-midpoint-zero-fourth-projection'/'field.json').read_text())
    T=json.loads((W/'tower-data.json').read_text())
    C=runpy.run_path(str(W/'verify.py'))
    C['real'](F,T)
    I,hull,eva,moment=C['I'],C['hull'],C['eva'],C['moments']
    def iv(k):
        a,b,m=T['isolations'][k]
        return I(Q(a,m),Q(b,m))
    x,f,a=iv('x'),iv('f'),I(Q(1,2))
    y,t=[eva([Q(*r) for r in F[j]],x) for j in ('y','t')]
    P=hull(I,[I(0),I(1),1-a,1-a*x,1-a*y,1-a*t,1-f])
    s,p,u,_=moment(I,a,x,y,t,f)
    n=[sum(c/(i+j+1) for i,c in enumerate(P)) for j in range(6)]
    # S=P[(Y^2-sY+p)(Y-u)] with S monic degree ten.
    # Quadrature minus integral on (1-Y)^12 is minus integral(Y^2 S).
    delta=-13*(n[5]-(s+u)*n[4]+(p+s*u)*n[3]-p*u*n[2])
    D0,D1=Q(85680969483153,10**20),Q(85680969483154,10**20)
    assert D0<delta.l<=delta.r<D1 and D0>0
    print('positive scaled order-13 bush in (85680969483153,85680969483154)/10^20, both real orientations')

if __name__=='__main__':
    check(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent)
