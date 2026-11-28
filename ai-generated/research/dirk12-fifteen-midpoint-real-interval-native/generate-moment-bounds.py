#!/usr/bin/env python3
"""Propose convenient outer dyadic-style rational bounds; Lean rechecks them."""
from fractions import Fraction as Q
from pathlib import Path
import sys,runpy,json

def run(R,out):
    W=R/'dirk12-fifteen-midpoint-degree216-field'
    F=json.loads((R/'dirk12-fifteen-rank3-invisible-midpoint-zero-fourth-projection'/'field.json').read_text())
    T=json.loads((W/'tower-data.json').read_text())
    C=runpy.run_path(str(W/'verify.py'));I,hull,ev=C['I'],C['hull'],C['eva']
    def iv(k):
        a,b,m=T['isolations'][k];return I(Q(a,m),Q(b,m))
    x,f,a=iv('x'),iv('f'),I(Q(1,2));y,t=[ev([Q(*r) for r in F[j]],x) for j in ('y','t')]
    rs=[I(0),I(1),1-a,1-a*x,1-a*y,1-a*t,1-f]
    # Match the formal recursive moment; the direction-only width is irrelevant.
    def mm(rs,k):
        if not rs:return I(Q(1,k+1))
        return mm(rs[1:],k+1)-rs[0]*mm(rs[1:],k)
    D=10**40
    outboxes=[]
    for k in range(6):
        a,b=mm(rs,k).l*D,mm(rs,k).r*D
        al=a.numerator//a.denominator-1
        br=-((-b.numerator)//b.denominator)+1
        outboxes.append((al,br))
    with out.open('w') as o:
        print('''module

public import RKCert.ReviewedNative.DIRK12MidpointRealIntervalData

@[expose] public section

namespace RKResearch.Certified.DIRK12MidpointRealInterval
open DirectedRatBox

def bounds : Fin 6 → Box := fun i =>
  match i.val with''',file=o)
        for j,(u,v) in enumerate(outboxes):
            p=str(j) if j<5 else '_'
            print(f'  | {p} => ⟨{u}/{D},{v}/{D}⟩',file=o)
        print('\nend RKResearch.Certified.DIRK12MidpointRealInterval',file=o)

if __name__=='__main__':
    run(Path(sys.argv[1]),Path(sys.argv[2]))
