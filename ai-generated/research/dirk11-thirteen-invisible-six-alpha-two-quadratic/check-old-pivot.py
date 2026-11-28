#!/usr/bin/env python3
"""Cross-check the singular input polynomial and the three alternate roots."""
from pathlib import Path
from runpy import run_path
import ast
from argparse import ArgumentParser
import sympy as S
H=Path(__file__).resolve().parent
arg=ArgumentParser()
arg.add_argument('--early',type=Path,
                 default=H.parent/'dirk11-thirteen-invisible-six-early-profile-census/project.py')
scope=run_path(str(arg.parse_args().early))
c0,c1,c2,s,r,F1,F2,Fn,D,A1=(scope[k]for k in ('c0','c1','c2','s','r','F1','F2','Fn','D','A1'))
A1terms=next(x for x in ast.parse((H/'singular.py').read_text()).body
             if isinstance(x,ast.Assign) and isinstance(x.targets[0],ast.Name)
             and x.targets[0].id=='A1_TERMS')
terms=ast.literal_eval(A1terms.value)
assert S.expand(sum(n*c0**i*c1**j*c2**k*s**l for (i,j,k,l),n in terms)
                - S.cancel(-10*c0*A1))==0
ds=[
 (15*(c2*s-c0)/(16*s),3*(c2*s-c0)*F1/(256*s*s)),
 ((c2*s-c0)/s,(c2*s-c0)*F2/(s*s)),
 (6*c2*s/(c1+6*s),3*s*Fn/(c1+6*s)**2)
]
for rr,target in ds:
    assert S.cancel(D.subs(r,rr)-target)==0
assert S.expand(Fn.subs(c2,0)+c0*(c1+6*s)**2)==0
assert S.expand(D.subs({c2:0,c1:-6*s})-(c0*r*r+4*s*s*r-3*c0*s))==0
print('exact source of the A1 coefficients and the three known D-roots audited')
