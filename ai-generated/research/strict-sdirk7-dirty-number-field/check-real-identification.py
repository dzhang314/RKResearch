#!/usr/bin/env python3
"""Check the real tableau isolated earlier is exactly the endpoint's real embedding."""
from pathlib import Path
from importlib.util import spec_from_file_location, module_from_spec
from fractions import Fraction
from math import prod
from flint import fmpq,fmpz_poly
import argparse
import json

parser=argparse.ArgumentParser()
parser.add_argument("--work-dir",type=Path,default=Path(".projection-work"))
args=parser.parse_args()
here=Path(__file__).resolve().parent
spec=spec_from_file_location("box",here.parent/'strict-sdirk7-real-dirty'/'check-real-box.py')
box=module_from_spec(spec)
spec.loader.exec_module(box)
I=box.I

def iv(t):
    q=fmpq(t)
    return I(Fraction(int(q.numerator),int(q.denominator)))

z,a,b,c,h=(I(q-box.RADIUS,q+box.RADIUS) for q in box.CENTER)
base=(z,c,a+b)
def sign_on_box(poly):
    n=[max(t[j] for t in poly) for j in range(3)]
    pp=[[v**e for e in range(k+1)] for v,k in zip(base,n)]
    return sum(iv(w)*pp[0][i]*pp[1][j]*pp[2][k] for i,j,k,w in poly)

cut=json.loads((args.work_dir/'chart-cuts.json').read_text())
other=json.loads((args.work_dir/'projection-cuts.json').read_text())
assert all(sign_on_box(a).nz() for a in list(cut.values())+other)
print("all local elimination scales and discarded factors remain nonzero on the certified real box")
H=fmpz_poly([int(x) for x in json.loads((here/'primitive-z-degree-324.json').read_text())])
O=fmpz_poly([int(x) for x in json.loads((args.work_dir/'integer-projection.json').read_text())])
assert O%H==0
other=O//H
cen=fmpq(box.CENTER[0].numerator,box.CENTER[0].denominator)
r=fmpq(box.RADIUS.numerator,box.RADIUS.denominator)
length=abs(cen)+r
co,sq=other.factor_squarefree()
assert co*prod(A**j for A,j in sq)==other
for A,j in sq:
    a=abs(A(cen))
    derivative_majorant=fmpz_poly([abs(v) for v in A.derivative()])(length)
    assert a>r*derivative_majorant
print("every squarefree layer of the complementary projection is nonzero throughout the real isolator")
print("the prior exact real solution lies on H; the primitive formula identifies it with the real embedding")
