#!/usr/bin/env python3
"""Replay algebraic-prefix ERK10 prime families and check unit pressure derivatives."""
import argparse
import json
from pathlib import Path
import sys

D = Path(__file__).resolve().parent
sys.path.insert(0, str(D.parent / "erk10-sixteen-small-prime-portfolio"))
from build import chart, decode, solve
from residue import M

PREFIX = decode(D.parent / "erk10-sixteen-17-power-lift" / "prefix-algebraic.json")
RULE = lambda t: 3*t*t-15*t+20
INDICES = (0, 3, 5)

def run(row, exponent, output):
    p, omit, x0, x2, defect1, defect2, det = row
    pick = tuple(j for j in range(6) if j != omit)
    def call(x, m, emit=False, guard=None):
        return chart(x, m, p, pick, emit, guard, prefix=PREFIX, theta_rule=RULE)
    assert call(x0, p)[0] == (0, 0, 0)
    f0, _ = call(x0, p*p)
    cols = []
    for k in INDICES:
        t = list(x0)
        t[k] += p
        f, _ = call(t, p*p)
        ds = [a-b for a,b in zip(f,f0)]
        assert all(a%p==0 for a in ds)
        cols.append([(a//p)%p for a in ds])
    J = [list(z) for z in zip(*cols)]
    D0 = (J[0][0]*(J[1][1]*J[2][2]-J[1][2]*J[2][1])
          - J[0][1]*(J[1][0]*J[2][2]-J[1][2]*J[2][0])
          + J[0][2]*(J[1][0]*J[2][1]-J[1][1]*J[2][0]))
    assert D0 % p == det and det != 0
    a, x = p, list(x0)
    for e in range(1, exponent+1):
        if e > 1:
            f, _ = call(x, a*p)
            assert all(i%a==0 for i in f)
            M.p = p
            dy = solve([[M(c) for c in z] for z in J], [-M(i//a) for i in f], p)
            for k,y in zip(INDICES,dy):
                x[k] += a*int(y)
            a *= p
        guard = {}
        A, b, defect, _ = call(x,a,True,guard)
        assert defect % p == defect1
        if e == 1:
            print(p, "omitted row", omit, "Jacobian", J, "det", det,
                  "base guards", json.dumps(guard,sort_keys=True))
        if e == 2:
            assert x == x2 and defect == defect2
        print(p, e, "checked all 1205 conditions; next bush defect", defect, flush=True)
        literal = dict(prime=p, exponent=e, modulus=a, parameters=x,
                       A=[[int(t) for t in r[:i]] for i,r in enumerate(A)],
                       b=list(map(int,b)), bush_failure=defect)
        if output:
            (output/f"mod{p}pow{e}.json").write_text(json.dumps(literal,indent=2)+"\n")

if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--exponent",type=int,default=2)
    ap.add_argument("--emit",type=Path)
    args = ap.parse_args()
    if args.emit:
        args.emit.mkdir(exist_ok=True,parents=True)
    for row in json.loads((D/"seeds.json").read_text()):
        run(row,args.exponent,args.emit)
