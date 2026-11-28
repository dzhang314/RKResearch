#!/usr/bin/env python3
"""Exact literal 21-stage ordinary DIRK12 by six midpoint branches."""
from fractions import Fraction as Q
from math import factorial, lcm, prod
import json
from pathlib import Path

OUTPUT = Path(__file__).with_name("tableau21.json")

def build():
    branches = range(1, 7)
    branch_weights = [prod(Q(m*m,m*m-j*j) for j in branches if j!=m) for m in branches]
    A, b, c, branch_map = [], [], [], []
    for m, wm in zip(branches, branch_weights, strict=True):
        z = len(A)
        for j in range(m):
            row = [Q(0)]*21
            for k in range(j):
                row[z+k] = Q(1,m)
            row[z+j] = Q(1,2*m)
            A.append(row)
            b.append(wm/m)
            c.append(Q(2*j+1, 2*m))
            branch_map.append([m,j])
    DA = lcm(*(x.denominator for row in A for x in row))
    DB = lcm(*(x.denominator for x in b))
    assert all(sum(row)==x for row,x in zip(A,c,strict=True))
    assert sum(b)==1
    D = lcm(DA,DB)
    e = next(k for k in range(1,20) if factorial(12)**k%D==0)
    s = 13*sum(z*x**12 for z,x in zip(b,c,strict=True))-1
    z = [Q(1)]*21
    for _ in range(12):
        z=[sum(a*v for a,v in zip(row,z,strict=True)) for row in A]
    t = factorial(13)*sum(w*v for w,v in zip(b,z,strict=True))-1
    assert t==Q(-231,1024)
    packet = dict(stages=21,order=12,A=[[str(x) for x in row] for row in A],
                  b=list(map(str,b)),c=list(map(str,c)),branch_map=branch_map,
                  branch_weights=list(map(str,branch_weights)),
                  matrix_denominator=DA,weight_denominator=DB,common_denominator=D,
                  common_factorial_exponent=e,thirteenth_bush_defect=str(s),
                  thirteenth_tall_defect=str(t))
    return packet

def main():
    import argparse
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--emit",type=Path)
    options = p.parse_args()
    encoded = json.dumps(build(),separators=(",",":"))+"\n"
    if options.emit:
        options.emit.write_text(encoded,encoding="utf-8")
    else:
        assert OUTPUT.read_text(encoding="utf-8")==encoded
        print("Exact branch construction byte-matches the frozen tableau.")

if __name__=="__main__":
    main()
