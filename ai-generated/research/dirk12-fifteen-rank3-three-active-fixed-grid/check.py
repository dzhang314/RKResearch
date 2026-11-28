#!/usr/bin/env python3
"""Exact rank cut for the three-label cases with exactly seven candidate clocks."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import importlib.util

path = (Path(__file__).resolve().parent.parent
        / "dirk12-fifteen-rank3-four-singleton-end-exclusion" / "check.py")
spec = importlib.util.spec_from_file_location("lobatto", path)
fixed = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixed)

EXPECTED = {(2,0):210, (1,0):665, (1,1):140, (0,0):546, (0,1):210}


def paid_cut(early, late, holes):
    q = len(holes)
    f, g = fixed.hull((*early,*holes)), fixed.hull((*late,*holes))
    columns, rows = 6-q-len(early), 6-q-len(late)
    m = [[fixed.integrate(fixed.mul(fixed.sh(g,i),fixed.primitive(fixed.sh(f,j))))
          for j in range(columns)] for i in range(rows)]
    return fixed.rank(m, columns)


def main():
    D, P, roots = fixed.DERIVATIVE, fixed.P, fixed.ROOTS
    assert tuple(z for z in range(P) if fixed.ev(D,z)==0) == roots
    grid = (0,*roots,1)
    count = Counter()
    for q,g,cut in ((2,0,2),(1,0,3),(1,1,3),(0,0,4),(0,1,4)):
        for holes in combinations(grid,q):
            C = tuple(z for z in grid if z not in holes)
            for a in range(1,cut+1):
                for early in combinations(C,a):
                    max_late = 15-(6+2*q)-g-cut
                    for b in range(max(1,len(C)-a),max_late+1):
                        for late in combinations(C,b):
                            if len(set(early)|set(late)) != len(C):
                                continue
                            assert paid_cut(early,late,holes)>g, (q,g,early,late,holes)
                            count[q,g]+=1
    assert dict(count)==EXPECTED, count
    for (q,g),c in count.items():
        print(f"q={q}, zero weights={g}: {c} fixed-grid cases, each cut rank > {g}")


if __name__ == "__main__":
    main()
