#!/usr/bin/env python3
"""Exact padded 7+4 cut for both physical origin possibilities."""
from itertools import combinations
from pathlib import Path
import importlib.util

path = (Path(__file__).resolve().parent.parent
        / "dirk12-fifteen-rank3-four-singleton-end-exclusion" / "check.py")
spec = importlib.util.spec_from_file_location("lobatto", path)
fixed = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixed)


def main():
    assert tuple(z for z in range(fixed.P)
                 if fixed.ev(fixed.DERIVATIVE,z)==0) == fixed.ROOTS
    grid = (0,*fixed.ROOTS,1)
    n = 0
    for early in combinations(grid,4):
        late = tuple(z for z in grid if z not in early)
        for origin_is_ghost in (False, True):
            padded = (*early,0) if origin_is_ghost and 0 not in early else early
            F,G = fixed.hull(padded),fixed.hull(late)
            M = [[fixed.integrate(fixed.mul(fixed.sh(G,i),
                                    fixed.primitive(fixed.sh(F,j))))
                  for j in range(2)] for i in range(2)]
            assert fixed.rank(M,2)==2, (early, origin_is_ghost, M)
            n += 1
    assert n==70
    print("mod 1013: padded 7+4 cut rank two for all 70 cases")


if __name__=="__main__":
    main()
