#!/usr/bin/env python3
"""Exact two-cut plane obstruction for a single doubled-amplitude clock."""
from itertools import permutations
from pathlib import Path
import importlib.util

path = (Path(__file__).resolve().parent.parent
        / "dirk12-fifteen-rank3-four-singleton-end-exclusion" / "check.py")
spec = importlib.util.spec_from_file_location("lobatto", path)
fixed = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixed)
P = fixed.P


def cross(u,v):
    return [(u[(j+1)%3]*v[(j+2)%3]-u[(j+2)%3]*v[(j+1)%3])%P for j in range(3)]


def normals(g):
    F,G = fixed.hull(g[:3]),fixed.hull(g[4:])
    F4,G4 = (fixed.mul(h,[-g[3],1]) for h in (F,G))
    M = [[fixed.integrate(fixed.mul(fixed.sh(G4,i),fixed.primitive(fixed.sh(F,j))))
          for j in range(3)] for i in range(2)]
    Nt = [[fixed.integrate(fixed.mul(fixed.sh(G,i),fixed.primitive(fixed.sh(F4,j))))
           for i in range(3)] for j in range(2)]
    return cross(*M),cross(*Nt)


def main():
    assert tuple(z for z in range(P) if fixed.ev(fixed.DERIVATIVE,z)==0) == fixed.ROOTS
    for xs in permutations(fixed.ROOTS):
        u,v = normals((0,*xs,1))
        assert any(u) and any(v)
        assert fixed.rank(fixed.mac_rows((u,v),3),4)==4
    print("mod 1013: both plane ranks two and binary degree-three rank four, all 120 orders")


if __name__ == "__main__":
    main()
