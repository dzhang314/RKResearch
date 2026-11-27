#!/usr/bin/env python3
"""Generate the complementary rational tableau from the cubic two-pair atlas."""
from fractions import Fraction as F
from math import lcm
from pathlib import Path
import sys,json

# This neighboring file is the exact two-pair solver with the scalar
# quadrature requirement set to degree eight (to target order nine).
from reverse_construction import Q,orientation,seed,tail

def make():
    nodes=list(map(Q,("-3","3/17","1/2","3/5","5/6")))
    block=orientation(nodes)
    assert block is not None
    opening=seed("3/10","3/4","4/5","1/10",block[-3])
    assert opening is not None
    data=tail(block,opening)
    assert data is not None
    A,b,L,tau,ell,f,Pi,H=data
    assert all(not q.b for r in A for q in r) and all(not q.b for q in b)
    D=lcm(*(q.a.denominator for r in A for q in r),*(q.a.denominator for q in b))
    assert D==44115870234031229210137015593600
    return {"den":D,"A":[[str(q.a)for q in r[:i]]for i,r in enumerate(A)],
       "b":[str(q.a)for q in b],"nodes":[str(q.a)for q in nodes],
       "reverse_L":[[str(q.a)for q in row]for row in L],
       "pressure_root":str(tau.a),"third_donor_tap":str(f.a),
       "donor_annihilator":[str(x.a)for x in ell],
       "fallback_residue_characteristics":[13,19,47]}
if __name__=="__main__":
    out=json.dumps(make(),indent=2)+"\n"
    if len(sys.argv)>1:
        Path(sys.argv[1]).write_text(out)
    else:
        assert out==Path(__file__).with_name("tableau.json").read_text()
    print("Complementary rational tableau reproduced byte for byte.")
