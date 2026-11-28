#!/usr/bin/env python3
"""Generate compact inputs and six independent packed quotient receipts."""
from pathlib import Path
from build_univariate_moment_certificate import exact
import json,sys

def arr(a):return '['+','.join(map(str,a))+']'
def gen(src,where):
    d=exact(json.loads(src.read_text()))
    head='''module
public import RKCert.ReviewedNative.IntegerPolyRootReplay
@[expose] public section
namespace RKResearch.Certified.DIRK12Q36Moments
open IntegerPolyRootReplay
'''
    with (where/'DIRK12Q36MomentData.lean').open('w') as o:
        print(head,end='',file=o)
        for k in ('dy','dt','fd','den'):print(f'def {k} : Nat := {d[k]}',file=o)
        for k in ('Q','Y','T'):print(f'def {k} : ZP := {arr(d[k])}',file=o)
        for i,p in enumerate(d['f']):print(f'def F{i} : ZP := {arr(p)}',file=o)
        for j,(a,b) in enumerate(d['moments']):
            print(f'def nC{j} : ZP := {arr(a)}',file=o)
            print(f'def nX{j} : ZP := {arr(b)}',file=o)
        print('end RKResearch.Certified.DIRK12Q36Moments',file=o)
    for k,a in enumerate(d['divisors'],3):
        for j,p in enumerate(a):
            id=f'{k}{j}'
            t=f'''module
public import RKCert.ReviewedNative.DIRK12Q36PackedGatesCore
@[expose] public section
namespace RKResearch.Certified.DIRK12Q36Moments
open IntegerPolyRootReplay IntegerPolyRootReplay.Packing

def quotient{id} : ZP := {arr(p)}
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem pack{id} :
    Packing.read (base:Int) (gate R{k} {j}) = eval Q (base:Int)*eval quotient{id} (base:Int) := by
  decide +kernel

theorem bound{id} : bound (gate R{k} {j}) + norm Q * norm quotient{id} < base := by
  decide +kernel

theorem gate{id}_checked {{K : Type*}} [CommRing K] {{x : K}} (hx : eval Q x = 0) :
    Packing.read x (gate R{k} {j}) = 0 := quotient_from_packed x hx pack{id} bound{id}

end RKResearch.Certified.DIRK12Q36Moments

#print axioms RKResearch.Certified.DIRK12Q36Moments.gate{id}_checked
'''
            (where/f'DIRK12Q36PackedGate{id}.lean').write_text(t)
if __name__=='__main__':gen(Path(sys.argv[1]),Path(sys.argv[2]))
