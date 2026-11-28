#!/usr/bin/env python3
"""Generate small ordinary-kernel arithmetic receipts, never native_decide."""
from pathlib import Path
import argparse
here=Path(__file__).resolve().parent
p=argparse.ArgumentParser()
p.add_argument('--lean',type=Path,default=here.parent.parent/'lean/RKCert/ReviewedNative')
cfg=p.parse_args(); out=cfg.lean
stem='DIRK11Width14Integer'
ns='RKResearch.Certified.'+stem+'Checks'
dims=[0,0,0,1,2,3,5,8,11,12,13]

def make(tail,text,imports=None,extra=''):
    if imports is None:imports=[stem+'Blocks']
    s='module\n\n'+''.join('public import RKCert.ReviewedNative.'+i+'\n'for i in imports)+extra
    s+=f'\n@[expose] public section\nnamespace {ns}\nopen {stem}Core {stem}Data\n'
    s+='set_option maxHeartbeats 0\nset_option maxRecDepth 50000\n\n'+text+'\nend '+ns+'\n'
    (out/(stem+tail+'.lean')).write_text(s)

make('Blocks','''
def blockARow (d i : Nat) : Bool :=
  if hi : i < packet.size d then checkA packet d ⟨i,hi⟩ else true
def blockC (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkC packet d)
def blockS (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkSilent packet d)
def blockP (d e : Nat) : Bool := (List.finRange (packet.size d)).all fun i =>
  (List.finRange (packet.size e)).all (checkProduct packet d e i)
''',[stem+'Data'])

parts=[]
def batch(s,ts):
    make(s,'\n'.join('theorem '+n+' : '+v+' = true := by decide +kernel' for n,v in ts))
    parts.append(stem+s)

batch('BitsBase',[('chk_node','checkNode packet'),('chk_failure','checkFailure packet')])
for d in range(3,10):
    size=dims[d]
    for i in range(0,size,2 if d>=6 else 3):
        batch(f'BitsA{d}From{i}',
              [(f'chk_a{d}_{j}',f'blockARow {d} {j}')for j in range(i,min(size,i+(2 if d>=6 else 3)))])
for i in range(0,11,3):
    batch('BitsCS'+str(i),[(f'chk_c{j}',f'blockC {j}')for j in range(i,min(10,i+3))]+[(f'chk_s{j}',f'blockS {j}')for j in range(i,min(11,i+3))])
cp = """
theorem eqV_identity {u v : V} (ok : eqV u v = true) : u=v :=
  funext fun i => of_decide_eq_true (List.all_eq_true.mp ok i (List.mem_finRange i))

theorem pow_zero_checked : litPow 0 = one := by
  apply eqV_identity
  decide +kernel
"""
for d in range(10):
    cp+=f"theorem pow_at{d} : litPow {d+1} = mulV packet (litPow {d}) (node packet) := by\n"
    cp+="  apply eqV_identity\n  decide +kernel\n"
cp+="""
theorem pow_lit_next (d : Nat) (hd : d < 10) :
    litPow (d+1) = mulV packet (litPow d) (node packet) := by
  interval_cases d
"""+''.join(f'  · exact pow_at{d}\n'for d in range(10))
cp+="""
theorem pow_checked (d : Nat) (hd : d ≤ 10) : powC packet d = litPow d := by
  induction d with
  | zero => exact pow_zero_checked.symm
  | succ d ih =>
    have r : powC packet (d+1) = mulV packet (powC packet d) (node packet) := rfl
    rw [r,ih (by omega),←pow_lit_next d (by omega)]
"""
make('PowCache',cp,[stem+'PowData'],'import Mathlib.Tactic.IntervalCases\n')
for i in range(0,11,2):
    n='BitsQ'+str(i)
    r=''
    for j in range(i,min(11,i+2)):
        r+=f"theorem chk_q{j} : checkScalar packet {j} = true := by\n"
        r+=f"  unfold checkScalar\n  rw [pow_checked {j} (by decide)]\n  decide +kernel\n"
    for j in range(i,min(10,i+2)):
        r+=f"theorem chk_h{j} : checkPrimitive packet {j} = true := by\n"
        r+=f"  unfold checkPrimitive primitiveV\n  rw [pow_checked {j} (by decide),pow_checked {j+1} (by decide)]\n  decide +kernel\n"
    make(n,r,[stem+'PowCache'])
    parts.append(stem+n)
for d in range(3,8):
    batch('BitsP'+str(d),[(f'chk_p{d}_{e}',f'blockP {d} {e}')for e in range(3,11-d)])
g=''

def enumer(name,ts,limit,fn):
    return f'theorem {name} (d : Nat) (hd : d < {limit}) : {ts} = true := by\n  interval_cases d\n'+''.join('  · exact '+fn(j)+'\n'for j in range(limit))+'\n'

for name,ts,limit,fn in [('allC','blockC d',10,'chk_c'),('allS','blockS d',11,'chk_s'),
    ('allQ','checkScalar packet d',11,'chk_q'),('allH','checkPrimitive packet d',10,'chk_h')]:
    g+=enumer(name,ts,limit,lambda r:fn+str(r))
g+="""theorem allA (d : Nat) (hd : d < 10) (i : Fin (packet.size d)) :
    checkA packet d i = true := by
  have hi := i.isLt
  have row (h : blockARow d i.val = true) : checkA packet d i = true := by
    simpa [blockARow,hi] using h
  apply row
  interval_cases d
"""
for d in range(10):
    if dims[d]:
        g+=f'  · change i.val < {dims[d]} at hi\n    interval_cases i.val\n'
        g+=''.join(f'    · exact chk_a{d}_{j}\n'for j in range(dims[d]))
    else:g+='  · change i.val < 0 at hi\n    omega\n'
g+="""
theorem allP (d e : Nat) (h : d+e < 11) : blockP d e = true := by
  have hn : d < 11 := by omega
  interval_cases d
"""
for d in range(11):
    if not dims[d]:
        g+='  · rfl\n'
    else:
        g+=f'  · have he : e < {11-d} := by omega\n    interval_cases e\n'
        g+=''.join(f'    · exact chk_p{d}_{e}\n'if dims[e] else '    · decide +kernel\n'for e in range(11-d))
g+="""
theorem receipts : Receipts packet := by
  refine ⟨chk_node,allA,?_,?_,allH,?_,allQ,chk_failure⟩
  · intro d hd i
    exact List.all_eq_true.mp (allC d hd) i (List.mem_finRange i)
  · intro d e hd i j
    exact List.all_eq_true.mp
      (List.all_eq_true.mp (allP d e hd) i (List.mem_finRange i)) j (List.mem_finRange j)
  · intro d hd i
    exact List.all_eq_true.mp (allS d hd) i (List.mem_finRange i)
"""
make('Receipts',g,parts,'import Mathlib.Tactic.IntervalCases\n')
