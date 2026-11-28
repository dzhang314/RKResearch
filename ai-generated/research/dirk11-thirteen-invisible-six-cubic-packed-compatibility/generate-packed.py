#!/usr/bin/env python3
"""Generate a tiny kernel-arithmetic adapter for either frozen Bézout witness."""
import sys
from pathlib import Path
assert len(sys.argv)==4, "usage: generate-packed.py five-or-pair witness.txt output.lean"
chart,source,out=sys.argv[1:]
assert chart in ('five','pair')
R='Five' if chart=='five' else 'Pair'
name=f'DIRKOrderElevenInvisibleSixCubicLive{R}Packed'
F,G,d,U,V=[list(map(int,a.split())) for a in Path(source).read_text().splitlines()]
assert d==[1]
pp=103
width=27
b=1<<width
n=1+max(len(F)+len(U)-2,len(G)+len(V)-2)
coeffs=(F,G,U,V)
assert all(0<=c<pp for a in coeffs for c in a)
assert b>2*max(map(len,coeffs))*(pp-1)**2
def encode(a):return sum(c<<(i*width) for i,c in enumerate(a))
f,g,u,v=map(encode,coeffs)
a=f*u+g*v
assert a>>(width*n)==0
assert all(((a>>(width*i))%(1<<width))%pp==(1 if i==0 else 0)for i in range(n))
p=f'''/-! Staged packed Bézout arithmetic for the exact {chart} projection.
Each 27-bit input word is exactly one coefficient from the frozen
GF(103) witness. The generator verifies this conversion and absence
of carries separately. These receipts use only the Lean prelude. -/
namespace RKCert.ReviewedNative.{name}
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
'''
for nm,k in zip(('F','G','U','V','S'),(f,g,u,v,a)):
    p+=f'def {nm} : Nat := {hex(k)}\n'
p+='''
theorem multiplication : F*U+G*V=S := by decide
theorem constantDigit : (S % (2^27)) % 103 = 1 := by decide

def digits (n b : Nat) : Bool :=
  match n with
  | 0 => true
  | n+1 => ((b % (2^27)) % 103 == 0) && digits n (b >>> 27)
'''
for i in range(1,n,128):
    p+=f'\ntheorem digitBlock{i} : digits {min(128,n-i)} (S >>> {width*i}) = true := by decide\n'
p+=f'\ntheorem noRemainingDigits : (S >>> {width*n}) = 0 := by decide\n'
p+=f'\nend RKCert.ReviewedNative.{name}\n'
Path(out).write_text(p)
