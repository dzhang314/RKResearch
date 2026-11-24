#!/usr/bin/env python3
"""Compare the emitted Lean numerator data to the exact archived replay table."""
import json, re, sys
from pathlib import Path

lean, src = map(Path, sys.argv[1:])
text = lean.read_text()
tableau = json.loads(src.read_text())

def ints(raw):
    return [int(s) for s in raw.split(",") if s.strip()]

def crop(x):
    x = list(x)
    while x and x[-1] == 0:
        x.pop()
    return x

def limb(raw):
    raw=raw.strip()
    if raw.startswith("("):
        assert raw.endswith(")")
        raw=raw[1:-1]
    if raw.startswith(".atom"):
        m=re.fullmatch(r"\.atom \[([-\d,\s]*)\]",raw)
        return ints(m[1])
    m=re.fullmatch(r"\.mul \(\.atom \[(-?\d+)\]\) \(\.atom \[([-\d,\s]*)\]\)",raw)
    return [int(m[1])*c for c in ints(m[2])]

def decode(raw):
    assert raw.startswith("⟨") and raw.endswith("⟩")
    raw=raw[1:-1]
    n=0; pos=[]
    for i,c in enumerate(raw):
        if c in "([":
            n+=1
        elif c in ")]":
            n-=1
        elif c=="," and n==0:
            pos.append(i)
    assert n==0 and len(pos)==1
    i=pos[0]
    return [crop(limb(raw[:i])),crop(limb(raw[i+1:]))]

p=re.search(r"^def innerMod : List ℤ := \[([-\d,\s]+)\]$",text,re.M)
assert ints(p[1])==tableau["innerPolynomialAscending"]
for k in ("stageDen","weightDen"):
    assert int(re.search(r"^def "+k+r" : ℤ := (\d+)$",text,re.M)[1])==tableau[k]
assert tableau["outerSquare"]==7 and "(hy : y^2 = 7)" in text

stage=text.split("def rawA ")[1].split("def rawB ")[0]
weight=text.split("def rawB ")[1].split("def Vec ")[0]
A={};b={}
for i,j,s in re.findall(r"^  \| (\d+), (\d+) => (⟨.*⟩)$",stage,re.M):
    key=(int(i),int(j)); assert 0<=key[1]<=key[0]<10 and key not in A
    A[key]=decode(s)
for i,s in re.findall(r"^  \| (\d+) => (⟨.*⟩)$",weight,re.M):
    key=int(i); assert 0<=key<10 and key not in b
    b[key]=decode(s)
assert stage.count("=> ⟨")==len(A) and stage.count("=> QExpr.zero")==1
assert weight.count("=> ⟨")==len(b) and weight.count("=> QExpr.zero")==1
zero=[[],[]]
for i in range(10):
    for j in range(10):
        assert A.get((i,j),zero)==list(map(crop,tableau["A"][i][j])),(i,j)
    assert b.get(i,zero)==list(map(crop,tableau["b"][i])),i
print("All 100 stage entries and ten weights match the exact archived quartic/quadratic tableau.")
print("Both relations and both denominator factors match.")
