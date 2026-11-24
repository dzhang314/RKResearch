#!/usr/bin/env python3
"""Match the emitted literal Lean numerators to the reconstructed Lobatto tableau."""
import json,re,sys
from pathlib import Path
lean,j=map(Path,sys.argv[1:])
text=lean.read_text(); P=json.loads(j.read_text())
assert [int(re.search(r"^def "+name+r" : ℤ := (\d+)$",text,re.M)[1])
            for name in ("stageDen","weightDen")]==[P["stageDen"],P["weightDen"]]
A,B={},{}

a=text.split("def rawA ")[1].split("def rawB ")[0]
for i,j,r,v in re.findall(r"^  \| (\d+), (\d+) => pair \((-?\d+)\) \((-?\d+)\)$",a,re.M):
    key=(int(i),int(j)); assert 0<=key[1]<=key[0]<8 and key not in A
    A[key]=[int(r),int(v)]
assert a.count(" => pair ")==len(A) and a.count("=> QExpr.zero")==1

b=text.split("def rawB ")[1].split("def Vec ")[0]
for i,r,v in re.findall(r"^  \| (\d+) => pair \((-?\d+)\) \((-?\d+)\)$",b,re.M):
    key=int(i); assert 0<=key<8 and key not in B
    B[key]=[int(r),int(v)]
assert b.count(" => pair ")==len(B) and b.count("=> QExpr.zero")==1

z=[0,0]
for i in range(8):
    for j in range(8):
        assert A.get((i,j),z)==P["A"][i][j],(i,j)
    assert B.get(i,z)==P["b"][i],i
print("All 64 literal stage entries and eight literal weights match in the 1,sqrt(21) basis.")
