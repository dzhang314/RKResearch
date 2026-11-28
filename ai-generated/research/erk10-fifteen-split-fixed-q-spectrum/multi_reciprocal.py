"""Exact rational slice closure; no height cap on d,e,a,b in any listed row."""
from reciprocal import F, S, ring, t, scalar_slice
from unified import matrix, sumprod

slices=[
  ("1/2","2/3","1/4"),("1/2","1/4","2/3"),("2/3","1/2","3/4"),
  ("2/3","3/4","1/2"),("1/2","1/3","2/3"),("2","1/2","3/4"),
  ("-1","1/2","3/4"),("-2","-1","1/4")
]
for row in slices:
    D,degs,gcd,H,rs=scalar_slice(*map(F,row))
    assert not D["origin"]
    pivot=S.Poly(ring.to_sympy(D["Delta"]),t,domain=S.QQ)
    assert not pivot.ground_roots()
    for z in rs:
        assert z!=0 and sumprod(matrix(D,F(z)))[1]==0
    print("c,g,R =",",".join(row), "| pivot: no rational root;",
          "residual rational τ:", ",".join(map(str,rs)) or "none",
          "| every listed τ forces ab=0" if rs else "| slice closed")
