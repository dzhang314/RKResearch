#!/usr/bin/env python3
"""The one p20 continuation; no alternate pair, point scan or big fractions."""
import contextlib
import io
import runpy
import sys
from pathlib import Path

here=Path(__file__).resolve().parent
p19=here/"verify-targeted-p19.py"
saved_argv=sys.argv[:]
try:
    sys.argv=[str(p19),*saved_argv[1:]]
    with contextlib.redirect_stdout(io.StringIO()) as s:
        V=runpy.run_path(str(p19))
finally:
    sys.argv=saved_argv

I,F,Q=V["I"],V["F"],V["Q"]
split,replace,need=V["split"],V["replace_named"],V["need"]
u,v,d,a,b=V["i2"]
uF,vF,dF,aF,bF=V["m2"]
labels,xs=V["l19"],V["x19"]
labF,xsF=V["l19F"],V["x19F"]
need(V["h19"]==1698450493 and len(xs)==17 and V["p2"]==("9b","9a"),"exact p19 provider and pair")
print("Pinned exact interval order 19, 17 sites, h19 mod q=1698450493; next pair 9b,9a.")
print("Next pair exact nontorsion model and multiples mod q:",V["ec_cert"](F,aF,bF))
rf=V["triple"](I,u,d,a,b)
need(rf[0].negative(),"rank-free route exterior")
print("Rank-free triple enclosures (10^6 scaled):",[x.bracket() for x in rf])
# Target phase near 21/142 using 141/142 as an approximation to phi(2D).
# The shorter signed representative avoids a larger group chain.
k=21*pow(141,-1,142)%142-142
need(k==-21,"the one prescribed group congruence")
m=2*k
new,tau,P,c=split(I,u,v,d,a,b,m)
newF,tauF,PF,cF=split(F,uF,vF,dF,aF,bF,m)
need(c==cF==(5,2),"literal next signed point group chain")
need(tau.between(I.c(1,2),I.c(7,10)) and all(x.between(I.c(0),I.c(1)) for x in new),
     "actual exact inside roots and physical tau")
less=V["less"]
need(less(v,new[0]) and less(u,new[1]) and less(new[1],v) and less(new[2],u),
     "selected ordering right,middle,left")
print(f"One targeted [{m}]D, binary chain doubles/adds={c}; E mod q:",tuple(x.x for x in PF))
print("Actual physical tau and branch triple enclosures:",tau.bracket(),[x.bracket() for x in new])
l20,x20=replace(labels,xs,new,"9b","9a",10)
l20F,x20F=replace(labF,xsF,newF,"9b","9a",10)
need(l20==l20F and len(l20)==18 and all(l in l20 for l in ("m3","p3")),"eighteen labels, retained endpoints")
h20=V["exact_checks"](F,x20F)
need(h20==240109312,"literal order-20 first failure")
print("PASS exact interval order 20 / 18 contributing sites; first defect mod q =",h20)
