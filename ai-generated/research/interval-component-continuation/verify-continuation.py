#!/usr/bin/env python3
"""At most four prescribed adjacent fresh moves; first nonpassing gate stops."""
import contextlib
import io
import runpy
import sys
from pathlib import Path
from time import monotonic

source=Path(sys.argv[1]).resolve() if len(sys.argv)==2 else (
    Path(__file__).resolve().parent.parent/"interval-real-pencil/verify-interval-pencil.py")
began=monotonic()
with contextlib.redirect_stdout(io.StringIO()) as previous_output:
    D=runpy.run_path(str(source))
if "Explicit exact order 16: 14 contributing interval sites; first defect mod q = 1366411467" not in previous_output.getvalue():
    raise AssertionError("unexpected checked order-16 provider")
I,F,Q=D["I"],D["F"],D["Q"]
params,moment,nodal,data=D["cubic_parameters"],D["moment"],D["nodal"],D["c_data"]
replace,real_window,triple=D["interval_replace"],D["real_window"],D["triple"]
exact_checks,ec_cert=D["exact_checks"],D["ec_cert"]
zl,zr=I.c(0),I.c(1)

prior_labels,prior=D["labI"],D["xsI"]
last_u,last_v,_,_,_=params(prior,prior_labels,I,D["ul2"],D["vl2"])
hprev=data(prior,I)[0]
labels,xs,fresh=replace(I,prior_labels,prior,D["ul2"],D["vl2"],6)
labmod,xmod=D["labM2"],D["xsM2"]
if labels!=labmod or exact_checks(F,xmod)!=1366411467:
    raise AssertionError("order16 model pin")
last_verified=16


class Stop(Exception):
    pass


def gate(b, tag):
    if not b:
        raise Stop(tag)


def strictly_less(a,b):
    return a.u < b.l


def ordered_fresh(last_left,last_right,fresh_values,fresh_labels):
    left=[l for l,x in zip(fresh_labels,fresh_values) if strictly_less(x,last_left)]
    mid=[l for l,x in zip(fresh_labels,fresh_values)
         if strictly_less(last_left,x) and strictly_less(x,last_right)]
    right=[l for l,x in zip(fresh_labels,fresh_values) if strictly_less(last_right,x)]
    gate([len(left),len(mid),len(right)]==[1,1,1],"fresh sorted branches unavailable")
    return left[0],mid[0],right[0]


print("Pinned exact interval order 16 / 14 active sites. Tests: at most four sign-selected fresh pairs.")
print("All numeric buckets are outward bounds scaled by 10^6.")
for j in range(7,11):
    step_started=monotonic()
    order=j+10
    try:
        gate(step_started-began<8, "total foreground stop")
        h=data(xs,I)[0]
        delta=h/hprev
        gate(delta.positive() or delta.negative(),"defect-ratio sign not proved")
        l,m,r=ordered_fresh(last_u,last_v,fresh,[f"{j-1}{c}" for c in "abc"])
        ul,vl=(m,r) if delta.positive() else (l,m)
        u,v,d,a,b=params(xs,labels,I,ul,vl)
        ru,rv=d*d*a,d*d*b
        gate(u.between(zl,zr) and v.between(zl,zr) and strictly_less(u,v),
             "fresh anchor sites not certified distinct interior")
        gate(ru.negative() and rv.negative(),"negative pole theorem sign failed")
        f0,f1=real_window(I,u,v,ru,rv)
        width=f1-f0
        tau0=moment(nodal(xs,I),I,3)/h-u-v
        print(f"Target {order}: pair {ul},{vl}; delta={delta.bracket()}, "
              f"R={ru.bracket()},{rv.bracket()}, width={width.bracket()}, "
              f"window={f0.bracket()}..{f1.bracket()}, tau0={tau0.bracket()}.")
        gate(width.positive(),"real interval window not certified positive")
        _,_,_,am,bm=params(xmod,labmod,F,ul,vl)
        ec=ec_cert(F,am,bm)
        print("  Smooth marked arithmetic model and [6],[9],[12] residues:",ec)
        proposal=triple(I,u,d,a,b)
        print("  Prescribed rank-free triple:",[x.bracket() for x in proposal])
        if not all(x.between(zl,zr) for x in proposal):
            kind="proved exterior" if any(x.u<zl.l or x.l>zr.u for x in proposal) else "not proved strictly inside"
            raise Stop("rank-free triple "+kind+"; no further candidate evaluated")
        ll,xn,nn=replace(I,labels,xs,ul,vl,j)
        lm,xm,_=replace(F,labmod,xmod,ul,vl,j)
        gate(ll==lm and len(xm)==order-2 and "m3" in lm and "p3" in lm,"label and width check")
        hn=exact_checks(F,xm)
        gate(monotonic()-step_started<2 and monotonic()-began<8,"per-step or total wall stop")
        print(f"  PASS exact order {order}, {len(xm)} contributing sites in [0,1], first defect mod {Q} = {hn}.")
        last_verified=order
        labels,xs,fresh,ll_unused=ll,xn,nn,ll
        labmod,xmod=lm,xm
        hprev=h
        last_u,last_v=u,v
    except (AssertionError,ValueError,Stop) as e:
        print(f"STOP before accepting order {order}: {e}")
        print(f"Last verified exact interval order {last_verified}; no alternate pair or group point searched.")
        break
else:
    print("PASS all four prescribed continuation moves; no alternate pair, grid, or elliptic point search.")
