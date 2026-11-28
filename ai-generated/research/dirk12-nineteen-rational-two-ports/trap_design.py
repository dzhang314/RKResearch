"""Synthesize a free scalar clock by the first three reverse trapezoids."""
from fractions import Fraction as Q
from probe import taps, prodpoly, prim, ev
from ranktwo import early, poles

def free_site(fixed, head):
    # fixed includes zero, one, and all unmoved proper sites.
    # Use -y^2 I[full hull omitting the site] for each of the three.
    amps=[]
    for u in head:
        p=prodpoly(tuple((-v,Q(1)) for v in fixed if v!=u))
        y=1-u
        amps.append((y*y*ev(prim((Q(0),)+p),Q(1)),-y*y*ev(prim(p),Q(1))))
    a,b,c=head
    rat=(b-c)/(b-a)
    pair=[amps[2][j]-rat*amps[0][j]-(1-rat)*amps[1][j] for j in range(2)]
    if pair[1]==0:
        return None
    v=-pair[0]/pair[1]
    return v if v not in fixed else None

def setup(M,head,u):
    nodes=(Q(0),Q(1),*M)
    v=free_site(nodes,head)
    if v is None: return
    xs=(Q(1),*head,*(x for x in M if x not in (*head,u)),v,u)
    full=(Q(0),)+xs
    ww=taps(full,Q(1))
    if not all(ww): return
    y=[1-x for x in xs]
    assert len(full)==12 and len(set(full))==12
    w=ww[1:]
    f=poles(xs,w)
    seed=((y[2]/y[1])**3*f[1]/f[2]-1)/(xs[2]-xs[1])
    G,_=early(xs,w)
    assert ev(G,seed)==0
    return xs,w,ww[0],seed,v
