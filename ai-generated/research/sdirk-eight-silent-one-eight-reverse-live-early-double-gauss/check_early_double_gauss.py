"""Full pairwise-different front/fourth Legendre quartic fibers."""
from pathlib import Path
from sympy import isprime
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from seven_k0_anchors import Bfield,cv,ends,h4,pol,ev,Lco
from flint import nmod_poly
from itertools import permutations

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    K=Bfield(nmod_poly([0,1],p),p,t)
    roots=sorted(int(r) for r,e in nmod_poly(list(Lco),p).roots() if e==1)
    assert roots==[100,214,916,1030]
    L3=list(map(K,[-1,12,-30,20]))
    for front in (True,False):
        A,B,m=map(lambda v:cv(K,v),ends(front,1))
        ha,hb=(A-1)/2,(B-1-m)/2
        H=list(map(lambda v:cv(K,v),pol(h4(front),lambda x:x)))
        for slot,(a,h) in enumerate(((A,ha),(B,hb)),2):
            a.inv()
            for r,q in permutations(map(K,roots),2):
                gamma=r/a
                (ev(H,q/gamma)*ev(L3,r)-h*ev(L3,q)).inv()
            print('all twelve different quartic contact pairs excluded',front,slot,flush=True)

if __name__=='__main__':
    main()
