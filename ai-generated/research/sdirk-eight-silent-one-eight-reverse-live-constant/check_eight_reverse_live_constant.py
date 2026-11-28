"""Guards, full quartic closure, and the explicitly conditional pure quintic."""
from pathlib import Path
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
from sympy import isprime
from flint import fmpq_poly, fmpq
from mixed_front_projection import Q,can,lp,L3,L4,L5,front_projection
from reverse_live_quintic import mode
from reverse_live_quartic import mode4

def moment(P,j):
    return sum(fmpq(w,i+j+1) for i,w in enumerate(P))

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    a=Q.gen(0)
    assert not can(5*lp(L5,a)+4*lp(L3,a)-9*(2*a-1)*lp(L4,a))
    assert all(moment(P,j)==0 for a,P in enumerate((L3,L4,L5),3) for j in range(a))
    assert [moment(L3,3),moment(L3,4),moment(L4,4)]==[fmpq(1,140),fmpq(1,70),fmpq(1,630)]
    assert fmpq_poly(list(L3)).gcd(fmpq_poly(list(L4)))==fmpq_poly([1])
    for P in (L4,L5):
        Z=list(map(fmpq,P))
        W=[sum(Z[j]/(j-i) for j in range(i+1,len(Z))) for i in range(len(Z)-1)]
        assert fmpq_poly(Z).gcd(fmpq_poly(W))==fmpq_poly([1])
    modes=[(rear,slot) for rear in (True,False) for slot in (2,3,4,5)]+[(None,8)]
    for front in (True,False):
        front_projection(front)
        for rear,slot in modes:
            n=2 if front else 1
            assert mode4(front,rear,slot,p,t,True)==n
            assert mode(front,rear,slot,p,t,True)==n
    print('all eighteen forced L4 phases and all eighteen conditional L5 phases excluded',flush=True)

if __name__=='__main__':
    main()
