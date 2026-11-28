"""All thirty-six full phase groups with one literal early Gauss clock."""
from pathlib import Path
from sympy import isprime
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-eight-reverse-live-constant",
            "sdirk-eight-silent-one-eight-reverse-live-exceptional",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from early_gauss_fibers import roots,test

DATA={
 (True,2):([25,23,18,13],17),
 (True,3):([18,14,17,21],19),
 (False,2):([17,26,19,17],16),
 (False,3):([18,22,8,15],15),
}
def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    assert roots(p)==[100,214,916,1030]
    for (front,contact),(arith,silent) in DATA.items():
        for slot,n in zip((2,3,4,5),arith):
            assert test(front,contact,True,slot,p,t)==[0,0,0]
            assert test(front,contact,False,slot,p,t)==[n,0,0]
            print('single Gauss ordinary eighth verified',front,contact,slot,n,flush=True)
        assert test(front,contact,None,8,p,t)==[silent]*3
        print('single Gauss silent eighth verified',front,contact,silent,flush=True)
    print('all thirty-six single early-Gauss orientations excluded',flush=True)

if __name__=='__main__':
    main()
