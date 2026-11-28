"""All literal phases; no Gaussian atom is replaced by a virtual cubic read."""
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
from shared_one_front_fibers import test,models,root_consts

def main():
    rows=(
        (True,0,1129,203,21),(True,1,1129,203,25),
        (False,0,1559,529,14),(False,1,1129,203,22),
    )
    for f,a,p,t,count in rows:
        assert isprime(p) and (2*t*t-1)%p==0
        assert len(root_consts(p))==4
        assert models(f,a,True)==[]
        live=models(f,a,False)
        assert len(live)==1 and len(live[0][0])==31
        assert live[0][1] is None and live[0][2] is None
        n=test(f,a,p,t,True)
        assert n==(count,)*4
        print("excluded shared-Gauss one-front phase",f,a,n,flush=True)
    print("all four shared-Gauss one-front phases excluded",flush=True)

if __name__=='__main__':
    main()
