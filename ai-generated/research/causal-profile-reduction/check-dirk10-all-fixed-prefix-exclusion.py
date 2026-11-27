#!/usr/bin/env python3
"""Independent exact first-prefix check with genuine input degree at most four."""
from itertools import permutations


def replay(p):
    def div(x,y):
        assert y % p, ("denominator", x,y)
        return x*pow(y%p,-1,p)%p

    def nodal(nodes):
        cs=[1]
        for z in nodes:
            cs=[((cs[i-1] if i else 0)-z*(cs[i] if i<len(cs) else 0))%p
                for i in range(len(cs)+1)]
        return cs

    def primitive(nodes,x):
        return sum(div(c*x**(i+1),i+1) for i,c in enumerate(nodal(nodes)))%p

    def tap(nodes,z,x):
        other=tuple(t for t in nodes if t!=z)
        den=1
        for t in other:
            den=den*(z-t)%p
        return div(primitive(other,x),den)

    roots=tuple(z for z in range(p) if (42*z**4-84*z**3+56*z*z-14*z+1)%p==0)
    assert len(roots)==4 and all(z not in (0,1) for z in roots)
    if p==227:
        assert roots==(24,51,177,204)
    count=0
    for xi,a,b,x in permutations(roots):
        nodes=(0,xi,a,b,x)
        S={v:tap(nodes,v,x) for v in nodes}
        P={v:primitive((0,xi,a,b),v) for v in (xi,a,b)}
        assert all(S.values()) and all(P.values())
        g=div(xi**3,6)
        h=div(xi**2*a**3,36*(a-xi))
        alpha=div(3*(a-xi)*(a-2*xi),xi**2)
        for before in (True,False):
            if before:
                J=div(a-div(xi,2),alpha)
                hb=div(g*S[xi]*J-S[a]*h,S[b])
            else:
                hb=div(xi**2*b**3*(2*a-b),36*(xi-a)*(a-2*b))
                J=div(S[a]*h+S[b]*hb,g*S[xi])
            la,lb=div(-P[a],h),div(-P[b],hb)
            lxi=la+div((lb-la)*(xi-a),b-a)
            assert (g*lxi*J-P[xi])%p, (xi,a,b,x,before)
            count+=1
    assert count==48
    print(f"mod {p}: all {count} first-change separators and fixed tap guards pass")


if __name__=="__main__":
    for prime in (227,419,587):
        replay(prime)
