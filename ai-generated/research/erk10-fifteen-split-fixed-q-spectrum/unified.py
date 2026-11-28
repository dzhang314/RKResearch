"""Uniform exact rational head solve from τ=d*e, with all score-domain guards."""
from fractions import Fraction as F
from itertools import permutations
from collections import Counter
import argparse
from spectrum import (add,mul,scale,nodes,val,moment,primitive,L4,cubic,delta,interp,
                      sqrtq,distinct,require,Reject,head,nonlinear,late)

values=list(map(F,["-2","-1","-1/2","1/4","1/3","1/2","2/3","3/4","3/2","2"]))

def tail(c,g,R):
    require(distinct([F(0),F(1),c,g,R]),"initial_collision")
    M=mul([F(0),F(0),F(1)],nodes([c,c]))
    JM=primitive(M)
    Hu=mul(mul([F(1),F(-1)],nodes([g,R])),JM)
    hu=moment(Hu)
    require(hu,"h_pivot")
    h=moment(Hu,1)/hu
    S0=mul([F(1),F(-1)],nodes([g,h,R]))
    sm=moment(mul(S0,M))
    require(sm,"f_pivot")
    f=moment(mul(S0,M),1)/sm
    require(distinct([F(0),F(1),c,f,g,h,R]),"tail_collision")
    T=nodes([f,g,h])
    # k0/τ = ∫ y(y−1)(y−c)^2(y−R) T(y) dy
    k=moment(mul(mul(mul([F(0),F(-1),F(1)],nodes([c,c])),nodes([R])),T))
    CL=[F(0)]+L4()
    a=val(JM,c)/val(CL,c)
    PZ=add(JM,scale(CL,-a))
    P30=a/c
    P3f=val(PZ,f)/(f*(f-c))
    hf=-P3f*sm/P30
    ell=(hf-k)/f
    V=cubic(c)
    H=add(V,scale(T,-V[0]/T[0]))
    return dict(c=c,g=g,R=R,h=h,f=f,M=M,JM=JM,T=T,H=H,k=k,ell=ell,
                omega=(delta(c)-1)/c,origin=(k+ell==0))

def matrix(t,u):
    c,R=t["c"],t["R"]
    k,l=u*t["k"],u*t["ell"]
    pair=[u,-c+t["omega"]*u,F(1)]
    B=mul(mul([F(0),F(-1),F(1)],nodes([c])),mul(pair,t["T"]))
    E0,E1=moment(B),moment(B,1)
    phi=mul(mul(nodes([F(1),c]),pair),t["H"])
    L0,L1,L2=(moment(phi,j) for j in range(3))
    return [
        [E0*R*c*c-2*k*c,-E0*R*c-E0*c*c+E1*c+2*k-l*c,-E1*R*c*c+k*c*c],
        [-c*(E1+l),E0*c+2*l,-E0*R*c*c+E1*R*c+E1*c*c+k*c+l*c*c],
        [-L1,L0,L2],
    ]

def sumprod(M):
    for a,b in ((0,1),(0,2),(1,2)):
        p,q,r=M[a]; x,y,z=M[b]
        d=p*y-q*x
        if d:
            s,t=(-r*y+q*z)/d,(-p*z+x*r)/d
            require(all(p*s+q*t+r==0 for p,q,r in M),"inconsistent_linear_system")
            return s,t
    require(not any(p*z-x*r or q*z-y*r for p,q,r in M for x,y,z in M),
            "inconsistent_rank_one")
    require(any(p or q for p,q,r in M) or not any(r for p,q,r in M),
            "inconsistent_rank_zero")
    raise Reject("sumprod_rank_deficient")

def two(s,p,tag):
    q=sqrtq(s*s-4*p)
    require(q is not None and q!=0,tag)
    a,b=(s+q)/2,(s-q)/2
    return [(a,b),(b,a)]

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--count",type=int,default=0,
                    help="first N ordered quadruples (default tests all 5040)")
    args=ap.parse_args()
    C=Counter()
    total=0
    for c,d,g,R in permutations(values,4):
        if args.count and total>=args.count: break
        total+=1
        try:
            e,f,h,M,JM=ims=late(c,d,g,R)
            t=tail(c,g,R)
            assert (f,h)==(t["f"],t["h"])
            tau=d*e
            rows=matrix(t,tau)
            assert rows[0]==[-c*x for x in rows[1]]
            sp=sumprod(rows)
            ab=two(*sp,"a_b_discriminant")
        except Reject as ex:
            C[str(ex)]+=1; continue
        for a,b in ab:
            try:
                sol=head(c,d,g,R,a,b,ims,origin=t["origin"])
                assert (val(sol["A"],F(1))==0)==t["origin"]
                C["linear_compatible_spectrum"]+=1
                z=nonlinear(sol)
                C["nonlinear_compatible_spectrum"]+=1
                print("compatible",c,d,g,R,a,b,z)
            except Reject as ex:
                C["head_"+str(ex)]+=1
    print("ordered four-clock skeletons:",total)
    for k,n in sorted(C.items()): print(k,n)

if __name__=="__main__": main()
