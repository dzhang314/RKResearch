"""Exact rational gates of the fixed-q split chart. No float arithmetic."""
from collections import Counter
from fractions import Fraction as F
from itertools import permutations
from math import isqrt
import argparse
import json

def mul(p,q):
    a=[F(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):
            a[i+j]+=x*y
    return a

def add(p,q):
    a=[F(0)]*max(len(p),len(q))
    for r in (p,q):
        for j,x in enumerate(r):
            a[j]+=x
    return a

def scale(p,s): return [s*v for v in p]

def product(xs):
    p=F(1)
    for x in xs: p*=x
    return p

def nodes(xs):
    p=[F(1)]
    for x in xs: p=mul(p,[-x,F(1)])
    return p

def val(p,x):
    a=F(0)
    for c in p[::-1]: a=a*x+c
    return a

def moment(p,j=0):
    return sum((x/(i+1+j) for i,x in enumerate(p)),F(0))

def primitive(p): return [F(0)]+[x/(i+1) for i,x in enumerate(p)]

def derivative(p): return [i*x for i,x in enumerate(p) if i]

def distinct(xs): return len(set(xs))==len(xs)

def interp(ys):
    x=list(ys)
    p=[F(0)]
    for a in x:
        r=[b for b in x if b!=a]
        p=add(p,scale(nodes(r),ys[a]/product(a-b for b in r)))
    return p

def sqrtq(x):
    if x<0: return None
    a,b=isqrt(x.numerator),isqrt(x.denominator)
    return F(a,b) if (a*a,b*b)==(x.numerator,x.denominator) else None

def L4(): return [F(1),F(-14),F(56),F(-84),F(42)]

def cubic(c):
    return [
        75*c**3-108*c*c+45*c-5,
        -3*(175*c**3-244*c*c+97*c-10),
        3*(350*c**3-476*c*c+183*c-18),
        -15*(42*c**3-56*c*c+21*c-2),
    ]

def delta(c): return 210*c**4-336*c**3+168*c*c-28*c+1

class Reject(Exception):
    pass

def require(b,why):
    if not b: raise Reject(why)

def late(c,d,g,R):
    require(distinct([F(0),F(1),c,d,g,R]),"initial_collision")
    de=c+(delta(c)-1)*d
    require(de,"e_pivot")
    e=c*(c-d)/de
    M=mul([F(0),F(0),F(1)],nodes([c,c]))
    JM=primitive(M)
    U=mul(mul([F(1),F(-1)],nodes([g,R])),JM)
    uh=moment(U)
    require(uh,"h_pivot")
    h=moment(U,1)/uh
    SM=mul(mul([F(1),F(-1)],nodes([g,h,R])),M)
    uf=moment(SM)
    require(uf,"f_pivot")
    f=moment(SM,1)/uf
    require(distinct([F(0),F(1),c,d,e,f,g,h,R]),"late_collision")
    return e,f,h,M,JM

def first_two(c,d,g,R,ims):
    e,f,h,_,_=ims
    B=nodes([c,d,e,f,g,h])
    A0=mul([F(0),F(-1),F(1)],B)
    E0,E1=moment(A0),moment(A0,1)
    C2=mul([-R,F(1)],[c,F(-2)])
    D2=mul([F(1),F(-1)],[E1,-E0])
    u=C2[2]*D2[0]-C2[0]*D2[2]
    v=C2[2]*D2[1]-C2[1]*D2[2]
    w=C2[1]*D2[0]-C2[0]*D2[1]
    T=nodes([f,g,h]); V=cubic(c)
    phi=mul(nodes([F(1),c,d,e]),add(V,scale(T,-V[0]/T[0])))
    l0,l1,l2=(moment(phi,j) for j in range(3))
    det=u*l0+v*l1
    require(det,"symmetric_pivot")
    s=(-w*l0+v*l2)/det
    p=(-u*l2-l1*w)/det
    sq=sqrtq(s*s-4*p)
    require(sq is not None and sq!=0,"not_distinct_rational_ab")
    return [((s+sq)/2,(s-sq)/2),((s-sq)/2,(s+sq)/2)]

def cardinal(xs):
    return {
        z: moment(nodes([v for v in xs if v!=z]))/product(z-v for v in xs if v!=z)
        for z in xs
    }

def head(c,d,g,R,a,b,ims,origin=True):
    e,f,h,M,JM=ims
    ordinary=[a,b,c,d,e,f,g,h,R]
    allsites=[F(0),F(1)]+ordinary
    require(distinct(allsites),"a_b_collision")
    require(c!=2*b,"c_2b")
    w=cardinal([x for x in allsites if x!=R])
    w[R]=F(0)
    require(w[0] and w[a],"head_weight_zero")
    Fprime=lambda z:product(z-v for v in ordinary if z!=v)
    aa=-w[a]*a*a*(1-a)*Fprime(a)/2
    N=[2*b*c/(2*b-c),2*(-2*a*b+a*c+b*c-c*c)/(a*(2*b-c))]
    Ln=lambda x:val(N,x)/(x*x*(x-c))
    if origin:
        A=[aa/(1-a),-aa/(1-a)]
    else:
        require(Ln(b),"second_ratio_zero_generic")
        A=interp({a:aa,b:w[b]*(1-b)*Fprime(b)/Ln(b)})
        require(val(A,1),"generic_a1_zero")
    u={z:val(A,z)/((1-z)*Fprime(z)) for z in ordinary}
    u[F(0)]=F(0)
    require(u[R] and all(u[z] for z in [a,b,d,e]),"u_anchor_zero")
    require(w[a]==Ln(a)*u[a] and w[b]==Ln(b)*u[b],"first_two_ratio")
    require(w[d]==Ln(d)*u[d],"d_ratio")
    require(w[e]==Ln(e)*u[e],"e_ratio")
    CL=[F(0)]+L4()
    require(val(CL,c),"jacobi_pair_gate")
    PZ=add(JM,scale(CL,-val(JM,c)/val(CL,c)))
    QZ=interp({c:F(0),**{z:-Ln(z)*val(PZ,z) for z in [a,b,d]}})
    require(w[f]*val(PZ,f)+u[f]*val(QZ,f)==0,"f_ratio")
    Zf=w[f]*val(M,f)-(f-c)*val(N,f)*u[f]
    require(Zf,"Zf_zero")
    k=c/(2*c-4*b)
    bb,cc=b/a,c/a
    D=3*bb*k-2*cc*k+cc
    require(D,"head_Delta")
    Lc=-2*(2*bb*cc*k*k+2*bb*cc*k-2*bb*k*k+bb*k-2*cc*k+cc)/(c*c*D)
    require(w[c]!=Lc*u[c],"pair_dependent")
    return dict(ordinary=ordinary,w=w,u=u,A=A,N=N,Lc=Lc,k=k,PZ=PZ,QZ=QZ,M=M)

def nonlinear(s):
    a,b,c,d,e,f,g,h,R=s["ordinary"]
    w,u,A,Lc=s["w"],s["u"],s["A"],s["Lc"]
    U,W=u[c],w[c]
    V=cubic(c)
    norm=(1-R)*val(V,R)
    require(norm,"nu_host_zero")
    n=lambda z:(1-z)*val(V,z)/norm
    data=[(z,w[z]*n(z)/(u[z]*(z-R))) for z in [f,g,h] if u[z]]
    require(len(data)>=2,"quad_insufficient")
    Q=mul([-R,F(1)],interp(dict(data[:2])))
    require(any(Q) and val(A,1)*val(Q,1)==0,"quad_origin_guard")
    eta={F(0):F(0),R:F(1)}
    free=[]
    for z in [a,b,d,e,f,g,h]:
        rhs=val(Q,z)*u[z]
        if w[z]:
            eta[z]=rhs/w[z]
            require(z not in [f,g,h] or eta[z]==n(z),"quad_tail_mismatch")
        else:
            require(not rhs and u[z],"zero_score_guard")
            if z in [f,g,h]: eta[z]=n(z)
            else: free.append(z)
    require(len(free)<=1,"two_free_singletons")
    if free:
        z=free[0]
        eta[z]=-sum((y-c)*eta[y]*u[y] for y in eta)/((z-c)*u[z])
    for j in range(3):
        require(sum((z-c)*z**j*eta[z]*u[z] for z in eta)==0,"nonlinear_moment_"+str(j))
    Lambda=-sum(eta[z]*u[z] for z in eta)
    Qc=val(Q,c)
    if Qc:
        require(Lc,"Q_nonzero_first_zero")
        B0=Lambda/Qc
        p=B0*Lc+W/Lc-2*U
        require(p,"mobius_infinity")
        t=(B0*W-U*U)/p
        require(t and W-Lc*t,"mobius_pole")
        ec=[Qc/Lc,Qc*(U-t)/(W-Lc*t)]
    elif not Lc:
        t=F(1); ec=[Lambda,F(0)]
    elif not Lambda:
        t=F(1) if W!=Lc else F(2); ec=[F(0),F(0)]
    else:
        require(W,"zero_pair_mass_without_nonlinear_split")
        t=W/Lc; ec=[F(0),Lambda/(U-t)]
    ys=[F(0),a,b,c,c,d,e,f,g,h,R]
    ww=[w[z] if i not in [3,4] else [Lc*t,W-Lc*t][i-3] for i,z in enumerate(ys)]
    uu=[u[z] if i not in [3,4] else [t,U-t][i-3] for i,z in enumerate(ys)]
    ee=[eta[z] if i not in [3,4] else ec[i-3] for i,z in enumerate(ys)]
    assert all(wi*ei==val(Q,z)*ui for z,wi,ui,ei in zip(ys,ww,uu,ee))
    assert all(sum(wi*ei*z**j for z,wi,ei in zip(ys,ww,ee))==0 for j in range(6))
    assert all(sum(ui*ei*z**j for z,ui,ei in zip(ys,uu,ee))==0 for j in range(4))
    return dict(ys=ys,w=ww,u=uu,eta=ee,quad=Q)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--grid",action="store_true",help="replay the finite 10-value origin-root screen")
    parser.add_argument("--c");parser.add_argument("--d");parser.add_argument("--g");parser.add_argument("--R")
    parser.add_argument("--a");parser.add_argument("--b")
    parser.add_argument("--literal",action="store_true",
                        help="construct fixed-q tableau on a scalar survivor and independently replay")
    args=parser.parse_args()
    if args.grid:
        values=list(map(F,["-2","-1","-1/2","1/4","1/3","1/2","2/3","3/4","3/2","2"]))
        params=permutations(values,4)
    else:
        params=[tuple(F(getattr(args,k)) for k in ["c","d","g","R"])]
    counts=Counter()
    n=0
    for c,d,g,R in params:
        n+=1
        try:
            ims=late(c,d,g,R)
            aa=first_two(c,d,g,R,ims) if args.a is None else [(F(args.a),F(args.b))]
        except Reject as ex:
            counts[str(ex)]+=1
            continue
        for a,b in aa:
            try:
                s=head(c,d,g,R,a,b,ims,origin=(args.a is None))
                z=nonlinear(s)
                print("nonlinear-compatible spectrum",json.dumps(z,default=str))
                counts["nonlinear_compatible"]+=1
                if args.literal:
                    import literal
                    try:
                        mat,weights,clocks=literal.full(s,z)
                        err,cnt=literal.rooted(mat,clocks,weights,10)
                        assert sum(cnt.values())==1205
                        if err is not None:
                            raise AssertionError(("literal order failure",err))
                        defect,_=literal.rooted(mat,clocks,weights,11)
                        print("exact literal order through ten, next defect:",defect)
                        print(json.dumps(dict(A=mat,b=weights,c=clocks),default=str))
                        counts["literal_through_ten"]+=1
                    except literal.Reject as ex:
                        counts["literal_"+str(ex)]+=1
            except Reject as ex:
                counts[str(ex)]+=1
    print("ordered input quadruples:",n)
    for key,n in sorted(counts.items()):
        print(key,n)

if __name__=="__main__":
    main()
