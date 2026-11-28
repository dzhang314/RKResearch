"""Good-reduction dual rank proof of the scope of the arithmetic d-contact factor."""
from eight_arithmetic_fibers import *

def check_bad_rank(front,p,t):
    G,B,ds=projections(front)
    F,M,C,E5,guards,geom,data0=ds
    _,_,q,bq,pegs,Lx,Lc,Ld=data0
    k=1+2*u-u*u
    Qx,Qc=[can(g*q+bq*v) for v in pegs[-3:-1]]
    Fd=ea(can(2*Lc*Qx-k*Lx*Qc))
    Ld=ea(Ld);Lx=ea(Lx)[0]
    gs=[ea(G0) for G0,_ in removed_common[front]]
    Fp=Bfield(nmod_poly([0,1],p),p,t)
    Q=Fp.cast(B)
    assert Q.degree()==B.degree() and Q.leading_coefficient()==1
    ans=[]
    for Md,_ in Q.factor()[1]:
        K=Bfield(Md,p,t);gg=K(nmod_poly([0,1],p))
        fe=lambda q:eval_E(K,gg,q)
        ff,mm,fd,ld=[list(map(fe,U)) for U in (F,M,Fd,Ld)]
        ff[-1].inv();ld[-1].inv();fe(Lx).inv();gg.inv()
        sd=gcdp(fd,ld)
        assert len(sd)>1
        U=Tower(sd);v=U.gen()
        for G0 in gs:ev([U(fe(f)) for f in G0],v).inv()
        # The root exists in the exact fiber by the defining resultant and the
        # nonzero leading coefficient of Ld; the weak reduced degree condition
        # only certifies rank, it does not choose the exact root.
        assert len(gcdp(ff,mm))<=2
        print('d-contact exact rank certificate',front,p,t,Md.degree(),len(sd)-1,flush=True)
        ans.append(Md.degree())
    return tuple(ans)
