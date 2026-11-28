"""All exact and finite local candidates at one other actual rear Gaussian clock."""
from rear_gauss_projection import *
from coprime_terminal_fibers import physical_sixth,mask,keep_leading_unit,span_unit
from shared_one_front_fibers import ev_poly,root_consts
from unequal_finite import Bfield,Tower
from equal_undetected_front import Nested
from flint import nmod_poly

def val(P,K,p,rr,t,ga,s):
    v=ev_poly(P,0,K,p,rr,t,ga,s)
    assert len(v)<=1
    return v[0] if v else K(0)

def padded_res(A,B,K):
    assert len(A)<=3 and len(B)<=6
    z=K(0)
    A=A+[z]*(3-len(A));B=B+[z]*(6-len(B))
    rows=[[z]*i+A+[z]*(4-i) for i in range(5)]
    rows += [[z]*i+B+[z]*(1-i) for i in range(2)]
    @lru_cache(None)
    def walk(i,mask):
        if i==7:return K(1)
        v=z;sg=1
        for j in range(7):
            if mask>>j&1:
                a=rows[i][j]
                if a:v+=sg*a*walk(i+1,mask^(1<<j))
                sg=-sg
        return v
    return walk(0,127)

def test(front,slot,rear,hit,p,t,verbose=False):
    gam,Old,T,Et,Ea,ds=rear_gauss(front,slot,rear,hit)
    q0,q1,xx,cc,dd,guards,Fp=ds
    A,B,m,ha,hb,a,quiet,H,H4=Fp
    roots=root_consts(p);assert roots is not None
    counts=[0]*4
    for rr in roots:
        R0=Bfield(nmod_poly([-rr,1],p),p,t)
        Gamma=nmod_poly([int(R0(v).x[0]) for v in gam],p)
        assert Gamma.degree()==len(gam)-1 and Gamma.leading_coefficient()==1
        for M,n in Gamma.factor()[1]:
            K=Bfield(M,p,t);ga=K(nmod_poly([0,1],p))
            ga.inv()
            counts[0]+=1
            P0=ev_poly(Old,1,K,p,rr,t,ga,K(0))
            assert len(P0)==8
            P0[-1].inv()
            SS=gcdp(P0,ev_poly(T,1,K,p,rr,t,ga,K(0)))
            if len(SS)<=1:continue
            counts[1]+=1
            U=Tower(SS);s0=U.gen();g0=U(ga)
            et=ev_poly(Et,0,U,p,rr,t,g0,s0)
            ea=ev_poly(Ea,0,U,p,rr,t,g0,s0)
            M0=keep_leading_unit(et,ea,U,3)
            YY=gcdp(gcdp(M0,et),ea)
            if len(YY)<=1:continue
            counts[2]+=1
            V=Nested(YY);y0=V.gen()
            z=lambda P:V(val(P,U,p,rr,t,g0,s0))
            cv0=lambda a:V(U(K(a)))
            gz=V(g0);sz=V(s0);cz=z(cc);dz=z(dd);xz=z(xx)
            qn=[z(q0),z(q1)];qp=[gz*qn[0],qn[1]]
            pegs=[gz*cv0(a),gz*sz,gz*y0,xz,cz,dz]
            if verbose:print('coprime rear Gauss candidate',front,slot,rear,hit,p,t,rr,M.degree(),len(SS)-1,len(YY)-1,flush=True)
            poly,S0=mask(V,V(U(rr)),qp,pegs)
            try:
                span_unit(V,*S0)
            except ArithmeticError:
                H6=physical_sixth(V,gz,*map(cv0,(A,B,m,ha,hb,a,H)),list(map(cv0,H4)),sz,y0,qn)
                R2=[v*gz**j for j,v in enumerate(poly)]
                span_unit(V,padded_res(R2,H6,V),*S0)
            counts[3]+=1
    return tuple(counts)
