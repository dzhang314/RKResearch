"""Actual zero-at-fifth pure-four determinant, with exact literal *fourth* pads only."""
from aq_rear import C,u as Y,s,g,red,ev,divide,front_data,Lco
from regular_star_projection import con,nodal,det,Z
from functools import lru_cache

def scalar_inv(v):
    v=red(v);d=red(v*con(v))
    assert d and d.is_constant()
    return red(con(v)/d)

@lru_cache(None)
def zero_fifth(front):
    A,B,m,ha,hb,_,H4,_=front_data(front)[0]
    h=ev(H4,s)
    assert ev(H4,A)==ha and ev(H4,B)==hb
    iBA=scalar_inv(B-A)
    TA=red(A**3+A-1-A**4/4)
    TB=red(B**3+B-1-m+m*A**3-B**4/4)
    phi_A=red(((B-s)+(s-A)*(1+m*ha*scalar_inv(hb)))*iBA)
    phi_T=red(((B-s)*TA*scalar_inv(ha)+(s-A)*TB*scalar_inv(hb))*iBA)
    M0=s-1-2*h;M1=s*s/2-s-2*h
    ta=red((B*M0-M1)*iBA);tb=M0-ta
    Ah=red(h+ta*ha+tb*hb-h*phi_A)
    Th=red(s**3-s**4/4+2*h+ta*A**3+tb*B**3-h*phi_T)
    pad=red((s-A)*(s-B))
    Ar=divide(Ah,pad);Tr=divide(Th,pad)
    # Earlier literal h-values are interpolated by H4 minus its monic nodal term.
    E=nodal([A,B,s])
    qh=[red(H4[j]-H4[-1]*E[j]) for j in range(3)]
    qi=[-v for v in E[:3]]
    M=[Y-1,Y**2/2-Y,Y**3/3-Y**2]
    A5=red(sum(f*m for f,m in zip(qh,M)))
    T5=red(Y**3-Y**4/4+sum(f*m for f,m in zip(qi,M)))
    Q=red(Ar*T5-Tr*A5)
    # Independent exact Cramer reconstruction of the consecutive literal row
    # (cleared by its actual predecessor Vandermonde) and determinant check.
    v0,v1,v2=M
    pA=red((s-B)*(v2-(s+B)*v1+s*B*v0))
    pB=red(-(s-A)*(v2-(s+A)*v1+s*A*v0))
    pS=red((B-A)*(v2-(A+B)*v1+A*B*v0))
    V0=red((B-A)*pad)
    a5=red(pA*ha+pB*hb+pS*h)
    t5=red(V0*(Y**3-Y**4/4)+pA*A**3+pB*B**3+pS*s**3)
    assert a5==red(V0*A5) and t5==red(V0*T5)
    raw=det([[ha,red(A*ha),ha,TA],
             [hb,red(B*hb),red(hb+m*ha),TB],
             [h,red(s*h),red(h+ta*ha+tb*hb),
                red(s**3-s**4/4+2*h+ta*A**3+tb*B**3)],
             [Z,Z,a5,t5]])
    assert raw==red(ha*hb*(B-A)*V0*pad*Q)
    assert Q.degrees()[:3]==(4,1 if front else 3,0)
    print('actual zero fifth determinant',front,Q.degrees(),Ar.degrees(),Tr.degrees(),flush=True)
    return Q,(A,B,m,ha,hb,H4)
