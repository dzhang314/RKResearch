"""Full local exceptional exclusion, retaining all genuine finite fibers."""
from exception_nodal import *

def exact_div(a,b):
    q,r=divp(a,b)
    assert not r
    return q

def poly_contact(K,g,x,H0,H1):
    # x is actual terminal; c=x-g*u.
    u=[K(0),K(1)];c=[x,-g]
    return exact_div(add(sc(subst(H1,c),ev(H0,x)),sc(subst(H0,c),-ev(H1,x))),u)

def solve_minor(J,N,K):
    """Keep an entire selected marked fiber; require a common unit pivot."""
    for I in combinations(range(4),N):
        A=[[J[j][i] for j in range(N)] for i in I]
        rhs=[-J[N][i] for i in I]
        try:d=det(A).inv()
        except ArithmeticError:continue
        ans=[z*d for z in cramer(A,rhs)]
        return ans
    raise ArithmeticError('no missing-clock minor unit')

def silent_fifth(data,Q,F0,F1,N,pegs,contact,verbose=False):
    K,g,A,B,m,ha,hb,s,hp,H0,H1=data
    assert len(N)==22 and len(contact)==5
    dc=gcdp(F1,contact)
    assert len(dc)==1 and contact[0], (len(dc)-1,bool(contact[0]))
    U=N
    for W in (F1,F1,contact):
        U=exact_div(U,W)
    assert len(U)==8
    Z=Nested(mon(U));u=Z.gen()
    gz,az,bz,mz,haz,hbz,sz,hpz=map(Z,(g,A,B,m,ha,hb,s,hp))
    X=1-gz;c=X-gz*u;k=1+2*u-u*u
    evu=lambda f:ev(list(map(Z,f)),u)
    # Any contact ghost already divided exactly. We test inverses in *all* remaining fibers.
    f0=evu(F0);f1=evu(F1);f1i=f1.inv()
    H=[Z(a)-f0*f1i*Z(b) for a,b in zip(H0,H1)]
    L=[h*gz**j for j,h in enumerate(H)]
    assert ev(L,az)==haz and ev(L,bz)==hbz and ev(L,sz)==hpz
    Peg=[[evu(e)] for e in pegs]
    # (2) in coefficient form, keeping a degree-three monic missing factor.
    J=ordinary_cols([[v] for v in H],Peg,Z)
    J=[[v[0] if v else Z(0) for v in row] for row in J]
    T=solve_minor(J,3,Z)+[Z(1)]
    assert all(sum(T[j]*J[j][i] for j in range(4))==0 for i in range(4))
    Yn=[r*gz**j/gz**3 for j,r in enumerate(T)]
    Y5=literal_fifth(Z,az,bz,mz,haz,hbz,sz,hpz,L)
    g0=multicol(Yn,Y5)
    try:g0.inv()
    except ArithmeticError:
        print('late nonunit',Q,len(U)-1,'first projection components residual gcd degrees in coefficient algebra',
              len(gcdp(Z.F,g0.x))-1,flush=True)
        raise
    if verbose:print('literal fifth missing cubic unit',Q,len(U)-1,flush=True)

def check_modes(front,p,t,verbose=False):
    ct=[0,0,0]
    for data in base(front,p,t,verbose):
        K,g,A,B,m,ha,hb,s,hp,H0,H1=data
        # Depth-three ordinary head actual anchors.
        for a0 in (s-A,s-B,A-B):
            a0.inv()
        x=1-g;K0=K.B.M.degree()
        for rear,slot in [(h,i) for h in (True,False) for i in (2,3,4,5)]+[(None,8)]:
            F0,F1,N,E,_=projected(*data,rear,slot)
            d=2 if rear else (6 if rear is False else 5)
            assert len(F0)==len(F1)==d+1
            assert len(gcdp(F0,F1))==1
            if slot<=4:
                assert len(N[-1])==(7 if rear else 10)
                assert len(gcdp(N[0],N[-1]))==1
                ct[0]+=1
            elif slot==5:
                # Removal of F1 is by the exact three-anchor rank argument.
                U=[exact_div(v,F1) for v in N]
                assert len(U[0])==(11 if rear else 19)
                v=U[0]
                for j in U[1:]:v=gcdp(v,j)
                assert len(v)==1
                ct[1]+=1
            else:
                B=poly_contact(K,g,x,H0,H1)
                silent_fifth(data,(front,K0,rear,slot),F0,F1,N[0],E,B,verbose=verbose)
                ct[2]+=1
    print('exception verified',front,p,t,ct,flush=True)
    return ct
