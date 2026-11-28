"""Exact degree-five diagonal branch when both centered tail coefficients vanish."""
from regular_star_projection import C,Z,O,g,s,t,red,ev as evx,profile
from mixed_front_projection import L3,L4,L5
from seven_k0_anchors import ends,h4,pol,F2,cv
from unequal_finite import Bfield,Tower,gcdp,trim
from equal_undetected_front import Nested
from off8_fibers import ev,add,mul,sc,qr,nodal,det
from flint import fmpq_poly,nmod_poly
from math import comb

QU=(1,-12,60,-120)
PU=(-5,114,-1155,6270,-17010,17640)
DU=(1,-20,180,-840,1400)

def ex_constants():
    a,b=red(2+2*t),red(2-2*t)
    ha,hb=(a-1)/2,(b-1)/2
    c,d=evx(QU,g),evx(PU,g)
    h=[red(-8*d*(L3[j] if j<4 else 0)+(162*g-45)*c*(L4[j] if j<5 else 0)+5*c*L5[j]) for j in range(6)]
    J=red(hb*evx(h,g*a)-ha*evx(h,g*b))
    assert not red(J+36*t*(18*g-5)*c*evx(DU,g))
    assert fmpq_poly(list(QU)).gcd(fmpq_poly(list(PU)))==fmpq_poly([1])
    m=1-2*g;x=1-g
    AH0=[]
    for j in (2,4):
        row=[]
        for P in (L3,L4,L5):
            p0=red(sum(q0*comb(i,j)*m**(i-j)*g**j for i,q0 in enumerate(P) if i>=j)+
                   sum(q0*comb(i,j+1)*m**(i-j-1)*g**(j+1) for i,q0 in enumerate(P) if i>=j+1))
            if j==2:p0=red(p0+evx(P,x))
            row.append(p0)
        AH0.append(row)
    assert AH0[0][0]==c
    assert not red((162*g-45)*AH0[0][1]+5*AH0[0][2]-8*d)
    assert AH0[1][0]==0 and not red(AH0[1][1]-70*g**4)
    assert not red(AH0[1][2]+126*g**4*(18*g-5))
    return h

def moment(P,K):
    return [sum(P[j]/(j-i) for j in range(i+1,len(P))) for i in range(len(P)-1)]
def bcol(A,H,K):
    W=moment(A,K);V=moment(H,K)
    S=add(mul(H,W),sc(mul(A,V),-1))
    assert len(S)<=5
    return (S+[K(0)]*5)[1:5]
def ccols(E,H,K):
    return [bcol([K(0)]*i+E,H,K) for i in range(4)]
def model(K,g):
    a=K(2)+K(2*K.t); b=K(2)-K(2*K.t)
    ha,hb=(a-1)/2,(b-1)/2
    Q,P=ev(list(map(K,QU)),g),ev(list(map(K,PU)),g)
    L=[-8*P*(L3[j] if j<4 else 0)+(162*g-45)*Q*(L4[j] if j<5 else 0)+5*Q*L5[j] for j in range(6)]
    la,lb=g*a,g*b
    h0=ha/ev(L,la)
    L=sc(L,h0)
    assert ev(L,lb)==hb
    H4=[cv(K,w) for w in pol(h4(True),lambda x:x)]
    L4s=[l*g**j for j,l in enumerate(L)]
    Y=add(L4s,sc(H4,-1))
    S,e=qr(Y,nodal([a,b]));assert not e and len(S)==4
    return L,S,(a,b,ha,hb,H4)

def test(p,t,verbose=True):
    raw=nmod_poly([-5,18],p)*nmod_poly(list(DU),p)
    assert raw.degree()==5
    assert sorted((f.degree(),e) for f,e in raw.factor()[1])==[(1,1),(1,1),(3,1)]
    counts=0
    for M,e in raw.factor()[1]:
        K=Bfield(M,p,t);g=K(nmod_poly([0,1],p));g.inv()
        L,S,(A,B,ha,hb,H4)=model(K,g)
        U=Tower(sc(S,S[-1].inv()));s=U.gen();GL=list(map(U,L))
        gg=U(g); x=1-gg; m=1-2*gg; q=gg*s
        hp=[sum(GL[i]*comb(i,j)*m**(i-j)*gg**j for i in range(j,6)) for j in range(6)]
        hx=ev(GL,x)
        assert not hp[4]+hp[5] and not hp[2]+hp[3]+hx
        P=[(x-q)*hp[0]-2*(m-q)*hx,(x-q)*hp[2]+(m-q)*hx,(x-q)*hp[4]]
        Z0=Nested(sc(P,P[-1].inv()));w=Z0.gen()
        W=Z0(gg);X=Z0(x);V=Z0(m);R=Z0(s)
        a,b=map(Z0,(U(A),U(B)))
        E=mul(nodal([W*a,W*b,X]),[V*V-W*W*w,-2*V,Z0(1)])
        H=list(map(Z0,GL))
        J=ccols(E,H,Z0)
        N=det(J)
        N.inv()
        counts+=1
        if verbose: print('zero-tail exact fiber',p,t,M.degree(),len(P)-1,flush=True)
    return counts
