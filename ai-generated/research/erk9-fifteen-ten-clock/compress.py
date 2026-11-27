from scalar import *
from dataclasses import dataclass
@dataclass
class Core:
    W:dict
    X:tuple
    U:dict
    G:dict
    H:dict
    theta:F
    alpha:F
    beta:F
    gamma:F
    delta:F
    d4:F
    d6:F

def init(a,b,c,t):
    """Unweighted u responses at the first three interior reverse labels (with y=a,b,c)."""
    if not t:return
    d=b-a
    beta=(a/2-b/3+a*t/3)/(t*d)
    delta=-a*(F(1,2)+t)/(2*t*d)
    alf=2*a/3-beta*a; gam=-delta*a
    k=(a/2+t*b)/d
    R=-a*c*c/4+k*(c**3/3-a*c*c/2)
    K=-a/2+k*(alf+beta*c-a)-(gam+delta*c)
    if not K:return
    U=( -a*a/2, t*b*b, -R/K)
    if not all(map(paid,(*U,alf,beta,gam,delta))):return
    return U,alf,beta,gam,delta

def weighted(U_init,X_pre,W,bar):
    u=tuple(W[x]*v/bar[x] for v,x in zip(U_init,X_pre))
    l=[lagrange(X_pre,i) for i in range(3)]
    coeffs=[sum(r[k]*v for r,v in zip(l,u))for k in range(3)]
    return {x:bar[x]*pe(coeffs,x) for x in bar}

def profile(Y,W,U,k):
    return [[W[x]*(1-x)**i for x in Y] for i in range(k)]+[[U[x]for x in Y]]

def ths(a,b,c):
    basic=[-b/(2*a),-F(1,3),F(1,2),F(1,3),F(1),F(-1),F(2),-F(2),F(1,6),-F(1,6),
           F(3),F(-3),F(2,3),-F(2,3),F(3,2),-F(3,2),F(5,2),-F(5,2),F(7,2),-F(7,2)]
    return tuple(dict.fromkeys(t for t in basic if t not in (-F(1,2),-a/(2*b))))

def cores():
    for k,ht,w,X,v,UU in found():
        if k<5: continue
        W=dict(zip(X,v))|{F(1):w}
        S=tuple(x for x in X if x)
        bar={x:1/(x*prod(x-y for y in S if x!=y)) for x in S}
        # Moments on X times degree <=5: nine nonzero sites include 1.
        bar={x:1/(x*prod(x-y for y in (*S,F(1)) if x!=y)) for x in (*S,F(1))}
        for abc in permutations(UU,3):
            a,b,c=(1-x for x in abc)
            for t in ths(a,b,c):
                h=init(a,b,c,t)
                if h is None:continue
                initu,alf,bet,gam,delt=h
                # There is a compulsory fourth interpolation value at x=1: first reverse row is zero.
                # 9 nonzero sites => deg2 cofactor => only three FREE values.  u(1)=0 leaves
                # controls at first TWO interior rows.  Our independent target at c must match.
                # handled below by degree-two interpolation with (1, a, b), and exact row3 check.
                A,B,C=abc
                U=weighted((F(0),*initu[:2]),(F(1),A,B),W,bar)
                if U[C] != W[C]*initu[2]:continue
                Y=(F(1),*abc)
                d4=det(profile(Y,W,U,3))
                if not d4:continue
                for e,f in combinations(tuple(x for x in UU if x not in abc),2):
                    R=(*Y,e,f)
                    d6=det(profile(R,W,U,4)+[[(1-x)*U[x]for x in R]])
                    if not d6:continue
                    G={x:(alf+bet*(1-x))*U[x] for x in U}
                    H={x:(gam+delt*(1-x))*U[x] for x in U}
                    yield Core(W,R,U,G,H,t,alf,bet,gam,delt,d4,d6)
if __name__=='__main__':
    for a in cores():
        print(a, flush=True)
