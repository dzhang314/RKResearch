"""Exact geometric and leading-degree split for shared-Gauss one-front mode."""
from shared_one_front_projection import *
from equal_undetected_front import Nested
from unequal_finite import V

def shorten(x,d):
    x=list(x)
    while len(x)>1:
        g0=gcdp(x,d)
        if len(g0)<=1:break
        x,r=qr(x,g0);assert not r
    return mon(x)

def sf(A):
    return mon(divp(A,gcdp(A,deriv(A)))[0]) if len(A)>1 else A

def arithmetic_tail():
    x=1-g;u=s;c=x-g*u;d=x-2*g*u
    k=1+2*u-u*u;H=-2+u+4*u*u-u**3;J=2+3*u-12*u*u+4*u**3
    D=can(H*U(d)+2*J*U(c)-k*J*U(x))
    DD,rem=exdiv(D,u*u);assert not rem and DD.degrees()[1]==3
    return DD,x,c,d

class SplitAt(Exception):
    def __init__(self, divisor): self.divisor=divisor

class ExactV(V):
    def inv(self):
        if not self.x:raise ArithmeticError('exact zero pivot')
        D=gcdp(self.A.F,self.x)
        if len(D)>1:
            assert len(D)<len(self.A.F)
            raise SplitAt(D)
        return super().inv()

class ExactRing(Nested):
    def __init__(self,H): self.F,self.B=list(H),F
    def __call__(self,x):
        if isinstance(x,ExactV) and x.A is self:return x
        return ExactV(qr(x if isinstance(x,list) else [self.B(x)],self.F)[1],self)

def nested(P,coeff_at):
    return [coeff_at(gco(q)) for q in co(P,1)]

def trim(A):
    while A and not A[-1]:A.pop()
    return A

def split_early_exact(G,Phi,Old,S_guard):
    K=ExactRing(G);ga=K.gen()
    gg=lambda x:ev(list(map(K,x)),ga)
    try:
        SS=trim(nested(Phi,gg));assert SS
        # Exact leading coefficient test. If it is a zero divisor,
        # keep each literal component, including further degree drops.
        if len(SS)>1:SS[-1].inv()
        else:SS[0].inv();return [(G,[[F(1)]])]
        S0=mon(SS)
        Sf=trim(nested(S_guard,gg))
        assert Sf
        S1=shorten(S0,Sf)
        if len(S1)>1:
            old=qr(trim(nested(Old,gg)),S1)[1]
            S1=gcdp(S1,old)
        cs=[list(K(v).x) for v in S1]
        return [(G,cs)]
    except SplitAt as q:
        B,r=qr(G,q.divisor);assert not r
        return split_early_exact(q.divisor,Phi,Old,S_guard)+split_early_exact(mon(B),Phi,Old,S_guard)

@lru_cache(None)
def models(front,slot,hole8):
    G,RR,Old,Phi,Et,Ea,Gh,Th,gQ,ds=projection(front,slot)
    # The exact fifth-hole gcd is one in all four early phases.
    assert len(RR)==1
    # Reverse star has a degree-three condition independent of u.
    assert len(gcdp(G,gstar()))==1
    arith,x,c,d=arithmetic_tail()
    lead=gco(co(Phi,1)[-1])
    A,B,m,ha,hb,active,quiet,H,H4,*_=ds
    sGuard=can(term(H4,s)*(s-expr(A))*(s-expr(B))*(g*s-r))
    Pfor=gco(can(Phi.resultant(sGuard,1)))
    U0=mon(guarded(G,[[1-r0,F(-1)]]))
    if hole8:
        U0=gcdp(U0,geight())
        if len(U0)<=1:
            print('Gauss-eighth early exclusion',front,slot,flush=True)
            return []
    tlead=gco(co(arith,1)[-1])
    print('shared-one-front gamma branch',front,slot,hole8,
          'gamma',len(U0)-1,'s lower',len(gcdp(U0,lead))-1,
          's forbidden',len(gcdp(U0,Pfor))-1,'gap lower',len(gcdp(U0,tlead))-1,flush=True)
    # All projected lower degrees and geometric shadows are handled in
    # exact coefficient quotients; regular pieces use the full quadratic.
    exceptional=sf(mul(gcdp(U0,lead),gcdp(U0,Pfor)))
    regular=shorten(U0,exceptional)
    print('exact exceptional size',front,slot,hole8,len(exceptional)-1,flush=True)
    early=[(regular,None)]
    if len(exceptional)>1:
        early+=split_early_exact(exceptional,Phi,Old,sGuard)
    print('exact early refined components',front,slot,hole8,[(len(B)-1,None if S is None else len(S)-1) for B,S in early],flush=True)
    all_cases=[]
    for D,exact_s in early:
        if len(D)<=1 or (exact_s is not None and len(exact_s)<=1): continue
        if hole8:
            all_cases.append((D,exact_s,None))
            continue
        E=mon(guarded(D,[tlead]))
        if len(E)>1:all_cases.append((E,exact_s,None))
        D0=sf(gcdp(D,tlead))
        if len(D0)>1:
            K=ExactRing(D0);ga=K.gen()
            Kc=lambda x:ev(list(map(K,x)),ga)
            R=trim(nested(arith,Kc))
            assert R and len(R)<=3
            if len(R)>1:R[-1].inv()
            else:R[0].inv();continue
            all_cases.append((D0,exact_s,[list(K(v).x) for v in R]))
    print('shared-one-front monic models',front,slot,hole8,
          [(len(q)-1,2 if S is None else len(S)-1,3 if U is None else len(U)-1)
           for q,S,U in all_cases],flush=True)
    return all_cases
