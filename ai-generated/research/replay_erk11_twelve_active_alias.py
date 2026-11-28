"""Exact standard-library certificate for the q10 n12 double-zero dormant alias."""
from fractions import Fraction as F
from math import comb

S=(17640,-190365,869470,-2140908,2982540,-2214300,680625)
D=871363785600000
def add(*ps):
    r={}
    for p in ps:
        for i,c in p.items():r[i]=r.get(i,0)+c
    return {i:c for i,c in r.items() if c!=0}

def scale(p,c):
    return {i:c*x for i,x in p.items() if c*x!=0}

def mul(*ps):
    r={(0,0):1}
    for p in ps:
        t={}
        for (i,j),c in r.items():
            for (k,l),d in p.items():
                t[i+k,j+l]=t.get((i+k,j+l),0)+c*d
        r={i:c for i,c in t.items() if c!=0}
    return r

def integ(p,k=0):
    r={}
    for (i,j),v in p.items():r[i,0]=r.get((i,0),0)+F(v,j+k+1)
    return {i:c for i,c in r.items() if c!=0}

def poly(c):
    return {(i,0):v for i,v in enumerate(c) if v!=0}

def hom_replay(num,den):
    # Coefficients of den(T)^6 S(num(T)/den(T)) for affine num, den.
    E=[0]*7
    for i,c in enumerate(S):
        for j in range(i+1):
            u=c*comb(i,j)*num[0]**(i-j)*num[1]**j
            for k in range(7-i):
                E[j+k]+=u*comb(6-i,k)*den[0]**(6-i-k)*den[1]**k
    return E

def replay():
    V={(0,4):1,(1,3):-2,(2,2):1}
    W={(0,2):1,(0,3):-2,(0,4):1}
    P={(i,j+1):F(v,j+1) for (i,j),v in V.items()}
    WB={(i,j+1):F(v,j+1) for (i,j),v in W.items()}
    Q=add(integ(W),scale(WB,-1))
    H=integ(mul(P,W));assert H==integ(mul(V,Q))
    C1=integ(mul(P,W),1);C2=integ(mul(V,Q),1)
    I0,I1,I2=[integ(mul(V,W),j) for j in range(3)]
    data=[
     (H,12600,(7,-25,25)),(C1,831600,(336,-1155,1100)),
     (C2,831600,(280,-924,825)),(I0,1260,(5,-15,12)),
     (I1,2520,(7,-20,15)),(I2,13860,(28,-77,55))]
    assert all(scale(p,k)==poly(co) for p,k,co in data)
    P0=add(mul(H,H,I2),scale(mul(H,I1,add(C1,C2)),-1),mul(I0,C1,C2))
    assert scale(P0,D)==poly(S)
    print('Twice-dormant center at d=0: exact sextic from all six rational clock integrals.')
    windows=[
      ((0,-1),(1,0),[17640,190365,869470,2140908,2982540,2214300,680625]),
      ((0,1),(2,2),[1128960,682080,387520,181216,35088,11368,3721]),
      ((5,8),(10,10),[58140625,451575000,1577370000,2686124000,2230776000,384636000,152224000]),
      ((4,1),(5,0),[2378500,5507375,17992750,25162500,16483500,5263500,680625]),
    ]
    for num,den,expect in windows:
        test=hom_replay(num,den)
        assert test==expect and min(test)>0
    print('All coefficients positive in the two exterior and two rational interior charts.')

if __name__=='__main__':
    replay()
