"""The fourth Q root is exterior: independent of the earlier quartic parity cut."""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
from runpy import run_path

src=Path(__file__).resolve().parents[1]/'weak-four-complete'/'check_uniform.py'
ref=run_path(str(src))
cases,box,D=(ref['CASES'],ref['enclosure'],ref['D'])

def weight_bounds(case,s,t,R,a):
    P,T,_=cases[case]
    assert P[8]==0<T[8] and P[7]>0
    S0=F(sum(l for l,h in R),D); S1=F(sum(h for l,h in R),D)
    # Ambient polynomial p_x=(1-x)P+xT with leading coefficient x T[8].
    # Its roots are e and seven t_i with sum S. Thus the homogeneous
    # scalar B=-x e equals ((1-x)P[7]+x T[7])/T[8]+x S.
    bounds=[((1-v)*P[7]+v*T[7])/T[8]+v*S
            for v in (s,t) for S in (S0,S1)]
    loB=max(0,min(bounds));hiB=max(bounds)
    assert 0<=loB<=hiB
    # A=x a, and omega=A/(A+B). For x=0 use A=0, B=P[7]/T[8]>0.
    loA=s*R[a][0]/D; hiA=t*R[a][1]/D
    assert loA>=0 and hiA>0 and loA+hiB>0
    L=loA/(loA+hiB); H=hiA/(hiA+loB)
    assert 0<=L<=H<=1
    return L,H

def pair(z,w):
    # The fourth affine factor is (w Y+1-w); clear its positive denominator.
    P=[1]
    for n,d in z:
        assert d>0
        Q=[0]*(len(P)+1)
        for i,c in enumerate(P):
            Q[i]-=n*c; Q[i+1]+=d*c
        P=Q
    Q=[0]*(len(P)+1); n,d=w.numerator,w.denominator
    for i,c in enumerate(P):
        Q[i]+=(d-n)*c; Q[i+1]+=n*c
    assert all(420%(k+i+1)==0 for k in (1,2) for i in range(len(Q)))
    return tuple(sum(v*(420//(k+i+1)) for i,v in enumerate(Q)) for k in (1,2))

def separated(V):
    for i in (0,1):
        if min(v[i] for v in V)>0 or max(v[i] for v in V)<0:
            return True
    for x,y in V:
        signs=[x*b-y*a for a,b in V]
        if min(signs)>=0 or max(signs)<=0:
            if all(t or x*a+y*b>0 for t,(a,b) in zip(signs,V)): return True
    return False

def prove(case):
    roles=[(j,I) for j in range(7) for I in combinations(
        [i for i in range(7) if i!=j],3) if sum(i<j for i in I)>=2]
    todo=[(F(0),F(1),0,roles)]
    leaves=dmax=0
    while todo:
        s,t,depth,active=todo.pop(); dmax=max(depth,dmax)
        R=box(case,s,t); retained=[]
        for a,I in active:
            al,ah=R[a]
            z=[((R[i][0],ah),(R[i][1],al)) for i in I]
            W=weight_bounds(case,s,t,R,a)
            V=[pair(v,w) for v in product(*z) for w in W]
            if not separated(V): retained.append((a,I))
        if not retained:
            leaves+=1
            continue
        assert depth<18,(case,s,t,retained)
        mid=(s+t)/2
        todo.extend([(s,mid,depth+1,retained),(mid,t,depth+1,retained)])
    print(f'{case}: {len(roles)} three-inner-Q ranks, {leaves} leaves, depth {dmax}.')
    return len(roles),leaves,dmax

if __name__=='__main__':
    for c in ('low exterior, X','low exterior, 1-X'): assert prove(c)==(70,7,3)
