"""Exact two-doubled-read prefixes at both ends of the seven-clock constant graph."""
import sympy as S
from sympy.polys.rings import ring
from itertools import product

A=S.Symbol('a')
F=S.Poly(5*A*A-3,A).monic()
assert F.is_irreducible
K=S.QQ.algebraic_field((F,A))
a=K.unit
q0,q1,q2=K.zero,K.one,K(2)
r0=q1/2
R,T=ring('T',K)
def hub(u):return -2+u+4*u*u-u**3
def num(u):return (1+4*u-4*u*u)*hub(u)+4*u*u*(3*u-2)
def kappa(u):return 1+2*u-u*u
def val(p,x):return p.evaluate(T,x)
gweight=(K(S.Rational(5,18)),K(S.Rational(4,9)),K(S.Rational(5,18)))

def check(m,end):
    D={ep:m*(1+ep*a) for ep in (-1,0,1)}
    assert D[end]==q1 and D[-end]==2*m-1
    L4=lambda t:t**4-K(S.Rational(6,7))*m*m*t*t+K(S.Rational(3,35))*m**4
    L={ep:L4(x-m) for ep,x in D.items()}
    assert all(L.values())
    starts=[]
    for ep,x2 in D.items():
        if ep==end:continue
        u=x2-1;k=kappa(u)
        assert u
        if not k: continue
        for mode in ('arith','star'):
            if mode=='arith':
                if 3*u==q2: continue
                assert hub(u)
                x3=1+2*u;q=num(u)/hub(u)
            else:
                if u in (q1,q2): continue
                x3=3-u;q=k
            if not q:continue
            d3=next((v for v,x in D.items() if x==x3),None)
            if d3 in (end,ep):continue
            starts.append((mode,ep,d3,x3,k,q))
    print('m',K.to_sympy(m),'prefixes',[(mod,i,j) for mod,i,j,*_ in starts])
    counts=[0,0,0,0,0]
    for (mode,i,j,x3,k,q),(rev,iR,jR,x3R,kR,qR) in product(starts,repeat=2):
        lf={end:r0,i:k/2}
        rr={-end:r0,-iR:kR/2}
        if j is not None: lf[j]=q/2
        if jR is not None: rr[-jR]=qR/2
        shared=set(lf).intersection(rr)
        assert shared
        multipliers={-L[d]/(lf[d]*rr[d]) for d in shared} # common B*lambda
        if len(multipliers)!=1:
            counts[0]+=1
            continue
        M=multipliers.pop()
        assert M
        if j is not None or jR is not None:
            print('non both-singleton-third survives products', mode,i,j,rev,iR,jR)
            counts[4]+=1
            continue
        r=q/2
        # Singleton residuals at reflected end are r/lambda.
        lam=q/qR
        B=M/lam
        if any(lf[d]==lam*rr[d] for d in shared) or x3==2*m-x3R:
            counts[1]+=1
            continue
        coords={d: L[d]/g-B*g for d,g in (lf|{d:lam*v for d,v in rr.items()}).items()}
        assert all(coords[d]==L[d]/lf[d]-B*lf[d]==L[d]/(lam*rr[d])-B*(lam*rr[d]) for d in shared)
        # Trace of the nilpotent G^{-1}(A + A^star - 2m*1*b^T).
        ww={d:c for d,c in zip((-1,0,1),gweight)}
        row={d:(2-2*m*ww[d])/L[d] for d in (-1,0,1)}
        if len(coords)==2:
            d=(set(D)-set(coords)).pop()
            coords[d]=(-(8-2*m)/r-sum(row[j]*z for j,z in coords.items()))/row[d]
        else:
            assert len(coords)==3
            if (8-2*m)/r+sum(row[d]*z for d,z in coords.items()):
                counts[2]+=1
                continue
        # Interpolate the quadratic A_2 from its three distinct values.
        A2=R.zero
        for d,z in coords.items():
            term=R(z)
            for dd in coords:
                if d!=dd:term*=(T-(D[dd]-m))/R(D[d]-D[dd])
            A2+=term
        assert all(val(A2,D[d]-m)==z for d,z in coords.items())
        H4=L4(T)-r*(A2+B*r)
        if val(H4,x3-m) or val(H4,m-x3R):
            counts[3]+=1
            continue
        print('both S-third survives through trace',mode,i,j,rev,iR,jR)
        counts[4]+=1
    print('read-out',counts)
    assert not counts[4]
    return counts

if __name__=='__main__':
    assert check(K.one,0)==[8,4,4,0,0]
    assert check(K.one/(1-a),-1)==[7,1,4,4,0]
