from flint import fmpz_poly
from time import monotonic

def uv_coeffs(p,u,v):
    P=p.clear_denoms()[1]
    c=[{} for _ in range(P.degree(u)+1)]
    for (i,j),w in P.terms():
        c[i][j]=int(w)
    return [fmpz_poly([t.get(j,0) for j in range(max(t,default=0)+1)]) for t in c]

def project_resultant(p,q,u,v):
    r"""Evaluate Sylvester determinant at enough integral nodes and reconstruct in Z[v]."""
    A=uv_coeffs(p,u,v)
    B=uv_coeffs(q,u,v)
    ma,mb=len(A)-1,len(B)-1
    da,db=p.degree(v),q.degree(v)
    n=ma*db+mb*da # Sylvester row-degree bound
    lo=1000
    while any(not A[-1](k) or not B[-1](k) for k in range(lo,lo+n+1)):
        lo+=n+1
    vals=[]
    for k in range(lo,lo+n+1):
        a,b=fmpz_poly([c(k) for c in A]),fmpz_poly([c(k) for c in B])
        assert a.degree()==ma and b.degree()==mb
        vals.append(a.resultant(b))
    vpoly=fmpz_poly([0,1])
    res,fall,fac=fmpz_poly(),fmpz_poly([1]),1
    for j in range(n+1):
        c,r=divmod(vals[0],fac)
        assert not r
        res+=c*fall
        vals=[b-a for a,b in zip(vals, vals[1:])]
        fall*=vpoly-(lo+j)
        fac*=j+1
    assert res and res.degree()<=n
    return res
