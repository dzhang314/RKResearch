"""Necessary finite-characteristic p7/s8 all-active strict chart audit."""
from itertools import product
from argparse import ArgumentParser
from collections import Counter
from math import comb
p=0

def rref_solve(rows, vals, n):
    """None or one solution and a basis of its homogeneous translation space."""
    M=[[v%p for v in a]+[b%p] for a,b in zip(rows,vals)]
    dims=len(M)
    r=0; pivots=[]
    for j in range(n):
        i=next((i for i in range(r,dims) if M[i][j]),None)
        if i is None:continue
        M[r],M[i]=M[i],M[r]
        den=pow(M[r][j],-1,p);M[r]=[(x*den)%p for x in M[r]]
        for i in range(dims):
            if i!=r and M[i][j]:
                t=M[i][j];M[i]=[(x-t*y)%p for x,y in zip(M[i],M[r])]
        pivots.append(j)
        r+=1
        if r==dims:break
    if any(a[-1] for a in M[r:]):return None
    base=[0]*n
    for i,j in enumerate(pivots): base[j]=M[i][-1]
    basis=[]
    for k in range(n):
        if k not in pivots:
            a=[0]*n;a[k]=1
            for i,j in enumerate(pivots):a[j]=-M[i][k]%p
            basis.append(a)
    return base,basis

def points(lin):
    if lin is None:return
    a,basis=lin
    for w in product(range(p),repeat=len(basis)):
        yield [(c+sum(t*d[i] for t,d in zip(w,basis)))%p for i,c in enumerate(a)]

def kap(u):return (1+2*u-u*u)%p
def headcharts():
    inv2=pow(2,-1,p)
    for u in range(1,p):
        d=(-2+u+4*u*u-u**3)%p
        r0=2*u*(3*u-2)%p
        k=kap(u)
        assert k
        if u not in (1,2):
            # The third row is diagonal plus its sole edge from stage one.
            yield (u,(2-u)%p,k,(1,-2,inv2),0)
        if d and r0:
            # H = -(d*N^2-(3u-2)*(C-1)*(C-1-u)) at the profile level.
            w=2*u%p;r=r0*pow(d,-1,p)%p
            h=(u*u*(u-1)%p,-u*(u-2)*(2*u-1)%p,(u-2)*(u-1)**2*inv2%p)
            yield (u,w,(kap(w)+2*r*u)%p,h,1)
        elif not d and not r0:
            raise AssertionError("Unsupported singular r incidence; requires p with 2,3,5,7 units")

def opN(poly):
    return tuple(((poly[k-1]*pow(k,-1,p) if k else 0)-(poly[k] if k<len(poly) else 0))%p for k in range(len(poly)+1))

def crosspoly(F,G,z,deg=0):
    # (1/z)int_0^z f(x)g(z-x)x^deg dx.
    # Anti-diagonal beta value on monomials: z^(i+j+deg) i!j!/(i+j+deg+1)!.
    from math import factorial
    return sum(a*b*pow(z,i+j+deg,p)*factorial(i+deg)*factorial(j)*
               pow(factorial(i+j+deg+1),-1,p)
               for i,a in enumerate(F) for j,b in enumerate(G))%p

def centers(z,heads,rears):
    u,w,g,h,ty=heads;v,q,j,k,uy=rears
    f,gp=opN(h),opN(k)
    if crosspoly(f,gp,z):return
    t=crosspoly(h,gp,z)
    assert t==crosspoly(f,k,z)
    n=crosspoly(h,gp,z,1);m=crosspoly(f,k,z,1)
    if t:
        C=[(n*pow(t,-1,p)%p,m*pow(t,-1,p)%p)]
    elif n or m:
        return
    else:
        C=product(range(p),repeat=2)
    s0,s1,s2=[crosspoly(h,k,z,d) for d in range(3)]
    for c,d in C:
        if (s2-(c+d)*s1+c*d*s0)%p==0:yield c,d

def all_active_candidates():
    triples=list(headcharts())
    cnt=Counter()
    pure=[pow(k+1,-1,p) for k in range(7)]
    found=[]
    for z,h,t in product(range(1,p),triples,triples):
        u,w,g,_,branch=h;v,j,f,_,rtype=t
        for c,d in centers(z,h,t):
            knots=[1,1+u,1+w,c,d,z-1-j,z-1-v,z-1]
            knots=[a%p for a in knots]
            cnt['causal']+=1
            affine=rref_solve([[pow(c,i,p) for c in knots] for i in range(7)],
                [pure[i]*pow(z,i,p)%p for i in range(7)],8)
            if affine is None:continue
            cnt['quadrature']+=1
            cnt[f'node_groups_{len(set(knots))}']+=1
            for b in points(affine):
                if not all(b):continue
                cnt['all_nonzero_quadrature']+=1
                fixed=[1,kap(u),g]
                refl=[f,kap(v),1]
                M=[];target=[]
                for r in range(5):
                    powers=[b0*pow(x,r,p)%p for b0,x in zip(b,knots)]
                    M.append([powers[3],powers[4],sum(m*n for m,n in zip(powers[5:],refl))%p])
                    target.append(-sum(m*n for m,n in zip(powers[:3],fixed))%p)
                for a,d,k in points(rref_solve(M,target,3)):
                    if not k:continue
                    ss=fixed+[a,d]+[k*t%p for t in refl]
                    cnt['seed_moments']+=1
                    if any(sum(b0*s0*s0*pow(x,i,p) for b0,s0,x in zip(b,ss,knots))%p for i in range(3)):continue
                    if sum(b0*s0**3 for b0,s0 in zip(b,ss))%p:continue
                    cnt['seed_nonlinear']+=1
                    found.append((z,knots,b,ss,branch,rtype))
    return cnt,found

if __name__=='__main__':
    arg=ArgumentParser()
    arg.add_argument('prime',nargs='?',type=int,default=19)
    ns=arg.parse_args();p=ns.prime
    assert p>=11 and not any(x*x%p==2 for x in range(p))
    cnt,sol=all_active_candidates()
    print(p, dict(cnt),len(sol))
    print(*sol[:30],sep='\n')
