"""Independent exact F19 audit: integrate ordinary polynomial words directly."""
from itertools import product
from math import comb
from collections import Counter

P = 19
red = lambda n: n % P
inv = lambda n: pow(n % P, -1, P)

def pmul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            c[j+k] += x*y
    return list(map(red, c))

def reflected(f, z):
    return [sum(f[j]*(-1)**k*comb(j,k)*z**(j-k)
                for j in range(k,len(f))) % P for k in range(len(f))]

def primitive_minus_id(f):
    return [(-f[0]) % P] + [
        (f[k-1]*inv(k) - (f[k] if k < len(f) else 0)) % P
        for k in range(1, len(f)+1)
    ]

def mean(f, z):
    return sum(a*z**i*inv(i+1) for i,a in enumerate(f)) % P

def cross(A,B,z,deg=0):
    return mean([0]*deg + pmul(A,reflected(B,z)),z)

def defect(u):
    return (1+2*u-u*u)%P

# Enumerate all local third rows, rather than assuming the branch formula
# when generating the independently replayed chronological charts.
edges=[]
for u,w,r in product(range(1,19),range(1,19),range(19)):
    if w == u: continue
    g=(defect(w)+2*r*u)%P
    if r*u*(2*u-w)%P:continue
    if (w*g-defect(u)*(w+r*(defect(u)-1)))%P:continue
    if r:
        du=(-2+u+4*u*u-u**3)%P
        # -du*L_2(X)+(3u-2)(X-1)(X-1-u).
        H=[(-du + (3*u-2)*(1+u))%P,
           (2*du - (3*u-2)*(2+u))%P,
           (-du*inv(2)+3*u-2)%P]
    else:
        H=[1,-2,inv(2)]
    edges.append((u,w,g,H))
assert len(edges)==33

def lagrange_data(x,keep,z):
    out=[]
    for i in keep:
        q=[1]
        d=1
        for j in keep:
            if i!=j:
                q=pmul(q,[-x[j],1])
                d=d*(x[i]-x[j])%P
        out.append((i,[c*inv(d)%P for c in q],mean(q,z)*inv(d)%P))
    return out

def val(poly,x):
    return sum(a*x**j for j,a in enumerate(poly))%P

def minor4(M,inds):
    from itertools import permutations
    s=0
    for pi in permutations(range(4)):
        sg=(-1)**sum(pi[j]>pi[i] for j in range(4) for i in range(j+1,4))
        p=1
        for r,c in zip(inds,pi):p=p*M[r][c]%P
        s+=sg*p
    return s%P

counts=Counter()
for z,L,R in product(range(1,19),edges,edges):
    u,w,g,H=L
    v,k,j,K=R
    F,G=primitive_minus_id(H),primitive_minus_id(K)
    if cross(F,G,z):continue
    D=cross(H,G,z)
    X=cross(H,G,z,1);Y=cross(F,K,z,1)
    if not D:
        assert X or Y, (z,L,R)
        continue
    a,b=X*inv(D)%P,Y*inv(D)%P
    if cross(pmul(H,[-a,1]),pmul(K,[b-z,1]),z):continue
    counts['causal']+=1
    x=[n%P for n in [1,1+u,1+w,a,b,z-1-k,z-1-v,z-1]]
    # If six or fewer clocks, find the explicit polynomial which kills the
    # quadrature. This rule does not use Gaussian elimination.
    sites=sorted(set(x))
    if len(sites)<7:
        q=[1]
        for t in sites:q=pmul(q,[-t,1])
        assert any(mean([0]*i+q,z) for i in range(7-len(sites)))
        counts['quad_reject']+=1
        continue
    free=next(i for i in range(8) if len({s for jx,s in enumerate(x) if jx!=i})==7)
    keep=[i for i in range(8) if i!=free]
    Ld=lagrange_data(x,keep,z)
    counts['quad_family']+=1
    for bf in range(P):
        beta=[0]*8
        beta[free]=bf
        for i,l,m in Ld:beta[i]=(m-bf*val(l,x[free]))%P
        assert all(sum(y*X**d for y,X in zip(beta,x))%P == z**d*inv(d+1)%P for d in range(7))
        assert any(beta[:3]), "first-three-ghost mask survived"
        if not all(beta):continue
        counts['first_seed_reject']+=1
        M=[]
        for d in range(5):
            a=[y*X**d%P for y,X in zip(beta,x)]
            M.append([a[3],a[4],a[5]*j+a[6]*defect(v)+a[7],
                      a[0]+a[1]*defect(u)+a[2]*g])
        assert any(minor4(M, [i for i in range(5) if i!=skip]) for skip in range(5))
assert counts==Counter(causal=150,quad_reject=72,quad_family=78,first_seed_reject=1014),counts
assert all(x*x%P!=2 and (x**3-9*x*x+18*x-6)%P for x in range(P))
# Independent grouped width check with repeats, by the scalar nodal-product test.
from itertools import combinations
for width in range(1,5):
    for S in combinations(range(P),width):
        q=[1]
        for r in S:q=pmul(q,[-r,1])
        assert any(mean([0]*i+q,1) for i in range(7-width)), S
print("Complete F19 independent audit:", dict(counts))
