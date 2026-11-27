# Exact rational negative control for tall-only DIRK10/11 obstructions.
# Usage: python3 -B check-dirk10-tall-four-zero-control.py (requires SymPy).
from itertools import product
import sympy as S
from random import Random
from functools import lru_cache

N=11
Z=[0,4,6,10]
L=5
c=S.Matrix([S.Rational(i,10) for i in range(N)])
one=S.ones(N,1)
y=one-c
b=S.Matrix(N,N,lambda j,i:c[i]**j).inv()*S.Matrix([S.Rational(1,j+1) for j in range(N)])
B=b.T
diag=[0 if i in Z else S.Rational(1,20) if i in (1,9) else S.Rational(2*i+1,37) for i in range(N)]
print("nodes", list(c), "weights", list(b), "diag",diag,flush=True)
idx=[(i,j) for i in range(N) for j in range(i)]
sym=S.symbols('a:'+str(len(idx)))
A=S.diag(*diag)
for e,x in zip(idx,sym):A[e]=x
sq=lambda v:v.applyfunc(lambda u:u*u)
eq=list(A*one-c)+list(A*c-sq(c)/2)+list(B*A-B.multiply_elementwise(y.T))+list(B.multiply_elementwise(y.T)*A-B.multiply_elementwise(sq(y).T)/2)
sols=S.linsolve(eq,sym)
if sols==S.EmptySet:raise ValueError('no base')
base=list(sols)[0]
params=set().union(*(x.free_symbols for x in base))
print('free',len(params),flush=True)
rng=Random(514)
nn=set(range(N))-set(Z)
nn=sorted(nn)
Y=B.multiply_elementwise(y.T)
C=S.diag(*c)

def residues(A):
    R=C*A-A*C-A**2
    return R.extract(Z,Z)-R.extract(Z,nn)*R.extract(nn,nn).inv()*R.extract(nn,Z)

def response(A):
    ret=[]
    u=one
    for k in range(1,11):
        if k>=6:ret.append((B*u)[0])
        u=A*u
    ret.append(residues(A)[2,1])
    return S.Matrix(ret)

u=S.Matrix.vstack(B[:,L:],Y[:,L:]).nullspace()
v=S.Matrix.vstack(one.T[:,:L],c.T[:,:L]).nullspace()
basis=[]
for a,h in product(u,v):
    D=S.zeros(N)
    D[L:,:L]=a*h.T
    basis.append(D)
for trial in range(3):
    p0={x:S.Rational(rng.randint(-3,3),7) for x in sorted(params,key=str)}
    A0=A.subs(dict(zip(sym,[x.subs(p0) for x in base])),simultaneous=True)
    f=response(A0)
    H=S.Matrix.hstack(*(response(A0+D)-f for D in basis))
    print('linear cut rank',H.rank(),flush=True)
    target=S.Matrix([S.Rational(1,S.factorial(k)) for k in range(6,11)]+[0])
    pars=S.symbols('l:'+str(len(basis)))
    X=S.linsolve((H,target-f),pars)
    if X!=S.EmptySet:
        xl=list(X)[0]
        pf=set().union(*(x.free_symbols for x in xl))
        xl=[x.subs({p:0 for p in pf}) for x in xl]
        A1=A0+sum((d*xx for d,xx in zip(basis,xl)),S.zeros(N))
        assert response(A1)==target
        def P(k):return c.applyfunc(lambda x:x**k)
        assert A1*one==c and A1*c==P(2)/2 and B*A1==Y and Y*A1==B.multiply_elementwise(sq(y).T)/2
        u=one
        for k in range(1,11):
            assert (B*u)[0]==S.Rational(1,S.factorial(k))
            u=A1*u
        R=C*A1-A1*C-A1**2
        assert R.rank()==N-4
        assert residues(A1)==S.zeros(4)
        t=(B.multiply_elementwise(P(3).T)*A1*P(2))[0]-S.Rational(1,21)
        assert t!=0

        # Independently verify literal rooted-tree order, not just the tall trees.
        pool=[[] for _ in range(7)]
        pool[1]=[()]
        for n in range(2,7):
            choices=[(m,h) for m in range(1,n) for h in pool[m]]
            def children(rem, start):
                if rem==0:
                    yield ()
                else:
                    for t in range(start,len(choices)):
                        size,child=choices[t]
                        if size<=rem:
                            for more in children(rem-size,t):
                                yield (child,)+more
            pool[n]=list(children(n-1,0))
        @lru_cache(None)
        def gamma_node(tree):
            return (1+sum(gamma_node(t)[0] for t in tree),
                    (1+sum(gamma_node(t)[0] for t in tree))*
                    S.prod(gamma_node(t)[1] for t in tree))
        @lru_cache(None)
        def elementary(tree):
            r=one
            for t0 in tree:
                r=r.multiply_elementwise(A1*elementary(t0))
            return r
        assert [len(pool[k]) for k in range(1,7)]==[1,1,2,4,9,20]
        for k in range(1,7):
            for tree in pool[k]:
                assert (B*elementary(tree))[0]*gamma_node(tree)[1]==1
        z=S.symbols("z")
        H0=S.Poly(S.prod(1-e*z for e in diag),z)
        tall=[S.S.One]
        u=one
        for k in range(1,N+1):
            tall.append((B*u)[0])
            u=A1*u
        Acoeff=[sum(H0.nth(j)*tall[k-j] for j in range(min(k,H0.degree())+1))
                for k in range(N+1)]
        N0=S.Poly(sum(a*z**k for k,a in enumerate(Acoeff)),z)
        oldG=S.gcd(H0,N0)
        deg_m=N0.degree()-oldG.degree()
        deg_r=H0.degree()-oldG.degree()
        assert S.gcd(N0.exquo(oldG),H0.exquo(oldG)).degree()==0
        print("literal order 6; tall through 10; reduced numerator degree",deg_m,
              "and denominator degree",deg_r)

        print('order-seven mixed error for b^T C^3 A c^2:',t,flush=True)
        print('rational row max denominator digits',max(len(str(x.q)) for x in A1),flush=True)
        break
else:
    print("No control found")
