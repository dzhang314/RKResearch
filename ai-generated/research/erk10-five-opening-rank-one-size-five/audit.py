"""Exact independent rooted replay of control and true tilted fixture."""
from functools import lru_cache
from itertools import product
import sympy as S

R=S.Rational
X,h,z,u,v=S.symbols("X h z u v")
J=lambda f,z:S.integrate(f,(X,0,z))
P=X**3+u*X**2+v*X
assert S.expand(J(X*(X-h)*(X-h/2),z)-z**2*(z-h)**2/4)==0
assert S.expand(J(X*P,z)-z*J(P,z)+J(J(P,X),z))==0
print("two-functional cubic probe and primitive commutator checked exactly")
jp0,jjp0=J(P,z),J(J(P,X),z)
uv=S.solve((jp0,jjp0),(u,v))
assert uv=={u:-6*z/5,v:3*z*z/10}
assert S.cancel(100*P.subs(X,h).subs(uv)/h-((10*h-6*z)**2-6*z*z))==0
print("split-root rank-one exception requires sqrt(6)")


trees={1:[()]}
for size in range(2,6):
    bank=[(i,t) for i in range(1,size) for t in trees[i]]
    def forests(rem,mn):
        if rem==0:
            yield ()
        else:
            for j in range(mn,len(bank)):
                i,t=bank[j]
                if i<=rem:
                    for q in forests(rem-i,j):
                        yield (t,)+q
    trees[size]=list(forests(size-1,0))
assert [len(trees[i]) for i in trees]==[1,1,2,4,9]
old_degree=[i-1 for i in trees for t in trees[i]]
old_model=S.Matrix(5,len(old_degree),lambda j,i:int(j==old_degree[i]))
flat=[t for i in trees for t in trees[i]]
size=lambda t:1+sum(map(size,t))

def fixture(e,s,p,q,u,v,exception,eval_host=False):
    pol=X**3+u*X**2+v*X
    assert S.cancel(p*(3*s*s+2*s*u+2*v)-s*v)==0
    assert pol.subs(X,s)!=0
    alpha=p*p*(3*s-2*p)/s**3
    beta=pol.subs(X,q)/pol.subs(X,s)
    assert pol.subs(X,p)==alpha*pol.subs(X,s)
    O=S.zeros(5)
    O[1,0]=e
    O[2,1]=s*s/(2*e)
    O[3,1]=alpha*s*s/(2*e)
    O[3,2]=(p*p/2-O[3,1]*e)/s
    O[4,1]=beta*s*s/(2*e)
    a,b=S.symbols("a b")
    sol=S.solve((s*a+p*b-(q*q/2-O[4,1]*e),
                 s*s*a+p*p*b-(q**3/3-(2*e*s/3)*O[4,1])),(a,b))
    O[4,2],O[4,3]=sol[a],sol[b]
    for i,xi in enumerate([0,e,s,p,q]):
        O[i,0]=xi-sum(O[i,j] for j in range(1,5))
    xo=[R(0),e,s,p,q]; xh=[R(1,5),R(0),R(2,5),R(4,5)]
    row=S.Matrix([[1,0,0,0,0],[0,0,-alpha,1,0],[0,0,-beta,0,1]])
    E=lambda x,d:S.Matrix([[xi**j for j in range(d+1)] for xi in x])
    Pi=(row*E(xo,2)).inv()*row
    B=S.Matrix([[0,0,0,0],[R(1,8),0,0,0],[-R(1,7),R(1,3),0,0],[R(1,12),R(2,15),R(1,10),0]])
    EJ=S.Matrix([[xi**(j+1)/(j+1) for j in range(3)] for xi in xh])
    L=(EJ-B*E(xh,2))*Pi
    A=O.row_join(S.zeros(5,4)).col_join(L.row_join(B))
    assert list(A*S.ones(9,1))==xo+xh
    @lru_cache(None)
    def deriv(t):
        out=S.ones(9,1)
        for child in t:
            out=out.multiply_elementwise(size(child)*(A*deriv(child)))
        return out
    mat=S.Matrix.hstack(*(deriv(t) for t in flat))
    actual_old,actual_hi=mat[:5,:],mat[5:,:]
    deltas=actual_hi-E(xh,4)*old_model
    assert deltas[:,:8]==S.zeros(4,8)
    d=B*S.Matrix([pol.subs(X,xi) for xi in xh])-S.Matrix([J(pol,xi) for xi in xh])
    assert d!=S.zeros(4,1) and deltas.rank()==d.row_join(deltas).rank()==1
    # Genuine old pure controls and their high responses.
    c=A*S.ones(9,1)
    d0=A*c-c.applyfunc(lambda x:x*x/2)
    V=A*d0
    pure=S.Matrix.hstack(d0,V,c.multiply_elementwise(V),A*V)
    q3=A*c.applyfunc(lambda x:x**3)-c.applyfunc(lambda x:x**4/4)
    assert pure[5:,:]==S.zeros(4,4)
    assert q3[5:,:]==d
    om=actual_old
    kernels=S.Matrix.hstack(*om.nullspace())
    models=old_model*kernels
    assert models.rank()==4 and models[0,:]==S.zeros(1,models.cols)
    pure_zero=S.Matrix.hstack(*(kernels*v for v in models.nullspace()))
    gained=(actual_hi*pure_zero).rank()
    if not exception:
        assert pure[:5,:].rank()==4 and gained==1
        print("generic old model-zero four pivots recover full pure input despite nonzero literal dirt")
    else:
        assert pure[:5,:].rank()==3 and gained==0
        N=pure[1:5,:].T.nullspace()
        assert len(N)==1
        tau=N[0].T
        ell=-tau*E(xo,4)[1:5,:]/(tau*q3[1:5,:])[0]
        assert ell*S.Matrix([0,v,u,1,0])==S.zeros(1,1)
        assert ell*S.Matrix([0,0,v,u,1])==S.zeros(1,1)
        assert (ell*S.Matrix([0,0,v/2,u/3,R(1,4)]))[0]==1
        assert actual_hi*kernels==E(xh,4)*models+d*ell*models
        Q=S.Matrix.hstack(*ell[:,1:].nullspace())
        q0=Q.col_join(S.zeros(1,3))
        q1=S.zeros(1,3).col_join(Q)
        if not eval_host:
            assert q0.row_join(q1).rank()==5 and u*u-4*v<0
            print("exceptional actual tilt functional on X,...,X^4:",list(ell)[1:])
            print("all 17 actual profiles and pure marked input growth verified in the exceptional fixture")
        else:
            assert q0.row_join(q1).rank()==4
            assert ell[:,1:]==S.Matrix([[q**i/J(pol,q) for i in range(1,5)]])
            profile_error=actual_old-E(xo,4)*old_model
            assert deltas==(-d/J(pol,q))*profile_error[4,:]
            modelzero=S.Matrix.hstack(*old_model.nullspace())
            oldpure=actual_old*modelzero
            for k in range(1,5):
                j=flat.index(((),)*k)
                true_bush=S.eye(len(flat))[:,j]
                target=S.Matrix([0,0,0,0,q**k])
                coeff,args=oldpure.gauss_jordan_solve(target-actual_old*true_bush)
                coeff=coeff.subs({var:0 for var in args})
                profiles=mat*(true_bush+modelzero*coeff)
                assert profiles[:4,:]==S.zeros(4,1)
                assert profiles[4:,:]==S.Matrix([xi**k for xi in [q]+xh])
            print("split fixed decoder: actual ell(f) = (1024/729) f(9/4); all reclassified pure sources checked")

fixture(R(1,8),R(1,3),R(1,4),R(1,2),R(0),-R(1,2),False)
fixture(R(1,8),R(1),R(3,4),R(1,2),-R(5,2),R(3),True)


fixture(R(1,8),R(1),R(3,2),R(9,4),-R(15,4),R(27,8),True,True)

# Check literal q host formula when its old beta is zero, with symbolic s.
s,p,q=S.symbols("s p q")
alpha=p*p*(3*s-2*p)/s**3
b=q*q*(2*q-3*s)/(6*p*(p-s))
a=(q*q/2-p*b)/s
assert S.cancel(a+alpha*b-q*q*(3*p*s-(2*p-s)*q)/(3*s**3))==0
print("fixed decoder split old-host scalar equation checked symbolically")

# Nonzero taps from a genuinely erased axis: compare all short pure words.
B=S.Matrix([[0,0,0,0],[1,0,0,0],[2,3,0,0],[5,3,0,0]])
C=S.diag(2,3,4,4); E=S.Matrix([1,2,3,4]); w=S.Matrix([[7,0,2,-2]])
Q=S.diag(1,0,1,1)
for length in range(6):
    for letters in product([B,C],repeat=length):
        W=S.eye(4); Wq=Q
        for A in letters:
            W=W*A
            Wq=Wq*A*Q
        assert (w*W)[0,1]==0
        assert w*W*E==w*Wq*E
print("all 63 short raw words agree after erasing a nontrivial output-silent donor axis")
