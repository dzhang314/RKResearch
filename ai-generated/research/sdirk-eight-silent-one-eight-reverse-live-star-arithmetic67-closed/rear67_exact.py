"""Bounded CRT rational exact outer projection, including full image checks."""
from rear67_model import model
from silent8_diag import modular_resultant
from fast_outer_interpolate import get_compiler
from flint import fmpz_poly
from sympy import nextprime
from ctypes import c_ulong
from time import perf_counter

def full_native(P,Q,p):
    item=get_compiler()
    if item is None:return modular_resultant(P,Q,p)
    fn,_=item
    xs=[]
    g0,s0=P.degrees();g1,s1=Q.degrees()
    for A,g,s in ((P,g0,s0),(Q,g1,s1)):
        X=(c_ulong*((g+1)*(s+1)))()
        for (i,j),a in A.to_dict().items():
            X[j*(g+1)+i]=int(a)%p
        if not any(X[s*(g+1)+i] for i in range(g+1)):return None
        xs.append(X)
    C=(c_ulong*(g0*s1+g1*s0+1))()
    assert fn(p,xs[0],g0,s0,xs[1],g1,s1,C)==0
    return list(C)

def fixed_exact(P,Q,tag):
    g0,s0=P.degrees();g1,s1=Q.degrees()
    cap=g0*s1+g1*s0
    bound=sum(abs(int(c)) for c in P.to_dict().values())**s1*sum(abs(int(c)) for c in Q.to_dict().values())**s0
    Z=[0]*(cap+1);M=1;p=2**60;n=0;start=perf_counter()
    print('outer start',tag,cap,bound.bit_length(),bool(get_compiler()),flush=True)
    while M<=2*bound:
        p=int(nextprime(p+1000))
        A=full_native(P,Q,p)
        if A is None:continue
        if n==0: assert A==modular_resultant(P,Q,p)
        M1=pow(M,-1,p)
        Z=[z+M*((a-z)*M1%p) for z,a in zip(Z,A)]
        M*=p;n+=1
        if n%25==0:print('outer progress',tag,n,round(perf_counter()-start,2),flush=True)
    Z=[z if 2*z<M else z-M for z in Z]
    assert any(Z) and all(abs(z)<=bound for z in Z)
    p=1129
    E=modular_resultant(P,Q,p)
    assert E and all((a-b)%p==0 for a,b in zip(E,Z))
    h=next(i for i,z in enumerate(Z) if z)
    F=fmpz_poly(Z[h:]);F=F//F.content()
    assert (cap,bound.bit_length(),F.degree()+h,h,n)=={
        11:(2556,7207,2556,271,121),
        14:(4056,11126,4056,470,186),
    }[tag]
    print('outer exact',tag,F.degree()+h,h,F.degree(),n,round(perf_counter()-start,2),flush=True)
    return F

def projection(d):
    A,B,J,*_=model()
    X=fixed_exact(A,J[d],d)
    F=X.factor_squarefree()[1]
    Y=fmpz_poly([1]);fs=[]
    for M,a in F:
       T=M.factor()[1]
       assert T and all(b==1 for P,b in T)
       for Z,e in T:fs.append((Z,a));Y*=Z**a
    assert Y==X or Y==-X
    return fs
