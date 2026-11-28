"""Exact front Cramer and fifth-remainder pivots for exceptional star seventh."""
from flint import fmpq_mpoly_ctx, fmpq, fmpq_poly
from functools import lru_cache
C=fmpq_mpoly_ctx.get(("q","r","gamma"),ordering="lex")
q,r,g=C.gens()
def det(M):
 a,b,c=M
 return sum(a[i]*(b[(i+1)%3]*c[(i+2)%3]-b[(i+2)%3]*c[(i+1)%3]) for i in range(3))

def co(P,j):
 return C.from_dict({(0,k,l):v for (i,k,l),v in P.to_dict().items() if i==j})

def guard(dividend,ds):
 out=[]
 for a in ds:
  k=0
  while 1:
   p,b=divmod(dividend,a)
   if b:break
   dividend=p;k+=1
  out.append(k)
 return dividend,out

def prem(N,Q):
 lc=co(Q,2)
 while N and N.degrees()[0]>1:
  k=N.degrees()[0]
  N=lc*N-co(N,k)*Q*q**(k-2)
 return N


def monicq(f):
    return f/f.leading_coefficient()



def mul(a,b):
    z=[C.constant(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            z[i+j]+=x*y
    return z


def ev(P,x):
    return sum(a*x**i for i,a in enumerate(P))


def integ(P,j=0):
    return sum(a/(i+j+1) for i,a in enumerate(P))


@lru_cache(None)
def basis():
    d2=(1680*g**4-840*g**3+180*g*g-20*g+1)/4
    d1=-1680*g**4+1050*g**3-270*g*g+35*g-2
    d0=(2520*g**4-1680*g**3+540*g*g-120*g+11)/4
    ell0=fmpq(4,3)*(1-2*d0)
    ell1=8*(d2-70*g**4)
    y=(3*q-g)/2
    D=d2*q*q+d1*g*q+d0*g*g
    U=ell0*g**3+ell1*y*g*g+fmpq(4,3)*D*(5*g-q)
    V=d2*(q+y)+g*d1
    C3=[6*g**3,-18*g*g,9*g,C.constant(-1),C.constant(0)]
    E2=[2*g*g,-4*g,C.constant(1)]
    J=lambda P,j:integ(P,j+1)-r*integ(P,j)
    M=[[J(E2,i+j) for j in range(3)] for i in range(3)]
    b=[-J(C3,j) for j in range(3)]
    h=det(M)
    abc=[det([[b[i] if j==k else M[i][j] for j in range(3)] for i in range(3)])
         for k in range(3)]
    A,B,L=abc
    C0,err=divmod(L,g*g)
    assert not err
    H=[h*x+y for x,y in zip(C3,mul(E2,abc))]
    assert H[-1]==L
    Q=A+B*q+L*q*q
    N=B+L*(q+y)
    K0=d2*B-g*d1*L
    Pi=ell1/2
    hr,beta=ev(H,r),integ(H)
    lr=70*r**4-140*r**3+90*r*r-20*r+1
    gs=(g,h,C0,Pi,hr,beta,lr,K0,N)
    F=U*N-8*g*g*V*h
    return Q,F,H,gs,abc,h


def small_exact_guard(rows,guard,M):
    """Common gcd with a cubic guard over the exact field Q[gamma]/M."""
    def as_r_poly(q):
        terms=q.to_dict()
        return [fmpq_poly([terms.get((0,j,k),0) for k in range(q.degrees()[2]+1)])%M
                for j in range(q.degrees()[1]+1)]
    def trim(a):
        while a and not a[-1]:
            a.pop()
        return a
    def inv(u):
        z,a,_=u.xgcd(M)
        assert z==fmpq_poly([1])
        return a%M
    def rem(a,b):
        a=trim(a[:]); b=trim(b[:])
        h=inv(b[-1])
        while a and len(a)>=len(b):
            z=(h*a[-1])%M
            off=len(a)-len(b)
            for i,x in enumerate(b):
                a[i+off]=(a[i+off]-x*z)%M
            trim(a)
        return a
    def gcd(a,b):
        while b:
            a,b=b,rem(a,b)
        h=inv(a[-1])
        return [(h*v)%M for v in a]
    w=trim(as_r_poly(guard))
    for row in rows:
        w=gcd(w,rem(as_r_poly(row),w))
    return len(w)-1

def reduce_coef(x,p):
    return int(x.p)*pow(int(x.q),-1,p)%p
