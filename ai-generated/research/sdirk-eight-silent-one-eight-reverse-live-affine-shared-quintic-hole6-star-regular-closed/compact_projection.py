"""Exact physical fourth-clock projection for the regular star-sixth branch."""
from flint import fmpq_mpoly_ctx, fmpq, fmpq_poly, nmod_mpoly_ctx, nmod_poly
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

@lru_cache(None)
def basis():
 d2=(1680*g**4-840*g**3+180*g*g-20*g+1)/4
 d1=-1680*g**4+1050*g**3-270*g*g+35*g-2
 d0=(2520*g**4-1680*g**3+540*g*g-120*g+11)/4
 qp=(3*q-g)/2
 D=d2*q*q+d1*g*q+d0*g*g
 U=fmpq(4,3)*(1-2*d0)*g**3+8*(d2-70*g**4)*qp*g*g+fmpq(4,3)*D*(5*g-q)
 V=d2*(q+qp)+g*d1
 C3=[6*g**3,-18*g*g,9*g,C.constant(-1)]
 E2=[2*g*g,-4*g,C.constant(1)]
 def mo(q,j):return sum(c/(i+j+1) for i,c in enumerate(q))
 def f(q,j):return mo(q,j+1)-r*mo(q,j)
 M=[[f(E2,i+j) for j in range(3)] for i in range(3)]
 vv=[-f(C3,i) for i in range(3)]
 h=det(M)
 A,B,D2=[det([[vv[i] if k==j else M[i][k] for k in range(3)] for i in range(3)]) for j in range(3)]
 H=[A,B,D2]
 Q=A+B*q+D2*q*q
 J=r**4-16*g*r**3+72*g*g*r*r-96*g**3*r+24*g**4
 LR=70*r**4-140*r**3+90*r*r-20*r+1
 M4=(r**4/4-g*r**3-(q+4*g)*(r**3/3-g*r*r)+(4*q+2*g)*(g*r*r/2-g*g*r)-2*q*(g*g*r-g**3))
 N=B+D2*(q+qp)
 F=U*N-8*g*g*V*h
 T=(9*h-N)*g**6*LR+D*(h*J-4*N*M4)
 return h,H,Q,F,T,(g,h,D2,LR),(U,V,D)

def prem(N,Q):
 lc=co(Q,2)
 while N and N.degrees()[0]>1:
  k=N.degrees()[0]
  N=lc*N-co(N,k)*Q*q**(k-2)
 return N


def monicq(f):
    return f/f.leading_coefficient()


@lru_cache(None)
def projections():
    h,abc,Q,F,T,_,_=basis()
    c0,rem=divmod(abc[2],g**2)
    assert not rem
    Pi=1400*g**4-840*g**3+180*g*g-20*g+1
    G=(g,h,c0,Pi)
    assert h.degrees()==(0,3,6)
    assert [a.degrees() for a in abc]==[(0,3,7),(0,3,6),(0,3,5)]
    assert Q.degrees()==(2,3,7) and F.degrees()==(4,3,13) and T.degrees()==(4,7,16)
    f,fe=guard(prem(F,Q),G)
    t,te=guard(prem(T,Q),G)
    assert fe==[2,0,1,1] and te==[2,0,1,0]
    assert [z.degrees() for z in (f,t)]==[(1,9,19),(1,13,26)]
    D=[]
    for P,Z in ((Q,f),(f,t),(Q,t)):
        u,e=guard(P.resultant(Z,0),G)
        assert e==[8,0,2,0]
        D.append(u)
    assert [v.degrees() for v in D]==[(0,15,29),(0,16,30),(0,23,43)]
    return Q,f,t,D,G,abc


@lru_cache(None)
def diagonal():
    Q,f,t,(A,B,C0),G,abc=projections()
    R=A.resultant(B,1)
    assert R.degrees()==(0,0,847)
    terms=R.to_dict()
    z=monicq(fmpq_poly([terms.get((0,0,j),0) for j in range(848)]))
    fac=[(monicq(q),e) for q,e in z.factor()[1]]
    assert sorted((q.degree(),e) for q,e in fac)==[
       (1,42),(4,6),(4,27),(12,1),(12,1),(30,1),(144,2),(331,1)]
    p=fmpq_poly([1])
    for q,e in fac:
        p*=q**e
    assert p==z
    assert (fmpq_poly([0,1]),42) in fac
    assert (monicq(fmpq_poly([1,-20,180,-840,1400])),27) in fac
    assert (monicq(fmpq_poly([1,-20,180,-840,1680])),6) in fac
    print("exact 847-degree projection: factors 1^42, 4^6, 4^27, 12, 12, 30, 144^2, 331",
          flush=True)
    return fac


def reduce_coef(x,p):
    return int(x.p)*pow(int(x.q),-1,p)%p


def auxiliar(p):
    _,_,_,(A,B,C0),_,_=projections()
    K=nmod_mpoly_ctx.get(("q","r","g"),p)
    def red(H):
        return K.from_dict({m:reduce_coef(c,p) for m,c in H.to_dict().items()})
    a,c=red(A),red(C0)
    assert a.degrees()==A.degrees() and c.degrees()==C0.degrees()
    z=a.resultant(c,1)
    assert z.degrees()==(0,0,1230)
    terms=z.to_dict()
    return nmod_poly([int(terms.get((0,0,j),0)) for j in range(1231)],p)


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
