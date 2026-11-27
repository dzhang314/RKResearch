#!/usr/bin/env python3
"""Independent exact specialization of the archived literal SDIRK(11,8) donor."""
from flint import fq_default_ctx,fq_default_poly_ctx
from functools import lru_cache
from math import prod
import json,sys

@lru_cache(None)
def size(t):
    return 1+sum(map(size,t))

@lru_cache(None)
def gamma(t):
    return size(t)*prod(map(gamma,t))

def bank(n):
    levels=[[],[()]]
    for j in range(2,n+1):
        opts=sum(levels[1:],[])
        def combinations(k,start):
            if k==0:
                yield ()
                return
            for m in range(start,len(opts)):
                t=opts[m];d=size(t)
                if d>k:break
                for rem in combinations(k-d,m):yield (t,)+rem
        levels.append(list(combinations(j-1,0)))
    return levels

def rooted_order(A,b,p):
    levels=bank(9);s=len(A)
    assert [len(t) for t in levels[1:]]==[1,1,2,4,9,20,48,115,286]
    def mv(A,v):
        return [sum(x*y for x,y in zip(r,v))%p for r in A]
    phi={}
    fail=[]
    for j in range(1,10):
        for q in levels[j]:
            ff=[mv(A,phi[t]) for t in q]
            v=[prod(xs)%p for xs in zip(*ff)] if ff else [1]*s
            phi[q]=v
            diff=(sum(x*y for x,y in zip(b,v))*gamma(q)-1)%p
            if diff:
                if j<=8:return False,j,q,diff
                fail.append((j,q,diff))
    return True,fail

def build(p):
    F=fq_default_ctx(p);R=fq_default_poly_ctx(F);X=R.gen()
    O=F.one();Z=F.zero()
    def roots(aa):return [a for a,e in aa.roots()]
    def prim(Y):return R([Z]+[q/(i+1) for i,q in enumerate(Y.coeffs())])
    def product(xs):return prod((X-x for x in xs),start=R.one())
    def cards(ports):return [product(ports[:i]+ports[i+1:])/prod((r-y for j,y in enumerate(ports) if j!=i),start=O) for i,r in enumerate(ports)]
    def mv(A,v):return [sum((a*b for a,b in zip(r,v)),start=Z) for r in A]
    def operator(n,f):
        cs=[f([O if i==j else Z for i in range(n)]) for j in range(n)]
        return [list(line) for line in zip(*cs)]
    def project(ports,tag,vec):
        Q=cards(ports[:3])
        it=lambda vals:sum((b*y for b,y in zip(Q,vals)),start=R.zero())
        G=it(tag);W=it(vec);d=ports[3]
        sigma=(vec[3]-W(d))/(tag[3]-G(d))
        return W-sigma*G
    for s in roots(X**3-9*X**2+18*X-6):
      for t in roots(X**2-(s+3)*X+s):
        a=(1+s)/2; z=a+s
        J=product([s,t,O])
        Zp=J*(X-a)
        try:
          gam=1/z
          mu=[prim(X**j*Zp)(z)/z for j in range(4)]
          D=mu[0]*mu[2]-mu[1]**2
          B1=(mu[1]*mu[2]-mu[0]*mu[3])/D
          B0=(mu[1]*mu[3]-mu[2]**2)/D
        except ZeroDivisionError:continue
        for c in roots(X**2+B1*X+B0):
          try:
            def spec():
              h=a-1;g1=O/2+h-h*h/2;eta=2*g1;Bs=(1-s)*(3-s)
              q=prim(J)-J
              ell=[prim(X**j*(X-a)*(X-c)*q)(z)/z for j in range(2)]
              selector=lambda T:(T-z+c)*(ell[0]*(z-T)-ell[1])
              rr=s/3
              Ld=lambda T:(Bs-1)*(T-1)-eta*(T+1-2*s)
              ms=eta*Bs-3*(Bs-1-eta)
              def affine(T):
                af=((T-a)*selector(O)/(1-rr)-(T-1)*selector(a)/(a-rr))/(1-a)
                return (Ld(T)*selector(rr)/((1-rr)*(a-rr)))-(ms/3)*af
              d=-affine(Z)/(affine(O)-affine(Z))
              gd=(eta/2)*(d-s)*(d*d-(s+3)*d+s)/Ld(d)
              U=d*d/2-d+gd
              V=2*(1+d+(d-1)/eta)*gd/3-d*d+d**3/3
              f4=[d-1,U,V]
              c3=cards([O,a,s])
              fp=[sum((P[i]*f4[i] for i in range(3)),start=Z) for P in c3]
              rp=[prim(P)(t)-P(t) for P in c3]
              tap=2/(h-2)
              a3=[[O,Z,Z,Z],[h,O,Z,Z],[2*h-tap,tap,O,Z]]
              G=[[gam*x for x in row] for row in a3+[fp+[O]]]
              RR=[[gam*x for x in row] for row in a3+[rp+[O]]]
              b=-B1-c
              y=[gam*q for q in [O,a,s,t,b,c]]
              x=[1-q for q in y]
              W=[prim(Q)(O) for Q in cards(y)]
              ru=product([x[1],x[4],x[5]])
              A=(d-a)*gd/((a-1)*(O/2))
              B=-(d-1)*gd/((a-1)*g1)
              clean=lambda Q:A*Q(gam)+B*Q(gam*a)+Q(gam*d)
              normalize=lambda Q,x:Q/Q(x)
              h4=normalize(product([x[1],x[5]]),x[4])
              h5=normalize(product([x[1],x[4]]),x[5])
              HH=[Q-(clean(Q)/clean(ru))*ru for Q in [h4,h5]]
              KK=[normalize(product([y[2],y[3],y[4]]),y[0]),
                  normalize(product([y[2],y[3],y[0]]),y[4])]
              pair=lambda i,j:sum((W[k]*HH[i](x[k])*(prim(KK[j])(y[k])-gam*KK[j](y[k])) for k in range(6)),start=Z)
              a40=pair(0,0)/W[4];a50=pair(1,0)/W[5];a54=pair(1,1)/W[5]
              forward_ports=[gam*q for q in [O,a,s,d]];reverse_ports=[gam*q for q in [O,a,s,t]]
              forward_tag=[gam**2*q for q in [O/2,g1,Z,gd]];reverse_tag=[gam**2*q for q in [O/2,g1,Z,Z]]
              old=[7,6,5,4]
              site=[1,5,4,0,3,2,1,0]
              ww=[W[1]/2,W[5],W[4],W[0]/2,W[3],W[2],W[1]/2,W[0]/2]
              def rear(v):
                ov=[v[i] for i in old]
                A=project(reverse_ports,reverse_tag,ov)
                C=[(v[3]+v[7])/2,(v[0]+v[6])/2,v[5],v[4],v[2],v[1]]
                C=[Cc-A(yy) for Cc,yy in zip(C,y)]
                U=[gam*P+prim(A)(yy) for P,yy in zip(C,y)]
                U[4]+=a40*C[0]
                U[5]+=a50*C[0]+a54*C[4]
                O=mv(RR,ov)
                return [2*U[1]-O[1],U[5],U[4],2*U[0]-O[0],O[3],O[2],O[1],O[0]]
              L=operator(8,rear)
              TT=[[ww[j]/ww[i]*L[j][i] for j in range(8)] for i in range(8)]
              def cross(v):
                H=project(forward_ports,forward_tag,v)
                hx=[x[i] for i in site]
                prod=mv(TT,[H(s) for s in hx])
                return [prim(H)(s)-c for s,c in zip(hx,prod)]
              DD=operator(4,cross)
              A=[row+[Z]*8 for row in G]+[d+t for d,t in zip(DD,TT)]
              b=[Z]*4+ww
              for i in range(12):
                A[i][2]+=A[i][4]
              b[2]+=b[4]
              keep=[0,1,2,3,5,6,7,8,9,10,11]
              A=[[int(A[i][j]) for j in keep] for i in keep]
              b=[int(b[i]) for i in keep]
              assert gam!=0 and all(A[i][i]==int(gam) and not any(A[i][i+1:]) for i in range(11))
              return A,b,[int(s),int(t),int(c),int(d),int(gam)]
            A,b,seeds=spec()
          except (ZeroDivisionError,AssertionError):continue
          if A:
            result=rooted_order(A,b,p)
            if result[0]:
              yield A,b,seeds,result[1]

if __name__=='__main__':
    if sys.argv[1:]:
        ps=list(map(int,sys.argv[1:]))
    else:
        from sympy import primerange
        ps=list(primerange(11,10001))
    for p in ps:
        controls=list(build(p))
        if controls:
            A,b,seeds,fail=controls[0]
            print('prime',p,'witnesses',len(controls),'seed',seeds,'first next failure',fail[0] if fail else None,flush=True)
            if len(sys.argv)==1:
                print(json.dumps({'p':p,'A':A,'b':b,'seeds':seeds,'nextFail':fail[0]},indent=2),flush=True)
                break
