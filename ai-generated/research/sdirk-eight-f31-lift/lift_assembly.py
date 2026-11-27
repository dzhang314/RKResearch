#!/usr/bin/env python3
from flint import fmpz_mod_ctx,fmpz_mod_poly_ctx
from math import prod,gcd
from pathlib import Path
import json,sys
here=Path(__file__).resolve().parent
sys.path.insert(0,str(here.parent/'sdirk-eight-f31-upper'))
from specialize import rooted_order

p=31

def moment(F,R,X,s,t):
    def prim(V): return R([0]+[q/(i+1) for i,q in enumerate(V.coeffs())])
    a=(1+s)/2; z=a+s
    J=(X-s)*(X-t)*(X-1); Zp=J*(X-a)
    mu=[prim(X**j*Zp)(z)/z for j in range(4)]
    D=mu[0]*mu[2]-mu[1]**2
    B1=(mu[1]*mu[2]-mu[0]*mu[3])/D
    B0=(mu[1]*mu[3]-mu[2]**2)/D
    return a,z,J,D,B0,B1

def lift(seed,k,value,deriv):
    x=seed;mod=1
    for j in range(1,k):
        mod=p**j
        y=int(value(x))%(mod*p)
        assert y%mod==0
        x+=mod*(-(y//mod)*pow(int(deriv(x))%p,-1,p)%p)
    assert int(value(x))%(p**k)==0
    return x

def parameters(k):
    n=p**k; F=fmpz_mod_ctx(n); R=fmpz_mod_poly_ctx(F); x=R.gen()
    s=lift(11,k,lambda s:s**3-9*s*s+18*s-6,lambda s:3*s*s-18*s+18)
    t=lift(17,k,lambda t:t*t-(s+3)*t+s,lambda t:2*t-s-3)
    _,z,J,D,B0,B1=moment(F,R,x,F(s),F(t))
    c=lift(4,k,lambda c:F(c)**2+B1*c+B0,lambda c:F(2*c)+B1)
    return s,t,c

def assemble(n,tri):
    F=fmpz_mod_ctx(n); R=fmpz_mod_poly_ctx(F); X=R.gen()
    s,t,c=map(F,tri)
    O=F.one();Z=F.zero()
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

    assert s**3-9*s*s+18*s-6==0 and t*t-(s+3)*t+s==0
    a,z,J,Dmu,B0,B1=moment(F,R,X,s,t)
    assert c*c+B1*c+B0==0
    gam=1/z
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
    assert gcd(int(gam),n)==1 and all(A[i][i]==int(gam) and not any(A[i][i+1:]) for i in range(11))
    return A,b,[int(s),int(t),int(c),int(d),int(gam)]

def main():
    lit=json.loads((here.parent/'sdirk-eight-f31-upper'/'witness.json').read_text())
    kvalues=(1,2,4,12)
    for k in kvalues:
        n=p**k
        A,b,ss=assemble(n,parameters(k))
        assert ss[:3]==list(parameters(k))
        exact,bad=rooted_order(A,b,n)
        assert exact and bad and bad[0][0]==9 and len(bad[0][1])==8 and bad[0][2]%p==17
        clocks=[sum(r)%n for r in A]
        val=sum(t*pow(x,8,n) for t,x in zip(b,clocks))%n
        assert (val-pow(9,-1,n))%p==26
        if k==1:
            assert A==lit["A"] and b==lit["b"]
        out={'modulus':n,'seed':ss[:4],'gamma':ss[-1],'A':A,'b':b,'ninth_bush':val}
        if k==2:
            if '--emit961' in sys.argv:print(json.dumps(out,indent=2))
            else:assert out==json.loads((here/'mod961.json').read_text())
        print(k,n,ss,'ninth bush',val,file=sys.stderr)
if __name__=='__main__':
    main()
