#!/usr/bin/env python3
"""Complete one-live-clock five-node scalar and four-zero causal block checks."""
from flint import nmod_poly,fmpz_mod_poly_ctx,fq_default_ctx,fq_default_poly_ctx
from itertools import product,permutations
from math import lcm
from prime_certificates import certify
def lin(F,qs,n):
 P={};ix=[]
 for j,row in enumerate(qs):
  a=list(row)
  for i in range(n):
   c=a[i]
   if c==0:continue
   if i in P:a=[t-c*v for t,v in zip(a,P[i])]
   else:
    P[i]=[x/c for x in a];ix.append(j);break
  else:
   if a[-1]!=0:return len(P),j,a[-1],ix+[j]
 return len(P),None,None,ix
def det(F,mat):
 M=[list(x) for x in mat];r=F.one()
 for j in range(len(M)):
  ps=[i for i in range(j,len(M)) if M[i][j]!=0]
  if not ps:return F.zero()
  k=ps[0]
  if k!=j:M[k],M[j]=M[j],M[k];r=-r
  a=M[j][j];r*=a
  for i in range(j+1,len(M)):
   b=M[i][j]/a
   M[i]=[x-b*y for x,y in zip(M[i],M[j])]
 return r
for p,case in ((770514337,'midpoint'),(26254266039604698273071,'other')):
    assert certify(p)
    R0=(lambda c:nmod_poly(c,p)) if p<2**63 else fmpz_mod_poly_ctx(p)
    Q=R0([2,3,-12,4]);K=R0([1,2,-1])
    deg=2*lcm(*(f.degree() for ff in (Q,K) for f,e in ff.factor()[1]))
    F=fq_default_ctx(p,deg,'w')
    R=fq_default_poly_ctx(F);X=R.gen()
    O=F.one();Z=F.zero()
    us=[a for a,e in (4*X**3-12*X*X+3*X+2).roots()]
    vs=[a for a,e in (1+2*X-X*X).roots()]
    assert len(us)==3 and len(vs)==2
    I=lambda P:sum((a/(j+1) for j,a in enumerate(P.coeffs()) if j%2==0),Z)
    def J(P):
        T=R([Z]+[a/(2*(j+1)) for j,a in enumerate(P.coeffs())])
        return T-T(-O)
    def card(xs,j):
        P=R.one()
        for k,y in enumerate(xs):
            if k!=j:P=P*(X-y)/(xs[j]-y)
        return P
    count=0
    for u,v in product(us,vs):
        if u+2==0:continue
        if case=='midpoint':
            gamma=O/2;d=Z;e=u;a=2*u;b=-v
        else:
            gamma=O/(u+2);d=u/(u+2);e=-d
            a=3*u/(u+2);b=(u-2*v)/(u+2)
        if a==b or a==d or b==d:continue
        P3=(X-d)*(X-a)*(X-b)
        M=[I(P3*X**j) for j in range(5)]
        D=M[0]*(M[2]*M[4]-M[3]**2)-M[1]*(M[1]*M[4]-M[2]*M[3])+M[2]*(M[1]*M[3]-M[2]**2)
        if D!=0:continue
        delta=M[0]*M[2]-M[1]*M[1]
        assert delta!=0
        q=(M[1]*M[3]-M[2]*M[2])/delta
        k=(M[1]*M[2]-M[0]*M[3])/delta
        P2=X*X+k*X+q
        assert all(I(P3*P2*X**i)==0 for i in range(3))
        yy=[x for x,factor in P2.roots()]
        if len(yy)!=2 or any(x in (a,b,d) for x in yy):continue
        c=[d,a,*yy,b]
        gW=[I(card(c,i)) for i in range(5)]
        print('control',p,u,v,d,e,a,b,yy,gW,flush=True)
        assert all(w!=0 for w in gW)
        assert all(sum((b*x**j for b,x in zip(gW,c)),Z)==I(X**j) for j in range(8))
        count+=1
        r=(X-d)*(X-e)
        jr=J(r);w1=X-d;jw=J(w1);I1=I(w1)
        dets=[]; idxs=[]
        for yz in permutations(yy):
            c=[a,*yz,b];bW=[gW[1],gW[2+yy.index(yz[0])],gW[2+yy.index(yz[1])],gW[4]]
            ix=[(i,j) for i in range(4) for j in range(i)]
            T=[]
            def eq(L,U,ref):
                T.append([L[i]*U[j] for i,j in ix]+[ref-gamma*sum((a*b for a,b in zip(L,U)),Z)])
            vv=[r(y) for y in c];ll=[w*w1(y) for y,w in zip(c,bW)]
            for i in range(4):
                ei=[O if i==k else Z for k in range(4)]
                eq(ei,vv,jr(c[i]))
                eq(ll,ei,bW[i]*(I1-jw(c[i])))
            for j in range(1,4):
                rr=w1**j;L=[w*rr(y) for y,w in zip(c,bW)]
                for U in (r,X*r):eq(L,[U(y) for y in c],I(rr*J(U)))
            o=lin(F,T,6)
            assert o[0]==6 and o[-1]==[1,2,3,4,5,11,13]
            N=det(F,[T[i] for i in o[-1]])
            assert N!=0
            print('block rank and mismatch',p,yz,o,'det',N,flush=True)
            dets.append(N);idxs.append(o[-1])
        assert idxs[0]==idxs[1]
        A1=(dets[0]-dets[1])/(yy[0]-yy[1]);A0=dets[0]-A1*yy[0]
        NN=dets[0]*dets[1]
        assert NN==A0**2-k*A0*A1+q*A1**2
        expected=(319570959,537196966,289010734,692783714,170900925) if case=='midpoint' else (
          10931918996081537634502,43800998913746017963,17164986678066544640509,7327693306740711712779,
          306422335611480264695)
        assert tuple(map(int,(k,q,A0,A1,NN)))==expected
        print('DET FIELD NORM',p, expected,flush=True)
    assert count==1
    print('total admissible weights and nodes',p,count,flush=True)
