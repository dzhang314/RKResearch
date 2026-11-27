#!/usr/bin/env python3
"""Exact arithmetic for a 13-row triple-port, altered-grade reverse prototype."""
import itertools as it, json, sys
from functools import lru_cache
import witness as t
from witness import (
    Ball,Jet,prod,dot,powers,unit,zero,integ,hull,transpose,eye,matvec,matmul,inverse,
    strength,forward,shift,peval,pmul,abs_bound,card,trees,size,factorial,powers0,
)

def mesh(v,w,z,G,R,S):
    return [G,R,S,1-G*v,1-G*w,1-G*z]

def eq(d,v,w,z,G,R,S):
    a=(zero(d)+3)/5
    H=hull(mesh(v,w,z,G,R,S))
    zroot=z**3-(v+w+5)*z**2+(v*w+3*(v+w))*z-v*w
    return [*forward(a,d,v,w),zroot,*[1000*integ(H,j) for j in range(3)]]

CENTRE=['3.375386150380654','2.397863379510887','5.682374243633903','3.5901852413125317',
    '0.17043790994445146','0.7880630277167423','0.954445413567599']
def setup():
    t.eq=eq; t.C0=CENTRE

def check(box):
    d,v,w,z,G,R,S=box
    a=(zero(d)+3)/5
    x,Af,Df,_=forward(a,d,v,w,True)
    o=unit(G); q=zero(G)
    Jp=hull([q,v,v,w,w])
    P=[(i+1)*p for i,p in enumerate(Jp[1:])]
    pz=peval(P,z)
    assert abs_bound(pz)>Ball.unit>>10
    rz=matvec(transpose(Df),[shift(powers0(z,j),z) for j in range(4)])
    F=[r+[q] for r in Af]+[rz+[o]]
    epz=matvec(transpose(Df),powers(z,4))
    D7=[
      [(Df[j][k] if j<4 else q)-P[j]/pz*epz[k]for k in range(6)]+[P[j]/pz]
      for j in range(5)
    ]
    for site,i in [(v,4),(w,5),(z,6)]:
        for k,y in enumerate(matvec(transpose(D7),powers(site,5))):
            assert (y-(o if k==i else q)).contains0()
        for k,y in enumerate(matvec(transpose(D7),[shift(powers0(site,j),site)for j in range(5)])):
            assert (y-(F[i][k] if k!=i else q)).contains0()
    Y=mesh(v,w,z,G,R,S); yr=[y/G for y in Y]
    assert min(abs_bound(y-x) for y,x in it.combinations(Y,2))>Ball.unit//64
    W=[integ(card(Y,i))for i in range(6)]
    assert all(not (x*x-4*G*x+2*G*G).contains0() for x in Y[1:])
    assert all(not (y-2*x+G).contains0() and not (x+y-4*G).contains0()
               for x,y in it.permutations(Y[1:],2))
    print('fixed scalar mesh excludes all regular pure-rank-two old three-row arrangements')
    assert all(wi.lo>Ball.unit//16 for wi in W)
    a,b=yr[1:3]
    h=-(o+o+o+o)/3
    g1=o/2;g2=2*a-1-a*a/2
    q0=(g1*(a*a+h*a)-g2*(1+h))/(g2-g1)
    Q=[q0,h,o]
    f=(g1*peval(Q,b)/peval(Q,o) - (2*b-1-b*b/2))/(a-1)
    gr=[g1,g2,2*b-1-b*b/2+f*(a-1)]
    Ar=[[o,q,q],[a-1,o,q],[b-1-f,f,o]]
    Dr=inverse([powers(k,2)+[gg] for k,gg in zip(yr[:3],gr)])[:2]
    Q2=[-u for u in matvec(Dr,[x*x for x in yr[:3]])]+[o]
    assert all((a-b).contains0()for a,b in zip(Q,Q2))
    # Altered grade: degree-one polynomial return, with the genuine length-two
    # residual Q. First live site is exactly y=1; both later live rows pay it.
    Smean=eye(6,G)
    assert shift(Q,yr[0]).contains0()
    for i in (1,2): Smean[i][0]=shift(Q,yr[i])/peval(Q,yr[0])
    # Test the actual old-kernel marked polynomial XQ at length three.
    K=[q]+Q
    nu=[integ(hull([y for j,y in enumerate(Y) if j!=i]))for i in (0,1)]
    top=nu[0]*shift(K,yr[0])+nu[1]*(Smean[1][0]*peval(K,yr[0])-shift(K,yr[1]))
    assert not top.contains0()
    print('separated real mixed XQ obstruction',top)
    site=[0,1,2,0,1,2,3,4,5]
    b=[W[i]/2 if i<3 else W[i] for i in site]
    M=[[b[j]/W[i] if site[j]==i else q for j in range(9)]for i in range(6)]
    evaldr=matmul([powers(y,2) for y in yr],Dr)
    primdr=matmul([[y,y*y/2]for y in yr],Dr)
    U=[[x+y for x,y in zip(a,b)]for a,b in zip(
        [r+[q]*6 for r in primdr],matmul(Smean,
        [[x-y for x,y in zip(m,n+[q]*6)]for m,n in zip(M,evaldr)]))]
    L=[r+[q]*6 for r in Ar]
    for i in range(6):L.append([2*x-y for x,y in zip(U[i],L[i])] if i<3 else U[i])
    for i in range(9):
        assert (sum(L[i])-yr[site[i]]).contains0()
        assert (L[i][i]-o).contains0()
        assert all(L[i][j].contains0()for j in range(i+1,9))
        for j in range(i+1,9):L[i][j]=q
        L[i][i]=o
    B=[[b[8-j]/b[8-i]*L[8-j][8-i] for j in range(9)]for i in range(9)]
    bx=[b[8-i] for i in range(9)]
    xi=[1/G-yr[site[8-i]] for i in range(9)]
    Ex=[powers(y,5)for y in xi]
    EJ=[[y**(j+1)/(j+1)for j in range(5)]for y in xi]
    O=matmul([[p-r for p,r in zip(x,y)]for x,y in zip(EJ,matmul(B,Ex))],D7)
    A16=[r+[q]*9 for r in F]+[a+b for a,b in zip(O,B)]
    b16=[q]*7+bx
    target={4:9,5:8,6:7}
    for i,j in target.items():
        assert all((A16[i][k]-A16[j][k]).contains0()for k in range(16)if k!=i and k!=j)
    keep=[*range(7),*range(10,16)]
    A=[[(A16[i][j]+(A16[i][target[j]] if j in target else q))*G
        for j in keep]for i in keep]
    b=[b16[j]+(b16[target[j]] if j in target else q)for j in keep]
    for i in range(13):
        assert (A[i][i]-G).contains0()
        A[i][i]=G
        assert all(A[i][j].contains0()for j in range(i+1,13))
    out=plain(A,b,9)
    assert out[0]==200 and len(out[1])>0
    print('direct actual order-nine failure',out[1][0])
    return A,b

def plain(A,b,N):
    @lru_cache(None)
    def node(t):
        return [Ball.fromval(1)]*len(b) if not t else [prod(s) for s in zip(*(prim(c)for c in t))]
    @lru_cache(None)
    def prim(t):return matvec(A,node(t))
    ct=0;fail=[]
    for j in range(1,N+1):
        worst=0;n=0
        for t in trees(j):
            r=dot(b,node(t))-1/Ball.fromval(factorial(t))
            if r.contains0():n+=1
            else:fail.append((j,t,r))
            worst=max(worst,r.bound())
        if j<=8:
            assert n==len(trees(j))
            ct+=n
        print('tree rows',j,len(trees(j)),'targets in interval',n,'worst bound exponent',worst.bit_length()-Ball.bits)
    return ct,fail

if __name__=='__main__':
    cmd,file=sys.argv[1:3];setup()
    if cmd=='refine': t.generate(file)
    else:
        assert cmd=='check'
        A,b=check(t.replay_root(file))
        if len(sys.argv)>3:
            with open(sys.argv[3],'w')as f:
                json.dump(dict(bits=Ball.bits,A=[[[x.lo,x.hi] for x in r]for r in A],
                               b=[[x.lo,x.hi]for x in b]),f,indent=2)
