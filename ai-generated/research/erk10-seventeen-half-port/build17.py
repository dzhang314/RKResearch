#!/usr/bin/env python3
from scalar import *
from replay_rooted import audit,trees,size,tf
from argparse import ArgumentParser
from pathlib import Path
import json
from hashlib import sha256

def prefix(pth):
    src=pth.read_bytes()
    assert sha256(src).hexdigest()=="49e854cdda01628174223f46ba8bc9da03e1b8706b774380f7a4db9820a4f370"
    data=json.loads(src)
    A,Pi=([[F(t)for t in row]for row in data[k]]for k in ("A","Pi"))
    @lru_cache(None)
    def phi(t):
        V=[act(c) for c in t]
        return tuple(prod(v[i]for v in V)for i in range(9))
    @lru_cache(None)
    def act(t):return tuple(dot(row,phi(t))for row in A)
    D=hull((F(0),F(1),F(1,2)))
    R=D+[F(0)]*3;S=mul(D,[F(0),-F(1),F(1)])
    for n in range(1,9):
        for t in trees(n-1):
            rho=[-dot(row,phi(t))for row in Pi]+[F(0)]*(8-len(Pi))
            rho[n-1]+=F(n,tf(t))
            assert rho[0]==0
            if n<=5:assert not any(rho)
            if n in (6,7):assert not sum(rho)
            if n==6:
                a=rho[5]
                b=rho[3]-a*S[3]
                assert rho==[b*x+a*y for x,y in zip(R,S)]+[F(0)]*2
    return A,Pi

def terminal18(x):
    w=x*(x-1)*(x-F(1,2))
    return w,w*x*(x-1)

def factory(c,w,u):
    y=[1-a for a in c]
    m=[[v*z**j for v,z in zip(w,y)]for j in range(5)]
    s=[u_i*z for u_i,z in zip(u,y)]
    v=[F(0),*[z/(1-x)for z,x in zip(u[1:],c[1:])]]
    e=v
    R=[*m[:3],u,m[3],s,e]
    M=[[r[i]for r in (u,s,v)]for i in range(1,4)]
    N=[r[:4]for r in R[:4]]
    d3,d4=det(M),det(N)
    if not (d3 and d4):return
    orders=list(zip(*map(terminal18,c)))
    # Precompute literal inverses, reused when sampling the affine maps.
    inv=lambda T,n:list(zip(*(solve(T,[int(i==j)for i in range(n)])for j in range(n))))
    IA2=inv([r[:2]for r in R[:2]],2)
    IG=inv(M,3)
    IA4=inv(N,4)
    L0=[F(0)]*9
    def execute(P,retain=False):
        # P[0] is the third-interior row's added tap. Remaining
        # entries are row/column chronological on columns fourth+.
        L=[L0.copy()for _ in c]
        L[1][0]=m[1][1]/w[0]
        for i in (2,3):
            if i==3:L[i][2]=P[0]
            tar=[m[1][i]-L[i][2]*R[0][2],m[2][i]/2+u[i]-L[i][2]*R[1][2]]
            L[i][:2]=[dot(row,tar)for row in IA2]
        pg=[dot(row,[dot(L[i],m[2])-m[3][i]/3 for i in range(1,4)])for row in IG]
        ph=[dot(row,[dot(L[i],u) for i in range(1,4)])for row in IG]
        G=[dot(pg,[a,b,c])for a,b,c in zip(u,s,v)]
        H=[dot(ph,[a,b,c])for a,b,c in zip(u,s,v)]
        idx=1
        for i in range(4,9):
            for j in range(4,i if i<8 else 4):
                L[i][j]=P[idx];idx+=1
            T=[m[1][i],m[2][i]/2+u[i],m[3][i]/3+G[i],H[i]]
            tt=[q-dot(L[i][4:],r[4:])for q,r in zip(T,R)]
            L[i][:4]=[dot(rr,tt)for rr in IA4]
        assert idx==7
        defects=[[dot(L[i],m[3])-m[4][i]/4 for i in range(9)],[dot(row,s)for row in L],[dot(row,e)for row in L]]
        result=tuple(dot(p,r)for p in defects for r in orders)
        if retain:
            for i in range(9):
                assert [dot(L[i],r)for r in R[:4]]==[m[1][i],m[2][i]/2+u[i],m[3][i]/3+G[i],H[i]]
                assert not any(L[i][i:])
            return L,defects,pg,ph
        return result
    return execute,d3,d4

def affine(M,b):
    R=[list(row)+[x]for row,x in zip(M,b)];n=len(M[0]);piv=[]
    for c in range(n):
        z=next((i for i in range(len(piv),len(R))if R[i][c]),None)
        if z is None:continue
        r=len(piv);R[r],R[z]=R[z],R[r]
        R[r]=[x/R[r][c]for x in R[r]]
        for i in range(len(R)):
            if i!=r and R[i][c]:
                R[i]=[a-R[i][c]*b for a,b in zip(R[i],R[r])]
        piv.append(c)
    if any(r[-1]for r in R[len(piv):]):return
    p=[F(0)]*n
    for i,c in enumerate(piv):p[c]=R[i][-1]
    K=[]
    for f in range(n):
        if f in piv:continue
        q=[F(0)]*n;q[f]=F(1)
        for i,c in enumerate(piv):q[c]=-R[i][f]
        K.append(q)
    return p,K,len(piv)


from math import lcm

def construct(A0,Pi):
    nodes=tuple(F(j,6)for j in range(-3,7))
    W={x:j0(lagrange(nodes,i))for i,x in enumerate(nodes)}
    assert all(sum(w*x**k for x,w in W.items())==F(1,k+1)for k in range(10))
    c=tuple(map(F,('1','-1/2','-1/3','-1/6','1/3','5/6','2/3','1/6','1/2')))
    w=[W[x]for x in c]
    bar={x:1/(x*prod(x-z for z in c[1:] if x!=z))for x in c[1:]}
    U=[F(0)]+[-W[c[1]]*(1-c[1])**2/2*bar[x]/bar[c[1]]for x in c[1:]]
    assert all(dot(U,[x**k for x in c])==0 for k in range(1,8))
    E,d3,d4=factory(c,w,U)
    assert unit(d3) and unit(d4)
    a=E([F(0)]*7)
    M=list(zip(*([x-y for x,y in zip(E([F(int(i==j))for i in range(7)]),a)]for j in range(7))))
    P,VT,rank=affine(M,[-v for v in a])
    expected=tuple(map(F,('0','-56/45','-1/9','-5/72','0','16/9','-8/5')))
    assert rank==5 and tuple(P)==expected
    assert VT==[[1,0,0,0,0,0,0],[0,1,0,0,1,0,0]]
    assert not any(E(P))
    L,defs,pg,ph=E(P,True)
    coeffs=[x for r in L for x in r]
    for v in VT:
        x=[p+t for p,t in zip(P,v)]
        assert not any(E(x))
        D=E(x,True)[0]
        coeffs.extend(a-b for r,z in zip(D,L)for a,b in zip(r,z))
    Q=lcm(*(v.denominator for v in coeffs))
    assert Q==740880 and unpaid(Q)==1
    print('six terminal moments in seven affine taps; exact matrix and augmented ranks:',rank,rank)
    print('particular taps:',list(map(str,P)))
    print('kernel basis:',VT)
    print('common affine coefficient denominator',Q)
    print('G,H coefficients on U, yU, and U/y:',pg,ph)
    print('paid four-donor and three-input determinants:',d4,d3)
    N=len(c);high=c[::-1]
    B=[[L[N-1-j][N-1-i]if i>j else F(0)for j in range(N)]for i in range(N)]
    cross=[]
    for i,x in enumerate(high):
        ks=[x**(d+1)/(d+1)-dot(B[i],[a**d for a in high])for d in range(5)]
        cross.append([dot(ks,[Pi[d][j]for d in range(5)])for j in range(9)])
    assert not any(B[0])
    assert cross[0]==A0[8]+[F(0)]
    print('first high physical row equals ninth opening row after padding:',list(map(str,cross[0])))
    # Redirect every tap to the half-port and add the transferred output weight.
    A=[r+[F(0)]*(17-len(r))for r in A0]
    for h,r in zip(cross[1:],B[1:]):
        h[8]+=r[0]
        A.append(h+r[1:])
    b=[W[F(0)]]+[F(0)]*7+[w[-1]]+w[-2::-1]
    assert len(A)==len(b)==17 and len({tuple(r)for r in A})==17
    assert all(not any(r[i:])for i,r in enumerate(A))
    assert all(paid(v)for v in (*b,*(x for r in A for x in r)))
    return A,b,c,w,U,L,P

def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument('--prefix',type=Path,default=Path(__file__).with_name('seed6-prefix.json'))
    p.add_argument('--emit',type=Path)
    args=p.parse_args()
    A0,Pi=prefix(args.prefix)
    A,b,c,w,u,L,P=construct(A0,Pi)
    D,ds=audit(A,b)
    T={'A':[list(map(str,r[:i]))for i,r in enumerate(A)],'b':list(map(str,b)),
       'D':str(D),'defects':[[t,str(g)]for t,g in ds], 'reverse_clocks':list(map(str,c)),
       'reverse_w':list(map(str,w)), 'reverse_U':list(map(str,u)),
       'reverse_K':[list(map(str,r[:i]))for i,r in enumerate(L)], 'free':list(map(str,P)),
       'scale':'1'}
    if args.emit:args.emit.write_text(json.dumps(T,indent=2)+"\n")
if __name__=='__main__':main()
