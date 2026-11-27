#!/usr/bin/env python3
'''Exact off-mesh geometry and one actual marked size-six rooted test.'''
from itertools import permutations
from pathlib import Path
import argparse
p=227
def inv(x):return pow(x%p,-1,p)
def mul(x,y):
    z=[0]*(len(x)+len(y)-1)
    for i,u in enumerate(x):
        for j,v in enumerate(y):z[i+j]=(z[i+j]+u*v)%p
    return z
def val(f,x):return sum(u*pow(x,j,p)for j,u in enumerate(f))%p
def Int(f):return [0]+[u*inv(j+1)%p for j,u in enumerate(f)]
def summ(*terms):
    d=max(len(f)for a,f in terms)
    return [sum(a*f[i]for a,f in terms if i<len(f))%p for i in range(d)]
def dt(u,v):return (u[0]*v[1]-u[1]*v[0])%p
def dot(u,v):return sum(a*b for a,b in zip(u,v))%p
def solve2(a,b,x,y):
    d=dt(a,b)
    if not d:return
    return dt([x,a[1]],[y,b[1]])*inv(d)%p,dt([a[0],x],[b[0],y])*inv(d)%p
def geom(a,b,c,d,x,y):
    S=[a,b,c,d]; L=[];D=[]
    for k in S:
        h=[0,1]
        for l in S:
            if l!=k:h=mul(h,[-l,1])
        v=val(h,k);D.append(v)
        L.append([coef*inv(v)%p for coef in h])
    J={z:[val(Int(h),z)for h in L]for z in S+[1]}
    A,B,U,V=J[x];Aa,Bb,Uu,Vv=J[y]
    M=[A*(b-c),B*(a-c)],[A*(b-d),B*(a-d)]
    ic,id0=2,3
    def et(v,w):
        return solve2(*M,U*D[ic]*v,V*D[id0]*w)
    def trial(u,v):
        ea,eb=et(u,v)
        r=lambda k: D[k]*[u,v][k-2]*J[y][k]
        if x==a:
            return ((b-d)*(r(2)-Bb*eb*(a-c))-(b-c)*(r(3)-Bb*eb*(a-d)))%p
        if x==b:
            return ((a-d)*(r(2)-Aa*ea*(b-c))-(a-c)*(r(3)-Aa*ea*(b-d)))%p
        k=3 if x==c else 2
        return (r(k)-Aa*ea*(b-S[k])-Bb*eb*(a-S[k]))%p
    R0,R1=trial(1,0),trial(0,1)
    if not R0 or not R1:return ('ratio',R0,R1)
    rho=-R1*inv(R0)%p
    ea,eb=et(rho,1)
    fa=[1,0,ea*(b-c)*inv(D[2]*rho),ea*(b-d)*inv(D[3])]
    fb=[0,1,eb*(a-c)*inv(D[2]*rho),eb*(a-d)*inv(D[3])]
    fa=[q%p for q in fa];fb=[q%p for q in fb]
    f0=dot(fa,[k**4*inv(4)%p for k in S])
    f1=dot(fa,[-k**3*inv(3)%p for k in S])
    f2=dot(fa,[k**2*inv(2)%p for k in S])
    assert all(J[z][i] for z in S for i in range(4))
    rq=solve2([(-c+rho*d)%p,(1-rho)%p],[f1,f2],(rho*d*d-c*c)%p,-f0%p)
    if not rq:return ('pair',rho,f0,f1,f2)
    sr,t=rq
    P2=[(k*k-sr*k+t)%p for k in S]
    if not all(P2):return ('edge',sr,t,P2)
    assert (P2[2]-rho*P2[3])%p==0
    ea=ea*P2[3]%p;eb=eb*P2[3]%p
    Da=(1-ea*(b-a)*inv(D[0]*P2[0]))%p; Db=(1-eb*(a-b)*inv(D[1]*P2[1]))%p
    if not (Da*Db*ea*eb)%p:return ('scale',Da,Db,ea,eb)
    Aphys=[q*inv(Da)%p for q in fa]; Bphys=[q*inv(Db)%p for q in fb]
    al=-inv((b-a)*ea*inv(Da))%p;bl=-inv((a-b)*eb*inv(Db))%p
    omega=[inv(D[k]*P2[k]) for k in range(4)]
    return ('ok',J,sr,t,fa,fb,Aphys,Bphys,al,bl,omega,L,R0,R1)
def paid_pressure(a,b,c,d,G):
    _,J,s,t,fa,fb,Aphys,Bphys,al,bl,omega,L,*_=G
    U=[a,b,c,d]
    JP=[(z**4*inv(4)-s*z**3*inv(3)+t*z**2*inv(2))%p for z in U]
    JXP=[(z**5*inv(5)-s*z**4*inv(4)+t*z**3*inv(3))%p for z in U]
    return (dot(omega,JXP)-al*JXP[0]+bl*(a*dot(Bphys,JP)-JXP[1]))%p

def mesh(p,x,y,z):
    assert (x*x-3)%p==0 and (y*y-7)%p==0 and (z*z-147-42*y)%p==0 and z%p
    a=z*pow(21,-1,p)%p;b=x*y*pow(z,-1,p)%p
    U=[(1+k)*pow(2,-1,p)%p for k in (-a,-b,b,a)]
    assert len(set(U+[0,1]))==6
    assert all((42*w**4-84*w**3+56*w*w-14*w+1)%p==0 for w in U)
    return U
def cases(M,u,v,w,left):
    global p
    p=M
    U=mesh(p,u,v,w)
    ans={}
    for h in sorted(left):
        a,b=U[h[0]],U[h[1]]
        c,d=[z for k,z in enumerate(U) if k not in h[:2]]
        x,y=U[h[2]],U[h[3]]
        G=geom(a,b,c,d,x,y)
        if G[0]!='ok':continue
        R=paid_pressure(a,b,c,d,G)
        if R:ans[h]=(p,G[2],G[3],R)
    return ans
def emit(path,rows):
    with path.open('w')as f:
        f.write("""/- Independent split-prime arithmetic audit of the off-mesh interface. -/
namespace RKResearch.Core.ERK10TwoDirtyOffMesh

structure Witness where
  key : Nat
  modulus : Nat
  donorSum : Nat
  donorProduct : Nat
  paidPressure : Nat

def witnesses : List Witness := [
""")
        f.write(',\n'.join('  ⟨'+', '.join(map(str,r))+'⟩'for r in rows))
        f.write("""]

theorem exact_cover : witnesses.map Witness.key = List.range 144 := by
  decide +kernel

theorem split_prime_counts :
    (witnesses.filter fun w => w.modulus == 227).length = 133 ∧
    (witnesses.filter fun w => w.modulus == 251).length = 11 := by
  decide +kernel

theorem rooted_pressure_values :
    (witnesses.all fun w => w.paidPressure % w.modulus != 0) = true := by
  decide +kernel

end RKResearch.Core.ERK10TwoDirtyOffMesh
""")
def main():
    p=argparse.ArgumentParser()
    p.add_argument('--emit-lean',type=Path)
    args=p.parse_args()
    labels=list(permutations(range(4),2))
    keys=sorted((i,j,x,y)for i,j in labels for x,y in labels)
    left=set(keys)
    ans={}
    for M,u,v,w,expect in [(227,177,190,149,133),(251,76,42,107,11)]:
        got=cases(M,u,v,w,left)
        print('split prime',M,'clocks',mesh(M,u,v,w),'nonzero paid pressure values',len(got))
        assert len(got)==expect
        ans.update(got)
        left-=set(got)
    assert not left and len(ans)==144
    if args.emit_lean:emit(args.emit_lean,[(i,*ans[h])for i,h in enumerate(keys)])
if __name__=='__main__':main()
