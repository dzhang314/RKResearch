#!/usr/bin/env python3
"""Exact screen of the high-off characteristic-11 branch in the prime field.

Needs the high-off rank/localization and scalar hull hypotheses, not the
characteristic-zero tagged census. Looks for literal strict finite tableaux.
"""
from itertools import combinations,permutations
from math import prod
import json
import sys
P=11
h=pow(2,-1,P)
q=lambda x:(x*x-x+pow(7,-1,P))%P
iv=[None]+[pow(j,-1,P) for j in range(1,P)]
M=[iv[j+1] for j in range(8)]

def exponents(c,k):
    return [pow(x,k,P) for x in c]
def dot(a,b):
    return sum(x*y for x,y in zip(a,b))%P

def solve(rows,ncols,rank=False):
    rows=[list(row) for row in rows]
    piv=[]
    for c in range(ncols):
        r=len(piv)
        k=next((k for k in range(r,len(rows)) if rows[k][c]%P),None)
        if k is None: continue
        rows[k],rows[r]=rows[r],rows[k]
        rr=[x*iv[rows[r][c]%P]%P for x in rows[r]]
        rows[r]=rr
        for k in range(r+1,len(rows)):
            d=rows[k][c]%P
            if d: rows[k]=[(x-d*y)%P for x,y in zip(rows[k],rr)]
        piv.append(c)
    if any(row[-1]%P for row in rows[len(piv):]):return None
    if rank:assert len(piv)==ncols
    z=[0]*ncols
    for c,row in reversed(list(zip(piv,rows[:len(piv)]))):
        z[c]=(row[-1]-dot(row[c+1:ncols],z[c+1:]))%P
    return z

def sites():
    for S in combinations(range(P),7):
        rs={a:iv[prod(a-b for b in S if b!=a)%P] for a in S}
        bs={a:rs[a]*iv[q(a)]%P for a in S}
        rhs=[[sum(bs[a]*pow(a,k,P) for a in S)%P,*exponents([0,h,1],k),M[k]] for k in range(8)]
        ans=solve(rhs,4,rank=True)
        if ans is None:continue
        lam,b0,bh,b1=ans
        assert lam!=0
        yield S,rs,{a:lam*x%P for a,x in bs.items()},(b0,bh,b1)

def heads(S):
    """Determine all first three off rows from paid linear data."""
    for a,b,d in permutations(S,3):
        if a==0: continue
        theta=-a*a*iv[2]*iv[q(a)]%P
        pg={u:theta*q(u)%P for u in S}
        ga,gb,gd=map(pg.get,(a,b,d))
        u=(gb+b*b*iv[2])*iv[a]%P
        if not u:continue
        beta=u*ga*iv[gb]*iv[(b-a)%P]%P
        l0=-a**3*iv[3]*iv[ga]%P
        l1=((u*a*a-b**3*iv[3])*iv[gb]-l0)*iv[(b-a)%P]%P
        ac=(gd+d*d*iv[2])%P
        ac2=(d**3*iv[3]+gd*(l0+l1*(d-a)))%P
        ag=gd*beta*(d-a)%P
        if b:
            t=(ac2-a*ac)*iv[b*(b-a)%P]%P
            s=(ac-b*t)*iv[a]%P
            if (ga*s+gb*t-ag)%P:continue
        else:
            s=ac*iv[a]%P
            t=(ag-ga*s)*iv[gb]%P
            if (a*a*s-ac2)%P:continue
        m0=-a**4*iv[4]*iv[ga]%P
        m1=((u*a**3-b**4*iv[4])*iv[gb]-m0)*iv[(b-a)%P]%P
        m2=((s*a**3+t*b**3-d**4*iv[4])*iv[gd]-m0-m1*(d-a))*iv[(d-a)*(d-b)%P]%P
        n1=a*beta%P
        n2=((s*a*ga+t*b*gb)*iv[gd]-n1*(d-a))*iv[(d-a)*(d-b)%P]%P
        def target(x,g,a=a,b=b,beta=beta,l0=l0,l1=l1,m0=m0,m1=m1,m2=m2,n1=n1,n2=n2):
            v=x-a;w=v*(x-b)
            return [n%P for n in [x,x*x*iv[2]+g,x**3*iv[3]+g*(l0+l1*v),
                x**4*iv[4]+g*(m0+m1*v+m2*w),g*beta*v,g*(n1*v+n2*w)]]
        pref=[[0]*0,[a],[(b-u)%P,u],[(d-s-t)%P,s,t]]
        yield (a,b,d),pg,target,pref

def probes(c,g):
    es=[exponents(c,k) for k in range(4)]+[g,[(u*v)%P for u,v in zip(c,g)]]
    return es+[exponents(c,4),[(u*u*v)%P for u,v in zip(c,g)]]

def realize(c,g,w,r,pref,target,loose=False):
    s=len(pref)
    acols=[(i,j) for i in range(s,10) for j in range(i)]
    idx={p:i for i,p in enumerate(acols)}
    fs=probes(c,g)
    mat=[]
    def lin(terms,rhs):
        row=[0]*(len(acols)+1)
        row[-1]=rhs
        for i,j,x in terms:
            if i<s:
                row[-1]-=pref[i][j]*x
            else:
                row[idx[i,j]]+=x
        mat.append([y%P for y in row])
    # Literal paid forward bands and strict chronological prefixes.
    for i in range(s,10):
        for f,y in zip(fs,target(c[i],g[i])):
            lin([(i,j,f[j]) for j in range(i)], y)
    y=[1-t for t in c]
    for j in range(10):
        lin([(i,j,w[i]) for i in range(j+1,10)],w[j]*y[j])
    # J1 proportional to r, the W-annihilator. Its scalar is fixed from
    # the last off coordinate's literal value if no nonterminal clean is later;
    # permit it as an independent unknown to avoid a hidden support shortcut.
    k=next(j for j in range(10) if r[j])
    for j in range(10):
        if k==j: continue
        lin([(i,j,2*w[i]*y[i]*r[k]) for i in range(j+1,10)] +
            [(i,k,-2*w[i]*y[i]*r[j]) for i in range(k+1,10)],
            w[j]*y[j]**2*r[k]-w[k]*y[k]**2*r[j])
    for f in fs:
        lin([(i,j,3*w[i]*y[i]**2*f[j]) for i in range(10) for j in range(i)],
            sum(w[j]*y[j]**3*f[j] for j in range(10)))
        # A(E4) ⊆ W, with W-annihilator r.
        lin([(i,j,r[i]*f[j]) for i in range(10) for j in range(i)],0)
    ans=solve(mat,len(acols))
    if ans is None:return None
    A=[row+[0]*(10-i) for i,row in enumerate(pref)]
    A.extend([[0]*10 for _ in range(s,10)])
    for (i,j),a in zip(acols,ans):A[i][j]=a
    return A

def screen():
    counts=[0]*7
    sols=list(sites())
    for S,rs,bs,bc in sols:
        for (a,b,d),pg,tar,pref in heads(S):
            counts[0]+=1
            lft=tuple(u for u in S if u not in (a,b,d))
            def extend(c,flag,pref,hused,rem):
                if not rem and hused:
                    Q=c+[1]; G=[pg[u] if f else 0 for u,f in zip(c,flag)]+[0]
                    W=[bs[u] if f else bc[([0,h,1].index(u))] for u,f in zip(c,flag)]+[bc[2]]
                    R=[rs[u] if f else 0 for u,f in zip(c,flag)]+[0]
                    counts[6]+=1
                    A=realize(Q,G,W,R,pref,tar)
                    if A is not None:
                        print('full linear candidate',json.dumps(dict(A=A,b=W,c=Q,g=G,support=S),separators=(',',':')))
                        return A
                    return None
                choices=[(u,True) for u in rem]+([] if hused else [(h,False)])
                for u,off in choices:
                    g=[pg[x] if f else 0 for x,f in zip(c,flag)]
                    M=probes(c,g)
                    tg=tar(u,pg[u] if off else 0)
                    tap=solve([[*f,z] for f,z in zip(M,tg)],len(c))
                    if tap is None:continue
                    counts[len(c)-3]+=1
                    # Only fix taps while the six forward equations have unique
                    # solution: up to 4 senders, and require rank if it matters.
                    cand=pref+[tap] if len(c)==4 else pref
                    if extend(c+[u],flag+[off],cand,hused or not off,tuple(v for v in rem if not off or v!=u)):
                        return True
                return None
            extend([0,a,b,d],[False,True,True,True],pref,False,lft)
    print('off sets with bush and g moments:',len(sols))
    print('counts: heads, row4 through row8, global trials:',counts)

if __name__=='__main__':screen()
