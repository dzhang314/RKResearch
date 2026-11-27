#!/usr/bin/env python3
"""Independent arithmetic replay of the two-ended, nowhere-zero SDIRK8 census at 11."""
from itertools import product,permutations
from pathlib import Path
import sys

P=11
INV=[0]+[pow(s,-1,P) for s in range(1,P)]
def div(a,b):
    assert b%P
    return (a*INV[b%P])%P

def find_solution(s,l):
    # Eliminate augmented rows as short mutable arrays. None = inconsistent, [] = free.
    rows=[[x%P for x in row] for row in s]
    ps=[]
    q=0
    for j in range(l):
        w=next((w for w in range(q,len(rows)) if rows[w][j]),None)
        if w is None:
            continue
        rows[w],rows[q]=rows[q],rows[w]
        r=INV[rows[q][j]]
        for j2 in range(j,l+1):
            rows[q][j2]=(rows[q][j2]*r)%P
        for k,r in enumerate(rows):
            if k!=q and r[j]:
                h=r[j]
                for j2 in range(j,l+1):
                    r[j2]=(r[j2]-h*rows[q][j2])%P
        ps.append(j)
        q+=1
    if any(r[-1] for r in rows[q:]):
        return None
    if q!=l:
        return []
    return [r[-1] for r in rows[:l]]

def branch_gen():
    for u in range(1,P):
        k=(1+2*u-u*u)%P
        if k==0:
            continue
        for v in range(1,P):
            if v==u:
                continue
            # Solve literal third row equations independently, without the rational r formula.
            for r in range(P):
                g=(1+2*v-v*v+2*r*u)%P
                if not g:
                    continue
                if r*u*(2*u-v)%P or (v*g-k*(v+r*(k-1)))%P:
                    continue
                yield u,v,r,[(1,INV[2]),((1+u)%P,div(k,2)),((1+v)%P,div(g,2))]

def paircheck(x,g,uv,m):
    r,s=uv
    t=(x-m)%P
    return (
       (t**4-div(6*(m*t)**2,7)+div(3*m**4,35)-g*(r[0]+r[1]*t+r[2]*t*t+r[3]*g))%P==0
       and (t**3-div(3*m*m*t,5)-g*(s[0]+s[1]*t+s[2]*t*t+s[3]*t**3+s[4]*g+s[5]*t*g))%P==0
    )

def goodleading(r,s):
    if not r[3] or not(s[3] or s[5]):
        return False
    if not s[5]:
        return True
    q=div(-s[3],s[5])
    return (1-r[2]*q-r[3]*q*q)%P!=0

def gate(point,u):
    # Recover the quadratic interpolant of the first three residuals by the
    # exact A-tableau formulas; use both slopes directly at clock 1.
    _,_,_,pairs=u
    x,g=point
    hm=pairs[0][1]
    x1,g1=pairs[1]; x2,g2=pairs[2]
    rows=[]
    for i,(a,b) in enumerate(pairs):
        rows.append([1,a,a*a,b])
    T=find_solution(rows,3); assert T
    du=(x1-1)%P
    A2row=du+x1*x1
    D2=div(A2row-div(x1**3,3),g1)
    D1=div(1-div(1,3),hm)
    D=(D1+(x-1)*div(D2-D1,du))%P
    Alpha=(1+(x-1)*div(hm,g1))%P
    a,b,c=T
    f=g-(a+b*x+c*x*x)
    J=-(a*x+div(b*x*x,2)+div(c*x**3,3))
    return (f-J-g*(Alpha-b-c*D))%P==0

def census():
    # Keys encode m, output residual at terminal, and both actual normalized opener
    # differences u,w plus the forward/reflected normalized third residuals.
    data=[]
    bn=list(branch_gen())
    trials=unique=0
    for m,L,R,G in product(range(1,P),bn,bn,range(1,P)):
        f=L[-1];r=R[-1]
        seen=f+[((2*m-x)%P,(g*2*G)%P) for x,g in r]
        if len(set(seen))!=6:
            continue
        trials+=1
        U=[];V=[]
        for x,g in seen:
            t=(x-m)%P
            q=div(t**4-div(6*(m*t)**2,7)+div(3*m**4,35),g)
            h=div(t**3-div(3*m*m*t,5),g)
            U.append([1,t,t*t,g,q]);V.append([1,t,t*t,t**3,g,t*g,h])
        F=find_solution(U,4);H=find_solution(V,6)
        if F is None or H is None:
            continue
        assert F and H
        unique+=1
        if not goodleading(F,H):
            continue
        rem=[(x,g) for x,g in product(range(P),range(1,P))
             if (x,g) not in seen and paircheck(x,g,(F,H),m)]
        if len(rem)!=4:
            continue
        for p4,p7 in permutations(rem,2):
            p7r=((2*m-p7[0])%P,div(p7[1],2*G))
            assert not (gate(p4,L) and gate(p7r,R))
        data.append(((m,G,L[0],L[1],L[-1][-1][1],R[0],R[1],R[-1][-1][1]),rem))
    assert trials==20714 and unique==406 and len(data)==39
    return sorted(data)

def lean_data(ds):
    return ',\n'.join(
        '  ⟨'+','.join(map(str,x))+
        ',['+','.join('('+str(z)+','+str(g)+')' for z,g in y)+']⟩'
        for x,y in ds
    )+'\n'
if __name__=='__main__':
    ds=census()
    if len(sys.argv)>1 and sys.argv[1]=='--emit-lean':
        print(lean_data(ds),end='')
    else:
        src=(Path(__file__).resolve().parents[2]/'lean/RKCert/Research/SDIRKEightTwoEndedF11.lean')
        s=src.read_text()
        assert lean_data(ds) in s
        print('F11: 20,714 exact openers, 406 unique consistent fits, 39 ten-pair intersections, no eligible fourth pair in both directions')
