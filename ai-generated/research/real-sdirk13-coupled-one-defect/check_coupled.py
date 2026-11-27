"""Exact shifted-moment closure and actual 25-row below-order-13 counterexample."""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import sys
interface=Path(sys.argv[2]) if len(sys.argv)>2 else Path(__file__).resolve().parent.parent/'real-sdirk13-joined-interface'
sys.path.insert(0,str(interface))
from check_reverse_bank import (I,B,Z,O,Y,Ynorm,W,gamma,identity,ps,mu,conv,
    pay_reverse,lower_rank,front_rank,test_words,mixed_probe,subvec,mult,combine,addvec)
from check_two_ports import cert_roots,cert_ports,front_prep,actual_bank,dot,ev,plus,sc,T,cross

def interval_sqrt(x):
    assert x.lo>0
    scale=1<<B
    lo=isqrt(scale*x.lo);hi=isqrt(scale*x.hi)
    return I(lo,hi+(hi*hi<scale*x.hi))
def div_by_root(p,x):
    n=len(p)-1
    q=[Z]*n
    q[-1]=p[-1]
    for i in reversed(range(n-1)):
        q[i]=p[i+1]+x*q[i+1]
    r=p[0]+x*q[0]
    assert not r.sign()
    return q
def extract_defect(roots,U,ports):
    z,v,w=ports;theta=roots[5][0]
    eta=cross([ev(p,z)for p in U],[ev(p,v)for p in U])
    q=plus(sc(eta[0],U[0]),plus(sc(eta[1],U[1]),sc(eta[2],U[2])))
    qm=T(q)
    assert len(q)==6 and q[-1].sign()
    assert not ev(q,v).sign() and not ev(qm,v).sign()
    r=q[:]
    for x in [z,v,theta]:
        r=div_by_root(r,x)
    discriminant=r[1]*r[1]-4*r[2]*r[0]
    assert discriminant.sign()
    extra=[]
    if discriminant.sign()>0:
        s=interval_sqrt(discriminant)
        extra=[(-r[1]-s)/(2*r[2]),(-r[1]+s)/(2*r[2])]
    qs=[ev(qm,x)for x in [z,theta]+extra]
    assert all(v.sign()for v in qs)
    print('The degree-5 missing mode Q and its shifted primitive have only one common real root: v.')
    assert ev(q,w).sign() and not ev(qm,w).sign()
    X=[(1-y)/gamma for y in Y]
    for i,x in enumerate(X):
        e=ev(qm,x)
        if i in (3,7):assert not e.sign()
        else:assert e.sign()
    print('Only the two prescribed representative sites have zero shifted Q primitive on this grid.')
    return q,qm,X

def full_tail(q,qm,X,labels=(3,2,1,4,5,6,7),a=6,b=4):
    A,R,c,m1,m2,_=pay_reverse(list(labels),a,b)
    V,_=test_words(A,R,c,m1,m2)
    assert lower_rank(V)==4
    assert mixed_probe(V,a,b)
    order=[i for i in range(8) if i not in (a,b,3,7)]+[7,3]
    oldlabels=list(labels)+[a,b]
    labels=oldlabels+order
    m=len(labels);oldn=len(oldlabels)
    groups=[[i for i,y in enumerate(labels)if y==j]for j in range(8)]
    shares=[W[j]/len(groups[j]) for j in labels]
    assert all(y.sign()for y in shares)
    means=[[I.val(F(1,len(groups[j]))) if i in groups[j] else Z for i in range(m)]for j in range(8)]
    R=[r+[Z]*(m-oldn)for r in R]
    model=[combine(ps(Ynorm[j],5),R)for j in range(8)]
    contrast=[subvec(x,y)for x,y in zip(means,model)]
    L=[r+[Z]*(m-oldn)for r in A]
    Act=order[:-2]
    ss=[[Z]*8 for i in range(8)]
    factor=W[7]*ev(q,X[7]);assert factor.sign()
    for j in Act:
        ss[7][j]=W[j]*ev(qm,X[j])/factor
    for k,i in enumerate(order):
        j=oldn+k
        v=combine(mu(Ynorm[i],5),R)
        for h in order[:k]:v=addvec(v,mult(ss[i][h],contrast[h]))
        v=mult(len(groups[i]),v)
        for h in groups[i]:
            if h<oldn:v=subvec(v,subvec(L[h],identity(m,h)))
        assert all(not z.sign() for z in v[j:])
        L.append(v[:j]+[O]+[Z]*(m-j-1))
    for i in range(8):
        d=combine(means[i],L)
        r=combine([Ynorm[i]**(j+1)/(j+1)for j in range(5)],R)
        r=addvec(r,contrast[i])
        for j in range(8):
            if j!=i:r=addvec(r,mult(ss[i][j],contrast[j]))
        assert not any(v.sign() for v in subvec(d,r))
    tail_sites=[X[labels[m-1-i]]for i in range(m)]
    Btail=[[L[m-1-j][m-1-i]*shares[m-1-j]/shares[m-1-i] if j<i else O if i==j else Z
        for j in range(m)]for i in range(m)]
    qdata=[ev(q,x)for x in tail_sites]
    for i,x in enumerate(tail_sites):
        e=dot(Btail[i],qdata)-(ev(qm,x)+qdata[i])
        assert not e.sign()
    print('Physical weighted transpose has 15 rows, with the whole missing-mode column equality checked.')
    return Btail,tail_sites,shares[::-1]

def forward_coalesced(roots,U,ports,coef,Btail,c,weights):
    F12,D6=actual_bank(roots,U,ports,coef)
    _,D5=front_prep(roots)
    n=len(F12)-1; m=len(Btail)
    fake=combine(ps(ports[2],5),D5)+[Z,Z]
    D=[[row[i]+row[-1]*fake[i] for i in range(n)]for row in D6]
    A=[r[:n]+[Z]*m for r in F12[:n]]
    out=[Z]*n+weights[:]
    for i,x in enumerate(c):
        t=[x**(k+1)/(k+1)-dot(Btail[i],[y**k for y in c])for k in range(6)]
        A.append(combine(t,D)+Btail[i])
    old=n-1;new=n
    assert all(not v.sign() for v in subvec(subvec(A[old],identity(n+m,old)),subvec(A[new],identity(n+m,new))))
    for r in A:r[old]=r[old]+r[new]
    out[old]=out[old]+out[new]
    del A[new];del out[new]
    for r in A:del r[new]
    for i,r in enumerate(A):
        assert all(not a.sign()for a in r[i+1:])
        assert not (r[i]-1).sign()
        r[i]=O
    return [mult(gamma,r)for r in A],out

def first_tall_test(A,b):
    a=[O]*len(A)
    for n in range(1,14):
        e=dot(b,a)-F(1,n)
        if e.sign():
            print('First nonzero tall-tree defect at size %d, magnitude >= 2^(%d).'%(n,e.inf().bit_length()-1-B))
            return n
        a=[n*dot(r,a)for r in A]
    return None

def check_small(A,b):
    ts=[];worst=0
    cap=12 if "--full" in sys.argv[3:] else 9
    for n in range(1,cap+1):
        old=ts[:]
        def rec(rem,k,p):
            nonlocal worst
            if not rem:
                d=dot(p,b)-F(1,n);assert not d.sign()
                worst=max(d.sup(),worst)
                ts.append((n,[n*dot(r,p)for r in A] if n<cap else []));return
            for i in range(k,len(old)):
                t,f=old[i]
                if t<=rem:rec(rem-t,i,[x*y for x,y in zip(p,f)])
        rec(n-1,0,[O]*len(A))
    assert len(ts)==(7813 if cap==12 else 486)
    print('%d independently recomputed rooted conditions through size %d; worst enclosure < 2^(%s).'%(len(ts),cap,worst.bit_length()-B))

if __name__=='__main__':
    roots=cert_roots();U,ports,coef=cert_ports(roots)
    assert front_rank()==5
    Q,TQ,X=extract_defect(roots,U,ports)
    Btail,c,weights=full_tail(Q,TQ,X)
    A,b=forward_coalesced(roots,U,ports,coef,Btail,c,weights)
    assert len(A)==25
    assert first_tall_test(A,b)==13
    check_small(A,b)
