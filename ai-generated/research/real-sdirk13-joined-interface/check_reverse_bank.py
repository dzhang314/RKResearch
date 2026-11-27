"""Exact actual nine-row AP reverse bank, two mean terminals, and its mixed obstruction."""
from itertools import combinations, permutations
from check_eight_ports import I,Y,W,gamma,conv,Z,O,cert_ports,cert_roots,ev,solve,tr,det,around
from check_two_ports import actual_bank,dot,B
from fractions import Fraction as Q

Ynorm=[k/gamma for k in Y]
def identity(n,i):return [I.val(j==i) for j in range(n)]
def ps(x,n):return [x**j for j in range(n)]
def mu(x,n):return [x**(j+1)/(j+1)-x**j for j in range(n)]
def addvec(a,b):return [x+y for x,y in zip(a,b)]
def subvec(a,b):return [x-y for x,y in zip(a,b)]
def mult(a,b):return [a*x for x in b]
def combine(coeff,rows):return [dot(coeff,b)for b in tr(rows)]
def small_det(A):
    n=len(A);original=A;A=[r[:]for r in A];v=O
    for j in range(n):
        k=max(range(j,n),key=lambda i:A[i][j].inf())
        if k!=j:A[k],A[j]=A[j],A[k];v=-v
        q=A[j][j]
        if not q.sign():return det(original)
        v=v*q
        for i in range(j+1,n):
            h=A[i][j]/q
            for u in range(j+1,n):A[i][u]=A[i][u]-h*A[j][u]
            A[i][j]=Z
    return v

def ap_seed(C,params=(0,0,0)):
    n=len(C);A=[identity(n,i) for i in range(n)];g=[I.val(Q(1,2))]
    A[1][0]=C[1]-1
    g.append(dot(C[:2],A[1][:2])-C[1]**2/2)
    eta=2*g[1]
    coef=None
    for i,x in enumerate(C[2:],2):
        p=C[:i];q=(x-1)/eta;d=(1+x+q)*Q(2,3);g0=x-x**2/2
        L=[[O]*i,[a-q*b for a,b in zip(g,p)]]
        target=[x-1,q*g0]
        if i>=3:
            L.append([b**2-d*b for b in p])
            target.append(x**3/3-x**2+d*g0)
        if i>=4:
            a0,a1,a2,a3=coef
            a=a0+a1*x+a2*x**2+a3*x
            L.append([b**3-a3*b*h-a*b for b,h in zip(p,g)])
            target.append(x**4/4-x**3+a*g0)
        k=len(L)
        free=[] if i<5 else [I.val(params[0])] if i==5 else [I.val(z) for z in params[1:]]
        r=solve([row[:k]for row in L],
            [[v-dot(row[k:],free)]for row,v in zip(L,target)])
        A[i][:i]=[v[0]for v in r]+free
        g.append(dot(A[i][:i+1],C[:i+1])-x**2/2)
        if i==2:
            z=dot(A[i][:i+1],[b**2 for b in C[:i+1]])-x**3/3-d*g[i]
            assert not z.sign()
        if i==3:
            M=defects(A[:4],C[:4],g)
            coef=[r[0]for r in solve(M,[[dot(A[j][:4],[b**3 for b in C[:4]])-C[j]**4/4]for j in range(4)])]
    return A,g

def defects(A,C,g):
    c=[a*b for a,b in zip(C,g)]
    return [[g[i],c[i],C[i]*c[i],dot(A[i][:len(C)],c)] for i in range(len(C))]
def clean(A,C,g):
    n=len(C);Z4=defects(A,C,g)
    mixed=solve(tr(Z4[:4]),tr(Z4[4:]))
    c=[mult(-1,r)+identity(n-4,i) for i,r in enumerate(tr(mixed))]
    return c,[combine(r,[ps(x,5)for x in C]) for r in c]

def fit(R,target):
    q=len(R)
    for cols in combinations(range(5),q):
        m=[[r[k]for r in R]for k in cols]
        if small_det(m).sign():
            w=[a[0]for a in solve(m,[[target[k]]for k in cols])]
            assert not any(a.sign() for a in subvec(target,combine(w,R)))
            return w
    raise AssertionError("rank")

def pay_reverse(labels,a,b):
    C=[Ynorm[i]for i in labels];a0=labels.index(a);b0=labels.index(b)
    muA=mu(Ynorm[a],5);muB=mu(Ynorm[b],5);ea=ps(Ynorm[a],5);eb=ps(Ynorm[b],5)
    A,g=ap_seed(C[:6]);_,q=clean(A,C[:6],g)
    A,g=ap_seed(C[:6],(1,0,0));_,q1=clean(A,C[:6],g)
    u,f0=q
    f=-small_det([u,f0,muA,ea,muB])/small_det([u,subvec(q1[1],f0),muA,ea,muB])
    A,g=ap_seed(C,(f,0,0));_,q=clean(A,C,g)
    A,g=ap_seed(C,(f,1,0));_,q1=clean(A,C,g)
    A,g=ap_seed(C,(f,0,1));_,q2=clean(A,C,g)
    F=[subvec(q1[2],q[2]),subvec(q2[2],q[2]),mult(-1,q[0]),mult(-1,q[1]),mult(-1,muA)]
    k1,k2,d0,d1,d2=[r[0]for r in solve(tr(F),[[z]for z in mult(-1,q[2])])]
    assert d2.sign()
    A,g=ap_seed(C,(f,k1,k2));M,V=clean(A,C,g)
    h=fit(V,muA)
    p=fit(V+[ea],muB)
    rev=[r+[Z,Z]for r in A]
    first=combine(h,M)
    row1=subvec(mult(2,first),subvec(A[a0],identity(7,a0)))+[O,Z]
    w1=mult(Q(1,2),addvec(identity(9,a0),identity(9,7)))
    w2=mult(Q(1,2),addvec(identity(9,b0),identity(9,8)))
    last=addvec(combine(p[:3],M)+[Z],mult(p[3],w1[:8]))
    row2=subvec(mult(2,last),subvec(A[b0],identity(7,b0))+[Z])+[O]
    rev.extend((row1,row2))
    D4=solve(V+[ea,eb],[r+[Z,Z]for r in M]+[w1,w2])
    C+=[Ynorm[a],Ynorm[b]]
    return rev,D4,C,w1,w2,(f,k1,k2)
def lower_rank(A):
    A=[list(r)for r in A];r=0
    for j in range(len(A[0])):
        if len(A)==r:break
        k=max(range(r,len(A)),key=lambda i:A[i][j].inf())
        if not A[k][j].sign():continue
        A[k],A[r]=A[r],A[k]
        for i in range(r+1,len(A)):
            c=A[i][j]/A[r][j]
            for u in range(j+1,len(A[0])):A[i][u]=A[i][u]-c*A[r][u]
            A[i][j]=Z
        r+=1
    return r

def poly_extra(D4,prof,p,n):
    f=[Z]*n+[p];v=[dot(r,prof)for r in D4]+[Z]
    return subvec(f,v)
def test_words(A,D,c,w1,w2):
    layer=[([O]*len(A),O)];maxerr=0;V=None
    for n in range(6):
        for t,p in layer:
            for r,x in [(w1,c[-2]),(w2,c[-1])]:
                e=dot(r,t)-p*x**n
                assert not e.sign()
                maxerr=max(maxerr,e.sup())
            if n<5:
                for i,row in enumerate(D):
                    e=dot(row,t)-(p if i==n else Z)
                    assert not e.sign()
                    maxerr=max(maxerr,e.sup())
            else:
                if V is None:V=[]
                V.append(poly_extra(D,t,p,n))
        if n<5:
            layer=[(vec,fac)for t,p in layer for vec,fac in
                   [([dot(row,t)for row in A],p/(n+1)),([a*b for a,b in zip(t,c)],p)]]
    return V,maxerr
def front_rank():
    roots=cert_roots();u,pts,pay=cert_ports(roots)
    A,D=actual_bank(roots,u,pts,pay)
    T=[(1,[O]*len(A))]
    for n in range(2,8):
        old=T[:]
        def rec(rem,k,q):
            if not rem:T.append((n,q));return
            for i in range(k,len(old)):
                d,t=old[i]
                if d<=rem:rec(rem-d,i,[z*d*dot(row,t)for z,row in zip(q,A)])
        rec(n-1,0,[O]*len(A))
    return lower_rank([subvec([Z]*6+[O],[dot(r,t)for r in D]+[Z])for n,t in T if n==7])

def mixed_probe(V,a,b):
    # A polynomial annihilating the six nonterminal physical forward sites.
    X=[(1-y)/gamma for y in Y]
    H=[O]
    for i,x in enumerate(X):
        if i not in (a,b):H=conv(H,[-x,O])
    ua,ub=(W[i]*ev(H,X[i])for i in (a,b))
    assert ua.sign() and ub.sign()
    return max((ua*dot(v,mu(Ynorm[a],6))+ub*dot(v,mu(Ynorm[b],6))).inf() for v in V)

if __name__=='__main__':
    labels=[3,2,1,4,5,6,7]
    a,b=6,4
    A,D,c,w1,w2,params=pay_reverse(labels,a,b)
    assert all((r[i]-1).sup()==0 and all(x.sup()==0 for x in r[i+1:]) for i,r in enumerate(A))
    assert all(not (sum(r,Z)-x).sign()for r,x in zip(A,c))
    V,err=test_words(A,D,c,w1,w2)
    print('Actual nine reverse rows verified by the paid AP word architecture, and 63 directed word diagnostics.')
    print('Worst word residual enclosure < 2^(%s).' % (err.bit_length()-B))
    print('Exact lower rank of forward first-excess residual:',front_rank())
    print('Exact lower rank of reverse first-excess residual:',lower_rank(V))
    M=mixed_probe(V,a,b);assert M>0
    print('The required terminal-only mixed pairing has a separated witness, magnitude >= 2^(%s).'%(M.bit_length()-1-B))
