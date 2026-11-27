"""Directed actual 15-stage one-defect prefix with a true size-eight row at 14."""
import json,sys
from pathlib import Path
from itertools import combinations
helper=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'real-sdirk13-forward-ports'
sys.path.insert(0,str(helper))
from check_two_ports import I,B,S,ev,der,plus,sc,T,solve,tr,around,sign_bracket,dot
Z=I.val(0);O=I.val(1)
def eye(n,i):return [I.val(j==i)for j in range(n)]
def combine(w,A):return [dot(w,u)for u in tr(A)]
def sub(a,b):return [x-y for x,y in zip(a,b)]
def add(a,b):return [x+y for x,y in zip(a,b)]
N=json.loads((Path(__file__).resolve().parent/'stem-centers.json').read_text())
W=[[O]]
for n in range(1,7):W.append(sc(n,T(W[-1])))
R={}
for k,cs in N['clocks'].items():
    n=int(k);R[n]=[]
    for x in cs:
        if n==1:R[n].append(O)
        else:
            _,a,_=around(x,'1e-46')
            sign_bracket(W[n],a)
            R[n].append(a)
def lift(n,p):
    r=R[n];h=n-len(r)
    t=solve([[ev(W[j],x)for j in range(h,n)]for x in r],[[-ev(p,x)]for x in r])
    for j,r in enumerate(t,h):p=plus(p,sc(r[0],W[j]))
    return p
M=lift(4,W[0]);M=plus(M,sc(-M[3],W[3]))
U=[W[6],lift(6,W[4]),lift(6,lift(5,W[2])),lift(6,lift(5,M))]
P=[T(p)for p in U]
def proj(a):return [a[0]+25*a[1],*a[2:]]
def pair(which,v,deriv=False):
    return proj([ev(der(p) if deriv else p,v)for p in which])
def f(v,y):
    p=pair(P,v);q=pair(U,y)
    return [p[0]*q[j]-p[j]*q[0] for j in [1,2]]
def jac(v,y):
    p=pair(P,v);q=pair(U,y)
    dp=pair(P,v,True);dq=pair(U,y,True)
    return [[dp[0]*q[j]-dp[j]*q[0],p[0]*dq[j]-p[j]*dq[0]]for j in [1,2]]
def det2(A):return A[0][0]*A[1][1]-A[0][1]*A[1][0]
v0,v,r=around(N['v'],'1e-29');y0,y,r2=around(N['y'],'1e-29');assert r==r2
J=jac(v,y);assert det2(J).sign()
J0=[[a.midpoint()for a in t]for t in jac(v0,y0)]
L=[[a.midpoint()for a in t]for t in solve(J0,[eye(2,0),eye(2,1)])]
assert det2(L).sign()
norm=max(sum((I.val(i==j)-dot(L[i],row)).sup()for j,row in enumerate(tr(J))) for i in range(2))
off=max(dot(row,f(v0,y0)).sup()for row in L)
assert norm<S and off*S+norm*r<S*r
assert pair(U,y)[0].sign() and pair(P,v)[0].sign()
l=pair(P,v)[0]/pair(U,y)[0]
tau=ev(P[1],v)/l-ev(U[1],y)
assert l.sign() and tau.sign()
print('Two original shifted-jet equations contract: norm < 2^(%s), displacement < 2^(%s)'%(norm.bit_length()-B,off.bit_length()-B))

def base():
    A=[];D=[];old4=None
    for n in range(1,7):
        r=R[n];old=len(A);m=len(r);z=[Z]*m;L=n-m;Nn=old+m
        A=[row+z for row in A]
        for i,x in enumerate(r):
            strict=[dot([ev(W[k+1],x)/(k+1)for k in range(n-1)],column)for column in tr(D)]if old else []
            A.append(strict+eye(m,i))
        pre=[row+z for row in D[:L]]
        v=[[ev(W[k],x)for k in range(L)]for x in r]
        obs=[sub(eye(Nn,old+i),combine(v[i],pre) if L else [Z]*Nn)for i in range(m)]
        d=solve([[ev(W[j],x)for j in range(L,n)]for x in r],obs)
        D=pre+d
        if n==4:old4=D[3]
    old4=old4+[Z]*(len(A)-len(old4))
    h=sub(sc(I.val('1/4'),sub(D[3],old4)),sc(I.val('25/6'),D[5]))
    Q=[[dot([p[j] if j<len(p) else Z for p in W[:6]],r)for r in tr(D)]for j in range(6)]
    return A,Q,h

def rank_lower(A):
    A=[r[:]for r in A];v=0
    for j in range(len(A[0])):
        if v==len(A):break
        i=max(range(v,len(A)),key=lambda i:A[i][j].inf())
        if not A[i][j].sign():continue
        A[v],A[i]=A[i],A[v]
        for i in range(v+1,len(A)):
            h=A[i][j]/A[v][j]
            A[i][j]=Z
            for k in range(j+1,len(A[0])):A[i][k]=A[i][k]-h*A[v][k]
        v+=1
    return v

def candidate_second_port_gate():
    row=add([ev(p,y)for p in U],sc(tau,[I.val(-25),O,Z,Z]))
    E=[row,[ev(p,v)for p in U]]
    for cols in combinations(range(4),2):
        mat=[[r[i]for i in cols]for r in E]
        if rank_lower(mat)==2:break
    else:raise AssertionError('two actual observation rows must be independent')
    pols=[]
    for free in range(4):
        if free in cols:continue
        v0=[r[0]for r in solve(mat,[[-r[free]]for r in E])]
        c=eye(4,free)
        for i,z0 in zip(cols,v0):c[i]=z0
        p=[dot(c,[p[j]if j<len(p)else Z for p in U])for j in range(7)]
        assert not ev(T(p),v).sign()
        t=T(p);d=len(t)-1;w=[Z]*d;w[-1]=t[-1]
        for i in reversed(range(d-1)):w[i]=t[i+1]+v*w[i+1]
        assert not (t[0]+v*w[0]).sign()
        pols.append(w)
    a,b=pols
    assert a[-1].sign() and b[-1].sign()
    m=len(a)-1;n=len(b)-1
    S0=[[Z]*i+a+[Z]*(n-i-1)for i in range(n)]+[[Z]*i+b+[Z]*(m-i-1)for i in range(m)]
    assert rank_lower(S0)==m+n
    print('After the first 14 rows, the two shifted residual polynomials have no other common root (full Sylvester rank after removing v).')

def construct():
    G,D,h=base();x=I.val(2)
    A=[r+[Z]*3 for r in G]
    pv=lambda y:[y**j for j in range(6)]
    mu=lambda y:[y**(j+1)/(j+1)-y**j for j in range(6)]
    A.append(add(combine(mu(y),D),sc(tau,h))+[O,Z,Z])
    A.append(combine(sub(mu(v),sc(l,pv(y))),D)+[l,O,Z])
    A.append(combine(mu(x),D)+[Z,Z,O])
    rowY=add([ev(p,y)for p in U],sc(tau,[I.val(-25),O,Z,Z]))
    E=[rowY,[ev(p,v)for p in U],[ev(p,x)for p in U]]
    obs=[sub(eye(15,i),combine(pv(u),D)+[Z]*3)for i,u in zip((12,13,14),(y,v,x))]
    for J in combinations(range(4),3):
        if rank_lower([[p[j]for j in J]for p in E])==3:
            t=solve([[p[j]for j in J]for p in E],obs)
            Q1=[([O]*4)[i] if i not in J else Z for i in range(4)]
            idF=next(i for i in range(4) if i not in J)
            uv=solve([[p[j]for j in J]for p in E],[[-p[idF]]for p in E])
            for i,a in zip(J,uv):Q1[i]=a[0]
            break
    else:raise AssertionError
    Q=[dot(Q1,[p[j]if j<len(p)else Z for p in U])for j in range(7)]
    D=[r+[Z]*3 for r in D]+[[Z]*15]
    for j in range(7):
        for i in range(15):
            D[j][i]=D[j][i]+dot([U[k][j]if j<len(U[k])else Z for k in J],[r[i]for r in t])
    return A,D,Q,idF
def test(A,D,Q,idF):
    c=[sum(r,Z)for r in A]
    targets=[x for n in range(1,7) for x in R[n]]+[y,v,I.val(2)]
    assert all(not w.sign()for w in sub(c,targets))
    assert not ev(Q,v).sign() and not ev(T(Q),v).sign()
    cats=[];worst=0;U8=[];newQ=True
    j=max(range(len(Q)),key=lambda k:Q[k].inf());assert Q[j].sign()
    for n in range(1,9):
        pool=cats[:]
        def rec(k,start,a):
            nonlocal worst
            if not k:
                err=a[13]-v**(n-1)
                assert not err.sign();worst=max(worst,err.sup())
                r=sub([I.val(j==n-1)for j in range(8)],[dot(row,a)for row in D]+[Z])
                if n<=6:assert not any(v.sign()for v in r)
                if n==7:
                    h=r[j]/Q[j]
                    assert not any(v.sign() for v in sub(r,sc(h,Q)+[Z]))
                if n==8:
                    U8.append(r)
                cats.append((n,[n*dot(row,a)for row in A]));return
            for i in range(start,len(pool)):
                m,u=pool[i]
                if m<=k:rec(k-m,i,[x*y for x,y in zip(a,u)])
        # Avoid shadowing the certified port in the inner recursive loop.
        rec(n-1,0,[O]*15)
    assert len(cats)==200
    print('Actual row 14 forwards all 200 rooted profiles through size 8; worst enclosure < 2^(%s).'%(worst.bit_length()-B))
    print('After row 15 the paid size-seven residual rank is one.')
    print('Rank of the size-eight residual plus the missing line, lower certificate:',rank_lower(U8+[Q+[Z]]))

if __name__=='__main__':
    test(*construct())
    candidate_second_port_gate()
