from itertools import combinations, permutations
from math import prod
from functools import lru_cache
import sys,json

class F:
 def __init__(self,p):
    self.p=p
    self.I=[0]+[pow(i,-1,p) for i in range(1,p)]
 def inv(self,a):return self.I[a%self.p]
 def dot(self,a,b):return sum(x*y for x,y in zip(a,b))%self.p
 def scale(self,k,a):return [k*z%self.p for z in a]
 def mul(self,a,b):
    q=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):q[i+j]+=x*y
    return [x%self.p for x in q]
 def hull(self,r):
    q=[1]
    for x in r:q=self.mul(q,[-x,1])
    return q
 def integ(self,q):return self.dot(q,self.I[1:])
 def solve(self,A,b,n=None):
    M=[[x%self.p for x in row]+[z%self.p]for row,z in zip(A,b)]
    N=n or len(M[0])-1
    ix=[]
    for j in range(N):
        i=len(ix);k=next((k for k in range(i,len(M))if M[k][j]),None)
        if k is None:continue
        ix.append(j);M[i],M[k]=M[k],M[i]
        M[i]=self.scale(self.inv(M[i][j]),M[i])
        for k in range(i+1,len(M)):
            if M[k][j]:
                v=M[k][j];M[k][j:]=[(u-v*w)%self.p for u,w in zip(M[k][j:],M[i][j:])]
    if any(r[-1]for r in M[len(ix):]):return
    x=[0]*N
    for i,row in reversed(list(zip(ix,M))):x[i]=(row[-1]-self.dot(row[:-1],x))%self.p
    return x,len(ix)
 def solveUni(self,A,b):
    z=self.solve(A,b)
    assert z is not None and z[1]==len(A[0]),(A,b,z)
    return z[0]

class Chart:
 def __init__(self,a,b,c,r,W,mu,arith):
    self.a,self.b,self.c=a,b,c
    self.r=r;self.W=W;self.mu=mu;self.F=arith;self.p=arith.p
    p=self.p;I=arith.inv
    # A1 and A2 equally split; likewise the dormant B pair.
    w0,wA,wB,wC=W[0],W[a]*I(2)%p,W[b]*I(2)%p,W[c]
    self.y=[0,a,a,b,b,c]
    self.w=[w0,wA,wA,wB,wB,wC]
    self.hu={z:-mu[a]*a*a*z*I(4*mu[z])%p for z in [a,b,c]+list(r)}
    self.h=[0,0,-a**3*I(2)%p,a**3%p,(2*self.hu[b]-a**3)%p,self.hu[c]]
    self.u=[0,-a*a*I(2)%p,a*a*I(2)%p,0,0,0]
    # L rows 0, A1, A2, B1 have literal one-tap histories.
    self.L=[[],[a],[0,a],[0,0,b]]
    def input_for(z,u,h):return [1,z,z*z,u,z**3,h]
    self.M=[input_for(z,u,h)for z,u,h in zip(self.y,self.u,self.h)]
    self.m=[z**4%p for z in self.y]
    self.s=[z*h%p for z,h in zip(self.y,self.h)]
    for i in (4,5):
        basis=list(zip(*self.M[:i]))
        ids=[0,1,2,3] if i==4 else [0,1,2,3,5]
        z=self.y[i];h=self.h[i]
        response=self.responses(z,0,h)
        self.L.append(self.F.solveUni([basis[j]for j in ids],[response[j]for j in ids]))
        assert all(self.F.dot(self.L[i],row)==v%p for row,v in zip(basis,response))
    for i,row in enumerate(self.L):
        assert all(self.F.dot(row,col)==v%p for col,v in zip(zip(*self.M),self.responses(self.y[i],self.u[i],self.h[i]))),i
    self.base={};self.effects={}
    for z in r:
        self.base[z]=self.F.solveUni(list(zip(*self.M)),self.responses(z,0,self.hu[z]))
        t=self.F.solveUni(list(zip(*self.M)),input_for(z,0,self.hu[z]))
        self.effects[z]=((z**4-self.F.dot(t,self.m))%p,
                         (z*self.hu[z]-self.F.dot(t,self.s))%p,t)
    self.target1={z:(self.F.dot(self.base[z],self.m)-z**5*I(5))%p for z in r}
    self.target2={z:self.F.dot(self.base[z],self.s) for z in r}
    self.tests=[]
    for k in range(1,5):
        B1=-sum(w*(1-z)**k*(self.F.dot(row,self.m)-z**5*I(5))
                for z,w,row in zip(self.y,self.w,self.L))
        B1-=sum(W[z]*(1-z)**k*self.target1[z]for z in r)
        B2=-sum(w*(1-z)**k*self.F.dot(row,self.s)for z,w,row in zip(self.y,self.w,self.L))
        B2-=sum(W[z]*(1-z)**k*self.target2[z]for z in r)
        self.tests.append((B1%p,B2%p))
 def responses(self,z,u,h):
    p=self.p;I=self.F.inv;a=self.a
    return [z,(z*z*I(2)+u)%p,(z**3*I(3)+(2*a*u-2*h)*I(3))%p,h,
        (z**4*I(4)+a*a*u*I(2)-z*h)%p,(a-z)*h%p]
 def terminal(self,perm):
    pairs=[(i,j)for i in range(4)for j in range(i)]
    rows=[];rr=[]
    for k,(t1,t2) in enumerate(self.tests,1):
       for s,t in enumerate((t1,t2)):
           rows.append([self.W[perm[i]]*pow((1-perm[i])%self.p,k,self.p)*self.effects[perm[j]][s]%self.p for i,j in pairs])
           rr.append(t)
    z=self.F.solve(rows,rr)
    if z is None:return
    L=[r[:]for r in self.L]
    for i,v in enumerate(perm):L.append(self.base[v][:]+[0]*i)
    for g,(i,j) in zip(z[0],pairs):
        L[6+i][6+j]=g
        L[6+i][:6]=[(a-g*b)%self.p for a,b in zip(L[6+i][:6],self.effects[perm[j]][2])]
    return L
 def forward(self,perm,L):
    p=self.p;I=self.F.inv
    ys=self.y+list(perm)
    x=[(1-y)%p for y in ys]
    w=self.w+[self.W[v]for v in perm]
    xx=x[::-1];ww=w[::-1]
    B=[[w[9-j]*L[9-j][9-i]*I(w[9-i])%p for j in range(i)]for i in range(10)]
    forms=[]
    for i,y in enumerate(xx):
        forms.append([(self.F.dot(B[i],[pow(v,k,p)for v in xx])-pow(y,k+1,p)*I(k+1))%p
                      for k in (1,2,3)])
    z=self.F.solve([row[:2]for row in forms],[-row[2]%p for row in forms],2)
    if z is None:return None
    v,u=z[0]
    P=lambda z: z**3+u*z*z+v*z
    assert not any(self.F.dot(r,[v,u,1])for r in forms)
    for s in range(1,p):
        if not P(s)%p:continue
        den=(3*s*s+2*s*u+2*v)%p
        pp=s*v*I(den)%p if den else next(q for q in range(1,p)if q!=s)if not v else 0
        if pp and pp!=s:break
    else:return None
    q=next(q for q in range(1,p)if q not in (s,pp))
    e=1
    Vs=s*s*I(2*e)%p
    al=pp*pp*(3*s-2*pp)*I(s**3)%p
    be=P(q)*I(P(s))%p
    js=(pp*pp-al*s*s)*I(2*s)%p
    B1=(q*q*I(2)-be*Vs*e)%p
    B2=(q**3*I(3)-be*Vs*2*e*s*I(3))%p
    qs=(pp*B1-B2)*I(s*(pp-s))%p
    qp=(B2-s*B1)*I(pp*(pp-s))%p
    A=[[],[e],[(s-Vs)%p,Vs],[(pp-al*Vs-js)%p,al*Vs%p,js],
            [(q-be*Vs-qs-qp)%p,be*Vs%p,qs,qp]]
    Q=[[1,0,0],[1-al,pp-al*s,pp*pp-al*s*s],[1-be,q-be*s,q*q-be*s*s]]
    rhs=[[1,0,0],[0,0,0],[0,-al,-be],[0,1,0],[0,0,1]]
    Pi=[self.F.solveUni(Q,z)for z in rhs]
    for i,x in enumerate(xx):
        row=[(x**(k+1)*I(k+1)-self.F.dot(B[i],[pow(y,k,p)for y in xx]))%p for k in range(3)]
        A.append([self.F.dot(r,row)for r in Pi]+B[i])
    weights=[self.W[1],0,0,0,0]+ww
    return {'mod':p,'a':A,'b':weights,'reverse_y':ys,'kernel_ascending':[0,v,u,1],
            'low_clocks':[0,e,s,pp,q],'reverse_L':L}

def actual(t):
    p,A,b=t['mod'],t['a'],t['b']
    @lru_cache(None)
    def size(t):return 1+sum(size(v)for v in t)
    @lru_cache(None)
    def d(t):return size(t)*prod(d(v)for v in t)
    @lru_cache(None)
    def phi(t):
        pre=[phi(u)for u in t]
        return [prod(sum(a*z for a,z in zip(r,v))%p for v in pre)%p for r in A]
    G={1:[()]}
    fault=None;checks=0
    for k in range(1,12):
        if k>1:
            T=[(t,j)for j in range(1,k)for t in G[j]]
            def forests(n,i):
                if not n:yield ()
                else:
                    for j in range(i,len(T)):
                        u,s=T[j]
                        if s>n:break
                        for tail in forests(n-s,j):yield (u,)+tail
            G[k]=list(forests(k-1,0))
        for tree in G[k]:
            res=(d(tree)*sum(w*z for w,z in zip(b,phi(tree)))-1)%p
            if k<=10:
                assert res==0,(k,tree,res,t)
                checks+=1
            elif fault is None and res:fault=(tree,res)
    assert checks==1205
    print('All',checks,'literal rooted checks; first checked order-11 failure',fault,flush=True)
    return fault

def search(p):
    FF=F(p);I=FF.inv
    counts=[0,0,0,0,0,0,0]
    for a in range(2,p):
        b=2*a%p
        if b in (0,1,a):continue
        fixed=[0,1,a,b]
        for other in combinations([z for z in range(2,p)if z not in fixed],5):
            nodes=fixed+list(other)
            if FF.integ(FF.hull(nodes)):continue
            counts[0]+=1
            mu={z:FF.integ(FF.hull([v for v in nodes if z!=v]))for z in nodes}
            if any(not mu[z]for z in nodes if z!=1):continue
            W={z:mu[z]*I(prod(z-v for v in nodes if z!=v))%p for z in nodes}
            if -a*a*mu[a]%p==2*a*a*mu[b]%p:continue # equal dormant h values
            counts[1]+=1
            for c in other:
                if (mu[c]*c*(c-b)+a*a*mu[a])%p:continue
                counts[2]+=1
                tail=tuple(z for z in other if z!=c)
                chart=Chart(a,b,c,tail,W,mu,FF)
                for perm in permutations(tail):
                    counts[3]+=1
                    L=chart.terminal(perm)
                    if L is None:continue
                    counts[4]+=1
                    t=chart.forward(perm,L)
                    if not t:continue
                    counts[5]+=1
                    fail=actual(t)
                    if fail:
                        t['next_failure']=fail
                        print('literal candidate',p,t,flush=True)
                        with open('exceptional-active-'+str(p)+'.json','w')as f:json.dump(t,f,indent=2)
                        return counts
    return counts
if __name__=='__main__':
    for p in map(int,sys.argv[1:] or [11,13,17,19,23,29]):
        print('start p',p,flush=True)
        print('finish',p,search(p),flush=True)
