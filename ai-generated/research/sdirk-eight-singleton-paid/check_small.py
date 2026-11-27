#!/usr/bin/env python3
from splitting_fields import Engine,degree
from resultant_data import PRIMES
from collections import Counter
from itertools import product

def solve(Rows,d,F):
    A=[row[:] for row in Rows]
    j=0;piv=[]
    for i in range(d):
        a=next((k for k in range(j,len(A)) if A[k][i]!=0),None)
        if a is None:continue
        A[j],A[a]=A[a],A[j]
        A[j]=[s/A[j][i] for s in A[j]]
        for k in range(len(A)):
            if k!=j and A[k][i]!=0:
                u=A[k][i]
                A[k]=[s-u*t for s,t in zip(A[k],A[j])]
        piv.append(i);j+=1
    if any(row[d]!=0 for row in A[j:]):return None
    out=[F.zero() for i in range(d)]
    for i,k in enumerate(piv):out[k]=A[i][d]
    return j,out

def ini(A,E):
    s,u,w,k,q,l=A;K=E.K
    return [K,1+u,1+w],[K/2,k/2,q/2]

def fourth(A,P,D,E):
    X=E.x;K=E.K
    xx,gg=ini(A,E)
    b=solve([[K,x,x*x,g] for x,g in zip(xx,gg)],3,E.F)
    assert b and b[0]==3
    a,b,c=b[1];k=A[3]
    Ft=-a-b*X-c*X*X+a*X+b*X*X/2+c*X**3/3
    Gt=1-(1+(X-1)*(1/k))+b+c*(4*K/3+(2*(k+1)/(3*k))*(X-1))
    R=Ft*D+Gt*P
    assert R
    C=E.Q.one()
    for q in xx:C*=X-q
    quo,rem=divmod(R,C)
    assert not rem and quo.degree()<=1
    res=[]
    for t,e in R.roots():
        p,d=P(t),D(t)
        if d==0:
            if p!=0:continue
            den=Gt(t);num=Ft(t)
            if den==0:
                if num==0:return None,'unfixed vertical residual'
                continue
            g=-num/den
        else:
            g=p/d
        if g==0 or any(t==y and g==h for y,h in zip(xx,gg)):continue
        res.append((t,g))
    return res, ('quartic' if R.degree()==4 else 'degree '+str(R.degree()))

def roots(P):
    return [r for r,e in P.roots()]
def unique(xs):
    return all(x!=y for i,x in enumerate(xs) for y in xs[:i])
def finish(E,a,A,B,tau):
    F=E.F;X=E.x;K=E.K
    G,P,_=E.setup(a); _,Q,_=E.setup(1-a)
    P=P.compose(X-1);Q=Q.compose(X-1)
    D=2*(P(K)+A[-1]*(X-1)); DR=2*(Q(K)+B[-1]*(X-1))
    if not D or not DR:return 'zero entire affine graph'
    W1,reason1=fourth(A,P,D,E);W2,reason2=fourth(B,Q,DR,E)
    same=(P.gcd(D).degree(),Q.gcd(DR).degree())
    if W1 is None or W2 is None:return ('bad fourth branch',reason1,reason2,same)
    if not W1 or not W2:return ('empty fourth',reason1,reason2,same)
    z=1/G;a0=a*z
    xx,g=ini(A,E);yy,h=ini(B,E)
    endx=[z-y for y in yy]
    endg=[tau*h0 for h0 in h]
    if not unique([*zip(xx,g),*zip(endx,endg)]):return 'repeated true pair among openers'
    mom=[(z**j)/(j+1) for j in range(8)]
    qa=2*G
    if same!=(0,0):
        return finish_vertical(E,a0,z,qa,tau,P,D,Q,DR,W1,W2,xx,endx,g,endg,mom)
    rows=[]
    for k in range(4):
        for j in range(8-2*k):
            R=D**(3-k)*P**k*X**j
            v=mom[j]-qa*a0**j if not k else F.zero()
            rows.append([R[i] for i in range(11)]+[v])
    sol=solve(rows,11,F)
    if sol is None:return ('inconsistent masked moments',)
    assert sol[0]==11
    M=sol[1]
    Phi=lambda p:sum((M[j]*p[j] for j in range(p.degree()+1)),start=F.zero())
    fails=[]
    for (t,gt),(s,gs) in product(W1,W2):
        # For this generic graph, pairs at known clocks are determined uniquely.
        ds=xx+[t,z-s]+endx
        Pi=E.Q.one()
        for q in ds:Pi*=X-q
        Y0,Y1,Y2=(Phi(Pi*X**j) for j in range(3))
        dd=Y0*Y2-Y1*Y1
        if dd!=0:
            fails.append(('nonzero pencil',degree(dd,E.p),str(dd)))
            continue
        if Y0==0:
            fails.append(('free clock pivot',Y1,Y2));continue
        q=Y1/Y0
        if D(q)==0 or P(q)==0:
            fails.append(('recovered nonoffzero',));continue
        if not unique(ds+[q]):
            fails.append(('recovered duplicated clock not yet handled',));continue
        is_all=ds+[q]
        Wg=[P(t)/D(t) for t in is_all]
        sol=solve([[t**j for t in is_all]+[M[j]] for j in range(11)],9,F)
        assert sol and sol[0]==9
        ww=[b*D(t)**3 for t,b in zip(is_all,sol[1])]
        if any(b==0 for b in ww):
            fails.append(('silent weight after reconstruction',));continue
        fails.append(('FULL MOMENT DATA',is_all,Wg,ww,a0,qa))
    return fails

def finish_vertical(E,a0,z,qa,tau,P,D,Q,DR,U,V,L,R,l,r,mom):
    F=E.F;X=E.x
    common=P.gcd(D)
    other=Q.gcd(DR)
    if common.degree()!=1 or other.degree()!=1:return 'unsupported vertical degrees'
    d=roots(common)[0];dr=roots(other)[0]
    assert z-dr==d
    H=P//common
    H=H*(1/(D//common)[0])
    h=H(d)
    assert h!=0
    if any(t==d for t in L+R):
        return ('vertical earlier than fourth, unresolved',)
    out=[]
    for (t,g),(s,hs) in product(U,V):
        g2=tau*hs;s=z-s
        if t!=d or s!=d:
            out.append(('at least one nonvertical fourth, unresolved',t,s,d));continue
        # Two visible vertical rows and only one unknown off-zero site. Degree-three
        # moments in g-H(x) force that third site to be vertical too.
        phi=lambda P:sum((P[j]*mom[j] for j in range(P.degree()+1)),start=F.zero())
        mass1=phi(-H)+qa*H(a0)
        mass2=phi(H**2)-qa*H(a0)**2
        mass3=phi(-H**3)+qa*H(a0)**3
        q1,q2=g-h,g2-h
        if mass3-(q1+q2)*mass2+q1*q2*mass1==0:
            out.append(('two-vertical moments permitted, unresolved',));continue
        sites=L+R+[a0,d]
        if not unique(sites):
            out.append(('earlier clocks collide with vertical, unresolved',));continue
        sol=solve([[t**j for t in sites]+[mom[j]] for j in range(8)],8,F)
        assert sol and sol[0]==8
        if sol[1][6]!=qa:
            out.append(('wrong Gauss mass',str(sol[1][6]),str(qa)));continue
        out.append(('vertical paid quadrature, next need chronology',sites,mass1,mass2,mass3))
    return out


def main():
    expected={601:(2,0,2),613:(12,12,0),6277:(2,0,2),
              118709:(12,12,0),5428349:(12,12,0)}
    for p in PRIMES:
        E=Engine(p);X=E.x
        L=70*X**4-140*X**3+90*X*X-20*X+1
        aa=roots(L)
        assert len(aa)==4 and all(degree(a,p) in (1,2,4) for a in aa)
        tally=Counter();total=0
        for a in aa:
            for A,B,tau in E.fronts(a):
                total+=1
                ans=finish(E,a,A,B,tau)
                assert isinstance(ans,list) and len(ans)==1 and isinstance(ans[0],tuple),ans
                outcome=ans[0]
                tally[outcome[0]]+=1
                if p in (601,6277):
                    assert outcome[:3]==(('wrong Gauss mass','392','561') if p==601 else
                                         ('wrong Gauss mass','5211','5613')),outcome
        assert (total,tally["nonzero pencil"],tally["wrong Gauss mass"])==expected.get(p,(0,0,0)),(p,total,tally)
        print(p,total,dict(tally))
if __name__=='__main__':
    main()
