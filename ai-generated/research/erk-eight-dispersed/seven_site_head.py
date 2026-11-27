#!/usr/bin/env python3
"""Exact linear feasibility for a prescribed signed seven-site rank-four chart."""
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import json
import sympy as s
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'erk-eight-rank3-four'))
from construct import audit

def feasible(order, a=Q(1,8), anchors=None, loud=False):
    h=Q(1,2)
    if anchors is None:
        anchors=(h/2,h)
    N,T=anchors
    # Actual physical clock order: origin, three inactive defective head rows,
    # first pure midpoint, four active dispersed rows, repeated pure midpoint,
    # terminal. For this chart the head is the known T=2N rank-two prefix.
    assert N==h/2 and T==h
    clocks=[Q(0),a,N,T,h,*order,h,Q(1)]
    wM={Q(0):Q(7,80),Q(1):Q(7,80),Q(2,7):Q(16807,38880),
        Q(5,7):Q(16807,38880),Q(-1):Q(-1,38880),Q(2):Q(-1,38880),
        h:Q(-16,405)}
    b=[wM[0],Q(0),Q(0),Q(0),Q(0),*(wM[x] for x in order),wM[h],wM[1]]
    assert all(sum(bi*ci**k for bi,ci in zip(b,clocks))==Q(1,k+1) for k in range(8))
    y=[1-t for t in clocks]
    f3=h*h/(8*a)
    f4=-h*h/(2*a)
    f=[Q(0),Q(0),f3,f4,*([Q(0)]*7)]
    A=[[Q(0)]*11 for _ in range(11)]
    A[1][0]=a
    A[2][:2]=[N-f3,f3]
    A[3][:3]=[h-f4-2*h,f4,2*h]
    A[4][:4]=[h/6,Q(0),2*h/3,h/6]
    P=lambda x:7*x*x-7*x+1
    delta=[Q(0)]*11
    delta[0]=b[0]-Q(1,20)
    delta[4]=b[9]*y[9]*P(h)+Q(2,15)
    for i in range(5,9):
        delta[i]=b[i]*y[i]*P(clocks[i])
    assert all(sum(delta[i]*clocks[i]**k for i in range(11))==0 for k in range(5))
    scale=b[8]*y[8]**2/(2*b[9]*y[9]*delta[8])
    delta=[x*scale for x in delta]
    A[9]=[a+b for a,b in zip(A[4],delta)]
    tau=-b[9]*y[9]**2
    lam=b[9]*y[9]*(3*y[9]-2*y[8])
    eqs=[]
    vs=[]
    for i in range(5,9):
        for j in range(i):
            if j!=1:
                t=s.Symbol(f'M{i+1}_{j+1}')
                vs.append(t)
                A[i][j]=t
        for k in range(3):
            eqs.append((f'F{i+1},{k}',sum(A[i][j]*clocks[j]**k for j in range(i))-clocks[i]**(k+1)/(k+1)))
    for j in range(10):
        A[10][j]=(b[j]*y[j]-sum(b[i]*A[i][j] for i in range(10)))/b[10]
    r=[int(i==9)-int(i==4) for i in range(11)]
    def reverse(k,j):
        return (k+1)*sum(b[i]*y[i]**k*A[i][j] for i in range(11))-b[j]*y[j]**(k+1)
    for j in range(11):
        eqs.append((f'J1,{j+1}',reverse(1,j)-tau*r[j]))
        eqs.append((f'J2,{j+1}',reverse(2,j)-y[9]*tau*r[j]-lam*delta[j]))
    for p,test in [('f',f),('c3',[c**3 for c in clocks])]:
        # J3 on c^0,c^1,c^2 is already paid by the exact forward
        # primitives; J3 on q=e2 likewise by strict support.
        eqs.append((f'J3{p}',sum(reverse(3,j)*col for j,col in enumerate(test))))
        # δ annihilates c^0..c^4 and all pure head coordinates.
        eqs.append((f'deltaA{p}',sum(delta[i]*A[i][j]*col
                    for i in range(11) for j,col in enumerate(test))))
    try:
        M, rhs=s.linear_eq_to_matrix([t for _,t in eqs],vs)
        z,params=M.gauss_jordan_solve(rhs)
    except ValueError:
        if loud:
            # Give an exact linear contradiction in the left cokernel.
            N=M.T.nullspace()
            cert=[]
            for n in N:
                value=(n.dot(rhs))
                if value:
                    cert.append((sum(q!=0 for q in n),n,value))
            k,n,v=min(cert,key=lambda x:x[0])
            print('infeasible',a,order,'rank',M.rank(),'vars',len(vs),'cert support',k)
            print([(label,str(c)) for (label,_),c in zip(eqs,n) if c],v)
        return
    z=[Q(str(q.subs({p:0 for p in params}))) for q in z]
    tab=[[Q(str(s.sympify(w).subs(dict(zip(vs,z))))) for w in row] for row in A]
    assert [sum(row) for row in tab]==clocks
    failed,dev=audit(tab,b)
    if failed:
        print('unexpected order failure',len(failed),failed[0])
        return
    print('literal feasible!',clocks,'free parameters',list(params),'bush9',dev)
    return dict(A=[[str(v) for v in row[:i]] for i,row in enumerate(tab)],b=list(map(str,b)),
        clocks=list(map(str,clocks)),defect=str(dev))

if __name__=='__main__':
    # The last reverse two-column condition selects preceding clocks 2,5/7.
    data=[]
    for early in [(Q(2,7),Q(-1)),(Q(-1),Q(2,7))]:
      order=[*early,Q(2),Q(5,7)]
      for a in [Q(1,8),Q(1,6),Q(1,5),Q(1,4),Q(2,7),Q(2,5)]:
        res=feasible(order,a,loud=True)
        if res:data.append(res)
    if data:Path('candidate-family.json').write_text(json.dumps(data,indent=2)+'\n')
