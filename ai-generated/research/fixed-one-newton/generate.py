"""Reconstruct the fixed rational one-diagonal tableaux; direct verification is independent.
Usage: python generate.py PATH_TO_FIVE_STAGE_JSON --out DIR (requires SymPy).
"""
from pathlib import Path
import argparse, json, math
from functools import reduce
import sympy as sp
R=sp.Rational; M=sp.Matrix; X=sp.Symbol("X")
def integral(poly):
    return sum(v/(i+1) for (i,),v in sp.Poly(poly,X).terms())
def at(poly,x):
    return sp.Poly(poly,X).eval(x)
def trees(p):
    children=[()]; ns=[1]
    for n in range(2,p+1):
        oldlen=len(ns)
        def rec(rem,start,kids):
            if not rem:yield tuple(kids);return
            for i in range(start,oldlen):
                if ns[i]>rem:break
                yield from rec(rem-ns[i],i,kids+[i])
        add=list(rec(n-1,0,[]));children+=add;ns += [n]*len(add)
    return children,ns
def weighted_tree_data(A,degree):
    kids,ns=trees(degree); data=[];pr=[]
    for k,n in zip(kids,ns):
        v=sp.ones(A.rows,1)
        for i in k: v=v.multiply_elementwise(pr[i])
        data.append(v);pr.append(n*A*v)
    return M.hstack(*data),ns
def strict_stage(A,x,gamma,size):
    E,ns=weighted_tree_data(A,size-1)
    target=M([[x**n/n - gamma*x**(n-1) for n in ns]])
    cols=list(E.rref()[1]); rows=list(E[:,cols].T.rref()[1])
    T=E.extract(rows,cols)
    coeff=target[:,cols]*T.inv()
    v=sp.zeros(1,A.rows)
    for j,i in enumerate(rows):v[i]=coeff[j]
    assert v*E==target, ('no such pure row',x,size)
    return v
def solve_node(known):
    H=sp.prod(X-z for z in known)
    z=integral(X*H)/integral(H)
    assert z not in known and len(set(known))==len(known)
    return z
def lift(A,b,p,head_spec,free_clock_spec):
    gamma=A[0,0]; q=(p-1)//2; a=p-q-1; oldN=A.rows
    pins=[1-(2*i-1)*gamma for i in range(a,0,-1)]
    known=list(free_clock_spec)+pins
    z=solve_node(known); xs=list(free_clock_spec)+[z]+pins;k=len(xs); h=k-a
    assert k==p-1 and len(head_spec)==h
    F=sp.Poly(sp.prod(X-x for x in xs),X)
    w=[integral(F.exquo(sp.Poly(X-x,X)).as_expr())/F.diff().eval(x) for x in xs]
    assert all(w) and all(sum(wi*x**j for wi,x in zip(w,xs))==R(1,j+1) for j in range(p))
    defect=(p+1)*sum(wi*x**p for wi,x in zip(w,xs))-1
    assert defect!=0
    P=[sp.Integer(1)]
    for x in reversed(xs):P.append(sp.expand(P[-1]*(X-x)))
    L=M([[wi*at(Pj,x) for x,wi in zip(xs,w)] for Pj in P])
    S=sp.zeros(k); U=sp.zeros(k,oldN); partial=A; merges={}
    for j,(mode,parameter) in enumerate(head_spec):
        if mode=='new':
            v=strict_stage(partial,xs[j],gamma,parameter)
        else:
            r=parameter; assert xs[j]==sum(A[r,:])
            v=sp.zeros(1,oldN+j);v[0,:oldN]=A[r,:];v[r]=0;merges[j]=r
        partial=partial.row_join(sp.zeros(partial.rows,1)).col_join(v.row_join(M([[gamma]])))
        U[j,:]=v[:,:oldN]
        if j:S[j,:j]=v[:,oldN:]
    for j in range(k):
        piv=list(range(max(h,j+1),k));d=len(piv)
        if not d:continue
        right=M([-L[i+1,j]/(i+1) for i in range(d)])-L[:d,:h]*S[:h,j]
        vals=L.extract(range(d),piv).inv()*right
        for t,row in enumerate(piv):S[row,j]=vals[t]
    for i in range(a):assert L[i,:]*S==-L[i+1,:]/(i+1)
    c=A*sp.ones(oldN,1)
    H=sp.zeros(a,oldN)
    for i in range(a):
        J=sp.integrate(P[i],X)
        hi=sp.expand(J.subs(X,1)-J-gamma*P[i]+P[i+1]/(i+1))
        assert hi==0 or sp.degree(hi,X)<=i-1
        for j in range(oldN):H[i,j]=b[j]*at(hi,c[j])
    U[h:,:]=L[:a,h:].inv()*(H-L[:a,:h]*U[:h,:])
    B=S+gamma*sp.eye(k)
    AA=A.row_join(sp.zeros(oldN,k)).col_join(U.row_join(B)); bb=sp.zeros(oldN,1).col_join(M(w))
    # All virtual duplicate row definitions were paid as exact equalities, not a same-clock assumption.
    for j,r in sorted(merges.items(),reverse=True):
        k0=oldN+j
        rrow=AA.row(r).copy();drow=AA.row(k0).copy();rrow[r]-=gamma;drow[k0]-=gamma
        assert rrow==drow
        AA[:,r]+=AA[:,k0];bb[r]+=bb[k0]
        AA.row_del(k0);AA.col_del(k0);bb.row_del(k0)
    # Return physical indices of the newly retained output rows.
    indices=[merges[j] if j in merges else oldN+j-sum(i<j for i in merges) for j in range(k)]
    return AA,bb,indices,xs,defect
def dump(A,b,p,defect,path):
    ad=math.lcm(*(int(v.q) for v in A));bd=math.lcm(*(int(v.q) for v in b))
    data=dict(order=p,stages=A.rows,common_diagonal="1",a_denominator=ad,b_denominator=bd,a_integer=[[int(ad*v) for v in A.row(j)] for j in range(A.rows)],b_integer=[int(bd*v) for v in b],next_bush_defect=str(defect))
    (path/('tableau-'+str(p)+'.json')).write_text(json.dumps(data,indent=1)+'\n')
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('seed',type=Path);parser.add_argument('--out',type=Path,default=Path('.'));o=parser.parse_args()
    t=json.loads(o.seed.read_text());A=M(t['a_integer'])/t['a_denominator'];b=M(t['b_integer'])/t['b_denominator']
    assert A.shape==(5,5) and A[0,0]==1
    A,b,idx,xs,df=lift(A,b,7,[('new',4),('new',4),('new',5)],[R(-1),R(-3)])
    dump(A,b,7,df,o.out);print('order 7',A.rows,xs,'defect',df,flush=True)
    A,b,idx,xs,df=lift(A,b,9,[('merge',idx[2]),('new',5),('new',6),('new',6)],[xs[2],R(-5),R(-7)])
    dump(A,b,9,df,o.out);print('order 9',A.rows,xs,'defect',df,flush=True)
    A,b,idx,xs,df=lift(A,b,11,[('merge',idx[2]),('merge',idx[3]),('new',7),('new',7),('new',7)],[xs[2],xs[3],R(-9),R(-11)])
    dump(A,b,11,df,o.out);print('order 11',A.rows,xs,'defect',df,flush=True)
if __name__=='__main__':main()
