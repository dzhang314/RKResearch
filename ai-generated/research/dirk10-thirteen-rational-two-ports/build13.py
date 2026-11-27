"""Construct the exact rational 13-stage DIRK and recheck its rooted order.

Requires SymPy. audit_tableau.py independently reads only the literal JSON.
"""
from argparse import ArgumentParser
import sympy as S
import json
from pathlib import Path
x=S.symbols('X')
R=S.Rational
def e(f,c): return f.subs(x,c)
def J(f):
    primitive=S.Poly(f,x).integrate()
    return primitive.as_expr()-primitive.eval(0)
def rowq(nodes,a): return S.Matrix([[z**k for z in nodes] for k in range(len(nodes))]).inv()*S.Matrix([a**(k+1)/R(k+1) for k in range(len(nodes))])
def interp(nodes): return [S.expand(S.prod((x-v)/(u-v) for v in nodes if v!=u)) for u in nodes]
def tree_enum(A,p):
    n=A.rows;t=[];sizes=[]
    for k in range(1,p+1):
        layer=[]
        def gen(rem,j,is_):
            if rem==0:
                fac=k;v=S.ones(n,1)
                for i in is_:
                    fac*=t[i][1];v=v.multiply_elementwise(t[i][3])
                layer.append((k,fac,v,A*v))
                return
            for i in range(j,len(t)):
                if t[i][0]>rem: break
                gen(rem-t[i][0],i,is_+[i])
        gen(k-1,0,[])
        t.extend(layer); sizes.append(len(layer))
    return t,sizes

def main():
    ap=ArgumentParser(description=__doc__)
    ap.add_argument("--emit",type=Path,help="optionally export regenerated literal JSON here")
    args=ap.parse_args()
    a=R(1,9)
    c=[0,R(1,7),a,2*a,R(123,220),R(3,4),R(1,4)]
    n0=len(c);A=S.zeros(n0,n0)
    A[1,0]=A[1,1]=c[1]/2
    for i,idx in [(2,[0,1,2]),(3,[0,2,3]),(4,[0,2,3,4]),(5,[0,3,4,5]),(6,[0,3,4,5,6])]:
        w=rowq([c[j] for j in idx],c[i])
        for j,z in zip(idx,w): A[i,j]=z
    assert A*S.ones(n0,1)==S.Matrix(c)
    assert (A*S.Matrix(c)-S.Matrix([z*z/2 for z in c]))==S.zeros(n0,1)
    clean=[0,3,4,5,6]
    Phi=[S.S(0)]*n0
    for i,f in zip(clean,interp([c[i] for i in clean])): Phi[i]=f
    def res(n,fac,v):
        return S.expand(R(n,fac)*x**(n-1)-sum(f*a for f,a in zip(Phi,v)))
    data,sizes=tree_enum(A,7)
    assert sizes==[1,1,2,4,9,20,48]
    assert all(res(*t[:3])==0 for t in data if t[0]<=5)
    def basis(polys):
        ps=sorted(set(polys),key=str)
        M=S.Matrix([[S.Poly(f,x).nth(i) for i in range(7)] for f in ps]).T
        return [ps[i] for i in M.rref()[1]]
    f5=basis([res(*t[:3]) for t in data if t[0]==6])
    f56=basis([res(*t[:3]) for t in data if t[0]>=6])
    print('F5 dim',len(f5),'F5+F6 dim',len(f56),flush=True)
    # cofactor on seven proper clocks: x=1 and x=0 are excluded.
    clocks=[S.S(1),R(2,3),R(1,3),R(11,12),R(1,2),R(1,12),R(1,4),R(3,4)]
    y=[1-z for z in clocks];n=len(y)
    ws=list(rowq([0]+clocks,S.S(1)))
    w0,w=ws[0],ws[1:]
    assert all(w) and w0
    assert all(sum(m*z**i for z,m in zip([0]+clocks,ws))==R(1,i+1) for i in range(10))
    gg=[S.S(0)]+[1/(m*z*S.prod(z-u for u in clocks[1:] if u!=z)) for z,m in zip(clocks[1:],w[1:])]
    g=[z*(y[1]**3/6)/gg[1] for z in gg]
    assert all(sum(wi*gi*xi**k for wi,gi,xi in zip(w,g,clocks))==0 for k in range(1,7))
    V=S.Matrix([[z**k for z in y] for k in range(4)]+[g])
    det=V[:,:5].det()
    print('first5 det=',det,flush=True)
    assert det!=0
    L=S.zeros(n,n)
    assert g[0]==0
    for j,v in enumerate((y[1]/2,y[1]/2)):
        L[1,j]=v
    for i in range(2,n):
        yy=y[i]
        init=[yy,yy**2/2,yy**3/3+g[i]]
        for j,z in enumerate(V[:3,:3].inv()*S.Matrix(init)): L[i,j]=z
    Y=S.Matrix(y);G=S.Matrix(g)
    for k in range(3):
        expect= [z**(k+1)/R(k+1)+(g[i] if k==2 else 0) for i,z in enumerate(y)]
        assert L*Y.applyfunc(lambda z:z**k)==S.Matrix(expect)
    H0=L*Y.applyfunc(lambda z:z**3)-Y.applyfunc(lambda z:z**4/4)
    K0=L*G
    test=lambda v:S.Matrix([sum(m*z*e(f,u) for m,z,u in zip(w,v,clocks)) for f in f5])
    jj=S.Matrix([sum(m*z*e(J(f),u) for m,z,u in zip(w,g,clocks)) for f in f5])
    # A one-tap correction at reflected row 4 and two each at rows 5,6.
    lifts=[]
    for i,m in [(3,4),(4,5),(5,5)]:
        for v in V[:3,:m].nullspace():
            M=S.zeros(n,n);M[i,:m]=v.T; lifts.append(M)
    C=S.Matrix.hstack(*(test(M*Y.applyfunc(lambda z:z**3)).col_join(test(M*G)) for M in lifts))
    target=(-test(H0)).col_join(jj-test(K0))
    print('top map ranks:',C.rank(),C.row_join(target).rank(),flush=True)
    assert C.rank()==C.cols==C.row_join(target).rank()==5
    solution=C.gauss_jordan_solve(target)[0]
    for i,M in enumerate(lifts): L+=solution[i]*M
    print('top corrections=',list(solution),flush=True)
    assert test(L*Y.applyfunc(lambda z:z**3)-Y.applyfunc(lambda z:z**4/4))==S.zeros(len(f5),1)
    assert test(L*G)==jj
    for k in range(3):
        expect= [z**(k+1)/R(k+1)+(g[i] if k==2 else 0) for i,z in enumerate(y)]
        assert L*Y.applyfunc(lambda z:z**k)==S.Matrix(expect)
    T=S.zeros(n,n)
    for i in range(n):
        for j in range(i+1):
            ii,jj=n-1-i,n-1-j
            T[i,j]=w[jj]*L[jj,ii]/w[ii]
    xs=clocks[::-1]
    D=S.zeros(n0+n,n0+n); D[:n0,:n0]=A;D[n0:,n0:]=T
    for i in range(n):
        for j,f in enumerate(Phi):
            D[n0+i,j]=e(J(f),xs[i])-sum(T[i,k]*e(f,xs[k]) for k in range(i+1))
    b=S.Matrix([w0]+[S.S(0)]*(n0-1)+w[::-1])
    assert b.rows==15 and D.rows==15
    assert D*S.ones(15,1)==S.Matrix(c+xs)
    assert all(D[i,j]==0 for i in range(15) for j in range(i+1,15))
    print('diagonal',list(D.diagonal()),flush=True)
    print('denominator',S.ilcm(*(z.q for z in list(D)+list(b))),flush=True)
    # Both first suffix rows equal existing whole old stage rows.
    assert D[7,7]==D[8,8]==0 and D[7,:]==D[5,:] and D[8,:]==D[6,:]
    assert all(e(f,q)==0 for f in f5 for q in [R(3,4),R(1,4)])
    keep=[i for i in range(15) if i not in [7,8]]
    for old,new in [(5,7),(6,8)]:
        D[:,old]+=D[:,new]; b[old]+=b[new]
    D=D.extract(keep,keep); b=b.extract(keep,[0])
    assert D*S.ones(13,1)==S.Matrix(c+xs[2:])
    print('merged diagonal',list(D.diagonal()),flush=True)
    print('merged denominator',S.ilcm(*(z.q for z in list(D)+list(b))),flush=True)
    t,sizes=tree_enum(D,10)
    fails=[(n,fac,v.dot(b)-1/R(fac)) for n,fac,v,_ in t if v.dot(b)!=1/R(fac)]
    print('fails=',len(fails),'first=',fails[:10],flush=True)
    assert not fails
    bush11=sum(z*u**10 for u,z in zip(c+xs[2:],b))-R(1,11)
    print('counts=',sizes,'bush11=',bush11,flush=True)
    assert bush11
    jdata=dict(schema='rational-lower-triangular-runge-kutta-tableau-v1',stages=13,order=10,
       A=[[str(D[i,j]) for j in range(i+1)] for i in range(13)],
       b=[str(z) for z in b], c=[str(z) for z in c+xs[2:]],eleventh_bush_defect=str(bush11))
    if args.emit:
        args.emit.write_text(json.dumps(jdata,indent=2)+'\n')

if __name__=='__main__':main()
