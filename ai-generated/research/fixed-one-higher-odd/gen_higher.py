"""Generate exact symbolic fixed-one strict SDIRK certificates through order 19.

Usage: python3 gen_higher.py PATH/TO/tableau-13.json --out DIRECTORY [--through 15|17|19].
Uses exact rational arithmetic (SymPy); no rooted-tree enumeration and no proof trust
is placed in the generator. Lean checks the emitted finite matrix receipts itself.
"""
from __future__ import annotations
import argparse, json, math, sys, time
from pathlib import Path
import sympy as S

R=S.Rational; Mat=S.Matrix; x=S.Symbol('x')
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

def integ(f): return sum(a/(k+1) for (k,),a in S.Poly(f,x).terms())
def at(f,z): return S.Poly(f,x).eval(z)
def polcoeffs(f,q):
    P=S.Poly(f,x);return [P.nth(i) for i in range(q+1)]
def arr(items): return '#['+', '.join(map(str,items))+']'
def qexpr(y):
    y=R(y);return str(y.p) if y.q==1 else f'({y.p} / {y.q} : ℚ)'
def matrixDef(name,M):
    lines=',\n  '.join(arr([qexpr(y) for y in M.row(i)]) for i in range(M.rows))
    return f'def raw{name} : Array (Array ℚ) := #[\n  {lines}\n]\n'+(
        f'def {name} : Matrix (Fin {M.rows}) (Fin {M.cols}) ℚ := fun i j => (raw{name}[i.val]!)[j.val]!\n')
def vecDef(name,v):
    return f'def raw{name} : Array ℚ := {arr([qexpr(y) for y in v])}\n'+(
        f'def {name} (i : Fin {len(v)}) : ℚ := raw{name}[i.val]!\n')
def data(A,b,p,defect):
    d=math.lcm(*(int(y.q) for y in A));e=math.lcm(*(int(y.q) for y in b))
    return dict(order=p,stages=A.rows,common_diagonal="1",a_denominator=d,b_denominator=e,
                a_integer=[[int(d*y) for y in A.row(i)] for i in range(A.rows)],
                b_integer=[int(e*y) for y in b],next_bush_defect=str(defect))
def stage(old,w0,p,donors,out):
    n0=old.rows; q=(p-1)//2; m=2*q; r=len(donors); protected=q-r
    c0=old*S.ones(n0,1); bankTimes=[c0[j] for j in donors]
    assert protected>=3 and len(set(bankTimes))==r and bankTimes[0]<0 and bankTimes[1]<0
    pins=[R(2-2*i) for i in reversed(range(1,q+1))]
    head=bankTimes+[-R(100*p+2*j+1) for j in range(protected-1)]
    F0=S.prod(x-z for z in head+pins)
    z=integ(x*F0)/integ(F0); cs=head+[z]+pins
    assert len(set(cs))==m
    F=F0*(x-z); fp=S.diff(F,x)
    w=[integ(S.div(F,x-c,x)[0])/at(fp,c) for c in cs]
    Q=Mat([[a*c**i for a,c in zip(w,cs)] for i in range(q+1)])
    assert all(w) and all(sum(a*c**j for a,c in zip(w,cs))==R(1,j+1) for j in range(p))
    defect=(p+1)*sum(a*c**p for a,c in zip(w,cs))-1
    assert defect
    P=[S.Integer(1)]
    for v in reversed(cs): P.append(S.expand(P[-1]*(x-v)))
    L=Mat([[a*at(f,c) for a,c in zip(w,cs)] for f in P])
    T=S.zeros(m)
    for j in range(m):
        piv=list(range(max(q,j+1),m)); n=len(piv)
        if n:
            v=L.extract(range(n),piv).inv()*Mat([-L[i+1,j]/(i+1) for i in range(n)])
            for i,k in enumerate(piv): T[k,j]=v[i]
    assert all(L[j,:]*T==-L[j+1,:]/(j+1) for j in range(q))
    B=T+S.eye(m)
    C=Mat([polcoeffs(f,q-1) for f in P[:q]])
    GP=Mat([polcoeffs(P[j]-P[j+1]/(j+1),q) for j in range(q)])
    G=C.inv()*GP
    H=Mat([[R(int(k==0)-int(k==j+1),j+1)-G[j,k] for k in range(q+1)] for j in range(q)])
    assert all(G[j,k]==0 for j in range(q) for k in range(j+2,q+1))
    assert all(H[j,k]==0 for j in range(q) for k in range(j,q+1))
    assert Q[:q,:]*B==G*Q
    for j in range(q):
        for n in range(q+1,2*q-j+1):
            assert n*sum((G[j,k]+H[j,k])*R(1,n+k) for k in range(q+1))==R(1,n+j+1)
    mom=Mat([[w0[j]*c0[j]**i for j in range(n0)] for i in range(q+1)])
    O=mom[:q-1,:].col_join(Mat([[int(j==k) for j in range(n0)] for k in donors[:2]]))
    pred=Mat([[old[i,j]-int(i==j) for j in range(n0)]for i in donors])
    K=O.col_join(pred)
    mixed=Mat([[R(1,i+j+1) for j in range(q+1)] for i in range(q-1)]
               +[[v**j for j in range(q+1)]for v in bankTimes[:2]])
    inv=mixed.inv()
    J=lambda c:[c**(j+1)/(j+1)-c**j for j in range(q+1)]
    response=mixed.col_join(Mat([J(c) for c in bankTimes]))
    V=S.zeros(q,q+1+r)
    for i in range(r):V[i,q+1+i]=1
    for i in range(r,q):V[i,:q+1]=Mat([J(cs[i])])*inv
    C0=(C*H).row_join(S.zeros(q,r))
    CF=V.col_join(L[:q,q:].inv() * (C0-L[:q,:q]*V))
    U=CF*K
    E=Mat([[v**k for k in range(q+1)]for v in cs])
    I=Mat([[v**(k+1)/(k+1) for k in range(q+1)]for v in cs])
    feedCheck=CF*response+B*E
    assert feedCheck[:,:q]==I[:,:q]
    assert feedCheck[r:q,:]==I[r:q,:] and CF[r:q,q+1:]==S.zeros(protected,r)
    assert Q[:q,:]*U==H*mom
    A=old.row_join(S.zeros(n0,m)).col_join(U.row_join(B)); b=S.zeros(n0,1).col_join(Mat(w))
    for i in reversed(range(r)):
        j=n0+i;k=donors[i]
        duplicate=A.row(j).copy();original=A.row(k).copy()
        duplicate[j]-=1;original[k]-=1
        assert duplicate==original
        A[:,k]+=A[:,j];b[k]+=b[j];A.row_del(j);A.col_del(j);b.row_del(j)
    assert A.rows==n0+m-r and all(A[i,i]==1 and not any(A[i,j] for j in range(i+1,A.rows)) for i in range(A.rows))
    assert (A*S.ones(A.rows,1))[n0:n0+protected]==cs[r:q]
    dat=data(A,b,p,defect)
    (out/f'tableau-{p}.json').write_text(json.dumps(dat,indent=1)+'\n')
    src=f'''module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Matrix.Mul

@[expose] public section
namespace RKResearch.Certified.Stage{p}Data
'''
    for name,v in [('blockU',U),('blockB',B),('G',G),('H',H),('feedCoeffs',CF),('mixInv',inv)]:
        src+=matrixDef(name,v)
    for name,v in [('weights',w),('site',cs)]:
        src+=vecDef(name,v)
    src+=f'end RKResearch.Certified.Stage{p}Data\n'
    (out/f'Stage{p}Data.lean').write_text(src)
    tex=Path(__file__).with_name('Stage.lean.in').read_text()
    prevModule='Seed13Fast' if p==15 else f'Stage{p-2}'
    prevNS='FixedOneSeed13' if p==15 else f'FixedOneOrder{p-2}'
    for key,zv in dict(P=p,Q=q,OLD=n0,COPIES=r,PREV_MODULE=prevModule,PREV_NS=prevNS).items():
        tex=tex.replace('@'+key+'@',str(zv))
    (out/f'Stage{p}.lean').write_text(tex)
    print(f'order {p}, {A.rows} physical stages, {n0+m} virtual, {r} actual copied rows; next-bush defect sign {S.sign(defect)}',flush=True)
    return A,b,list(range(n0,n0+protected))

def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('seed13',type=Path);cli.add_argument('--out',type=Path,default=Path('.'))
    cli.add_argument('--through',type=int,default=19,choices=[15,17,19]);args=cli.parse_args()
    t=json.loads(args.seed13.read_text())
    if t['stages']!=35 or t['order']!=13 or t['common_diagonal']!='1':
        raise ValueError("expected the frozen order-thirteen physical matrix")
    A=Mat(t['a_integer'])/t['a_denominator']; b=Mat(t['b_integer'])/t['b_denominator']
    donors=[26,27,28];args.out.mkdir(parents=True,exist_ok=True)
    for p in range(15,args.through+1,2):
        st=time.monotonic()
        A,b,donors=stage(A,b,p,donors,args.out)
        print(f'  new physical bank {donors}; exact arithmetic time {time.monotonic()-st:.2f}s',flush=True)
if __name__=='__main__':main()
