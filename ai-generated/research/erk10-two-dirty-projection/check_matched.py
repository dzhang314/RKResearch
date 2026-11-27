#!/usr/bin/env python3
"""First two clean primitive and first dirty literal anchor, finite matched mesh."""
from itertools import permutations,combinations
from pathlib import Path
from hashlib import md5
import sys
p=227
nodes=(51,24,204,177)
def inv(x):return pow(x%p,-1,p)
def mul(x,y):
    z=[0]*(len(x)+len(y)-1)
    for i,u in enumerate(x):
        for j,v in enumerate(y):z[i+j]=(z[i+j]+u*v)%p
    return z
def val(f,x):return sum(u*pow(x,j,p)for j,u in enumerate(f))%p
def Int(f):return [0]+[u*inv(j+1)%p for j,u in enumerate(f)]
def summ(*terms):
    d=max(len(f)for a,f in terms)
    return [sum(a*f[i]for a,f in terms if i<len(f))%p for i in range(d)]
def mk(a,b,r,s,x,y):
    S=[a,b,r,s];co=[]
    for k in S:
        L=[0,1]
        for v in S:
            if v!=k:L=mul(L,[-v,1])
        z=inv(val(L,k));co.append([z*t%p for t in L])
    A,B,R,Sx=[val(Int(L),x)for L in co]
    C,D,T,U=[val(Int(L),y)for L in co]
    assert all([A,B,R,Sx,C,D,T,U])
    V=[A*(b-r)%p,-B*(a-r)%p]
    W=[A*(b-s)%p,-B*(a-s)%p]
    H=Int(mul(mul([0,1],[-r,1]),[-s,1]))
    F=summ((val(H,a),mul(V,W)),((b-r)*R*val(H,r),W),((b-s)*Sx*val(H,s),V))
    if x==a:
        G=summ((T*inv((b-r)*R),V),(-U*inv((b-s)*Sx),W),
            (D*((a-r)*inv(b-r)-(a-s)*inv(b-s)),[0,1]))
    elif x==b:
        G=summ((T*inv((a-r)*R),V),(-U*inv((a-s)*Sx),W),
            (-C*((b-r)*inv(a-r)-(b-s)*inv(a-s)),[1,0]))
    elif x==r:
        G=summ((U,W),(-Sx,[C*(b-s),-D*(a-s)]))
    else:
        assert x==s
        G=summ((T,V),(-R,[C*(b-r),-D*(a-r)]))
    g0,g1=G
    f0,f1,f2=F
    result=(f0*g1*g1-f1*g0*g1+f2*g0*g0)%p
    return F,G,result
def verify_source(source):
    raw=source.read_bytes()
    assert md5(raw).hexdigest()=='be9e5e3ba1ff8ed21124ad285d7d2fd5'
    x,y,z=177,190,149
    assert (x*x-3)%p==0 and (y*y-7)%p==0 and (z*z-147-42*y)%p==0
    def decode(line):
        a,b,c,d,e,f,g,h,q=map(int,line.split())
        return (63*a+63*b*x+63*c*y+63*d*x*y+3*e*z+(-2*f+7*h)*x*z+
                3*g*y*z+(f-2*h)*x*y*z)*inv(63*q)%p
    clocks=[decode(line)for line in raw.splitlines()[:15]]
    assert tuple(clocks[i]for i in (8,10,6,7))==nodes
    assert len(set(nodes+(0,1)))==6
def all_predecessor():
    for x in nodes:
        for j in range(4):
            for S in combinations(nodes,j):
                h=[0,1]
                for y in S:h=mul(h,[-y,1])
                yield val(Int(h),x)
def all_successor():
    for x in nodes:
        for j in range(3):
            for S in combinations([y for y in nodes if y!=x],j):
                h=[-1,1]
                for y in S:h=mul(h,[-y,1])
                H=Int(h)
                yield (val(H,1)-val(H,x))%p
def emit(path,rows,pre,suc):
    with path.open('w')as f:
        f.write("""/- Independent finite field audit of the Lobatto interface. -/
namespace RKResearch.Core.ERK10TwoDirtyMatched

def modulus : Nat := 227
def elimination (f0 f1 f2 g0 g1 : Nat) : Nat :=
  (f0*g1*g1 + modulus^4 - f1*g0*g1 + f2*g0*g0) % modulus

def coefficients : List (Nat × Nat × Nat × Nat × Nat) := [\n""")
        f.write(',\n'.join('  ('+', '.join(map(str,r))+')'for r in rows))
        f.write(']\n\n')
        for k,t in [('predecessors',pre),('successors',suc)]:
            f.write('def '+k+' : List Nat := '+str(t)+'\n')
        f.write("""
theorem matched_eliminations :
    coefficients.length = 288 ∧
      (coefficients.all fun (f0,f1,f2,g0,g1) => elimination f0 f1 f2 g0 g1 != 0) = true := by
  decide +kernel

theorem support_hulls :
    predecessors.length = 60 ∧ successors.length = 28 ∧
      (predecessors.all (· != 0)) = true ∧ (successors.all (· != 0)) = true := by
  decide +kernel

end RKResearch.Core.ERK10TwoDirtyMatched
""")
def main():
    import argparse
    pa=argparse.ArgumentParser()
    pa.add_argument('--source',type=Path,default=Path(__file__).parent.parent/'erk10-stepanov-five-opening'/'stepanov15-source.txt')
    pa.add_argument('--emit-lean',type=Path)
    args=pa.parse_args()
    verify_source(args.source)
    pre,suc=list(all_predecessor()),list(all_successor())
    assert len(pre)==60 and len(suc)==28 and all(pre) and all(suc)
    rows=[]
    counts={};fail=[]
    for a,b,r,s in permutations(nodes):
        for x,y in permutations(nodes,2):
            F,G,R=mk(a,b,r,s,x,y)
            rows.append(tuple(F+G))
            if not R:
                fail.append((a,b,r,s,x,y,F,G))
            counts[R]=counts.get(R,0)+1
    print('total',sum(counts.values()),'zeros',counts.get(0,0),'distinct',len(counts))
    print("support hulls",len(pre),len(suc),"all nonzero")
    assert not fail,fail
    if args.emit_lean:emit(args.emit_lean,rows,pre,suc)
if __name__=='__main__': main()
