from pathlib import Path
from math import prod
from importlib.util import spec_from_file_location,module_from_spec
import json
def load(name,path):
    spec=spec_from_file_location(name,path);z=module_from_spec(spec);spec.loader.exec_module(z);return z
HERE=Path(__file__).resolve().parent
G=load('geometry',HERE/'geometry.py')
S=load('chart',HERE/'chart.py')
class Local(S.F):
 def __init__(self,m):self.p=m
 def inv(self,x):
    assert x%17,('nonunit',x,self.p)
    return pow(x,-1,self.p)
 def integ(self,q):
    return sum(z*self.inv(i+1)for i,z in enumerate(q))%self.p
 def solve(self,A,b,n=None):
    M=[[z%self.p for z in row]+[y%self.p]for row,y in zip(A,b)]
    N=n or len(M[0])-1
    piv=[]
    for j in range(N):
        i=len(piv);k=next((k for k in range(i,len(M))if M[k][j]%17),None)
        if k is None:continue
        piv.append(j);M[i],M[k]=M[k],M[i];M[i]=self.scale(self.inv(M[i][j]),M[i])
        for k in range(i+1,len(M)):
            if M[k][j]:
                z=M[k][j];M[k][j:]=[(x-z*y)%self.p for x,y in zip(M[k][j:],M[i][j:])]
    if any(row[-1] for row in M[len(piv):]):return
    y=[0]*N
    for j,row in reversed(list(zip(piv,M))):
        y[j]=(row[-1]-self.dot(row[:-1],y))%self.p
    assert all(self.dot(r,y)==v%self.p for r,v in zip(A,b))
    return y,len(piv)
def det(M,m=17):
    rows=[[z%m for z in r]for r in M];p=1
    for i in range(len(rows)):
        k=next((k for k in range(i,len(rows))if rows[k][i]),None)
        if k is None:return 0
        if k!=i:p=-p;rows[i],rows[k]=rows[k],rows[i]
        z=rows[i][i];p=p*z%m
        t=pow(z,-1,m)
        for k in range(i+1,len(rows)):
            u=rows[k][i]*t%m
            rows[k]=[(a-u*b)%m for a,b in zip(rows[k],rows[i])]
    return p%m

def reconstruct(T,m):
    a,c,d,e,f,g=T;F=Local(m);I=F.inv;b=2*a%m
    eq,(mu,detDonor,Zpair,A1,B1)=G.system(T,m,True)
    assert eq==[0]*5
    W={z:mu[z]*I(prod(z-u for u in mu if z!=u))%m for z in mu}
    C=S.Chart(a,b,c,(d,e,f,g),W,mu,F)
    L=C.terminal((d,e,f,g));assert L is not None
    literal=C.forward((d,e,f,g),L)
    assert literal is not None
    guards={}
    if m==17:
        y=literal['reverse_y']
        w=list(reversed(literal['b'][5:]));x=[(1-z)%m for z in y]
        h=C.h+[C.hu[z]for z in (d,e,f,g)];u=C.u+[0]*4
        O=[[v*pow(xx,j,m)%m for v,xx in zip(w,x)]for j in range(5)]
        O += [[w0*z%m for w0,z in zip(w,p)]for p in (u,h,[yy*hh for yy,hh in zip(y,h)])]
        O +=[[int(i==j)for i in range(10)]for j in (9,8)]
        guards['observer_coordinate_determinant']=det(O)
        T1=[]
        FF=[(sum(row)%m)for row in literal['a']][5:]
        for j in range(2):
            taps=literal['a'][5+j][5:]
            T1.append([(F.dot(taps,[pow(z,k,m)for z in FF])-pow(FF[j],k+1,m)*I(k+1))%m for k in (1,2)])
        guards['first_two_kernel_determinant']=det(T1)
        guards['DE_extra_response_determinant']=detDonor
        guards['B_h_difference']=(C.h[4]-C.h[3])%m
        guards['first_six_read_determinant']=det(C.M)
        guards['first_five_read_determinant']=det([row[:5]for row in [q[:4]+[q[5]]for q in C.M[:5]]])
        assert all(guards.values()),guards
    return literal,guards
if __name__=='__main__':
    from sys import argv
    n=int(argv[1])if len(argv)>1 else 5
    out={}
    for k,T in sorted(json.loads(Path('geometry-lifts.json').read_text()).items(),key=lambda t:int(t[0])):
        i=int(k)
        if i>n:break
        m=17**i
        W,guards=reconstruct(T,m)
        assert all(len(row)==j for j,row in enumerate(W['a']))
        if i==1:
            old=json.loads((HERE.parent/'erk10-fifteen-f17'/'tableau.json').read_text())
            assert W['a']==old['A'] and W['b']==old['b'],(W,old)
            print('Jacobian pivot determinant',det([[row[j] for j in (0,1,3,4,5)]for row in G.jac(G.base,17)]))
            print('base unit guards',guards)
        else:
            old=out[str(i-1)];z=m//17
            assert [[x%z for x in r]for r in W['a']]==old['a']
            assert [y%z for y in W['b']]==old['b']
        # Independent rooted tree enumeration from the literal.
        got=S.actual(W)
        assert got and got[0]==((),)*10 and got[1]%17==8
        W['next_failure']=got
        out[k]=W
        print('strict actual tableau power',i,'modulus',m,'unit witness',got[1])
    Path('literal-geometry-lifts.json').write_text(json.dumps(out,indent=2)+'\n')
