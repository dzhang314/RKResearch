"""Exact source-guard factors, used only after complete characteristic-zero divide."""
from literal23_outer import oriented
from star4_guarded_fibers import modQ
from flint import fmpz_poly,fmpq_poly,nmod_poly
from pathlib import Path
from functools import lru_cache

@lru_cache(None)
def aux():
    J={}
    for l in Path('literal23-guard-proposals.txt').read_text().splitlines():
        k,e,*A=l.split();A=tuple(map(int,A));e=int(e)
        if A[-1]<0:A=tuple(-x for x in A)
        J.setdefault(A,[]).append((k,e))
    return [(fmpz_poly(list(A)),l) for A,l in J.items()]

@lru_cache(None)
def orient_mod(p,t):
    E=oriented(p,2*t%p)
    assert E
    h=next(i for i,v in enumerate(E) if v)
    return nmod_poly(E[h:],p)

def mono(P,p):
    return P*pow(int(P.leading_coefficient()),-1,p)

def proposal(t=2040,p=65537):
    U,V=map(lambda tt:orient_mod(p,tt),(t,p-t))
    assert U.degree()==V.degree()==6705
    R=mono(U*V,p);M=R;ans=[]
    for P,l in aux():
        E=fmpq_poly(P);E=E*(1/E[E.degree()])
        try:A=modQ(E,p)
        except (ValueError,ZeroDivisionError):continue
        m,e=R,0
        while m and not m%A:m//=A;e+=1
        h=A.gcd(R).degree()
        if h and not e:
            print('part-only guard norm proposal',P.degree(),l,h,flush=True)
        if e:
            print('full guard norm proposal',P.degree(),l,e,A.gcd(U).degree(),flush=True)
            ans.append((P,l,e,A.gcd(U).degree()))
            for _ in range(e):
                if M%A:break
                M=M//A
    Z=M.gcd(U)
    print('remaining norm quotient mod proposal',M.degree(),
          'aligned generic',Z.degree(),[(q.degree(),e) for q,e in Z.factor()[1]],flush=True)
    assert sorted((P.degree(),e,n) for P,l,e,n in ans)==[
        (2,130,1),(3,16,3),(5,6,5),(21,216,21),(22,3,11),(46,6,46)]
    assert M.degree()==8194 and Z.degree()==4097
    return ans

def main():
    Q=proposal()
    Path('literal23-cover-plan.txt').write_text('\n'.join(
        str(e)+' '+str(k)+' '+str(l)+' '+' '.join(map(str,M))
        for M,l,e,k in Q))

if __name__=='__main__':main()
