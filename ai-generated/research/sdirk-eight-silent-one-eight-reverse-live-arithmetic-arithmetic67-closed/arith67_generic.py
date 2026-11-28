"""Complete true oriented finite components of the exact quotient."""
from arith67_cover import oriented_mod
from arith67_fibers import all_mod
from flint import nmod_poly
from sympy import isprime
import gzip,sys
sys.set_int_max_str_digits(0)

def main():
    p,t=65537,2040
    assert isprime(p) and (2*t*t-1)%p==0
    with gzip.open('arith67-quotient.gz','rt',encoding='utf-8') as f:
        M=nmod_poly([int(x)%p for x in f],p)
    assert M.degree()==7038
    U=oriented_mod(p,t)
    assert U.degree()==6843
    V=M.gcd(U);assert V.degree()==3519 and V.leading_coefficient()==1
    C=all_mod(V,p,t)
    assert C==23
    print('arith67 whole exact generic quotient has no actual fourth in all',C,'cases',flush=True)
if __name__=='__main__':main()
