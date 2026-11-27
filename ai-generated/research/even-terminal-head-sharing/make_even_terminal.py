"""Specialize the already checked even terminal proof at orders 16, 18, 20."""
from pathlib import Path
import sys,re
p=int(sys.argv[1]);base=Path(sys.argv[2]);out=Path(sys.argv[3]);s=(base/'ProofEven14.lean').read_text()
old=p-2;m=p//2; q=m-1;k=p-1
n,N={16:(41,49),18:(52,61),20:(65,75)}[p]
s=s.replace('EvenTerminal14',f'EvenTerminal{p}').replace('Even14Data',f'Even{p}Data').replace('EvenPrep12',f'EvenPrep{old}')
vs={6:q,7:m,8:m+1,13:k,12:old,14:p,15:p+1,31:n,38:N,44:n+k}
s=re.sub(r'(?<![\w])(?:6|7|8|12|13|14|15|31|38|44)(?![\w])',lambda t:str(vs[int(t[0])]),s)
(out/f'ProofEven{p}.lean').write_text(s)
