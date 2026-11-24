from itertools import combinations
p=15727
grid=[0,1069,1186,6796,7356,7876,8398,8920,9440,10000,15610]
count=0
fingerprint=1
for knots in combinations(grid,5):
    coeff=[1]
    for z in knots:
        coeff=[y-z*x for x,y in zip(coeff+[0],[0]+coeff)]
    for u in grid:
        if u in knots:continue
        m=[sum((2520//(j+k+1))*c*u**j for j,c in enumerate(coeff))%p for k in (1,2,3)]
        det=(m[0]*m[2]-m[1]**2)%p
        assert det!=0
        count+=1;fingerprint=fingerprint*det%p
assert (count,fingerprint)==(2772,3388)
print(f'{count} nonzero determinants; product = {fingerprint} mod {p}')
