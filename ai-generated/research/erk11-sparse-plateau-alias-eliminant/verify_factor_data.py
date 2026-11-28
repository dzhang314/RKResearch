"""Independently match archived width factors to fresh modular resultants."""
from pathlib import Path
import json
import flint
from replay_erk11_sparse_plateau_alias import build, geometry

here = Path(__file__).resolve().parent
D, G, L, Z, b = build('d')
guards = list(map(geometry, [b[2][0]*b[-1][2], b[3][0]*b[-1][3],
                            L['dt'], Z['dt'], L['G'][1], Z['G'][1]]))
archive = here / 'optional-exact-factor-data'
pairs = [(G, archive/'exact-regular-width-factors-d.json')]
pairs.extend((m, archive/f'exact-guard-{i}-factors-d.json') for i,m in enumerate(guards))
for prime in (103, 107):
    A = flint.fmpz_mod_mpoly_ctx.get(('a','d'),prime)
    U = flint.fmpz_mod_poly_ctx(prime)

    def reduce2(poly):
        return A.from_dict({ij: int(c.numerator)*pow(int(c.denominator),-1,prime)%prime
                            for ij,c in poly.to_dict().items()})

    reduced_d = reduce2(D)
    for i,(mask,path) in enumerate(pairs):
        actual_bivariate = reduced_d.resultant(reduce2(mask),'d')
        actual_dict = actual_bivariate.to_dict()
        assert actual_dict and all(d == 0 for _, d in actual_dict)
        actual = U([int(actual_dict.get((j,0),0))
                    for j in range(1+max(a for a,d in actual_dict))])
        product = U([1])
        for coefficients,power in json.loads(path.read_text()):
            factor = U([int(c)%prime for c in coefficients])
            assert factor.degree() == len(coefficients)-1
            product *= factor**power
        assert actual.degree() == product.degree()
        assert actual*product.leading_coefficient() == product*actual.leading_coefficient()
        print("Match", prime, "regular" if i == 0 else f"mask {i}", actual.degree(),flush=True)
