"""Independent, dependency-free integer replay of the new strict SDIRK tableau."""
from fractions import Fraction as F
from functools import cache
import json
from math import gcd, prod
from pathlib import Path

@cache
def size(tree):
    """A tree is the tuple of its immediate subtrees; the leaf is ()."""
    return 1 + sum(size(child) for child in tree)

@cache
def tree_factorial(tree):
    return size(tree) * prod(tree_factorial(child) for child in tree)

def trees_by_size(limit):
    layers = [[()]]
    for k in range(2, limit + 1):
        older = [t for layer in layers for t in layer]

        def branches(start, size_left):
            if not size_left:
                yield ()
                return
            for j in range(start, len(older)):
                t = older[j]
                if size(t) > size_left:
                    break
                for rest in branches(j, size_left - size(t)):
                    yield (t,) + rest

        layers.append(list(branches(0, k - 1)))
    return layers

def check(data):
    d, e, A, b = (data[key] for key in ('stage_den', 'weight_den', 'A', 'b'))
    assert len(A) == len(b) == 10
    assert all(len(row) == 10 for row in A)
    z = data['z']
    assert all(z * row[i] == d and not any(row[i+1:]) for i, row in enumerate(A))
    if z == 5:
        assert d == 2**2 * 3**4 * 5**3 * 7 * 11**2 * 23 * 53 * 317
        assert e == 2**7 * 3**4 * 7**2
    elif z == 4:
        assert d == 2**7 * 3**4 * 5 * 7**2 * 31 * 37
        assert e == 2 * 3**4 * 5 * 7**2
    else:
        raise AssertionError(z)
    assert d**4 % e == 0
    assert all(z * sum(row) == d * c for row, c in
               zip(A, [1, 2, 0] + data['normalized_tail_clocks']))

    @cache
    def stage(t):
        v = (1,) * 10
        for child in t:
            u = stage(child)
            v = tuple(x * sum(a*y for a, y in zip(row, u)) for x, row in zip(v, A))
        return v

    def payment(t):
        return tree_factorial(t) * sum(w*v for w, v in zip(b, stage(t)))

    layers = trees_by_size(8)
    assert list(map(len, layers)) == [1, 1, 2, 4, 9, 20, 48, 115]
    assert all(payment(t) == e * d**(size(t)-1) for layer in layers[:7] for t in layer)
    bush, tall = ((),) * 7, ()
    for _ in range(7):
        tall = (tall,)
    expected = e * d**7
    bush_value = F(payment(bush), expected)
    tall_value = F(payment(tall), expected)
    assert str(bush_value) == data['next_bush_payment']
    assert str(tall_value) == data['next_tall_payment']
    assert bush_value != 1
    assert gcd((bush_value - 1).numerator, (tall_value - 1).numerator) == 1
    print(f'z={z}: 85/85 rooted conditions through seven; eighth bush {bush_value}, tall {tall_value}')

if __name__ == '__main__':
    names = ('ten-stage-rational.json', 'ten-stage-rational-alt.json')
    data = [json.loads(Path(__file__).with_name(name).read_text()) for name in names]
    for d in data:
        check(d)
    assert gcd(*(d['stage_den'] for d in data)) == 11340
    assert 5040**2 % 11340 == 0
    assert 196151 * data[0]['stage_den'] - 892416183 * data[1]['stage_den'] == 11340
    assert -1812613994 * 61 + 15 * 7371296909 == 1
    print('Coprime-after-localization denominator certificate checked.')
