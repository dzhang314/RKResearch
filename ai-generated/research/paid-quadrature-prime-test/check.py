"""Exact degree-14 mean test on 13- and 14-site centered symmetric grids."""

from itertools import combinations


def check(den, pairs):
    total = retained = zero_means = 0
    for positive in combinations(range(1, 2 * den + 1), pairs):
        total += 1
        if sum(a*a for a in positive) % 13:
            continue
        retained += 1
        polynomial = [1]
        for a in positive:
            new = [0] * (len(polynomial) + 1)
            for j, coefficient in enumerate(polynomial):
                new[j] -= a*a * coefficient
                new[j+1] += den*den * coefficient
            polynomial = new
        # Coefficients in X=u², scaled by den**(2*pairs).
        if pairs == 6:
            polynomial.insert(0, 0)
        numerator = sum(
            c * (45045 // (2*j+1)) for j, c in enumerate(polynomial)
        )
        if numerator == 0:
            zero_means += 1
    return total, retained, zero_means


expected = {
    (6, 6): (924, 90, 0),
    (6, 7): (792, 60, 0),
    (9, 6): (18564, 1496, 0),
    (9, 7): (31824, 2513, 0),
    (12, 6): (134596, 10639, 0),
    (12, 7): (346104, 26863, 0),
}
for (den, pairs), answer in expected.items():
    observed = check(den, pairs)
    assert observed == answer
    print(den, 13 if pairs == 6 else 14, *observed)
