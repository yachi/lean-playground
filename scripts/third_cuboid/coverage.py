"""Exact proportion of triples (a, b, c) modulo 13 · 17 · ... · 79 on which `checkB certTables`
succeeds (`ThirdConjectureMulti.lean`). Needs python-flint.

The check intersects, over the primes, the subset sums of the degree pattern modulo p of the
class of (a, b, c) mod p (all of 0..12 for classes not in the table); by the Chinese remainder
theorem the classes modulo different primes are independent, so the proportion is computed from
the distribution of the subset-sum sets for each prime.
"""
import itertools, collections
from fractions import Fraction
from gen_tables import table, norm_key, sums

PRIMES = [13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
FULL = frozenset(range(13))

def distribution(p):
    tab = {k: frozenset(sums(d)) for k, _, d, _ in table(p)}
    cnt = collections.Counter()
    for a, b, c in itertools.product(range(p), repeat=3):
        cnt[tab.get(norm_key(p, a*a % p, b*b % p, c*c % p), FULL)] += 1
    return {m: Fraction(v, p**3) for m, v in cnt.items()}

if __name__ == "__main__":
    dist = {FULL: Fraction(1)}
    for p in PRIMES:
        new = collections.Counter()
        for m, c in dist.items():
            for m2, c2 in distribution(p).items():
                new[m & m2] += c * c2
        dist = new
        print(f"up to {p}: {float(dist.get(frozenset({0, 12}), 0)):.6f}")
