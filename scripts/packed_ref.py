#!/usr/bin/env python3
"""Reference implementation of the packed (bit-parallel) max-plus value iteration.

This mirrors, operation by operation, the Lean definitions in `Erdos455/DP/Step.lean`; it is
used to cross-check them and to measure the work. It is not part of the proof.

A function on the units modulo `M = 15 R` is stored as eight packed numbers, one for each unit
class modulo 15: `w[k][c]` (`k` = the class modulo 3, `c` = the class modulo 5) has `R` fields of
`B` bits, field `t` holding the value at the residue `r = k (mod 3)`, `c (mod 5)`, `t (mod R)`.

usage: packed_ref.py phi.txt [steps] [K]      (phi.txt as written by gen_phi.c, z >= 5)
"""
import math
import sys

B = 9          # field width; bit B-1 is the guard bit
MARGIN = 16    # the least stored value on a unit after normalisation
CLASSES = (1, 2, 3, 4)


def modulus(z):
    return math.prod(p for p in [3, 5, 7, 11, 13, 17] if p <= z)


def packed(R, f):
    x = 0
    for t in reversed(range(R)):
        x = (x << B) | f(t)
    return x


def consts(R):
    """ones, highs, umask, uones, uhighs"""
    ones = packed(R, lambda t: 1)
    umask = packed(R, lambda t: (1 << B) - 1 if math.gcd(t, R) == 1 else 0)
    uones = packed(R, lambda t: 1 if math.gcd(t, R) == 1 else 0)
    return ones, ones << (B - 1), umask, uones, uones << (B - 1)


def run_bound(i):
    for p in [3, 5, 7, 11, 13]:
        if i % p:
            return p - 2
    return 15


class Counter:
    ops = 0
    bits = 0


def op(v, R):
    Counter.ops += 1
    Counter.bits += R * B
    return v


def shift(k, x, R, C):
    rot = op(op(x << (B * k), R) | op(x >> (B * (R - k)), R), R)
    return op(op(rot + C[0], R) & C[2], R)


def pmax(a, x, R, C):
    t = op(op(a | C[1], R) - x, R)
    c = op(t & C[1], R)
    return op(x + op(t & op(c - op(c >> (B - 1), R), R), R), R)


def src5(delta, c):
    return (c + 5 - delta) % 5


def transfer(delta, k, src, dst, R, C):
    return {c: pmax(dst[c], shift(k, src[src5(delta, c)], R, C), R, C)
            if src5(delta, c) != 0 else dst[c] for c in CLASSES}


def chains(delta, k, n, w, R, C):
    X, alive, acc = dict(w), {c: True for c in CLASSES}, dict(w)
    for _ in range(n):
        alive = {c: src5(delta, c) != 0 and alive[src5(delta, c)] for c in CLASSES}
        X = {c: shift(k, X[src5(delta, c)], R, C) if alive[c] else 0 for c in CLASSES}
        acc = {c: pmax(acc[c], X[c], R, C) if alive[c] else acc[c] for c in CLASSES}
    return acc


def step_comps(i, w1, w2, R, C):
    k, delta = 2 * i % R, 2 * i % 5
    if i % 3 == 1:
        return transfer(delta, k, w2, w1, R, C), w2
    if i % 3 == 2:
        return w1, transfer(delta, k, w1, w2, R, C)
    L = run_bound(i)
    return chains(delta, k, L, w1, R, C), chains(delta, k, L, w2, R, C)


def fields(x, R):
    m = (1 << B) - 1
    return [(x >> (B * t)) & m for t in range(R)]


def unit_fields(x, R):
    return [v for t, v in enumerate(fields(x, R)) if math.gcd(t, R) == 1]


def crt(k, c, t, R):
    """The residue modulo 15 R that is k mod 3, c mod 5 and t mod R."""
    return next(r for r in range(t, 15 * R, R) if r % 3 == k and r % 5 == c)


def load_phi(path):
    with open(path) as f:
        z, M = map(int, f.readline().split())
        phi = {}
        for line in f:
            r, v = map(int, line.split())
            phi[r] = v
    assert M == modulus(z) and M % 15 == 0
    return z, M, phi


def initial(phi, R):
    lo = min(phi.values())
    return [{c: packed(R, lambda t, k=k, c=c: phi[crt(k, c, t, R)] - lo + MARGIN
                       if math.gcd(t, R) == 1 else 0) for c in CLASSES} for k in (1, 2)]


def main():
    z, M, phi = load_phi(sys.argv[1])
    steps = int(sys.argv[2]) if len(sys.argv) > 2 else M - 1
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 32
    R = M // 15
    C = consts(R)
    w1, w2 = initial(phi, R)
    v1, v2 = dict(w1), dict(w2)
    offset = 0
    bound = max(max(fields(x, R)) for w in (w1, w2) for x in w.values())
    for i in range(1, steps + 1):
        bound += run_bound(i)
        assert bound < 1 << (B - 1), i
        w1, w2 = step_comps(i, w1, w2, R, C)
        if i % K == 0:
            vals = [v for w in (w1, w2) for x in w.values() for v in unit_fields(x, R)]
            s = min(vals) - MARGIN
            w1 = {c: x - s * C[3] for c, x in w1.items()}
            w2 = {c: x - s * C[3] for c, x in w2.items()}
            offset += s
            bound = max(max(fields(x, R)) for w in (w1, w2) for x in w.values())
    lam = max(y - x + offset for (a, b) in ((v1, w1), (v2, w2)) for c in CLASSES
              for x, y in zip(unit_fields(a[c], R), unit_fields(b[c], R)))
    print(f"z={z} steps={steps} offset={offset} LAMBDA={lam} ops={Counter.ops} "
          f"GB={Counter.bits / 8e9:.2f}")


if __name__ == "__main__":
    main()
