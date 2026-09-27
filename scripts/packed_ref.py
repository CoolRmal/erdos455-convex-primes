#!/usr/bin/env python3
"""Reference implementation of the packed (bit-parallel) max-plus value iteration.

This mirrors, operation by operation, the Lean definitions in `Erdos455/DP/Step.lean`; it is
used to cross-check them and to measure the work. It is not part of the proof.

A function on the units modulo `M = 3 R` is stored as two packed numbers `w1`, `w2` (the unit
classes modulo 3), each with `R` fields of `B` bits: field `t` of `wk` holds the value at the
residue `r` with `r = k (mod 3)`, `r = t (mod R)`.

usage: packed_ref.py phi.txt [steps] [K]
"""
import math
import sys

B = 9          # field width; bit B-1 is the guard bit
MARGIN = 16    # the least stored value on a unit after normalisation


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


def rot(x, k, R):
    return op(op(x << (B * k), R) | op(x >> (B * (R - k)), R), R)


def shift(k, x, R, C):
    return op(op(rot(x, k, R) + C[0], R) & C[2], R)


def pmax(a, x, R, C):
    t = op(op(a | C[1], R) - x, R)
    c = op(t & C[1], R)
    return op(x + op(t & op(c - op(c >> (B - 1), R), R), R), R)


def chain_max(k, n, x, acc, R, C):
    for _ in range(n):
        x = shift(k, x, R, C)
        acc = pmax(acc, x, R, C)
    return acc


def step_comps(i, w1, w2, R, C):
    k = 2 * i % R
    if i % 3 == 1:
        return pmax(w1, shift(k, w2, R, C), R, C), w2
    if i % 3 == 2:
        return w1, pmax(w2, shift(k, w1, R, C), R, C)
    L = run_bound(i)
    return chain_max(k, L, w1, w1, R, C), chain_max(k, L, w2, w2, R, C)


def fields(x, R):
    m = (1 << B) - 1
    return [(x >> (B * t)) & m for t in range(R)]


def unit_fields(x, R):
    return [v for t, v in enumerate(fields(x, R)) if math.gcd(t, R) == 1]


def crt(k, t, R):
    """The residue modulo 3 R that is k mod 3 and t mod R."""
    return (k * R * pow(R, -1, 3) + t * 3 * pow(3, -1, R)) % (3 * R)


def load_phi(path):
    with open(path) as f:
        z, M = map(int, f.readline().split())
        phi = {}
        for line in f:
            r, v = map(int, line.split())
            phi[r] = v
    assert M == modulus(z)
    return z, M, phi


def initial(phi, R):
    lo = min(phi.values())
    return [packed(R, lambda t, k=k: phi[crt(k, t, R)] - lo + MARGIN
                   if math.gcd(t, R) == 1 else 0) for k in (1, 2)]


def normalise(w1, w2, R, C):
    vals = unit_fields(w1, R) + unit_fields(w2, R)
    s = min(vals) - MARGIN
    w1, w2 = w1 - s * C[3], w2 - s * C[3]
    return w1, w2, s, max(fields(w1, R) + fields(w2, R))


def main():
    z, M, phi = load_phi(sys.argv[1])
    steps = int(sys.argv[2]) if len(sys.argv) > 2 else M - 1
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 32
    R = M // 3
    C = consts(R)
    w1, w2 = initial(phi, R)
    v1, v2 = w1, w2
    offset = 0
    bound = max(fields(w1, R) + fields(w2, R))
    for i in range(1, steps + 1):
        bound += run_bound(i)
        assert bound < 1 << (B - 1), i
        w1, w2 = step_comps(i, w1, w2, R, C)
        if i % K == 0:
            w1, w2, s, bound = normalise(w1, w2, R, C)
            offset += s
    lam = max(y - x + offset for (a, b) in ((v1, w1), (v2, w2))
              for x, y in zip(unit_fields(a, R), unit_fields(b, R)))
    print(f"z={z} steps={steps} offset={offset} LAMBDA={lam} ops={Counter.ops} "
          f"GB={Counter.bits / 8e9:.2f}")


if __name__ == "__main__":
    main()
