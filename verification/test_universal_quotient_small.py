#!/usr/bin/env python3
"""Exhaustive finite-model tests for the universal cyclic quotient lemma.

This is not a formal proof.  It enumerates every 2- through 5-point set V
containing (0,0) inside {0,1,2}^2, takes W=V-V, enumerates every linear map
to the first prime p>max(2B,|V-V|), and verifies the collision average and all
modular-to-integer conclusions for a map with below-average collisions.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations, product


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def next_prime(n: int) -> int:
    p = n + 1
    while not is_prime(p):
        p += 1
    return p


def add(u, v):
    return tuple(a + b for a, b in zip(u, v))


def sub(u, v):
    return tuple(a - b for a, b in zip(u, v))


def dot(c, v, p):
    return sum(a * b for a, b in zip(c, v)) % p


def collision_count(images: list[int]) -> int:
    counts = {}
    for z in images:
        counts[z] = counts.get(z, 0) + 1
    return sum(t * (t - 1) // 2 for t in counts.values())


def audit(V):
    V = tuple(sorted(V))
    W = tuple(sorted({sub(a, b) for a in V for b in V}))
    B = max(abs(x) for w in W for x in w)
    p = next_prime(max(2 * B, len(W)))
    coeffs = list(product(range(p), repeat=2))

    collisions = []
    for c in coeffs:
        collisions.append(collision_count([dot(c, w, p) for w in W]))
    average = Fraction(sum(collisions), len(collisions))
    expected = Fraction(len(W) * (len(W) - 1), 2 * p)
    assert average == expected

    best_index = min(range(len(coeffs)), key=lambda i: (collisions[i], coeffs[i]))
    c = coeffs[best_index]
    assert collisions[best_index] < Fraction(len(W), 2)
    image_W = {dot(c, w, p) for w in W}
    assert len(image_W) > Fraction(len(W), 2)

    image_V = {dot(c, v, p) for v in V}
    nonzero = min(r for r in image_V if r != 0)
    scale = (-pow(nonzero, -1, p)) % p
    image_V = {(scale * r) % p for r in image_V}
    image_W = {(scale * r) % p for r in image_W}
    A = sorted(image_V)
    assert A[0] == 0 and A[-1] == p - 1

    sums = {a + b for a in A for b in A}
    diffs = {a - b for a in A for b in A}
    Vsum = {add(a, b) for a in V for b in V}
    Vdiff = set(W)
    assert len(sums) <= 2 * len(Vsum)
    assert len(diffs) >= len(image_W) > Fraction(len(W), 2)
    assert len(diffs) <= 2 * len(Vdiff) - 1 < 2 * p - 1


def main():
    origin = (0, 0)
    others = [v for v in product(range(3), repeat=2) if v != origin]
    count = 0
    for size in range(2, 6):
        for choice in combinations(others, size - 1):
            audit((origin,) + choice)
            count += 1
    print(f"EXHAUSTIVE UNIVERSAL-QUOTIENT MODELS: PASS ({count} sets)")


if __name__ == "__main__":
    main()
