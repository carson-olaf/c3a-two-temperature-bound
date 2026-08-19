#!/usr/bin/env python3
"""Exact verifier for a two-temperature cyclic-quotient bound on C_3a.

The human theorem proved in the accompanying note is:

Let M be a finite subset of nonnegative integers containing 0 and a positive
integer.  Put S=M+M, D=M-M, and

    kappa(d) = min(a+b : a,b in M and a-b=d).

For x,y in (0,1), define

    Pminus(x) = sum_{d in D} x^kappa(d),
    mu(x)     = sum_d kappa(d)x^kappa(d) / Pminus(x),
    rho(x)    = log Pminus(x) - mu(x) log x,

    Pplus(y)  = sum_{s in S} y^s,
    sigma(x,y)= log Pplus(y) - mu(x) log y.

If a rational rate R>1 satisfies rho < log R, then a cyclic-quotient
construction gives

    C_3a >= 1 + (rho-sigma)/log R.

This program reconstructs every finite combinatorial object from the two
semigroup generators 4 and 5 and proves, using only exact integer/rational
arithmetic and rigorously bounded rational series for logarithms, that the
hypotheses hold for

    M = <4,5> intersect [0,80],
    x = 8149/10000,
    y = 42571/50000,
    R = 249293/10000,

and that the resulting finite GHR seed has exponent strictly greater than
1.21418.

The code machine-checks the discrete reconstruction, all transcendental
inequalities through rational enclosures, and the finite-size correction.
It does not formally verify the general two-temperature quotient theorem or
the Gyarmati-Hennecart-Ruzsa lemma; those remain written mathematical arguments.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

GENERATORS = (4, 5)
B = 80
DEGREE = 2 * B

X_NUM, X_DEN = 8149, 10000
Y_NUM, Y_DEN = 42571, 50000
RATE_NUM, RATE_DEN = 249293, 10000

TARGET_THETA = Fraction(60709, 50000)  # 1.21418
TARGET_ALPHA = TARGET_THETA - 1       # 0.21418

EXPECTED_GAPS = (1, 2, 3, 6, 7, 11)
EXPECTED_MASK_SIZE = 75
EXPECTED_SUM_SIZE = 155
EXPECTED_DIFF_SIZE = 161
EXPECTED_KAPPA = {
    0: 0,
    1: 9,
    2: 18,
    3: 13,
    4: 4,
    5: 5,
    6: 14,
    7: 17,
    8: 8,
    9: 9,
    10: 10,
    11: 19,
    12: 12,
}

LOG_TERMS = 120

# Tight rational enclosures checked directly against the exact polynomial
# numerators.  Using these short rationals keeps the logarithm verifier fast;
# no decimal is trusted without the preceding exact cross-multiplication.
PMINUS_LO = Fraction(5214722552042, 10**12)
PMINUS_HI = Fraction(5214722552043, 10**12)
PPLUS_LO = Fraction(3661102186601, 10**12)
PPLUS_HI = Fraction(3661102186602, 10**12)
MU_LO = Fraction(7643532314898, 10**12)
MU_HI = Fraction(7643532314899, 10**12)


def semigroup_mask() -> list[int]:
    """Compute <4,5> intersect [0,B] by exact reachability."""
    reachable = bytearray(B + 1)
    reachable[0] = 1
    for n in range(B + 1):
        if not reachable[n]:
            continue
        for g in GENERATORS:
            if n + g <= B:
                reachable[n + g] = 1
    return [n for n, yes in enumerate(reachable) if yes]


def supports(mask: list[int]) -> tuple[list[int], list[int], list[tuple[int, int] | None]]:
    """Reconstruct M+M and minimum difference witnesses by direct pair loops."""
    sums = sorted({a + b for a in mask for b in mask})
    inf = 10**9
    kappa = [inf] * (B + 1)
    witness: list[tuple[int, int] | None] = [None] * (B + 1)
    for a in mask:
        for b in mask:
            if a < b:
                continue
            d = a - b
            cost = a + b
            if cost < kappa[d]:
                kappa[d] = cost
                witness[d] = (a, b)
    return sums, kappa, witness


def coefficient_vectors(sums: list[int], kappa: list[int]) -> tuple[list[int], list[int], list[int]]:
    """Coefficients of Pplus, Pminus, and x Pminus'(x)."""
    plus = [0] * (DEGREE + 1)
    minus = [0] * (DEGREE + 1)
    for s in sums:
        plus[s] = 1
    minus[0] = 1
    for d in range(1, B + 1):
        if kappa[d] < 10**9:
            minus[kappa[d]] += 2
    moment = [e * c for e, c in enumerate(minus)]
    return plus, minus, moment


def evaluate_common_den(poly: list[int], num: int, den: int) -> tuple[int, int]:
    """Evaluate an integer polynomial at num/den with denominator den**DEGREE."""
    assert len(poly) == DEGREE + 1
    value = poly[DEGREE]
    common_den = 1
    for e in range(DEGREE - 1, -1, -1):
        value = num * value + poly[e] * den * common_den
        common_den *= den
    return value, common_den


def atanh_log_unit(q: Fraction, terms: int = LOG_TERMS) -> tuple[Fraction, Fraction]:
    """Rigorous rational enclosure for log(q), for any positive q near 1."""
    if q <= 0:
        raise ValueError("log input must be positive")
    z = (q - 1) / (q + 1)
    z2 = z * z
    partial = Fraction(0)
    zpow = z
    for j in range(terms):
        partial += zpow / (2 * j + 1)
        zpow *= z2
    approximation = 2 * partial
    remainder = 2 * abs(zpow) / ((2 * terms + 1) * (1 - z2))
    return approximation - remainder, approximation + remainder


def floor_log2_fraction(x: Fraction) -> int:
    if x <= 0:
        raise ValueError("x must be positive")
    n, d = x.numerator, x.denominator
    k = n.bit_length() - d.bit_length()
    if k >= 0:
        if Fraction(1 << k, 1) > x:
            k -= 1
    elif Fraction(1, 1 << (-k)) > x:
        k -= 1
    return k


def log_bounds(x: Fraction, terms: int = LOG_TERMS) -> tuple[Fraction, Fraction]:
    """Rigorous rational lower and upper bounds for log(x)."""
    if x <= 0:
        raise ValueError("log input must be positive")
    if x == 1:
        return Fraction(0), Fraction(0)
    if x < 1:
        lo, hi = log_bounds(1 / x, terms)
        return -hi, -lo

    k = floor_log2_fraction(x)
    two_to_k = Fraction(2) ** k
    reduced = x / two_to_k  # 1 <= reduced < 2
    lo2, hi2 = atanh_log_unit(Fraction(2), terms)
    lor, hir = atanh_log_unit(reduced, terms)
    if k >= 0:
        return k * lo2 + lor, k * hi2 + hir
    return k * hi2 + lor, k * lo2 + hir


def interval_add(a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return a[0] + b[0], a[1] + b[1]


def positive_scale(c: Fraction, interval: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    assert c >= 0
    return c * interval[0], c * interval[1]


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def encoded_lines(values: list[int]) -> bytes:
    return "".join(f"{v}\n" for v in values).encode("ascii")


def signed_kappa_lines(kappa: list[int]) -> bytes:
    rows = ["d\tkappa\n"]
    for d in range(-B, B + 1):
        c = kappa[abs(d)]
        if c < 10**9:
            rows.append(f"{d}\t{c}\n")
    return "".join(rows).encode("ascii")


def decimal_fraction(x: Fraction, digits: int = 30) -> str:
    sign = "-" if x < 0 else ""
    x = abs(x)
    scale = 10**digits
    q = x.numerator * scale // x.denominator
    return f"{sign}{q // scale}.{q % scale:0{digits}d}"


def display_values(
    plus_num: int,
    plus_den: int,
    minus_num: int,
    minus_den: int,
    moment_num: int,
) -> dict[str, str]:
    with localcontext() as ctx:
        ctx.prec = 100
        pminus = Decimal(minus_num) / Decimal(minus_den)
        pplus = Decimal(plus_num) / Decimal(plus_den)
        mu = Decimal(moment_num) / Decimal(minus_num)
        lambda_x = (Decimal(X_DEN) / Decimal(X_NUM)).ln()
        lambda_y = (Decimal(Y_DEN) / Decimal(Y_NUM)).ln()
        rho = pminus.ln() + mu * lambda_x
        sigma = pplus.ln() + mu * lambda_y
        rate = (Decimal(RATE_NUM) / Decimal(RATE_DEN)).ln()
        fixed = Decimal(1) + (rho - sigma) / rate
        ideal = Decimal(2) - sigma / rho
        return {
            "Pminus": str(pminus),
            "Pplus": str(pplus),
            "mu": str(mu),
            "lambda_x": str(lambda_x),
            "lambda_y": str(lambda_y),
            "rho": str(rho),
            "sigma": str(sigma),
            "log_rate": str(rate),
            "log_rate_minus_rho": str(rate - rho),
            "fixed_rate_exponent": str(fixed),
            "ideal_exponent": str(ideal),
            "fixed_margin_over_target": str(fixed - Decimal(TARGET_THETA.numerator) / Decimal(TARGET_THETA.denominator)),
        }


def emit_certificate(
    directory: Path,
    mask: list[int],
    sums: list[int],
    kappa: list[int],
    summary: dict[str, object],
    finite_n: int,
    finite_l: int,
) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "mask.txt").write_bytes(encoded_lines(mask))
    (directory / "sum_support.txt").write_bytes(encoded_lines(sums))
    (directory / "difference_costs.tsv").write_bytes(signed_kappa_lines(kappa))
    (directory / "N.txt").write_text(f"{finite_n}\n", encoding="ascii")
    (directory / "L.txt").write_text(f"{finite_l}\n", encoding="ascii")
    (directory / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit", type=Path, help="write reconstructed certificate files")
    args = parser.parse_args()

    # 1. Reconstruct the structured alphabet from scratch.
    mask = semigroup_mask()
    gaps = tuple(n for n in range(1, 12) if n not in mask)
    assert gaps == EXPECTED_GAPS
    assert mask == [0, 4, 5, 8, 9, 10] + list(range(12, B + 1))
    assert len(mask) == EXPECTED_MASK_SIZE

    sums, kappa, witness = supports(mask)
    assert len(sums) == EXPECTED_SUM_SIZE
    assert sums == [0, 4, 5, 8, 9, 10] + list(range(12, DEGREE + 1))
    assert 1 + 2 * sum(c < 10**9 for c in kappa[1:]) == EXPECTED_DIFF_SIZE
    assert all(kappa[d] < 10**9 for d in range(B + 1))
    for d, expected in EXPECTED_KAPPA.items():
        assert kappa[d] == expected
    for d in range(12, B + 1):
        assert kappa[d] == d and witness[d] == (d, 0)

    plus, minus, moment = coefficient_vectors(sums, kappa)
    minus_num, minus_den = evaluate_common_den(minus, X_NUM, X_DEN)
    moment_num, moment_den = evaluate_common_den(moment, X_NUM, X_DEN)
    plus_num, plus_den = evaluate_common_den(plus, Y_NUM, Y_DEN)
    assert moment_den == minus_den

    mu = Fraction(moment_num, minus_num)

    # Tight decimal-looking bounds are first proved by exact integer
    # cross-multiplication.  They are therefore rational certificates, not
    # floating-point assumptions.
    assert PMINUS_LO.numerator * minus_den < PMINUS_LO.denominator * minus_num
    assert PMINUS_HI.denominator * minus_num < PMINUS_HI.numerator * minus_den
    assert PPLUS_LO.numerator * plus_den < PPLUS_LO.denominator * plus_num
    assert PPLUS_HI.denominator * plus_num < PPLUS_HI.numerator * plus_den
    assert MU_LO.numerator * minus_num < MU_LO.denominator * moment_num
    assert MU_HI.denominator * moment_num < MU_HI.numerator * minus_num

    # 2. Exact rational logarithm intervals for the two separate saddles.
    log_pminus_lo = log_bounds(PMINUS_LO)[0]
    log_pminus_hi = log_bounds(PMINUS_HI)[1]
    log_pplus_lo = log_bounds(PPLUS_LO)[0]
    log_pplus_hi = log_bounds(PPLUS_HI)[1]
    lambda_x = log_bounds(Fraction(X_DEN, X_NUM))
    lambda_y = log_bounds(Fraction(Y_DEN, Y_NUM))
    log_rate = log_bounds(Fraction(RATE_NUM, RATE_DEN))

    rho = (
        log_pminus_lo + MU_LO * lambda_x[0],
        log_pminus_hi + MU_HI * lambda_x[1],
    )
    sigma = (
        log_pplus_lo + MU_LO * lambda_y[0],
        log_pplus_hi + MU_HI * lambda_y[1],
    )

    # The quotient modulus rate must dominate the full-difference entropy rate.
    admissibility_margin = log_rate[0] - rho[1]
    assert admissibility_margin > 0

    # The fixed-rate exponent is > 1+alpha exactly when
    # rho - sigma - alpha log R > 0.
    exponent_rate_margin = rho[0] - sigma[1] - TARGET_ALPHA * log_rate[1]
    assert exponent_rate_margin > 0
    assert rho[0] > sigma[1]

    # 3. One exact finite Gibbs type and its finite-size correction.
    # Each signed d receives weight X_NUM^kappa(d) X_DEN^(DEGREE-kappa(d)).
    finite_n = minus_num
    assert moment_num % 2 == 0
    finite_l = moment_num // 2
    assert finite_l >= min(GENERATORS)
    assert finite_n >= 2

    # R is reduced and nonintegral, so R^N is nonintegral.  The least prime
    # above floor(R^N) is therefore > |V-V| and, by Bertrand, < 2R^N.
    assert math.gcd(RATE_NUM, RATE_DEN) == 1 and RATE_DEN > 1
    assert RATE_NUM * RATE_NUM > (2 * B + 1) * RATE_DEN * RATE_DEN

    # If q=2p-1, then q<4R^N.  The standard type-class lower bound and the
    # quotient factors reduce exponent > 1+alpha to
    #
    # N*(rho-sigma-alpha log R)
    #   > |D| log(N+1) + (2+2alpha) log 2.
    _, log2_hi = log_bounds(Fraction(2))
    bit_bound = (finite_n + 1).bit_length()
    rhs_upper = (
        Fraction(EXPECTED_DIFF_SIZE * bit_bound + 2, 1) + 2 * TARGET_ALPHA
    ) * log2_hi
    lhs_lower = finite_n * exponent_rate_margin
    assert lhs_lower > rhs_upper

    n_bytes = finite_n.to_bytes((finite_n.bit_length() + 7) // 8, "big")
    l_bytes = finite_l.to_bytes((finite_l.bit_length() + 7) // 8, "big")
    display = display_values(plus_num, plus_den, minus_num, minus_den, moment_num)

    summary: dict[str, object] = {
        "generators": list(GENERATORS),
        "B": B,
        "mask_size": len(mask),
        "sum_size": len(sums),
        "difference_size": EXPECTED_DIFF_SIZE,
        "x": f"{X_NUM}/{X_DEN}",
        "y": f"{Y_NUM}/{Y_DEN}",
        "rate": f"{RATE_NUM}/{RATE_DEN}",
        "target_theta": f"{TARGET_THETA.numerator}/{TARGET_THETA.denominator}",
        "mask_sha256": sha256_bytes(encoded_lines(mask)),
        "sum_support_sha256": sha256_bytes(encoded_lines(sums)),
        "difference_costs_sha256": sha256_bytes(signed_kappa_lines(kappa)),
        "finite_n": str(finite_n),
        "finite_l": str(finite_l),
        "finite_n_bits": finite_n.bit_length(),
        "finite_l_bits": finite_l.bit_length(),
        "finite_n_big_endian_sha256": sha256_bytes(n_bytes),
        "finite_l_big_endian_sha256": sha256_bytes(l_bytes),
        "rigorous_admissibility_margin_lower": decimal_fraction(admissibility_margin, 40),
        "rigorous_exponent_rate_margin_lower": decimal_fraction(exponent_rate_margin, 40),
        "display_only": display,
    }

    if args.emit:
        emit_certificate(args.emit, mask, sums, kappa, summary, finite_n, finite_l)

    print("TWO-TEMPERATURE EXACT RECONSTRUCTION: PASS")
    print(f"M=<4,5> intersect [0,{B}]")
    print(f"|M|={len(mask)} |M+M|={len(sums)} |M-M|={EXPECTED_DIFF_SIZE}")
    print(f"gaps={EXPECTED_GAPS}")
    print(f"x={X_NUM}/{X_DEN} y={Y_NUM}/{Y_DEN} R={RATE_NUM}/{RATE_DEN}")
    print("rigorous full-difference rate condition rho < log R: PASS")
    print("rigorous fixed-rate exponent > 1.21418: PASS")
    print("rigorous finite-size correction: PASS")
    print(f"admissibility margin lower > {decimal_fraction(admissibility_margin, 30)}")
    print(f"exponent-rate margin lower > {decimal_fraction(exponent_rate_margin, 30)}")
    print(f"finite N_bits={finite_n.bit_length()} L_bits={finite_l.bit_length()}")
    print(f"finite N_sha256={summary['finite_n_big_endian_sha256']}")
    print(f"finite L_sha256={summary['finite_l_big_endian_sha256']}")
    for key in (
        "Pminus", "Pplus", "mu", "rho", "sigma", "log_rate",
        "fixed_rate_exponent", "ideal_exponent", "fixed_margin_over_target",
    ):
        print(f"display {key}={display[key]}")
    print("CERTIFIED NUMERICAL HYPOTHESES FOR THE WRITTEN THEOREM: C_3a > 1.21418")


if __name__ == "__main__":
    main()
