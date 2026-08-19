# Independent audit of the two-temperature candidate for C3a

## Verdict

I found no fatal error in the proposed two-temperature cyclic-quotient
argument. Subject to the standard GHR finite-set lemma and the human proof in
`c3a_two_temperature_proof.md`, the exact arithmetic certificates establish

\[
C_{3a}>1.21418.
\]

This remains a candidate research result pending external review or formal
verification.

## Points checked

1. **Symmetric types.** The floor construction gives nonnegative integer
   counts converging to the Gibbs distribution. The unused count is absorbed
   at zero, and the total witness cost is at most the prescribed budget.

2. **Witness budgets.** Equal counts for `d` and `-d` make the total signed
   difference zero. The two witness budgets are exactly equal, and the total
   cost is even, so each is an integer at most `floor(n*mu/2)`.

3. **Selected-difference entropy.** The multinomial type class has exponential
   rate `H(p)=rho`. For the explicit finite Gibbs type, the standard lower
   bound `exp(N*rho)/(N+1)^|D|` is used in the safe direction.

4. **Separate sum tilt.** The sum bound may use a parameter `y` independent of
   the difference Gibbs parameter `x`: every sum word has coordinate total at
   most `2L`, so `|V+V| y^(2L) <= Pplus(y)^n`. Nothing in the difference
   construction requires `y=x`.

5. **Full-difference bound.** For every actual difference `z=a-b`,
   `kappa(z_i)<=a_i+b_i`. Thus `Pminus(x)` bounds every full difference word,
   not only the selected type.

6. **Universal quotient collision probability.** With all coefficients
   random, two distinct selected words differ in a coordinate whose absolute
   value is at most `2B<p`; that coordinate is nonzero modulo `p`, giving
   collision probability exactly `1/p`.

7. **Endpoint rescaling.** Fewer than `|W|/2` collisions imply more than one
   selected image residue. Hence the image of `V` contains a nonzero residue;
   multiplying the quotient map by a nonzero scalar can place `-1` in the
   image without changing any modular cardinality.

8. **Integer representative bounds.** A residue has at most two sum
   representatives in `[0,2p-2]`, while zero has one and every other residue
   at most two difference representatives in `[-(p-1),p-1]`. This gives the
   factors two and the strict GHR condition.

9. **Limit and quantifiers.** For every exponent below the limiting expression,
   one sufficiently large fixed finite quotient seed has a larger GHR
   exponent. Applying the GHR lemma to that one seed avoids any uniformity
   issue.

10. **Explicit finite seed.** At rational `x`, clearing the common denominator
    gives exact integer type counts. With
    `T=floor((249293/10000)^N)` and the least prime `p>T`, the strict full
    difference condition follows from `rho<log R`; Bertrand gives the required
    denominator bound. The verifier checks the complete finite-size
    correction.

## Independent arithmetic reconstruction

The standard-library Python and C++/GMP programs use different algorithms:

- Python: forward semigroup reachability, direct witness pair enumeration,
  Horner polynomial evaluation, rational atanh logarithm enclosures.
- C++: Apéry shortest paths, intersection scanning for minimum witnesses,
  sparse monomial evaluation, independently implemented GMP rational
  logarithm enclosures.

They emit byte-for-byte identical masks, sum supports, difference-cost tables,
and finite `N,L` values.

An exhaustive small-model program checks the universal quotient lemma for all
162 sets of size 2 through 5 containing the origin inside `{0,1,2}^2`,
enumerating every quotient coefficient vector and verifying the exact
collision average and all integer sum/difference bounds.

## Remaining trust boundary

The arithmetic is exactly reproducible, but no Lean kernel or external human
referee has checked the new theorem. The prime and coefficient vector of the
finite seed are canonically specified but not materialized because their
sizes are astronomical.

For this frozen alphabet and parameters, the entropy-matched ceiling is the
display-only value

\[
2-\sigma/\rho=1.214181180950531\ldots.
\]

Thus merely shrinking the quotient-rate slack cannot materially exceed the
certified `1.21418`. A further improvement needs a better inner family or a
richer constraint geometry, not more precision in the same certificate.
