# Two-temperature cyclic compression for the Gyarmati-Hennecart-Ruzsa constant

**Carson Olafson**  
August 19, 2026

## Status and result

This note gives a new candidate proof that

\[
\boxed{C_{3a}>1.21418}.
\]

The construction is not a retuning of the earlier six-generator mask.  Its
inner alphabet is the much smaller numerical-semigroup truncation

\[
M=\langle4,5\rangle\cap[0,80]
 =\{0,4,5,8,9,10\}\cup[12,80],
\]

and its main new ingredient is a **two-temperature entropy theorem**: the
difference family and the sum-family upper bound are evaluated at separate
dual parameters.  The old one-temperature theorem forced those two
parameters to coincide.

At the exact rational parameters

\[
x=\frac{8149}{10000},\qquad
 y=\frac{42571}{50000},\qquad
 R=\frac{249293}{10000},
\]

the display-only fixed-rate value is

\[
1+\frac{\rho-\sigma}{\log R}
 =1.21418089609778549420005709249\ldots,
\]

while the entropy-matched limiting value is

\[
2-\frac{\sigma}{\rho}
 =1.21418118095053104745496921148\ldots.
\]

The conservative claim is only the strict rationally certified inequality
\(C_{3a}>1.21418\).

The numerical certificate is machine checked by two independently structured
programs. The two-temperature theorem and the finite-set lemma remain written
mathematical arguments; this package is not a Lean formalization or an
externally refereed publication.

## 1. The finite-set principle

We use the following lemma from K. Gyarmati, F. Hennecart, and I. Z. Ruzsa,
*Sums and differences of finite sets*, Functiones et Approximatio Commentarii
Mathematici **37** (2007), 175-186, Section 2, pp. 178-179,
DOI 10.7169/facm/1229618749.

**GHR finite-set lemma.** Let \(U\subset\mathbb N_0\) be finite and nonempty,
with \(0\in U\). Put

\[
s=|U+U|,\qquad d=|U-U|,\qquad q_U=2\max U+1.
\]

If \(d<q_U\), then

\[
\theta(U)=1+\frac{\log(d/s)}{\log q_U}
\]

is an admissible exponent for the GHR problem. More precisely, for every
\(K>1\) there are arbitrarily large finite integer sets \(A,B\) such that
\(|A+B|\le K|A|\) and

\[
|A-B|\ge
\left(\frac{2(K-1)}{3K}\right)^{5/4}|A+B|^{\theta(U)}.
\]

Thus a single finite \(U\) satisfying the strict difference-set condition
supplies a lower bound for \(C_{3a}\).

## 2. Universal cyclic compression

The outer compression step does not depend on the numerical semigroup.

### Lemma 2.1 (cyclic quotient with controlled collisions)

Let \(V\subset\mathbb Z^n\) be finite and contain zero. Let
\(W\subset V-V\) have \(T=|W|\ge2\), and suppose every coordinate of every
word in \(W\) has absolute value at most \(B_0\). If \(p\) is prime and

\[
p>2B_0,\qquad p>|V-V|,
\]

then there is a linear map

\[
\phi_c(z)=\sum_{i=1}^n c_i z_i\pmod p
\]

such that, after multiplying \(\phi_c\) by a nonzero scalar if necessary,
the least-nonnegative representative set

\[
A=\operatorname{rep}_{[0,p-1]}\phi_c(V)
\]

satisfies

\[
\max A=p-1,
\tag{2.1}
\]

\[
|A+A|\le2|V+V|,
\tag{2.2}
\]

\[
|A-A|>\frac{T}{2},
\tag{2.3}
\]

and

\[
|A-A|\le2|V-V|-1<2p-1=2\max A+1.
\tag{2.4}
\]

The coefficient vector can be chosen canonically by conditional
expectations, followed by canonical rescaling.

### Proof

Choose all coefficients \(c_1,\ldots,c_n\) independently and uniformly in
\(\mathbb F_p\). For distinct \(w,w'\in W\), write \(h=w-w'\). Some
coordinate \(h_j\) is a nonzero integer with \(|h_j|\le2B_0<p\), and hence
is nonzero in \(\mathbb F_p\). Holding the other coefficients fixed, exactly
one value of \(c_j\) solves \(\phi_c(h)=0\). Therefore

\[
\Pr(\phi_c(w)=\phi_c(w'))=\frac1p.
\]

If \(C(c)\) is the number of unordered colliding pairs in \(W\), then

\[
\mathbb E C(c)=\frac{\binom T2}{p}<\frac T2,
\]

because \(T\le|V-V|<p\). Choose \(c\) with \(C(c)<T/2\). This choice can be
made coefficient by coefficient by minimizing the conditional expected final
collision count and breaking ties by the least residue.

If a fiber of \(\phi_c|_W\) has size \(t\), it loses \(t-1\) image points
but contributes \(\binom t2\ge t-1\) colliding pairs. Consequently

\[
|\phi_c(W)|\ge T-C(c)>T/2.
\]

Since \(T\ge2\), the image \(\phi_c(V)\) is not \(\{0\}\). Choose the least
specified \(v\in V\) with \(\phi_c(v)\ne0\), and multiply the map by
\(-\phi_c(v)^{-1}\). This does not change any cardinality and puts \(-1\)
in the image. Since zero is also in the image, the representative set
contains \(0,p-1\), proving (2.1).

Every residue has at most two representatives in \([0,2p-2]\), so

\[
|A+A|\le2|\phi_c(V+V)|\le2|V+V|.
\]

Distinct residues in \(\phi_c(W)\) give distinct integer differences, which
proves (2.3). In \([-(p-1),p-1]\), residue zero has one representative and
each nonzero residue has at most two. Hence

\[
|A-A|\le2|\phi_c(V-V)|-1\le2|V-V|-1<2p-1.
\]

This proves the lemma. \(\square\)

## 3. The two-temperature theorem

Let \(M\subset\mathbb N_0\) be finite, contain zero, and contain a positive
integer. Define

\[
S=M+M,\qquad D=M-M,
\]

and, for \(d\in D\),

\[
\kappa(d)=\min\{a+b:a,b\in M,\ a-b=d\}.
\]

For \(x,y\in(0,1)\), put

\[
P_-(x)=\sum_{d\in D}x^{\kappa(d)},
\qquad
P_+(y)=\sum_{s\in S}y^s,
\]

\[
\mu=
\frac{\sum_{d\in D}\kappa(d)x^{\kappa(d)}}{P_-(x)},
\]

\[
\rho=\log P_-(x)-\mu\log x,
\qquad
\sigma=\log P_+(y)-\mu\log y.
\]

### Theorem 3.1 (two-temperature cyclic quotient)

If \(\sigma<\rho\), then

\[
\boxed{
C_{3a}\ge2-\frac{\sigma}{\rho}.
}
\tag{3.1}
\]

More generally, for every real \(r>\rho\),

\[
\boxed{
C_{3a}\ge1+\frac{\rho-\sigma}{r}.
}
\tag{3.2}
\]

In particular, if a rational number \(R>1\) satisfies
\(\rho<\log R\), then

\[
\boxed{
C_{3a}\ge1+\frac{\rho-\sigma}{\log R}.
}
\tag{3.3}
\]

### Proof

Give \(D\) the symmetric Gibbs distribution

\[
p_d=\frac{x^{\kappa(d)}}{P_-(x)}.
\]

Its entropy is

\[
H(p)=-\sum_dp_d\log p_d
=\log P_-(x)-\mu\log x
=\rho.
\]

For every positive \(d\in D\), set

\[
n_d^{(n)}=n_{-d}^{(n)}=\lfloor np_d\rfloor,
\]

and put the unused count into zero:

\[
n_0^{(n)}=n-2\sum_{d>0}\lfloor np_d\rfloor.
\]

These counts are nonnegative, sum to \(n\), and their normalized frequencies
converge to \(p\). Moreover,

\[
\sum_d n_d^{(n)}\kappa(d)
=2\sum_{d>0}\lfloor np_d\rfloor\kappa(d)
\le n\mu.
\]

Let

\[
L_n=\left\lfloor\frac{n\mu}{2}\right\rfloor,
\]

\[
V_n=\left\{a\in M^n:\sum_i a_i\le L_n\right\},
\]

and let \(W_n\subset D^n\) be the type class with counts
\(n_d^{(n)}\).

Choose minimum-cost witnesses \(\alpha_d,\beta_d\in M\) with

\[
\alpha_d-\beta_d=d,
\qquad
\alpha_d+\beta_d=\kappa(d),
\]

choosing the witnesses for \(-d\) by swapping those for \(d\). Every word
in \(W_n\) has coordinate sum zero. Thus its total \(\alpha\)-budget equals
its total \(\beta\)-budget, while their sum is an even integer at most
\(n\mu\). Each budget is therefore at most \(L_n\), and

\[
W_n\subset V_n-V_n.
\]

Writing \(T_n=|W_n|\), Stirling's formula, or the standard method-of-types
bounds on a fixed alphabet, gives

\[
\frac1n\log T_n\longrightarrow H(p)=\rho.
\tag{3.4}
\]

Now use separate exponential tilts on the two sides. Every vector in
\(V_n+V_n\) has coordinates in \(S\) and total coordinate sum at most
\(2L_n\). Since \(0<y<1\),

\[
|V_n+V_n|y^{2L_n}\le P_+(y)^n.
\]

Because \(2L_n\le n\mu\),

\[
|V_n+V_n|\le e^{n\sigma}.
\tag{3.5}
\]

Likewise, if \(z=a-b\in V_n-V_n\), then
\(\kappa(z_i)\le a_i+b_i\) coordinatewise. Hence

\[
|V_n-V_n|x^{2L_n}\le P_-(x)^n,
\]

and

\[
|V_n-V_n|\le e^{n\rho}.
\tag{3.6}
\]

Fix \(r>\rho\). Put \(N_n=\lceil e^{rn}\rceil\), and use Bertrand's
postulate to choose a prime

\[
N_n<p_n<2N_n.
\]

For all sufficiently large \(n\), equations (3.4)-(3.6) give

\[
p_n>|V_n-V_n|,\qquad p_n>2\max M,\qquad T_n\ge2.
\]

Apply Lemma 2.1 to \(V_n,W_n,p_n\). It gives a finite
\(A_n\subset[0,p_n-1]\) satisfying the strict GHR hypothesis and

\[
|A_n-A_n|>T_n/2,
\qquad
|A_n+A_n|\le2e^{n\sigma},
\]

\[
2\max A_n+1=2p_n-1.
\]

Therefore

\[
\theta(A_n)>
1+\frac{\log T_n-n\sigma-\log4}{\log(2p_n-1)}.
\]

By (3.4), the numerator after the initial 1, divided by \(n\), tends to
\(\rho-\sigma\). The denominator divided by \(n\) tends to \(r\). For every
number strictly below the right side of (3.2), one sufficiently large fixed
\(n\) therefore supplies a finite GHR seed. Applying the GHR lemma to that
single seed proves (3.2). Letting \(r\downarrow\rho\) proves (3.1), and
putting \(r=\log R\) gives (3.3). \(\square\)

### What is new relative to the one-temperature theorem

The earlier cyclic-quotient proof used \(y=x\), so its numerator collapsed to
\(\log P_-(x)-\log P_+(x)\). The sum upper bound does not require this:
its Markov parameter can be optimized independently. The new theorem uses the
difference tilt \(x\) to choose the high-entropy realizable type and the sum
tilt \(y\) only to upper-bound all possible sums at the resulting budget.

For the gapless limiting alphabet \(\mathbb N_0\), taking
\(x=\sqrt2-1\) and \(y=1/2\) gives

\[
\rho=2\log(1+\sqrt2),
\qquad
\sigma=2\log2,
\]

and therefore

\[
2-\frac{\sigma}{\rho}
=2-\frac{\log2}{\log(1+\sqrt2)}
=1.213560298642605\ldots.
\]

Thus the independently announced \(1.21356\ldots\) result of Logan Kleinwaks
is the natural gapless baseline of the two-temperature theorem. The
construction below crosses it by changing the inner alphabet, not by changing
a cutoff in the old mask.

## 4. The structured alphabet \(\langle4,5\rangle\)

Let

\[
H=\langle4,5\rangle.
\]

It has conductor \(12\) and exactly six gaps:

\[
\mathbb N_0\setminus H=\{1,2,3,6,7,11\}.
\]

Take

\[
M=H\cap[0,80].
\]

Exact reconstruction gives

\[
|M|=75,
\qquad
|M+M|=155,
\qquad
|M-M|=161.
\]

In fact,

\[
M+M=\{0,4,5,8,9,10\}\cup[12,160],
\]

while

\[
M-M=[-80,80].
\]

For every positive \(d\in H\cap[1,80]\), the witness \((d,0)\) gives
\(\kappa(d)=d\). The six missing positive differences are recovered at the
following exact costs:

\[
\begin{array}{c|rrrrrr}
d&1&2&3&6&7&11\\ \hline
\kappa(d)&9&18&13&14&17&19.
\end{array}
\]

Thus the semigroup deletes six low-cost sum symbols but retains every
difference symbol, paying a moderate witness-cost penalty only on those six
gaps. That trade is exactly what improves the entropy ratio.

The partition polynomials can be written explicitly as

\[
P_+(y)=1+y^4+y^5+y^8+y^9+y^{10}+\sum_{s=12}^{160}y^s,
\]

and

\[
P_-(x)=1+2\left(
\sum_{d\in H\cap[1,80]}x^d
+x^9+x^{18}+x^{13}+x^{14}+x^{17}+x^{19}
\right).
\]

## 5. Exact numerical certificate

Use

\[
x=\frac{8149}{10000},
\qquad
y=\frac{42571}{50000},
\qquad
R=\frac{249293}{10000}.
\]

The exact verifier reconstructs the polynomials and proves by integer
cross-multiplication that

\[
5.214722552042<P_-(x)<5.214722552043,
\]

\[
3.661102186601<P_+(y)<3.661102186602,
\]

and

\[
7.643532314898<\mu<7.643532314899.
\]

It then uses rational atanh-series enclosures for every logarithm and proves

\[
\log R-\rho
>0.0000042772145404387872525092606,
\tag{5.1}
\]

and

\[
\rho-\sigma-\frac{10709}{50000}\log R
>0.0000028818893326729700122738247.
\tag{5.2}
\]

Equation (5.1) is the full-difference-rate condition in Theorem 3.1.
Equation (5.2) gives

\[
1+\frac{\rho-\sigma}{\log R}
>1+\frac{10709}{50000}
=1.21418.
\]

Hence

\[
\boxed{C_{3a}>1.21418}.
\]

Display-only values reconstructed from the exact integers are

\[
\begin{aligned}
P_-(x)&=5.21472255204231355326778335618\ldots,\\
P_+(y)&=3.66110218660138413370190644948\ldots,\\
\mu&=7.64353231489850089011819946550\ldots,\\
\rho&=3.21603954130634406125710246429\ldots,\\
\sigma&=2.52722439436574711487654603261\ldots,\\
\log R&=3.21604381852111829907290215884\ldots.
\end{aligned}
\]

## 6. One explicit finite GHR seed

Because \(x\) is rational, clear a common degree \(D_0=160\). For each
\(d\in M-M\), put

\[
\omega_d=8149^{\kappa(d)}10000^{160-\kappa(d)}.
\]

Define

\[
N=\sum_d\omega_d,
\qquad
2L=\sum_d\kappa(d)\omega_d.
\]

Then \(\omega_d/N\) is exactly the Gibbs distribution, \(2L\) is even, and

\[
V=\left\{a\in M^N:\sum_i a_i\le L\right\}.
\]

Let \(W\) be the exact type class containing \(\omega_d\) copies of each
\(d\). Its two witness budgets are exactly \(L\), so \(W\subset V-V\).

Set

\[
T=\left\lfloor\left(\frac{249293}{10000}\right)^N\right\rfloor,
\]

and let \(p\) be the least prime greater than \(T\). Since
\(|V-V|<R^N\), we have \(|V-V|\le T<p\). Bertrand's postulate gives
\(p<2T<2R^N\). Choose the quotient map by the canonical conditional-
expectation rule from Lemma 2.1, rescale canonically so that a nonzero image
element becomes \(-1\), and let \(A\subset[0,p-1]\) be the least-
nonnegative representative set.

The standard finite type-class estimate is

\[
|W|\ge\frac{e^{N\rho}}{(N+1)^{|M-M|}}.
\]

Together with the quotient bounds and \(2p-1<4R^N\), a sufficient finite
inequality for exponent greater than \(1+\alpha\), where
\(\alpha=10709/50000\), is

\[
N(\rho-\sigma-\alpha\log R)
>
|M-M|\log(N+1)+(2+2\alpha)\log2.
\tag{6.1}
\]

The verifier proves (6.1) with rigorous rational intervals. Thus the result is
not only a limit statement: the algorithm above specifies one finite GHR seed
whose exponent exceeds \(1.21418\).

The exact integers have

\[
\operatorname{bitlen}(N)=2129,
\qquad
\operatorname{bitlen}(L)=2131.
\]

Their big-endian byte hashes are

```text
N  a9db0611a20142dca241b32363fbb535cc64e9755d312f659edfe966add9e417
L  0f4a6eaef4e3f2387da12a5f1a0a2252c5cf929be806ee423a39957f137737e3
```

The complete decimal expansions are in the generated certificate directory.
The prime, quotient coefficients, and all elements of \(A\) are finitely and
canonically specified but are not materialized.

## 7. Verification boundary

The Python standard-library verifier performs:

1. exact reconstruction of \(\langle4,5\rangle\cap[0,80]\);
2. exact reconstruction of \(M+M\), \(M-M\), every \(\kappa(d)\), and the
   partition-polynomial numerators;
3. exact rational enclosures for \(P_-\), \(P_+\), and \(\mu\);
4. rigorous rational enclosures for every logarithm;
5. the strict rate and exponent comparisons (5.1)-(5.2);
6. the explicit finite-size correction (6.1);
7. reconstruction and hashing of the exact finite \(N,L\).

An independently written C++/GMP verifier uses Apéry shortest paths,
intersection scanning for minimum witnesses, sparse monomial evaluation, and
its own rational logarithm implementation. The two programs emit byte-for-
byte identical masks, supports, difference-cost tables, and finite parameters.

The programs do **not** formally prove Theorem 3.1, the method-of-types bound,
Bertrand's postulate, or the GHR finite-set lemma. Those remain written
mathematical arguments in this note.

## 8. Reproduction

Python, standard library only:

```bash
python3 verification/verify_c3a_two_temperature_121418.py --emit certificate
```

Independent C++/GMP:

```bash
g++ -O2 -std=c++20 verification/verify_c3a_two_temperature_121418_gmp.cpp \
  -lgmpxx -lgmp -o verify_gmp
./verify_gmp --emit certificate_gmp
```

Then compare the five discrete certificate files byte for byte.

## 9. Acknowledgements and AI-use disclosure

I thank Logan Kleinwaks for reviewing an earlier `1.2060` candidate, identifying
minor statement and exposition issues that are corrected here, and publicly
sharing his independent `1.21356` construction. I also thank the contributors
to the Optimization Constants in Mathematics project for maintaining the
problem record and its reproducibility standards.

Carson Olafson used ChatGPT extensively to explore constructions, formulate the
two-temperature argument, draft and revise this note, generate the verification
programs, and audit the resulting package. Carson selected the research
direction, ran and reviewed the verification outputs, and is the human
contributor responsible for this submission. This note is neither externally
refereed nor formally verified; independent review of Theorem 3.1 is expressly
invited.

## References

1. K. Gyarmati, F. Hennecart, and I. Z. Ruzsa, *Sums and differences of finite
   sets*, Functiones et Approximatio Commentarii Mathematici **37** (2007),
   175-186, DOI [10.7169/facm/1229618749](https://doi.org/10.7169/facm/1229618749).
2. L. Kleinwaks, review of an earlier cyclic-quotient construction and
   announcement of an independent `1.21356` bound,
   [optimizationproblems PR #134 comment](https://github.com/teorth/optimizationproblems/pull/134#issuecomment-5299513691),
   August 15, 2026.
3. L. Kleinwaks, *Improve C_3a lower bound via Lean-formalized controlled-carry
   semigroup mask-digit construction*,
   [optimizationproblems PR #146](https://github.com/teorth/optimizationproblems/pull/146),
   August 14, 2026.
