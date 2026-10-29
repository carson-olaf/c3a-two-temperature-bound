# Two-temperature cyclic compression for the Gyarmati-Hennecart-Ruzsa constant

**Carson Olafson**  
August 19, 2026; finite-proof revision October 29, 2026

## Status and result

This note gives a proof, with a Lean-verified finite instance in §6, that

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

The numerical inputs are checked by two independently structured programs.
The strict finite bound is also proved end to end in Lean 4, as described in
§6–7. The general limiting theorem remains a written argument. This package
is not an externally refereed publication.

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
\mathbb N_0\mathbin{\backslash} H=\{1,2,3,6,7,11\}.
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

## 6. The Lean-verified finite GHR seed

The formal proof uses one finite depth

\[
N=10^{13},\qquad x=\frac{8149}{10000},\qquad y=\frac{42571}{50000}.
\]

Let \(D=M-M=[-80,80]\) and \(Z=P_-(x)\). For \(d>0\), set

\[
n_d=n_{-d}=\left\lfloor\frac{Nx^{\kappa(d)}}Z\right\rfloor,
\qquad
n_0=N-2\sum_{d=1}^{80}n_d,
\qquad
L=\sum_{d=1}^{80}n_d\kappa(d).
\]

The exact finite checks in `formalization/lean/C3a/CertificateData.lean`
prove that all counts are positive, their sum is \(N\), and

\[
n_0=1917647564302,\qquad 2L=76435323145630.
\]

Write \(\mathcal V\) for the vector set, reserving \(V\) below for the
integer seed after dilation:

\[
\mathcal V=\left\{a\in M^N:\sum_i a_i\le L\right\}.
\]

Let \(W\subset D^N\) be the type class with counts \((n_d)\).
Symmetry makes the two minimum-witness budgets equal to \(L\), so
\(W\subset\mathcal V-\mathcal V\), and exact finite type counting gives

\[
|W|\prod_{d\in D}n_d!=N!.
\]

These statements and the independent tilted upper bounds

\[
|\mathcal V+\mathcal V|y^{2L}\le P_+(y)^N,
\qquad
|\mathcal V-\mathcal V|x^{2L}\le Z^N
\]

are proved in `C3a/VectorWords.lean`. No limit is taken.

The common envelope

\[
n_d\le\frac{(N+1000)x^{\kappa(d)}}Z\quad(d\in D)
\]

covers the floors and the extra zero symbols. Effective Stirling bounds in
`C3a/TypeEntropy.lean` imply

\[
\log|W|\ge N\log Z-2L\log x-1000
 -161\left(\frac{\log N}{2}+1\right).
\]

The rational logarithm bounds in `C3a/LogNumerics.lean` establish the
following conservative integer bounds, assembled in `C3a/Main.lean`:

\[
\begin{aligned}
\log|W|&\ge a=32160395000000,\\
\log|\mathcal V+\mathcal V|&\le b=25272245000000,\\
\log|\mathcal V-\mathcal V|&\le r=32160396000000.
\end{aligned}
\]

Put \(m=|\mathcal V-\mathcal V|+161\). Mathlib's proved Bertrand
postulate supplies a prime

\[
m<p\le2m.
\]

In particular, \(p>160\) and \(p>|\mathcal V-\mathcal V|\).
The finite collision-counting proof in `C3a/CyclicCompression.lean`,
together with `C3a/IntegerCompression.lean`, gives a linear map
\(\varphi:\mathbb Z^N\to\mathbb Z/p\mathbb Z\) such that the
least-nonnegative representative set \(A\subset[0,p-1]\) satisfies

\[
0\in A,\qquad \max A>0,\qquad
|A-A|>|W|/2,\qquad |A+A|\le2|\mathcal V+\mathcal V|.
\]

There is no rescaling to force \(-1\) into the quotient image. Instead,
use the integer seed \(V=2A=\{2a:a\in A\}\). Dilation preserves sumset
and difference-set cardinalities and supplies

\[
|V-V|<2\max V+1=4\max A+1.
\]

Moreover, since \(|\mathcal V-\mathcal V|\ge1\),

\[
4\max A+1\le1296|\mathcal V-\mathcal V|,
\qquad
\log(4\max A+1)\le r+\log1296<r+8.
\]

Logan Kleinwaks's proved GHR dilation principle applies to this one finite
seed. With \(\alpha=10709/50000\), the final comparison is

\[
\alpha(r+8)+b+2<a,
\tag{6.1}
\]

whose exact positive slack is \(36384716.28656\). Since \(\log4<2\),
this implies that the GHR exponent of \(V\) exceeds \(1+\alpha\).
The closed Lean theorem is

```lean
C3a.c3a_gt_121418 : (60709 / 50000 : Real) < MaskedDigit.C3a
```

Here `MaskedDigit.C3a` is exactly Kleinwaks's definition in
`RequestProject/GHRConstant.lean`. His admissibility predicate requires the
construction for every \(K>1\), so its lower bound also implies the bound
under the definition in Tao's problem 3a.

The prime, coefficient vector, and finite sets are specified by existence
proofs, not materialized. The rate \(R=249293/10000\) belongs to the
limiting comparison in §5; it is not used to choose the prime in this
finite proof.

## 7. Verification boundary and attribution

The end-to-end Lean proof of the strict finite bound is
`formalization/lean/C3a/Main.lean`. It includes the finite type argument,
weighted counts, quotient existence, integer lifts, and final inequality.
Bertrand's postulate is proved in Mathlib; the GHR finite-set and dilation
principles are proved in the reused files `RequestProject/GHRDigits.lean`
and `RequestProject/GHRConstant.lean`. They are not assumed axioms.
The general limiting Theorem 3.1 is not formalized here and is not needed
by the finite theorem.

The submitted proof pins Lean 4.35.0-rc2 and the Mathlib commit

`065356127b1dc0016f66b7283ce0ce2c4055aa55`

in `formalization/lean/lean-toolchain` and `lake-manifest.json`. The proof
was first built and kernel-checked with Lean 4.28.0 and Mathlib v4.28.0
(commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`), then ported to Lean's
module system for registration.

Run the axiom audit with
`lake env lean AxiomAudit.lean` from `formalization/lean/`.
The main theorem depends only on the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. All 17 original native finite checks
now have kernel-checked proofs, using interval arguments, exact rational
identities, `decide +kernel`, and `norm_num`. Neither `Lean.ofReduceBool`
nor `Lean.trustCompiler` occurs in the theorem's axiom list.

The verbatim audit is in `formalization/lean/evidence/AXIOMS.txt`, and
`evidence/KERNEL_CHECKS.md` records the replacements and timings. The
earlier native version remains available at commit
`5bbc2a5eb4d01eb3eb24fb909f819a8d220653f8`. Neither an independent agent
review nor a local build is a claim of journal refereeing or maintainer
acceptance.

Logan Kleinwaks's Apache-2.0 code is reused from
`kleinwaks/masked-digit-sum-difference-bound`, commit
`352ab86effecb7efce415507a8c781ec158b86e0`. The ten files under
`RequestProject/` are unchanged apart from attribution headers. They provide
the GHR definition and principles, mask infrastructure, type counting,
Stirling estimates, and logarithm bounds. The new vector-word proof adapts
his weighted-count and type-word arguments. The license and detailed
attribution are in `formalization/lean/`.

The original Python and C++/GMP verifiers remain independent exact checks
of the alphabet, costs, partition sums, and the §5 inequalities. They also
check an older, different exact-Gibbs finite instance: its depth has 2129
bits and its prime is chosen above \(\lfloor R^N\rfloor\), followed by
rescaling. Accordingly, `certificate/N.txt`, `certificate/L.txt`, their
hashes, and those programs' finite-size output describe that legacy
instance, not the \(N=10^{13}\) Lean instance in §6. Those artifacts are
preserved unchanged for reproducibility; they are not inputs or axioms of
the Lean proof.

## 8. Reproduction

Primary finite proof, from `formalization/lean/`:

```bash
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

Independent numerical and legacy-instance checks, using Python's standard
library only:

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
contributor responsible for this submission. The finite bound in §6 is
formally verified; this note is not externally refereed. Independent review of the general Theorem 3.1 is expressly invited.

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
