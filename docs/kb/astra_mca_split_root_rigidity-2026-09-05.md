# At most three candidates whose error polynomial splits on the domain

The [moment-rigidity argument](astra_mca_moment_rigidity-2026-09-05.md)
extends to every possible received degree if we restrict to candidates whose
error polynomial has all its roots in the evaluation domain. Repeated roots
are allowed, with no separate multiplicity bound. For the actual production
prime, the resulting sublist has at most three polynomials. The bound improves
to one or two in the higher degree ranges below.

This is a written argument with reproducible exact controls, **not a Lean
formalization or independently reviewed proof**. It does not bound the
remaining candidates, whose error polynomial has a root outside the domain.
It therefore supplies neither the universal single-hole bound nor a solution
to the Proximity Prize.

## Statement and exact scope

Retain the [certified prime and generator](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean):

```text
n=2^30=1073741824,
P=365375409332725729550921208179070755120141565953,
g=303645430271030343624574566109998498685964493478 in F_P,
order(g)=n,
k=n/2=536870912,
ell=n/4=268435456,
b=(n+2)/6=178956971,
A=k+b=715827883.
```

Let Omega=mu_n, fix an omitted point a, and let V be the unique interpolation
polynomial of a received word on Omega\{a}, so deg V<=n-2. For deg V=D>=A,
define the fully split sublist by

```text
L_split(V)={f : deg f<k,
  #{x in Omega\{a} : f(x)=V(x)}>=A,
  (V-f)/lc(V) is a product of D factors X-x with x in Omega}.
```

The last condition counts multiplicity. In particular, a residual root at
the omitted point is allowed; an irreducible residual factor over F_P or
a root in F_P\Omega is not allowed. Then

| Received degree D | Bound on the whole sublist L_split(V) |
| --- | ---: |
| 715827883 through 805306367 | 3 |
| 805306368 through 894784854 | 1 |
| 894784855 through 1073741822 | 2 |

Each bound is attained, with that many distinct values at a, for every
degree in its stated range. These are sharp bounds on the fully split
sublist; extra candidates outside this sublist are not excluded. At D=A,
every list candidate is automatically fully split, recovering the earlier
bound on the entire list. For D<A the earlier elementary root-bound cases
apply. Rescaling x by a reduces all the arguments to a=1.

## A norm bound controlled by extra multiplicity

Take two members f,f' and write rho_i,tau_i for the multiplicities of g^i
in their normalized error polynomials. Both multiplicity vectors have total
mass D and at least A distinct roots in Omega\{1}. Set

```text
s=D-A,       v_i=rho_i-tau_i,
E(v)=sum_i max(|v_i|-1,0).
```

Choose any A distinct punctured roots in each polynomial. Subtracting their
indicator vectors leaves two nonnegative multiplicity vectors of total mass
s. Their difference is the part not controlled by a signed indicator, so

```text
E(v)<=2s.                                               (1)
```

As both normalized polynomials have the same coefficients in degrees k
through D-1, Newton's identities give

```text
sum_i v_i*g^(ij)=0 in F_P,       1<=j<=D-k=b+s.          (2)
```

The moments now concern the entire root multiset, not an arbitrarily chosen
agreement subset. This is where the fully split hypothesis is used.

Suppose descent has already shown that v repeats a vector w of length m
exactly q=n/m times. Equation (1) gives

```text
E(w)<=floor(2s/q).
```

For d=m/2, form the negacyclic coefficients c_i=w_i-w_(i+d). Clip each
w_i to {-1,0,1}, leaving an integer remainder of total absolute mass E(w).
The clipped part contributes coefficients of absolute value at most two.
The folded remainder has total absolute mass at most E(w). Consequently

```text
sum_(i<d) c_i^2 <= 2m+4E(w)+E(w)^2.                    (3)
```

Indeed, the clipped squares sum to at most 4d; the cross terms contribute
at most 4E(w); and the remaining squares sum to at most E(w)^2. This is
stronger than applying a uniform maximum-multiplicity bound to every root.
Crucially, the excess budget shrinks by q during descent.

Let h=floor((b+s)/q) and r=ceil(h/2). The integer multiplication matrix of
C(T)=sum c_i*T^i in Z[T]/(T^d+1) has r zero eigenvalues modulo P at the
distinct primitive roots supplied by the odd moments. Thus P^r divides its
determinant. Hadamard's inequality and (3) give

```text
det(M)^2 <= (2m+4E(w)+E(w)^2)^(m/2).                    (4)
```

The [previous determinant proof](astra_mca_moment_rigidity-2026-09-05.md)
now shows c=0 whenever

```text
P^(2r) > (2m+4E(w)+E(w)^2)^(m/2).                      (5)
```

It uses irreducibility of T^(m/2)+1 over Q to ensure a nonzero determinant
when c is nonzero. The same proof works at m=4. After c=0, the even moments
and invertibility of two give the next descent step. No assertion about
divisibility by P in the whole ring of integers is substituted for the
distinct-root matrix argument.

## An exact certificate covering every received degree

Here 0<=s<=357913939. All 28 steps from m=n through m=8 pass (5) for every
integer s in this range. A certificate with only 840 gates establishes this,
without computing the enormous powers in (5):

1. Partition the s-range into {0} and the intervals
   [2^j,min(2^(j+1)-1,357913939)]. These 30 intervals are adjacent and cover
   the whole range.
2. For each interval [s_lo,s_hi] and each m=n/2^j>=8, set

   ```text
   h_lo=floor((b+s_lo)*m/n),       r_lo=ceil(h_lo/2),
   E_hi=floor(2*s_hi*m/n),
   B_hi=2m+4E_hi+E_hi^2,
   L=ceil(log2 B_hi),
   ```

   where the checker calculates L by integer bit length.
3. Verify the integer inequality 632*r_lo>=L*m. Since P>2^158, for every
   s in that interval this implies

   ```text
   P^(2r) > 2^(316r) >= 2^(L*m/2) >= B_hi^(m/2).
   ```

The moment count is nondecreasing with s, as is the norm bound, so the lower
and upper endpoints give the required uniform implication. The certificate
therefore proves period four of every multiplicity difference in a
coefficient fibre of fully split candidates.

If D>=3n/4, the reduced order-four vector still has h=1. Its excess budget
is at most two, so the squared row norm in (3) is at most 20. The same
determinant argument takes one more step and proves period two. This extra
step is also checked exactly. For D<3n/4 there need not be a remaining
order-four moment.

## Counting the periodic multiplicity fibres

If differences have period t, with t=4 or t=2, their entries are constant
on the t cosets of mu_(n/t). In each coset subtract the minimum multiplicity
of a candidate. The resulting nonnegative residual multiplicities are the
same for every member of the fibre: adding a constant to a whole coset
changes its minimum by that constant. Let R be their common monic root
polynomial.

For period four, put U_j=X^ell-i^j, where i=g^ell and j=0,1,2,3. Every
normalized candidate is therefore

```text
H=R*product_j U_j^(t_j),   t_j>=0,
sum_j t_j=T,              deg R=D-ell*T.                (6)
```

The fixed degree determines T. Distinct candidates have distinct tuples.
For D<3ell, only T=0,1,2 are possible.

- T=0 gives one candidate.
- If T=1, there are at most four candidates R*U_j. Were all four valid,
  a punctured node at a root of R would count four times, and every other
  punctured node would count once. Their total agreement count would be
  at most (n-1)+3 deg R. But deg R=D-ell<k and
  4A>(n-1)+3(k-1), so four candidates cannot each have A agreements.
- If T=2, a repeated choice R*U_j^2 has at most deg R+ell=D-ell<k
  distinct punctured roots, so it is not a list candidate. Every candidate
  chooses two different cosets. Complementary choices would have common
  roots only among the roots of R, hence at most deg R=D-2ell<ell.
  Two subsets of the punctured domain of size at least A must instead
  intersect in at least 2A-(n-1)=2b+1>ell-1 points. Complementary choices
  are therefore impossible. The six coset pairs form three complementary
  pairs, giving at most three candidates.

For D>=3ell, period two gives the analogous factorization using
X^k-1 and X^k+1. Because D<n, their total exponent T is at most one, hence
there are at most two candidates. If both occur, their common root
polynomial R has degree D-k and must account for at least 2b+1 common
punctured agreements. Thus two are possible only if D>=k+2b+1. This proves
the sharper bound of one below that threshold, and the table above.

## Sharp constructions in all three degree ranges

For A<=D<3ell, choose R as the monic locator of any D-2ell points in the
coset C_0 of mu_ell containing 1, excluding 1. This is possible because
b<=D-2ell<=ell-1. With U_1,U_2,U_3 as above, take

```text
H_0=R*U_1*U_2,  H_1=R*U_1*U_3,  H_2=R*U_2*U_3,
V=H_0,         f_j=V-H_j.
```

Each H_j has D distinct punctured roots. The candidate degrees are at most
D-ell<k, and their values at 1 are 0,-2i R(1),-4i R(1), all distinct.
The counting argument proves that these are the entire fully split sublist.

For 3ell<=D<k+2b+1, take V to be a monic locator of any D distinct punctured
nodes. The candidate f=0 exists, and the bound shows it is the unique member
of L_split(V).

For k+2b+1<=D<=n-2, choose a squarefree monic R of degree D-k, avoiding 1,
with at least b roots in mu_k\{1} and at least b+1 in the other coset of
mu_k. Such a choice is possible since 2b+1<=D-k<=k-2. Set

```text
H_0=R*(X^k-1), H_1=R*(X^k+1),
V=H_0,        f_0=0, f_1=-2R.
```

The first has at least (k-1)+(b+1)=A punctured roots; the second has at
least k+b=A. Repeated roots are present where R meets a private half-domain,
but they are permitted. Both candidates have degree below k, and their
values at 1 are 0 and -2R(1), which are distinct. The two-candidate bound
shows the fully split sublist is complete.

## The same bound for each fixed outside-domain factor

There is a unique factorization for every normalized error polynomial:

```text
(V-f)/lc(V)=H_f*Q_f,
H_f has all its roots in Omega,
Q_f is monic and gcd(Q_f,X^n-1)=1.
```

Here H_f includes the full multiplicity at every root in Omega. Fixing
Q_f=Q, of degree e, also gives a sublist of at most three candidates, with
the same upper bounds in the table indexed by the original received degree D.
The fully split sublist above is the fibre Q=1.

To see this, note that H_f has degree D-e>=A and at least A distinct
punctured roots. For two candidates in this fibre, Q divides f-f', and

```text
deg(H_f-H_f')<k-e.
```

Thus the H_f have the same top (D-e)-(k-e)=D-k coefficients. Their
multiplicity differences satisfy the same moment equations (2), with
excess at most 2(D-e-A)<=2s. Every determinant gate above still applies.
The counting argument also still applies: its degree bounds only become
stronger when D is replaced by D-e. The point counts and A are unchanged
because Q has no zeros in Omega. Here e<=D-A<k, so k-e is positive.

This corollary allows arbitrary nonconstant outside-domain factors provided
they are common to the candidates being compared. For example, multiplying
the low-degree three-member construction by Q=X^e gives three candidates
in a nontrivial fibre whenever A+e<3ell; the resulting candidate degrees
remain below k. The checker verifies these examples at n=64 and e=1,2,3,4.

For a fixed received word, the entire list is therefore partitioned into
fibres of size at most three by Q_f. No bound on the number of different
factors Q_f is proved here. This is a restriction on an arbitrary list,
not a bound on its total size or its full evaluation image.
The [outside-factor investigation](astra_mca_outside_factor_frontier-2026-09-05.md)
constructs a production word with two candidates whose outside factors are
nonconstant and coprime. Thus a common outside factor cannot be assumed for
the whole list. Separately, its complete affine-line census bounds the
whole list by one for degree-twelve received words on mu_16 over P, including
a variable extra root. That finite result is not a production-length bound.

## Verification and the unresolved root-escape case

Run `python3 scripts/probes/astra_mca_split_root_rigidity_check.py`.
The script verifies the complete production arithmetic certificate and
directly enumerates every monic degree-11 through degree-14 polynomial
over mu_16 having at least 11 distinct punctured roots. It enumerates root
multiplicities and groups by actual top coefficients, without pruning by
the proposed rigidity property. The same census over F17 checks that the
large-characteristic hypothesis cannot be silently discarded. Its explicit
nonperiodic witnesses are checked using integer determinants, modular rank,
prime-power divisibility and the multiplicity-sensitive norm bound.

Over the production prime the exact degree-by-degree counts are:

| Degree | Enumerated polynomials | Coefficient fibres | Largest fibre |
| --- | ---: | ---: | ---: |
| 11 | 1365 | 1363 | 3 |
| 12 | 16835 | 16835 | 1 |
| 13 | 112490 | 112490 | 1 |
| 14 | 539750 | 539750 | 1 |

All differences have the asserted period. Over F17, degrees 12, 13 and
14 instead have maximum fibre size two, with 464, 758 and 700 nonperiodic
differences from representatives, respectively. The first degree-12
example has multiplicity excess two and nonzero determinant 113288,
divisible by 17^2; its large-characteristic determinant gate fails. These
are explicit finite controls, not a production counterexample.

The three construction formulas are checked at every degree from 43 through
62 on mu_64 over the actual prime. Exact synthetic division recovers every
domain-root multiplicity from the constructed polynomials and verifies that
the remaining factor is one; the separate common-factor examples leave
exactly X^e. These tests distinguish constructed list
members from completeness: completeness only within L_split(V) uses the
written argument above. No arbitrary production received word is enumerated.

For a general list candidate, choosing A agreement roots gives

```text
(V-f)/lc(V)=H_S*W_f,       deg W_f=D-A.
```

If all roots of W_f are in Omega, the fully split result applies, even with
arbitrary repetitions. If W_f has a root outside Omega, its power sums in
Newton's identities are not moments of a bounded-mass integer vector on
the cyclic evaluation domain. The outside terms cancel when the complete
outside factor is fixed, as in the preceding corollary; they need not cancel
between different outside factors. Bounding that variation remains open.
In particular, the
[single-hole value budget](astra_mca_single_hole_reduction-2026-09-05.md)
still has not been established for arbitrary received words; neither has
the universal MCA lower bound. The restricted degree range has been removed
from the fully split case, not from the prize problem.
