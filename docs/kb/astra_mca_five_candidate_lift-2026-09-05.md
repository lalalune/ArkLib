# Five production candidates with pairwise coprime outside factors

There is an explicit received word on the punctured production domain with
at least five decoded polynomials taking five different values at the hole.
Four have 738197503 punctured agreements and the fifth has 805306367;
the required predecessor threshold is 715827883. Their five outside-domain
factors are nonconstant and pairwise coprime.

This extends the earlier [two-factor example](astra_mca_outside_factor_frontier-2026-09-05.md).
In particular, the bound of three for a
[fixed outside-factor fibre](astra_mca_split_root_rigidity-2026-09-05.md)
cannot become a bound of three on the whole list. No earlier restricted
theorem is contradicted. The unrestricted number of fibres remains open.

The construction is a written proof with a fixed-degree exact certificate
and independent dense polynomial controls. It is **not Lean-formalized or
independently reviewed**. Five bad scalars are far below the production
allowance of 1073741824; this does not improve the known threshold, disprove
the prize security bound, or classify the full production list. No claim
of novelty relative to the literature is made here.

## A general punctured lifting identity

Let g have order ms in a field whose characteristic does not divide ms,
and set eta=g^s, of order m. Take base polynomials V0 and f on mu_m, with
the point 1 omitted, and put

```text
J_s(X)=1+X+...+X^(s-1)=(X^s-1)/(X-1),
V(X)=J_s(X)*V0(X^s), F(X)=J_s(X)*f(X^s).
```

The fibre of eta^j consists of g^(j+mt), for 0<=t<s. On every fibre with
j!=0, J_s is nonzero, so V=F at precisely the lifts of a base agreement.
On the fibre of 1, J_s vanishes at all s-1 points other than 1. Consequently,
if f has exactly a punctured base agreements, then F has exactly

```text
s*a+(s-1)
```

punctured agreements. Also `F(1)=s*f(1)`, preserving distinct values, and
`degree F=s*(degree f+1)-1` for nonzero f. These are algebraic identities
and exact fibre counts, not an extrapolation from small tests.

If `V0-f=Z*Q`, where Z consists of its simple domain roots and Q has no
root on mu_m, then the lifted outside factor is Q(X^s), up to normalization.
Indeed, J_s and the factors `X^s-eta^j` have disjoint simple domain roots;
Q(X^s) has none. Coprimality of two Q polynomials is preserved under this
substitution by composing their Bezout identity.

## The fixed sixteen-point certificate

Use the [certified production field](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean),

```text
P=365375409332725729550921208179070755120141565953,
g=303645430271030343624574566109998498685964493478,
n=2^30, s=n/16=67108864,
eta=g^s, zeta=eta^2, order(eta)=16, order(zeta)=8.
```

In the base variable Y define

```text
R0=(Y+1)*(Y^2-zeta)*(Y^2-zeta^2),
l_i=zeta^i*Y^2+zeta^(-i),       i=0,1,2,3,
f_i=R0*l_i.
```

The punctured domain roots of R0 have exponents `{1,2,8,9,10}`.
Let H be the polynomial of degree at most nine interpolating the following
ten values, and set `V0=R0*H`:

| Exponent j of eta^j | Value H(eta^j) |
| --- | --- |
| 3, 11 | l_2(eta^j) |
| 4, 12 | l_1(eta^j) |
| 5 | l_0(eta^j) |
| 13 | l_1(eta^j) |
| 6, 14 | l_0(eta^j) |
| 7, 15 | l_0(eta^j) |

The relation

```text
l_i-l_j=(zeta^i-zeta^j)*(Y^2-zeta^(-(i+j)))
```

explains the paired agreements. The exact certificate checks the following
complete root sets of H-l_i on mu_16:

| Candidate | Exponents of roots of H-l_i |
| --- | --- |
| 0 | 5, 6, 7, 14, 15 |
| 1 | 4, 7, 12, 13, 15 |
| 2 | 3, 6, 11, 13, 14 |
| 3 | 3, 4, 5, 11, 12 |

Each has five simple roots, disjoint from R0's five. H has degree nine,
so each base error V0-f_i has ten simple domain roots and a degree-four
outside factor. Its value at 1 is nonzero.

### The fifth candidate

Put

```text
C=1-zeta-zeta^2+zeta^(-1),
f_4=C*Y^2*(Y+1)*(Y^2-zeta^2).
```

The exact certificate shows C is nonzero and V0-f_4 has precisely the
eleven simple domain roots with exponents

```text
2,3,4,6,7,8,10,11,12,14,15.
```

Its outside factor has degree three and no domain root. The fifth polynomial
has degree five, whereas the first four have degree seven. The five values
f_i(1) are distinct; the checker computes all five in the actual field.

There is a factorization explaining its eight agreements in the four
unsplit pair cosets. For i=0,1,2,3 respectively let

```text
(a_i,b_i)=(6,7),(4,7),(3,6),(3,4).
```

Then

```text
f_i-f_4=zeta^i*(Y+1)*(Y^2-zeta^2)
                     *(Y^2-zeta^(a_i))*(Y^2-zeta^(b_i)).
```

Together with the earlier difference identity, this shows that every
difference of two different candidates has only domain roots. A common
outside root of their errors would be a root of that difference, which is
impossible. The five outside factors are therefore pairwise coprime even
over an algebraic closure. The checker also verifies all ten polynomial
gcds independently.

## Exact production consequences

Apply the lifting identity with m=16 and s=67108864. The received polynomial
has degree `15s-1=1006632959`, below `n-1`, so it is already the canonical
punctured interpolation polynomial. All five lifted candidate degrees are
below the code dimension `k=n/2=536870912`.

| Candidates | Degree | Punctured agreements | Outside-factor degree |
| --- | --- | --- | --- |
| F_0 through F_3 | 536870911 | 738197503 | 268435456 |
| F_4 | 402653183 | 805306367 | 201326592 |

The first four exceed the predecessor agreement requirement by 22369620.
The lifted outside factors remain pairwise coprime and the five values at
1 remain distinct. Hence the example has at least five different
outside-factor fibres in the actual production punctured list.

For the [exact single-hole MCA reduction](astra_mca_single_hole_reduction-2026-09-05.md),
set u0 equal to this word off 1 and zero at 1, and set u1 to the indicator
of 1. Each candidate contributes its distinct value F_i(1) as an actual
bad scalar at radius 5/16: the first four have `11n/16` agreements after
adding the hole; the fifth has even more. A hypothetical joint direction
polynomial would have at least k zeros on the punctured support and value
one at the hole, contradicting the polynomial root bound. If an exact-size
support is desired, trim the fifth support while retaining the hole.

Thus this construction yields `epsMCA >= 5/P` at that radius. It does not
yield an upper bound on epsMCA. The inequality `5/P < 2^-128` means that
these five witnesses alone do not exceed the security budget; it does not
prove that the radius is secure against other inputs or other witnesses.

A subsequent [polynomial-pencil amplification](astra_mca_five_pencil_amplification-2026-09-05.md)
uses these five candidates to certify 805306374 distinct bad scalars at
radius `5/16+1/2^30`. This still falls below the security numerator budget
of 1073741824. A separate written argument bounds all contributions from
these five pencils by 1014089502 under explicit retained-core assumptions.
Neither result counts all MCA decodings or improves the unsafe-radius bound.

## Reproduction and verification limits

Run

```bash
python3 scripts/probes/astra_mca_five_candidate_lift_check.py
```

The [checker](../../scripts/probes/astra_mca_five_candidate_lift_check.py)
builds H by dense Lagrange interpolation, verifies the difference
factorizations as polynomial identities, divides out all claimed roots,
checks the remaining factors on all sixteen nodes, and checks ten gcds.
The output contains H's coefficients, the outside factors, and the five
production values at the hole.

Separate dense constructions check every coordinate at orders 16,64,256
over P, and at order 64 over F257 and F65537. They check candidate degrees,
exact agreement counts, and parity syndromes on k+1 nodes proving the
same-support no-joint condition. At order 16 over P, exhaustive enumeration
of all 3003 ten-element agreement supports proves that the entire list has
exactly five members and five values. That exact full-list count is asserted
only for the sixteen-point problem.

The production cell expands neither billion-degree polynomials nor the
domain. Its certificate is the fixed-degree arithmetic above plus the
written lifting proof. A Lean formalization and independent mathematical
review remain outstanding. The universal prize bound remains open.
