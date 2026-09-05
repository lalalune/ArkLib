# A necessary multiplicity condition for two-point deletion anchors

This is an exact screening condition for the
[two-generator deletion construction](astra_mca_two_generator_bridge-2026-09-04.md).
It does not exclude the asymmetric recursive production partition.

Start with a full pair partition and two balanced local triples of product
degree n/2. Every original coordinate x has one nonzero residual row R(x)
against its missing core. Let xi be in AB and eta in AC, with distinct
old projective directions. Normalize the old basis so that column 1
vanishes jointly at eta and column 2 vanishes jointly at xi. Divide the
columns by X-eta and X-xi, respectively, and make xi,eta private to A.

Let M_xi and M_eta be the multiplicities of their old projective directions
among all n original residual slots. At every surviving coordinate x,
the new residual row is

```text
(R_1(x)/(x-eta), R_2(x)/(x-xi)).
```

For an old direction equal to R(xi), the second coordinate is zero and
the first nonzero. There are M_xi-1 such surviving slots. They all
have direction (1,0). The new private-C slot at eta also has direction
(1,0): its second local G polynomial still vanishes at eta, while its
first is nonzero after division. The latter nonvanishing follows from
the two-generator determinant at the private point.

Likewise the M_eta-1 surviving old slots in the R(eta) direction, together
with the new private-B slot at xi, all have direction (0,1). These are
two disjoint collision classes of sizes M_xi and M_eta. There may be
additional slots in them and additional collisions elsewhere.

Consequently the number b of distinct new directions satisfies

```text
b <= (n+2) - (M_xi-1) - (M_eta-1)
  = n+4-M_xi-M_eta.
```

To reach n+1 directions it is necessary that `M_xi+M_eta<=3`.
In particular, at least one anchor must have a globally unique old
residual direction. To reach all n+2, both must have unique directions.
A constant change of basis cannot alter this condition.

## Why balanced degrees and quarter-coset structure alone are insufficient

Take a full partition and balanced basis on mu_N, and power-lift them by
X to X^d onto mu_(Nd), with d>=2 and the required roots in the field.
The pair locators and both primitive generators are compositions with
X^d; their minimal product degrees multiply by d. The last assertion
also follows by separating the coefficient residues modulo d: a smaller
lifted syzygy would yield a smaller nonzero seed syzygy.

Each fibre of X^d lies in one pair region and has d points with the same
old residual direction. Thus every old direction has multiplicity at
least d. Any valid deletion anchor pair therefore satisfies

```text
b <= Nd+4-2d <= Nd.
```

If the original partition used three whole quarter cosets and a split
fourth coset, its power lift still has that architecture. This gives a
counterexample mechanism to a general guarantee based only on that
architecture and balanced generator degrees.

The exact production profile is not such a pure lift: its original
AB and AC sizes `(n-1)/3` are odd for n=4^r and cannot both be divisible
by a nontrivial power of two. Its final recursive asymmetry can break
the repeated directions. No collision or nonexistence claim for that
specific production construction follows from this note.

This argument is an ordinary algebraic proof, not a Lean formalization.
