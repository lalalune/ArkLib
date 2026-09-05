# The degree-six mu16 pair-cover search is empty

The exhaustive search over **F65537** finds no nonzero syzygy of the prescribed
form in any of **378378** normalized partitions. Therefore this field/domain
does not supply the degree-six pair-cover triple needed by
[the pair-cover attack criterion](astra_mca_paircover_target-2026-09-04.md).
The original coefficient matrices also have full rank in characteristic zero,
by the separately justified reduction argument below. This result does not
address larger domains or other positive characteristics.

## Exact finite scope

Take `n=16`, `k=8`, `p=65537>n^4`. The code uses the primitive sixteenth root
`g=3^4096=64`, checks its order, and works on `mu16={g^i:0<=i<16}`. For a set
S of these nodes, write `W_S(X)=product_{x in S}(X-x)`.

Partition the domain into disjoint sets AB, AC, BC of sizes 5,5,6. The requested
syzygy is

```text
(aX+b)*W_AB + (cX+d)*W_AC + lambda*W_BC = 0.              (1)
```

Every triple of codewords of degree at most six with exactly the indicated
pair agreements would produce (1): subtract the first codeword, and factor
each difference by the product of its roots. Conversely, a solution with
exactly two codewords agreeing at every node gives such a triple by taking

```text
f_A=0,  f_B=-(aX+b)W_AB,  f_C=(cX+d)W_AC.
```

A nonzero syzygy must have `lambda!=0`. Otherwise coprimality of W_AB and W_AC,
each of degree five, would force a degree-five polynomial to divide a linear
polynomial, so all four remaining coefficients would vanish. We therefore
normalize lambda to one without losing any solution.

Domain rotation permits assuming `1 in BC`: choose any node of BC and divide
all nodes by it. Substitution and nonzero rescaling preserve the degree bounds
and existence of (1). Swapping AB and AC also preserves existence. Using the
integer mask ordering `AB<AC` therefore covers all cases up to these symmetries.
The resulting number checked is

```text
choose(15,5)*choose(10,5)/2 = 378378.
```

This normalization need not give a unique representative of each rotation
orbit; it only needs to include a representative of every orbit, which it does.

## Solver and independent verification

Put `A=W_AB`, `B=W_AC`, `C=W_BC`, and use ascending coefficient indices. Since
A,B are monic of degree five and C is monic of degree six, the top two
coefficient equations give

```text
c=-1-a,
d=beta-a*Delta_4-b,
Delta=A-B,  beta=B_4-C_5.
```

The remaining equations reduce to

```text
a*(X*Delta-Delta_4*B)+b*Delta = X*B-C-beta*B,              (2)
```

an equality of polynomials of degree at most four. Its two coefficient columns
are independent: a dependence would lift to a nonzero linear-coefficient
relation between the coprime degree-five polynomials A and B. The solver finds
an invertible two-row minor, solves for a,b, and verifies all five equations.
For a hit it also checks all seven original equations and the exact agreement
pattern at all sixteen nodes. No hit occurred here.

The `--cross-check` run independently performs Gaussian elimination on the
**original 7-by-5 coefficient matrix for every partition**, without using (2).
Every matrix has rank five, agreeing with the reduced solver. It also checks
all 12376 degree-five/six root polynomials by evaluation at all sixteen nodes,
including exact absence of roots outside their designated sets. These checks
run under undefined-behavior sanitization and pass.

| Result | Count |
|---|---:|
| Normalized partitions | 378378 |
| Original matrices independently checked | 378378 |
| Rank-five original matrices | 378378 |
| Nonzero syzygies | 0 |
| Exactly-two pair-cover triples from these syzygies | 0 |

## Characteristic-zero corollary

Choose a primitive complex sixteenth root zeta. Every coefficient of every
original matrix belongs to `Z[zeta]`. Since
`Phi_16(T)=T^8+1` and `64^8=-1 mod 65537`, the map `zeta -> 64` defines a ring
homomorphism from `Z[zeta]` to F65537.

For each partition, full rank modulo 65537 supplies a 5-by-5 minor with nonzero
image under this homomorphism. That minor cannot have been zero in `Z[zeta]`.
Thus the original matrix has rank five over Q(zeta), and its rank stays five
over any characteristic-zero field extension. The rotation and swap reductions
used above are valid in characteristic zero as well.

Consequently no degree-six triple with this 5:5:6 full pair-cover pattern exists
on mu16 in characteristic zero. This is an exact consequence of nonvanishing
minors, not an assumption that finite-field behavior approximates characteristic
zero. It supplies no analogous conclusion for another positive characteristic.

## Reproduction and limits

From the repository root:

```sh
clang++ -O1 -g -std=c++17 -fsanitize=undefined -fno-sanitize-recover=all scripts/probes/astra_mca_paircover_search.cpp -o /tmp/astra_mca_paircover_search
/tmp/astra_mca_paircover_search --cross-check
```

The default run omits the independent matrix/root checks but enumerates the same
complete set of partitions. JSON output records the field, nodes, counts, and
any witnesses. Assertions must remain enabled; do not compile with `-DNDEBUG`.

This computer-assisted finite exclusion has not been formalized in Lean. It
does not construct the missing seed, certify any fresh-hole attack, settle the
grand challenge, or justify extrapolating to larger domains. In particular, a
power lift of the partition would retain its unequal 5:5:6 proportions; the
separate attack criterion's assumptions must still be checked for any future
construction.
