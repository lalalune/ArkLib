# CLM-043 prime-quadratic cyclotomic-row transfer, 2026-08-25

Issue context: #466. Intended campaign base: `research/proximity-prize` at
`54007b004040a9cd0964dcb0a2413e86bc60ae8d`.

## Exact statement and boundary

Fix an odd prime `p`, a subgroup `G <= F_p^x` of order `n >= 3` with
`p >= n^4`, and the quadratic character `chi` extended by `chi(0)=0`. Every
`t`-sum below is over `F_p^x`, so `t=0` is excluded. Put

```text
Q = (F_p^x)^2,
C(t) = |tG intersect (1-Q)|,
r(t) = n-1_G(t),
S(t) = sum_(a in G) chi(1-at),
F(t) = sum_(A subset G, |A|=3) prod_(a in A) chi(1-at),
U = sum_(t in F_p^x) F(t)^2.
```

Here `Q` contains the nonzero squares. The exact result is

```text
S(t)=2C(t)-r(t),
6F(t)=S(t)^3-(3r(t)-2)S(t),
U=(1/36) sum_(t in F_p^x) [S(t)^3-(3r(t)-2)S(t)]^2.    (1)
```

This note also expresses `(1)` as a finite row statistic of exact cyclotomic
numbers. Its status is **PROVEN only as this affine-intersection/cyclotomic-row
transfer and reformulation**: the proof is the human derivation below, while
the six-cell package is supporting diagnostic evidence.

## Affine rows retain the inverse-root zero

For fixed nonzero `t`, write `x_a=chi(1-at)`. A zero occurs precisely when
`a=t^(-1)` belongs to `G`, which is equivalent to `t in G`. Therefore

```text
#{a in G:x_a != 0}=n-1_G(t)=r(t).                       (2)
```

No zero is cancelled. A value `x_a` equals `+1` exactly when `1-at` is a
nonzero square. Multiplication by `t` maps `G` bijectively to `tG`, so the
number of positive terms is

```text
#{a in G:1-at in Q}=|tG intersect (1-Q)|=C(t).           (3)
```

The other `r(t)-C(t)` nonzero terms equal `-1`. Subtracting their number from
the positive count gives

```text
S(t)=C(t)-(r(t)-C(t))=2C(t)-r(t).                       (4)
```

When `t in G`, the one inverse-root term contributes to neither side of `(4)`:
it is omitted from `C(t)`, reduces `r(t)` by one, and has character value zero.

## The factor six is exact

Let `e_k` and `p_k` be the elementary symmetric functions and power sums of
the `n` values `x_a`. By definition `F(t)=e_3`. Since every `x_a` lies in
`{0,+1,-1}`, equations `(2)` and `(4)` give

```text
p_1=S(t),    p_2=r(t),    p_3=S(t).
```

The first two Newton identities say

```text
2e_2=p_1^2-p_2,
3e_3=e_2p_1-e_1p_2+p_3.
```

Substitution yields

```text
6F(t)=S(t)^3-(3r(t)-2)S(t).                             (5)
```

Zeros require no exception to Newton's identities. Squaring `(5)` and summing
over the punctured domain gives `(1)`.

## Both cyclotomic parity branches

Choose a primitive root `zeta` of `F_p^x` and write

```text
m=(p-1)/n,    H=G intersect Q,    e=[G:H],    M=em.
```

If `m` is even, `zeta^m` is a square, so `H=G`, `e=1`, and `M=m`. If `m`
is odd, `zeta^m` is a nonsquare; its even powers form `H`, so `e=2` and
`M=2m`. Thus `M` is even in both branches. Set

```text
C_i=zeta^i H                    (indices modulo M),
N_(i,j)=|{x in C_i:1-x in C_j}|.
```

The classes partition `F_p^x`, every class has `|H|` elements, and

```text
G=disjoint_union_(0<=u<e) C_(um).
```

Because every element of `H` is a square and `chi(zeta)=-1`, `chi` has the
constant value `(-1)^j` on `C_j`. Multiplication by an element of `H`
permutes `G`, so `S(t)` is constant on each `C_i`; call its value `S_i`.
For `t in C_i`, multiplication by `t` maps `C_(um)` to `C_(i+um)`. Partition
the nonzero values of `1-at` by their destination class to get

```text
S_i=sum_(u=0)^(e-1) sum_(j=0)^(M-1) (-1)^j N_(i+um,j). (6)
```

If `at=1`, then `1-at=0` lies in no `C_j` and contributes zero to `(6)`, so
the inverse-root zero is retained. The puncture count is

```text
r_i=n-1 for i in {um:0<=u<e}, and r_i=n otherwise.      (7)
```

Combining `(5)`--`(7)` and grouping the punctured field by its `M` classes
gives the exact aggregate reformulation

```text
U=|H| sum_(i=0)^(M-1)
     ((S_i^3-(3r_i-2)S_i)/6)^2.                         (8)
```

The previously localized sixth-moment boundary can be written

```text
D_6=36U+R,    |R|<=87pn^3.
```

Substituting `(8)` is only a transfer of the unresolved nonnegative main
term. This document does not estimate that term.

## Six frozen exact diagnostics

The package
[`scripts/probes/clm043_cyclotomic_row_transfer/`](../../scripts/probes/clm043_cyclotomic_row_transfer/)
contains a closed `case.toml`, canonical integer-only expected output, and two
structurally independent Python 3.11+ standard-library implementations.
The reference implementation directly enumerates every affine row. The
independent implementation builds the cyclotomic classes and `N_(i,j)` rows
first, reconstructs `G`, and evaluates elementary symmetric functions by a
different recurrence.

Both programs exclude `t=0`; count each inverse-root zero; check `(4)`, `(5)`,
and `(8)` row by row; reconstruct the subgroup puncture rows; and verify the
six-cell `D_6` remainder inequality exactly. They agree byte for byte on:

| `(p,n)` | `m` | `e` | `|H|` | `U` | `D_6` | `R=D_6-36U` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `(97,3)` | 32 | 1 | 3 | 93 | 0 | -3,348 |
| `(257,4)` | 64 | 1 | 4 | 964 | 0 | -34,704 |
| `(641,5)` | 128 | 1 | 5 | 6,380 | 0 | -229,680 |
| `(1297,6)` | 216 | 1 | 6 | 25,464 | 64,800 | -851,904 |
| `(1459,6)` | 243 | 2 | 3 | 27,768 | 0 | -999,648 |
| `(2521,7)` | 360 | 1 | 7 | 118,377 | 211,680 | -4,049,892 |

The `(1459,6)` cell exercises the odd-`m`, `e=2` branch; the other five
exercise the even-`m`, `e=1` branch. These finite cells diagnose the algebra.
They are not premises of the proof and do not establish a uniform bound.

From the package directory, reproduce both implementations and compare them
to the frozen certificate with:

```shell
python -c "import hashlib,pathlib,subprocess,sys; r=subprocess.check_output([sys.executable,'reference.py','case.toml']); i=subprocess.check_output([sys.executable,'independent.py','case.toml']); e=pathlib.Path('expected.json').read_bytes(); assert r == i == e; print(hashlib.sha256(e).hexdigest())"
```

The expected SHA-256 is
`6f70178d995425a25109d64bb523879688363ea7c87780a28adda59f099ff7c5`.
`result-manifest.json` binds the case, implementations, and expected result by
SHA-256.

## Related work and collision boundary

The following public artifacts are credited as related context. They are
mathematically distinct and are not proof sources for `(1)`--`(8)`:

- The reviewed [`CLM-015` prime-quadratic sixth-moment localization](https://github.com/lalalune/ArkLib/issues/466#issuecomment-5202902188)
  isolates `D_6` but carries its unresolved scale forward.
- The [scalar-lower-moment campaign note](https://github.com/lalalune/ArkLib/issues/466#issuecomment-4943685700)
  concerns a seventh-order production profile and explains why scalar lower
  moments do not replace joint arithmetic there.
- The [cyclotomic-intersection campaign note](https://github.com/lalalune/ArkLib/issues/466#issuecomment-4944164457)
  concerns higher-order production BGK/cyclotomic intersection constraints,
  not the prime-quadratic row identity proved here.
- The [`CLM-019` affine-image counterexample](https://github.com/lalalune/ArkLib/issues/466#issuecomment-5229078811)
  refutes a broader circularity assertion. No bounded-intersection conclusion
  is inferred here.
- The [HBK ordered-profile note](https://github.com/lalalune/ArkLib/issues/466#issuecomment-4940851816)
  orders multiplicity-aware coset-intersection counts for a distinct HBK seam.
- At the exact campaign base, [`_ANT46ProjectedCharacterNoGo.lean`](https://github.com/lalalune/ArkLib/blob/54007b004040a9cd0964dcb0a2413e86bc60ae8d/ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ANT46ProjectedCharacterNoGo.lean)
  studies projected power-residue character collisions using cyclic Parseval,
  Jacobi modes, and a cyclotomic-class intersection container at the production
  two-power target. That production no-go/socket is distinct from the
  prime-quadratic affine-row transfer here.

## Nonclaims

- No uniform bound on `U`, `DC`, or `D_6` is proved.
- No result for `CLM-016`, the Proximity Gap Grand Challenge, or any prize is
  proved.
- The six finite diagnostics are not an exhaustive proof of the general
  statement and are not a prize-scale computation.
- No all-character or all-finite-field result is asserted.
- No novelty, priority, prize eligibility, authorship, affiliation, conflict
  of interest, license, copyright, award, payment, legal, or financial claim is
  made.
- This artifact is not a formal prize submission and performs no organizer
  communication.
