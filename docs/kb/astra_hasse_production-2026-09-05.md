# A finite production Hasse search covering every total cap

The exact [order-two local rank formula](astra_hasse_order_two-2026-09-05.md)
does not produce a positive dimension certificate in the bounded production
family below, for **any nonnegative total degree cap T**. This limits a specific
small-multiplicity family. It does not prove interpolants nonexistent and
does not exclude larger multiplicities, other derivative shapes, or other
methods for bounding the full global rank.

The production profile is

```text
n=262144, w=131071, A=181353, p=2130706433,
D=m*A,
1<=m<=24,
0<=S1<=min(12,m), 1<=S2<=min(6,m).
```

There are 1426 derivative-cap/multiplicity profiles. Ranks are calculated
over F_p, and therefore hold unchanged over the companion extension F_(p^6).
These are the same rectangular Y1/Y2 supports and contact weights as the
previous note. Only the total cap T is unbounded in this check.

## Removing the infinite T search exactly

For a monomial X^a Y0^i Y1^j Y2^k Z^z, let h=i+j+k. Positive global
X width requires (w-2)*h<D. Thus no h above

```text
H=floor((D-1)/(w-2))
```

contributes; here H<=33. Let C_h be the global coefficient count at a fixed
h and one admissible z, and R_h the exact local rank at that same slice.
Their formulas are

```text
C_h=sum_(j<=S1,k<=S2,j+k<=h)
      max(0,D-w*(h-j-k)-(w-1)*j-(w-2)*k),
R_h=sum_(r<m+h, r+(w-2)*h<D) rank M_(h,r).
```

The small matrices M_(h,r) are defined and independently checked in the
order-two note. Each allowed h has T+1-h possible Z exponents, so with
b_h=C_h-n*R_h the dimension surplus is exactly

```text
Delta(T)=sum_(h<=min(T,H)) (T+1-h)*b_h.
```

For all T>=H this is the affine function

```text
Delta(T)=(T+1)*B-M,
B=sum_(h=0..H) b_h, M=sum_(h=0..H) h*b_h.
```

Consequently it suffices to test T=0,...,H and the slope B. In every
enumerated profile the finite tests are nonpositive and B is strictly
negative. All larger T then fail the same strict dimension inequality.
The largest B in the family is -242369; this is a surplus slope, not a
numerical upper bound on the actual interpolation kernel dimension.

## Calibration and scope

The same slice decomposition with Y2 cap zero recovers the existing
first-derivative production source at m=166,S1=51: the first passing total
cap is T=7159, with surplus 228451639. Thus the small order-two failure
does not suggest that the production interpolation problem itself has no
nonzero source. The established source lies outside the searched m range.

To use a positive higher-derivative source, a future argument would still
need a quantitative root/factor analysis and the complete protocol bridge.
Neither increasing the number of source coefficients nor finding a positive
surplus alone would certify a new prize score.

## Reproduction

Run `python3 scripts/probes/astra_hasse_production_check.py`.
It regenerates all 1426 profiles, compares 16 slice counts with the earlier
direct count API, verifies the unbounded-T argument's premises, and reproduces
the first-derivative calibration. Its output includes a digest of the full
ordered profile vector. No production global matrix or decoded list is
enumerated, and this check is not Lean formalization.
