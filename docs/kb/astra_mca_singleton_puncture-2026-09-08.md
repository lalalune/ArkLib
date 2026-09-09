# Singleton puncturing reduction and a limit on generic boundary estimates

2026-09-08. Written reduction and exact toy control. The reduced words' low-degree numerator/common-denominator structure is essential and is not discarded below.

The coordinator independently reviewed the reduction and obstruction.
The [portable exact check](../../scripts/probes/astra_mca_singleton_puncture_check.py)
and [receipt](../../scripts/probes/receipts/astra_firststep_next_20260908/puncture-boundary.json)
verify the small control and production parameter arithmetic, not a universal
bound on this structured class. See the
[near-source result](astra_mca_near_source-2026-09-08.md) for the complementary
safety branch.

## Exact singleton reduction

Normalize the unique joint source with core at least t to zero. Let A be its exact zero core and E=D\A, m=|E|<=s+1, with n=4s, k=2s, t=3s-1. At every point of E the received pair (u,v) is nonzero.

A bad scalar outside the zero-source covered set has a chosen nonzero witness decoder f of degree below k. Define E' as its **full** set of outside projection-agreement points:

    E'={x in E:f(x)=u(x)+gamma v(x)}.

Since f has at most k-1 roots on A and its total agreement is at least t, |E'|>=t-(k-1)=s. Thus m is s or s+1. If m=s there is one possible bucket E'=E; if m=s+1 the possibilities are E itself and its s+1 single-point deletions. No other buckets occur.

For a fixed nonempty bucket E', put e=|E'|, let R be its monic vanishing polynomial, and interpolate received components on E' by a,b of degrees below e. Then

    f=a+gamma b+R h,    deg h<k-e.

On A, where R is everywhere nonzero, h agrees with the reduced received word

    u'=-a/R,  v'=-b/R

at at least t-e points. Thus that bucket injects its possible original scalars into the good-scalar set for RS(A,k-e) at agreement threshold t-e.

The reduced instance has **no joint source with core at least t-e**. Such a pair h_0,h_1 would lift to

    p=a+R h_0, q=b+R h_1,

of degrees below k. It would match the original pair on E' and on at least t-e points of A, giving a joint core at least t. It is distinct from zero because E' is nonempty and the received pair is nonzero there. This contradicts singleton uniqueness.

Hence every reduced good scalar is also a reduced original-MCA scalar: no qualifying support can have a joint explanation. The converse mapping may overcount original exceptional scalars, which is harmless for an upper bound. Different buckets can overlap in scalar values, so a sharp global budget should retain those correlations.

## Exact remaining parameter triples

If |A|=t=3s-1 and m=s+1, the two bucket types give

| e | Reduced length | Reduced dimension | Agreement threshold | Errors | Minimum distance |
|---|---:|---:|---:|---:|---:|
| s | 3s-1 | s | 2s-1 | s | 2s |
| s+1 | 3s-1 | s-1 | 2s-2 | s+1 | 2s+1 |

The first row is exactly half the minimum distance: 2*errors=distance. It fails the repository's strict unique-decoding inequality 2*errors<distance. The second row exceeds half the minimum distance by one half-error: 2*errors=distance+1.

If |A|=t+1=3s and m=s, the single bucket has (length,dimension,threshold)=(3s,s,2s-1), errors s+1, minimum distance 2s+1; again 2*errors=distance+1.

The zero source's covered contribution is at most m. A universal bound on a generic reduced instance at these parameters is insufficient if it ignores the special numerator/denominator structure or costs order s per each of order s buckets.

## A generic boundary empty-list example needs a linear scalar budget

This example applies to the first reduced parameter triple, but **does not belong to the structured punctured class**.

Let s>=3, N=3s-1, K=s, T=2s-1. Take N distinct nonzero evaluation points. Partition them into C of size 2s-2 and E_0 of size s+1. Define the received pair to be (0,0) on C and (1,x) at x in E_0.

There is no joint degree-below-s pair with a core of size T. Suppose p,q were one. The polynomial q-Xp has degree at most s and vanishes at every core point, because both kinds of received values satisfy v=xu. Since T=2s-1>s, q=Xp, and therefore deg p<=s-2. If p=0 its core is only C, too small. Otherwise p has at most s-2 roots on C, so a T-point joint core must contain at least s+1 points of E_0. Thus p=1 at all E_0 points; the degree bound forces p=1 identically. Its joint core then has size only s+1<T. Contradiction.

For every x in E_0, the distinct scalar gamma=-1/x has the zero decoder agreeing on C union {x}, of size T. By the previous paragraph no joint pair can explain that support. Thus there are at least s+1 **actual same-support MCA scalars**, while the high-core joint list is empty.

Therefore a constant bound independent of s is false for the generic reduced empty-list problem. This is not an over-budget counterexample, and does not refute the original first-step safety claim.

## Why this example cannot be the structured punctured word

In the true reduction the first component is -a/R, where deg a<e, e is s or s+1, and R has no zero on the reduced evaluation set. If the generic example's first component had that form, a would vanish on all 2s-2 points of C. For s>=3 this is at least s+1>=e, forcing a=0 and contradicting its nonzero values on E_0. Thus the displayed generic example is **provably excluded** from the structured punctured class.

The live question is consequently a bound for these rationally structured, empty-high-core reduced instances, together with joint accounting across the single-point-deletion buckets. No such bound is proved here.
