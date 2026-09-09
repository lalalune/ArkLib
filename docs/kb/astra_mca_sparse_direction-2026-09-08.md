# Bounded follow-up: the singleton spike is safe, and a sparse-direction branch

2026-09-08. Written proofs, independently reviewed with no gap found; no Lean verification. Parameters are `n=4s`,
`k=2s`, `t=3s-1`, with the actual production `s=2^28` and prime P.

## Full singleton-spike theorem

For **any field, distinct evaluation domain D, arbitrary received word u,
and direction v supported at one point a**, the full original-MCA bad set
at threshold t has size at most **four**, provided `s>=25`.
The value v(a) can be any nonzero field element. No assumption on J, the
full high-core pair list, is needed.

Proof. Every original MCA witness (gamma,S,f) must include a. Otherwise
v is zero on S and the codeword pair (f,0) explains (u,v) on that same
support, contradicting badness. Delete a. The decoder f agrees with the
fixed word u on at least `t-1` points of `D\{a}`, which has length `n-1`.
Distinct codeword polynomials still have at most `k-1` joint agreement
points on this punctured domain.

If five distinct decoders occurred, the incidence/Johnson inequality would
force

    5(t-1)^2 <= (n-1)((t-1)+4(k-1)).

Its left side minus its right side is exactly

    s^2-25s+14 > 0  (s>=25).

Thus at most four distinct witness decoders can occur across **all gamma**.
For each f, agreement at a fixes the only possible scalar

    gamma=(f(a)-u(a))/v(a).

Therefore the full bad set has size at most four.

This bounds the actual spike counterexample from the [first-step note](astra_mca_first_step-2026-09-08.md): its J is
the singleton {(0,0)}, it has at least the two distinct bad scalars 0 and
-c(a), and **at most four bad scalars in total** at production parameters.
It follows that its MCA probability is at most 4/P, far below 2^-128.
The argument does not claim an exact two-scalar census at production.

## A full bound for directions near a codeword, including J empty

More generally, suppose v is supported on E with m points. Every bad
witness must meet E. Its decoder belongs to the single fixed punctured
list of codewords agreeing with `u|_(D\E)` on at least `t-m` points.
Each listed decoder contributes at most m scalars, since some point
x in E lies in its bad support and agreement there fixes gamma uniquely.
Consequently, for an integer L>=0 and 0<=m<t such that

    (L+1)(t-m)^2 > (n-m)((t-m)+L(k-1)),

the full bad count is at most `L*m`.

At the first step, a concrete production-safe choice is **L=18** and
`m<=floor(n/18)`, provided `s>=304`. Indeed the positive-gap expression is

    19(t-m)^2-(n-m)((t-m)+18(k-1))
      =15s^2-38s+19-71sm+19m+18m^2.

It decreases in m throughout `0<=m<=2s/9`; its value at m=2s/9 is

    (s^2-304s+171)/9 > 0.

Thus the punctured list has at most 18 decoders and

    |B| <= 18m <= n.

For m=0, the direction itself is zero and no MCA witness exists.
Subtracting a codeword from v preserves the original same-support MCA
predicate: the witness decoder changes from f to f-gamma*q, while joint
explainability changes by the same codeword shift. Hence this safety
branch holds whenever **dist(v,C)<=floor(n/18)**. The same argument can
be applied after subtracting an arbitrary source's second polynomial.

This covers some received pairs with J empty as well as singleton pairs.
It does not cover every singleton: after subtracting its source, the
direction can still have s or s+1 nonzero coordinates, beyond this
punctured Johnson range.

## Remaining boundary

No universal bound for dense-direction J empty or arbitrary singleton J
was obtained. The low-cofactor statement alone does not resolve the
large choice of root subsets. For the spike family those choices are
controlled by one fixed punctured decoder list; that simplification is
valid because all scalar variation lies at a single coordinate. It is
not being assumed for a general received line.

The script checks exact production arithmetic and performs a complete
root-subset census for the specific spike construction at n=8 and n=16,
using the actual production prime and corresponding subgroup generators.
These small-s controls are not used to infer production safety: the
written punctured-list theorem supplies that guarantee.
