# Three exceptional decoders sharing k-2 roots force a near-high joint source

Written argument, reviewed by the coordinator and an independent agent;
not Lean formalized. The [review](../../scripts/probes/receipts/astra_firststep_next_20260908/common-root-projective-review.md)
records the exact scope. This uses
the [near-source safety theorem](astra_mca_near_source-2026-09-08.md).

Let n=4s, k=2s, t=3s-1, s>=6. Normalize one joint source to zero, with exact core A of size at least t and outside E=D\A of size m<=s+1. Suppose three distinct bad scalars gamma_i have chosen witness decoders f_i that are nonzero and have a common set R of at least k-2 roots in A.

Any such nonzero decoder can agree with the projected received word on at most k-1 points of A. Its witness therefore uses at least t-(k-1)=s points of E. In particular m is s or s+1; each witness omits at most one point of E, and if m=s it omits none.

Choose exactly k-2 common roots and let G be their monic vanishing polynomial. Each f_i=G L_i with deg L_i<=1. The three witnesses have at least m-3>=s-3>=3 common points of E. At a point matched by two distinct scalars, G cannot vanish: otherwise two distinct projections of the nonzero received pair there would both be zero. Choose two distinct common points x,y in E, so G(x),G(y) are nonzero.

Interpolate two decoders in their scalar parameter: let p,q be the degree-below-k polynomials determined by f_1=p+gamma_1 q and f_2=p+gamma_2 q. The polynomial f_3-p-gamma_3 q is divisible by G, with quotient of degree at most one. It vanishes at x,y because all three received projections agree there. Hence the quotient is zero, and f_i=p+gamma_i q for all three i.

The pair (p,q) vanishes on R. At any point of E appearing in two of the three witness supports, the two distinct scalar equations imply (p,q) equals the received pair. Since at most three outside-point omissions occur in total, at most one point of E can appear in fewer than two supports. Thus if m=s+1 the joint core has size at least

    (k-2)+(m-1)=3s-2=t-1.

If m=s, every witness includes E, and the core has size at least

    (k-2)+m=3s-2=t-1.

The new pair is distinct from zero because its projected decoders are nonzero. Therefore the near-source safety theorem applies at production parameters.

Consequently, in any remaining unsafe singleton instance, three distinct exceptional scalars cannot have chosen decoders sharing k-2 roots in the high core. In particular no projective decoder direction can occur at three exceptional scalars. This excludes a narrow family; it does not bound the total number of different root sets.

## Two exceptions alone do not force the second source

An [exact control](../../scripts/probes/astra_mca_singleton_two_exception_check.py)
uses the actual production prime but a smaller sixteen-point domain. Here
`k=8`, `t=11`, and the zero source is the only joint source with core at least
ten. Nevertheless, two distinct scalars have genuine MCA witnesses of size
twelve. Exhaustive interpolation checks all 6072 candidate nonzero sources;
the [receipt](../../scripts/probes/receipts/astra_firststep_next_20260908/two-exception-toy.json)
records no candidate with core at least ten. This refutes an unrestricted
two-exception forcing shortcut; it is not a production-size counterexample
or a violation of the n-scalar budget.
