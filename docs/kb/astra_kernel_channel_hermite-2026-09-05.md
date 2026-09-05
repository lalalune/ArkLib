# A sharp leading-coefficient contact bound and a stronger quotient estimate

The contact equations impose a stronger leading-coefficient divisibility
condition than the earlier [graded Hermite estimate](astra_colon_2026-09-04.md).
The resulting quotient-kernel upper bound is smaller, but still does not
exclude the binding factor. The proof is elementary, with bounded exact
transcription checks; it is not Lean-formalized.

This continues the [same-kernel descent](astra_kernel_descent_2026-09-04.md)
and [T-cutoff](astra_t_cutoff-2026-09-04.md) analyses. It retains full
nodewise contact conditions, rather than only the scalar budgets discussed
in the [C2 audit](astra_c2_budget_obstruction-2026-09-04.md). The companion
source pin and quotient parameters are those in the linked notes. No
parameter search or phase replay was performed for this result.

## New local coefficient theorem

At one node put t=X-x_i and A=Y-u0_i-Z*u1_i. The contact substitution is
A=v+Rt, with local weights (t,v,R,Z)=(1,2,0,0).

Let P have degree_Y at most h, degree_R at most S, and contact order at least
m at this node. Write its leading Y coefficient as

    [Y^h]P = sum_{j=0..S} C_j(X,Z) R^j.

Then

    (X-x_i)^max(0,m-h-min(h,S-j)) divides C_j(X,Z).       (A)

This strengthens the old exponent max(0,m-2h), with no characteristic
restriction and no assumptions on the received values.

Proof. Decompose P after Y=A+u0_i+Z*u1_i by ordinary total degree d in
(t,A). Write the degree-d piece as

    P_d(t,A,R,Z)=t^d f_d(A/t,R,Z).

This is a polynomial identity after clearing the displayed powers of t.
The polynomial f_d(s,R,Z) has s degree at most h and R degree at most S.
Different d pieces cannot cancel after A=v+Rt, since this substitution
preserves ordinary total degree in (t,v). The coefficient of v^k in the
localized degree-d piece has contact weight d+k. The order-m condition
therefore says exactly that

    (s-R)^ell divides f_d(s,R,Z), ell=max(0,m-d).

This follows by substituting s=R+z and requiring divisibility by z^ell; it
uses polynomial division, not ordinary derivatives or factorial denominators.
If f_d is nonzero, write f_d=(s-R)^ell*g_d. Degrees in each variable are
additive over the coefficient domains, so

    degree_s(g_d)<=h-ell, degree_R(g_d)<=S-ell.

The s^h coefficient of f_d is the s^(h-ell) coefficient of g_d. In
particular, its R^j coefficient can be nonzero only if ell<=h and ell<=S-j.
The leading Y coefficient is unchanged by the translation Y=A+u0_i+Zu1_i.
For its term t^a R^j one has d=a+h. The two necessary inequalities above give

    a>=m-2h, a>=m-h-S+j.

Together with a>=0 these are exactly (A).

The local exponent is sharp using only these degree caps. Put

    k=min(h,S-j), a=max(0,m-h-k),
    P=t^a R^j A^(h-k)(A-Rt)^k.

Its Y degree is h, R degree is j+k<=S, contact order is a+h+k>=m, and its
Y^h R^j coefficient is exactly t^a. Its nonzero highest-weight terms also
all have contact weight a+w*h+(w-1)*j. Thus an improved local exponent
requires additional hypotheses beyond these channel degrees and contacts.

## Stronger Hermite upper bound for the full quotient kernel

Use the box from the existing colon note:

    Xexp+w*Yexp+(w-1)*Rexp < D,
    Yexp+Rexp+Zexp<=T, Yexp+Rexp<=Y, Rexp<=S.

At distinct nodes impose orders m_i, and let V be the full vector space in
this box satisfying those conditions. Define

    H_hj=sum_i max(0,m_i-h-min(h,S-j)),

    U_channel=sum_{h=0..min(T,Y)} sum_{j=0..min(S,Y-h,T-h)}
        (T+1-h-j)*max(0,D-w*h-(w-1)*j-H_hj).

Then dim_K(V)<=U_channel. Filter by the largest Y degree, exactly as in
the existing graded Hermite proof. On each leading-Y slice, theorem (A)
forces every coefficient of R^j Z^z to contain the product of its distinct
node factors, of total X degree H_hj. This bounds that channel's dimension
by its remaining X width. The kernel of each leading-coefficient map is
the preceding Y slice, so summing these dimensions proves the bound.

Since min(h,S-j)<=h, every exponent H_hj is at least the earlier H_h.
Thus this is a valid strengthening of that full-kernel upper bound. It is
not an interpolation rank upper bound used in the wrong direction.

If F universally divides a nonzero full source kernel, the exact contact
colon identity gives the quotient orders m_i=max(0,m_source-nu_i(F)).
Division maps the source kernel injectively into this constrained quotient
box. Hence source_nullity_lower>U_channel would give a contradiction.
No such inequality is obtained below.

## One fixed critical quotient: improvement, but no exclusion

For the current T source, m_source=166 and its nullity lower bound is
228451639. At the binding factor degrees (total,YS,R)=(2364,47,10), use the
conservative contact weight c_min=6160327. The same quotient box as before is

    (D,T,Y,S)=(23944271,4795,182,41), n=262144, w=131071.

Only these two fixed profiles were evaluated:

| Factor order at all nodes | Retained order | Previous upper bound | New upper bound |
|---:|---:|---:|---:|
| 0 | 166 | 110165530464248 | 20556664632356 |
| 34 | 132 | 161783400912266 | 79928722931834 |

The first profile is already excluded by the earlier same-kernel descent
argument; it serves only to compare the estimates. The second is the
surviving arithmetic profile, not a constructed factor or received word.
Its new upper bound still exceeds the source nullity lower bound by
79928494480195. A larger actual c(F) or genuinely stronger source-dimension
information can change the comparison, but those are not supplied here.

The [existing zero-word construction](astra_colon_2026-09-04.md) already
puts 10123425550 independent monomials in this quotient box even with
retained order 166. Thus contact and support information alone cannot give
a uniformly small enough quotient bound. That example fails the far-word
condition and supplies no universal source divisor. A useful further
improvement must exploit those additional hypotheses, not just reduce the
numerical estimate for arbitrary received words.

The subsequent [far-word construction](astra_far_word_kernel-2026-09-05.md)
also rules out repairing that comparison using farness and quotient rank two
alone: both conditions hold while the quotient contains 10121888390
independent polynomials at retained order 166. The selected high-agreement
family and full source-divisor relationship remain additional information.

## Reproduction and scope

Run

    python3 scripts/probes/astra_kernel_channel_hermite_check.py

The [checker](../../scripts/probes/astra_kernel_channel_hermite_check.py)
checks 18 directly expanded small contact matrices over F2,F5,F101,
12 sharp local examples, and the two displayed integer quotient counts.
The matrix implementation is the existing independent monomial-substitution
routine. These finite checks support transcription; the general theorem
rests on the polynomial argument above.

This result strengthens a quotient-kernel estimate that retains the source
contact conditions but does not lower the C2 moving budget, establish
the required global factor-count deficit, or certify a ProtocolClaim.
