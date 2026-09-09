# Final small-branch follow-up audit

2026-09-08. Independent mathematical review of
`../02-safety/no-core-followup.md` and `../08-exceptions/two-source.md`.
**PASS as written mathematics with the minor wording fixes below.** These
branch arguments are not Lean formalized by this audit.

## One-point direction and sparse extension

For v supported at one point a with v(a) nonzero, every same-support MCA
witness contains a: otherwise the pair (f,0) jointly explains its support.
All witness decoders, across every scalar, therefore belong to one fixed
punctured polynomial list of length n-1 and agreement threshold t-1.
Pairwise intersections are at most k-1. The exact five-list gap
`s^2-25s+14` is positive for all s>=25. There are at most four decoders,
each fixing a unique scalar from agreement at a. Thus the full bad set has
size at most four, without a hypothesis on the high-core joint list.
The zero direction separately has no bad scalars.

The concrete sparse extension also checks: at most m support coordinates
are removed, giving a fixed polynomial list at threshold t-m. A listed
decoder supplies at most m scalars because an actual MCA witness must meet
the nonzero support. For L=18 and m<=floor(2s/9), its nineteen-list gap is
`15s^2-38s+19-71sm+19m+18m^2`. It decreases on this m interval, and its
endpoint value `(s^2-304s+171)/9` is positive for s>=304. Consequently
the concrete bound is 18m<=n. Subtracting a codeword from the direction
preserves the original event through the corresponding decoder/joint-pair
shift, so the near-codeword version follows.

**Wording correction:** the generalized arbitrary-m criterion must explicitly
assume nonnegative integer L and `0<=m<t`. Without the positive punctured
agreement threshold, the squared expression alone is not a valid list-size
criterion. The stated concrete sparse branch already satisfies this range.
The distance-to-code wording should specify number of differing coordinates.

## Full two-source closure, including the new linear-carrier argument

For two sources, primitive factorization and at least k-2 common core points
force carrier degree d<=1. The core union has at least n-1+d points. Thus
d=0 leaves at most one outside point and d=1 covers the whole domain.

For d=0, divide each exceptional decoder residual by its nonzero constant
carrier projection. This gives a fixed polynomial list on the source union
with at least t-1 agreements. The report's conservative n-coordinate
five-list gap is `s^2-36s+20`, positive for s>=52. Each resulting polynomial
lifts to a valid joint source. A genuine exception must use a nonzero
residual at the single possible outside coordinate, so each of at most four
profiles supplies at most one scalar. The bound `2(s+1)+4<=n` follows.
If the source union is all of D, there are no exceptions.

For d=1, the received word lies on one primitive affine carrier line on all
of D. Every carrier projection T_gamma is nonzero of degree at most one.
One chosen witness for each bad scalar gives a rational profile F_gamma/T_gamma
matching the fixed scalar word on at least t-1 points where T_gamma is
nonzero. Cancellation to a reduced fraction can only add removable points;
it does not invalidate the retained agreement set. Add the two distinct
base profiles 0,H explicitly.

Distinct profiles have a nonzero cross numerator of degree at most k.
Consequently five such profiles would have impossible incidence, with exact
gap `s^2-52s+20>0` for s>=52. There are at most four profiles in total.
Polynomial profiles of degree at most k-2 lift to valid joint sources with
cores at least t-1; the base profiles have cores at least t.

The nonliftable uniqueness argument covers every edge case: for distinct
scalars T_gamma and T_delta are coprime, and at least one is linear. A common
rational profile must then have constant reduced denominator, and multiplying
by the linear T bounds its polynomial degree by k-2. Thus a nonliftable
profile can occur at only one scalar, including the possible scalar with
constant T and a polynomial profile of degree k-1.

If all chosen profiles lift, every bad scalar is a carrier cancellation at
some domain coordinate, giving at most n scalars. Otherwise there are at
most three liftable profiles including both base profiles, and at most two
nonliftable scalar occurrences. Each fixed liftable source contributes at
most its number of noncore coordinates: a witness entirely inside the core
would be jointly explained. The deliberately relaxed combined bound is
`2(s+1)+(s+2)+2=3s+6<=n`. No assumption that an extra source belongs to J is
needed.

**Wording correction for arbitrary fields:** define the profile collection as
a set, without initially calling it finite. Any five distinct members give
the contradiction, which itself proves finiteness and cardinality at most
four. Over the production finite field finiteness is automatic. One chosen
witness per scalar suffices throughout; the report correctly states that
choice and does not need to classify every possible decoder.

## Resulting scope

The full first-step same-support MCA bound now has independently reviewed
written proofs for high-core joint lists of cardinality two, three, or four
(s>=52 covers all three cases). The sparse-direction branch also applies
without a high-core-list assumption. Dense-direction cases with high-core
list cardinality zero or one remain unresolved. None of these arguments
changes the separately kernel-checked production upper-bound theorem into
an exact threshold result.
