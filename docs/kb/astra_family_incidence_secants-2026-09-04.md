# Shared contacts, contained secants, and a weighted family bound

Status: a written global lemma with reproducible arithmetic checks; not a
Lean theorem or a C2 score improvement. The lemma connects shared node contacts
to lines on the generic surface. Its necessary inequality still admits the
order-34 profile that survives the other repair tests.

## Hypotheses and source scope

Let K have characteristic p and let Ω be an algebraically closed extension of
K(X). In particular, polynomial identities remain identities under the chosen
embedding; specialization of X to an algebraic value is not allowed here.
Let F be nonzero, with actual contact weight `c=c(F)` for weights
`(X,Y,R,Z)=(1,w,w-1,0)`, and node contact orders ν_i at distinct x_i, using
the received affine values `u0_i+Z u1_i`. Assume `w≥1`.

Let G be an irreducible component of F over Ω in coordinates (Y,R,Z), with
joint YR degree at most Y. **Assume G is not an affine plane.** For distinct
seeds γ in a finite set Γ, suppose selected polynomials fγ satisfy:

- `degree(fγ)≤w` and `F(X,fγ,fγ',γ)=0`;
- the generic points `(fγ,fγ',γ)` lie on G and have `∂RF≠0`;
- any affine polynomial pencil `P0+γP1`, with both degrees at most w, contains
  at most e+1 selected seeds.

These are the relevant solution, regularity, component, and no-large-pencil
fields of `RCN159.ResidualStage` (`PackedLegacyCore1.lean:19154`) and
`NoLargeSelectedPencil` (`:3647`) at companion snapshot
`032154395c51fd6f77715a7f42d9a987ab9fb48a`. The non-plane condition must be
checked on the actual geometric component; loose support upper bounds alone
do not establish it. Nor does full-kernel universality automatically pass to
a transformed factor after identity stripping or projection.

Write `L=|Γ|`, `d_i=|{γ : fγ(x_i)=u0_i+γu1_i}|`, and `S=Σ_i ν_i`. Then

```
2 Σ_i ν_i binom(d_i,2)
  ≤ c L(L-1) + max(0,S-c) L Y e.                         (1)
```

## Proof: heavy shared contacts force a contained secant

Fix distinct γ,δ. Their selected polynomials determine a unique pencil
`Π(X,Z)=P0(X)+ZP1(X)`, with Π(X,γ)=fγ, Π(X,δ)=fδ and `degree_X Π≤w`.
Substitute it into F:

```
B(X,Z)=F(X,Π(X,Z),∂XΠ(X,Z),Z),       degree_X B≤c.
```

At a common agreement node, the two affine polynomials in Z agree at γ and δ,
so `Π(x_i,Z)=u0_i+Z u1_i` identically. In local contact coordinates,

```
v=Π(x_i+τ,Z)-Π(x_i,Z)-τ ∂XΠ(x_i+τ,Z)
```

is divisible by τ². Hence `(X-x_i)^ν_i` divides B. Distinct nodes give coprime
factors. Therefore, if `Σ_{i common}ν_i>c`, then B is identically zero.

Its generic image is the secant line through the two selected points, with
nonzero Z direction. This line lies on G, not just on the union defined by F:
write F=GQ. At a selected point, `∂RF=(∂RG)Q≠0`, so Q is nonzero there. Since
G and Q restrict to polynomials on an integral line and their product vanishes
identically, Q cannot vanish identically and G must do so.

Consequently every secant not contained in G has shared contact sum at most c.
This step uses the actual c(F), not its lower bound from the flag.

## Proof: at most Y relevant lines through each regular point

At a selected point P, the preceding product rule also gives `∂RG(P)≠0`.
Normalize a line's Z direction to 1. A contained line must be tangent, so its
direction is `(b,αb+β,1)`, where α,β are fixed by the tangent equation at P.
Expand

```
G(P+T(b,αb+β,1)) = Σ_j q_j(b) T^j.
```

Every q_j has degree in b at most Y, since only the Y and R substitutions
involve b. At least one q_j is nonzero. Otherwise G would vanish on its entire
tangent plane: the parametrization covers the plane away from `Z=P_Z`, and
the same conclusion follows algebraically from injectivity of the substitution
`(s,t)↦(bt,t)`. The tangent plane's linear equation would then divide the
irreducible G, contradicting the non-plane assumption.

Choose a nonzero q_j. There are at most Y roots b and thus at most Y contained
lines with nonzero Z direction through P. Any such line containing a second
selected point gives the polynomial pencil constructed above, so it contains
at most e+1 selected points. Each selected point therefore has at most Y e
other selected points on contained secants. The number E of exceptional
unordered pairs obeys `2E≤L Y e`.

Double-count weighted common agreements. Ordinary pairs contribute at most c;
exceptional pairs at most S. Using the bound on E proves (1).

## What the inequality does and does not buy at the binding flag

Take `n=262144`, `a=181353`, `w=131071`, `e=80791`, `Y=47`.
The contained-secant neighbor bound is `Y e=3797177`. The regular-solution
incidence inequality from the derivative-repair note is also available:

```
Σ_i max(0,ν_i-1) d_i ≤ (c-w+1)L,      Σ_i d_i≥aL.
```

For the arithmetic profile `ν_i=34`, balanced incidence fractions `d_i/L=a/n`
give the limiting ordinary-pair contribution

```
34 a²/n = 559111480353/131072 ≈ 4265682.07 < 6160327.
```

Thus (1) remains consistent for arbitrarily large aggregate family sizes,
even as its exceptional-pair correction tends to zero after normalization.
The H-incidence condition also passes, by 44608 at `c=6160327`. The script
checks exact integral aggregate profiles with L a multiple of n, both at this
conservative weight and at `c=47w=6160337`; the existing full-weight, R-free,
cap-nine, and derivative repair inequalities also pass at both values.
These are scalar profiles, not constructed incidence matrices, selected
families, or universal factors. A larger actual c can strengthen interpolation
repair, so this calculation is not a uniform claim for every possible c.

For comparison, ordinary triple agreement counting gives

```
3 Σ_i binom(d_i,3)
 ≤ 3w binom(L,3) + (n-w)(e-1) binom(L,2).
```

A non-pencil triple has at most w common nodes; the number of pencil triples
is at most `(e-1)binom(L,2)/3`. Its limiting left side also passes, since
`a³/n²≈86794.94<w`. This comparison includes the actual pencil cap e+1,
rather than assuming every triple is outside a pencil.

The weighted secant lemma is a genuine shared-family restriction, but it does
not lower the current generic moving-tail allowance. A successful next step
must control more than these first shared-incidence moments—for example a
stronger multiplicity attached to non-contained secants, or restrictions on
the simultaneous contact profiles of actual selected solutions. No such
additional conclusion is asserted here.

Reproduce: `python3 scripts/probes/astra_family_incidence_secants.py`.
The finite checks include nine sharp examples of the elementary line-count
bound; the general geometric proof above is not inferred from those examples.
