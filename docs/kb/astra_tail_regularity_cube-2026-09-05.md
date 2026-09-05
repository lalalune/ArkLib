# The fixed regularity cube does not supply the missing budget reduction

Every raw contact tail N_d, for d>=2, has an exact polynomial factor H^3,
where H=F_R. Removing it preserves the regular first-tail components and
their multiplicities. However, its degree bounds lose the R-degree
improvement already present in the companion's reduced representative.
At the binding flag, the resulting first-tail/rational cost is larger by
2926707573042415. Simply removing the cube and using that representative
therefore does not improve the current bound.

The cube also cannot be replaced by a universally increasing power of H:
an irreducible surface at the binding degree flag, with a regular selected
polynomial solution, has exactly H-adic order three at both production
tail indices. This surface is not claimed to come from the full
interpolation kernel. The result does not rule out a correction using
that stronger provenance or another boundary component.

These are written identities, degree bounds, and exact controls. They do
not provide a new prize allowance. Independent review and Lean integration
remain outstanding.

## The raw tail recurrence and its cube

Use the companion definitions `RCN313.polyH`, `polyG`, `numeratorStep` and
`numerator` from
[`PackedLegacyCore1.lean`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLegacyCore1.lean).
Let

```text
H=F_R, G=-F_X-R*F_Y,
V=H*(partial_X+R*partial_Y)+G*partial_R.
```

V is a polynomial derivation and V(F)=0. The companion recurrence is

```text
N_0=Y,
N_(d+1)=H*V(N_d)-2d*N_d*V(H).
```

It gives N_1=H^2*R and N_2=H^3*G. Define

```text
M_2=G,
M_(d+1)=H*V(M_d)-(2d-3)*M_d*V(H), for d>=2.              (1)
```

Then, as a polynomial identity before restricting to F=0,

```text
N_d=H^3*M_d, for every d>=2.                             (2)
```

The induction substitutes (2) in the raw recurrence and uses
`V(H^3)=3H^2*V(H)`. It works over any commutative coefficient ring; the
integer coefficients can be reduced modulo the characteristic.

On the regular surface, the derivation is D=V/H. Hence

```text
D^d(Y)=N_d/H^(2d)=M_d/H^(2d-3).
```

The source's `globalTailCut` is N_d times the nonzero coefficient-field
scalar `(-X)^d`. Since H is a unit on every regular component, replacing
that cut by M_d preserves the component set and its divisor multiplicities
there. It does not preserve every ambient polynomial support bound.

## Exact order three at the excluded regularity locus

Reducing (1) modulo H and using `V(H)=H*(H_X+R*H_Y)+G*H_R` gives

```text
M_d = (-1)^(d-2)*(2d-5)!!*G^(d-1)*H_R^(d-2) modulo H,    (3)
```

where (-1)!!=1. If H is squarefree and coprime to G*H_R, and the displayed
integer coefficient is nonzero, then M_d is coprime to H. Thus H^3 divides
N_d and H^4 does not. More generally (3) describes the surviving residue
at each component of H=0 where G and H_R remain nonzero.

Here is a binding-flag example over characteristic p=2130706433:

```text
F=R+R^10+X*Y+Y^47+Z^2364,
H=1+10R^9,
G=-Y-XR-47R*Y^46.
```

Its cumulative R, YR and total degrees are exactly 10,47,2364, giving
raw flag (z,v,r)=(2317,37,10). It is irreducible over K[X,Y,R,Z]: view it
as primitive linear in X, with coefficient Y and constant term not
divisible by Y. It is also geometrically irreducible over K(X) as a
polynomial in Y,R,Z. Over the algebraic closure of K(X)(Z), give Y weight
10 and R weight 47; the leading part is Y^47+R^10. This binomial is
irreducible because 47 and 10 are coprime, and every other term has smaller
weight. Primitivity then gives the claimed irreducibility.

The selected polynomial f=0 at gamma=0 lies on F and has H=1. With u0=0
at all nodes it agrees everywhere. This gives a regular selected solution,
but does not assert an MCA-bad received line, a large family, or universal
full-kernel provenance for this binding example.

H has nine distinct nonzero roots. At any root R=r0, H_R is nonzero. On
F=0,H=0, the polynomial G is independent of Z and nonzero as a polynomial
in Y over K(X), whereas F remains monic of degree 2364 in Z. No curve
component of F=0,H=0 can therefore be contained in G=0: imposing G=0
leaves only finitely many Y and Z values. Thus (3) is nonzero on every
such curve component. H is reduced there: at a generic point Z is nonzero,
so F_Z=2364Z^2363 is nonzero, and the R derivative H_R is a unit. The
gradients of F and H are therefore independent over K(X).

At both d=131072 and d=131073, every factor in (2d-5)!! is below p and
nonzero. Consequently the raw tail has exactly order three along these
regularity-boundary curves. In particular it has no fourth H factor even
in the surface coordinate ring. The generic order does not grow with the
tail index in this example.

## Degree cost of the primitive representative

Suppose F has cumulative bounds r>=2, y>=r+1 and t>=y. Directly from
(1), the bounds on M_d are

```text
R degree     <= (2r-1)d-3r+3,
YR degree    <= (2d-3)(y-1)+1,
total degree <= (2d-3)(t-1)+1.                            (4)
```

For d=2 these are the bounds r+1,y,t on G. Applying V and then multiplying
by H, or multiplying by V(H), increases the R bound by at most 2r-1 and
the other two bounds by at most 2y-2 and 2t-2, respectively. This proves
(4) by induction. Put z=t-y,v=y-r. The resulting raw flag is

```text
((2d-3)z, (2d-3)v-d+1, (2r-1)d-3r+3).
```

Equivalently, it is the sharp raw-tail flag minus three copies of
(z,v,r-1). In contrast, C2 uses the reduced representative with raw flag
`(2dz,1+2dv,2d(r-1))`. At d=131072 the exact comparison is:

| Quantity | C2 reduced representative | M_d representative |
|---|---:|---:|
| Raw z | 607387648 | 607380697 |
| Raw v | 9699329 | 9568146 |
| Raw r | 2359296 | 2490341 |
| First-tail/rational mixed cost | 178395282264909660 | 181321989837952075 |

Holding the rational flag and moving contribution fixed, the replacement
increases the singleton allowance by 2926707573042415. The fixed savings
in total and YR degree do not compensate for the lost reduction in R.
This comparison is for these two explicit support bounds, not a proof
that every representative of the same regular divisor has this cost.

## Why the cube cannot just be subtracted from the reduced flag

The source's `RCN262.reducedNumerator` in
[`PackedLegacyCore2.lean`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLegacyCore2.lean)
subtracts multiples of F at each derivative step. Its residue on F=0
equals N_d, but as an ambient polynomial it need not be divisible even
by H, let alone H^3.

For F=R+R^2+XY+Y^3+Z^4, at d=2 and the point
`(X,Y,R,Z)=(0,1,-1/2,0)`, H=0 while the reduced numerator is -3. This is
checked in characteristics 17,257,2130706433. The point need not lie on
F=0: it certifies failure of **ambient polynomial divisibility**, which
is the property needed to subtract weighted degrees by taking a quotient.
Divisibility in the localized surface ring is insufficient for that step.

As an arithmetic stress test, even grant a simultaneous subtraction of
three copies of the maximum H flag from the already reduced first-tail
flag and from the moving-cut flag. Keep the other flags fixed. The
hypothetical saving is

```text
first-tail/rational: 2041571922705,
moving contribution: 2315973717288,
total:               4357545639993.
```

The result still exceeds the binding-cell target 266264875801744582 by
17134479015057497. This grant is not a proved geometric bound and is not
an upper bound on all possible boundary corrections. It only measures
this specific fixed-cube proposal. A successful correction must use more
than this removal, or retain the reduced support through an additional
argument.

## Exact checks and remaining scope

Run:

```sh
python3 scripts/probes/astra_tail_regularity_cube_check.py
```

The checker independently expands the raw recurrence and (1), comparing
N_d with H^3*M_d through d=7 in three characteristics. It also checks the
binding sparse polynomial through d=4 and transcribes the companion's
reduced recurrence to test its R-degree bound and nondivisibility.

For the production-index residue check, set Y=1,Z=0 and solve
X=-R-R^10-1 on F. Work modulo H=1+10R^9, where
`G=(9/10)R^2-46R-1`. The checker verifies that H is squarefree and G,H_R
are invertible modulo H. Binary powering evaluates (3) exactly at both
production indices; it does not construct the enormous full tail. The
signed double-factorial coefficients are respectively 271401217 and
1032078706, and both resulting residues are coprime to H.

The probe also reproduces the representative-cost comparison and the
explicit arithmetic grant. No full-kernel binding example, improved phase
recurrence, independent review, Lean theorem, or prize proof is supplied.
