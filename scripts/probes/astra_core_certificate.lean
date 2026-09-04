/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Std

/-!
# Core-only arithmetic certificate for the order-eight monomial census

Kernel checked with Lean 4.30.0-rc2 on 2026-09-04; the axiom audit reports only
`propext`. This file uses ordinary kernel `decide`, not `native_decide`, and needs
no Mathlib. It recomputes all 70 four-point supports and all 64 monomial pencils.
The run receipt is `docs/kb/astra-core-certificate-2026-09-04.md`.

The theorem certifies a finite arithmetic predicate. The proof that this predicate
implies the field-uniform MCA statement is documented separately in
`docs/kb/proximity-astra-monomial-census-2026-09-04.md`; that general algebraic
specialization argument is not formalized in this core-only file.

Run with a Lean 4 toolchain: `lean scripts/probes/astra_core_certificate.lean`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace AstraCoreCertificate

/-- Coordinates in the free integer algebra with the sole relation z^4=-1. -/
structure Z4 where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
  deriving BEq, DecidableEq, Repr

def zero : Z4 := ⟨0, 0, 0, 0⟩
def one : Z4 := ⟨1, 0, 0, 0⟩
def z : Z4 := ⟨0, 1, 0, 0⟩

def add (a b : Z4) : Z4 :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩

def neg (a : Z4) : Z4 := ⟨-a.c0, -a.c1, -a.c2, -a.c3⟩
def sub (a b : Z4) : Z4 := add a (neg b)

def mul (a b : Z4) : Z4 :=
  ⟨a.c0*b.c0 - a.c1*b.c3 - a.c2*b.c2 - a.c3*b.c1,
   a.c0*b.c1 + a.c1*b.c0 - a.c2*b.c3 - a.c3*b.c2,
   a.c0*b.c2 + a.c1*b.c1 + a.c2*b.c0 - a.c3*b.c3,
   a.c0*b.c3 + a.c1*b.c2 + a.c2*b.c1 + a.c3*b.c0⟩

def pow (a : Z4) : Nat → Z4
  | 0 => one
  | n+1 => mul (pow a n) a

/-- The same antipodal-squaring norm polynomial used by G330. -/
def norm (c : Z4) : Int :=
  let a0 := c.c0*c.c0
  let a1 := 2*c.c0*c.c2 - c.c1*c.c1
  let a2 := c.c2*c.c2 - 2*c.c1*c.c3
  let a3 := -(c.c3*c.c3)
  a0*a0 - (2*a0*a2-a1*a1) + (a2*a2-2*a1*a3) + a3*a3

/-- A positive power of two, including 1=2^0. -/
def twoPower (n : Nat) : Bool :=
  decide (0 < n) && ((n &&& (n-1)) == 0)

def hasTwoPowerNorm (a : Z4) : Bool := twoPower (norm a).natAbs

structure Support where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving Repr

def supports : List Support :=
  (List.range 8).flatMap fun a =>
    (List.range 8).flatMap fun b =>
      (List.range 8).flatMap fun c =>
        (List.range 8).flatMap fun d =>
          if a < b ∧ b < c ∧ c < d then [⟨a,b,c,d⟩] else []

structure FourCoeffs where
  c0 : Z4
  c1 : Z4
  c2 : Z4
  c3 : Z4

/-- Elementary symmetric coefficients of the four selected roots. -/
def elementary (s : Support) : FourCoeffs :=
  let a := pow z s.a
  let b := pow z s.b
  let c := pow z s.c
  let d := pow z s.d
  ⟨add (add a b) (add c d),
   add (add (add (mul a b) (mul a c)) (add (mul a d) (mul b c)))
     (add (mul b d) (mul c d)),
   add (add (mul (mul a b) c) (mul (mul a b) d))
     (add (mul (mul a c) d) (mul (mul b c) d)),
   mul (mul a b) (mul c d)⟩

/-- Multiply by X modulo X^4-e1*X^3+e2*X^2-e3*X+e4. -/
def nextRemainder (e r : FourCoeffs) : FourCoeffs :=
  ⟨neg (mul e.c3 r.c3),
   add r.c0 (mul e.c2 r.c3),
   sub r.c1 (mul e.c1 r.c3),
   add r.c2 (mul e.c0 r.c3)⟩

abbrev Vec2 := Z4 × Z4

def remainders (s : Support) : List Vec2 :=
  let e := elementary s
  let rec go : Nat → FourCoeffs → List Vec2
    | 0, _ => []
    | n+1, r => (r.c2,r.c3) :: go n (nextRemainder e r)
  go 8 ⟨one,zero,zero,zero⟩

def det (a b : Vec2) : Z4 := sub (mul a.1 b.2) (mul a.2 b.1)

structure AuditState where
  labels : List Vec2
  valid : Bool

/-- One support either excludes a scalar or gives an exact numerator/denominator.
All duplicate and distinct-label comparisons are checked, not just a sample. -/
def addSupport (a b : Nat) (state : AuditState) (rs : List Vec2) : AuditState :=
  let ra := rs[a]?.getD (zero,zero)
  let rb := rs[b]?.getD (zero,zero)
  let determinant := det ra rb
  if determinant != zero then
    { state with valid := state.valid && hasTwoPowerNorm determinant }
  else if rb == (zero,zero) then state
  else
    let denominator := if rb.1 != zero then rb.1 else rb.2
    let numerator := if rb.1 != zero then neg ra.1 else neg ra.2
    let candidate := (numerator,denominator)
    let identity :=
      (add (mul ra.1 denominator) (mul numerator rb.1) == zero) &&
      (add (mul ra.2 denominator) (mul numerator rb.2) == zero)
    let separation := state.labels.all fun previous =>
      let difference := det candidate previous
      (difference == zero) || hasTwoPowerNorm difference
    let duplicate := state.labels.any fun previous => det candidate previous == zero
    ⟨if duplicate then state.labels else state.labels ++ [candidate],
     state.valid && hasTwoPowerNorm denominator && identity && separation⟩

def pairAudit (rs : List (List Vec2)) (a b : Nat) : AuditState :=
  rs.foldl (addSupport a b) ⟨[],true⟩

def expectedProfile : List (List Nat) :=
  [[0,0,1,1,1,1,1,1],
   [0,0,1,1,1,1,1,1],
   [0,0,1,0,4,8,4,0],
   [0,0,0,1,8,4,0,4],
   [0,0,5,9,1,8,5,9],
   [0,0,9,5,8,1,9,5],
   [0,0,4,0,4,8,1,0],
   [0,0,0,4,8,4,0,1]]

/-- Exact roots remain distinct after every specialization certified by their norms. -/
def rootAudit : Bool :=
  (pow z 4 == neg one) && (pow z 8 == one) &&
    (List.range 8).all fun a =>
      (List.range 8).all fun b =>
        if a < b then hasTwoPowerNorm (sub (pow z a) (pow z b)) else true

/-- The finite predicate recomputes all supports and candidates from their indices. -/
def audit : Bool :=
  let rs := supports.map remainders
  let results := (List.range 8).map fun a => (List.range 8).map fun b => pairAudit rs a b
  let profile := results.map fun row => row.map fun result => result.labels.length
  (supports.length == 70) && rootAudit &&
    (results.all fun row => row.all fun result => result.valid) &&
    (profile == expectedProfile)

/-- Kernel-checkable finite arithmetic certificate; not a formal field-specialization theorem. -/
theorem certificate : audit = true := by decide

#print axioms certificate

end AstraCoreCertificate
