/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Current

/-!
# Finite concurrent execution summaries

This file lifts the one-step concurrent interface of `Concurrent.Current` to
whole finite traces.

The earlier concurrent modules provide:

* `Trace S`, a finite scheduler linearization of frontier events;
* `Control`, which says who controls each current decision;
* `Profile`, which says what each party can observe from each frontier event;
* `Current`, which combines those two structural layers into the local view of
  the **next** frontier event.

The present file packages those stepwise notions along an entire finite trace.

Main definitions:

* `Trace.currentControllers` — the current controlling party at each trace step;
* `Trace.schedulers` — the scheduler, when a genuine parallel scheduling choice
  exists at each trace step;
* `Trace.controllerPaths` — the full control path of each concrete event in the
  trace;
* `ObservedTrace me control profile trace` — the exact typed sequence of local
  observations available to a fixed party `me` along `trace`;
* `ObservedTrace.ofTrace` — the canonical observed trace induced by a concrete
  execution trace.

This stays continuation-based and does not add any new global state. A trace is
still consumed one frontier event at a time, with control and profile data
transported through the corresponding residual specs.
-/

universe u

namespace Interaction
namespace Concurrent

namespace Trace

/--
`currentControllers control trace` records the party currently controlling each
step of the trace.

At each step, this is exactly `Current.controller?` for the current residual
control tree before the next frontier event is scheduled.
-/
def currentControllers {Party : Type u} :
    {S : Spec} → (control : Control Party S) → Trace S → List (Option Party)
  | _, _, .done _ => []
  | _, control, .step event tail =>
      Current.controller? control ::
        currentControllers (Control.residual control event) tail

/--
`schedulers control trace` records the current scheduler at each step of the
trace, when a genuine parallel scheduling choice exists.

This is the stepwise trace lift of `Current.scheduler?`.
-/
def schedulers {Party : Type u} :
    {S : Spec} → (control : Control Party S) → Trace S → List (Option Party)
  | _, _, .done _ => []
  | _, control, .step event tail =>
      Current.scheduler? control ::
        schedulers (Control.residual control event) tail

/--
`controllerPaths control trace` records the full control path of each concrete
frontier event in the trace.

Each list element is the corresponding `Control.controllers control event` for
that trace step, so scheduler ownership and downstream payload ownership are
both preserved.
-/
def controllerPaths {Party : Type u} :
    {S : Spec} → (control : Control Party S) → Trace S → List (List Party)
  | _, _, .done _ => []
  | _, control, .step event tail =>
      Control.controllers control event ::
        controllerPaths (Control.residual control event) tail

end Trace

/--
`ObservedTrace me control profile trace` is the exact typed sequence of local
observations available to the fixed party `me` along the concrete execution
trace `trace`.

The type is indexed not only by the initial concurrent spec but also by the
current residual control tree, current residual observation profile, and the
trace itself. This keeps each step's observation at its precise dependent type
`Current.ObsType me control profile`.
-/
inductive ObservedTrace {Party : Type u} [DecidableEq Party] (me : Party) :
    {S : Spec} → (control : Control Party S) → (profile : Profile Party S) →
      Trace S → Type (u + 1) where
  | /-- The unique observed trace of a finished quiescent execution trace. -/
    done {S : Spec} {control : Control Party S} {profile : Profile Party S}
      {h : Front S → False} :
      ObservedTrace me control profile (.done h)
  | /-- Extend an observed trace by the local observation exposed at the next
    frontier event. The tail is indexed by the residual control tree, residual
    profile, and residual execution trace. -/
    step {S : Spec} {control : Control Party S} {profile : Profile Party S}
      {event : Front S} {tail : Trace (residual event)}
      (obs : Current.ObsType me control profile)
      (rest : ObservedTrace me (Control.residual control event)
        (Profile.residual profile event) tail) :
      ObservedTrace me control profile (.step event tail)

namespace ObservedTrace

/-- The number of steps recorded by an observed trace. -/
def length {Party : Type u} [DecidableEq Party] {me : Party} :
    {S : Spec} → {control : Control Party S} → {profile : Profile Party S} →
      {trace : Trace S} → ObservedTrace me control profile trace → Nat
  | _, _, _, .done _, .done => 0
  | _, _, _, .step _ _, .step _ rest => rest.length.succ

/--
`ofTrace me control profile trace` is the canonical observed trace induced by
the concrete concurrent trace `trace`.

It is computed by applying `Current.observe` at each step and then recurring on
the residual control tree, residual profile, and residual trace.
-/
def ofTrace {Party : Type u} [DecidableEq Party] (me : Party) :
    {S : Spec} → (control : Control Party S) → (profile : Profile Party S) →
      (trace : Trace S) → ObservedTrace me control profile trace
  | _, _, _, .done _ => .done
  | _, control, profile, .step event tail =>
      .step
        (Current.observe me control profile event)
        (ofTrace me (Control.residual control event) (Profile.residual profile event) tail)

@[simp, grind =]
theorem length_done {Party : Type u} [DecidableEq Party] {me : Party}
    {S : Spec} {control : Control Party S} {profile : Profile Party S}
    {h : Front S → False} :
    length (ObservedTrace.done (me := me) (S := S) (control := control)
      (profile := profile) (h := h)) = 0 := by
  simp [ObservedTrace.length]

@[simp, grind =]
theorem length_step {Party : Type u} [DecidableEq Party] {me : Party}
    {S : Spec} {control : Control Party S} {profile : Profile Party S}
    {event : Front S} {tail : Trace (residual event)}
    (obs : Current.ObsType me control profile)
    (rest : ObservedTrace me (Control.residual control event)
      (Profile.residual profile event) tail) :
    length (.step obs rest : ObservedTrace me control profile (.step event tail)) =
      rest.length.succ := by
  simp [ObservedTrace.length]

/--
The canonical observed trace has the same length as the underlying execution
trace.
-/
theorem length_ofTrace {Party : Type u} [DecidableEq Party] {me : Party} :
    {S : Spec} → (control : Control Party S) → (profile : Profile Party S) →
      (trace : Trace S) → (ofTrace me control profile trace).length = trace.length
  | _, _, _, .done _ => rfl
  | _, control, profile, .step event tail => by
      simpa [ObservedTrace.ofTrace, ObservedTrace.length, Trace.length] using
        length_ofTrace (me := me)
          (Control.residual control event) (Profile.residual profile event) tail

end ObservedTrace

end Concurrent
end Interaction
