{-# OPTIONS --guardedness #-}

-- A real cancellation edge from an initialized prefix cannot bypass contracts.
module ConnectionManagement.Negative.InboundConfiguredCancellation where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport
import ConnectionManagement.Negative.InboundConfiguredStart17 as Prefix
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.MuxJobTypes as JobTypes
import Data.Maybe as Maybe

s0 : B.State
s0 = Prefix.s2

a1 : B.Action
a1 = B.run (group (G.requestShutdown A.child₀))
s1 : B.State
s1 = snapshot (afterContract a1 s0)
e1 : B.step a1 s0 ≡ just s1
e1 = refl

a2 : B.Action
a2 = B.run (group (G.selectShutdown A.child₀))
s2 : B.State
s2 = snapshot (afterContract a2 s1)
e2 : B.step a2 s1 ≡ just s2
e2 = refl

a3 : B.Action
a3 = B.run (group (G.observeStoppingTrace A.child₀))
s3 : B.State
s3 = snapshot (afterContract a3 s2)
e3 : B.step a3 s2 ≡ just s3
e3 = refl

a4 : B.Action
a4 = B.run (group (G.writeStopping A.child₀))
s4 : B.State
s4 = snapshot (afterContract a4 s3)
e4 : B.step a4 s3 ≡ just s4
e4 = refl

a5 : B.Action
a5 = B.run (group (G.captureGroup A.child₀ (ident 15 ∷ ident 14 ∷ ident 13 ∷ ident 12 ∷ ident 11 ∷ ident 10 ∷ [])))
s5 : B.State
s5 = snapshot (afterContract a5 s4)
e5 : B.step a5 s4 ≡ just s5
e5 = refl

a6 : B.Action
a6 = B.run (group (G.requestGroupCancel A.child₀))
s6 : B.State
s6 = snapshot (afterContract a6 s5)
e6 : B.step a6 s5 ≡ just s6
e6 = refl

actions : List B.Action
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ []

abstract
  path : B.Runs s0 actions s6
  path = B.more {s = s0} {t = s1} {u = s6} {a = a1} e1 (B.more {s = s1} {t = s2} {u = s6} {a = a2} e2 (B.more {s = s2} {t = s3} {u = s6} {a = a3} e3 (B.more {s = s3} {t = s4} {u = s6} {a = a4} e4 (B.more {s = s4} {t = s5} {u = s6} {a = a5} e5 (B.more {s = s5} {t = s6} {u = s6} {a = a6} e6 (B.done))))))

-- The raw source genuinely permits delivery; the typed phase stays executing.
raw-event : V.Event
raw-event = group (G.deliverGroup A.child₀)
raw-runtime : V.Runtime
raw-runtime = snapshot (after raw-event (B.runtime s6))
raw-cancellation-enabled : V.advance raw-event (B.runtime s6) ≡ just raw-runtime
raw-cancellation-enabled = refl
raw-pool-unwinding : lookup (ident 15) (Pool.handles
  (P.poolAt A.child₀ (V.physical (V.base raw-runtime)))) ≡ just Pool.bodyUnwinding
raw-pool-unwinding = refl
raw-typed-phase-still-executing : Maybe.map JobTypes.phase
  (lookup (ident 15) (P.jobs (V.physical (V.base raw-runtime)))) ≡ just JobTypes.executing
raw-typed-phase-still-executing = refl
contracts-not-finished : B.normalDone 2 s6 ≡ false
contracts-not-finished = refl

-- This refusal therefore comes from the normal wrapper, not a disabled source.
no-physical-cancellation-bypass : B.step (B.run raw-event) s6 ≡ nothing
no-physical-cancellation-bypass = refl
