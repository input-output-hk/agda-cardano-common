{-# OPTIONS --guardedness #-}

-- Snapshot only. The separate edge module checks just/refl independently.
module ConnectionManagement.Negative.InboundConfiguredMux4Edge0State where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport
import ConnectionManagement.Scenarios.Admission as A

import ConnectionManagement.Negative.InboundConfiguredMux3 as Prefix

s0 : B.State
s0 = Prefix.s3

raw-event : V.Event
raw-event = group (G.beginWholeClose A.child₀ (ident 1 ∷ ident 0 ∷ []))
a1 : B.Action
a1 = B.run raw-event
next-runtime : V.Runtime
next-runtime = snapshot (after raw-event (B.runtime s0))
s1 : B.State
s1 = record s0 { runtime = next-runtime }
