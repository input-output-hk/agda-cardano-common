{-# OPTIONS --guardedness #-}

-- Initialized diagnostic, not a completed configured-bundle lifecycle.
-- Keep the source KeepAlive start mode and expose the real allocation refusal.
module ConnectionManagement.Negative.FullConfiguredBlocked where

open import ConnectionManagement.Negative.FullConfiguredProfile
import ConnectionManagement.Negative.FullConfiguredAcquire as Prefix
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.OutboundGovernor as Governor

negotiate : V.Event
negotiate = server (E.run (mux (U.negotiate L.child fullBundle unidirectional)))
endpoint : V.Runtime
endpoint = snapshot (after negotiate Prefix.s23)
edge : V.advance negotiate Prefix.s23 ≡ just endpoint
edge = refl

schedule : List V.Event
schedule = Prefix.actions ++ (negotiate ∷ [])
abstract
  initialized-to-obstruction : V.Runs initial schedule endpoint
  initialized-to-obstruction = append Prefix.path (V.more edge V.stop)

event-count : length schedule ≡ 24
event-count = refl
allocation-refused : V.advance
  (server (E.run (mux (U.allocateHandle L.child (ident 0) (ident 0))))) endpoint ≡ nothing
allocation-refused = refl
no-premature-publication : V.advance
  (server (E.run (mux (U.publishSuccess L.child)))) endpoint ≡ nothing
no-premature-publication = refl
no-premature-body-exit : V.advance (exit (W.beginExit L.child)) endpoint ≡ nothing
no-premature-body-exit = refl
no-premature-handler-result : V.advance (exit (W.publishAsyncResult L.child)) endpoint ≡ nothing
no-premature-handler-result = refl

-- No physical mux/handle was installed, no protocol result or handler result
-- was fabricated; the second known peer is present, not a second active run.
no-handles : IG.handles (IG.execution (governor endpoint)) ≡ []
no-handles = refl
no-muxes : IG.muxes (IG.execution (governor endpoint)) ≡ []
no-muxes = refl
no-protocol-jobs : P.jobs (V.physical (V.base endpoint)) ≡ []
no-protocol-jobs = refl
no-handler-result : W.resultOf L.child (handlerState endpoint) ≡ nothing
no-handler-result = refl
two-known-peers : length (Governor.knownPeers
  (Sub.privateState (PS.machine (K.peers (V.base endpoint))))) ≡ 2
two-known-peers = refl
