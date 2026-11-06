{-# OPTIONS --guardedness #-}

-- Lift real physical steps through empty exception wrappers. Outer permissions
-- remain explicit small equations; this construction does not enter CM close.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersMuxEmbedding
 (b io : ErrorId → Bool) where

open import Data.Bool using (true)
open import Data.Nat using (ℕ)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (HandleId)
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxExitCancellation as CancelModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.MuxDeltaQ as DeltaModel
import ConnectionManagement.MuxCatchUnwind as CatchModel
import ConnectionManagement.MuxPublicationUnwind as PublicationModel
import ConnectionManagement.ServerAdmission as ServerModel
import ConnectionManagement.ServerIGExit as IGModel
import ConnectionManagement.PeerContext as ContextModel
import ConnectionManagement.ServerPeers as Combined

module W = ExitModel b using (State; Action; step)
private
 module X = CancelModel b using (run)
 module R = UnwindModel b using (State; unwinding; run)
 module D = DeltaModel b using (State; deltaQState; run; allowed; note)
 module C = CatchModel b using (catchState; run)
 module N = PublicationModel b using (Action; publicationState; run)
 module S = ServerModel b using (State; Stage; serverState; run; allowed)
 module E = IGModel b using (State; Exit; Action; igExitState; run; runAllowed)
 module K = Combined b io using (combined; serverStep; step; serverAllowed)
module Context = ContextModel io using (Context)

raw : W.State → R.State
raw physical = R.unwinding physical []
delta : W.State → D.State
delta physical = D.deltaQState (raw physical) []
body : W.Action → N.Action
body action = N.run (C.run (D.run (R.run (X.run action))))
server : W.State → S.Stage → Bool → S.State
server physical stage listener = S.serverState (N.publicationState (C.catchState (delta physical) []) []) [] stage listener
outer : W.State → S.Stage → Bool → E.Exit → E.State
outer physical stage listener exit = E.igExitState (server physical stage listener) exit
action : W.Action → E.Action
action physicalAction = E.run (S.run (body physicalAction))

module Frontend (capability : HandleId → ℕ → Bool) where
 module T = Combined.Protocols b io capability using
  (Runtime; Front; Event; runtime; advance; dispatch; noteLegacy; inheritAllowed)
 embed : W.State → Context.Context → T.Front → S.Stage → Bool → E.Exit → T.Runtime
 embed physical context front stage listener exit = T.runtime
  (K.combined (outer physical stage listener exit) context) front
 event : W.Action → T.Event
 event a = T.dispatch (K.serverStep (action a))
 nextFront : W.Action → T.Front → T.Front
 nextFront a front = T.noteLegacy (K.serverStep (action a)) front

 -- Each premise observes an existing wrapper guard or its bookkeeping. The
 -- actual lower transition is supplied separately, never reconstructed by reset.
 record Allowed (a : W.Action) (before after : W.State) (context : Context.Context)
   (front : T.Front) (stage : S.Stage) (listener : Bool) (exit : E.Exit) : Set where
  field
   delta-permission : D.allowed (R.run (X.run a)) (delta before) ≡ true
   delta-tickets : D.note (R.run (X.run a)) (raw after) [] ≡ []
   server-permission : S.allowed (body a) (server before stage listener) ≡ true
   ig-permission : E.runAllowed (S.run (body a)) (outer before stage listener exit) ≡ true
   shared-permission : K.serverAllowed (action a) (K.combined (outer before stage listener exit) context) ≡ true
   front-permission : T.inheritAllowed (K.serverStep (action a)) (embed before context front stage listener exit) ≡ true

 lift-step : ∀ a before {after} context front stage listener exit →
  Allowed a before after context front stage listener exit → W.step a before ≡ just after →
  T.advance (event a) (embed before context front stage listener exit) ≡
    just (embed after context (nextFront a front) stage listener exit)
 lift-step a before context front stage listener exit permitted actual
  rewrite Allowed.front-permission permitted | Allowed.shared-permission permitted
    | Allowed.ig-permission permitted | Allowed.server-permission permitted
    | Allowed.delta-permission permitted | actual | Allowed.delta-tickets permitted = refl
