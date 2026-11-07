{-# OPTIONS --safe #-}

-- Exact executable selectors for every existing full node-driver policy transition.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.LeiosNotifyPipeLookahead.NodeDriverExecution
  (Notification : Set) (notificationEq : DecidableEquality Notification) where

open import Data.Bool using (true; false)
import Data.Bool.Properties as Bool
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.ClientExecution Notification ⊤ notificationEq as CE
import Cardano_network.LeiosNotifyPipeLookahead.DriverExecution Notification ⊤ notificationEq as DE
open import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification
open import Cardano_network.LeiosNotifyPipeLookahead.Selection using (select; select-complete)
open import Data.Empty using (⊥-elim)
import Cardano_network.LeiosNotifyPipeLookahead.Enumeration Notification as SE
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientExecution Notification ⊤ notificationEq as NX
-- Shared server operation execution retains the exact node-next contract.
module SX = S.Executable notificationEq

-- Schedule data name permitted operations without supplying their proof evidence.
data Choice : Set where
  client server : ℕ → Choice
  accept excessive queued continue terminate : Choice
  transport : DE.Choice → Choice

-- Internal interpretation reconstructs the independent node transition certificate.
hidden-step : (s : State) → Choice → Maybe (Σ[ t ∈ State ] Tau s t)
hidden-step (nodeDriver raw@(D.pair c s cs sc pc ps rc rs) q true forecast halt) (client n)
  with select (CE.internalMoves c) n
... | nothing = nothing
... | just (c′ , pr) = just (_ , clientSchedule (Client.schedule pr))
hidden-step (nodeDriver raw@(D.pair c s cs sc pc ps rc rs) q live forecast halt) (server n)
  with select (S.internalMoves s) n
... | nothing = nothing
... | just (s′ , pr) with Server.routine pr Bool.≟ true
...   | no _ = nothing
...   | yes allowed = just (_ , serverSchedule (Server.schedule pr allowed))
hidden-step (nodeDriver (D.pair c (S.state S.admit w sender completed flag) cs sc pc ps rc rs)
    (Q.credits free messages) live forecast halt) accept with free Nat.≟ 1000
... | yes _ = nothing
... | no unequal = just (_ , serverSchedule (Server.admitAccepted (Q.admitted unequal)))
hidden-step (nodeDriver (D.pair c (S.state S.admit w sender completed flag) cs sc pc ps rc rs)
    (Q.credits free messages) live forecast halt) excessive with free Nat.≟ 1000
... | no _ = nothing
... | yes equal = just (_ , serverSchedule (Server.admitExcessive (Q.excessive equal)))
hidden-step (nodeDriver (D.pair c s cs sc pc ps rc rs) (Q.credits free (msg ∷ messages)) live forecast halt) queued
  with SX.lookup S.nodeNext s (S.nextReply (S.normal msg))
... | nothing = nothing
... | just (s′ , pr) = just (_ , serverSchedule (Server.nextQueued Q.dequeued pr))
hidden-step (nodeDriver (D.pair c s cs sc pc ps rc rs) q true true false) continue
  with CE.lookup (C.continue (+ 1000)) c
... | nothing = nothing
... | just (c′ , pr) = just (_ , continueReady (Client.continueAtDepth pr))
hidden-step (nodeDriver (D.pair c s cs sc pc ps rc rs) q true forecast true) terminate
  with CE.lookup (C.terminate tt) c
... | nothing = nothing
... | just (c′ , pr) = just (_ , terminateReady (Client.terminate pr))
hidden-step (nodeDriver raw q live forecast halt) (transport choice)
  with DE.hidden S.nodeNext raw choice
... | nothing = nothing
... | just (raw′ , pr) with transportAllowed live pr Bool.≟ true
...   | no _ = nothing
...   | yes allowed = just (_ , Tau.transport pr allowed)
hidden-step _ _ = nothing

-- Visible interpretation checks exact wire packets, environment inputs and normal handlers.
visible-step : (s : State) (a : Action) → Maybe (Σ[ t ∈ State ] Step s a t)
visible-step (nodeDriver raw q true forecast halt) (wire row@(D.clientSend _)) with DE.lookup S.nodeNext row raw
... | nothing = nothing
... | just (raw′ , pr) = just (_ , clientRecord sent pr)
visible-step (nodeDriver raw q true forecast halt) (wire row@(D.clientRecv _)) with DE.lookup S.nodeNext row raw
... | nothing = nothing
... | just (raw′ , pr) = just (_ , clientRecord received pr)
visible-step (nodeDriver raw q live forecast halt) (wire row@(D.serverSend _)) with DE.lookup S.nodeNext row raw
... | nothing = nothing
... | just (raw′ , pr) = just (_ , serverRecord sent pr)
visible-step (nodeDriver raw q live forecast halt) (wire row@(D.serverRecv _)) with DE.lookup S.nodeNext row raw
... | nothing = nothing
... | just (raw′ , pr) = just (_ , serverRecord received pr)
visible-step (nodeDriver raw q live forecast halt) (setForecast ready) = just (_ , forecastInput)
visible-step (nodeDriver raw q live forecast halt) (setTerminate requested) = just (_ , terminateInput)
visible-step (nodeDriver raw (Q.credits free messages) live forecast halt) (eligible msg)
  with S.active (S.reader (D.serverState raw)) Bool.≟ true
... | no _ = nothing
... | yes active with free
...   | zero = just (_ , applicationInput (Server.applicationOffer active Q.dropped))
...   | suc n = just (_ , applicationInput (Server.applicationOffer active Q.enqueued))
visible-step (nodeDriver (D.pair c s cs sc pc ps rc rs) q true forecast halt) (handledNormal msg)
  with CE.lookup (C.handled (S.normal msg)) c
... | nothing = nothing
... | just (c′ , pr) = just (_ , normalHandler (Client.handled pr))
visible-step (nodeDriver (D.pair c s cs sc pc ps rc rs) q true forecast halt) rejectedCancel
  with NX.lookup Client.handlerRejectedCancel (Client.running c)
... | nothing = nothing
... | just (_ , pr@(Client.rejectedCancel _ _)) = just (_ , canceledHandlerExit pr)
visible-step _ _ = nothing

-- Every independent visible policy transition returns its own exact target.
visible-complete : ∀ {s a t} → Step s a t → map proj₁ (visible-step s a) ≡ just t
visible-complete (clientRecord {raw = raw} (sent {msg = msg}) pr)
  with DE.lookup S.nodeNext (D.clientSend msg) raw | DE.next-complete pr
... | just (_ , _) | refl = refl
visible-complete (clientRecord {raw = raw} (received {msg = msg}) pr)
  with DE.lookup S.nodeNext (D.clientRecv msg) raw | DE.next-complete pr
... | just (_ , _) | refl = refl
visible-complete (serverRecord {raw = raw} {live = true} (sent {msg = msg}) pr)
  with DE.lookup S.nodeNext (D.serverSend msg) raw | DE.next-complete pr
... | just (_ , _) | refl = refl
visible-complete (serverRecord {raw = raw} {live = false} (sent {msg = msg}) pr)
  with DE.lookup S.nodeNext (D.serverSend msg) raw | DE.next-complete pr
... | just (_ , _) | refl = refl
visible-complete (serverRecord {raw = raw} {live = true} (received {msg = msg}) pr)
  with DE.lookup S.nodeNext (D.serverRecv msg) raw | DE.next-complete pr
... | just (_ , _) | refl = refl
visible-complete (serverRecord {raw = raw} {live = false} (received {msg = msg}) pr)
  with DE.lookup S.nodeNext (D.serverRecv msg) raw | DE.next-complete pr
... | just (_ , _) | refl = refl
visible-complete (forecastInput {live = true}) = refl
visible-complete (forecastInput {live = false}) = refl
visible-complete (terminateInput {live = true}) = refl
visible-complete (terminateInput {live = false}) = refl
visible-complete (applicationInput {raw = raw} {live = true} (Server.applicationOffer active Q.dropped))
  with S.active (S.reader (D.serverState raw)) Bool.≟ true
... | yes _ = refl
... | no absent = ⊥-elim (absent active)
visible-complete (applicationInput {raw = raw} {live = false} (Server.applicationOffer active Q.dropped))
  with S.active (S.reader (D.serverState raw)) Bool.≟ true
... | yes _ = refl
... | no absent = ⊥-elim (absent active)
visible-complete (applicationInput {raw = raw} {live = true} (Server.applicationOffer active Q.enqueued))
  with S.active (S.reader (D.serverState raw)) Bool.≟ true
... | yes _ = refl
... | no absent = ⊥-elim (absent active)
visible-complete (applicationInput {raw = raw} {live = false} (Server.applicationOffer active Q.enqueued))
  with S.active (S.reader (D.serverState raw)) Bool.≟ true
... | yes _ = refl
... | no absent = ⊥-elim (absent active)
visible-complete (normalHandler {raw = D.pair c s cs sc pc ps rc rs} (Client.handled {m = msg} pr))
  with CE.lookup (C.handled (S.normal msg)) c | CE.next-complete pr
... | just (_ , _) | refl = refl
visible-complete (canceledHandlerExit {raw = D.pair c s cs sc pc ps rc rs} pr)
  with NX.lookup Client.handlerRejectedCancel (Client.running c) | NX.next-complete pr
... | just (_ , Client.rejectedCancel _ _) | refl = refl

-- Server routine classification depends on the operation family, not guard-proof identity.
routine-target : ∀ {s t} (first second : S.Tau s t) →
  Server.routine first ≡ true → Server.routine second ≡ true
routine-target S.admitted S.admitted allowed = allowed
routine-target S.excessive S.excessive allowed = allowed
routine-target _ S.registered _ = refl
routine-target _ S.setQuit _ = refl
routine-target _ (S.claim _) _ = refl
routine-target _ (S.cancel _) _ = refl
routine-target _ (S.retire _) _ = refl
routine-target _ S.flush _ = refl
routine-target _ S.drained _ = refl
routine-target _ S.abort _ = refl

-- A selected client bookkeeping certificate lifts without changing unrelated node fields.
client-target : ∀ {c c′ s cs sc pc ps rc rs q forecast halt n} {pr : C.Tau c c′} →
  select (CE.internalMoves c) n ≡ just (c′ , pr) →
  map proj₁ (hidden-step (nodeDriver (D.pair c s cs sc pc ps rc rs) q true forecast halt) (client n)) ≡
    just (nodeDriver (D.pair c′ s cs sc pc ps rc rs) q true forecast halt)
client-target same rewrite same = refl

-- An allowed selected server routine keeps its exact node-policy guard.
server-target : ∀ {c s s′ cs sc pc ps rc rs q live forecast halt n} {pr : S.Tau s s′} →
  select (S.internalMoves s) n ≡ just (s′ , pr) → Server.routine pr ≡ true →
  map proj₁ (hidden-step (nodeDriver (D.pair c s cs sc pc ps rc rs) q live forecast halt) (server n)) ≡
    just (nodeDriver (D.pair c s′ cs sc pc ps rc rs) q live forecast halt)
server-target {live = true} {pr = pr} same allowed rewrite same with Server.routine pr Bool.≟ true
... | yes _ = refl
... | no absent = ⊥-elim (absent allowed)
server-target {live = false} {pr = pr} same allowed rewrite same with Server.routine pr Bool.≟ true
... | yes _ = refl
... | no absent = ⊥-elim (absent allowed)

-- Source rules select an operation family; only finite-menu scheduling needs an index.
choose : ∀ {s t} → Tau s t → Choice
choose (clientSchedule (Client.schedule proof)) = client (proj₁ (select-complete (CE.target-complete proof)))
choose (serverSchedule (Server.schedule proof _)) = server (proj₁ (select-complete (SE.target-complete proof)))
choose (serverSchedule (Server.admitAccepted _)) = accept
choose (serverSchedule (Server.admitExcessive _)) = excessive
choose (serverSchedule (Server.nextQueued _ _)) = queued
choose (continueReady _) = continue
choose (terminateReady _) = terminate
choose (Tau.transport (D.clientInternal _) ())
choose (Tau.transport (D.serverInternal _) ())
choose (Tau.transport (D.clientCallback _ _) ())
choose (Tau.transport (D.serverCallback _) ())
choose (Tau.transport (D.commitClient {m = msg} _) _) = transport (DE.writeClient msg)
choose (Tau.transport (D.commitServer {m = msg} _) _) = transport (DE.writeServer msg)
choose (Tau.transport (D.decodeClient _) _) = transport DE.readClient
choose (Tau.transport (D.decodeServer _) _) = transport DE.readServer

-- Fix the operation before interpreting its guards, without equating certificates.
chosen-complete : ∀ {s t} (proof : Tau s t) → map proj₁ (hidden-step s (choose proof)) ≡ just t
chosen-complete (clientSchedule {raw = D.pair c s cs sc pc ps rc rs} (Client.schedule pr))
  with select-complete (CE.target-complete pr)
... | n , eq with select (CE.internalMoves c) n in chosen | eq
...   | just (_ , _) | refl = refl
chosen-complete (serverSchedule {raw = D.pair c s cs sc pc ps rc rs} (Server.schedule pr allowed))
  with select-complete (SE.target-complete pr)
... | n , eq with select (S.internalMoves s) n in chosen | eq
...   | just (_ , actual) | refl = server-target chosen (routine-target pr actual allowed)
chosen-complete (serverSchedule {raw = D.pair c (S.state S.admit w sender completed flag) cs sc pc ps rc rs} {live = true}
  (Server.admitAccepted (Q.admitted {c = free} unequal))) with free Nat.≟ 1000
... | no _ = refl
... | yes equal = ⊥-elim (unequal equal)
chosen-complete (serverSchedule {raw = D.pair c (S.state S.admit w sender completed flag) cs sc pc ps rc rs} {live = false}
  (Server.admitAccepted (Q.admitted {c = free} unequal))) with free Nat.≟ 1000
... | no _ = refl
... | yes equal = ⊥-elim (unequal equal)
chosen-complete (serverSchedule {raw = D.pair c (S.state S.admit w sender completed flag) cs sc pc ps rc rs} {live = true}
  (Server.admitExcessive (Q.excessive {c = free} equal))) with free Nat.≟ 1000
... | yes _ = refl
... | no unequal = ⊥-elim (unequal equal)
chosen-complete (serverSchedule {raw = D.pair c (S.state S.admit w sender completed flag) cs sc pc ps rc rs} {live = false}
  (Server.admitExcessive (Q.excessive {c = free} equal))) with free Nat.≟ 1000
... | yes _ = refl
... | no unequal = ⊥-elim (unequal equal)
chosen-complete (serverSchedule {raw = D.pair c s cs sc pc ps rc rs} {live = true} (Server.nextQueued (Q.dequeued {m = msg}) pr))
  with SX.lookup S.nodeNext s (S.nextReply (S.normal msg)) | SX.next-complete pr
... | just (_ , _) | refl = refl
chosen-complete (serverSchedule {raw = D.pair c s cs sc pc ps rc rs} {live = false} (Server.nextQueued (Q.dequeued {m = msg}) pr))
  with SX.lookup S.nodeNext s (S.nextReply (S.normal msg)) | SX.next-complete pr
... | just (_ , _) | refl = refl
chosen-complete (continueReady {raw = D.pair c s cs sc pc ps rc rs} (Client.continueAtDepth pr))
  with CE.lookup (C.continue (+ 1000)) c | CE.next-complete pr
... | just (_ , _) | refl = refl
chosen-complete (terminateReady {raw = D.pair c s cs sc pc ps rc rs} (Client.terminate pr))
  with CE.lookup (C.terminate tt) c | CE.next-complete pr
... | just (_ , _) | refl = refl
chosen-complete (Tau.transport (D.clientInternal _) ())
chosen-complete (Tau.transport (D.serverInternal _) ())
chosen-complete (Tau.transport (D.clientCallback _ _) ())
chosen-complete (Tau.transport (D.serverCallback _) ())
chosen-complete (Tau.transport {live = false} (D.commitClient _) ())
chosen-complete (Tau.transport {raw = D.pair c s cs sc pc ps rc rs} {live = true} (D.commitClient {m = msg} pr) allowed)
  with CE.lookup (D.clientSendAction msg) c | CE.next-complete pr
... | just (_ , _) | refl = refl
chosen-complete (Tau.transport {raw = D.pair c s cs sc pc ps rc rs} {live = true} (D.commitServer {m = msg} pr) allowed)
  with SX.lookup S.nodeNext s (D.serverSendAction msg) | SX.next-complete pr
... | just (_ , _) | refl = refl
chosen-complete (Tau.transport {raw = D.pair c s cs sc pc ps rc rs} {live = false} (D.commitServer {m = msg} pr) allowed)
  with SX.lookup S.nodeNext s (D.serverSendAction msg) | SX.next-complete pr
... | just (_ , _) | refl = refl
chosen-complete (Tau.transport {live = false} (D.decodeClient _) ())
chosen-complete (Tau.transport {raw = D.pair c s cs sc pc ps rc rs} {live = true} (D.decodeClient {m = msg} pr) allowed)
  with CE.lookup (D.clientRecvAction msg) c | CE.next-complete pr
... | just (_ , _) | refl = refl
chosen-complete (Tau.transport {raw = D.pair c s cs sc pc ps rc rs} {live = true} (D.decodeServer {m = msg} pr) allowed)
  with SX.lookup S.nodeNext s (D.serverRecvAction msg) | SX.next-complete pr
... | just (_ , _) | refl = refl
chosen-complete (Tau.transport {raw = D.pair c s cs sc pc ps rc rs} {live = false} (D.decodeServer {m = msg} pr) allowed)
  with SX.lookup S.nodeNext s (D.serverRecvAction msg) | SX.next-complete pr
... | just (_ , _) | refl = refl


-- Every independent hidden source rule has a concrete selector and exact target.
hidden-complete : ∀ {s t} → Tau s t → Σ[ choice ∈ Choice ] map proj₁ (hidden-step s choice) ≡ just t
hidden-complete proof = choose proof , chosen-complete proof
