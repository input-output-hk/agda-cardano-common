{-# OPTIONS --guardedness #-}

-- Exact-field native server witnesses, shutdown/fault cases and negative controls.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerBridgeTests where

open import Data.Bool using (true; false)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Product using (_,_)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Function using (_$_)
open import Process_Trees using (PTree; ExtI; ret)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Base using (lo; hi; FromInitiator)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams
open import Cardano_network.LeiosNotifyP exactParams using (LNPEv; sendLNP; receiveLNP; doneLNP)
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead exactParams as Native
import Cardano_network.LeiosNotifyPipeLookahead.ServerEvents exactParams as Events
import Cardano_network.LeiosNotifyPipeLookahead.Properties Payloads.Notification as Properties
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerBridge exactParams as Bridge
open Native.Reference
open Native.Machine nodeNext fzero hi
module B = Bridge.For nodeNext fzero hi
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as LTS
import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv} as Traces

-- Concrete values inhabit all four notification kinds while retaining nontrivial fields.
notifications : List Payloads.Notification
notifications =
  Payloads.announcement (header (just (31 , 37 , 41))) ∷
  Payloads.offer (43 , 47) 53 ∷
  Payloads.txsOffer (59 , 61) ∷
  Payloads.votes ((67 , 71) ∷ (73 , 79) ∷ (67 , 71) ∷ []) ∷ []

-- Every exact notification value has a real initial native request/readiness/reply run.
Round : Payloads.Notification → Set₁
Round notification = tree initial Traces.⟹∖√⟨
  map (Events.encode fzero hi) (Properties.roundActions notification) ⟩ tree (Properties.ready 1)

-- General realization is instantiated with an inhabited independent source run.
native-round : (notification : Payloads.Notification) → Round notification
native-round notification = B.realize (Properties.round-run notification atFirst)

-- All four concrete kinds participate in actual PTree executions.
all-kinds : All Round notifications
all-kinds = native-round _ All.∷ native-round _ All.∷ native-round _ All.∷ native-round _ All.∷ All.[]

-- An exact selected payload can survive Quit and flag publication before it is sent.
selected-shutdown-source : (notification : Payloads.Notification) → Run nodeNext initial
  (recvRequest ∷ nextReply (normal notification) ∷ recvQuit ∷ sendReply (normal notification) ∷ sendDone ∷ [])
  (state closed 0 idle 0 true)
selected-shutdown-source notification =
  visible (receiveRequest atFirst) $
  internal admitted $
  internal registered $
  internal (claim refl) $
  visible (choose refl refl) $
  visible (receiveQuit atNext) $
  internal setQuit $
  visible (send refl) $
  internal (retire refl) $
  internal flush $
  internal drained $
  visible finish stop

-- The whole shutdown is realized in LNPEv without inventing a readiness premise.
selected-shutdown-native : (notification : Payloads.Notification) → tree initial Traces.⟹∖√⟨
  map (Events.encode fzero hi)
    (recvRequest ∷ nextReply (normal notification) ∷ recvQuit ∷ sendReply (normal notification) ∷ sendDone ∷ []) ⟩
  tree (state closed 0 idle 0 true)
selected-shutdown-native notification = B.realize (selected-shutdown-source notification)

-- After flag publication the source can drain an outstanding request with cancellation.
canceled-shutdown-source : Run nodeNext initial
  (recvRequest ∷ recvQuit ∷ sendReply canceled ∷ sendDone ∷ []) (state closed 0 idle 0 true)
canceled-shutdown-source =
  visible (receiveRequest atFirst) $
  internal admitted $
  internal registered $
  visible (receiveQuit atNext) $
  internal setQuit $
  internal (claim refl) $
  internal (cancel refl) $
  visible (send refl) $
  internal (retire refl) $
  internal flush $
  internal drained $
  visible finish stop

-- Cancellation and the final Done are realized as native responder wire events.
canceled-shutdown-native : tree initial Traces.⟹∖√⟨
  map (Events.encode fzero hi) (recvRequest ∷ recvQuit ∷ sendReply canceled ∷ sendDone ∷ []) ⟩
  tree (state closed 0 idle 0 true)
canceled-shutdown-native = B.realize canceled-shutdown-source

-- Admission failure is also a concrete native prefix and emits no fabricated wire Done.
failure-source : Run nodeNext initial (recvRequest ∷ []) (state failed 0 idle 0 false)
failure-source = visible (receiveRequest atFirst) (internal excessive (internal abort stop))

-- The complete source failure schedule has an actual native execution.
failure-native : tree initial Traces.⟹∖√⟨ Events.encode fzero hi recvRequest ∷ [] ⟩
  tree (state failed 0 idle 0 false)
failure-native = B.realize failure-source

-- The terminal CSP result of that execution is explicitly abnormal.
failure-result : PTree.force (tree (state failed 0 idle 0 false)) ≡ ret Native.excessiveRequests
failure-result = refl

-- Successful shutdown has the distinct normal result at the same native entry point.
success-result : PTree.force (tree (state closed 0 idle 0 true)) ≡ ret Native.success
success-result = refl

-- A pending offer retains both its requested point and size until Send.
pendingOffer : State
pendingOffer = state awaitNext 0 (selected (normal (Payloads.offer (43 , 47) 53))) 0 false

-- Changing only the slot is rejected by the native selected-payload gate.
wrong-slot : next pendingOffer (Events.encode fzero hi (sendReply (normal (Payloads.offer (43 , 48) 53)))) ≡ nothing
wrong-slot = refl

-- Changing only the size is rejected independently of the hash and slot.
wrong-size : next pendingOffer (Events.encode fzero hi (sendReply (normal (Payloads.offer (43 , 47) 54)))) ≡ nothing
wrong-size = refl

-- Reordering votes is rejected even when the multiset and duplicate count agree.
wrong-vote-order : next
  (state awaitNext 0 (selected (normal (Payloads.votes ((67 , 71) ∷ (73 , 79) ∷ (67 , 71) ∷ [])))) 0 false)
  (Events.encode fzero hi (sendReply (normal (Payloads.votes ((73 , 79) ∷ (67 , 71) ∷ (67 , 71) ∷ []))))) ≡ nothing
wrong-vote-order = refl

-- Reply records cannot claim initiator agency even with the correct notification.
wrong-agency : next pendingOffer
  (LTS.evLabel _ (sendLNP fzero hi)
    (Events.packet FromInitiator (MsgLNPBlockOffer (43 , 47) 53))) ≡ nothing
wrong-agency = refl

-- Commands from a different direction do not operate the fixed local server.
wrong-direction : next initial
  (LTS.evLabel _ (receiveLNP fzero lo) (Events.packet FromInitiator MsgLNPRequestNext)) ≡ nothing
wrong-direction = refl

-- The source peer has no extra doneLNP API event before its wire Done.
no-extra-done-api : next (state doneReady 0 idle 0 true) (LTS.evLabel _ (doneLNP fzero hi) tt) ≡ nothing
no-extra-done-api = refl

-- The node callback contract cannot supply Canceled before shutdown flag publication.
node-cannot-select-canceled : next (state awaitNext 0 claimed 0 false)
  (Events.encode fzero hi (nextReply canceled)) ≡ nothing
node-cannot-select-canceled = refl

-- The generic callback contract separately permits that result, as its type does.
generic-can-select-canceled : Native.Machine.next genericNext fzero hi
  (state awaitNext 0 claimed 0 false) (Events.encode fzero hi (nextReply canceled)) ≡
  just (state awaitNext 0 (selected canceled) 0 false)
generic-can-select-canceled = refl

-- The native safety theorem rules out Done while even one completion token remains.
early-done-impossible : ∀ {P} → tree (state flushing 0 idle 1 true)
  LTS.─[ LTS.ev (LTS.evl (Events.encode fzero hi sendDone)) ]─► P → ⊥
early-done-impossible st with B.done-only-drained-native st
... | ()

-- The native safety theorem also forbids new requests immediately after the Quit record.
request-after-quit-impossible : ∀ {P} → tree (state signalQuit 0 idle 0 false)
  LTS.─[ LTS.ev (LTS.evl (Events.encode fzero hi recvRequest)) ]─► P → ⊥
request-after-quit-impossible = B.no-request-after-shutdown-native refl
