{-# OPTIONS --guardedness #-}

-- An actual CM mux delivery aborts the selected owner and acknowledges that
-- captured target. The receipt alone supplies no physical Async result.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersMuxReceipt
 (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (WorkerId; HandleId; EntryId)
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.MuxResultMonitor as Monitor
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
import ConnectionManagement.Properties.ServerPeersMonitorJoins as Joins
import ConnectionManagement.ServerPeers as Combined

private
 module W = Exit isBearerClosed using (State; base; shutdown; shared; control; setShutdown; resultReady; deliverShutdownMux)
 module G = Group isBearerClosed using (State; base; controls; step; abortOwner; abortStage; ownerContext; poolAt; protocolState)
 module M = Monitor isBearerClosed using (base)
 module Handler = ExitFacts isBearerClosed using (Control; control; control-observation)
 module K = Combined isBearerClosed isIOManagerError

-- Owner interruption changes only the local group control frame. In particular
-- it cannot replace CM's captured traversal while delivering its exception.
abort-base : ∀ worker err before {after} →
 G.step (G.abortOwner worker err) before ≡ just after → G.base after ≡ G.base before
abort-base worker err before actual
 with G.abortStage worker before | G.ownerContext worker before | P.noParent (G.poolAt worker before)
... | true | just (savedFrame , mid) | true with P.muxAt mid (G.protocolState before)
...   | nothing = case actual of λ ()
...   | just savedMux with Mux.callback savedMux
...     | Mux.returned = case just-injective actual of λ { refl → refl }
...     | Mux.readActive trace = case actual of λ ()
...     | Mux.commitTrace active trace = case actual of λ ()
...     | Mux.afterStart number = case actual of λ ()
...     | Mux.forkPending number = case actual of λ ()
...     | Mux.afterFailure = case actual of λ ()
...     | Mux.tracerFailed number = case actual of λ ()
abort-base worker err before actual | false | _ | _ = case actual of λ ()
abort-base worker err before actual | true | nothing | _ = case actual of λ ()
abort-base worker err before actual | true | just _ | false = case actual of λ ()

abort-coordinator : ∀ worker err before {next} →
 G.step (G.abortOwner worker err) (W.base before) ≡ just next →
 W.shutdown (record before { base = next }) ≡ W.shutdown before
abort-coordinator worker err before actual = cong
 (λ monitor → B.shutdown (P.U.base (P.base (M.base monitor))))
 (abort-base worker err (W.base before) actual)

private
 acknowledgment-shape : ∀ current available before entry worker {after} →
  Close.phase before ≡ Close.awaitDelivery entry worker →
  Close.step current available Close.acknowledgeDelivery before ≡ just after →
  after ≡ record before { phase = Close.reading;
    collected = Close.collected before ++ (worker ∷ []) }
 acknowledgment-shape current available before entry worker awaited actual
  rewrite awaited = sym (just-injective actual)

 last-member : ∀ (workers : List WorkerId) worker → worker ∈ workers ++ (worker ∷ [])
 last-member [] worker = here refl
 last-member (head ∷ tail) worker = there (last-member tail worker)

module Frontend (canInitiate : HandleId → ℕ → Bool) where
 private
  module T = K.Protocols canInitiate using (Runtime; Event; advance)
  module J = Joins.Frontend isBearerClosed isIOManagerError canInitiate using
   (MuxReceipt; handler-event; physical; physical-receipt)
  module Fields = Joins.Frontend.MuxReceipt using (entry; worker; next; awaiting; aborted; acknowledged)

 Receipt : ErrorId → W.State → W.State → Set
 Receipt = J.MuxReceipt
 event : ErrorId → T.Event
 event err = J.handler-event (W.deliverShutdownMux err)
 physical-receipt : ∀ err before {after} →
  T.advance (event err) before ≡ just after → Receipt err (J.physical before) (J.physical after)
 physical-receipt = J.physical-receipt

 private
  control-shape : ∀ before {after entry worker} →
   Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker →
   Handler.Control Close.acknowledgeDelivery before after →
   W.shutdown after ≡ record (W.shutdown before)
    { phase = Close.reading; collected = Close.collected (W.shutdown before) ++ (worker ∷ []) }
  control-shape before {entry = entry} {worker = worker} awaited (Handler.control successor primitiveStep refl) =
   acknowledgment-shape (Shared.cm (W.shared before)) (λ target → W.resultReady target before)
    (W.shutdown before) entry worker awaited primitiveStep

 coordinator-shape : ∀ {err before after} (receipt : Receipt err before after) →
  W.shutdown after ≡ record (W.shutdown before)
   { phase = Close.reading;
     collected = Close.collected (W.shutdown before) ++ (Fields.worker receipt ∷ []) }
 coordinator-shape {err} {before} receipt = trans
  (control-shape (record before { base = Fields.next receipt })
   (trans (cong Close.phase same) (Fields.awaiting receipt))
   (Handler.control-observation Close.acknowledgeDelivery
    (record before { base = Fields.next receipt }) (Fields.acknowledged receipt)))
  (cong (λ coordinator → record coordinator
   { phase = Close.reading; collected = Close.collected coordinator ++ (Fields.worker receipt ∷ []) }) same)
  where
  same = abort-coordinator (Fields.worker receipt) err before (Fields.aborted receipt)

 collected-append : ∀ {err before after} (receipt : Receipt err before after) →
  Close.collected (W.shutdown after) ≡
  Close.collected (W.shutdown before) ++ (Fields.worker receipt ∷ [])
 collected-append receipt = cong Close.collected (coordinator-shape receipt)

 receipt-member : ∀ {err before after} (receipt : Receipt err before after) →
  Fields.worker receipt ∈ Close.collected (W.shutdown after)
 receipt-member {before = before} receipt = subst (Fields.worker receipt ∈_)
  (sym (collected-append receipt))
  (last-member (Close.collected (W.shutdown before)) (Fields.worker receipt))

 observed-worker : ∀ {err before after entry worker} (receipt : Receipt err before after) →
  Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker → Fields.worker receipt ≡ worker
 observed-worker receipt known with trans (sym (Fields.awaiting receipt)) known
 ... | refl = refl

 observed-entry : ∀ {err before after entry worker} (receipt : Receipt err before after) →
  Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker → Fields.entry receipt ≡ entry
 observed-entry receipt known with trans (sym (Fields.awaiting receipt)) known
 ... | refl = refl
