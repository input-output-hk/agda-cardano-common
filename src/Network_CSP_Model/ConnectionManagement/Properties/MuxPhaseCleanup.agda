{-# OPTIONS --guardedness #-}

-- Phase/cleanup validity through the mux layers, handler exit, exit
-- cancellation and startup unwind (CM-I4c). A worker owned by a mux frame
-- keeps a handshaking physical thread; handler operations cannot target it, so
-- its cleanup record changes only above these layers. Workers outside F (those
-- owned by an exit frame above) must be framed and keep the cleanup record C;
-- workers in K (startup faults above) must stay framed. Framed workers inside F
-- have no cleanup record, and unframed workers satisfy the physical-thread
-- agreement.
module ConnectionManagement.Properties.MuxPhaseCleanup where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId; DecEq-Id)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other; lookup-head)
open import ConnectionManagement.Properties.CleanupWriters using (outbound-same; QuietOutbound)
open import ConnectionManagement.Properties.HandlerPhaseCleanup using (Expected; Agrees; module Relative; module Raw; module Physical)
import ConnectionManagement.Rules.MuxEgress as EgressLayout
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.CMShutdown as Close

present : ∀ {A : Set} → Maybe A → Bool
present nothing = false
present (just _) = true

-- Relative validity depends only on the excluded set's values.
on-ext : ∀ {Z Z′ s} → (∀ q → Z′ q ≡ Z q) → Relative.On Z s → Relative.On Z′ s
on-ext eqz v = Relative.on (λ q z → Relative.free v q (trans (sym (eqz q)) z)) (λ q z → Relative.kept v q (trans (sym (eqz q)) z))

Parked : Maybe H.Thread → Set
Parked nothing = ⊥
Parked (just t) = H.phase t ≡ H.handshaking

module Mux (F : WorkerId → Bool) (C : WorkerId → Maybe S.CleanupPC) (K : WorkerId → Bool) where
 private module U = MuxModel Types.TypedResult using (Action; Frame; module Startup; State; advanceStartup; allocate; allocateHandle; configure; configureMux; registerFor; registerCounters; beforePool; allocationAction; base; baseAllowed; birth; birthFresh; flow; frames; handleAllocated; handlerAllowed; inherit; initial; negotiate; negotiateReturned; noteBirth; origins; progress; promisePublished; publish; publishSuccess; returnedSuccess; run; setupFor; scheduled; nextSetup; setup; shutdownTargetAllowed; egressSetup; unframed; whenSetupDone-just; setFrame; setSource; source; startup; startupAllowed; startupStep; step; frame)
 private module Startup = U.Startup using (observePublication; step; initial)
 framedZ : U.State → WorkerId → Bool
 framedZ s q = present (lookup q (U.frames s))
 cleanupsU : U.State → Store WorkerId S.CleanupPC
 cleanupsU s = S.cleanups (Machine.world (O.core (U.source s)))
 record Valid (s : U.State) : Set where
  constructor mux-valid
  field
   relative : Relative.On (framedZ s) (B.view (U.base s))
   parked : ∀ q → framedZ s q ≡ true → Parked (lookup q (B.threads (U.base s)))
   clean : ∀ q → framedZ s q ≡ true → F q ≡ true → lookup q (cleanupsU s) ≡ nothing
   owned : ∀ q → F q ≡ false → framedZ s q ≡ true
   frozen : ∀ q → F q ≡ false → lookup q (cleanupsU s) ≡ C q
   kept : ∀ q → K q ≡ true → framedZ s q ≡ true
 open Valid public

 -- Steps that keep threads, cleanup records and the framed set.
 quiet : ∀ {s t} → (∀ q → framedZ t q ≡ framedZ s q) → B.threads (U.base t) ≡ B.threads (U.base s) →
   cleanupsU t ≡ cleanupsU s → Valid s → Valid t
 quiet {s} {t} keys th cl v = mux-valid rel park cln own frz (λ q k → trans (keys q) (kept v q k))
  where
  rel : Relative.On (framedZ t) (B.view (U.base t))
  rel = on-ext keys (proj₁ (Relative.transport (framedZ s) {s = B.view (U.base s)} {t = B.view (U.base t)} th cl (relative v)))
  park : ∀ q → framedZ t q ≡ true → Parked (lookup q (B.threads (U.base t)))
  park q z rewrite th = parked v q (trans (sym (keys q)) z)
  cln : ∀ q → framedZ t q ≡ true → F q ≡ true → lookup q (cleanupsU t) ≡ nothing
  cln q z f rewrite cl = clean v q (trans (sym (keys q)) z) f
  own : ∀ q → F q ≡ false → framedZ t q ≡ true
  own q f = trans (keys q) (owned v q f)
  frz : ∀ q → F q ≡ false → lookup q (cleanupsU t) ≡ C q
  frz q f rewrite cl = frozen v q f
 keys-put : ∀ w f s → framedZ s w ≡ true → ∀ q → framedZ (U.setFrame w f s) q ≡ framedZ s q
 keys-put w f s pw q with q ≟ w
 ... | yes refl rewrite lookup-put w f (U.frames s) = sym pw
 ... | no other rewrite lookup-put-other w q f (U.frames s) other = refl
 -- Rewriting an existing frame and a quiet source step.
 put-valid : ∀ w f s → framedZ s w ≡ true → Valid s → Valid (U.setFrame w f s)
 put-valid w f s pw v = quiet (keys-put w f s pw) refl refl v
 source-valid : ∀ c s → S.cleanups (Machine.world (O.core c)) ≡ cleanupsU s → Valid s → Valid (U.setSource c s)
 source-valid c s cl v = quiet (λ q → refl) refl cl v
 note-valid : ∀ birth s → Valid s → Valid (U.noteBirth birth s)
 note-valid nothing s v = v
 note-valid (just origin) s v = quiet (λ q → refl) refl refl v

 -- The mux guard keeps handler targets outside the framed set.
 free-of : ∀ w s → U.unframed w s ≡ true → framedZ s w ≡ false
 free-of w s allowed with lookup w (U.frames s)
 ... | nothing = refl
 ... | just _ = case allowed of λ ()
 target-free : ∀ s → U.shutdownTargetAllowed s ≡ true → Relative.TargetFree (framedZ s) (B.view (U.base s))
 target-free s allowed e w ph with Close.phase (B.shutdown (U.base s))
 ... | Close.awaitDelivery e′ w′ = case ph of λ { refl → free-of w s allowed }
 ... | Close.initial = case ph of λ ()
 ... | Close.reading = case ph of λ ()
 ... | (Close.sendReady e″ w″) = case ph of λ ()
 ... | Close.awaitResults = case ph of λ ()
 ... | Close.closed = case ph of λ ()
 handler-guard : ∀ a s → U.handlerAllowed a s ≡ true → Relative.Guard (framedZ s) a (B.view (U.base s))
 handler-guard (H.run a) s allowed = tt
 handler-guard (H.enterHandshake w) s allowed = free-of w s allowed
 handler-guard (H.deliverHandshakeCancellation w _) s allowed = free-of w s allowed
 handler-guard (H.deliverBlockedSetupCancellation w _) s allowed = free-of w s allowed
 handler-guard (H.publishCaught w) s allowed = free-of w s allowed
 handler-guard (H.rethrowCaught w) s allowed = free-of w s allowed
 handler-guard (H.enterFinalizer w) s allowed = free-of w s allowed
 handler-guard (H.cleanup w _) s allowed = free-of w s allowed
 handler-guard (H.finishCleanup w) s allowed = free-of w s allowed
 handler-guard (H.publishAsyncResult w) s allowed = free-of w s allowed
 handler-guard (H.shutdownStep _) s allowed = tt
 handler-guard (H.deliverShutdownHandshake _) s allowed = target-free s allowed
 handler-guard (H.deliverShutdownBlockedSetup _) s allowed = target-free s allowed
 handler-guard (H.deliverShutdownTimeWait _) s allowed = target-free s allowed
 handler-guard H.acknowledgeFinished s allowed = tt
 base-guard : ∀ a s → U.baseAllowed a s ≡ true → Relative.Outbound.Guarded (framedZ s) a (U.base s)
 base-guard (B.handler a) s allowed = handler-guard a s allowed
 base-guard (B.outbound a) s allowed = tt

 -- Inherited physical steps never touch a framed worker.
 based : ∀ s b → Relative.Moves (framedZ s) (B.view (U.base s)) (B.view b) → Valid s → Valid (record s { base = b })
 based s b (rel , fz) v = mux-valid rel park cln (owned v) frz (kept v)
  where
  park : ∀ q → framedZ s q ≡ true → Parked (lookup q (B.threads b))
  park q z rewrite proj₁ (fz q z) = parked v q z
  cln : ∀ q → framedZ s q ≡ true → F q ≡ true → lookup q (S.cleanups (Machine.world (O.core (B.source b)))) ≡ nothing
  cln q z f rewrite proj₂ (fz q z) = clean v q z f
  frz : ∀ q → F q ≡ false → lookup q (S.cleanups (Machine.world (O.core (B.source b)))) ≡ C q
  frz q f rewrite proj₂ (fz q (owned v q f)) = frozen v q f
 inherited : ∀ a s {t} → U.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq v with U.baseAllowed a s in allowed
 ... | false = case eq of λ ()
 ... | true with U.birthFresh (U.birth a (U.base s)) (U.origins s)
 ...   | false = case eq of λ ()
 ...   | true with B.step a (U.base s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just b = case just-injective eq of λ { refl → note-valid (U.birth a (U.base s)) (record s { base = b })
   (based s b (Relative.Outbound.step-moves′ (framedZ s) a (U.base s) (base-guard a s allowed) actual (relative v)) v) }

 -- Negotiation frames an unframed handshaking thread, which has no cleanup record.
 framed-new : ∀ w f th s → lookup w (U.frames s) ≡ nothing → lookup w (B.threads (U.base s)) ≡ just th →
   H.phase th ≡ H.handshaking → Valid s → Valid (U.setFrame w f s)
 framed-new w f th s absent found ph v = mux-valid rel park cln own frz kpt
  where
  t = U.setFrame w f s
  zw : framedZ s w ≡ false
  zw rewrite absent = refl
  none : lookup w (cleanupsU s) ≡ nothing
  none = subst (λ p → Expected p (lookup w (cleanupsU s))) ph (Relative.at (framedZ s) (relative v) zw found)
  rel : Relative.On (framedZ t) (B.view (U.base s))
  rel = Relative.on free′ kept′
   where
   free′ : ∀ q → framedZ t q ≡ false → Agrees (lookup q (B.threads (U.base s))) (lookup q (cleanupsU s))
   free′ q z with q ≟ w
   ... | yes refl rewrite lookup-put w f (U.frames s) = case z of λ ()
   ... | no other rewrite lookup-put-other w q f (U.frames s) other = Relative.free (relative v) q z
   kept′ : ∀ q → framedZ t q ≡ true → Σ H.Thread (λ x → lookup q (B.threads (U.base s)) ≡ just x)
   kept′ q z with q ≟ w
   ... | yes refl = th , found
   ... | no other rewrite lookup-put-other w q f (U.frames s) other = Relative.kept (relative v) q z
  park : ∀ q → framedZ t q ≡ true → Parked (lookup q (B.threads (U.base s)))
  park q z with q ≟ w
  ... | yes refl rewrite found = ph
  ... | no other rewrite lookup-put-other w q f (U.frames s) other = parked v q z
  cln : ∀ q → framedZ t q ≡ true → F q ≡ true → lookup q (cleanupsU s) ≡ nothing
  cln q z fq with q ≟ w
  ... | yes refl = none
  ... | no other rewrite lookup-put-other w q f (U.frames s) other = clean v q z fq
  own : ∀ q → F q ≡ false → framedZ t q ≡ true
  own q fq with q ≟ w
  ... | yes refl rewrite lookup-put w f (U.frames s) = refl
  ... | no other rewrite lookup-put-other w q f (U.frames s) other = owned v q fq
  frz : ∀ q → F q ≡ false → lookup q (cleanupsU s) ≡ C q
  frz q fq = frozen v q fq
  kpt : ∀ q → K q ≡ true → framedZ t q ≡ true
  kpt q k with q ≟ w
  ... | yes refl rewrite lookup-put w f (U.frames s) = refl
  ... | no other rewrite lookup-put-other w q f (U.frames s) other = kept v q k
 negotiated : ∀ w ps flow s {t} → U.negotiateReturned w ps flow s ≡ just t → Valid s → Valid t
 negotiated w ps flow s eq v with lookup w (B.threads (U.base s)) in found |
   lookup w (U.origins s) | lookup w (U.frames s) in absent
 ... | just thread | just origin | nothing with H.phase thread in ph
 negotiated w ps flow s eq v | just thread | just origin | nothing | H.maskedSetup = case eq of λ ()
 ...   | H.handshaking = case just-injective eq of λ { refl → framed-new w _ thread s absent found ph v }
 negotiated w ps flow s eq v | just thread | just origin | nothing | (H.caughtCancellation err) = case eq of λ ()
 negotiated w ps flow s eq v | just thread | just origin | nothing | (H.cancellationPublished err) = case eq of λ ()
 negotiated w ps flow s eq v | just thread | just origin | nothing | (H.bodyExited err) = case eq of λ ()
 negotiated w ps flow s eq v | just thread | just origin | nothing | (H.finalizing err) = case eq of λ ()
 negotiated w ps flow s eq v | just thread | just origin | nothing | (H.cleanupComplete err outcome) = case eq of λ ()
 negotiated w ps flow s eq v | just thread | just origin | nothing | (H.resultAvailable err outcome) = case eq of λ ()
 negotiated w ps flow s eq v | nothing | origin | old = case eq of λ ()
 negotiated w ps flow s eq v | just thread | nothing | old = case eq of λ ()
 negotiated w ps flow s eq v | just thread | just origin | just old = case eq of λ ()
 allocated : ∀ w hid mid s {t} → U.allocate w hid mid s ≡ just t → Valid s → Valid t
 allocated w hid mid s eq v with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.returnedSuccess with O.advance (O.inbound (Machine.igStep (U.allocationAction f hid mid))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → put-valid w _ (U.setSource c s) (cong present found)
   (source-valid c s (outbound-same (O.inbound (Machine.igStep (U.allocationAction f hid mid))) (U.source s) advanced tt) v) }
 allocated w hid mid s eq v | just f | U.handleAllocated old mid′ = case eq of λ ()
 allocated w hid mid s eq v | just f | U.promisePublished old mid′ = case eq of λ ()
 configured : ∀ w plan limit bound keys s {s′} → U.configure w plan limit bound keys s ≡ just s′ → Valid s → Valid s′
 configured w EgressLayout.plainLayout limit bound keys s eq = case eq of λ ()
 configured w (EgressLayout.scheduledLayout slice) limit bound keys s eq with lookup w (U.frames s)
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.handleAllocated hid mid with O.advance (O.inbound (Machine.igStep (IG.configureEgress mid (EgressLayout.scheduledLayout slice) limit bound keys))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → source-valid c s
   (outbound-same (O.inbound (Machine.igStep (IG.configureEgress mid (EgressLayout.scheduledLayout slice) limit bound keys))) (U.source s) advanced tt) }
 configured w (EgressLayout.scheduledLayout slice) limit bound keys s eq | just f | U.returnedSuccess = case eq of λ ()
 configured w (EgressLayout.scheduledLayout slice) limit bound keys s eq | just f | U.promisePublished h m = case eq of λ ()
 registered : ∀ w s {s′} → U.registerFor w s ≡ just s′ → Valid s → Valid s′
 registered w s eq with lookup w (U.frames s)
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | U.beforePool (U.Startup.phase (U.startup f))
 ...   | U.promisePublished hid mid | true with O.advance (O.inbound (Machine.igStep (IG.registerCells mid))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → source-valid c s (outbound-same (O.inbound (Machine.igStep (IG.registerCells mid))) (U.source s) advanced tt) }
 registered w s eq | just f | U.promisePublished hid mid | false = case eq of λ ()
 registered w s eq | just f | U.returnedSuccess | _ = case eq of λ ()
 registered w s eq | just f | U.handleAllocated h m | _ = case eq of λ ()
 setup-valid : ∀ w s {t} → U.setupFor w s ≡ just t → Valid s → Valid t
 setup-valid w s eq v with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.scheduled f (U.source s) | U.nextSetup (U.setup f)
 ...   | true | just next = case just-injective eq of λ { refl → put-valid w _ s (cong present found) v }
 ...   | true | nothing = case eq of λ ()
 ...   | false | _ = case eq of λ ()
 published : ∀ w s {t} → U.publish w s ≡ just t → Valid s → Valid t
 published w s eq v with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.handleAllocated hid mid with O.advance
   (O.inbound (Machine.handlerPublication w (S.negotiated hid (U.flow f)) Machine.resultWritten)) (U.source s) in advanced |
   Startup.step Startup.observePublication (U.startup f)
 ...     | just c | just next = case just-injective eq of λ { refl → put-valid w _ (U.setSource c s) (cong present found)
   (source-valid c s (outbound-same (O.inbound (Machine.handlerPublication w (S.negotiated hid (U.flow f)) Machine.resultWritten)) (U.source s) advanced tt) v) }
 ...     | nothing | _ = case eq of λ ()
 ...     | just c | nothing = case eq of λ ()
 published w s eq v | just f | U.returnedSuccess = case eq of λ ()
 published w s eq v | just f | U.promisePublished hid mid = case eq of λ ()
 startup : ∀ w a s {t} → U.advanceStartup w a s ≡ just t → Valid s → Valid t
 startup w a s eq v with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | U.startupAllowed a f s
 ...   | U.promisePublished hid mid | true with Startup.step a (U.startup f)
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → put-valid w _ s (cong present found) v }
 startup w a s eq v | just f | U.returnedSuccess | allowed = case eq of λ ()
 startup w a s eq v | just f | U.handleAllocated hid mid | allowed = case eq of λ ()
 startup w a s eq v | just f | U.promisePublished hid mid | false = case eq of λ ()
 step-preserves : ∀ a s {t} → U.step a s ≡ just t → Valid s → Valid t
 step-preserves (U.run a) = inherited a
 step-preserves (U.negotiate w ps flow) = negotiated w ps flow
 step-preserves (U.allocateHandle w hid mid) = allocated w hid mid
 step-preserves (U.configureMux w plan limit bound keys) s eq = configured w plan limit bound keys s eq
 step-preserves (U.registerCounters w) s eq = registered w s eq
 step-preserves (U.egressSetup w) = setup-valid w
 step-preserves (U.publishSuccess w) s eq = published w s (U.whenSetupDone-just w s (U.publish w s) eq)
 step-preserves (U.startupStep w a) = startup w a
 -- Initially there are no frames and every physical thread agrees with its record.
 initial-valid : ∀ c {s} → (∀ q → F q ≡ true) → (∀ q → K q ≡ false) → U.initial c ≡ just s → Valid s
 initial-valid c allF noK eq with IG.handles (IG.execution (Machine.inboundGovernor (O.core c))) |
   IG.muxes (IG.execution (Machine.inboundGovernor (O.core c))) | B.initial c in actual
 ... | [] | [] | just b = case just-injective eq of λ { refl → mux-valid
   (Relative.on (λ q z → Raw.agrees (Physical.initialized-valid c actual) q) (λ q ()))
   (λ q ()) (λ q ()) (λ q f → case trans (sym (allF q)) f of λ ()) (λ q f → case trans (sym (allF q)) f of λ ())
   (λ q k → case trans (sym k) (noK q) of λ ()) }
 ... | _ ∷ _ | _ | _ = case eq of λ ()
 ... | [] | _ ∷ _ | _ = case eq of λ ()
 ... | [] | [] | nothing = case eq of λ ()

import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolProperties
import ConnectionManagement.Rules.MuxRuntime as WireMux
import Data.Nat as Nat
open import Relation.Nullary using (does)
-- Protocol jobs issue only quiet source operations and rewrite existing frames.
module Protocol (F : WorkerId → Bool) (C : WorkerId → Maybe S.CleanupPC) (K : WorkerId → Bool) where
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; bodySource; publicationSource; locate; pendingAt; sameOutcome; Action; module Pool; module Startup; State; module U; appendPending; asyncInfraResult; asyncProtocolResult; base; commitClean; control; controlReady; deregisterInfra; deregisterProtocol; forkInitiator; forkResponder; infraId; infrastructureReturn; inherit; inheritedAllowed; initial; jobs; monitorControl; monitoring; muxAt; noParent; poolAt; protocolException; protocolReturned; unlessAwaiting-just; publishInfra; publishProtocol; register; registerProtocol; removePublished; returnProtocol; returned; run; setPool; setSource; source; sourceControl; step; viaInfra; viaProtocol; viaDb; viaDb-source; submitDb-via; awaitDb-via; dbFailure-via; DbFailure; refused; abandoned; submitDbWrite; awaitDbWrite; dbWriteFailed; writerComplete; writerSeal)
 private module U = P.U using (base; frames; handleAllocated; initial; progress; promisePublished; returnedSuccess; startup; step)
 private module Pool = P.Pool using (bodyReturnedWith; deregister; parentFork; publishAsyncResult; publishCompletion; register; step)
 private module Startup = P.Startup using (phase)
 private module Old = ProtocolProperties using (EgressChange; enter-observation; send-observation; muxer-egress-observation; ForkSource; responderSource; initiatorSource; BodyReturn; CompletionCommit; Fork; Publication; clean-observation; exception-observation; initiator-fork-observation; publication-observation; responder-fork-observation; return-observation)
 private module MV = Mux F C K
 Valid : P.State → Set
 Valid s = MV.Valid (P.base s)
 cleanupsP : P.State → Store WorkerId S.CleanupPC
 cleanupsP s = S.cleanups (Machine.world (O.core (P.source s)))
 source-valid : ∀ c s → S.cleanups (Machine.world (O.core c)) ≡ cleanupsP s → Valid s → Valid (P.setSource c s)
 source-valid c s cl valid = MV.source-valid c (P.base s) cl valid
 pool-valid : ∀ w f p s → present (lookup w (U.frames (P.base s))) ≡ true → Valid s → Valid (P.setPool w f p s)
 pool-valid w f p s pw valid = MV.put-valid w _ (P.base s) pw valid
 pending-valid : ∀ job j s → Valid s → Valid (P.appendPending job j s)
 pending-valid job j s valid with Types.direction job
 ... | WireMux.initiatorJob = valid
 ... | WireMux.responderJob = valid
 removed-valid : ∀ job kept s → Valid s → Valid (P.removePublished job kept s)
 removed-valid job kept s valid with Types.direction job
 ... | WireMux.initiatorJob = valid
 ... | WireMux.responderJob = valid
 inherited : ∀ a s {t} → P.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with P.inheritedAllowed a
 ... | false = case eq of λ ()
 ... | true with U.step a (P.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just u = case just-injective eq of λ { refl → MV.step-preserves a (P.base s) actual valid }
 -- Source effects of protocol completion and publication are IG operations.
 body-source-same : ∀ job result s {c} → P.bodySource job result s ≡ just c → S.cleanups (Machine.world (O.core c)) ≡ cleanupsP s
 body-source-same job result s eq with Types.direction job
 ... | WireMux.initiatorJob = case just-injective eq of λ { refl → refl }
 ... | WireMux.responderJob = outbound-same (O.inbound (Machine.igStep (IG.finishProtocol (Types.mux job) (Types.protocolNumber job) result))) (P.source s) eq tt
 publication-source-same : ∀ j job result s {c kept} → P.publicationSource j job result s ≡ just (c , kept) → S.cleanups (Machine.world (O.core c)) ≡ cleanupsP s
 publication-source-same j job result s eq with Types.direction job
 ... | WireMux.initiatorJob = case just-injective eq of λ { refl → refl }
 ... | WireMux.responderJob with P.locate j (P.pendingAt (Types.owner job) s) | P.muxAt (Types.mux job) s
 ...   | just (i , pendingRest) | just m with IG.takePending i (WireMux.finishedJobs m)
 ...     | just ((n , outcome) , rest) with does (Types.protocolNumber job Nat.≟ n) ∧ P.sameOutcome result outcome
 ...       | true with O.advance (O.inbound (Machine.igStep (IG.publishJobOccurrence (Types.mux job) i))) (P.source s) in advanced
 ...         | just c = case just-injective eq of λ { refl → outbound-same (O.inbound (Machine.igStep (IG.publishJobOccurrence (Types.mux job) i))) (P.source s) advanced tt }
 ...         | nothing = case eq of λ ()
 publication-source-same j job result s eq | WireMux.responderJob | just (i , pendingRest) | just m | just ((n , outcome) , rest) | false = case eq of λ ()
 publication-source-same j job result s eq | WireMux.responderJob | just (i , pendingRest) | just m | nothing = case eq of λ ()
 publication-source-same j job result s eq | WireMux.responderJob | nothing | _ = case eq of λ ()
 publication-source-same j job result s eq | WireMux.responderJob | just _ | nothing = case eq of λ ()
 fork-source : ∀ {f mid n s c d} → Old.ForkSource f mid n s c d → S.cleanups (Machine.world (O.core c)) ≡ cleanupsP s
 fork-source {mid = mid} {s = s} (Old.responderSource m found callback advanced) = outbound-same (O.inbound (Machine.igStep (IG.forkResponder mid))) (P.source s) advanced tt
 fork-source (Old.initiatorSource descriptor found unchanged) = cong (λ c → S.cleanups (Machine.world (O.core c))) unchanged
 fork-valid : ∀ w j gen s {t} → Old.Fork w j gen s t → Valid s → Valid t
 fork-valid w j gen s observation valid rewrite Old.Fork.after-shape observation =
   pool-valid w (Old.Fork.ownerFrame observation) (Old.Fork.poolAfter observation)
     (P.setSource (Old.Fork.sourceAfter observation) s) (cong present (Old.Fork.frame-before observation))
     (source-valid (Old.Fork.sourceAfter observation) s (fork-source (Old.Fork.source-boundary observation)) valid)
 commit-valid : ∀ j s {t} → Old.CompletionCommit j s t → Valid s → Valid t
 commit-valid j s observation valid rewrite Old.CompletionCommit.after-shape observation =
   pending-valid (Old.CompletionCommit.capturedJob observation) j _
     (source-valid (Old.CompletionCommit.sourceAfter observation) s
       (body-source-same (Old.CompletionCommit.capturedJob observation) (Old.CompletionCommit.outcome observation) s (Old.CompletionCommit.actual-source-commit observation)) valid)
 body-valid : ∀ j s {t} → Old.BodyReturn j s t → Valid s → Valid t
 body-valid j s observation valid rewrite Old.BodyReturn.after-shape observation =
   pool-valid (Types.owner (Old.BodyReturn.capturedJob observation))
     (Old.BodyReturn.ownerFrame observation) (Old.BodyReturn.poolAfter observation) s
     (cong present (Old.BodyReturn.frame-before observation)) valid
 publication-valid : ∀ j s {t} → Old.Publication j s t → Valid s → Valid t
 publication-valid j s observation valid rewrite Old.Publication.after-shape observation =
   removed-valid (Old.Publication.capturedJob observation) (Old.Publication.remainingPending observation) _
     (pool-valid (Types.owner (Old.Publication.capturedJob observation))
       (Old.Publication.ownerFrame observation) (Old.Publication.poolAfter observation)
       (P.setSource (Old.Publication.sourceAfter observation) s)
       (cong present (Old.Publication.frame-before observation))
       (source-valid (Old.Publication.sourceAfter observation) s
         (publication-source-same j (Old.Publication.capturedJob observation) (Old.Publication.outcome observation) s (Old.Publication.actual-source observation)) valid))
 returned : ∀ j s {t} → P.returned j s ≡ just t → Valid s → Valid t
 returned j s eq valid with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with Types.phase job
 ...   | Types.executing with P.hasWanton j job s
 ...     | false = case eq of λ ()
 ...     | true = case just-injective eq of λ { refl → valid }
 returned j s eq valid | just job | Types.waitingEgress = case eq of λ ()
 returned j s eq valid | just job | Types.resultCaptured result = case eq of λ ()
 registered : ∀ j s {t} → P.register j s ≡ just t → Valid s → Valid t
 registered j s eq valid with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) in found | Pool.parentFork (P.poolAt (Types.owner job) s)
 ...   | just f | just current with j ≟ current
 ...     | no _ = case eq of λ ()
 ...     | yes _ with Pool.step Pool.register (P.poolAt (Types.owner job) s)
 ...       | nothing = case eq of λ ()
 ...       | just p = case just-injective eq of λ { refl → pool-valid (Types.owner job) f p s (cong present found) valid }
 registered j s eq valid | just job | nothing | _ = case eq of λ ()
 registered j s eq valid | just job | just f | nothing = case eq of λ ()
 via-protocol : ∀ j a s {t} → P.viaProtocol j a s ≡ just t → Valid s → Valid t
 via-protocol j a s eq valid with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) in found | Pool.step a (P.poolAt (Types.owner job) s)
 ...   | just f | just p = case just-injective eq of λ { refl → pool-valid (Types.owner job) f p s (cong present found) valid }
 ...   | nothing | _ = case eq of λ ()
 ...   | just f | nothing = case eq of λ ()
 via-infra : ∀ w role a s {t} → P.viaInfra w role a s ≡ just t → Valid s → Valid t
 via-infra w role a s eq valid with lookup w (U.frames (P.base s)) in found
 ... | nothing = case eq of λ ()
 ... | just f with P.infraId role (Startup.phase (U.startup f))
 ...   | nothing = case eq of λ ()
 ...   | just j with Pool.step (a j) (P.poolAt w s)
 ...     | nothing = case eq of λ ()
 ...     | just p = case just-injective eq of λ { refl → pool-valid w f p s (cong present found) valid }
 control : ∀ w a s {t} → P.monitorControl w a s ≡ just t → Valid s → Valid t
 control w a s eq valid with lookup w (U.frames (P.base s))
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | P.monitoring f | P.noParent (P.poolAt w s)
 ...   | U.promisePublished hid mid | true | true with P.muxAt mid s
 ...     | nothing = case eq of λ ()
 ...     | just m with P.controlReady a m (P.poolAt w s)
 ...       | false = case eq of λ ()
 ...       | true with O.advance (O.inbound (Machine.igStep (P.sourceControl a mid))) (P.source s) in advanced
 ...         | nothing = case eq of λ ()
 ...         | just c = case just-injective eq of λ { refl → source-valid c s (outbound-same (O.inbound (Machine.igStep (P.sourceControl a mid))) (P.source s) advanced tt) valid }
 control w a s eq valid | just f | U.returnedSuccess | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.handleAllocated hid mid | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.promisePublished hid mid | false | _ = case eq of λ ()
 control w a s eq valid | just f | U.promisePublished hid mid | true | false = case eq of λ ()
 egress-valid : ∀ s {t} → Old.EgressChange s t → Valid s → Valid t
 egress-valid s observation valid rewrite Old.EgressChange.after-shape observation =
   source-valid (Old.EgressChange.sourceAfter observation) s
     (outbound-same (O.inbound (Machine.igStep (IG.egressStep (Old.EgressChange.capturedMux observation) (Old.EgressChange.operation observation)))) (P.source s) (Old.EgressChange.actual-source observation) tt) valid
 db-valid : ∀ a s {t} → P.viaDb a s ≡ just t → Valid s → Valid t
 db-valid a s eq valid with P.viaDb-source a s eq
 ... | c , advanced , refl = source-valid c s (outbound-same (O.inbound (Machine.igStep (IG.leiosDb a))) (P.source s) advanced tt) valid
 step-preserves : ∀ a s {t} → P.step a s ≡ just t → Valid s → Valid t
 step-preserves (P.run a) = inherited a
 step-preserves (P.forkResponder w j gen) s eq = fork-valid w j gen s (Old.responder-fork-observation w j gen s eq)
 step-preserves (P.forkInitiator w j gen n) s eq = fork-valid w j gen s (Old.initiator-fork-observation w j gen n s eq)
 step-preserves (P.registerProtocol j) = registered j
 step-preserves (P.enterProtocolBody j) s eq = egress-valid s (Old.enter-observation j s eq)
 step-preserves (P.appendProtocolPayload j bytes) s eq = egress-valid s (Old.send-observation j bytes s eq)
 step-preserves (P.egressMuxer w action) s eq = egress-valid s (Old.muxer-egress-observation w action s eq)
 step-preserves (P.protocolReturned j) s eq = returned j s (P.unlessAwaiting-just j s _ eq)
 step-preserves (P.commitClean j) s eq = commit-valid j s (Old.clean-observation j s eq)
 step-preserves (P.protocolException j err) s eq = commit-valid j s (Old.exception-observation j err s eq)
 step-preserves (P.returnProtocol j) s eq = body-valid j s (Old.return-observation j s eq)
 step-preserves (P.publishProtocol j) s eq = publication-valid j s (Old.publication-observation j s eq)
 step-preserves (P.deregisterProtocol j) = via-protocol j (Pool.deregister j)
 step-preserves (P.asyncProtocolResult j) = via-protocol j (Pool.publishAsyncResult j)
 step-preserves (P.infrastructureReturn w role err) = via-infra w role (λ j → Pool.bodyReturnedWith j (Types.infraResult role err))
 step-preserves (P.publishInfra w role) = via-infra w role Pool.publishCompletion
 step-preserves (P.deregisterInfra w role) = via-infra w role Pool.deregister
 step-preserves (P.asyncInfraResult w role) = via-infra w role Pool.publishAsyncResult
 step-preserves (P.control w a) = control w a
 step-preserves (P.submitDbWrite j d) s eq = db-valid _ s (P.submitDb-via j d s eq)
 step-preserves (P.awaitDbWrite j) s eq = db-valid _ s (P.awaitDb-via j s eq)
 step-preserves (P.writerComplete d) s eq = db-valid _ s eq
 step-preserves (P.writerSeal err) s eq = db-valid _ s eq
 step-preserves (P.dbWriteFailed j) s eq valid with P.dbFailure-via j s eq
 ... | P.refused err failed = commit-valid j s (Old.exception-observation j err s failed) valid
 ... | P.abandoned err mid abandon failed = commit-valid j mid (Old.exception-observation j err mid failed) (db-valid _ s abandon valid)
 initial-valid : ∀ c {s} → (∀ q → F q ≡ true) → (∀ q → K q ≡ false) → P.initial c ≡ just s → Valid s
 initial-valid c allF noK eq with U.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just u = case just-injective eq of λ { refl → MV.initial-valid c allF noK actual }

import ConnectionManagement.MuxResultMonitor as MonitorModel
open import ConnectionManagement.IGTypes using (clean; errored)
module Monitor (isBearerClosed : ErrorId → Bool) (F : WorkerId → Bool) (C : WorkerId → Maybe S.CleanupPC) (K : WorkerId → Bool) where
 private module W = MonitorModel isBearerClosed using (Action; State; base; beginDead; commitTracer; consume; deadAction; deadReady; deadTracing; delegateAllowed; demuxFinish; failed; findCaptured; finishDead; finishMatches; finishMux; finishProtocol; finishProtocolTrace; finished; handleHead; handleProtocol; handleSelected; inherit; initial; initiatorTracing; legacyMatches; muxAt; ownerContext; pcAt; poolAt; protocolSource; recordFinish; responderTracing; run; sampleTracer; selectHead; selected; setPC; setSource; source; startDead; statusAction; step; traceSource; tracing; viaSource; waiting)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base; initial; jobs; monitoring; noParent; step)
 private module U = P.U using (base; frames; handleAllocated; progress; promisePublished; returnedSuccess)
 private module Pool = P.Pool using (completions; consumeCompletion; step)
 private module PV = Protocol F C K
 Valid : W.State → Set
 Valid s = PV.Valid (W.base s)
 record CIPaths (before after : W.State) : Set where
  constructor paths
  field preserves : Valid before → Valid after
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = paths (λ valid → valid)
 ci-pc-paths : ∀ w pc s → CIPaths s (W.setPC w pc s)
 ci-pc-paths w pc s = paths (λ valid → valid)
 ci-compose : ∀ {p q r} → CIPaths p q → CIPaths q r → CIPaths p r
 ci-compose first second = paths (λ valid → CIPaths.preserves second (CIPaths.preserves first valid))
 ci-source-step : ∀ action s {c} → O.advance (O.inbound (Machine.igStep action)) (W.source s) ≡ just c → CIPaths s (W.setSource c s)
 ci-source-step action s {c} eq = paths (λ valid → PV.source-valid c (W.base s) (outbound-same (O.inbound (Machine.igStep action)) (W.source s) eq tt) valid)
 inherited : ∀ a s {t} → W.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with W.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with P.step a (W.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → PV.step-preserves a (W.base s) actual valid }
 owner-found : ∀ w s {f mid} → W.ownerContext w s ≡ just (f , mid) → lookup w (U.frames (P.base (W.base s))) ≡ just f
 owner-found w s eq with lookup w (U.frames (P.base (W.base s))) in found
 ... | nothing = case eq of λ ()
 ... | just actual with U.progress actual | P.monitoring actual
 ...   | U.promisePublished hid mid | true = case just-injective eq of λ { refl → refl }
 ...   | U.promisePublished hid mid | false = case eq of λ ()
 ...   | U.returnedSuccess | _ = case eq of λ ()
 ...   | U.handleAllocated hid mid | _ = case eq of λ ()
 ci-via-projects : ∀ action s {s′} → W.viaSource action s ≡ just s′ → CIPaths s s′
 ci-via-projects action s eq with O.advance (O.inbound (Machine.igStep action)) (W.source s) in advanced
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → ci-source-step action s advanced }
 ci-select-projects : ∀ w s {s′} → W.selectHead w s ≡ just s′ → CIPaths s s′
 ci-select-projects w s eq with W.pcAt w s | W.ownerContext w s in context
 ... | W.waiting | just (f , mid) with W.muxAt mid s | P.noParent (W.poolAt w s) | Pool.completions (W.poolAt w s)
 ...   | just m | true | item ∷ rest with WireMux.status m | WireMux.callback m
 ...     | WireMux.ready | WireMux.returned with Pool.step Pool.consumeCompletion (W.poolAt w s) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → paths (λ valid → PV.pool-valid w f next (W.base s) (cong present (owner-found w s context)) valid) }
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.stopping | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.stopped | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.failed err | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.readActive tr = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.commitTrace active tr = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.afterStart n = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.forkPending n = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.afterFailure = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.tracerFailed n = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | nothing | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just _ | false | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just _ | true | [] = case eq of λ ()
 ci-select-projects w s eq | W.waiting | nothing = case eq of λ ()
 ci-select-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-select-projects w s eq | W.responderTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.finished outcome | _ = case eq of λ ()

 ci-pc-after : ∀ w pc {before after} → CIPaths before after → CIPaths before (W.setPC w pc after)
 ci-pc-after w pc {after = after} path = ci-compose path (ci-pc-paths w pc after)
 ci-protocol-source-projects : ∀ w mid dir n outcome s {s′} → W.protocolSource w mid dir n outcome s ≡ just s′ → CIPaths s s′
 ci-protocol-source-projects w mid WireMux.responderJob n outcome s eq with W.muxAt mid s
 ... | nothing = case eq of λ ()
 ... | just m with W.legacyMatches n outcome (WireMux.completions m)
 ...   | false = case eq of λ ()
 ...   | true with W.viaSource (IG.monitorCompletion mid) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-pc-after w (W.responderTracing outcome) (ci-via-projects (IG.monitorCompletion mid) s advanced) }
 ci-protocol-source-projects w mid WireMux.initiatorJob n clean s eq = case just-injective eq of λ { refl → ci-pc-paths w (W.initiatorTracing clean) s }
 ci-protocol-source-projects w mid WireMux.initiatorJob n (errored err) s eq with W.viaSource (IG.recordMuxFailure mid err) s in advanced
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → ci-pc-after w (W.initiatorTracing (errored err)) (ci-via-projects (IG.recordMuxFailure mid err) s advanced) }
 ci-handle-protocol-projects : ∀ w dir n gen outcome s {s′} → W.handleProtocol w dir n gen outcome s ≡ just s′ → CIPaths s s′
 ci-handle-protocol-projects w dir n gen outcome s eq with W.ownerContext w s | W.findCaptured w dir n gen outcome (P.jobs (W.base s))
 ... | just (f , mid) | just (j , job) with does (Types.mux job ≟ mid) | W.muxAt mid s
 ...   | true | just m with WireMux.status m | WireMux.callback m
 ...     | WireMux.ready | WireMux.returned = ci-protocol-source-projects w mid dir n outcome s eq
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.stopping | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.stopped | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.failed err | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.readActive tr = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.commitTrace active tr = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.afterStart k = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.forkPending k = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.afterFailure = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.tracerFailed k = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | false | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | nothing = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | nothing | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just _ | nothing = case eq of λ ()
 ci-record-finish-projects : ∀ w outcome s {s′} → W.recordFinish w outcome s ≡ just s′ → CIPaths s s′
 ci-record-finish-projects w outcome s eq with W.ownerContext w s
 ... | nothing = case eq of λ ()
 ... | just (f , mid) with W.viaSource (W.statusAction outcome mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-pc-after w (W.deadReady outcome) (ci-via-projects (W.statusAction outcome mid) s advanced) }
 ci-handle-projects : ∀ w s {s′} → W.handleHead w s ≡ just s′ → CIPaths s s′
 ci-handle-projects w s eq with W.pcAt w s
 ... | W.selected (Types.protocolCompletion dir n gen outcome) = ci-handle-protocol-projects w dir n gen outcome s eq
 ... | W.selected (Types.infraMuxer err) = ci-record-finish-projects w (W.failed err) s eq
 ... | W.selected (Types.infraDemuxer err) = ci-record-finish-projects w (W.demuxFinish w err s) s eq
 ... | W.waiting = case eq of λ ()
 ... | W.responderTracing _ = case eq of λ ()
 ... | W.initiatorTracing _ = case eq of λ ()
 ... | W.deadReady _ = case eq of λ ()
 ... | W.deadTracing _ = case eq of λ ()
 ... | W.finished _ = case eq of λ ()
 ci-trace-projects : ∀ sample w s {s′} → W.traceSource sample w s ≡ just s′ → CIPaths s s′
 ci-trace-projects sample w s eq with W.tracing (W.pcAt w s) | W.ownerContext w s
 ... | true | just (f , mid) with sample
 ...   | true = ci-via-projects (IG.sampleTracer mid) s eq
 ...   | false = ci-via-projects (IG.commitTracer mid) s eq
 ci-trace-projects sample w s eq | false | _ = case eq of λ ()
 ci-trace-projects sample w s eq | true | nothing = case eq of λ ()
 ci-finish-protocol-projects : ∀ w s {s′} → W.finishProtocol w s ≡ just s′ → CIPaths s s′
 ci-finish-protocol-projects w s eq with W.pcAt w s | W.ownerContext w s
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.waiting) s }
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.afterFailure = case just-injective eq of λ { refl → ci-pc-paths w (W.deadReady (W.failed err)) s }
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.returned = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.waiting) s }
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.deadReady (W.failed err)) s }
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing result | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.waiting | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.finished outcome | _ = case eq of λ ()

 ci-start-dead-projects : ∀ w s {s′} → W.startDead w s ≡ just s′ → CIPaths s s′
 ci-start-dead-projects w s eq with W.pcAt w s | W.ownerContext w s
 ... | W.deadReady outcome | just (f , mid) with W.muxAt mid s
 ...   | just m with W.finishMatches outcome (WireMux.status m) | W.deadAction outcome (WireMux.callback m) mid
 ...     | true | just action with W.viaSource action s in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → ci-pc-after w (W.deadTracing outcome) (ci-via-projects action s advanced) }
 ci-start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | just m | false | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | just m | true | nothing = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | nothing = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadReady outcome | nothing = case eq of λ ()
 ci-start-dead-projects w s eq | W.waiting | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.responderTracing result | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.finished outcome | _ = case eq of λ ()
 ci-finish-dead-projects : ∀ w s {s′} → W.finishMux w s ≡ just s′ → CIPaths s s′
 ci-finish-dead-projects w s eq with W.pcAt w s | W.ownerContext w s
 ... | W.deadTracing outcome | just (f , mid) with W.muxAt mid s
 ...   | just m with WireMux.callback m | W.finishMatches outcome (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → ci-pc-paths w (W.finished outcome) s }
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.readActive tr | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.commitTrace active tr | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.afterStart n | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.forkPending n | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.afterFailure | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.tracerFailed n | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.returned | false = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | nothing = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | nothing = case eq of λ ()
 ci-finish-dead-projects w s eq | W.waiting | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.responderTracing result | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.finished outcome | _ = case eq of λ ()

 step-preserves : ∀ action s {s′} → W.step action s ≡ just s′ → Valid s → Valid s′
 step-preserves (W.run action) s eq = inherited action s eq
 step-preserves (W.consume w) s eq = CIPaths.preserves (ci-select-projects w s eq)
 step-preserves (W.handleSelected w) s eq = CIPaths.preserves (ci-handle-projects w s eq)
 step-preserves (W.sampleTracer w) s eq = CIPaths.preserves (ci-trace-projects true w s eq)
 step-preserves (W.commitTracer w) s eq = CIPaths.preserves (ci-trace-projects false w s eq)
 step-preserves (W.finishProtocolTrace w) s eq = CIPaths.preserves (ci-finish-protocol-projects w s eq)
 step-preserves (W.beginDead w) s eq = CIPaths.preserves (ci-start-dead-projects w s eq)
 step-preserves (W.finishDead w) s eq = CIPaths.preserves (ci-finish-dead-projects w s eq)
 initial-valid : ∀ c {s} → (∀ q → F q ≡ true) → (∀ q → K q ≡ false) → W.initial c ≡ just s → Valid s
 initial-valid c allF noK eq with P.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → PV.initial-valid c allF noK actual }
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.Properties.MuxGroupShutdown as GroupProperties
module Group (isBearerClosed : ErrorId → Bool) (F : WorkerId → Bool) (C : WorkerId → Maybe S.CleanupPC) (K : WorkerId → Bool) where
 private module W = GroupModel isBearerClosed using (Action; module M; State; abortMonitor; abortOwner; abortStage; asyncDead; asyncDeadTracing; asyncExit; asyncFailure; asyncFailureWritten; asyncTrace; base; beginAsyncDead; beginWhole; beginWholeClose; cancelPC; captureGroup; captureMini; childEligible; commitAsyncTracer; commitStoppedTracer; delegateAllowed; deliverGroup; deliverMini; deliverWhole; deliverWholeChild; delivered; discardClean; drainEmpty; drainReady; draining; failedExit; findOwner; finishAsync; finishAsyncDead; finishChildUnwind; finishGroup; finishMini; finishNormalScope; finishOrdinary; finishStopped; finishStoppedTrace; finishWhole; finishWholeClose; frameAt; fromPhase; groupClosing; idle; inherit; initial; isInfra; joinGroup; joinMini; joinMiniHead; joinWhole; joined; miniMember; monitorReturnedNormal; normalExit; observeStoppingTrace; observeTraceStopped; ownerAborting; ownerContext; ownerOf; phase; poolAt; prepareUnwind; protocolState; ready; registeredMini; remaining; replaceUnwind; replacementEligible; requestGroup; requestGroupCancel; requestShutdown; requestStop; retireFor; retireAllowed; retireCounters; requestWholeCancel; requested; run; sameStage; sampleAsyncTracer; sampleStoppedTracer; scopeDone; selectShutdown; selectStop; setFrame; setPhase; setPool; setProtocols; setSource; shutdownSelected; source; sourcePhase; step; stoppedTrace; stoppedTracing; stoppingTraced; stoppingWritten; timeout2Elapsed; unwindChild; unwindReplacedBySync; viaPool; viaSource; wholeAction; wholeClosed; wholeClosing; wholeDeliverable; wholeOutcome; writeAsyncFailure; writeStopped; writeStopping)
 private module M = W.M using (deadReady; deadTracing; failed; finishMatches; finished; initial; initiatorTracing; pcAt; responderTracing; selected; step; waiting)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base; jobs; locate; muxAt; noParent; noResults; pendingAt; protocolException; sameOutcome; step)
 private module U = P.U using (module Startup; Frame; frames; handleAllocated; progress; promisePublished; returnedSuccess; startup)
 private module Startup = U.Startup using (pool)
 private module Pool = P.Pool using (beginClose; bodyReturned; bodyRunning; bodyUnwinding; bodyUnwound; cancelPending; closedPool; closing; deliverCancel; deregisterPending; deregistered; finishClose; handles; interruptJob; join; joinPending; openPool; phase; requestCancel; resultAvailable; resumeAfterUnwindError; sameSnapshot; step)
 private module Lower = Monitor isBearerClosed F C K using (Valid; owner-found; step-preserves)
 private module PV = Protocol F C K
 open W using (remaining; joined; cancelPC)
 Valid : W.State → Set
 Valid s = Lower.Valid (W.base s)
 record CIPaths (before after : W.State) : Set where
  constructor paths
  field preserves : Valid before → Valid after
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = paths (λ valid → valid)
 ci-compose : ∀ {p q r} → CIPaths p q → CIPaths q r → CIPaths p r
 ci-compose first second = paths (λ valid → CIPaths.preserves second (CIPaths.preserves first valid))
 ci-frame-paths : ∀ w f s → CIPaths s (W.setFrame w f s)
 ci-frame-paths w f s = paths (λ valid → valid)
 ci-phase-paths : ∀ w pc s → CIPaths s (W.setPhase w pc s)
 ci-phase-paths w pc s = ci-frame-paths w _ s
 ci-phase-after : ∀ w pc {before after} → CIPaths before after → CIPaths before (W.setPhase w pc after)
 ci-phase-after w pc {after = after} path = ci-compose path (ci-phase-paths w pc after)
 ci-frame-after : ∀ w f {before after} → CIPaths before after → CIPaths before (W.setFrame w f after)
 ci-frame-after w f {after = after} path = ci-compose path (ci-frame-paths w f after)
 ci-protocol-projects : ∀ s p → (PV.Valid (W.protocolState s) → PV.Valid p) → CIPaths s (W.setProtocols p s)
 ci-protocol-projects s p proof = paths proof
 ci-source-step : ∀ action s {c} → O.advance (O.inbound (Machine.igStep action)) (W.source s) ≡ just c → CIPaths s (W.setSource c s)
 ci-source-step action s {c} eq = paths (λ valid → PV.source-valid c (W.protocolState s) (outbound-same (O.inbound (Machine.igStep action)) (W.source s) eq tt) valid)
 inherited : ∀ a s {t} → W.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with W.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with M.step a (W.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just m = case just-injective eq of λ { refl → Lower.step-preserves a (W.base s) actual valid }
 owner-found : ∀ w s {f mid} → W.ownerContext w s ≡ just (f , mid) → lookup w (U.frames (P.base (W.protocolState s))) ≡ just f
 owner-found w s found = Lower.owner-found w (W.base s) found
 -- The owner found for a job is a key of the frame table.
 cons-present : ∀ {A : Set} w q (x : A) (rows : Store WorkerId A) → present (lookup w rows) ≡ true → present (lookup w ((q , x) ∷ rows)) ≡ true
 cons-present w q x rows p with w ≟ q
 ... | yes _ = refl
 ... | no _ = p
 find-found : ∀ j rows {w f} → W.findOwner j rows ≡ just (w , f) → present (lookup w rows) ≡ true
 find-found j [] ()
 find-found j ((q , first) ∷ rows) eq with lookup j (Pool.handles (Startup.pool (U.startup first)))
 ... | just result = case just-injective eq of λ { refl → cong present (lookup-head q first rows) }
 ... | nothing = cons-present _ q first rows (find-found j rows eq)
 ownerOf-found : ∀ j s {w f} → W.ownerOf j s ≡ just (w , f) → present (lookup w (U.frames (P.base (W.protocolState s)))) ≡ true
 ownerOf-found j s eq = find-found j (U.frames (P.base (W.protocolState s))) eq
 ci-via-source-projects : ∀ action s {s′} → W.viaSource action s ≡ just s′ → CIPaths s s′
 ci-via-source-projects action s eq with O.advance (O.inbound (Machine.igStep action)) (W.source s) in advanced
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → ci-source-step action s advanced }
 ci-pool-step : ∀ w f action s {p} → Pool.step action (W.poolAt w s) ≡ just p →
   present (lookup w (U.frames (P.base (W.protocolState s)))) ≡ true → CIPaths s (W.setPool w f p s)
 ci-pool-step w f action s {p} eq pw = paths (λ valid → PV.pool-valid w f p (W.protocolState s) pw valid)
 ci-via-pool-projects : ∀ w action s {s′} → W.viaPool w action s ≡ just s′ → CIPaths s s′
 ci-via-pool-projects w action s eq with W.ownerContext w s in context
 ... | nothing = case eq of λ ()
 ... | just (f , mid) with Pool.step action (W.poolAt w s) in advanced
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → ci-pool-step w f action s advanced (cong present (owner-found w s context)) }
 ci-from-phase-projects : ∀ w before after s {s′} → W.fromPhase w before after s ≡ just s′ → CIPaths s s′
 ci-from-phase-projects w before after s eq with W.sameStage before (W.phase (W.frameAt w s))
 ... | false = case eq of λ ()
 ... | true = case just-injective eq of λ { refl → ci-phase-paths w after s }
 ci-source-phase-projects : ∀ w before after action s {s′} → W.sourcePhase w before after action s ≡ just s′ → CIPaths s s′
 ci-source-phase-projects w before after action s eq with W.sameStage before (W.phase (W.frameAt w s)) | W.ownerContext w s
 ... | true | just (f , mid) with W.viaSource (action mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w after (ci-via-source-projects (action mid) s advanced) }
 ci-source-phase-projects w before after action s eq | false | _ = case eq of λ ()
 ci-source-phase-projects w before after action s eq | true | nothing = case eq of λ ()
 ci-request-projects : ∀ w s {s′} → W.requestStop w s ≡ just s′ → CIPaths s s′
 ci-request-projects w s eq with lookup w (U.frames (P.base (W.protocolState s)))
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.promisePublished hid mid = ci-via-source-projects (IG.enqueueMuxStop mid) s eq
 ...   | U.returnedSuccess = case eq of λ ()
 ...   | U.handleAllocated hid mid = case eq of λ ()
 -- Counter retirement writes only the actual IG registry at scopeDone.
 ci-retire-projects : ∀ w s {s′} → W.retireFor w s ≡ just s′ → CIPaths s s′
 ci-retire-projects w s eq with W.retireAllowed (W.phase (W.frameAt w s))
 ... | false = case eq of λ ()
 ... | true with lookup w (U.frames (P.base (W.protocolState s)))
 ...   | nothing = case eq of λ ()
 ...   | just f with U.progress f
 ...     | U.promisePublished hid mid = ci-via-source-projects (IG.retireCells mid) s eq
 ...     | U.returnedSuccess = case eq of λ ()
 ...     | U.handleAllocated hid mid = case eq of λ ()
 ci-select-projects : ∀ w s {s′} → W.selectStop w s ≡ just s′ → CIPaths s s′
 ci-select-projects w s eq with W.phase (W.frameAt w s) | M.pcAt w (W.base s) | W.ownerContext w s
 ... | W.idle | M.waiting | just (f , mid) with P.noParent (W.poolAt w s) | P.noResults (W.poolAt w s)
 ...   | true | true with W.viaSource (IG.takeShutdownCommand mid) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-phase-after w W.shutdownSelected (ci-via-source-projects (IG.takeShutdownCommand mid) s advanced) }
 ci-select-projects w s eq | W.idle | M.waiting | just (f , mid) | false | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.waiting | just (f , mid) | true | false = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.waiting | nothing = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.selected item | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.responderTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.initiatorTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.deadReady outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.deadTracing outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.finished outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-capture-projects : ∀ w order s {s′} → W.captureMini w order s ≡ just s′ → CIPaths s s′
 ci-capture-projects w order s eq with W.phase (W.frameAt w s) | Pool.sameSnapshot order (W.registeredMini w s) | P.noParent (W.poolAt w s)
 ... | W.stoppingWritten | true | true = case just-injective eq of λ { refl → ci-frame-paths w _ s }
 ... | W.stoppingWritten | false | _ = case eq of λ ()
 ... | W.stoppingWritten | true | false = case eq of λ ()
 ci-capture-projects w order s eq | W.idle | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.draining | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-request-group-projects : ∀ w s {s′} → W.requestGroup w s ≡ just s′ → CIPaths s s′
 ci-request-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.ready | j ∷ rest = case just-injective eq of λ { refl → ci-frame-paths w _ s }
 ... | W.groupClosing | W.ready | [] = case eq of λ ()
 ... | W.groupClosing | W.requested j | _ = case eq of λ ()
 ... | W.groupClosing | W.delivered j | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-deliver-group-projects : ∀ w s {s′} → W.deliverMini w s ≡ just s′ → CIPaths s s′
 ci-deliver-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.requested j | current ∷ rest with j ≟ current | W.miniMember w j s | W.childEligible j s
 ...   | yes same | true | true with W.viaPool w (Pool.interruptJob j) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-frame-after w _ (ci-via-pool-projects w (Pool.interruptJob j) s advanced) }
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | no apart | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | yes same | false | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | yes same | true | false = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | [] = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.ready | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.delivered j | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-join-head-projects : ∀ w current s {s′} → W.joinMiniHead w current s ≡ just s′ → CIPaths s s′
 ci-join-head-projects w current s eq with W.remaining (W.frameAt w s) | lookup current (Pool.handles (W.poolAt w s))
 ... | head ∷ rest | just (Pool.resultAvailable exit) with current ≟ head
 ...   | yes same = case just-injective eq of λ { refl → ci-frame-paths w _ s }
 ...   | no apart = case eq of λ ()
 ci-join-head-projects w current s eq | [] | _ = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | nothing = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just Pool.bodyRunning = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just (Pool.bodyReturned result) = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just Pool.bodyUnwinding = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just (Pool.deregisterPending exit) = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just (Pool.deregistered exit) = case eq of λ ()
 ci-join-group-projects : ∀ w s {s′} → W.joinMini w s ≡ just s′ → CIPaths s s′
 ci-join-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s)
 ... | W.groupClosing | W.requested j = ci-join-head-projects w j s eq
 ... | W.groupClosing | W.delivered j = ci-join-head-projects w j s eq
 ... | W.groupClosing | W.ready = case eq of λ ()
 ci-join-group-projects w s eq | W.idle | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.draining | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.drainReady | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.wholeClosed outcome | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-finish-group-projects : ∀ w s {s′} → W.finishMini w s ≡ just s′ → CIPaths s s′
 ci-finish-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.ready | [] = case just-injective eq of λ { refl → ci-phase-paths w W.draining s }
 ... | W.groupClosing | W.ready | _ ∷ _ = case eq of λ ()
 ... | W.groupClosing | W.requested j | _ = case eq of λ ()
 ... | W.groupClosing | W.delivered j | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-discard-projects : ∀ j job s {s′} → W.discardClean j job s ≡ just s′ → CIPaths s s′
 ci-discard-projects j job s eq with Types.direction job
 ... | WireMux.initiatorJob = case just-injective eq of λ { refl → ci-idle s }
 ... | WireMux.responderJob with P.locate j (P.pendingAt (Types.owner job) (W.protocolState s)) | P.muxAt (Types.mux job) (W.protocolState s)
 ...   | just (index , kept) | just m with IG.takePending index (WireMux.finishedJobs m)
 ...     | just ((n , result) , rest) with does (n Nat.≟ Types.protocolNumber job) ∧ P.sameOutcome ConnectionManagement.IGTypes.clean result
 ...       | true with W.viaSource (IG.discardJobOccurrence (Types.mux job) index) s in advanced
 ...         | nothing = case eq of λ ()
 ...         | just next = case just-injective eq of λ { refl → ci-compose
   (ci-via-source-projects (IG.discardJobOccurrence (Types.mux job) index) s advanced)
   (ci-protocol-projects next _ (λ valid → valid)) }
 ci-discard-projects j job s eq | WireMux.responderJob | just (index , kept) | just m | just ((n , result) , rest) | false = case eq of λ ()
 ci-discard-projects j job s eq | WireMux.responderJob | just (index , kept) | just m | nothing = case eq of λ ()
 ci-discard-projects j job s eq | WireMux.responderJob | nothing | _ = case eq of λ ()
 ci-discard-projects j job s eq | WireMux.responderJob | just pair | nothing = case eq of λ ()
 ci-prepare-projects : ∀ j w f s {s′} → W.prepareUnwind j w f s ≡ just s′ → CIPaths s s′
 ci-prepare-projects j w f s eq with lookup j (P.jobs (W.protocolState s))
 ... | nothing with W.isInfra j f
 ...   | true = case just-injective eq of λ { refl → ci-idle s }
 ...   | false = case eq of λ ()
 ci-prepare-projects j w f s eq | just job with does (w ≟ Types.owner job) | Types.phase job
 ... | true | Types.executing = case just-injective eq of λ { refl → ci-idle s }
 ... | true | Types.waitingEgress = case just-injective eq of λ { refl → ci-idle s }
 ... | true | Types.resultCaptured ConnectionManagement.IGTypes.clean = ci-discard-projects j job s eq
 ... | true | Types.resultCaptured (ConnectionManagement.IGTypes.errored err) = case eq of λ ()
 ... | false | _ = case eq of λ ()
 framesG : W.State → Store WorkerId U.Frame
 framesG s = U.frames (P.base (W.protocolState s))
 via-frames : ∀ action s {s′} → W.viaSource action s ≡ just s′ → framesG s′ ≡ framesG s
 via-frames action s eq with O.advance (O.inbound (Machine.igStep action)) (W.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → refl }
 discard-frames : ∀ j job s {s′} → W.discardClean j job s ≡ just s′ → framesG s′ ≡ framesG s
 discard-frames j job s eq with Types.direction job
 ... | WireMux.initiatorJob = case just-injective eq of λ { refl → refl }
 ... | WireMux.responderJob with P.locate j (P.pendingAt (Types.owner job) (W.protocolState s)) | P.muxAt (Types.mux job) (W.protocolState s)
 ...   | just (index , kept) | just m with IG.takePending index (WireMux.finishedJobs m)
 ...     | just ((n , result) , rest) with does (n Nat.≟ Types.protocolNumber job) ∧ P.sameOutcome ConnectionManagement.IGTypes.clean result
 ...       | true with W.viaSource (IG.discardJobOccurrence (Types.mux job) index) s in advanced
 ...         | nothing = case eq of λ ()
 ...         | just next = case just-injective eq of λ { refl → via-frames (IG.discardJobOccurrence (Types.mux job) index) s advanced }
 discard-frames j job s eq | WireMux.responderJob | just (index , kept) | just m | just ((n , result) , rest) | false = case eq of λ ()
 discard-frames j job s eq | WireMux.responderJob | just (index , kept) | just m | nothing = case eq of λ ()
 discard-frames j job s eq | WireMux.responderJob | nothing | _ = case eq of λ ()
 discard-frames j job s eq | WireMux.responderJob | just pair | nothing = case eq of λ ()
 prepare-frames : ∀ j w f s {s′} → W.prepareUnwind j w f s ≡ just s′ → framesG s′ ≡ framesG s
 prepare-frames j w f s eq with lookup j (P.jobs (W.protocolState s))
 ... | nothing with W.isInfra j f
 ...   | true = case just-injective eq of λ { refl → refl }
 ...   | false = case eq of λ ()
 prepare-frames j w f s eq | just job with does (w ≟ Types.owner job) | Types.phase job
 ... | true | Types.executing = case just-injective eq of λ { refl → refl }
 ... | true | Types.waitingEgress = case just-injective eq of λ { refl → refl }
 ... | true | Types.resultCaptured ConnectionManagement.IGTypes.clean = discard-frames j job s eq
 ... | true | Types.resultCaptured (ConnectionManagement.IGTypes.errored err) = case eq of λ ()
 ... | false | _ = case eq of λ ()
 ci-unwind-projects : ∀ j s {s′} → W.unwindChild j s ≡ just s′ → CIPaths s s′
 ci-unwind-projects j s eq with W.ownerOf j s in owned
 ... | nothing = case eq of λ ()
 ... | just (w , f) with lookup j (Pool.handles (W.poolAt w s))
 ...   | just Pool.bodyUnwinding with W.prepareUnwind j w f s in prepared
 ...     | nothing = case eq of λ ()
 ...     | just next with Pool.step (Pool.bodyUnwound j) (W.poolAt w next) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just p = case just-injective eq of λ { refl → paths
   (λ valid → PV.pool-valid w f p (W.protocolState next)
     (trans (cong (λ rows → present (lookup w rows)) (prepare-frames j w f s prepared)) (ownerOf-found j s owned))
     (CIPaths.preserves (ci-prepare-projects j w f s prepared) valid)) }
 ci-unwind-projects j s eq | just (w , f) | nothing = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just Pool.bodyRunning = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.bodyReturned result) = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.deregisterPending exit) = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.deregistered exit) = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.resultAvailable exit) = case eq of λ ()
 ci-replacement-projects : ∀ j err s {s′} → W.replaceUnwind j err s ≡ just s′ → CIPaths s s′
 ci-replacement-projects j err s eq with lookup j (P.jobs (W.protocolState s))
 ... | nothing = case eq of λ ()
 ... | just job with W.replacementEligible (Types.phase job) | W.ownerOf j s in owned
 ...   | true | just (w , f) with does (w ≟ Types.owner job) | Pool.step (Pool.resumeAfterUnwindError j) (W.poolAt w s) in advanced
 ...     | true | just p with P.step (P.protocolException j err) (W.protocolState (W.setPool w f p s)) in captured
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → ci-compose
   (ci-pool-step w f (Pool.resumeAfterUnwindError j) s advanced (ownerOf-found j s owned))
   (ci-protocol-projects (W.setPool w f p s) next
     (PV.step-preserves (P.protocolException j err) (W.protocolState (W.setPool w f p s)) captured)) }
 ci-replacement-projects j err s eq | just job | true | just (w , f) | false | _ = case eq of λ ()
 ci-replacement-projects j err s eq | just job | true | just (w , f) | true | nothing = case eq of λ ()
 ci-replacement-projects j err s eq | just job | false | _ = case eq of λ ()
 ci-replacement-projects j err s eq | just job | true | nothing = case eq of λ ()
 ci-abort-projects : ∀ w err s {s′} → W.abortMonitor w err s ≡ just s′ → CIPaths s s′
 ci-abort-projects w err s eq with W.abortStage w s | W.ownerContext w s | P.noParent (W.poolAt w s)
 ... | true | just (f , mid) | true with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.callback m
 ...     | WireMux.returned = case just-injective eq of λ { refl → ci-phase-paths w (W.ownerAborting err) s }
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.readActive tr = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.afterStart n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.forkPending n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.afterFailure = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | nothing = case eq of λ ()
 ci-abort-projects w err s eq | false | _ | _ = case eq of λ ()
 ci-abort-projects w err s eq | true | nothing | _ = case eq of λ ()
 ci-abort-projects w err s eq | true | just pair | false = case eq of λ ()
 ci-begin-whole-projects : ∀ w order s {s′} → W.beginWhole w order s ≡ just s′ → CIPaths s s′
 ci-begin-whole-projects w order s eq with W.wholeOutcome w s
 ... | nothing = case eq of λ ()
 ... | just outcome with W.viaPool w (Pool.beginClose order) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.wholeClosing outcome) (ci-via-pool-projects w (Pool.beginClose order) s advanced) }
 ci-whole-action-projects : ∀ w action s {s′} → W.wholeAction w action s ≡ just s′ → CIPaths s s′
 ci-whole-action-projects w action s eq with W.phase (W.frameAt w s)
 ... | W.wholeClosing outcome = ci-via-pool-projects w action s eq
 ci-whole-action-projects w action s eq | W.idle = case eq of λ ()
 ci-whole-action-projects w action s eq | W.shutdownSelected = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppingTraced = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppingWritten = case eq of λ ()
 ci-whole-action-projects w action s eq | W.groupClosing = case eq of λ ()
 ci-whole-action-projects w action s eq | W.draining = case eq of λ ()
 ci-whole-action-projects w action s eq | W.drainReady = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppedTrace = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppedTracing = case eq of λ ()
 ci-whole-action-projects w action s eq | W.monitorReturnedNormal = case eq of λ ()
 ci-whole-action-projects w action s eq | W.ownerAborting err = case eq of λ ()
 ci-whole-action-projects w action s eq | W.wholeClosed outcome = case eq of λ ()
 ci-whole-action-projects w action s eq | W.asyncFailureWritten err = case eq of λ ()
 ci-whole-action-projects w action s eq | W.asyncDeadTracing err = case eq of λ ()
 ci-whole-action-projects w action s eq | W.scopeDone outcome = case eq of λ ()
 ci-whole-delivery-projects : ∀ w s {s′} → W.deliverWholeChild w s ≡ just s′ → CIPaths s s′
 ci-whole-delivery-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s | Pool.phase (W.poolAt w s)
 ... | W.wholeClosing outcome | just (f , mid) | Pool.cancelPending j with W.wholeDeliverable w j f s
 ...   | true = ci-via-pool-projects w Pool.deliverCancel s eq
 ...   | false = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | nothing | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.openPool = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.closing = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.closedPool = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.joinPending j = case eq of λ ()
 ci-finish-whole-projects : ∀ w s {s′} → W.finishWhole w s ≡ just s′ → CIPaths s s′
 ci-finish-whole-projects w s eq with W.phase (W.frameAt w s)
 ... | W.wholeClosing outcome with W.viaPool w Pool.finishClose s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.wholeClosed outcome) (ci-via-pool-projects w Pool.finishClose s advanced) }
 ci-finish-whole-projects w s eq | W.idle = case eq of λ ()
 ci-finish-whole-projects w s eq | W.shutdownSelected = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppingTraced = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppingWritten = case eq of λ ()
 ci-finish-whole-projects w s eq | W.groupClosing = case eq of λ ()
 ci-finish-whole-projects w s eq | W.draining = case eq of λ ()
 ci-finish-whole-projects w s eq | W.drainReady = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppedTrace = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppedTracing = case eq of λ ()
 ci-finish-whole-projects w s eq | W.monitorReturnedNormal = case eq of λ ()
 ci-finish-whole-projects w s eq | W.ownerAborting err = case eq of λ ()
 ci-finish-whole-projects w s eq | W.wholeClosed outcome = case eq of λ ()
 ci-finish-whole-projects w s eq | W.asyncFailureWritten err = case eq of λ ()
 ci-finish-whole-projects w s eq | W.asyncDeadTracing err = case eq of λ ()
 ci-finish-whole-projects w s eq | W.scopeDone outcome = case eq of λ ()
 ci-async-failure-projects : ∀ w s {s′} → W.asyncFailure w s ≡ just s′ → CIPaths s s′
 ci-async-failure-projects w s eq with W.phase (W.frameAt w s) | Pool.phase (W.poolAt w s) | W.ownerContext w s
 ... | W.wholeClosed (W.asyncExit err) | Pool.closedPool | just (f , mid) with W.viaSource (IG.recordAsyncMuxFailure mid err) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.asyncFailureWritten err) (ci-via-source-projects (IG.recordAsyncMuxFailure mid err) s advanced) }
 ci-async-failure-projects w s eq | W.wholeClosed W.normalExit | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.failedExit err) | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.closedPool | nothing = case eq of λ ()
 ci-async-failure-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.openPool | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.closing | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.cancelPending j | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.joinPending j | _ = case eq of λ ()
 ci-async-dead-projects : ∀ w s {s′} → W.asyncDead w s ≡ just s′ → CIPaths s s′
 ci-async-dead-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s
 ... | W.asyncFailureWritten err | just (f , mid) with W.viaSource (IG.traceMuxDead mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.asyncDeadTracing err) (ci-via-source-projects (IG.traceMuxDead mid) s advanced) }
 ci-async-dead-projects w s eq | W.asyncFailureWritten err | nothing = case eq of λ ()
 ci-async-dead-projects w s eq | W.idle | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.groupClosing | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.draining | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.drainReady | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.wholeClosed outcome | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-async-trace-projects : ∀ sample w s {s′} → W.asyncTrace sample w s ≡ just s′ → CIPaths s s′
 ci-async-trace-projects sample w s eq with W.phase (W.frameAt w s) | W.ownerContext w s
 ... | W.asyncDeadTracing err | just (f , mid) with sample
 ...   | true = ci-via-source-projects (IG.sampleTracer mid) s eq
 ...   | false = ci-via-source-projects (IG.commitTracer mid) s eq
 ci-async-trace-projects sample w s eq | W.asyncDeadTracing err | nothing = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.idle | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.groupClosing | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.draining | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.drainReady | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.wholeClosed outcome | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-finish-async-projects : ∀ w s {s′} → W.finishAsync w s ≡ just s′ → CIPaths s s′
 ci-finish-async-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s | Pool.phase (W.poolAt w s)
 ... | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.callback m | M.finishMatches (M.failed err) (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone (W.asyncExit err)) s }
 ...     | WireMux.returned | false = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.readActive tr | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.commitTrace active tr | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.afterStart n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.forkPending n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.afterFailure | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.tracerFailed n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | nothing = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | nothing | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.openPool = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closing = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.cancelPending j = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.joinPending j = case eq of λ ()
 ci-finish-ordinary-projects : ∀ w s {s′} → W.finishOrdinary w s ≡ just s′ → CIPaths s s′
 ci-finish-ordinary-projects w s eq with W.phase (W.frameAt w s) | Pool.phase (W.poolAt w s)
 ... | W.wholeClosed W.normalExit | Pool.closedPool = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone W.normalExit) s }
 ... | W.wholeClosed (W.failedExit err) | Pool.closedPool = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone (W.failedExit err)) s }
 ... | W.wholeClosed (W.asyncExit err) | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.idle | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.groupClosing | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.draining | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.drainReady | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.openPool = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.closing = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.cancelPending j = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.joinPending j = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.openPool = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.closing = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.cancelPending j = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.joinPending j = case eq of λ ()
 ci-finish-stopped-projects : ∀ w s {s′} → W.finishStopped w s ≡ just s′ → CIPaths s s′
 ci-finish-stopped-projects w s eq with W.sameStage W.stoppedTracing (W.phase (W.frameAt w s)) | W.ownerContext w s
 ... | true | just (f , mid) with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.status m | WireMux.callback m
 ...     | WireMux.stopped | WireMux.returned = case just-injective eq of λ { refl → ci-phase-paths w W.monitorReturnedNormal s }
 ...     | WireMux.stopped | WireMux.readActive tr = case eq of λ ()
 ...     | WireMux.stopped | WireMux.commitTrace flag tr = case eq of λ ()
 ...     | WireMux.stopped | WireMux.afterStart n = case eq of λ ()
 ...     | WireMux.stopped | WireMux.forkPending n = case eq of λ ()
 ...     | WireMux.stopped | WireMux.afterFailure = case eq of λ ()
 ...     | WireMux.stopped | WireMux.tracerFailed n = case eq of λ ()
 ...     | WireMux.ready | _ = case eq of λ ()
 ...     | WireMux.stopping | _ = case eq of λ ()
 ...     | WireMux.failed err | _ = case eq of λ ()
 ci-finish-stopped-projects w s eq | true | just (f , mid) | nothing = case eq of λ ()
 ci-finish-stopped-projects w s eq | false | _ = case eq of λ ()
 ci-finish-stopped-projects w s eq | true | nothing = case eq of λ ()

 step-preserves : ∀ action s {s′} → W.step action s ≡ just s′ → Valid s → Valid s′
 step-preserves (W.run action) s eq = inherited action s eq
 step-preserves (W.requestShutdown w) s eq = CIPaths.preserves (ci-request-projects w s eq)
 step-preserves (W.retireCounters w) s eq = CIPaths.preserves (ci-retire-projects w s eq)
 step-preserves (W.selectShutdown w) s eq = CIPaths.preserves (ci-select-projects w s eq)
 step-preserves (W.observeStoppingTrace w) s eq = CIPaths.preserves (ci-from-phase-projects w W.shutdownSelected W.stoppingTraced s eq)
 step-preserves (W.writeStopping w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppingTraced W.stoppingWritten IG.recordMuxStopping s eq)
 step-preserves (W.captureGroup w order) s eq = CIPaths.preserves (ci-capture-projects w order s eq)
 step-preserves (W.requestGroupCancel w) s eq = CIPaths.preserves (ci-request-group-projects w s eq)
 step-preserves (W.deliverGroup w) s eq = CIPaths.preserves (ci-deliver-group-projects w s eq)
 step-preserves (W.joinGroup w) s eq = CIPaths.preserves (ci-join-group-projects w s eq)
 step-preserves (W.finishGroup w) s eq = CIPaths.preserves (ci-finish-group-projects w s eq)
 step-preserves (W.drainEmpty w) s eq = CIPaths.preserves (ci-from-phase-projects w W.draining W.drainReady s (GroupProperties.drain-phase isBearerClosed w s eq))
 step-preserves (W.timeout2Elapsed w) s eq = CIPaths.preserves (ci-from-phase-projects w W.draining W.drainReady s eq)
 step-preserves (W.writeStopped w) s eq = CIPaths.preserves (ci-source-phase-projects w W.drainReady W.stoppedTrace IG.completeMuxStopping s eq)
 step-preserves (W.observeTraceStopped w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppedTrace W.stoppedTracing IG.traceGracefulMuxStopped s eq)
 step-preserves (W.sampleStoppedTracer w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.sampleTracer s eq)
 step-preserves (W.commitStoppedTracer w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.commitTracer s eq)
 step-preserves (W.finishStoppedTrace w) s eq = CIPaths.preserves (ci-finish-stopped-projects w s eq)
 step-preserves (W.finishChildUnwind j) s eq = CIPaths.preserves (ci-unwind-projects j s eq)
 step-preserves (W.unwindReplacedBySync j err) s eq = CIPaths.preserves (ci-replacement-projects j err s eq)
 step-preserves (W.abortOwner w err) s eq = CIPaths.preserves (ci-abort-projects w err s eq)
 step-preserves (W.beginWholeClose w order) s eq = CIPaths.preserves (ci-begin-whole-projects w order s eq)
 step-preserves (W.requestWholeCancel w) s eq = CIPaths.preserves (ci-whole-action-projects w Pool.requestCancel s eq)
 step-preserves (W.deliverWhole w) s eq = CIPaths.preserves (ci-whole-delivery-projects w s eq)
 step-preserves (W.joinWhole w) s eq = CIPaths.preserves (ci-whole-action-projects w Pool.join s eq)
 step-preserves (W.finishWholeClose w) s eq = CIPaths.preserves (ci-finish-whole-projects w s eq)
 step-preserves (W.finishNormalScope w) s eq = CIPaths.preserves (ci-finish-ordinary-projects w s eq)
 step-preserves (W.writeAsyncFailure w) s eq = CIPaths.preserves (ci-async-failure-projects w s eq)
 step-preserves (W.beginAsyncDead w) s eq = CIPaths.preserves (ci-async-dead-projects w s eq)
 step-preserves (W.sampleAsyncTracer w) s eq = CIPaths.preserves (ci-async-trace-projects true w s eq)
 step-preserves (W.commitAsyncTracer w) s eq = CIPaths.preserves (ci-async-trace-projects false w s eq)
 step-preserves (W.finishAsyncDead w) s eq = CIPaths.preserves (ci-finish-async-projects w s eq)
 initial-valid : ∀ c {s} → (∀ q → F q ≡ true) → (∀ q → K q ≡ false) → W.initial c ≡ just s → Valid s
 initial-valid c allF noK eq with M.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just m = case just-injective eq of λ { refl → Monitor.initial-valid isBearerClosed F C K c allF noK actual }
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Rules.OutboundRelease as OutboundRelease
open import ConnectionManagement.Properties.CleanupWriters using (exit-effect; cleanup-effect; stepped)
-- The cleanup record an exit phase requires (independent of the kept set).
module ExitPhase (isBearerClosed : ErrorId → Bool) where
 private module W = ExitModel isBearerClosed using (Phase; bufferScope; classifying; errorTracing; peerRethrow; nodeDelivery; nodeRethrow; bodyExited; finalizing; cleanupComplete; resultAvailable)
 ExitExpected : W.Phase → Maybe S.CleanupPC → Set
 ExitExpected (W.bufferScope _) c = c ≡ nothing
 ExitExpected (W.classifying _) c = c ≡ nothing
 ExitExpected (W.errorTracing _ _) c = c ≡ nothing
 ExitExpected (W.peerRethrow _) c = c ≡ nothing
 ExitExpected (W.nodeDelivery _) c = c ≡ nothing
 ExitExpected (W.nodeRethrow _) c = c ≡ nothing
 ExitExpected (W.bodyExited _) c = c ≡ nothing
 ExitExpected (W.finalizing _) c = Σ S.CleanupPC (λ p → c ≡ just p)
 ExitExpected (W.cleanupComplete _ outcome) c = c ≡ just (S.cleanupDone outcome)
 ExitExpected (W.resultAvailable _ outcome) c = c ≡ just (S.cleanupDone outcome)
-- Exit frames own the cleanup records of their workers. A worker with an exit
-- frame is framed and excluded from the lower layers' agreement, so mux steps
-- leave its record intact; its own exit steps keep the record matching the
-- exit phase.
module Exit (isBearerClosed : ErrorId → Bool) (K : WorkerId → Bool) where
 private module W = ExitModel isBearerClosed using (Action; Frame; Phase; BodyResult; Plan; State; acknowledgeFinished; acknowledgeReleaseFinished; deliverReleaseMux; deliverReleaseTimeWait; releaseTarget; timeWaitTarget; releaseDelivery; releaseTimeWaitDelivery; base; beginExit; bodyExited; bufferScope; choose; choosePolicy; classifying; cleanup; cleanupComplete; cleanupException; cleanupFault; control; coordinator; currentCapture; delegateAllowed; deliverShutdownMux; deliverShutdownTimeWait; edit; effectiveResult; enact; enterFinalizer; errorTracing; exits; finalizing; finishCleanup; inherited; initial; local; machine; muxDelivery; nodeDelivery; nodeRethrow; noteCleanup; observeBufferException; observeBufferReturn; observeErrorTrace; observeNodeDelivery; peerRethrow; phase; phaseAfterBuffer; physical; poolAt; publishAsyncResult; resultAvailable; resultReady; rethrow; run; sameCleanup; sameStart; countersClear; setShutdown; setSource; shared; shutdown; shutdownStep; source; step; timeWaitDelivery; Executes; done; next)
 private module G = GroupModel isBearerClosed using (Outcome; abortOwner; asyncDeadTracing; asyncExit; asyncFailureWritten; drainReady; draining; failedExit; frameAt; groupClosing; idle; initial; monitorReturnedNormal; normalExit; ownerAborting; phase; protocolState; scopeDone; setPool; shutdownSelected; step; stoppedTrace; stoppedTracing; stoppingTraced; stoppingWritten; wholeClosed; wholeClosing)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base)
 private module U = P.U using (State; captured; frames; base; source)
 private module Pool = P.Pool using (cancelPending; closedPool; closing; joinPending; openPool; phase)
 uview : W.State → U.State
 uview s = P.base (G.protocolState (W.base s))
 cleanupsW : W.State → Store WorkerId S.CleanupPC
 cleanupsW s = S.cleanups (Machine.world (O.core (W.source s)))
 Free : W.State → WorkerId → Bool
 Free s q = not (present (lookup q (W.exits s)))
 Current : W.State → WorkerId → Maybe S.CleanupPC
 Current s q = lookup q (cleanupsW s)
 open ExitPhase isBearerClosed public
 record Valid (s : W.State) : Set where
  constructor exit-valid
  field lower : Mux.Valid (Free s) (Current s) K (uview s)
        exits-ok : ∀ q f → lookup q (W.exits s) ≡ just f → ExitExpected (W.phase f) (lookup q (cleanupsW s))
 open Valid public

 after-buffer : ∀ outcome c → c ≡ nothing → ExitExpected (W.phaseAfterBuffer outcome) c
 after-buffer G.normalExit c none = none
 after-buffer (G.failedExit err) c none = none
 after-buffer (G.asyncExit err) c none = none
 excluded : ∀ s {q f} → lookup q (W.exits s) ≡ just f → Free s q ≡ false
 excluded s found rewrite found = refl
 exit-at : ∀ {s w f p} → Valid s → lookup w (W.exits s) ≡ just f → W.phase f ≡ p → ExitExpected p (lookup w (cleanupsW s))
 exit-at {s} {w} {f} v found ph = subst (λ p → ExitExpected p (lookup w (cleanupsW s))) ph (exits-ok v w f found)
 -- Lower validity depends only on the excluded set and the frozen records.
 reframe : ∀ {F F′ C C′ u} → (∀ q → F′ q ≡ F q) → (∀ q → F′ q ≡ false → lookup q (Mux.cleanupsU F C K u) ≡ C′ q) →
   Mux.Valid F C K u → Mux.Valid F′ C′ K u
 reframe eqF frz v = Mux.mux-valid (Mux.relative v) (Mux.parked v)
   (λ q z f → Mux.clean v q z (trans (sym (eqF q)) f)) (λ q f → Mux.owned v q (trans (sym (eqF q)) f)) frz (Mux.kept v)

 -- Lower steps keep exit frames and every excluded record.
 g-step : ∀ a s {g} → G.step a (W.base s) ≡ just g → Valid s → Valid (record s { base = g })
 g-step a s {g} eq v = exit-valid (reframe (λ q → refl) (λ q f → refl) moved) ok
  where
  moved : Mux.Valid (Free s) (Current s) K (P.base (G.protocolState g))
  moved = Group.step-preserves isBearerClosed (Free s) (Current s) K a (W.base s) eq (lower v)
  ok : ∀ q f → lookup q (W.exits s) ≡ just f → ExitExpected (W.phase f) (lookup q (S.cleanups (Machine.world (O.core (W.source (record s { base = g }))))))
  ok q f found rewrite Mux.frozen moved q (excluded s found) = exits-ok v q f found
 source-quiet : ∀ c s → S.cleanups (Machine.world (O.core c)) ≡ cleanupsW s → Valid s → Valid (W.setSource c s)
 source-quiet c s cl v = exit-valid
   (reframe (λ q → refl) (λ q f → refl) (Mux.quiet (Free s) (Current s) K {s = uview s} {t = uview (W.setSource c s)} (λ q → refl) refl cl (lower v)))
   (λ q f found → subst (ExitExpected (W.phase f)) (cong (lookup q) (sym cl)) (exits-ok v q f found))
 shutdown-quiet : ∀ co s → Valid s → Valid (W.setShutdown co s)
 shutdown-quiet co s v = exit-valid
   (Mux.quiet (Free s) (Current s) K {s = uview s} {t = uview (W.setShutdown co s)} (λ q → refl) refl refl (lower v)) (exits-ok v)
 control-preserves : ∀ a s {t} → W.control a s ≡ just t → Valid s → Valid t
 control-preserves a s eq v with Close.step (S.cm (W.shared s)) (λ w → W.resultReady w s) a (W.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → shutdown-quiet next s v }

 keys-edit : ∀ w f g s → lookup w (W.exits s) ≡ just f → ∀ q → Free (record s { exits = put w g (W.exits s) }) q ≡ Free s q
 keys-edit w f g s found q with q ≟ w
 ... | yes refl rewrite lookup-put w g (W.exits s) | found = refl
 ... | no other rewrite lookup-put-other w q g (W.exits s) other = refl
 -- A local phase change of an existing exit frame.
 edit-valid : ∀ w f pc s → lookup w (W.exits s) ≡ just f → ExitExpected pc (lookup w (cleanupsW s)) → Valid s →
   Valid (record s { exits = W.edit w f pc s })
 edit-valid w f pc s found ok v = exit-valid (reframe (keys-edit w f _ s found) (λ q f′ → refl) (lower v)) ok′
  where
  ok′ : ∀ q g → lookup q (W.edit w f pc s) ≡ just g → ExitExpected (W.phase g) (lookup q (cleanupsW s))
  ok′ q g eq with q ≟ w
  ... | yes refl rewrite lookup-put w (record f { phase = pc }) (W.exits s) with just-injective eq
  ...   | refl = ok
  ok′ q g eq | no other rewrite lookup-put-other w q (record f { phase = pc }) (W.exits s) other = exits-ok v q g eq
 -- A new exit frame for a framed worker without one, which has no cleanup record.
 begin-valid : ∀ w outcome s → lookup w (W.exits s) ≡ nothing → present (lookup w (U.frames (uview s))) ≡ true →
   ∀ captured → Valid s → Valid (record s { exits = put w (ExitModel.exitFrame captured (W.bufferScope outcome) nothing) (W.exits s) })
 begin-valid w outcome s absent framed captured v = exit-valid (Mux.mux-valid (Mux.relative (lower v)) (Mux.parked (lower v)) cln own (λ q f → refl) kpt) ok
  where
  nf = ExitModel.exitFrame captured (W.bufferScope outcome) nothing
  t = record s { exits = put w nf (W.exits s) }
  free-w : Free s w ≡ true
  free-w rewrite absent = refl
  kpt : ∀ q → K q ≡ true → Mux.framedZ (Free t) (Current t) K (uview s) q ≡ true
  kpt = Mux.kept (lower v)
  cln : ∀ q → Mux.framedZ (Free t) (Current t) K (uview s) q ≡ true → Free t q ≡ true → lookup q (cleanupsW s) ≡ nothing
  cln q z fq with q ≟ w
  ... | yes refl rewrite lookup-put w nf (W.exits s) = case fq of λ ()
  ... | no other rewrite lookup-put-other w q nf (W.exits s) other = Mux.clean (lower v) q z fq
  own : ∀ q → Free t q ≡ false → Mux.framedZ (Free t) (Current t) K (uview s) q ≡ true
  own q fq with q ≟ w
  ... | yes refl = framed
  ... | no other rewrite lookup-put-other w q nf (W.exits s) other = Mux.owned (lower v) q fq
  ok : ∀ q g → lookup q (W.exits t) ≡ just g → ExitExpected (W.phase g) (lookup q (cleanupsW s))
  ok q g eq with q ≟ w
  ... | yes refl rewrite lookup-put w nf (W.exits s) with just-injective eq
  ...   | refl = Mux.clean (lower v) w framed free-w
  ok q g eq | no other rewrite lookup-put-other w q nf (W.exits s) other = exits-ok v q g eq

 -- An exit frame before the finalizer adopted for a framed worker without one.
 adopt-valid : ∀ w nf s → lookup w (W.exits s) ≡ nothing → present (lookup w (U.frames (uview s))) ≡ true →
   (∀ c → c ≡ nothing → ExitExpected (W.phase nf) c) → Valid s → Valid (record s { exits = put w nf (W.exits s) })
 adopt-valid w nf s absent framed pre v = exit-valid (Mux.mux-valid (Mux.relative (lower v)) (Mux.parked (lower v)) cln own (λ q f → refl) kpt) ok
  where
  t = record s { exits = put w nf (W.exits s) }
  free-w : Free s w ≡ true
  free-w rewrite absent = refl
  kpt : ∀ q → K q ≡ true → Mux.framedZ (Free t) (Current t) K (uview s) q ≡ true
  kpt = Mux.kept (lower v)
  cln : ∀ q → Mux.framedZ (Free t) (Current t) K (uview s) q ≡ true → Free t q ≡ true → lookup q (cleanupsW s) ≡ nothing
  cln q z fq with q ≟ w
  ... | yes refl rewrite lookup-put w nf (W.exits s) = case fq of λ ()
  ... | no other rewrite lookup-put-other w q nf (W.exits s) other = Mux.clean (lower v) q z fq
  own : ∀ q → Free t q ≡ false → Mux.framedZ (Free t) (Current t) K (uview s) q ≡ true
  own q fq with q ≟ w
  ... | yes refl = framed
  ... | no other rewrite lookup-put-other w q nf (W.exits s) other = Mux.owned (lower v) q fq
  ok : ∀ q g → lookup q (W.exits t) ≡ just g → ExitExpected (W.phase g) (lookup q (cleanupsW s))
  ok q g eq with q ≟ w
  ... | yes refl rewrite lookup-put w nf (W.exits s) with just-injective eq
  ...   | refl = pre _ (Mux.clean (lower v) w framed free-w)
  ok q g eq | no other rewrite lookup-put-other w q nf (W.exits s) other = exits-ok v q g eq

 pool-quiet : ∀ w f p s → present (lookup w (U.frames (uview s))) ≡ true → Valid s →
   Valid (record s { base = G.setPool w f p (W.base s) })
 pool-quiet w f p s pw v = exit-valid (Protocol.pool-valid (Free s) (Current s) K w f p (G.protocolState (W.base s)) pw (lower v)) (exits-ok v)
 -- One source cleanup write at an exit worker, with the exit table updated.
 machine-write : ∀ w f p s c fs → lookup w (W.exits s) ≡ just f →
   S.cleanups (Machine.world (O.core c)) ≡ put w p (cleanupsW s) →
   (∀ q → present (lookup q fs) ≡ present (lookup q (W.exits s))) →
   (∀ q g → lookup q fs ≡ just g → ExitExpected (W.phase g) (lookup q (put w p (cleanupsW s)))) →
   Valid s → Valid (record (W.setSource c s) { exits = fs })
 machine-write w f p s c fs found cl keys phases v = exit-valid (Mux.mux-valid rel park cln own (λ q f′ → refl) (Mux.kept (lower v))) ok
  where
  t = record (W.setSource c s) { exits = fs }
  u = uview s
  zw : Mux.framedZ (Free s) (Current s) K u w ≡ true
  zw = Mux.owned (lower v) w (excluded s found)
  freeT : ∀ q → Free t q ≡ Free s q
  freeT q = cong not (keys q)
  rel : Relative.On (Mux.framedZ (Free t) (Current t) K (uview t)) (B.view (U.base (uview t)))
  rel = Relative.excluded-write (Mux.framedZ (Free s) (Current s) K u) {s = B.view (U.base u)} {t = B.view (U.base (uview t))} w p zw refl cl (Mux.relative (lower v))
  park = Mux.parked (lower v)
  cln : ∀ q → Mux.framedZ (Free t) (Current t) K (uview t) q ≡ true → Free t q ≡ true → lookup q (S.cleanups (Machine.world (O.core c))) ≡ nothing
  cln q z fq with q ≟ w
  ... | yes refl = case trans (sym fq) (trans (freeT w) (excluded s found)) of λ ()
  ... | no other rewrite cl | lookup-put-other w q p (cleanupsW s) other = Mux.clean (lower v) q z (trans (sym (freeT q)) fq)
  own : ∀ q → Free t q ≡ false → Mux.framedZ (Free t) (Current t) K (uview t) q ≡ true
  own q fq = Mux.owned (lower v) q (trans (sym (freeT q)) fq)
  ok : ∀ q g → lookup q fs ≡ just g → ExitExpected (W.phase g) (lookup q (S.cleanups (Machine.world (O.core c))))
  ok q g eq rewrite cl = phases q g eq
 inbound-machine : ∀ a c {d} → O.advance (O.inbound a) c ≡ just d → Machine.advance a (O.core c) ≡ just (O.core d)
 inbound-machine a c eq with Machine.advance a (O.core c)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → refl }
 -- An exit-frame phase change together with its cleanup write.
 edit-machine : ∀ w f pc p s c → lookup w (W.exits s) ≡ just f →
   S.cleanups (Machine.world (O.core c)) ≡ put w p (cleanupsW s) → ExitExpected pc (just p) → Valid s →
   Valid (record (W.setSource c s) { exits = W.edit w f pc s })
 edit-machine w f pc p s c found cl ok v = machine-write w f p s c (W.edit w f pc s) found cl keys phases v
  where
  keys : ∀ q → present (lookup q (W.edit w f pc s)) ≡ present (lookup q (W.exits s))
  keys q with q ≟ w
  ... | yes refl rewrite lookup-put w (record f { phase = pc }) (W.exits s) | found = refl
  ... | no other rewrite lookup-put-other w q (record f { phase = pc }) (W.exits s) other = refl
  phases : ∀ q g → lookup q (W.edit w f pc s) ≡ just g → ExitExpected (W.phase g) (lookup q (put w p (cleanupsW s)))
  phases q g eq with q ≟ w
  ... | yes refl rewrite lookup-put w (record f { phase = pc }) (W.exits s) | lookup-put w p (cleanupsW s) with just-injective eq
  ...   | refl = ok
  phases q g eq | no other rewrite lookup-put-other w q (record f { phase = pc }) (W.exits s) other | lookup-put-other w q p (cleanupsW s) other = exits-ok v q g eq
 enter-safe : ∀ w f r s → lookup w (W.exits s) ≡ just f → Valid s → ∀ c →
   O.advance (O.inbound (Machine.handlerExit w)) (W.source s) ≡ just c →
   Valid (record (W.setSource c s) { exits = W.edit w f (W.finalizing r) s })
 enter-safe w f r s found v c adv = edit-machine w f (W.finalizing r) S.cleanupAcquire s c found
   (proj₂ (exit-effect w (O.core (W.source s)) (inbound-machine (Machine.handlerExit w) (W.source s) adv))) (S.cleanupAcquire , refl) v
 -- A finalizing exit frame keeps its phase; only the fault note may change.
 finalizing-at : ∀ w p (cl : Store WorkerId S.CleanupPC) g r → W.phase g ≡ W.finalizing r → ExitExpected (W.phase g) (lookup w (put w p cl))
 finalizing-at w p cl g r ph rewrite ph | lookup-put w p cl = p , refl
 note-machine : ∀ w f r action p s c → lookup w (W.exits s) ≡ just f → W.phase f ≡ W.finalizing r →
   S.cleanups (Machine.world (O.core c)) ≡ put w p (cleanupsW s) → Valid s →
   Valid (record (W.setSource c s) { exits = W.noteCleanup w action s })
 note-machine w f r action p s c found ph cl v with lookup w (W.exits s) in found′ | W.cleanupFault action
 ... | nothing | _ = case found of λ ()
 ... | just g | nothing with just-injective found
 ...   | refl = machine-write w f p s c (W.exits s) found′ cl (λ q → refl) phases v
  where
  phases : ∀ q h → lookup q (W.exits s) ≡ just h → ExitExpected (W.phase h) (lookup q (put w p (cleanupsW s)))
  phases q h eq with q ≟ w
  ... | yes refl with just-injective (trans (sym found′) eq)
  ...   | refl = finalizing-at w p (cleanupsW s) f r ph
  phases q h eq | no other rewrite lookup-put-other w q p (cleanupsW s) other = exits-ok v q h eq
 note-machine w f r action p s c found ph cl v | just g | just fault with just-injective found
 ... | refl = machine-write w f p s c (put w (record f { cleanupException = just fault }) (W.exits s)) found′ cl keys phases v
  where
  nf = record f { cleanupException = just fault }
  keys : ∀ q → present (lookup q (put w nf (W.exits s))) ≡ present (lookup q (W.exits s))
  keys q with q ≟ w
  ... | yes refl rewrite lookup-put w nf (W.exits s) | found′ = refl
  ... | no other rewrite lookup-put-other w q nf (W.exits s) other = refl
  phases : ∀ q h → lookup q (put w nf (W.exits s)) ≡ just h → ExitExpected (W.phase h) (lookup q (put w p (cleanupsW s)))
  phases q h eq with q ≟ w
  ... | yes refl rewrite lookup-put w nf (W.exits s) with just-injective eq
  ...   | refl = finalizing-at w p (cleanupsW s) nf r ph
  phases q h eq | no other rewrite lookup-put-other w q nf (W.exits s) other | lookup-put-other w q p (cleanupsW s) other = exits-ok v q h eq
 cleanup-safe : ∀ w f r action s → lookup w (W.exits s) ≡ just f → W.phase f ≡ W.finalizing r → Valid s → ∀ c →
   O.advance (O.inbound (Machine.cleanupStep w action)) (W.source s) ≡ just c →
   Valid (record (W.setSource c s) { exits = W.noteCleanup w action s })
 cleanup-safe w f r action s found ph v c adv with cleanup-effect w action (O.core (W.source s)) (inbound-machine (Machine.cleanupStep w action) (W.source s) adv)
 ... | stepped prior seen live (next , rw) = note-machine w f r action next s c found ph rw v
 release-safe : ∀ caller target s → Valid s → ∀ c →
   O.advance (O.release caller (OutboundRelease.cancellationDelivered target)) (W.source s) ≡ just c →
   Valid (record (W.setSource c s) { exits = W.exits s })
 release-safe caller target s v c adv = source-quiet c s (outbound-same (O.release caller (OutboundRelease.cancellationDelivered target)) (W.source s) adv tt) v
 -- The release caller's TIME_WAIT target holds a finalizing exit frame.
 target-exit : ∀ caller s {target} → W.timeWaitTarget caller s ≡ just target →
   Σ W.Frame (λ f → lookup target (W.exits s) ≡ just f × Σ W.BodyResult (λ r → W.phase f ≡ W.finalizing r))
 target-exit caller s eq with W.releaseTarget caller s
 ... | nothing = case eq of λ ()
 ... | just t with lookup t (W.exits s) in found | lookup t (S.cleanups (W.shared s))
 ...   | just f | just (S.cleanupWaiting h) with W.phase f in ph | W.currentCapture t f s
 target-exit caller s eq | just t | just f | just (S.cleanupWaiting h) | (W.bufferScope o) | cap = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupWaiting h) | (W.classifying e) | cap = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupWaiting h) | (W.errorTracing e pol) | cap = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupWaiting h) | (W.peerRethrow e) | cap = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupWaiting h) | (W.nodeDelivery e) | cap = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupWaiting h) | (W.nodeRethrow e) | cap = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupWaiting h) | (W.bodyExited r) | cap = case eq of λ ()
 ...     | (W.finalizing r) | true = case just-injective eq of λ { refl → f , found , r , ph }
 target-exit caller s eq | just t | just f | just (S.cleanupWaiting h) | (W.finalizing r) | false = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupWaiting h) | (W.cleanupComplete r oc) | cap = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupWaiting h) | (W.resultAvailable r oc) | cap = case eq of λ ()
 target-exit caller s eq | just t | just f | just S.cleanupAcquire = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupSelect l) = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupClose l m tl) = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupPublish l m tl) = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupRestore l y) = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupFinalize h oc) = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupCount oc) = case eq of λ ()
 target-exit caller s eq | just t | just f | just (S.cleanupDone oc) = case eq of λ ()
 target-exit caller s eq | just t | just f | nothing = case eq of λ ()
 target-exit caller s eq | just t | nothing | _ = case eq of λ ()
 target-safe : ∀ caller target err s → W.timeWaitTarget caller s ≡ just target → Valid s → ∀ c →
   O.advance (O.inbound (Machine.cleanupStep target (Cleanup.interruptTimeWait err))) (W.source s) ≡ just c →
   Valid (record (W.setSource c s) { exits = W.noteCleanup target (Cleanup.interruptTimeWait err) s })
 target-safe caller target err s eq v with target-exit caller s eq
 ... | f , found , r , ph = cleanup-safe target f r (Cleanup.interruptTimeWait err) s found ph v
 data PlanSafe : W.Plan → W.State → Set where
  safe-local : ∀ {fs s} → Valid (record s { exits = fs }) → PlanSafe (W.local fs) s
  safe-machine : ∀ {a fs s} → (∀ c → O.advance a (W.source s) ≡ just c → Valid (record (W.setSource c s) { exits = fs })) → PlanSafe (W.machine a fs) s
  safe-inherited : ∀ {a s} → PlanSafe (W.inherited a) s
  safe-coordinator : ∀ {a s} → PlanSafe (W.coordinator a) s
  safe-muxDelivery : ∀ {w err s} → PlanSafe (W.muxDelivery w err) s
  safe-timeWaitDelivery : ∀ {w err s} → (∀ c → O.advance (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s) ≡ just c →
    Valid (record (W.setSource c s) { exits = W.noteCleanup w (Cleanup.interruptTimeWait err) s })) → PlanSafe (W.timeWaitDelivery w err) s
  safe-releaseDelivery : ∀ {caller worker err s} → PlanSafe (W.releaseDelivery caller worker err) s
  safe-releaseTimeWaitDelivery : ∀ {caller worker err s} → (∀ c → O.advance (O.inbound (Machine.cleanupStep worker (Cleanup.interruptTimeWait err))) (W.source s) ≡ just c →
    Valid (record (W.setSource c s) { exits = W.noteCleanup worker (Cleanup.interruptTimeWait err) s })) → PlanSafe (W.releaseTimeWaitDelivery caller worker err) s
 enact-preserves : ∀ p s {t} → W.enact p s ≡ just t → Valid s → PlanSafe p s → Valid t
 enact-preserves (W.local fs) s eq v (safe-local next) = case just-injective eq of λ { refl → next }
 enact-preserves (W.machine a fs) s eq v (safe-machine next) with O.advance a (W.source s) in adv
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → next c refl }
 enact-preserves (W.inherited a) s eq v safe-inherited with G.step a (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = case just-injective eq of λ { refl → g-step a s actual v }
 enact-preserves (W.coordinator a) s eq v safe-coordinator = control-preserves a s eq v
 enact-preserves (W.muxDelivery w err) s eq v safe-muxDelivery with G.step (G.abortOwner w err) (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = control-preserves Close.acknowledgeDelivery (record s { base = g }) eq (g-step (G.abortOwner w err) s actual v)
 enact-preserves (W.timeWaitDelivery w err) s eq v (safe-timeWaitDelivery next) with O.advance
   (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s) in adv
 ... | nothing = case eq of λ ()
 ... | just c = control-preserves Close.acknowledgeDelivery
   (record (W.setSource c s) { exits = W.noteCleanup w (Cleanup.interruptTimeWait err) s }) eq (next c refl)
 enact-preserves (W.releaseDelivery caller worker err) s eq v safe-releaseDelivery with G.step (G.abortOwner worker err) (W.base s) in aborted
 ... | nothing = case eq of λ ()
 ... | just g with O.advance (O.release caller (OutboundRelease.cancellationDelivered worker)) (W.source (record s { base = g })) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just c = case just-injective eq of λ { refl → source-quiet c (record s { base = g })
   (outbound-same (O.release caller (OutboundRelease.cancellationDelivered worker)) (W.source (record s { base = g })) acknowledged tt)
   (g-step (G.abortOwner worker err) s aborted v) }
 enact-preserves (W.releaseTimeWaitDelivery caller worker err) s eq v (safe-releaseTimeWaitDelivery next) with O.advance
   (O.inbound (Machine.cleanupStep worker (Cleanup.interruptTimeWait err))) (W.source s) in adv
 ... | nothing = case eq of λ ()
 ... | just c with O.advance (O.release caller (OutboundRelease.cancellationDelivered worker)) c in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just c′ = case just-injective eq of λ { refl → source-quiet c′
   (record (W.setSource c s) { exits = W.noteCleanup worker (Cleanup.interruptTimeWait err) s })
   (outbound-same (O.release caller (OutboundRelease.cancellationDelivered worker)) c acknowledged tt) (next c refl) }
 choose-safe : ∀ a s {p} → W.choose a s ≡ just p → Valid s → PlanSafe p s
 choose-safe (W.run a) s eq valid with W.delegateAllowed a
 ... | true = case just-injective eq of λ { refl → safe-inherited }
 ... | false = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid with lookup w (W.exits s) in absent | lookup w (U.frames (P.base (G.protocolState (W.base s)))) in found |
   G.phase (G.frameAt w (W.base s)) | Pool.phase (W.poolAt w s)
 ... | nothing | just f | G.scopeDone outcome | Pool.closedPool with lookup w (S.handlers (W.shared s))
 ...   | just h with W.sameStart (U.captured f) h ∧ W.countersClear f s
 ...     | true = case just-injective eq of λ { refl → safe-local (begin-valid w outcome s absent (cong present found) (U.captured f) valid) }
 ...     | false = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.closedPool | nothing = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | just old | _ | _ | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | nothing | _ | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.idle | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.shutdownSelected | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.stoppingTraced | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.stoppingWritten | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.groupClosing | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.draining | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.drainReady | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.stoppedTrace | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.stoppedTracing | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.monitorReturnedNormal | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.ownerAborting err | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.wholeClosing outcome | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.wholeClosed outcome | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.asyncFailureWritten err | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.asyncDeadTracing err | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.openPool = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.closing = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.cancelPending j = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.joinPending j = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f in ph
 ...   | W.bufferScope outcome = case just-injective eq of λ { refl → safe-local (edit-valid w f _ s found (after-buffer outcome _ (exit-at valid found ph)) valid) }
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.observeBufferException w G.normalExit) s eq valid = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f in ph
 ...   | W.bufferScope outcome = case just-injective eq of λ { refl → safe-local (edit-valid w f _ s found (exit-at valid found ph) valid) }
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | nothing = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f in ph
 ...   | W.bufferScope outcome = case just-injective eq of λ { refl → safe-local (edit-valid w f _ s found (exit-at valid found ph) valid) }
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | nothing = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f in ph
 ...   | W.classifying err = case just-injective eq of λ { refl → safe-local (edit-valid w f _ s found (exit-at valid found ph) valid) }
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | nothing = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f in ph
 ...   | W.errorTracing err Life.shutdownPeer = case just-injective eq of λ { refl → safe-local (edit-valid w f _ s found (exit-at valid found ph) valid) }
 ...   | W.errorTracing err Life.shutdownNode = case just-injective eq of λ { refl → safe-local (edit-valid w f _ s found (exit-at valid found ph) valid) }
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f in ph
 ...   | W.nodeDelivery err = case just-injective eq of λ { refl → safe-local (edit-valid w f _ s found (exit-at valid found ph) valid) }
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f in ph
 ...   | W.peerRethrow err = case just-injective eq of λ { refl → safe-local (edit-valid w f _ s found (exit-at valid found ph) valid) }
 ...   | W.nodeRethrow err = case just-injective eq of λ { refl → safe-local (edit-valid w f _ s found (exit-at valid found ph) valid) }
 choose-safe (W.rethrow w) s eq valid | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f in ph | W.currentCapture w f s
 ...   | W.bodyExited result | true = case just-injective eq of λ { refl → safe-machine (enter-safe w f result s found valid) }
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.bufferScope otherOutcome | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.classifying otherError | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.errorTracing otherError otherPolicy | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.peerRethrow otherError | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.nodeDelivery otherError | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.nodeRethrow otherError | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.finalizing otherResult | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.resultAvailable otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.bodyExited otherResult | false = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f in ph | W.currentCapture w f s
 ...   | W.finalizing result | true = case just-injective eq of λ { refl → safe-machine (cleanup-safe w f result action s found ph valid) }
 choose-safe (W.cleanup w action) s eq valid | just f | W.bufferScope otherOutcome | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.classifying otherError | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.errorTracing otherError otherPolicy | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.peerRethrow otherError | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.nodeDelivery otherError | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.nodeRethrow otherError | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.bodyExited otherResult | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.cleanupComplete otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.resultAvailable otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.finalizing otherResult | false = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | nothing = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid with lookup w (W.exits s) in found | lookup w (S.cleanups (W.shared s)) in cl
 ... | just f | just (S.cleanupDone outcome) with W.phase f in ph
 ...   | W.finalizing result with W.effectiveResult result outcome (W.cleanupException f)
 ...     | just effective = case just-injective eq of λ { refl → safe-local (edit-valid w f _ s found cl valid) }
 ...     | nothing = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.classifying otherError = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | nothing | _ = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | nothing = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupAcquire) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupSelect savedLease) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupClose savedLease map tail) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupPublish savedLease map tail) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupRestore savedLease error) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupWaiting captured) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupCount outcome) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid with lookup w (W.exits s) in found | lookup w (S.cleanups (W.shared s)) in cl
 ... | just f | just (S.cleanupDone outcome) with W.phase f in ph
 ...   | W.cleanupComplete result observed with W.sameCleanup observed outcome
 ...     | true = case just-injective eq of λ { refl → safe-local (edit-valid w f _ s found cl valid) }
 ...     | false = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.classifying otherError = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | nothing | _ = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | nothing = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupAcquire) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupSelect savedLease) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupClose savedLease map tail) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupPublish savedLease map tail) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupRestore savedLease error) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupWaiting captured) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupCount outcome) = case eq of λ ()
 choose-safe (W.shutdownStep Close.acknowledgeDelivery) s eq valid = case eq of λ ()
 choose-safe (W.shutdownStep Close.captureSnapshot) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.shutdownStep Close.readEntry) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.shutdownStep Close.requestCancellation) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.shutdownStep Close.finishTraversal) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.shutdownStep Close.finishClose) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.deliverShutdownMux err) s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w = case just-injective eq of λ { refl → safe-muxDelivery }
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.initial = case eq of λ ()
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.reading = case eq of λ ()
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.sendReady e w = case eq of λ ()
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.awaitResults = case eq of λ ()
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.closed = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w with lookup w (W.exits s) in found | lookup w (S.cleanups (W.shared s))
 ...   | just f | just (S.cleanupWaiting h) with W.phase f in ph | W.currentCapture w f s
 ...     | W.finalizing result | true = case just-injective eq of λ { refl → safe-timeWaitDelivery (cleanup-safe w f result (Cleanup.interruptTimeWait err) s found ph valid) }
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.bufferScope otherOutcome | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.classifying otherError | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.errorTracing otherError otherPolicy | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.peerRethrow otherError | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.nodeDelivery otherError | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.nodeRethrow otherError | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.bodyExited otherResult | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.cleanupComplete otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.resultAvailable otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.finalizing result | false = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | nothing | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | nothing = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupAcquire) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupSelect savedLease) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupClose savedLease map tail) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupPublish savedLease map tail) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupRestore savedLease error) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupCount outcome) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupDone outcome) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.initial = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.reading = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.sendReady e w = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitResults = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.closed = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w with W.resultReady w s
 ...   | true = case just-injective eq of λ { refl → safe-coordinator }
 ...   | false = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.initial = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.reading = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.sendReady e w = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.awaitResults = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.closed = case eq of λ ()

 choose-safe (W.deliverReleaseMux caller err) s eq valid with W.releaseTarget caller s
 ... | nothing = case eq of λ ()
 ... | just worker = case just-injective eq of λ { refl → safe-releaseDelivery }
 choose-safe (W.deliverReleaseTimeWait caller err) s eq valid with W.timeWaitTarget caller s in target
 ... | nothing = case eq of λ ()
 ... | just worker = case just-injective eq of λ { refl → safe-releaseTimeWaitDelivery (target-safe caller worker err s target valid) }
 choose-safe (W.acknowledgeReleaseFinished caller) s eq valid with W.releaseTarget caller s
 ... | nothing = case eq of λ ()
 ... | just worker with W.resultReady worker s
 ...   | false = case eq of λ ()
 ...   | true = case just-injective eq of λ { refl → safe-machine (release-safe caller worker s valid) }

 step-preserves : ∀ a s {t} → W.step a s ≡ just t → Valid s → Valid t
 step-preserves a s eq v with W.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq v (choose-safe a s chosen v)
 exec-preserves : ∀ {s as t} → W.Executes s as t → Valid s → Valid t
 exec-preserves W.done v = v
 exec-preserves {s} (W.next {a = a} eq rest) v = exec-preserves rest (step-preserves a s eq v)
 initialized-valid : ∀ c {s} → (∀ q → K q ≡ false) → W.initial c ≡ just s → Valid s
 initialized-valid c noK eq with G.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just g = case just-injective eq of λ { refl →
   exit-valid (Group.initial-valid isBearerClosed _ _ K c (λ q → refl) noK actual) (λ q f ()) }
 -- Every initialized handler-exit run keeps exit phases, mux frames and physical
 -- threads in agreement with the shared cleanup records.
 from-initial : ∀ c {start as s} → (∀ q → K q ≡ false) → W.initial c ≡ just start → W.Executes start as s → Valid s
 from-initial c noK actual path = exec-preserves path (initialized-valid c noK actual)

-- Exit modules with different kept sets agree whenever the new kept workers are framed.
rekeep : ∀ {ib K K′ x} → (∀ q → K′ q ≡ true → present (lookup q (MuxModel.frames (Exit.uview ib K x))) ≡ true) →
  Exit.Valid ib K x → Exit.Valid ib K′ x
rekeep {K = K} keep v = Exit.exit-valid (Mux.mux-valid (Mux.relative l) (Mux.parked l) (Mux.clean l) (Mux.owned l) (Mux.frozen l) keep) (Exit.exits-ok {K = K} v)
 where l = Exit.lower {K = K} v

import ConnectionManagement.MuxExitCancellation as CancellationModel
-- Cancellation edits only phases before the finalizer.
module Cancellation (isBearerClosed : ErrorId → Bool) (K : WorkerId → Bool) where
 private module X = CancellationModel isBearerClosed using (Window; State; bufferBlock; errorTraceBlock; nodeSendBlock; deliver; deliverShutdown; observeCancellation; observeErrorTraceException; run; shutdownDelivery; step; target; traceThrew)
 private module W = ExitModel isBearerClosed using (bodyExited; bufferScope; classifying; cleanupComplete; edit; errorTracing; exits; finalizing; nodeDelivery; nodeRethrow; peerRethrow; phase; resultAvailable; shutdown; syncException; Phase; Frame)
 private module Lower = Exit isBearerClosed K
 Valid : X.State → Set
 Valid = Lower.Valid
 target-ok : ∀ window err p {pc} c → X.target window err p ≡ just pc → Lower.ExitExpected p c → Lower.ExitExpected pc c
 target-ok X.bufferBlock err (W.bufferScope o) c eq none = case just-injective eq of λ { refl → none }
 target-ok X.bufferBlock err (W.classifying e) c ()
 target-ok X.bufferBlock err (W.errorTracing e pol) c ()
 target-ok X.bufferBlock err (W.peerRethrow e) c ()
 target-ok X.bufferBlock err (W.nodeDelivery e) c ()
 target-ok X.bufferBlock err (W.nodeRethrow e) c ()
 target-ok X.bufferBlock err (W.bodyExited r) c ()
 target-ok X.bufferBlock err (W.finalizing r) c ()
 target-ok X.bufferBlock err (W.cleanupComplete r oc) c ()
 target-ok X.bufferBlock err (W.resultAvailable r oc) c ()
 target-ok X.errorTraceBlock err (W.bufferScope o) c ()
 target-ok X.errorTraceBlock err (W.classifying e) c ()
 target-ok X.errorTraceBlock err (W.errorTracing e pol) c eq none = case just-injective eq of λ { refl → none }
 target-ok X.errorTraceBlock err (W.peerRethrow e) c ()
 target-ok X.errorTraceBlock err (W.nodeDelivery e) c ()
 target-ok X.errorTraceBlock err (W.nodeRethrow e) c ()
 target-ok X.errorTraceBlock err (W.bodyExited r) c ()
 target-ok X.errorTraceBlock err (W.finalizing r) c ()
 target-ok X.errorTraceBlock err (W.cleanupComplete r oc) c ()
 target-ok X.errorTraceBlock err (W.resultAvailable r oc) c ()
 target-ok X.nodeSendBlock err (W.bufferScope o) c ()
 target-ok X.nodeSendBlock err (W.classifying e) c ()
 target-ok X.nodeSendBlock err (W.errorTracing e pol) c ()
 target-ok X.nodeSendBlock err (W.peerRethrow e) c ()
 target-ok X.nodeSendBlock err (W.nodeDelivery e) c eq none = case just-injective eq of λ { refl → none }
 target-ok X.nodeSendBlock err (W.nodeRethrow e) c ()
 target-ok X.nodeSendBlock err (W.bodyExited r) c ()
 target-ok X.nodeSendBlock err (W.finalizing r) c ()
 target-ok X.nodeSendBlock err (W.cleanupComplete r oc) c ()
 target-ok X.nodeSendBlock err (W.resultAvailable r oc) c ()
 deliver-preserves : ∀ window w err s {t} → X.deliver window w err s ≡ just t → Valid s → Valid t
 deliver-preserves window w err s eq valid with lookup w (W.exits s) in found
 ... | nothing = case eq of λ ()
 ... | just f with X.target window err (W.phase f) in targeted
 ...   | nothing = case eq of λ ()
 ...   | just pc = case just-injective eq of λ { refl → Lower.edit-valid w f pc s found
   (target-ok window err (W.phase f) _ targeted (Lower.exit-at valid found refl)) valid }
 trace-preserves : ∀ w err s {t} → X.traceThrew w err s ≡ just t → Valid s → Valid t
 trace-preserves w err s eq valid with lookup w (W.exits s) in found
 ... | nothing = case eq of λ ()
 ... | just f with W.phase f in ph
 trace-preserves w err s eq valid | just f | (W.bufferScope o) = case eq of λ ()
 trace-preserves w err s eq valid | just f | (W.classifying e) = case eq of λ ()
 ...   | (W.errorTracing e pol) = case just-injective eq of λ { refl → Lower.edit-valid w f (W.bodyExited (W.syncException err)) s found (Lower.exit-at valid found ph) valid }
 trace-preserves w err s eq valid | just f | (W.peerRethrow e) = case eq of λ ()
 trace-preserves w err s eq valid | just f | (W.nodeDelivery e) = case eq of λ ()
 trace-preserves w err s eq valid | just f | (W.nodeRethrow e) = case eq of λ ()
 trace-preserves w err s eq valid | just f | (W.bodyExited r) = case eq of λ ()
 trace-preserves w err s eq valid | just f | (W.finalizing r) = case eq of λ ()
 trace-preserves w err s eq valid | just f | (W.cleanupComplete r oc) = case eq of λ ()
 trace-preserves w err s eq valid | just f | (W.resultAvailable r oc) = case eq of λ ()
 shutdown-preserves : ∀ window err s {t} → X.shutdownDelivery window err s ≡ just t → Valid s → Valid t
 shutdown-preserves window err s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w with X.deliver window w err s in delivered
 ...   | nothing = case eq of λ ()
 ...   | just next = Lower.control-preserves Close.acknowledgeDelivery next eq (deliver-preserves window w err s delivered valid)
 shutdown-preserves window err s eq valid | Close.initial = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.reading = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.sendReady e w = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.awaitResults = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.closed = case eq of λ ()
 step-preserves : ∀ a s {t} → X.step a s ≡ just t → Valid s → Valid t
 step-preserves (X.run a) = Lower.step-preserves a
 step-preserves (X.observeCancellation window w err) = deliver-preserves window w err
 step-preserves (X.deliverShutdown window err) = shutdown-preserves window err
 step-preserves (X.observeErrorTraceException w err) = trace-preserves w err

import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.Properties.MuxStartupUnwind as UnwindProperties
-- Startup faults are owned by framed workers (the kept set of the exit layer).
-- A handoff installs an exit frame before the finalizer for a framed worker
-- without one, which therefore has no cleanup record.
module Unwind (isBearerClosed : ErrorId → Bool) where
 private module R = UnwindModel isBearerClosed using (Executes; done; next; Action; Fault; Plan; State; acknowledge; allowed; async; asyncDead; asyncStatus; awaitingClose; base; beginClose; beginDead; cancellationPlan; choose; closing; commitDead; continueSync; deadThrowPoint; deliverCancel; deliverShutdown; deliveryControl; deliveryRoute; enact; faults; finishClose; finishDead; handedOff; handoff; inherited; initial; join; local; machine; mux; observeCancellation; observeDeadTraceException; observeFailure; outcome; owner; phase; pool; poolAt; poolClosed; protocols; readyBody; readyBuffer; requestCancel; run; sameClose; sampleDead; setPhase; setPool; setSource; siteControl; siteRoute; source; start; step; sync; transfer; withPool; writeAsyncFailure)
 private module W = ExitModel isBearerClosed using (base; control; exits; setShutdown; shutdown; phase; setSource; source; Frame)
 private module X = CancellationModel isBearerClosed using (initial; step)
 private module G = GroupModel isBearerClosed using (module M; protocolState; wholeDeliverable; setPool)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base; muxAt)
 private module U = P.U using (frames)
 private module Pool = P.Pool using (beginClose; cancelPending; closedPool; closing; finishClose; join; joinPending; openPool; phase; requestCancel; step)
 private module M = G.M using (failed; finishMatches)
 private module F = UnwindProperties isBearerClosed using (Selection; selection-observation)

 Faulted : R.State → WorkerId → Bool
 Faulted s q = present (lookup q (R.faults s))
 framedR : R.State → WorkerId → Bool
 framedR s q = present (lookup q (U.frames (P.base (G.protocolState (W.base (R.base s))))))
 Valid : R.State → Set
 Valid s = Exit.Valid isBearerClosed (Faulted s) (R.base s)
 FaultsFramed : Store WorkerId R.Fault → R.State → Set
 FaultsFramed fs s = ∀ q → present (lookup q fs) ≡ true → framedR s q ≡ true
 fault-framed : ∀ s {q f} → Valid s → lookup q (R.faults s) ≡ just f → framedR s q ≡ true
 fault-framed s {q} v found = Mux.kept (Exit.lower v) q (cong present found)
 ff-same : ∀ s → Valid s → FaultsFramed (R.faults s) s
 ff-same s v q pq = Mux.kept (Exit.lower v) q pq
 ff-put : ∀ w x s → framedR s w ≡ true → Valid s → FaultsFramed (put w x (R.faults s)) s
 ff-put w x s pw v q pq with q ≟ w
 ... | yes refl = pw
 ... | no other = Mux.kept (Exit.lower v) q (trans (sym (cong present (lookup-put-other w q x (R.faults s) other))) pq)
 ff-phase : ∀ w f pc s → lookup w (R.faults s) ≡ just f → Valid s → FaultsFramed (R.setPhase w f pc s) s
 ff-phase w f pc s found v = ff-put w _ s (fault-framed s v found) v
 -- A quiet source change keeps faults, frames and exit frames.
 source-quiet : ∀ c s → S.cleanups (Machine.world (O.core c)) ≡ S.cleanups (Machine.world (O.core (R.source s))) → Valid s → Valid (R.setSource c s)
 source-quiet c s cl v = Exit.source-quiet isBearerClosed (Faulted s) c (R.base s) cl v
 shutdown-quiet : ∀ co s → Valid s → Valid (record s { base = W.setShutdown co (R.base s) })
 shutdown-quiet co s v = Exit.shutdown-quiet isBearerClosed (Faulted s) co (R.base s) v
 pool-valid : ∀ w u p s → framedR s w ≡ true → Valid s → Valid (R.setPool w u p s)
 pool-valid w u p s pw v = Exit.pool-quiet isBearerClosed (Faulted s) w u p (R.base s) pw v
 data PlanSafe : R.Plan → R.State → Set where
  safe-local : ∀ {fs s} → FaultsFramed fs s → PlanSafe (R.local fs) s
  safe-machine : ∀ {a fs s} → QuietOutbound a → FaultsFramed fs s → PlanSafe (R.machine a fs) s
  safe-pool : ∀ {w u a fs s} → framedR s w ≡ true → FaultsFramed fs s → PlanSafe (R.pool w u a fs) s
  safe-transfer : ∀ {w f fs s} → framedR s w ≡ true → lookup w (W.exits (R.base s)) ≡ nothing →
    (∀ c → c ≡ nothing → Exit.ExitExpected isBearerClosed (Faulted s) (W.phase f) c) → FaultsFramed fs s → PlanSafe (R.transfer w f fs) s
  safe-inherited : ∀ {a s} → PlanSafe (R.inherited a) s
  safe-acknowledge : ∀ {p s} → PlanSafe p s → PlanSafe (R.acknowledge p) s
 enact-preserves : ∀ p s {t} → R.enact p s ≡ just t → Valid s → PlanSafe p s → Valid t
 enact-preserves (R.local fs) s eq valid (safe-local ff) = case just-injective eq of λ { refl → rekeep ff valid }
 enact-preserves (R.machine a fs) s eq valid (safe-machine quiet ff) with O.advance a (R.source s) in adv
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → rekeep ff
   (Exit.source-quiet isBearerClosed (Faulted s) c (R.base s) (outbound-same a (R.source s) adv quiet) valid) }
 enact-preserves (R.pool w u a fs) s eq valid (safe-pool pw ff) with Pool.step a (R.poolAt w s)
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → rekeep
   (λ q pq → trans (Mux.keys-put (λ _ → true) (λ _ → nothing) (λ _ → false) w _ (P.base (G.protocolState (W.base (R.base s)))) pw q) (ff q pq))
   (Exit.pool-quiet isBearerClosed (Faulted s) w u p (R.base s) pw valid) }
 enact-preserves (R.transfer w f fs) s eq valid (safe-transfer pw absent pre ff) = case just-injective eq of λ { refl →
   rekeep ff (Exit.adopt-valid isBearerClosed (Faulted s) w f (R.base s) absent pw pre valid) }
 enact-preserves (R.inherited a) s eq valid safe-inherited with X.step a (R.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just x = case just-injective eq of λ { refl → Cancellation.step-preserves isBearerClosed (Faulted s) a (R.base s) actual valid }
 enact-preserves (R.acknowledge p) s eq valid (safe-acknowledge safe) with R.enact p s in actual
 ... | nothing = case eq of λ ()
 ... | just next with W.control Close.acknowledgeDelivery (R.base next) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just w = case just-injective eq of λ { refl → Exit.control-preserves isBearerClosed (Faulted next) Close.acknowledgeDelivery (R.base next) acknowledged
   (enact-preserves p s actual valid safe) }
 start-safe : ∀ w result route s {p} → R.start w result route s ≡ just p → Valid s → PlanSafe p s
 start-safe w result route s chosen valid with F.selection-observation w result route s chosen
 ... | selected rewrite F.Selection.plan-shape selected = safe-local
   (ff-put w _ s (cong present (F.Selection.owner-found selected)) valid)
 IsDirect : R.Action → Set
 IsDirect (R.run a) = ⊥
 IsDirect (R.deliverShutdown site err) = ⊥
 IsDirect _ = ⊤
 NonAck : R.Plan → Set
 NonAck (R.acknowledge p) = ⊥
 NonAck _ = ⊤
 ChosenSafe : R.Action → R.Plan → R.State → Set
 ChosenSafe a p s = PlanSafe p s × (IsDirect a → NonAck p)
 start-nonack : ∀ w result route s {p} → R.start w result route s ≡ just p → NonAck p
 start-nonack w result route s chosen with F.selection-observation w result route s chosen
 ... | selected rewrite F.Selection.plan-shape selected = tt
 cancellation-safe : ∀ w site err s {p} → R.cancellationPlan w site err s ≡ just p → Valid s → PlanSafe p s × NonAck p
 cancellation-safe w site err s eq valid with R.deliveryControl w site s
 ... | false = case eq of λ ()
 ... | true = start-safe w (R.async err) (λ f m → R.deliveryRoute site f m) s eq valid ,
   start-nonack w (R.async err) (λ f m → R.deliveryRoute site f m) s eq
 pool-safe : ∀ w before action after s {p} → R.withPool w before action after s ≡ just p → Valid s → PlanSafe p s × NonAck p
 pool-safe w before action after s eq valid with lookup w (R.faults s) in found | R.owner w s in owner
 ... | just f | just u with R.sameClose before (R.phase f)
 ...   | true = case just-injective eq of λ { refl → safe-pool (cong present owner) (ff-phase w f after s found valid) , tt }
 ...   | false = case eq of λ ()
 pool-safe w before action after s eq valid | nothing | nothing = case eq of λ ()
 pool-safe w before action after s eq valid | nothing | just u = case eq of λ ()
 pool-safe w before action after s eq valid | just f | nothing = case eq of λ ()
 chosen-safe : ∀ a s {p} → R.choose a s ≡ just p → Valid s → ChosenSafe a p s
 chosen-safe (R.run a) s eq valid with R.allowed a s
 ... | true = case just-injective eq of λ { refl → safe-inherited , λ () }
 ... | false = case eq of λ ()
 chosen-safe (R.observeFailure w site err) s eq valid with R.siteControl w site s
 ... | true = start-safe w (R.sync err) (λ f m → R.siteRoute w site f m s) s eq valid ,
   (λ _ → start-nonack w (R.sync err) (λ f m → R.siteRoute w site f m s) s eq)
 ... | false = case eq of λ ()
 chosen-safe (R.observeCancellation w site err) s eq valid with cancellation-safe w site err s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.deliverShutdown site err) s eq valid with Close.phase (W.shutdown (R.base s))
 ... | Close.awaitDelivery e w with R.cancellationPlan w site err s in cancelled
 ...   | just p = case just-injective eq of λ { refl → safe-acknowledge (proj₁ (cancellation-safe w site err s cancelled valid)) , λ () }
 ...   | nothing = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.initial = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.reading = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.sendReady e w = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.awaitResults = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.closed = case eq of λ ()
 chosen-safe (R.beginClose w order) s eq valid with pool-safe w R.awaitingClose (Pool.beginClose order) R.closing s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.requestCancel w) s eq valid with pool-safe w R.closing Pool.requestCancel R.closing s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.join w) s eq valid with pool-safe w R.closing Pool.join R.closing s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.finishClose w) s eq valid with pool-safe w R.closing Pool.finishClose R.poolClosed s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.deliverCancel w) s eq valid with lookup w (R.faults s) | R.owner w s in owner | Pool.phase (R.poolAt w s)
 ... | just f | just u | Pool.cancelPending j with R.phase f | G.wholeDeliverable w j u (W.base (R.base s))
 ...   | R.closing | true = case just-injective eq of λ { refl → safe-pool (cong present owner) (ff-same s valid) , λ _ → tt }
 ...   | R.readyBody | _ = case eq of λ ()
 ...   | R.readyBuffer | _ = case eq of λ ()
 ...   | R.awaitingClose | _ = case eq of λ ()
 ...   | R.poolClosed | _ = case eq of λ ()
 ...   | R.asyncStatus | _ = case eq of λ ()
 ...   | R.asyncDead | _ = case eq of λ ()
 ...   | R.handedOff | _ = case eq of λ ()
 ...   | R.closing | false = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | nothing | _ | _ = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | nothing | _ = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.openPool = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.closing = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.joinPending j = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.closedPool = case eq of λ ()

 chosen-safe (R.continueSync w) s eq valid with lookup w (R.faults s) in found | Pool.phase (R.poolAt w s)
 ... | just f | Pool.closedPool with R.phase f | R.outcome f
 ...   | R.poolClosed | R.sync err = case just-injective eq of λ { refl → safe-local (ff-phase w f R.readyBuffer s found valid) , λ _ → tt }
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.poolClosed | R.async err = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.readyBody | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.readyBuffer | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.closing | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.asyncDead | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.openPool = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closing = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.cancelPending j = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.joinPending j = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | nothing | _ = case eq of λ ()

 chosen-safe (R.writeAsyncFailure w) s eq valid with lookup w (R.faults s) in found | Pool.phase (R.poolAt w s)
 ... | just f | Pool.closedPool with R.phase f | R.outcome f
 ...   | R.poolClosed | R.async err = case just-injective eq of λ { refl → safe-machine tt (ff-phase w f R.asyncStatus s found valid) , λ _ → tt }
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.poolClosed | R.sync err = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.readyBody | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.readyBuffer | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.closing | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.asyncDead | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.openPool = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closing = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.cancelPending j = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.joinPending j = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | nothing | _ = case eq of λ ()

 chosen-safe (R.beginDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f
 ...   | R.asyncStatus = case just-injective eq of λ { refl → safe-machine tt (ff-phase w f R.asyncDead s found valid) , λ _ → tt }
 chosen-safe (R.beginDead w) s eq valid | just f | R.readyBody = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.readyBuffer = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.awaitingClose = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.closing = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.poolClosed = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.asyncDead = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.handedOff = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.sampleDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f
 ...   | R.asyncDead = case just-injective eq of λ { refl → safe-machine tt (ff-same s valid) , λ _ → tt }
 chosen-safe (R.sampleDead w) s eq valid | just f | R.readyBody = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.readyBuffer = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.awaitingClose = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.closing = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.poolClosed = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.asyncStatus = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.handedOff = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.commitDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f
 ...   | R.asyncDead = case just-injective eq of λ { refl → safe-machine tt (ff-same s valid) , λ _ → tt }
 chosen-safe (R.commitDead w) s eq valid | just f | R.readyBody = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.readyBuffer = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.awaitingClose = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.closing = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.poolClosed = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.asyncStatus = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.handedOff = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.finishDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f | R.outcome f | P.muxAt (R.mux f) (R.protocols s)
 ...   | R.asyncDead | R.async err | just m with WireMux.callback m | M.finishMatches (M.failed err) (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → safe-local (ff-phase w f R.readyBuffer s found valid) , λ _ → tt }
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.returned | false = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.readActive tr | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.commitTrace active tr | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.afterStart n | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.forkPending n | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.afterFailure | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.tracerFailed n | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | nothing = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.sync err | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.readyBody | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.readyBuffer | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.awaitingClose | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.closing | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.poolClosed | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncStatus | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.handedOff | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.observeDeadTraceException w err) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f | P.muxAt (R.mux f) (R.protocols s)
 ...   | R.asyncDead | just m with R.deadThrowPoint m
 ...     | true = case just-injective eq of λ { refl → safe-local (ff-put w _ s (fault-framed s valid found) valid) , λ _ → tt }
 ...     | false = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.asyncDead | nothing = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.readyBody | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.readyBuffer | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.closing | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.poolClosed | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.handoff w) s eq valid with lookup w (R.faults s) in found | lookup w (W.exits (R.base s)) in absent
 ... | just f | nothing with R.phase f | R.outcome f
 ...   | R.readyBuffer | result = case just-injective eq of λ { refl → safe-transfer (fault-framed s valid found) absent (λ c none → none) (ff-phase w f R.handedOff s found valid) , λ _ → tt }
 ...   | R.readyBody | R.sync err = case just-injective eq of λ { refl → safe-transfer (fault-framed s valid found) absent (λ c none → none) (ff-phase w f R.handedOff s found valid) , λ _ → tt }
 ...   | R.readyBody | R.async err = case just-injective eq of λ { refl → safe-transfer (fault-framed s valid found) absent (λ c none → none) (ff-phase w f R.handedOff s found valid) , λ _ → tt }
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.closing | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.poolClosed | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.asyncDead | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | just exit = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | nothing | _ = case eq of λ ()

 choose-safe : ∀ a s {p} → R.choose a s ≡ just p → Valid s → PlanSafe p s
 choose-safe a s chosen valid = proj₁ (chosen-safe a s chosen valid)
 step-preserves : ∀ a s {t} → R.step a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid with R.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq valid (choose-safe a s chosen valid)
 exec-preserves : ∀ {s as t} → R.Executes s as t → Valid s → Valid t
 exec-preserves R.done v = v
 exec-preserves {s} (R.next {a = a} eq rest) v = exec-preserves rest (step-preserves a s eq v)
 initialized-valid : ∀ c {s} → R.initial c ≡ just s → Valid s
 initialized-valid c eq with X.initial c in initialized
 ... | nothing = case eq of λ ()
 ... | just x = case just-injective eq of λ { refl → Exit.initialized-valid isBearerClosed _ c (λ q → refl) initialized }
 -- Every initialized startup-unwind run keeps exit phases, mux frames, startup
 -- faults and physical threads in agreement with the shared cleanup records.
 from-initial : ∀ c {start as s} → R.initial c ≡ just start → R.Executes start as s → Valid s
 from-initial c actual path = exec-preserves path (initialized-valid c actual)
