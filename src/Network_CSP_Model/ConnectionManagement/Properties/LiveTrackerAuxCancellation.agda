{-# OPTIONS --guardedness #-}

-- Joint job/pool-content preservation at actual child unwind and replacement.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxCancellation (b : ErrorId → Bool) where
open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; JobId)
open import ConnectionManagement.IGTypes using (clean; errored)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as WireMux
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Properties.MuxProtocolJobs as Old
import ConnectionManagement.Properties.LiveTrackerAuxContent as Aux
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Trans
import ConnectionManagement.Properties.LiveTrackerAuxUpdates as Updates
import ConnectionManagement.Properties.LiveTrackerAuxProtocol as Protocol
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.Properties.LiveTrackerAuxMonitor as MonitorFacts
import Data.Nat as Nat
import Data.Empty
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import ConnectionManagement.Properties.Stores using (UniqueKeys; apart-lookup; lookup-head)
module A = Aux b
module T = Trans b
module Up = Updates b
module U = P.U
module Pool = P.Pool
module Startup = P.Startup
open T using (Retains; job-kept; completion-kept; job-phase)

module W = Group b
-- A successful traversal lookup names the keyed row when frame keys are
-- unique, as they are in the initialized put-only frame store.
find-found : ∀ j rows {w f} → UniqueKeys rows → W.findOwner j rows ≡ just (w , f) → lookup w rows ≡ just f
find-found j [] unique ()
find-found j ((q , first) ∷ rows) {w} {f} (apart ∷ unique) eq with lookup j (Pool.handles (Startup.pool (U.startup first)))
... | just phase = case just-injective eq of λ { refl → lookup-head q first rows }
... | nothing = lift (find-found j rows unique eq)
 where
 lift : lookup w rows ≡ just f → lookup w ((q , first) ∷ rows) ≡ just f
 lift found with w ≟ q
 ... | yes refl = case trans (sym (apart-lookup q rows apart)) found of λ ()
 ... | no _ = found

module For (Obs : P.State → Set) (stable : ∀ {s t} → Retains s t → Obs s → Obs t) where
 open Protocol.For b Obs stable using (source-valid; same; pool-valid; step-preserves)
 Valid : W.State → Set
 Valid s = Up.Valid (W.protocolState s) × Obs (W.protocolState s)
 ownerOf-found : ∀ j s {w f} → W.ownerOf j s ≡ just (w , f) → Valid s → lookup w (U.frames (P.base (W.protocolState s))) ≡ just f
 ownerOf-found j s actual valid = find-found j _ (Up.Valid.unique (proj₁ valid)) actual
 -- Preparation performs source/pending bookkeeping and retains exact frames.
 record Prepared (s t : W.State) : Set where
  constructor prep
  field preserves : Valid s → Valid t
        frames-same : U.frames (P.base (W.protocolState t)) ≡ U.frames (P.base (W.protocolState s))
 ci-idle : ∀ s → Prepared s s
 ci-idle s = prep (λ valid → valid) refl
 ci-compose : ∀ {s t u} → Prepared s t → Prepared t u → Prepared s u
 ci-compose first second = prep (λ valid → Prepared.preserves second (Prepared.preserves first valid))
   (trans (Prepared.frames-same second) (Prepared.frames-same first))
 ci-via-source-projects : ∀ action s {t} → W.viaSource action s ≡ just t → Prepared s t
 ci-via-source-projects action s actual with O.advance (O.inbound (Machine.igStep action)) (W.source s)
 ... | nothing = case actual of λ ()
 ... | just c = case just-injective actual of λ { refl → prep (source-valid c (W.protocolState s)) refl }
 ci-protocol-projects : ∀ s p → (Valid s → Up.Valid p × Obs p) →
   U.frames (P.base p) ≡ U.frames (P.base (W.protocolState s)) → Prepared s (W.setProtocols p s)
 ci-protocol-projects s p preserves frames = prep preserves frames
 ci-discard-projects : ∀ j job s {s′} → W.discardClean j job s ≡ just s′ → Prepared s s′
 ci-discard-projects j job s eq with Types.direction job
 ... | WireMux.initiatorJob = case just-injective eq of λ { refl → ci-idle s }
 ... | WireMux.responderJob with P.locate j (P.pendingAt (Types.owner job) (W.protocolState s)) | P.muxAt (Types.mux job) (W.protocolState s)
 ...   | just (index , kept) | just m with IG.takePending index (WireMux.finishedJobs m)
 ...     | just ((n , result) , rest) with does (n Nat.≟ Types.protocolNumber job) ∧ P.sameOutcome ConnectionManagement.IGTypes.clean result
 ...       | true with W.viaSource (IG.discardJobOccurrence (Types.mux job) index) s in advanced
 ...         | nothing = case eq of λ ()
 ...         | just next = case just-injective eq of λ { refl → ci-compose
   (ci-via-source-projects (IG.discardJobOccurrence (Types.mux job) index) s advanced)
   (ci-protocol-projects next _ (same (W.protocolState next) _ refl refl (λ w → refl)) refl) }
 ci-discard-projects j job s eq | WireMux.responderJob | just (index , kept) | just m | just ((n , result) , rest) | false = case eq of λ ()
 ci-discard-projects j job s eq | WireMux.responderJob | just (index , kept) | just m | nothing = case eq of λ ()
 ci-discard-projects j job s eq | WireMux.responderJob | nothing | _ = case eq of λ ()
 ci-discard-projects j job s eq | WireMux.responderJob | just pair | nothing = case eq of λ ()
 ci-prepare-projects : ∀ j w f s {s′} → W.prepareUnwind j w f s ≡ just s′ → Prepared s s′
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
 ci-unwind-projects : ∀ j s {s′} → W.unwindChild j s ≡ just s′ → Valid s → Valid s′
 ci-unwind-projects j s eq valid with W.ownerOf j s in owned
 ... | nothing = case eq of λ ()
 ... | just (w , f) with lookup j (Pool.handles (W.poolAt w s))
 ...   | just Pool.bodyUnwinding with W.prepareUnwind j w f s in prepared
 ...     | nothing = case eq of λ ()
 ...     | just next with Pool.step (Pool.bodyUnwound j) (W.poolAt w next) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just p = case just-injective eq of λ { refl → pool-valid w f (Pool.bodyUnwound j) (W.protocolState next)
   (trans (cong (lookup w) (Prepared.frames-same preparation)) (ownerOf-found j s owned valid)) advanced tt
   (Prepared.preserves preparation valid) }
   where preparation = ci-prepare-projects j w f s prepared

 ci-unwind-projects j s eq valid | just (w , f) | nothing = case eq of λ ()
 ci-unwind-projects j s eq valid | just (w , f) | just Pool.bodyRunning = case eq of λ ()
 ci-unwind-projects j s eq valid | just (w , f) | just (Pool.bodyReturned result) = case eq of λ ()
 ci-unwind-projects j s eq valid | just (w , f) | just (Pool.deregisterPending exit) = case eq of λ ()
 ci-unwind-projects j s eq valid | just (w , f) | just (Pool.deregistered exit) = case eq of λ ()
 ci-unwind-projects j s eq valid | just (w , f) | just (Pool.resultAvailable exit) = case eq of λ ()
 ci-replacement-projects : ∀ j err s {s′} → W.replaceUnwind j err s ≡ just s′ → Valid s → Valid s′
 ci-replacement-projects j err s eq valid with lookup j (P.jobs (W.protocolState s))
 ... | nothing = case eq of λ ()
 ... | just job with W.replacementEligible (Types.phase job) | W.ownerOf j s in owned
 ...   | true | just (w , f) with does (w ≟ Types.owner job) | Pool.step (Pool.resumeAfterUnwindError j) (W.poolAt w s) in advanced
 ...     | true | just p with P.step (P.protocolException j err) (W.protocolState (W.setPool w f p s)) in captured
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → step-preserves (P.protocolException j err) (W.protocolState (W.setPool w f p s)) captured
   (pool-valid w f (Pool.resumeAfterUnwindError j) (W.protocolState s) (ownerOf-found j s owned valid) advanced tt valid) }

 ci-replacement-projects j err s eq valid | just job | true | just (w , f) | false | _ = case eq of λ ()
 ci-replacement-projects j err s eq valid | just job | true | just (w , f) | true | nothing = case eq of λ ()
 ci-replacement-projects j err s eq valid | just job | false | _ = case eq of λ ()
 ci-replacement-projects j err s eq valid | just job | true | nothing = case eq of λ ()

 -- All group/whole-close pool primitives introduce no new result payload;
 -- their actual ownerContext supplies the selected current frame.
 via-pool : ∀ w a s {t} → W.viaPool w a s ≡ just t →
   (∀ C → Up.Kernel.NewReturn a C) → Valid s → Valid t
 via-pool w a s eq new valid with W.ownerContext w s in context
 ... | nothing = case eq of λ ()
 ... | just (f , mid) with Pool.step a (W.poolAt w s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → pool-valid w f a (W.protocolState s)
     (MonitorFacts.owner-frame b w (W.base s) context) actual (new _) valid }

 -- Public writer lemmas expose the real operations without proof-path names.
 unwind-preserves : ∀ j s {t} → W.unwindChild j s ≡ just t → Valid s → Valid t
 unwind-preserves = ci-unwind-projects
 replacement-preserves : ∀ j err s {t} → W.replaceUnwind j err s ≡ just t → Valid s → Valid t
 replacement-preserves = ci-replacement-projects
