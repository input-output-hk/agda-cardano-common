{-# OPTIONS --guardedness #-}

-- Only two source operations write the shared cleanup store: Machine.handlerExit
-- creates a worker's cleanup record and Machine.cleanupStep advances it. Every
-- other machine and outbound-machine operation leaves the whole store unchanged.
-- A created record starts at cleanupAcquire, a step rewrites only the stepping
-- worker's record, and a completed record (cleanupDone) admits no further step.
-- The quiet cases adapt the admission-table proofs of InboundOriginCore.
module ConnectionManagement.Properties.CleanupWriters where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (any)
open import Data.Nat using (suc; _≤?_; _∸_)
open import Data.List using (length; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; EntryId; PromiseId; ident)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.CM as CM
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as Release
import ConnectionManagement.Rules.InboundRelease as InRelease
import ConnectionManagement.Rules.Pruning as Prune
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Rules.IGRegistration as IG

-- Every source operation other than the two cleanup writers.
QuietMachine : M.Action → Set
QuietMachine (M.cleanupStep _ _) = ⊥
QuietMachine (M.handlerExit _) = ⊥
QuietMachine _ = ⊤
QuietOutbound : O.Action → Set
QuietOutbound (O.inbound a) = QuietMachine a
QuietOutbound _ = ⊤

-- Admission and handshake continuations write admissions, map and handler
-- state, never the cleanup store.
private
 prefix-worker : ∀ act w a s {s′} → lookup w (S.admissions s) ≡ just a → Admission.stepWorker w a act s ≡ just s′ →
   S.cleanups s′ ≡ S.cleanups s
 prefix-worker Admission.take w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.take w a@(S.admissionWorker r S.acquireMap) s owned eq with CM.takeMap w (S.cm s) in takenEq
 ... | nothing = case eq of λ ()
 ... | just (l , c′) = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.countLimit w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.countLimit w a@(S.admissionWorker r (S.count l)) s owned eq with S.countIncoming (S.entries (S.cm s)) (S.savedMap l)
 ... | nothing = case eq of λ ()
 ... | just n with suc n ≤? S.hardLimit r
 ...   | yes _ = case just-injective eq of λ { refl → refl }
 ...   | no _ = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.allocatePromise w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.allocatePromise w a@(S.admissionWorker r (S.prepare l)) s owned eq = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.chooseEntry w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.chooseEntry w a@(S.admissionWorker r (S.selectEntry l p)) s owned eq with CM.selectInbound l r (S.cm s) in selectedEq
 ... | nothing = case eq of λ ()
 ... | just CM.denied = case just-injective eq of λ { refl → refl }
 ... | just (CM.selected e c′) = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.fork w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.fork w a@(S.admissionWorker r (S.forkHandler l p e)) s owned eq with lookup (S.child r) (S.handlers s) in absent | lookup (S.child r) (S.admissions s)
 ... | just _ | _ = case eq of λ ()
 ... | nothing | just _ = case eq of λ ()
 ... | nothing | nothing = case just-injective eq of λ { refl → refl }

 prefix-worker Admission.failFork w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.failFork w a@(S.admissionWorker r (S.forkHandler l p e)) s owned eq = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.readCounters w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.readCounters w a@(S.admissionWorker r (S.countPublished p e)) s owned eq with S.mapCell (S.cm s)
 ... | S.taken _ = case eq of λ ()
 ... | S.full m with S.countIncoming (S.entries (S.cm s)) m
 ...   | nothing = case eq of λ ()
 ...   | just _ = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.close w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.close w a@(S.admissionWorker r (S.closeSocket reason)) s owned eq = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.putMapBack w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.reject l S.forbidden)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.reject l S.bodyFailed)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.reject l S.forkFailed)) s owned ()
 prefix-worker Admission.putMapBack w a@(S.admissionWorker r (S.publish l p e)) s owned eq with CM.putMap l (S.insertConnection (S.key r) e (S.savedMap l)) (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.putMapBack w a@(S.admissionWorker r (S.reject l S.hardLimitReached)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.restore w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.reject l S.hardLimitReached)) s owned ()
 prefix-worker Admission.restore w a@(S.admissionWorker r (S.reject l S.forbidden)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.restore w a@(S.admissionWorker r (S.reject l S.bodyFailed)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.restore w a@(S.admissionWorker r (S.reject l S.forkFailed)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → refl }


 prefix-worker Admission.restoreBody w a@(S.admissionWorker r (S.count l)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.restoreBody w a@(S.admissionWorker r (S.prepare l)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.restoreBody w a@(S.admissionWorker r (S.selectEntry l p)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.restoreBody w a@(S.admissionWorker r (S.forkHandler l p e)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.restoreBody w a@(S.admissionWorker r (S.publish l p e)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → refl }
 prefix-worker Admission.restoreBody w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.reject l S.hardLimitReached)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.reject l S.forbidden)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.reject l S.bodyFailed)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.reject l S.forkFailed)) s owned ()
 success-result : ∀ (native : M.Action) w a e h f decision s →
   S.cleanups (H.applySuccess w a e h f decision s) ≡ S.cleanups s
 success-result native w a e h f (H.update st provenance) s = refl
 success-result native w a e h f (H.retain provenance) s = refl
 success-result native w a e h f (H.disconnect reason) s = refl
 success-result native w a e h f H.impossible s = refl

 terminate-result : ∀ (native : M.Action) w a e reason s {s′} → H.terminateResult w a e reason s ≡ just s′ →
   S.cleanups s′ ≡ S.cleanups s
 terminate-result native w a e reason s eq with lookup e (S.entries (S.cm s)) | S.mapCell (S.cm s)
 ... | nothing | _ = case eq of λ ()
 ... | just _ | S.taken _ = case eq of λ ()
 ... | just _ | S.full m with S.lookupConnection (S.key (S.request a)) m
 ...   | nothing = case just-injective eq of λ { refl → refl }
 ...   | just current with e ≟ current
 ...     | no _ = case just-injective eq of λ { refl → refl }
 ...     | yes _ = case just-injective eq of λ { refl → refl }

 handshake-worker : ∀ (native : M.Action) act mode w a s {s′} → H.stepWorker mode w a act s ≡ just s′ →
   S.cleanups s′ ≡ S.cleanups s
 handshake-worker native H.readResult mode w (S.admissionWorker r S.acquireMap) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.count l)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.prepare l)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.selectEntry l p)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.forkHandler l p e)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.publish l p e)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.reject l reason)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.closeSocket reason)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.finished reason)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.countPublished p e)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.commitHandshake e result)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.countHandshake result)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.notifyInbound info)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.returnHandshake result)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.completedHandshake result)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r S.impossibleHandshake) s ()
 handshake-worker native H.readResult mode w a@(S.admissionWorker r (S.awaitHandshake p e)) s eq with lookup p (S.handshakeResults s)
 ... | nothing = case eq of λ ()
 ... | just result = case just-injective eq of λ { refl → refl }
 handshake-worker native H.commitResult mode w (S.admissionWorker r S.acquireMap) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.count l)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.prepare l)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.selectEntry l p)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.forkHandler l p e)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.publish l p e)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.reject l reason)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.closeSocket reason)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.finished reason)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.countPublished p e)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.awaitHandshake p e)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.countHandshake result)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.notifyInbound info)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.returnHandshake result)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.completedHandshake result)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r S.impossibleHandshake) s ()
 handshake-worker native H.commitResult mode w a@(S.admissionWorker r (S.commitHandshake e (S.negotiated h f))) s eq with lookup e (S.entries (S.cm s))
 ... | nothing = case eq of λ ()
 ... | just st = case just-injective eq of λ { refl → success-result native w a e h f (H.decideSuccess r h f st) s }
 handshake-worker native H.commitResult mode w a@(S.admissionWorker r (S.commitHandshake e S.query)) s eq = terminate-result native w a e S.handshakeQuery s eq
 handshake-worker native H.commitResult mode w a@(S.admissionWorker r (S.commitHandshake e (S.handlerError cls err))) s eq = terminate-result native w a e (S.handshakeError cls err) s eq
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r S.acquireMap) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.count l)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.prepare l)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.selectEntry l p)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.forkHandler l p e)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.publish l p e)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.reject l reason)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.closeSocket reason)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.finished reason)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.countPublished p e)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.awaitHandshake p e)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.commitHandshake e result)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.notifyInbound info)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.returnHandshake result)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.completedHandshake result)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r S.impossibleHandshake) s ()
 handshake-worker native H.readResultCounters mode w a@(S.admissionWorker r (S.countHandshake result)) s eq with S.mapCell (S.cm s)
 ... | S.taken _ = case eq of λ ()
 ... | S.full m with S.countIncoming (S.entries (S.cm s)) m
 ...   | nothing = case eq of λ ()
 ...   | just _ with result | mode
 ...     | S.connected info | S.responderMode = case just-injective eq of λ { refl → refl }
 ...     | S.connected info | S.noResponderMode = case just-injective eq of λ { refl → refl }
 ...     | S.disconnected reason | _ = case just-injective eq of λ { refl → refl }
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r S.acquireMap) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.count l)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.prepare l)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.selectEntry l p)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.forkHandler l p e)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.publish l p e)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.reject l reason)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.closeSocket reason)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.finished reason)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.countPublished p e)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.awaitHandshake p e)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.commitHandshake e result)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.countHandshake result)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.returnHandshake result)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.completedHandshake result)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r S.impossibleHandshake) s ()
 handshake-worker native H.enqueueInbound mode w a@(S.admissionWorker r (S.notifyInbound info)) s eq with suc (length (S.inboundInfo s)) ≤? 100
 ... | no _ = case eq of λ ()
 ... | yes _ = case just-injective eq of λ { refl → refl }
 handshake-worker native H.returnResult mode w (S.admissionWorker r S.acquireMap) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.count l)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.prepare l)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.selectEntry l p)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.forkHandler l p e)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.publish l p e)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.reject l reason)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.closeSocket reason)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.finished reason)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.countPublished p e)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.awaitHandshake p e)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.commitHandshake e result)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.countHandshake result)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.notifyInbound info)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.completedHandshake result)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r S.impossibleHandshake) s ()
 handshake-worker native H.returnResult mode w a@(S.admissionWorker r (S.returnHandshake result)) s eq = case just-injective eq of λ { refl → refl }



admission-quiet : ∀ worker action c {d} → M.advance (M.admissionStep worker action) c ≡ just d →
 S.cleanups (M.world d) ≡ S.cleanups (M.world c)
admission-quiet worker action c eq with lookup worker (S.admissions (M.world c)) in owned
... | nothing = case eq of λ ()
... | just row with Admission.stepWorker worker row action (M.world c) in actual
...   | nothing = case eq of λ ()
...   | just next with just-injective eq
...     | refl = prefix-worker action worker row (M.world c) owned actual
handshake-quiet : ∀ worker action c {d} → M.advance (M.handshakeStep worker action) c ≡ just d →
 S.cleanups (M.world d) ≡ S.cleanups (M.world c)
handshake-quiet worker action c eq with lookup worker (S.admissions (M.world c))
... | nothing = case eq of λ ()
... | just row with H.stepWorker (M.responder c) worker row action (M.world c) in actual
...   | nothing = case eq of λ ()
...   | just next with just-injective eq
...     | refl = handshake-worker (M.handshakeStep worker action) action (M.responder c) worker row (M.world c) actual

-- Publication writes only result storage; entry edits write only entries.
publication-cleanups : ∀ w result s {t} → H.publishBoundary w result s ≡ just (H.published t) →
  S.cleanups t ≡ S.cleanups s
publication-cleanups w result s eq with lookup w (S.handlers s) | lookup w (S.cleanups s)
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
... | just h | nothing with any (λ p → does (p ≟ S.handlerPromise h)) (S.promises s)
...   | false = case eq of λ ()
...   | true with lookup (S.handlerPromise h) (S.handshakeResults s)
...     | just _ = case eq of λ ()
...     | nothing = case just-injective eq of λ { refl → refl }
edit-cleanups : ∀ edit s {t} → InRelease.applyEdit edit s ≡ just t → S.cleanups t ≡ S.cleanups s
edit-cleanups nothing s eq = case just-injective eq of λ { refl → refl }
edit-cleanups (just (e , st)) s eq with lookup e (S.entries (S.cm s))
... | nothing = case eq of λ ()
... | just old = case just-injective eq of λ { refl → refl }
edits-cleanups : ∀ edits s {t} → Prune.applyEdits edits s ≡ just t → S.cleanups t ≡ S.cleanups s
edits-cleanups [] s eq = case just-injective eq of λ { refl → refl }
edits-cleanups (edit ∷ edits) s eq with InRelease.applyEdit (just edit) s in edited
... | nothing = case eq of λ ()
... | just mid = trans (edits-cleanups edits mid eq) (edit-cleanups (just edit) s edited)

private
 module AcquireQuiet where
  open import Data.Bool using (true; false)
  open import Data.Maybe using (just; nothing)
  open import Data.Maybe.Properties using (just-injective)
  open import Data.Product using (_×_; _,_; proj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
  open import Function using (case_of_)
  open import ConnectionManagement.Domain using (entry; ident; inbound; local; outbound; socket)
  open import ConnectionManagement.State using (State; cleanups; admitting; child; closeUncertain; closed; cm; commitHandshake; connected; count; countIncoming; descriptor; disconnected; duplexActive; entries; forkHandler; full; handlerError; handlerSocket; handlerStart; handlers; handling; handshakeError; handshakeQuery; handshakeResults; inboundActive; inboundIdle; inboundInfo; mapCell; negotiated; newConnection; newConnectionInfo; nextEntry; nextPromise; noResponderMode; outboundDup; outboundIdle; outboundUni; owner; pc; peer; query; reservedOutbound; responderMode; result; selectEntry; socketRef; sockets; state; taken; terminated; terminating; unnegotiated)
  open import ConnectionManagement.Store using (lookup; put)
  import ConnectionManagement.Rules.OutboundAcquire as A
  import ConnectionManagement.Rules.OutboundCases as C
  import ConnectionManagement.Rules.InformationChannel as Queue

  -- Every outbound-acquire write targets a different component of the shared state.
  Effects : State → State → Set
  Effects s s′ = cleanups s′ ≡ cleanups s
  identity : ∀ s → Effects s s
  identity s = refl
  entry-write : ∀ e st s → Effects s
    (record s { cm = record (cm s) { entries = put e st (entries (cm s)) } })
  entry-write e st s = refl
  socket-write : ∀ sock owner s → Effects s (record s { sockets = put sock owner (sockets s) })
  socket-write sock owner s = refl
  fork-write : ∀ child descriptor s → lookup child (handlers s) ≡ nothing → Effects s
    (record s { handlers = put child descriptor (handlers s)
              ; sockets = put (handlerSocket descriptor) (handling child) (sockets s) })
  fork-write child descriptor s absent = refl

  -- Transport store effects through an exact pair result.
  result-retains : ∀ {before} {pair pair′ : A.Frame × State} → just pair ≡ just pair′ →
    Effects before (proj₂ pair) → Effects before (proj₂ pair′)
  result-retains {before} eq = subst (λ pair → Effects before (proj₂ pair)) (just-injective eq)

  -- Reuse decisions retain immutable lookups and allocated resource identities.
  choice-retains : ∀ first e d f s {out} → A.applyChoice first e d f s ≡ just out → Effects s (proj₂ out)
  choice-retains first e C.retry f s ()
  choice-retains first e (C.waitInbound k) f s eq = result-retains {before = s} eq (identity s)
  choice-retains true e (C.refuse err) f s eq = result-retains {before = s} eq (identity s)
  choice-retains false e (C.refuse err) f s eq = result-retains {before = s} eq (identity s)
  choice-retains first e (C.gone result) f s eq = result-retains {before = s} eq (identity s)
  choice-retains true e (C.reuse st result) f s eq = result-retains {before = s} eq (entry-write e st s)
  choice-retains false e (C.reuse st result) f s eq = result-retains {before = s} eq (entry-write e st s)

  -- Reservation either reuses a branch or adds a fresh entry.
  known-retains : ∀ chosen m f s {out} → A.selectKnown chosen m f s ≡ just out → Effects s (proj₂ out)
  known-retains (just e) m f s eq with lookup e (entries (cm s)) in found
  ... | nothing = case eq of λ ()
  ... | just st = choice-retains true e (C.acquireCase st) f s eq
  known-retains nothing m f s eq with A.provenance (A.req f)
  ... | inbound = result-retains {before = s} eq (identity s)
  ... | outbound with lookup (ident (nextEntry (cm s))) (entries (cm s))
  ...   | just _ = case eq of λ ()
  ...   | nothing = result-retains {before = s} eq
    (entry-write (ident (nextEntry (cm s))) reservedOutbound s)

  -- Selection preserves effects of the actual guarded reservation branch.
  selection-retains : ∀ chosen f s {out} → A.selectEntry chosen f s ≡ just out → Effects s (proj₂ out)
  selection-retains chosen f s eq with mapCell (cm s)
  ... | taken _ = case eq of λ ()
  ... | full m with A.validSelection (A.peer (A.req f)) chosen m
  ...   | false = case eq of λ ()
  ...   | true = known-retains chosen m f s eq

  -- Handshake success changes entries and notification queues only.
  success-retains : ∀ mode e k h flow f s {out} → A.commitSuccess mode e k h flow f s ≡ just out → Effects s (proj₂ out)
  success-retains mode e k h flow f s eq with lookup e (entries (cm s))
  ... | nothing = case eq of λ ()
  ... | just st with C.successCase k (A.child (A.req f)) h flow st
  ...   | C.decision replacement notify (C.raised err) = result-retains {before = s} eq (identity s)
  ...   | C.decision replacement false (C.connected k′ flow′ h′) with replacement
  ...     | nothing = result-retains {before = s} eq (identity s)
  ...     | just replacement′ = result-retains {before = s} eq (entry-write e replacement′ s)
  success-retains mode e k h flow f s eq | just st | C.decision replacement false (C.disconnected k′ reason) with replacement
  ... | nothing = result-retains {before = s} eq (identity s)
  ... | just replacement′ = result-retains {before = s} eq (entry-write e replacement′ s)
  success-retains noResponderMode e k h flow f s eq | just st | C.decision replacement true result with result | replacement
  ... | C.connected _ _ _ | nothing = result-retains {before = s} eq (identity s)
  ... | C.connected _ _ _ | just replacement′ = result-retains {before = s} eq (entry-write e replacement′ s)
  ... | C.disconnected _ _ | nothing = result-retains {before = s} eq (identity s)
  ... | C.disconnected _ _ | just replacement′ = result-retains {before = s} eq (entry-write e replacement′ s)
  ... | C.raised _ | _ = result-retains {before = s} eq (identity s)
  success-retains responderMode e k h flow f s eq | just st | C.decision replacement true result
    with Queue.writeMessage (newConnection (newConnectionInfo outbound k flow h)) (inboundInfo s) in enqueued | result | replacement
  ... | nothing | C.connected _ _ _ | _ rewrite enqueued = case eq of λ ()
  ... | nothing | C.disconnected _ _ | _ rewrite enqueued = case eq of λ ()
  ... | just queue | C.connected _ _ _ | nothing rewrite enqueued = result-retains {before = s} eq (identity s)
  ... | just queue | C.connected _ _ _ | just replacement′ rewrite enqueued = result-retains {before = s} eq (entry-write e replacement′ s)
  ... | just queue | C.disconnected _ _ | nothing rewrite enqueued = result-retains {before = s} eq (identity s)
  ... | just queue | C.disconnected _ _ | just replacement′ rewrite enqueued = result-retains {before = s} eq (entry-write e replacement′ s)
  ... | _ | C.raised _ | _ = result-retains {before = s} eq (identity s)

  -- Error/query cleanup retains historical resources and immutable lookups.
  error-retains : ∀ e k reason f s {out} → A.commitError e k reason f s ≡ just out → Effects s (proj₂ out)
  error-retains e k reason f s eq with lookup e (entries (cm s)) | mapCell (cm s)
  ... | nothing | _ = case eq of λ ()
  ... | just _ | taken _ = case eq of λ ()
  ... | just st | full m = result-retains {before = s} eq (identity s)

  -- Exhaust every successful action without a savedFrame-validity premise.
  step-cleanups : ∀ caller mode action f s {out} → A.step caller mode action f s ≡ just out → Effects s (proj₂ out)
  step-cleanups caller mode (A.select chosen) f s eq with A.pc f
  ... | A.selecting = selection-retains chosen f s eq
  step-cleanups caller mode (A.select chosen) f s eq | (A.count p) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.allocatePromise e) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.openSocket e p) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.configureSocket e p) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.bindSocket e p) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.connectSocket e p) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.localAddress e p) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.commitResult e k result) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.closeError e err′) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.removeError e err′) = case eq of λ ()
  step-cleanups caller mode (A.select chosen) f s eq | (A.complete result) = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq with A.pc f | mapCell (cm s)
  ... | A.count next | full m with countIncoming (entries (cm s)) m
  ...   | nothing = case eq of λ ()
  ...   | just _ = result-retains {before = s} eq (identity s)
  step-cleanups caller mode A.readCounters f s eq | A.selecting | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.complete result) | _ = case eq of λ ()
  step-cleanups caller mode A.readCounters f s eq | (A.count p) | taken w = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq with A.pc f
  ... | A.allocatePromise e with lookup (ident (nextPromise s)) (handshakeResults s)
  ...   | just _ = case eq of λ ()
  ...   | nothing = result-retains {before = s} eq (identity s)
  step-cleanups caller mode A.newPromise f s eq | A.selecting = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.count p) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.openSocket e p) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.configureSocket e p) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.bindSocket e p) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.connectSocket e p) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.localAddress e p) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.commitResult e k result) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.closeError e err′) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.removeError e err′) = case eq of λ ()
  step-cleanups caller mode A.newPromise f s eq | (A.complete result) = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq with A.pc f | lookup (A.socketRef (A.req f)) (sockets s)
  ... | A.openSocket e p | nothing = result-retains {before = s} eq (socket-write (A.socketRef (A.req f)) (admitting caller) s)
  step-cleanups caller mode A.openOK f s eq | A.selecting | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.count p) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.complete result) | _ = case eq of λ ()
  step-cleanups caller mode A.openOK f s eq | (A.openSocket e p) | just sock = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq with A.pc f | A.bindLocal (A.req f)
  ... | A.configureSocket e p | nothing = result-retains {before = s} eq (identity s)
  ... | A.configureSocket e p | just _ = result-retains {before = s} eq (identity s)
  step-cleanups caller mode A.configureOK f s eq | A.selecting | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.count p) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-cleanups caller mode A.configureOK f s eq | (A.complete result) | _ = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq with A.pc f
  ... | A.bindSocket e p = result-retains {before = s} eq (identity s)
  step-cleanups caller mode A.bindOK f s eq | A.selecting = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.count p) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.allocatePromise e) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.openSocket e p) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.configureSocket e p) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.connectSocket e p) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.localAddress e p) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.commitResult e k result) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.closeError e err′) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.removeError e err′) = case eq of λ ()
  step-cleanups caller mode A.bindOK f s eq | (A.complete result) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq with A.pc f
  ... | A.connectSocket e p = result-retains {before = s} eq (identity s)
  step-cleanups caller mode A.connectOK f s eq | A.selecting = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.count p) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.allocatePromise e) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.openSocket e p) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.configureSocket e p) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.bindSocket e p) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.localAddress e p) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.commitResult e k result) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.closeError e err′) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.removeError e err′) = case eq of λ ()
  step-cleanups caller mode A.connectOK f s eq | (A.complete result) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq with A.pc f
  ... | A.localAddress e p = result-retains {before = s} eq (identity s)
  step-cleanups caller mode (A.gotLocal local) f s eq | A.selecting = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.count p) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.allocatePromise e) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.openSocket e p) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.configureSocket e p) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.bindSocket e p) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.connectSocket e p) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.commitResult e k result) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.closeError e err′) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.removeError e err′) = case eq of λ ()
  step-cleanups caller mode (A.gotLocal local) f s eq | (A.complete result) = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq with A.pc f | mapCell (cm s)
  ... | A.updateAddress e p k | full m with A.updateLocal k m
  ...   | true , m′ = result-retains {before = s} eq (identity s)
  ...   | false , m′ = result-retains {before = s} eq (identity s)
  step-cleanups caller mode A.updateLocalAddress f s eq | A.selecting | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.count p) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.complete result) | _ = case eq of λ ()
  step-cleanups caller mode A.updateLocalAddress f s eq | (A.updateAddress e p k) | taken w = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq with A.pc f | lookup (A.child (A.req f)) (handlers s) in absent
  ... | A.forkHandler e p k | nothing = result-retains {before = s} eq (fork-write (A.child (A.req f)) (handlerStart e (A.socketRef (A.req f)) p k) s absent)
  step-cleanups caller mode A.forkOK f s eq | A.selecting | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.count p) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.complete result) | _ = case eq of λ ()
  step-cleanups caller mode A.forkOK f s eq | (A.forkHandler e p k) | just h = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq with A.pc f
  ... | A.connectedCommit e p k with lookup e (entries (cm s)) in found
  ...   | nothing = case eq of λ ()
  ...   | just reservedOutbound = result-retains {before = s} eq
    (entry-write e (unnegotiated outbound k (A.child (A.req f))) s)
  ...   | just (unnegotiated inbound _ _) = result-retains {before = s} eq
    (entry-write e (unnegotiated outbound k (A.child (A.req f))) s)
  ...   | just old@(unnegotiated outbound _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(outboundUni _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(outboundDup _ _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(outboundIdle _ _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(inboundIdle _ _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(inboundActive _ _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(duplexActive _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(terminating _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(terminated _) = result-retains {before = s} eq (identity s)
  step-cleanups caller mode A.commitConnected f s eq | A.selecting = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.count p) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.allocatePromise e) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.openSocket e p) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.configureSocket e p) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.bindSocket e p) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.connectSocket e p) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.localAddress e p) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.commitResult e k result) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.closeError e err′) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.removeError e err′) = case eq of λ ()
  step-cleanups caller mode A.commitConnected f s eq | (A.complete result) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq with A.pc f
  ... | A.awaitResult e p k with lookup p (handshakeResults s)
  ...   | nothing = case eq of λ ()
  ...   | just result = result-retains {before = s} eq (identity s)
  step-cleanups caller mode A.readResult f s eq | A.selecting = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.count p) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.allocatePromise e) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.openSocket e p) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.configureSocket e p) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.bindSocket e p) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.connectSocket e p) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.localAddress e p) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.commitResult e k result) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.closeError e err′) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.removeError e err′) = case eq of λ ()
  step-cleanups caller mode A.readResult f s eq | (A.complete result) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq with A.pc f
  ... | A.commitResult e k (negotiated h flow) = success-retains mode e k h flow f s eq
  ... | A.commitResult e k query = error-retains e k handshakeQuery f s eq
  ... | A.commitResult e k (handlerError cls err) = error-retains e k (handshakeError cls err) f s eq
  step-cleanups caller mode A.commitHandshake f s eq | A.selecting = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.count p) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.allocatePromise e) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.openSocket e p) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.configureSocket e p) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.bindSocket e p) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.connectSocket e p) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.localAddress e p) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.closeError e err′) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.removeError e err′) = case eq of λ ()
  step-cleanups caller mode A.commitHandshake f s eq | (A.complete result) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq with A.pc f
  ... | A.waitingInbound e k with lookup e (entries (cm s)) in found
  ...   | nothing = case eq of λ ()
  ...   | just st = choice-retains false e (C.waitCase k st) f s eq
  step-cleanups caller mode A.waitNegotiated f s eq | A.selecting = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.count p) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.allocatePromise e) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.openSocket e p) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.configureSocket e p) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.bindSocket e p) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.connectSocket e p) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.localAddress e p) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.commitResult e k result) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.closeError e err′) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.removeError e err′) = case eq of λ ()
  step-cleanups caller mode A.waitNegotiated f s eq | (A.complete result) = case eq of λ ()
  step-cleanups caller mode (A.failIO err) f s eq with A.pc f
  ... | A.openSocket e p = result-retains {before = s} eq (identity s)
  ... | A.configureSocket e p = result-retains {before = s} eq (identity s)
  ... | A.bindSocket e p = result-retains {before = s} eq (identity s)
  ... | A.connectSocket e p = result-retains {before = s} eq (identity s)
  ... | A.localAddress e p = result-retains {before = s} eq (identity s)
  ... | A.forkHandler e p k = result-retains {before = s} eq (identity s)
  step-cleanups caller mode (A.failIO err) f s eq | A.selecting = case eq of λ ()
  step-cleanups caller mode (A.failIO err) f s eq | (A.count p) = case eq of λ ()
  step-cleanups caller mode (A.failIO err) f s eq | (A.allocatePromise e) = case eq of λ ()
  step-cleanups caller mode (A.failIO err) f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-cleanups caller mode (A.failIO err) f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-cleanups caller mode (A.failIO err) f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-cleanups caller mode (A.failIO err) f s eq | (A.commitResult e k result) = case eq of λ ()
  step-cleanups caller mode (A.failIO err) f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-cleanups caller mode (A.failIO err) f s eq | (A.closeError e err′) = case eq of λ ()
  step-cleanups caller mode (A.failIO err) f s eq | (A.removeError e err′) = case eq of λ ()
  step-cleanups caller mode (A.failIO err) f s eq | (A.complete result) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq with A.pc f
  ... | A.closeError e err = result-retains {before = s} eq (socket-write (A.socketRef (A.req f)) closed s)
  step-cleanups caller mode A.closeOK f s eq | A.selecting = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.count p) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.allocatePromise e) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.openSocket e p) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.configureSocket e p) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.bindSocket e p) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.connectSocket e p) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.localAddress e p) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.commitResult e k result) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.removeError e err′) = case eq of λ ()
  step-cleanups caller mode A.closeOK f s eq | (A.complete result) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq with A.pc f
  ... | A.closeError e _ = result-retains {before = s} eq (socket-write (A.socketRef (A.req f)) (closeUncertain err) s)
  step-cleanups caller mode (A.closeFailed err) f s eq | A.selecting = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.count p) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.allocatePromise e) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.openSocket e p) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.configureSocket e p) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.bindSocket e p) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.connectSocket e p) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.localAddress e p) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.commitResult e k result) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.removeError e err′) = case eq of λ ()
  step-cleanups caller mode (A.closeFailed err) f s eq | (A.complete result) = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq with A.pc f | mapCell (cm s)
  ... | A.removeError e err | full m = result-retains {before = s} eq (entry-write e (terminated nothing) s)
  step-cleanups caller mode A.removeReservation f s eq | A.selecting | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.count p) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.complete result) | _ = case eq of λ ()
  step-cleanups caller mode A.removeReservation f s eq | (A.removeError e err′) | taken w = case eq of λ ()
  step-cleanups caller mode A.returnResult f s ()

  -- Pair-projection-free form for the enclosing outbound-machine invariant.
  acquire-cleanups : ∀ caller mode action savedFrame before {savedFrame′ after} →
    A.step caller mode action savedFrame before ≡ just (savedFrame′ , after) →
    cleanups after ≡ cleanups before
  acquire-cleanups caller mode action savedFrame before =
    step-cleanups caller mode action savedFrame before

acquire-cleanups : ∀ caller mode action savedFrame before {savedFrame′ after} → A.step caller mode action savedFrame before ≡ just (savedFrame′ , after) → S.cleanups after ≡ S.cleanups before
acquire-cleanups = AcquireQuiet.acquire-cleanups

private
 module ReleaseQuiet where
  open S using (State; cm; mapCell; full; taken; lookupConnection; entries; countIncoming; terminated; terminating)
  -- Transport store effects through an exact pair result.
  release-result : ∀ {before} {pair pair′ : Release.Frame × State} → just pair ≡ just pair′ →
    S.cleanups (proj₂ pair) ≡ S.cleanups before → S.cleanups (proj₂ pair′) ≡ S.cleanups before
  release-result {before} eq = subst (λ pair → S.cleanups (proj₂ pair) ≡ S.cleanups before) (just-injective eq)

  -- A release branch writes only an entry value.
  release-apply-cleanups : ∀ e d f s → S.cleanups (proj₂ (Release.apply e d f s)) ≡ S.cleanups s
  release-apply-cleanups e d f s with Release.replacement d
  ... | nothing = refl
  ... | just st = refl

  -- Atomic pruning transports all shared-store effects.
  release-capacity : ∀ limit scores m e old d f s {out} → Release.capacity limit scores m e old d f s ≡ just out → S.cleanups (proj₂ out) ≡ S.cleanups s
  release-capacity limit scores m e old d f s eq with Release.needsCapacity d
  ... | false with scores
  ...   | nothing = release-result {before = s} eq (release-apply-cleanups e d f s)
  ...   | just _ = case eq of λ ()
  release-capacity limit scores m e old d f s eq | true with countIncoming (entries (cm s)) m
  ... | nothing = case eq of λ ()
  ... | just n with suc n ≤? limit
  ...   | yes _ with scores
  ...     | nothing = release-result {before = s} eq (release-apply-cleanups e d f s)
  ...     | just _ = case eq of λ ()
  release-capacity limit scores m e old d f s eq | true | just n | no _
    with scores | Release.replacement d | Prune.candidates m (entries (cm s))
  ... | just draws | just st | just candidates with Prune.candidateFor (Release.key f) e st
  ...   | nothing = case eq of λ ()
  ...   | just self with Prune.makePlan (suc n ∸ limit) self st candidates draws
  ...     | nothing = case eq of λ ()
  ...     | just selectedPlan with Prune.applyEdits (map (λ c → Prune.entryRef c , terminated nothing) (Prune.victims selectedPlan)) s in edited
  ...       | nothing = case eq of λ ()
  ...       | just s′ = release-result {before = s} eq (edits-cleanups (map (λ c → Prune.entryRef c , terminated nothing) (Prune.victims selectedPlan)) s edited)
  release-capacity limit scores m e old d f s eq | true | just n | no _ | nothing | _ | _ = case eq of λ ()
  release-capacity limit scores m e old d f s eq | true | just n | no _ | just _ | nothing | _ = case eq of λ ()
  release-capacity limit scores m e old d f s eq | true | just n | no _ | just _ | just _ | nothing = case eq of λ ()

  -- The transaction selects one of the checked release branches.
  release-transact : ∀ limit scores f s {out} → Release.transact limit scores f s ≡ just out → S.cleanups (proj₂ out) ≡ S.cleanups s
  release-transact limit scores f s eq with mapCell (cm s)
  ... | taken _ = case eq of λ ()
  ... | full m with lookupConnection (Release.key f) m
  ...   | nothing with scores
  ...     | nothing = release-result {before = s} eq (refl)
  ...     | just _ = case eq of λ ()
  release-transact limit scores f s eq | full m | just e with lookup e (entries (cm s))
  ... | nothing = case eq of λ ()
  ... | just st = release-capacity limit scores m e st (Release.branch (Release.key f) e st) f s eq

  -- Exhaust every successful action without a savedFrame-validity premise.
  release-step-cleanups : ∀ limit action f s {out} → Release.step limit action f s ≡ just out → S.cleanups (proj₂ out) ≡ S.cleanups s
  release-step-cleanups limit Release.transactionStep f s eq with Release.pc f
  ... | Release.transaction = release-transact limit nothing f s eq
  release-step-cleanups limit Release.transactionStep f s eq | (Release.check flag p) = case eq of λ ()
  release-step-cleanups limit Release.transactionStep f s eq | (Release.count p) = case eq of λ ()
  release-step-cleanups limit Release.transactionStep f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-cleanups limit Release.transactionStep f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-cleanups limit Release.transactionStep f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-cleanups limit Release.transactionStep f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-cleanups limit Release.transactionStep f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-cleanups limit Release.transactionStep f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-cleanups limit Release.transactionStep f s eq | (Release.complete result) = case eq of λ ()
  release-step-cleanups limit (Release.transactionPruning scores) f s eq with Release.pc f
  ... | Release.transaction = release-transact limit (just scores) f s eq
  release-step-cleanups limit (Release.transactionPruning scores) f s eq | (Release.check flag p) = case eq of λ ()
  release-step-cleanups limit (Release.transactionPruning scores) f s eq | (Release.count p) = case eq of λ ()
  release-step-cleanups limit (Release.transactionPruning scores) f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-cleanups limit (Release.transactionPruning scores) f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-cleanups limit (Release.transactionPruning scores) f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-cleanups limit (Release.transactionPruning scores) f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-cleanups limit (Release.transactionPruning scores) f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-cleanups limit (Release.transactionPruning scores) f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-cleanups limit (Release.transactionPruning scores) f s eq | (Release.complete result) = case eq of λ ()
  release-step-cleanups limit Release.checkAssertion f s eq with Release.pc f
  ... | Release.check true next = release-result {before = s} eq (refl)
  ... | Release.check false next = release-result {before = s} eq (refl)
  release-step-cleanups limit Release.checkAssertion f s eq | (Release.transaction) = case eq of λ ()
  release-step-cleanups limit Release.checkAssertion f s eq | (Release.count p) = case eq of λ ()
  release-step-cleanups limit Release.checkAssertion f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-cleanups limit Release.checkAssertion f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-cleanups limit Release.checkAssertion f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-cleanups limit Release.checkAssertion f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-cleanups limit Release.checkAssertion f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-cleanups limit Release.checkAssertion f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-cleanups limit Release.checkAssertion f s eq | (Release.complete result) = case eq of λ ()
  release-step-cleanups limit Release.readCounters f s eq with Release.pc f | mapCell (cm s)
  ... | Release.count next | full m with countIncoming (entries (cm s)) m
  ...   | nothing = case eq of λ ()
  ...   | just _ = release-result {before = s} eq (refl)
  release-step-cleanups limit Release.readCounters f s eq | (Release.transaction) | _ = case eq of λ ()
  release-step-cleanups limit Release.readCounters f s eq | (Release.check flag p) | _ = case eq of λ ()
  release-step-cleanups limit Release.readCounters f s eq | (Release.armTimer e v) | _ = case eq of λ ()
  release-step-cleanups limit Release.readCounters f s eq | (Release.waitIdle e v) | _ = case eq of λ ()
  release-step-cleanups limit Release.readCounters f s eq | (Release.timeoutWrite e v) | _ = case eq of λ ()
  release-step-cleanups limit Release.readCounters f s eq | (Release.cancel v p) | _ = case eq of λ ()
  release-step-cleanups limit Release.readCounters f s eq | (Release.delivering v p) | _ = case eq of λ ()
  release-step-cleanups limit Release.readCounters f s eq | (Release.prune victims result) | _ = case eq of λ ()
  release-step-cleanups limit Release.readCounters f s eq | (Release.complete result) | _ = case eq of λ ()
  release-step-cleanups limit Release.readCounters f s eq | (Release.count p) | taken w = case eq of λ ()
  release-step-cleanups limit Release.registerTimer f s eq with Release.pc f
  ... | Release.armTimer e w = release-result {before = s} eq (refl)
  release-step-cleanups limit Release.registerTimer f s eq | (Release.transaction) = case eq of λ ()
  release-step-cleanups limit Release.registerTimer f s eq | (Release.check flag p) = case eq of λ ()
  release-step-cleanups limit Release.registerTimer f s eq | (Release.count p) = case eq of λ ()
  release-step-cleanups limit Release.registerTimer f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-cleanups limit Release.registerTimer f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-cleanups limit Release.registerTimer f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-cleanups limit Release.registerTimer f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-cleanups limit Release.registerTimer f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-cleanups limit Release.registerTimer f s eq | (Release.complete result) = case eq of λ ()
  release-step-cleanups limit Release.expireTimer f s eq with Release.pc f | Release.timerReady f
  ... | Release.waitIdle e w | false = release-result {before = s} eq (refl)
  release-step-cleanups limit Release.expireTimer f s eq | (Release.transaction) | _ = case eq of λ ()
  release-step-cleanups limit Release.expireTimer f s eq | (Release.check flag p) | _ = case eq of λ ()
  release-step-cleanups limit Release.expireTimer f s eq | (Release.count p) | _ = case eq of λ ()
  release-step-cleanups limit Release.expireTimer f s eq | (Release.armTimer e v) | _ = case eq of λ ()
  release-step-cleanups limit Release.expireTimer f s eq | (Release.timeoutWrite e v) | _ = case eq of λ ()
  release-step-cleanups limit Release.expireTimer f s eq | (Release.cancel v p) | _ = case eq of λ ()
  release-step-cleanups limit Release.expireTimer f s eq | (Release.delivering v p) | _ = case eq of λ ()
  release-step-cleanups limit Release.expireTimer f s eq | (Release.prune victims result) | _ = case eq of λ ()
  release-step-cleanups limit Release.expireTimer f s eq | (Release.complete result) | _ = case eq of λ ()
  release-step-cleanups limit Release.expireTimer f s eq | (Release.waitIdle e v) | true = case eq of λ ()
  release-step-cleanups limit Release.selectWakeup f s eq with Release.pc f
  ... | Release.waitIdle e w with lookup e (entries (cm s))
  ...   | nothing = case eq of λ ()
  ...   | just st with Release.isIdle st | Release.isTerminated st | Release.timerReady f
  ...     | false | true | _ = release-result {before = s} eq (refl)
  ...     | false | false | _ = release-result {before = s} eq (refl)
  ...     | true | _ | true = release-result {before = s} eq (refl)
  ...     | true | _ | false = case eq of λ ()
  release-step-cleanups limit Release.selectWakeup f s eq | (Release.transaction) = case eq of λ ()
  release-step-cleanups limit Release.selectWakeup f s eq | (Release.check flag p) = case eq of λ ()
  release-step-cleanups limit Release.selectWakeup f s eq | (Release.count p) = case eq of λ ()
  release-step-cleanups limit Release.selectWakeup f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-cleanups limit Release.selectWakeup f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-cleanups limit Release.selectWakeup f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-cleanups limit Release.selectWakeup f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-cleanups limit Release.selectWakeup f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-cleanups limit Release.selectWakeup f s eq | (Release.complete result) = case eq of λ ()
  release-step-cleanups limit Release.commitTimeout f s eq with Release.pc f
  ... | Release.timeoutWrite e w with lookup e (entries (cm s))
  ...   | nothing = case eq of λ ()
  ...   | just _ = release-result {before = s} eq (refl)
  release-step-cleanups limit Release.commitTimeout f s eq | (Release.transaction) = case eq of λ ()
  release-step-cleanups limit Release.commitTimeout f s eq | (Release.check flag p) = case eq of λ ()
  release-step-cleanups limit Release.commitTimeout f s eq | (Release.count p) = case eq of λ ()
  release-step-cleanups limit Release.commitTimeout f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-cleanups limit Release.commitTimeout f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-cleanups limit Release.commitTimeout f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-cleanups limit Release.commitTimeout f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-cleanups limit Release.commitTimeout f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-cleanups limit Release.commitTimeout f s eq | (Release.complete result) = case eq of λ ()
  release-step-cleanups limit Release.requestCancellation f s eq with Release.pc f
  ... | Release.cancel w next = release-result {before = s} eq (refl)
  ... | Release.prune [] result = release-result {before = s} eq (refl)
  ... | Release.prune (victim ∷ rest) result = release-result {before = s} eq (refl)
  release-step-cleanups limit Release.requestCancellation f s eq | (Release.transaction) = case eq of λ ()
  release-step-cleanups limit Release.requestCancellation f s eq | (Release.check flag p) = case eq of λ ()
  release-step-cleanups limit Release.requestCancellation f s eq | (Release.count p) = case eq of λ ()
  release-step-cleanups limit Release.requestCancellation f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-cleanups limit Release.requestCancellation f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-cleanups limit Release.requestCancellation f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-cleanups limit Release.requestCancellation f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-cleanups limit Release.requestCancellation f s eq | (Release.complete result) = case eq of λ ()
  release-step-cleanups limit (Release.cancellationDelivered w) f s eq with Release.pc f
  ... | Release.delivering v next with w ≟ v
  ...   | yes _ = release-result {before = s} eq (refl)
  ...   | no _ = case eq of λ ()
  release-step-cleanups limit (Release.cancellationDelivered w) f s eq | (Release.transaction) = case eq of λ ()
  release-step-cleanups limit (Release.cancellationDelivered w) f s eq | (Release.check flag p) = case eq of λ ()
  release-step-cleanups limit (Release.cancellationDelivered w) f s eq | (Release.count p) = case eq of λ ()
  release-step-cleanups limit (Release.cancellationDelivered w) f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-cleanups limit (Release.cancellationDelivered w) f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-cleanups limit (Release.cancellationDelivered w) f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-cleanups limit (Release.cancellationDelivered w) f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-cleanups limit (Release.cancellationDelivered w) f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-cleanups limit (Release.cancellationDelivered w) f s eq | (Release.complete result) = case eq of λ ()
  release-step-cleanups limit Release.returnResult f s ()

release-cleanups : ∀ limit action savedFrame before {savedFrame′ after} → Release.step limit action savedFrame before ≡ just (savedFrame′ , after) → S.cleanups after ≡ S.cleanups before
release-cleanups limit action savedFrame before actual = ReleaseQuiet.release-step-cleanups limit action savedFrame before actual


-- Source operations other than the two cleanup writers preserve the store.
machine-same : ∀ action c {d} → M.advance action c ≡ just d → QuietMachine action → S.cleanups (M.world d) ≡ S.cleanups (M.world c)
machine-same (M.cleanupStep worker action) c actual ()
machine-same (M.handlerExit worker) c actual ()
machine-same (M.admissionStep worker action) c eq quiet = admission-quiet worker action c eq
machine-same (M.handshakeStep worker action) c eq quiet = handshake-quiet worker action c eq
machine-same (M.handlerStep worker action) c eq quiet with Life.step worker action (M.handlerLifecycles c) (M.inboundGovernor c) (M.world c)
... | nothing = case eq of λ ()
... | just (runtime , governor) = case just-injective eq of λ { refl → refl }
machine-same (M.remoteStep action) c eq quiet with Life.allowRemote action (M.handlerLifecycles c) (M.world c)
... | false = case eq of λ ()
... | true with Remote.step (M.promotionHardLimit c) (M.pruningGeneration c) action (M.remoteCall c) (M.inboundGovernor c) (M.world c)
...   | nothing = case eq of λ ()
...   | just plan with Prune.applyEdits (Remote.edits plan) (M.world c) in actual
...     | nothing = case eq of λ ()
...     | just next with just-injective eq
...       | refl = edits-cleanups (Remote.edits plan) (M.world c) actual
machine-same (M.releaseStep action) c eq quiet with Life.allowRelease action (M.handlerLifecycles c) (M.world c)
... | false = case eq of λ ()
... | true with InRelease.step action (M.inboundRelease c) (M.inboundGovernor c) (M.world c)
...   | nothing = case eq of λ ()
...   | just plan with InRelease.applyEdit (InRelease.edit plan) (M.world c) in actual
...     | nothing = case eq of λ ()
...     | just next with just-injective eq
...       | refl = edit-cleanups (InRelease.edit plan) (M.world c) actual
machine-same (M.igStep action) c eq quiet with Life.allowIG action (M.handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (M.responder c) action (M.inboundGovernor c) (S.inboundInfo (M.world c))
...   | nothing = case eq of λ ()
...   | just (governor , queue) = case just-injective eq of λ { refl → refl }
machine-same (M.handlerPublication worker result outcome) c eq quiet with any (λ other → does (other ≟ worker)) (M.publicationFaults c)
... | true = case eq of λ ()
... | false with H.publishBoundary worker result (M.world c) in actual | outcome
...   | nothing | _ = case eq of λ ()
...   | just (H.published next) | M.resultWritten with just-injective eq
...     | refl = publication-cleanups worker result (M.world c) actual
machine-same (M.handlerPublication worker result outcome) c eq quiet | false | just (H.published next) | M.duplicateWrite = case eq of λ ()
machine-same (M.handlerPublication worker result outcome) c eq quiet | false | just H.writerBlocked | M.resultWritten = case eq of λ ()
machine-same (M.handlerPublication worker result outcome) c eq quiet | false | just H.writerBlocked | M.duplicateWrite = case just-injective eq of λ { refl → refl }

private
 acquire-wrapper : ∀ worker action c {d} → O.advanceAcquire worker action c ≡ just d → S.cleanups (M.world (O.core d)) ≡ S.cleanups (M.world (O.core c))
 acquire-wrapper worker A.returnResult c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.pc savedFrame
 ...   | A.complete result = case just-injective eq of λ { refl → refl }
 ...   | A.selecting = case eq of λ ()
 ...   | A.count pc = case eq of λ ()
 ...   | A.allocatePromise entry = case eq of λ ()
 ...   | A.openSocket entry promise = case eq of λ ()
 ...   | A.configureSocket entry promise = case eq of λ ()
 ...   | A.bindSocket entry promise = case eq of λ ()
 ...   | A.connectSocket entry promise = case eq of λ ()
 ...   | A.localAddress entry promise = case eq of λ ()
 ...   | A.updateAddress entry promise key = case eq of λ ()
 ...   | A.forkHandler entry promise key = case eq of λ ()
 ...   | A.connectedCommit entry promise key = case eq of λ ()
 ...   | A.awaitResult entry promise key = case eq of λ ()
 ...   | A.commitResult entry key result = case eq of λ ()
 ...   | A.waitingInbound entry key = case eq of λ ()
 ...   | A.closeError entry error = case eq of λ ()
 ...   | A.removeError entry error = case eq of λ ()
 acquire-wrapper worker (A.select chosen) c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) (A.select chosen) savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) (A.select chosen) savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.readCounters c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.readCounters savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.readCounters savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.newPromise c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.newPromise savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.newPromise savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.openOK c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.openOK savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.openOK savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.configureOK c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.configureOK savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.configureOK savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.bindOK c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.bindOK savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.bindOK savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.connectOK c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.connectOK savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.connectOK savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker (A.gotLocal local) c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) (A.gotLocal local) savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) (A.gotLocal local) savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.updateLocalAddress c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.updateLocalAddress savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.updateLocalAddress savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.forkOK c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.forkOK savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.forkOK savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.commitConnected c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.commitConnected savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.commitConnected savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.readResult c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.readResult savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.readResult savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.commitHandshake c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.commitHandshake savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.commitHandshake savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker (A.failIO error) c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) (A.failIO error) savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) (A.failIO error) savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker (A.closeFailed error) c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) (A.closeFailed error) savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) (A.closeFailed error) savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.closeOK c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.closeOK savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.closeOK savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.removeReservation c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.removeReservation savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.removeReservation savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.waitNegotiated c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.waitNegotiated savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-cleanups worker (M.responder (O.core c)) A.waitNegotiated savedFrame (M.world (O.core c)) actual
 release-wrapper : ∀ worker action c {d} → O.advanceRelease worker action c ≡ just d → S.cleanups (M.world (O.core d)) ≡ S.cleanups (M.world (O.core c))
 release-wrapper worker Release.returnResult c eq with lookup worker (O.releasing c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with Release.pc savedFrame
 ...   | Release.complete result = case just-injective eq of λ { refl → refl }
 ...   | Release.transaction = case eq of λ ()
 ...   | Release.check flag pc = case eq of λ ()
 ...   | Release.count pc = case eq of λ ()
 ...   | Release.armTimer entry target = case eq of λ ()
 ...   | Release.waitIdle entry target = case eq of λ ()
 ...   | Release.timeoutWrite entry target = case eq of λ ()
 ...   | Release.cancel target pc = case eq of λ ()
 ...   | Release.delivering target pc = case eq of λ ()
 ...   | Release.prune victims result = case eq of λ ()
 release-wrapper worker Release.transactionStep c eq with lookup worker (O.releasing c) | O.canDeliver Release.transactionStep c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.transactionStep savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-cleanups (M.promotionHardLimit (O.core c)) Release.transactionStep savedFrame (M.world (O.core c)) actual
 release-wrapper worker (Release.transactionPruning scores) c eq with lookup worker (O.releasing c) | O.canDeliver (Release.transactionPruning scores) c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) (Release.transactionPruning scores) savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-cleanups (M.promotionHardLimit (O.core c)) (Release.transactionPruning scores) savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.checkAssertion c eq with lookup worker (O.releasing c) | O.canDeliver Release.checkAssertion c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.checkAssertion savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-cleanups (M.promotionHardLimit (O.core c)) Release.checkAssertion savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.readCounters c eq with lookup worker (O.releasing c) | O.canDeliver Release.readCounters c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.readCounters savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-cleanups (M.promotionHardLimit (O.core c)) Release.readCounters savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.registerTimer c eq with lookup worker (O.releasing c) | O.canDeliver Release.registerTimer c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.registerTimer savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-cleanups (M.promotionHardLimit (O.core c)) Release.registerTimer savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.expireTimer c eq with lookup worker (O.releasing c) | O.canDeliver Release.expireTimer c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.expireTimer savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-cleanups (M.promotionHardLimit (O.core c)) Release.expireTimer savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.selectWakeup c eq with lookup worker (O.releasing c) | O.canDeliver Release.selectWakeup c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.selectWakeup savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-cleanups (M.promotionHardLimit (O.core c)) Release.selectWakeup savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.commitTimeout c eq with lookup worker (O.releasing c) | O.canDeliver Release.commitTimeout c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.commitTimeout savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-cleanups (M.promotionHardLimit (O.core c)) Release.commitTimeout savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.requestCancellation c eq with lookup worker (O.releasing c) | O.canDeliver Release.requestCancellation c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.requestCancellation savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-cleanups (M.promotionHardLimit (O.core c)) Release.requestCancellation savedFrame (M.world (O.core c)) actual
 release-wrapper worker (Release.cancellationDelivered target) c eq with lookup worker (O.releasing c) | O.canDeliver (Release.cancellationDelivered target) c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) (Release.cancellationDelivered target) savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-cleanups (M.promotionHardLimit (O.core c)) (Release.cancellationDelivered target) savedFrame (M.world (O.core c)) actual

outbound-same : ∀ action c {d} → O.advance action c ≡ just d → QuietOutbound action → S.cleanups (M.world (O.core d)) ≡ S.cleanups (M.world (O.core c))
outbound-same (O.inbound action) c actual quiet with M.advance action (O.core c) in stepped
... | nothing = case actual of λ ()
... | just next with just-injective actual
...   | refl = machine-same action (O.core c) stepped quiet
outbound-same (O.acquire worker action) c actual quiet = acquire-wrapper worker action c actual
outbound-same (O.release worker action) c actual quiet = release-wrapper worker action c actual
outbound-same (O.beginAcquire worker request) c actual quiet with lookup worker (O.acquiring c) | lookup worker (O.releasing c)
... | nothing | nothing = case just-injective actual of λ { refl → refl }
... | nothing | just _ = case actual of λ ()
... | just _ | _ = case actual of λ ()
outbound-same (O.beginRelease worker key) c actual quiet with lookup worker (O.acquiring c) | lookup worker (O.releasing c)
... | nothing | nothing = case just-injective actual of λ { refl → refl }
... | nothing | just _ = case actual of λ ()
... | just _ | _ = case actual of λ ()

-- A completed record is terminal: no cleanup operation applies to it.
Unfinished : S.CleanupPC → Set
Unfinished (S.cleanupDone _) = ⊥
Unfinished _ = ⊤
-- The stepping worker's record is replaced; every other record is unchanged.
Rewrites : WorkerId → S.State → S.State → Set
Rewrites w s t = Σ S.CleanupPC (λ next → S.cleanups t ≡ put w next (S.cleanups s))

select-effect : ∀ w h l decision s → Rewrites w s (Cleanup.selectCleanup w h l decision s)
select-effect w h l Cleanup.terminateAndPurge s = _ , refl
select-effect w h l Cleanup.purgeOnly s = _ , refl
select-effect w h l (Cleanup.waitBeforePurge st) s = _ , refl

worker-effect : ∀ act w h p s {t} → Cleanup.stepWorker w h p act s ≡ just t → Unfinished p × Rewrites w s t
worker-effect act w h (S.cleanupDone outcome) s ()
worker-effect Cleanup.takeCleanupMap w h S.cleanupAcquire s eq with CM.takeMap w (S.cm s)
... | nothing = case eq of λ ()
... | just (l , c) = case just-injective eq of λ { refl → tt , S.cleanupSelect l , refl }
worker-effect Cleanup.selectCleanupEntry w h S.cleanupAcquire s ()
worker-effect Cleanup.closeHandlerSocket w h S.cleanupAcquire s ()
worker-effect Cleanup.publishCleanupMap w h S.cleanupAcquire s ()
worker-effect Cleanup.restoreCleanupMap w h S.cleanupAcquire s ()
worker-effect Cleanup.readCleanupCounters w h S.cleanupAcquire s ()
worker-effect Cleanup.finishTimeWait w h S.cleanupAcquire s ()
worker-effect (Cleanup.failSocketClose x) w h S.cleanupAcquire s ()
worker-effect Cleanup.timeWaitElapsed w h S.cleanupAcquire s ()
worker-effect (Cleanup.interruptTimeWait x) w h S.cleanupAcquire s ()
worker-effect Cleanup.takeCleanupMap w h (S.cleanupSelect l) s ()
worker-effect Cleanup.selectCleanupEntry w h (S.cleanupSelect l) s eq with S.mapCell (S.cm s)
... | S.full _ = case eq of λ ()
... | S.taken owner with owner ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with lookup (S.handlerEntry h) (S.entries (S.cm s))
...     | nothing = case eq of λ ()
...     | just st = case just-injective eq of λ { refl → tt , select-effect w h l (Cleanup.decideCleanup st) s }
worker-effect Cleanup.closeHandlerSocket w h (S.cleanupSelect l) s ()
worker-effect Cleanup.publishCleanupMap w h (S.cleanupSelect l) s ()
worker-effect Cleanup.restoreCleanupMap w h (S.cleanupSelect l) s ()
worker-effect Cleanup.readCleanupCounters w h (S.cleanupSelect l) s ()
worker-effect Cleanup.finishTimeWait w h (S.cleanupSelect l) s ()
worker-effect (Cleanup.failSocketClose x) w h (S.cleanupSelect l) s ()
worker-effect Cleanup.timeWaitElapsed w h (S.cleanupSelect l) s ()
worker-effect (Cleanup.interruptTimeWait x) w h (S.cleanupSelect l) s ()
worker-effect Cleanup.takeCleanupMap w h (S.cleanupClose l m tail) s ()
worker-effect Cleanup.selectCleanupEntry w h (S.cleanupClose l m tail) s ()
worker-effect Cleanup.closeHandlerSocket w h (S.cleanupClose l m tail) s eq = case just-injective eq of λ { refl → tt , S.cleanupPublish l m tail , refl }
worker-effect Cleanup.publishCleanupMap w h (S.cleanupClose l m tail) s ()
worker-effect Cleanup.restoreCleanupMap w h (S.cleanupClose l m tail) s ()
worker-effect Cleanup.readCleanupCounters w h (S.cleanupClose l m tail) s ()
worker-effect Cleanup.finishTimeWait w h (S.cleanupClose l m tail) s ()
worker-effect (Cleanup.failSocketClose x) w h (S.cleanupClose l m tail) s eq = case just-injective eq of λ { refl → tt , S.cleanupRestore l x , refl }
worker-effect Cleanup.timeWaitElapsed w h (S.cleanupClose l m tail) s ()
worker-effect (Cleanup.interruptTimeWait x) w h (S.cleanupClose l m tail) s ()
worker-effect Cleanup.takeCleanupMap w h (S.cleanupPublish l m tail) s ()
worker-effect Cleanup.selectCleanupEntry w h (S.cleanupPublish l m tail) s ()
worker-effect Cleanup.closeHandlerSocket w h (S.cleanupPublish l m tail) s ()
worker-effect Cleanup.publishCleanupMap w h (S.cleanupPublish l m tail) s eq with CM.putMap l m (S.cm s)
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → tt , Cleanup.afterPublish tail , refl }
worker-effect Cleanup.restoreCleanupMap w h (S.cleanupPublish l m tail) s ()
worker-effect Cleanup.readCleanupCounters w h (S.cleanupPublish l m tail) s ()
worker-effect Cleanup.finishTimeWait w h (S.cleanupPublish l m tail) s ()
worker-effect (Cleanup.failSocketClose x) w h (S.cleanupPublish l m tail) s ()
worker-effect Cleanup.timeWaitElapsed w h (S.cleanupPublish l m tail) s ()
worker-effect (Cleanup.interruptTimeWait x) w h (S.cleanupPublish l m tail) s ()
worker-effect Cleanup.takeCleanupMap w h (S.cleanupRestore l err) s ()
worker-effect Cleanup.selectCleanupEntry w h (S.cleanupRestore l err) s ()
worker-effect Cleanup.closeHandlerSocket w h (S.cleanupRestore l err) s ()
worker-effect Cleanup.publishCleanupMap w h (S.cleanupRestore l err) s ()
worker-effect Cleanup.restoreCleanupMap w h (S.cleanupRestore l err) s eq with CM.restoreMap l (S.cm s)
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → tt , S.cleanupDone (S.cleanupError err) , refl }
worker-effect Cleanup.readCleanupCounters w h (S.cleanupRestore l err) s ()
worker-effect Cleanup.finishTimeWait w h (S.cleanupRestore l err) s ()
worker-effect (Cleanup.failSocketClose x) w h (S.cleanupRestore l err) s ()
worker-effect Cleanup.timeWaitElapsed w h (S.cleanupRestore l err) s ()
worker-effect (Cleanup.interruptTimeWait x) w h (S.cleanupRestore l err) s ()
worker-effect Cleanup.takeCleanupMap w h (S.cleanupWaiting captured) s ()
worker-effect Cleanup.selectCleanupEntry w h (S.cleanupWaiting captured) s ()
worker-effect Cleanup.closeHandlerSocket w h (S.cleanupWaiting captured) s ()
worker-effect Cleanup.publishCleanupMap w h (S.cleanupWaiting captured) s ()
worker-effect Cleanup.restoreCleanupMap w h (S.cleanupWaiting captured) s ()
worker-effect Cleanup.readCleanupCounters w h (S.cleanupWaiting captured) s ()
worker-effect Cleanup.finishTimeWait w h (S.cleanupWaiting captured) s ()
worker-effect (Cleanup.failSocketClose x) w h (S.cleanupWaiting captured) s ()
worker-effect Cleanup.timeWaitElapsed w h (S.cleanupWaiting captured) s eq = case just-injective eq of λ { refl → tt , S.cleanupFinalize captured S.cleanupNormal , refl }
worker-effect (Cleanup.interruptTimeWait x) w h (S.cleanupWaiting captured) s eq = case just-injective eq of λ { refl → tt , S.cleanupFinalize captured (S.cleanupError x) , refl }
worker-effect Cleanup.takeCleanupMap w h (S.cleanupFinalize captured outcome) s ()
worker-effect Cleanup.selectCleanupEntry w h (S.cleanupFinalize captured outcome) s ()
worker-effect Cleanup.closeHandlerSocket w h (S.cleanupFinalize captured outcome) s ()
worker-effect Cleanup.publishCleanupMap w h (S.cleanupFinalize captured outcome) s ()
worker-effect Cleanup.restoreCleanupMap w h (S.cleanupFinalize captured outcome) s ()
worker-effect Cleanup.readCleanupCounters w h (S.cleanupFinalize captured outcome) s ()
worker-effect Cleanup.finishTimeWait w h (S.cleanupFinalize captured outcome) s eq with S.mapCell (S.cm s)
... | S.taken _ = case eq of λ ()
... | S.full m with lookup (S.handlerEntry h) (S.entries (S.cm s))
...   | nothing = case eq of λ ()
...   | just _ = case just-injective eq of λ { refl → tt , S.cleanupCount outcome , refl }
worker-effect (Cleanup.failSocketClose x) w h (S.cleanupFinalize captured outcome) s ()
worker-effect Cleanup.timeWaitElapsed w h (S.cleanupFinalize captured outcome) s ()
worker-effect (Cleanup.interruptTimeWait x) w h (S.cleanupFinalize captured outcome) s ()
worker-effect Cleanup.takeCleanupMap w h (S.cleanupCount outcome) s ()
worker-effect Cleanup.selectCleanupEntry w h (S.cleanupCount outcome) s ()
worker-effect Cleanup.closeHandlerSocket w h (S.cleanupCount outcome) s ()
worker-effect Cleanup.publishCleanupMap w h (S.cleanupCount outcome) s ()
worker-effect Cleanup.restoreCleanupMap w h (S.cleanupCount outcome) s ()
worker-effect Cleanup.readCleanupCounters w h (S.cleanupCount outcome) s eq with S.mapCell (S.cm s)
... | S.taken _ = case eq of λ ()
... | S.full m with S.countIncoming (S.entries (S.cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = case just-injective eq of λ { refl → tt , S.cleanupDone outcome , refl }
worker-effect Cleanup.finishTimeWait w h (S.cleanupCount outcome) s ()
worker-effect (Cleanup.failSocketClose x) w h (S.cleanupCount outcome) s ()
worker-effect Cleanup.timeWaitElapsed w h (S.cleanupCount outcome) s ()
worker-effect (Cleanup.interruptTimeWait x) w h (S.cleanupCount outcome) s ()

-- handlerExit creates exactly the exiting worker's record, at cleanupAcquire.
begin-effect : ∀ w s {t} → Cleanup.beginCleanupBoundary w s ≡ just t →
  lookup w (S.cleanups s) ≡ nothing × S.cleanups t ≡ put w S.cleanupAcquire (S.cleanups s)
begin-effect w s eq with lookup w (S.handlers s) | lookup w (S.cleanups s)
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
... | just h | nothing = case just-injective eq of λ { refl → refl , refl }
exit-effect : ∀ w c {d} → M.advance (M.handlerExit w) c ≡ just d →
  lookup w (S.cleanups (M.world c)) ≡ nothing ×
  S.cleanups (M.world d) ≡ put w S.cleanupAcquire (S.cleanups (M.world c))
exit-effect w c eq with Life.mayExit w (M.handlerLifecycles c)
... | false = case eq of λ ()
... | true with Cleanup.beginCleanupBoundary w (M.world c) in actual
...   | nothing = case eq of λ ()
...   | just next with just-injective eq
...     | refl = begin-effect w (M.world c) actual

-- A cleanup step needs an existing unfinished record of the stepping worker.
record Stepped (w : WorkerId) (before after : S.State) : Set where
 constructor stepped
 field
  prior : S.CleanupPC
  found : lookup w (S.cleanups before) ≡ just prior
  unfinished : Unfinished prior
  rewrites : Rewrites w before after
cleanup-effect : ∀ w act c {d} → M.advance (M.cleanupStep w act) c ≡ just d →
  Stepped w (M.world c) (M.world d)
cleanup-effect w act c eq with lookup w (S.handlers (M.world c)) | lookup w (S.cleanups (M.world c)) in found
... | nothing | _ = case eq of λ ()
... | just h | nothing = case eq of λ ()
... | just h | just p with Cleanup.stepWorker w h p act (M.world c) in actual
...   | nothing = case eq of λ ()
...   | just next with just-injective eq
...     | refl with worker-effect act w h p (M.world c) actual
...       | live , rw = stepped p found live rw
