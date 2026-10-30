{-# OPTIONS --guardedness #-}

-- Lift source invariants through every Server action. New handoff/socket
-- writers need explicit proofs; inherited effects use existing source traces.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerAdmissionInvariant
  (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.MuxPublicationUnwind as Publication
private
  module S = Server isBearerClosed
  module N = Publication isBearerClosed

-- Observe just the new writes, without adding a transition or a guard.
withWorld : O.Configuration → Shared.State → O.Configuration
withWorld c world = record c { core = Machine.replaceWorld (O.core c) world }
admitSource : WorkerId → Shared.Admission → O.Configuration → O.Configuration
admitSource w req c = withWorld c (record (Machine.world (O.core c))
  { admissions = put w (Shared.admissionWorker req Shared.acquireMap) (Shared.admissions (Machine.world (O.core c)))
  ; sockets = put (Shared.socketRef req) (Shared.admitting w) (Shared.sockets (Machine.world (O.core c))) })
socketSource : SocketId → Shared.SocketOwner → O.Configuration → O.Configuration
socketSource sock owner c = withWorld c (record (Machine.world (O.core c))
  { sockets = put sock owner (Shared.sockets (Machine.world (O.core c))) })

module Lift
  (Valid : O.Configuration → Set)
  (lower-preserves : ∀ a n {n′} → N.step a n ≡ just n′ → Valid (N.source n) → Valid (N.source n′))
  (admit-preserves : ∀ w req c → Valid c → Valid (admitSource w req c))
  (socket-preserves : ∀ sock owner c → Valid c → Valid (socketSource sock owner c)) where

  -- Successful birth writes an admission and socket; physical metadata is separate.
  fork-preserves : ∀ w req s {t} → S.forkAccepted w req s ≡ just t → Valid (S.source s) → Valid (S.source t)
  fork-preserves w req s eq valid with S.accepting (S.stage s) | S.listenerOpen s |
    S.sameLimit req (S.workers s) | S.fresh w s | S.fresh (Shared.child req) s |
    w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (S.shared s))
  ... | true | true | true | true | true | no _ | nothing =
    case just-injective eq of λ { refl → admit-preserves w req (S.source s) valid }
  ... | false | _ | _ | _ | _ | _ | _ = case eq of λ ()
  ... | true | false | _ | _ | _ | _ | _ = case eq of λ ()
  ... | true | true | false | _ | _ | _ | _ = case eq of λ ()
  ... | true | true | true | false | _ | _ | _ = case eq of λ ()
  ... | true | true | true | true | false | _ | _ = case eq of λ ()
  ... | true | true | true | true | true | yes _ | _ = case eq of λ ()
  ... | true | true | true | true | true | no _ | just _ = case eq of λ ()

  -- Guarded delegation and scope plans retain actual lower-step evidence.
  inherit-preserves : ∀ a s {t} → S.inherit a s ≡ just t → Valid (S.source s) → Valid (S.source t)
  inherit-preserves a s eq valid with S.allowed a s
  ... | false = case eq of λ ()
  ... | true with N.step a (S.base s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just n = case just-injective eq of λ { refl → lower-preserves a (S.base s) advanced valid }
  enact-scope-preserves : ∀ p s {t} → S.enactScope p s ≡ just t → Valid (S.source s) → Valid (S.source t)
  enact-scope-preserves p s eq valid with S.physicalAction p
  ... | nothing = case just-injective eq of λ { refl → valid }
  ... | just a with N.step a (S.base s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just n = case just-injective eq of λ { refl → lower-preserves a (S.base s) advanced valid }
  scope-preserves : ∀ a s {t} → S.scopeAdvance a s ≡ just t → Valid (S.source s) → Valid (S.source t)
  scope-preserves a s eq valid with S.chooseScope a s
  ... | nothing = case eq of λ ()
  ... | just p = enact-scope-preserves p s eq valid

  -- Return, exception and result observations change only raw-worker metadata.
  return-preserves : ∀ w s {t} → S.observeReturn w s ≡ just t → Valid (S.source s) → Valid (S.source t)
  return-preserves w s eq valid with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
  ... | just worker | just a with S.pc worker | Shared.pc a
  ...   | S.calling | Shared.completedHandshake (Shared.connected _) = case just-injective eq of λ { refl → valid }
  ...   | S.calling | Shared.completedHandshake (Shared.disconnected _) = case just-injective eq of λ { refl → valid }
  ...   | S.calling | Shared.acquireMap = case eq of λ ()
  ...   | S.calling | Shared.count _ = case eq of λ ()
  ...   | S.calling | Shared.prepare _ = case eq of λ ()
  ...   | S.calling | Shared.selectEntry _ _ = case eq of λ ()
  ...   | S.calling | Shared.forkHandler _ _ _ = case eq of λ ()
  ...   | S.calling | Shared.publish _ _ _ = case eq of λ ()
  ...   | S.calling | Shared.reject _ _ = case eq of λ ()
  ...   | S.calling | Shared.closeSocket _ = case eq of λ ()
  ...   | S.calling | Shared.finished _ = case eq of λ ()
  ...   | S.calling | Shared.countPublished _ _ = case eq of λ ()
  ...   | S.calling | Shared.awaitHandshake _ _ = case eq of λ ()
  ...   | S.calling | Shared.commitHandshake _ _ = case eq of λ ()
  ...   | S.calling | Shared.countHandshake _ = case eq of λ ()
  ...   | S.calling | Shared.notifyInbound _ = case eq of λ ()
  ...   | S.calling | Shared.returnHandshake _ = case eq of λ ()
  ...   | S.calling | Shared.impossibleHandshake = case eq of λ ()
  ...   | S.closeDisconnected | _ = case eq of λ ()
  ...   | S.closeException _ | _ = case eq of λ ()
  ...   | S.closePrefix _ _ | _ = case eq of λ ()
  ...   | S.bodyExited _ | _ = case eq of λ ()
  ...   | S.resultAvailable _ | _ = case eq of λ ()
  return-preserves w s eq valid | nothing | _ = case eq of λ ()
  return-preserves w s eq valid | just _ | nothing = case eq of λ ()
  prefix-return-preserves : ∀ w s {t} → S.prefixReturned w s ≡ just t → Valid (S.source s) → Valid (S.source t)
  prefix-return-preserves w s eq valid with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
  ... | just worker | just a with S.pc worker | Shared.pc a
  ...   | S.calling | Shared.closeSocket Shared.hardLimitReached = case just-injective eq of λ { refl → valid }
  ...   | S.calling | Shared.acquireMap = case eq of λ ()
  ...   | S.calling | Shared.count _ = case eq of λ ()
  ...   | S.calling | Shared.prepare _ = case eq of λ ()
  ...   | S.calling | Shared.selectEntry _ _ = case eq of λ ()
  ...   | S.calling | Shared.forkHandler _ _ _ = case eq of λ ()
  ...   | S.calling | Shared.publish _ _ _ = case eq of λ ()
  ...   | S.calling | Shared.reject _ _ = case eq of λ ()
  ...   | S.calling | Shared.finished _ = case eq of λ ()
  ...   | S.calling | Shared.countPublished _ _ = case eq of λ ()
  ...   | S.calling | Shared.awaitHandshake _ _ = case eq of λ ()
  ...   | S.calling | Shared.commitHandshake _ _ = case eq of λ ()
  ...   | S.calling | Shared.countHandshake _ = case eq of λ ()
  ...   | S.calling | Shared.notifyInbound _ = case eq of λ ()
  ...   | S.calling | Shared.returnHandshake _ = case eq of λ ()
  ...   | S.calling | Shared.completedHandshake _ = case eq of λ ()
  ...   | S.calling | Shared.impossibleHandshake = case eq of λ ()
  ...   | S.calling | Shared.closeSocket Shared.forbidden = case eq of λ ()
  ...   | S.calling | Shared.closeSocket Shared.forkFailed = case eq of λ ()
  ...   | S.closeDisconnected | _ = case eq of λ ()
  ...   | S.closeException _ | _ = case eq of λ ()
  ...   | S.closePrefix _ _ | _ = case eq of λ ()
  ...   | S.bodyExited _ | _ = case eq of λ ()
  ...   | S.resultAvailable _ | _ = case eq of λ ()
  prefix-return-preserves w s eq valid | nothing | _ = case eq of λ ()
  prefix-return-preserves w s eq valid | just _ | nothing = case eq of λ ()
  prefix-exception-preserves : ∀ w err s {t} → S.prefixException w err s ≡ just t → Valid (S.source s) → Valid (S.source t)
  prefix-exception-preserves w err s eq valid with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
  ... | just worker | just a with S.pc worker | Shared.pc a
  ...   | S.calling | Shared.closeSocket Shared.forbidden = case just-injective eq of λ { refl → valid }
  ...   | S.calling | Shared.closeSocket Shared.forkFailed = case just-injective eq of λ { refl → valid }
  ...   | S.calling | Shared.acquireMap = case eq of λ ()
  ...   | S.calling | Shared.count _ = case eq of λ ()
  ...   | S.calling | Shared.prepare _ = case eq of λ ()
  ...   | S.calling | Shared.selectEntry _ _ = case eq of λ ()
  ...   | S.calling | Shared.forkHandler _ _ _ = case eq of λ ()
  ...   | S.calling | Shared.publish _ _ _ = case eq of λ ()
  ...   | S.calling | Shared.reject _ _ = case eq of λ ()
  ...   | S.calling | Shared.finished _ = case eq of λ ()
  ...   | S.calling | Shared.countPublished _ _ = case eq of λ ()
  ...   | S.calling | Shared.awaitHandshake _ _ = case eq of λ ()
  ...   | S.calling | Shared.commitHandshake _ _ = case eq of λ ()
  ...   | S.calling | Shared.countHandshake _ = case eq of λ ()
  ...   | S.calling | Shared.notifyInbound _ = case eq of λ ()
  ...   | S.calling | Shared.returnHandshake _ = case eq of λ ()
  ...   | S.calling | Shared.completedHandshake _ = case eq of λ ()
  ...   | S.calling | Shared.impossibleHandshake = case eq of λ ()
  ...   | S.calling | Shared.closeSocket Shared.hardLimitReached = case eq of λ ()
  ...   | S.closeDisconnected | _ = case eq of λ ()
  ...   | S.closeException _ | _ = case eq of λ ()
  ...   | S.closePrefix _ _ | _ = case eq of λ ()
  ...   | S.bodyExited _ | _ = case eq of λ ()
  ...   | S.resultAvailable _ | _ = case eq of λ ()
  prefix-exception-preserves w err s eq valid | nothing | _ = case eq of λ ()
  prefix-exception-preserves w err s eq valid | just _ | nothing = case eq of λ ()
  exception-preserves : ∀ w err s {t} → S.observeException w err s ≡ just t → Valid (S.source s) → Valid (S.source t)
  exception-preserves w err s eq valid with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
  ... | just worker | just a with S.pc worker | Shared.pc a
  ...   | S.calling | Shared.awaitHandshake _ _ = case just-injective eq of λ { refl → valid }
  ...   | S.calling | Shared.acquireMap = case eq of λ ()
  ...   | S.calling | Shared.count _ = case eq of λ ()
  ...   | S.calling | Shared.prepare _ = case eq of λ ()
  ...   | S.calling | Shared.selectEntry _ _ = case eq of λ ()
  ...   | S.calling | Shared.forkHandler _ _ _ = case eq of λ ()
  ...   | S.calling | Shared.publish _ _ _ = case eq of λ ()
  ...   | S.calling | Shared.reject _ _ = case eq of λ ()
  ...   | S.calling | Shared.closeSocket _ = case eq of λ ()
  ...   | S.calling | Shared.finished _ = case eq of λ ()
  ...   | S.calling | Shared.countPublished _ _ = case eq of λ ()
  ...   | S.calling | Shared.commitHandshake _ _ = case eq of λ ()
  ...   | S.calling | Shared.countHandshake _ = case eq of λ ()
  ...   | S.calling | Shared.notifyInbound _ = case eq of λ ()
  ...   | S.calling | Shared.returnHandshake _ = case eq of λ ()
  ...   | S.calling | Shared.completedHandshake _ = case eq of λ ()
  ...   | S.calling | Shared.impossibleHandshake = case eq of λ ()
  ...   | S.closeDisconnected | _ = case eq of λ ()
  ...   | S.closeException _ | _ = case eq of λ ()
  ...   | S.closePrefix _ _ | _ = case eq of λ ()
  ...   | S.bodyExited _ | _ = case eq of λ ()
  ...   | S.resultAvailable _ | _ = case eq of λ ()
  exception-preserves w err s eq valid | nothing | _ = case eq of λ ()
  exception-preserves w err s eq valid | just _ | nothing = case eq of λ ()
  result-preserves : ∀ w s {t} → S.publishWorkerResult w s ≡ just t → Valid (S.source s) → Valid (S.source t)
  result-preserves w s eq valid with lookup w (S.workers s)
  ... | nothing = case eq of λ ()
  ... | just worker with S.pc worker
  ...   | S.bodyExited r = case just-injective eq of λ { refl → valid }
  ...   | S.calling = case eq of λ ()
  ...   | S.closeDisconnected = case eq of λ ()
  ...   | S.closeException _ = case eq of λ ()
  ...   | S.closePrefix _ _ = case eq of λ ()
  ...   | S.resultAvailable _ = case eq of λ ()

  -- Both successful/uncertain socket observations preserve the source predicate.
  enact-close-preserves : ∀ w worker outcome next s → Valid (S.source s) →
    Valid (S.source (S.enactClose w worker outcome next s))
  enact-close-preserves w worker outcome next s valid =
    socket-preserves (Shared.socketRef (S.request worker)) (S.socketOutcome outcome) (S.source s) valid
  enact-prefix-preserves : ∀ w worker result outcome s {t} → S.enactPrefixClose w worker result outcome s ≡ just t →
    Valid (S.source s) → Valid (S.source t)
  enact-prefix-preserves w worker result nothing s eq valid with N.step
    (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s) in advanced
  ... | nothing = case eq of λ ()
  ... | just n = case just-injective eq of λ { refl → lower-preserves
    (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s) advanced valid }
  enact-prefix-preserves w worker result (just err) s eq valid = case just-injective eq of λ
    { refl → enact-close-preserves w worker (just err) (S.prefixCloseFailed result err) s valid }
  close-prefix-preserves : ∀ w worker failure result outcome s {t} →
    S.closePrefixWorker w worker failure result outcome s ≡ just t → Valid (S.source s) → Valid (S.source t)
  close-prefix-preserves w worker failure result outcome s eq valid with S.prefixMatches w failure s
  ... | false = case eq of λ ()
  ... | true = enact-prefix-preserves w worker result outcome s eq valid
  close-preserves : ∀ w outcome s {t} → S.closeWorker w outcome s ≡ just t → Valid (S.source s) → Valid (S.source t)
  close-preserves w outcome s eq valid with lookup w (S.workers s)
  ... | nothing = case eq of λ ()
  ... | just worker with S.pc worker
  ...   | S.closeDisconnected = case just-injective eq of λ
    { refl → enact-close-preserves w worker outcome (S.nextNormal outcome) s valid }
  ...   | S.closeException err = case just-injective eq of λ
    { refl → enact-close-preserves w worker outcome (S.nextException err outcome) s valid }
  ...   | S.closePrefix f r = close-prefix-preserves w worker f r outcome s eq valid
  ...   | S.calling = case eq of λ ()
  ...   | S.bodyExited _ = case eq of λ ()
  ...   | S.resultAvailable _ = case eq of λ ()

  -- Exhaustive action coverage retains the exact caller-supplied predicate.
  step-preserves : ∀ a s {t} → S.step a s ≡ just t → Valid (S.source s) → Valid (S.source t)
  step-preserves (S.acceptedFork w req) = fork-preserves w req
  step-preserves (S.run a) = inherit-preserves a
  step-preserves (S.workerReturned w) = return-preserves w
  step-preserves (S.workerPrefixReturned w) = prefix-return-preserves w
  step-preserves (S.workerPrefixException w err) = prefix-exception-preserves w err
  step-preserves (S.workerException w err) = exception-preserves w err
  step-preserves (S.workerClose w outcome) = close-preserves w outcome
  step-preserves (S.workerResult w) = result-preserves w
  step-preserves (S.scope a) = scope-preserves a
  exec-preserves : ∀ {s as t} → S.Executes s as t → Valid (S.source s) → Valid (S.source t)
  exec-preserves S.done valid = valid
  exec-preserves (S.next {s = s} {a = a} eq rest) valid = exec-preserves rest (step-preserves a s eq valid)
  from-source : ∀ {c start as t} → S.source start ≡ c → S.Executes start as t → Valid c → Valid (S.source t)
  from-source source-is-c path valid = exec-preserves path (subst Valid (sym source-is-c) valid)
