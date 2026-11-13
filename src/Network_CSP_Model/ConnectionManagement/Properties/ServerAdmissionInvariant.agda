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
  body-restore-preserves : ∀ w s {t} → S.restoreWorker w s ≡ just t → Valid (S.source s) → Valid (S.source t)
  body-restore-preserves w s eq valid with lookup w (S.workers s)
  ... | nothing = case eq of λ ()
  ... | just worker with S.pc worker
  ...   | S.closePrefix Shared.bodyFailed (S.raised fault) with N.step (S.runMachine (Machine.admissionStep w Admission.restoreBody)) (S.base s) in actual
  ...     | nothing = case eq of λ ()
  ...     | just n = case just-injective eq of λ { refl → lower-preserves (S.runMachine (Machine.admissionStep w Admission.restoreBody)) (S.base s) actual valid }
  body-restore-preserves w s eq valid | just worker | S.calling = case eq of λ ()
  body-restore-preserves w s eq valid | just worker | S.closeDisconnected = case eq of λ ()
  body-restore-preserves w s eq valid | just worker | S.closeException fault = case eq of λ ()
  body-restore-preserves w s eq valid | just worker | S.closePrefix Shared.hardLimitReached result = case eq of λ ()
  body-restore-preserves w s eq valid | just worker | S.closePrefix Shared.forbidden result = case eq of λ ()
  body-restore-preserves w s eq valid | just worker | S.closePrefix Shared.forkFailed result = case eq of λ ()
  body-restore-preserves w s eq valid | just worker | S.closePrefix Shared.bodyFailed S.returned = case eq of λ ()
  body-restore-preserves w s eq valid | just worker | S.bodyExited result = case eq of λ ()
  body-restore-preserves w s eq valid | just worker | S.resultAvailable result = case eq of λ ()

  enact-scope-preserves : ∀ p s {t} → S.enactScope p s ≡ just t → Valid (S.source s) → Valid (S.source t)
  enact-scope-preserves (S.scopePlan st keep ig action) s eq valid with action
  ... | nothing = case just-injective eq of λ { refl → valid }
  ... | just a with N.step a (S.base s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just n = case just-injective eq of λ { refl → lower-preserves a (S.base s) advanced valid }
  enact-scope-preserves (S.socketScopePlan st keep ig sock owner) s eq valid =
    case just-injective eq of λ { refl → socket-preserves sock owner (S.source s) valid }
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
  ...   | S.calling | Shared.closeSocket Shared.bodyFailed = case eq of λ ()
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
  ...   | S.calling | Shared.closeSocket Shared.bodyFailed = case eq of λ ()
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
  ...   | S.calling | Shared.count _ = case just-injective eq of λ { refl → valid }
  ...   | S.calling | Shared.prepare _ = case just-injective eq of λ { refl → valid }
  ...   | S.calling | Shared.selectEntry _ _ = case just-injective eq of λ { refl → valid }
  ...   | S.calling | Shared.forkHandler _ _ _ = case just-injective eq of λ { refl → valid }
  ...   | S.calling | Shared.publish _ _ _ = case just-injective eq of λ { refl → valid }
  ...   | S.calling | Shared.reject _ _ = case eq of λ ()
  ...   | S.calling | Shared.closeSocket _ = case eq of λ ()
  ...   | S.calling | Shared.finished _ = case eq of λ ()
  ...   | S.calling | Shared.countPublished _ _ = case just-injective eq of λ { refl → valid }
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
  -- The failed bare fork's close changes only the captured socket cell.
  fork-close-preserves : ∀ outcome s {t} → S.closeFailedFork outcome s ≡ just t → Valid (S.source s) → Valid (S.source t)
  fork-close-preserves outcome s eq valid with S.failedForkSocket s
  ... | nothing = case eq of λ ()
  ... | just sock with S.isAcceptedSocket sock s
  ...   | false = case eq of λ ()
  ...   | true = case just-injective eq of λ { refl → socket-preserves sock (S.socketOutcome outcome) (S.source s) valid }
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
  step-preserves (S.closeForkFailure outcome) = fork-close-preserves outcome
  step-preserves (S.acceptedFork w req) = fork-preserves w req
  step-preserves (S.workerRestore w) = body-restore-preserves w
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

-- Historical job captures survive Server actions.
module CaptureIdentity where
  open import ConnectionManagement.Store using (Store)
  import ConnectionManagement.Rules.MuxJobTypes as Types
  import ConnectionManagement.Properties.MuxProtocolJobs as PhysicalFacts
  import ConnectionManagement.Properties.MuxPublicationUnwind as PublicationFacts
  module CIPhysical = PhysicalFacts.CaptureIdentity
  private
    module CIBase = PublicationFacts.CaptureIdentity isBearerClosed
  jobs : N.State → Store JobId Types.ProtocolJob
  jobs n = N.P.jobs (N.R.protocols (N.raw n))
  module From (captured : Store JobId Types.ProtocolJob) where
    ValidN : N.State → Set
    ValidN n = CIPhysical.Retains captured (jobs n)
    Valid : S.State → Set
    Valid s = ValidN (S.base s)
    lower-preserves : ∀ a n {n′} → N.step a n ≡ just n′ → ValidN n → ValidN n′
    lower-preserves a n {n′} eq valid = CIPhysical.compose-retains
      {xs = captured} {ys = jobs n} {zs = jobs n′} valid
      (CIBase.retained-jobs {s = n} {t = n′} (CIBase.step-stable a n eq))
    -- Successful birth writes an admission and socket; physical metadata is separate.
    fork-preserves : ∀ w req s {t} → S.forkAccepted w req s ≡ just t → Valid s → Valid t
    fork-preserves w req s eq valid with S.accepting (S.stage s) | S.listenerOpen s |
      S.sameLimit req (S.workers s) | S.fresh w s | S.fresh (Shared.child req) s |
      w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (S.shared s))
    ... | true | true | true | true | true | no _ | nothing =
      case just-injective eq of λ { refl → valid }
    ... | false | _ | _ | _ | _ | _ | _ = case eq of λ ()
    ... | true | false | _ | _ | _ | _ | _ = case eq of λ ()
    ... | true | true | false | _ | _ | _ | _ = case eq of λ ()
    ... | true | true | true | false | _ | _ | _ = case eq of λ ()
    ... | true | true | true | true | false | _ | _ = case eq of λ ()
    ... | true | true | true | true | true | yes _ | _ = case eq of λ ()
    ... | true | true | true | true | true | no _ | just _ = case eq of λ ()

    -- Guarded delegation and scope plans retain actual lower-step evidence.
    inherit-preserves : ∀ a s {t} → S.inherit a s ≡ just t → Valid s → Valid t
    inherit-preserves a s eq valid with S.allowed a s
    ... | false = case eq of λ ()
    ... | true with N.step a (S.base s) in advanced
    ...   | nothing = case eq of λ ()
    ...   | just n = case just-injective eq of λ { refl → lower-preserves a (S.base s) advanced valid }
    body-restore-preserves : ∀ w s {t} → S.restoreWorker w s ≡ just t → Valid s → Valid t
    body-restore-preserves w s eq valid with lookup w (S.workers s)
    ... | nothing = case eq of λ ()
    ... | just worker with S.pc worker
    ...   | S.closePrefix Shared.bodyFailed (S.raised fault) with N.step (S.runMachine (Machine.admissionStep w Admission.restoreBody)) (S.base s) in actual
    ...     | nothing = case eq of λ ()
    ...     | just n = case just-injective eq of λ { refl → lower-preserves (S.runMachine (Machine.admissionStep w Admission.restoreBody)) (S.base s) actual valid }
    body-restore-preserves w s eq valid | just worker | S.calling = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.closeDisconnected = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.closeException fault = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.closePrefix Shared.hardLimitReached result = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.closePrefix Shared.forbidden result = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.closePrefix Shared.forkFailed result = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.closePrefix Shared.bodyFailed S.returned = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.bodyExited result = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.resultAvailable result = case eq of λ ()

    enact-scope-preserves : ∀ p s {t} → S.enactScope p s ≡ just t → Valid s → Valid t
    enact-scope-preserves (S.scopePlan st keep ig action) s eq valid with action
    ... | nothing = case just-injective eq of λ { refl → valid }
    ... | just a with N.step a (S.base s) in advanced
    ...   | nothing = case eq of λ ()
    ...   | just n = case just-injective eq of λ { refl → lower-preserves a (S.base s) advanced valid }
    enact-scope-preserves (S.socketScopePlan st keep ig sock owner) s eq valid =
      case just-injective eq of λ { refl → valid }
    scope-preserves : ∀ a s {t} → S.scopeAdvance a s ≡ just t → Valid s → Valid t
    scope-preserves a s eq valid with S.chooseScope a s
    ... | nothing = case eq of λ ()
    ... | just p = enact-scope-preserves p s eq valid

    -- Return, exception and result observations change only raw-worker metadata.
    return-preserves : ∀ w s {t} → S.observeReturn w s ≡ just t → Valid s → Valid t
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
    prefix-return-preserves : ∀ w s {t} → S.prefixReturned w s ≡ just t → Valid s → Valid t
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
    ...   | S.calling | Shared.closeSocket Shared.bodyFailed = case eq of λ ()
    ...   | S.calling | Shared.closeSocket Shared.forbidden = case eq of λ ()
    ...   | S.calling | Shared.closeSocket Shared.forkFailed = case eq of λ ()
    ...   | S.closeDisconnected | _ = case eq of λ ()
    ...   | S.closeException _ | _ = case eq of λ ()
    ...   | S.closePrefix _ _ | _ = case eq of λ ()
    ...   | S.bodyExited _ | _ = case eq of λ ()
    ...   | S.resultAvailable _ | _ = case eq of λ ()
    prefix-return-preserves w s eq valid | nothing | _ = case eq of λ ()
    prefix-return-preserves w s eq valid | just _ | nothing = case eq of λ ()
    prefix-exception-preserves : ∀ w err s {t} → S.prefixException w err s ≡ just t → Valid s → Valid t
    prefix-exception-preserves w err s eq valid with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
    ... | just worker | just a with S.pc worker | Shared.pc a
    ...   | S.calling | Shared.closeSocket Shared.bodyFailed = case eq of λ ()
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
    exception-preserves : ∀ w err s {t} → S.observeException w err s ≡ just t → Valid s → Valid t
    exception-preserves w err s eq valid with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
    ... | just worker | just a with S.pc worker | Shared.pc a
    ...   | S.calling | Shared.awaitHandshake _ _ = case just-injective eq of λ { refl → valid }
    ...   | S.calling | Shared.acquireMap = case eq of λ ()
    ...   | S.calling | Shared.count _ = case just-injective eq of λ { refl → valid }
    ...   | S.calling | Shared.prepare _ = case just-injective eq of λ { refl → valid }
    ...   | S.calling | Shared.selectEntry _ _ = case just-injective eq of λ { refl → valid }
    ...   | S.calling | Shared.forkHandler _ _ _ = case just-injective eq of λ { refl → valid }
    ...   | S.calling | Shared.publish _ _ _ = case just-injective eq of λ { refl → valid }
    ...   | S.calling | Shared.reject _ _ = case eq of λ ()
    ...   | S.calling | Shared.closeSocket _ = case eq of λ ()
    ...   | S.calling | Shared.finished _ = case eq of λ ()
    ...   | S.calling | Shared.countPublished _ _ = case just-injective eq of λ { refl → valid }
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
    result-preserves : ∀ w s {t} → S.publishWorkerResult w s ≡ just t → Valid s → Valid t
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
    enact-close-preserves : ∀ w worker outcome next s → Valid s →
      Valid (S.enactClose w worker outcome next s)
    enact-close-preserves w worker outcome next s valid =
      valid
    -- The failed bare fork's close changes only the captured socket cell.
    fork-close-preserves : ∀ outcome s {t} → S.closeFailedFork outcome s ≡ just t → Valid s → Valid t
    fork-close-preserves outcome s eq valid with S.failedForkSocket s
    ... | nothing = case eq of λ ()
    ... | just sock with S.isAcceptedSocket sock s
    ...   | false = case eq of λ ()
    ...   | true = case just-injective eq of λ { refl → valid }
    enact-prefix-preserves : ∀ w worker result outcome s {t} → S.enactPrefixClose w worker result outcome s ≡ just t →
      Valid s → Valid t
    enact-prefix-preserves w worker result nothing s eq valid with N.step
      (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s) in advanced
    ... | nothing = case eq of λ ()
    ... | just n = case just-injective eq of λ { refl → lower-preserves
      (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s) advanced valid }
    enact-prefix-preserves w worker result (just err) s eq valid = case just-injective eq of λ
      { refl → enact-close-preserves w worker (just err) (S.prefixCloseFailed result err) s valid }
    close-prefix-preserves : ∀ w worker failure result outcome s {t} →
      S.closePrefixWorker w worker failure result outcome s ≡ just t → Valid s → Valid t
    close-prefix-preserves w worker failure result outcome s eq valid with S.prefixMatches w failure s
    ... | false = case eq of λ ()
    ... | true = enact-prefix-preserves w worker result outcome s eq valid
    close-preserves : ∀ w outcome s {t} → S.closeWorker w outcome s ≡ just t → Valid s → Valid t
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
    step-preserves : ∀ a s {t} → S.step a s ≡ just t → Valid s → Valid t
    step-preserves (S.closeForkFailure outcome) = fork-close-preserves outcome
    step-preserves (S.acceptedFork w req) = fork-preserves w req
    step-preserves (S.workerRestore w) = body-restore-preserves w
    step-preserves (S.run a) = inherit-preserves a
    step-preserves (S.workerReturned w) = return-preserves w
    step-preserves (S.workerPrefixReturned w) = prefix-return-preserves w
    step-preserves (S.workerPrefixException w err) = prefix-exception-preserves w err
    step-preserves (S.workerException w err) = exception-preserves w err
    step-preserves (S.workerClose w outcome) = close-preserves w outcome
    step-preserves (S.workerResult w) = result-preserves w
    step-preserves (S.scope a) = scope-preserves a
    exec-preserves : ∀ {s as t} → S.Executes s as t → Valid s → Valid t
    exec-preserves S.done valid = valid
    exec-preserves (S.next {s = s} {a = a} eq rest) valid = exec-preserves rest (step-preserves a s eq valid)

  -- The source table itself is the starting witness for each enabled action.
  step-stable : ∀ a s {t} → S.step a s ≡ just t → CIPhysical.Retains (jobs (S.base s)) (jobs (S.base t))
  step-stable a s eq = From.step-preserves (jobs (S.base s)) a s eq (CIPhysical.identity (jobs (S.base s)))

-- Preserve already captured physical results through this adapter.
module CommittedRows where
  open import ConnectionManagement.Store using (Store)
  import ConnectionManagement.Rules.MuxJobTypes as Types
  import ConnectionManagement.Properties.MuxProtocolJobs as PhysicalFacts
  import ConnectionManagement.Properties.MuxPublicationUnwind as PublicationFacts
  module CIPhysical = PhysicalFacts.CommittedRows
  private
    module CIBase = PublicationFacts.CommittedRows isBearerClosed
  jobs : N.State → Store JobId Types.ProtocolJob
  jobs n = N.P.jobs (N.R.protocols (N.raw n))
  module From (captured : Store JobId Types.ProtocolJob) where
    ValidN : N.State → Set
    ValidN n = CIPhysical.Retains captured (jobs n)
    Valid : S.State → Set
    Valid s = ValidN (S.base s)
    lower-preserves : ∀ a n {n′} → N.step a n ≡ just n′ → ValidN n → ValidN n′
    lower-preserves a n {n′} eq valid = CIPhysical.compose-retains
      {xs = captured} {ys = jobs n} {zs = jobs n′} valid
      (CIBase.retained-jobs {s = n} {t = n′} (CIBase.step-stable a n eq))
    -- Successful birth writes an admission and socket; physical metadata is separate.
    fork-preserves : ∀ w req s {t} → S.forkAccepted w req s ≡ just t → Valid s → Valid t
    fork-preserves w req s eq valid with S.accepting (S.stage s) | S.listenerOpen s |
      S.sameLimit req (S.workers s) | S.fresh w s | S.fresh (Shared.child req) s |
      w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (S.shared s))
    ... | true | true | true | true | true | no _ | nothing =
      case just-injective eq of λ { refl → valid }
    ... | false | _ | _ | _ | _ | _ | _ = case eq of λ ()
    ... | true | false | _ | _ | _ | _ | _ = case eq of λ ()
    ... | true | true | false | _ | _ | _ | _ = case eq of λ ()
    ... | true | true | true | false | _ | _ | _ = case eq of λ ()
    ... | true | true | true | true | false | _ | _ = case eq of λ ()
    ... | true | true | true | true | true | yes _ | _ = case eq of λ ()
    ... | true | true | true | true | true | no _ | just _ = case eq of λ ()

    -- Guarded delegation and scope plans retain actual lower-step evidence.
    inherit-preserves : ∀ a s {t} → S.inherit a s ≡ just t → Valid s → Valid t
    inherit-preserves a s eq valid with S.allowed a s
    ... | false = case eq of λ ()
    ... | true with N.step a (S.base s) in advanced
    ...   | nothing = case eq of λ ()
    ...   | just n = case just-injective eq of λ { refl → lower-preserves a (S.base s) advanced valid }
    body-restore-preserves : ∀ w s {t} → S.restoreWorker w s ≡ just t → Valid s → Valid t
    body-restore-preserves w s eq valid with lookup w (S.workers s)
    ... | nothing = case eq of λ ()
    ... | just worker with S.pc worker
    ...   | S.closePrefix Shared.bodyFailed (S.raised fault) with N.step (S.runMachine (Machine.admissionStep w Admission.restoreBody)) (S.base s) in actual
    ...     | nothing = case eq of λ ()
    ...     | just n = case just-injective eq of λ { refl → lower-preserves (S.runMachine (Machine.admissionStep w Admission.restoreBody)) (S.base s) actual valid }
    body-restore-preserves w s eq valid | just worker | S.calling = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.closeDisconnected = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.closeException fault = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.closePrefix Shared.hardLimitReached result = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.closePrefix Shared.forbidden result = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.closePrefix Shared.forkFailed result = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.closePrefix Shared.bodyFailed S.returned = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.bodyExited result = case eq of λ ()
    body-restore-preserves w s eq valid | just worker | S.resultAvailable result = case eq of λ ()

    enact-scope-preserves : ∀ p s {t} → S.enactScope p s ≡ just t → Valid s → Valid t
    enact-scope-preserves (S.scopePlan st keep ig action) s eq valid with action
    ... | nothing = case just-injective eq of λ { refl → valid }
    ... | just a with N.step a (S.base s) in advanced
    ...   | nothing = case eq of λ ()
    ...   | just n = case just-injective eq of λ { refl → lower-preserves a (S.base s) advanced valid }
    enact-scope-preserves (S.socketScopePlan st keep ig sock owner) s eq valid =
      case just-injective eq of λ { refl → valid }
    scope-preserves : ∀ a s {t} → S.scopeAdvance a s ≡ just t → Valid s → Valid t
    scope-preserves a s eq valid with S.chooseScope a s
    ... | nothing = case eq of λ ()
    ... | just p = enact-scope-preserves p s eq valid

    -- Return, exception and result observations change only raw-worker metadata.
    return-preserves : ∀ w s {t} → S.observeReturn w s ≡ just t → Valid s → Valid t
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
    prefix-return-preserves : ∀ w s {t} → S.prefixReturned w s ≡ just t → Valid s → Valid t
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
    ...   | S.calling | Shared.closeSocket Shared.bodyFailed = case eq of λ ()
    ...   | S.calling | Shared.closeSocket Shared.forbidden = case eq of λ ()
    ...   | S.calling | Shared.closeSocket Shared.forkFailed = case eq of λ ()
    ...   | S.closeDisconnected | _ = case eq of λ ()
    ...   | S.closeException _ | _ = case eq of λ ()
    ...   | S.closePrefix _ _ | _ = case eq of λ ()
    ...   | S.bodyExited _ | _ = case eq of λ ()
    ...   | S.resultAvailable _ | _ = case eq of λ ()
    prefix-return-preserves w s eq valid | nothing | _ = case eq of λ ()
    prefix-return-preserves w s eq valid | just _ | nothing = case eq of λ ()
    prefix-exception-preserves : ∀ w err s {t} → S.prefixException w err s ≡ just t → Valid s → Valid t
    prefix-exception-preserves w err s eq valid with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
    ... | just worker | just a with S.pc worker | Shared.pc a
    ...   | S.calling | Shared.closeSocket Shared.bodyFailed = case eq of λ ()
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
    exception-preserves : ∀ w err s {t} → S.observeException w err s ≡ just t → Valid s → Valid t
    exception-preserves w err s eq valid with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
    ... | just worker | just a with S.pc worker | Shared.pc a
    ...   | S.calling | Shared.awaitHandshake _ _ = case just-injective eq of λ { refl → valid }
    ...   | S.calling | Shared.acquireMap = case eq of λ ()
    ...   | S.calling | Shared.count _ = case just-injective eq of λ { refl → valid }
    ...   | S.calling | Shared.prepare _ = case just-injective eq of λ { refl → valid }
    ...   | S.calling | Shared.selectEntry _ _ = case just-injective eq of λ { refl → valid }
    ...   | S.calling | Shared.forkHandler _ _ _ = case just-injective eq of λ { refl → valid }
    ...   | S.calling | Shared.publish _ _ _ = case just-injective eq of λ { refl → valid }
    ...   | S.calling | Shared.reject _ _ = case eq of λ ()
    ...   | S.calling | Shared.closeSocket _ = case eq of λ ()
    ...   | S.calling | Shared.finished _ = case eq of λ ()
    ...   | S.calling | Shared.countPublished _ _ = case just-injective eq of λ { refl → valid }
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
    result-preserves : ∀ w s {t} → S.publishWorkerResult w s ≡ just t → Valid s → Valid t
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
    enact-close-preserves : ∀ w worker outcome next s → Valid s →
      Valid (S.enactClose w worker outcome next s)
    enact-close-preserves w worker outcome next s valid =
      valid
    -- The failed bare fork's close changes only the captured socket cell.
    fork-close-preserves : ∀ outcome s {t} → S.closeFailedFork outcome s ≡ just t → Valid s → Valid t
    fork-close-preserves outcome s eq valid with S.failedForkSocket s
    ... | nothing = case eq of λ ()
    ... | just sock with S.isAcceptedSocket sock s
    ...   | false = case eq of λ ()
    ...   | true = case just-injective eq of λ { refl → valid }
    enact-prefix-preserves : ∀ w worker result outcome s {t} → S.enactPrefixClose w worker result outcome s ≡ just t →
      Valid s → Valid t
    enact-prefix-preserves w worker result nothing s eq valid with N.step
      (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s) in advanced
    ... | nothing = case eq of λ ()
    ... | just n = case just-injective eq of λ { refl → lower-preserves
      (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s) advanced valid }
    enact-prefix-preserves w worker result (just err) s eq valid = case just-injective eq of λ
      { refl → enact-close-preserves w worker (just err) (S.prefixCloseFailed result err) s valid }
    close-prefix-preserves : ∀ w worker failure result outcome s {t} →
      S.closePrefixWorker w worker failure result outcome s ≡ just t → Valid s → Valid t
    close-prefix-preserves w worker failure result outcome s eq valid with S.prefixMatches w failure s
    ... | false = case eq of λ ()
    ... | true = enact-prefix-preserves w worker result outcome s eq valid
    close-preserves : ∀ w outcome s {t} → S.closeWorker w outcome s ≡ just t → Valid s → Valid t
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
    step-preserves : ∀ a s {t} → S.step a s ≡ just t → Valid s → Valid t
    step-preserves (S.closeForkFailure outcome) = fork-close-preserves outcome
    step-preserves (S.acceptedFork w req) = fork-preserves w req
    step-preserves (S.workerRestore w) = body-restore-preserves w
    step-preserves (S.run a) = inherit-preserves a
    step-preserves (S.workerReturned w) = return-preserves w
    step-preserves (S.workerPrefixReturned w) = prefix-return-preserves w
    step-preserves (S.workerPrefixException w err) = prefix-exception-preserves w err
    step-preserves (S.workerException w err) = exception-preserves w err
    step-preserves (S.workerClose w outcome) = close-preserves w outcome
    step-preserves (S.workerResult w) = result-preserves w
    step-preserves (S.scope a) = scope-preserves a
    exec-preserves : ∀ {s as t} → S.Executes s as t → Valid s → Valid t
    exec-preserves S.done valid = valid
    exec-preserves (S.next {s = s} {a = a} eq rest) valid = exec-preserves rest (step-preserves a s eq valid)

  -- The source table itself is the starting witness for each enabled action.
  step-stable : ∀ a s {t} → S.step a s ≡ just t → CIPhysical.Retains (jobs (S.base s)) (jobs (S.base t))
  step-stable a s eq = From.step-preserves (jobs (S.base s)) a s eq (CIPhysical.identity (jobs (S.base s)))
