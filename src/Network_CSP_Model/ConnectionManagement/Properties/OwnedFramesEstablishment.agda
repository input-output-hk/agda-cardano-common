{-# OPTIONS --guardedness #-}

-- The two explicit establishment-return adapters preserve the same caller and
-- separate the logical completion PC from its later physical body return.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesEstablishment
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (UniqueKeys; apart-lookup; lookup-head)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesJobNames as Names
import ConnectionManagement.Properties.OwnedFramesJobFlags as Flags
import ConnectionManagement.Properties.OwnedFramesThreadUpdate as Threads
import ConnectionManagement.Properties.OwnedFramesPoolReturn as BodyReturn
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesLifts as Lifts
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module X = Auxiliary isBearerClosed isIOManagerError
  module N = Names isBearerClosed isIOManagerError
  module F = Flags isBearerClosed isIOManagerError
  module T = Threads isBearerClosed isIOManagerError
  module B = BodyReturn isBearerClosed isIOManagerError
  module D = Cancellation isBearerClosed isIOManagerError
  module L = Lifts isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- The parent selector's exact row is backed by the unique thread-key table.
parent-lookup : ∀ parent rows → UniqueKeys rows → ∀ tid t → PS.byParent parent rows ≡ just (tid , t) → lookup tid rows ≡ just t
parent-lookup parent [] [] tid t ()
parent-lookup parent ((uid , u) ∷ rows) (apart ∷ unique) tid t found with parent ≟ PS.parent u
... | yes same = case just-injective found of λ { refl → lookup-head uid u rows }
... | no other with tid ≟ uid
...   | yes refl = ⊥-elim (case trans (sym (apart-lookup uid rows apart)) (parent-lookup parent rows unique uid t found) of λ ())
...   | no different = parent-lookup parent rows unique tid t found

-- The named logical return updates one non-await job and one parent's mask PC.
establish-target : PS.State → ConnectionManagement.Domain.JobId → Sub.JobFrame → ConnectionManagement.Domain.JobId → PS.Thread → PS.State
establish-target s j jf tid t = record (PS.setMachine (record (PS.machine s)
  { jobs = put j (record jf { execution = record (Sub.execution jf) { pc = J.complete (G.establishedOK (PS.peerRef t)) } }) (Sub.jobs (PS.machine s)) }) s)
  { monitors = put tid (record t { parentPC = PS.returned }) (PS.monitors s) }

-- Caller separation and all existing owners survive the two component writes.
establish-write : ∀ s j jf tid t → lookup j (Sub.jobs (PS.machine s)) ≡ just jf →
  PS.byParent j (PS.monitors s) ≡ just (tid , t) → J.pc (Sub.execution jf) ≡ J.forkMonitor → D.Held s → D.Held (establish-target s j jf tid t)
establish-write s j jf tid t saved parent pc (inv , unique , aux) =
  T.update-inv (PS.cm s) job-context tid t next-thread (PS.monitorPool s) (X.Aux.monitorKeys job-aux) thread-saved refl refl
    (λ uid apart → refl) keep job-inv , unique ,
  T.update-aux job-context tid t next-thread (PS.monitorPool s) thread-saved refl refl (λ uid apart → refl) keep job-aux
  where
  next-job = record jf { execution = record (Sub.execution jf) { pc = J.complete (G.establishedOK (PS.peerRef t)) } }
  next-thread = record t { parentPC = PS.returned }
  job-context = N.job-context (C.capture s) (put j next-job (Sub.jobs (PS.machine s)))
  job-inv = F.change-inv (PS.cm s) (C.capture s) j jf next-job saved refl
    (λ equal → case trans (sym pc) equal of λ ()) (λ equal → case trans (sym pc) equal of λ ()) inv
  job-aux = F.caller-aux (C.capture s) j jf next-job saved refl aux
  thread-saved = parent-lookup j (PS.monitors s) (X.Aux.monitorKeys aux) tid t parent
  keep = T.keep-stable job-context tid t next-thread (PS.monitorPool s) (X.Aux.monitorKeys job-aux) thread-saved refl refl

-- The real adapter requires registration, its original fork PC and running body.
return-establishment : ∀ j s {t} → PS.step (PS.returnEstablishment j) s ≡ just t → D.Held s → D.Held t
return-establishment j s eq held with PS.byParent j (PS.monitors s) in parent | lookup j (Sub.jobs (PS.machine s)) in saved
... | just (tid , t) | just jf with PS.parentPC t | J.pc (Sub.execution jf) in pc | GP.running j (GP.pool (PS.governor s))
...   | PS.registered | J.forkMonitor | true = case just-injective eq of λ { refl → establish-write s j jf tid t saved parent pc held }
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | J.begin | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | J.awaitAcquire | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | (J.startBundle temp ns) | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | (J.publishBundle temp) | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | J.markWarm | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | J.finishActivation | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | J.awaitHot | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | J.awaitAll | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | J.callRelease | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | J.awaitRelease | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | J.delayFailure | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | (J.awaitCold result) | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | (J.complete result) | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | (J.acquirePolicy fault) | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | (J.nodeDelivery fault) | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | (J.nodeRethrow fault) | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.created | pc | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.returned | pc | running = case eq of λ ()
return-establishment j s eq held | just (tid , t) | just jf | PS.registered | J.forkMonitor | false = case eq of λ ()
return-establishment j s eq held | nothing | any = case eq of λ ()
return-establishment j s eq held | just pair | nothing = case eq of λ ()

-- Physical completion is checked only after the job's actual complete PC.
finish-establishment : ∀ j s {t} → PS.step (PS.finishEstablishment j) s ≡ just t → D.Held s → D.Held t
finish-establishment j s eq (inv , unique , aux) with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s)) in saved
... | just pair | just jf with PS.parentPC (proj₂ pair) | J.pc (Sub.execution jf) in pc
...   | PS.returned | J.complete result with GP.Pool.step
  (GP.Pool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) (GP.pool (PS.governor s)) in returned
...     | nothing = case eq of λ ()
...     | just p′ = case just-injective eq of λ { refl →
  B.return-inv (PS.cm s) (C.capture s) j jf p′ (GP.Pool.bodyReturned (GP.body j (J.work (Sub.execution jf)) result)) result saved pc (proj₂ facts) inv , unique ,
  B.return-aux (C.capture s) j p′ (GP.Pool.bodyReturned (GP.body j (J.work (Sub.execution jf)) result)) (proj₁ facts) (proj₂ facts) aux }
  where facts = B.returned-fields j (GP.body j (J.work (Sub.execution jf)) result) (GP.pool (PS.governor s)) returned
finish-establishment j s eq held | just pair | just jf | PS.returned | J.begin = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.awaitAcquire = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | (J.startBundle temp ns) = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | (J.publishBundle temp) = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.markWarm = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.finishActivation = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.awaitHot = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.awaitAll = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.callRelease = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.awaitRelease = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.delayFailure = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | (J.awaitCold result) = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | (J.acquirePolicy fault) = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | (J.nodeDelivery fault) = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | (J.nodeRethrow fault) = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.forkMonitor = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.created | pc = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.registered | pc = case eq of λ ()
finish-establishment j s eq held | nothing | any = case eq of λ ()
finish-establishment j s eq held | just pair | nothing = case eq of λ ()

-- The common lift retains the actual K permissions for both adapters.
k-return-establishment : ∀ j s {t} → K.step (K.peerStep (PS.returnEstablishment j)) s ≡ just t → R.Reach s → R.Reach t
k-return-establishment j = L.peer-lift (PS.returnEstablishment j) (return-establishment j)
k-finish-establishment : ∀ j s {t} → K.step (K.peerStep (PS.finishEstablishment j)) s ≡ just t → R.Reach s → R.Reach t
k-finish-establishment j = L.peer-lift (PS.finishEstablishment j) (finish-establishment j)
