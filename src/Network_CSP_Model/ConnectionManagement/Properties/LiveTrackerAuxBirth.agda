{-# OPTIONS --guardedness #-}

-- Direct frontend birth uses a saved call rather than P.initiatorFork. This
-- writer preserves the joint core invariant given the call's published owner.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxBirth (b : ErrorId → Bool) where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (WorkerId; JobId; RunId; MuxId)
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Properties.MuxProtocolJobs as Jobs
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Properties.LiveTrackerAuxContent as Content
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Transport
import ConnectionManagement.Properties.LiveTrackerAuxUpdates as Updates
module A = Content b
module T = Transport b
module Up = Updates b
module U = P.U
module Pool = P.Pool

-- The saved mux reference is related to an actual owner, not inferred from a
-- default startupAt/frameAt value. All older payloads are retargeted as well.
core-birth : ∀ w f pool j gen dir n mid s →
 lookup w (U.frames (P.base s)) ≡ just f →
 lookup j (P.jobs s) ≡ nothing →
 Pool.step (Pool.fork j) (P.poolAt w s) ≡ just pool →
 (own : A.Owner w s) → A.Owner.mux own ≡ mid → Up.Valid s →
 Up.Valid (record (P.setPool w f pool s)
   { jobs = put j (Types.protocolJob w mid dir n gen Types.executing) (P.jobs s) })
core-birth w f pool j gen dir n mid s found fresh actual own matches valid =
 Up.job-valid j job middle freshKept (T.job-kept freshKept j job newGood)
   (Up.pool-valid w f (Pool.fork j) s found actual tt valid)
 where
 job = Types.protocolJob w mid dir n gen Types.executing
 middle = P.setPool w f pool s
 poolKept = Up.pool-retains w f pool s found (Up.Kernel.handles-retained (Pool.fork j) (P.poolAt w s) actual)
 keptOwner = T.Retains.owners poolKept w own
 freshKept = Up.fresh-job j job middle fresh
 newGood : A.JobContent j job middle
 newGood = A.job-content (proj₁ keptOwner)
   (trans (T.OwnerKept.same-mux (proj₂ keptOwner)) matches) Pool.bodyRunning
   (trans (cong (λ p → lookup j (Pool.handles p)) (Jobs.pool-same w f pool s)) (A.fork-handle j (P.poolAt w s) actual))

import ConnectionManagement.ServerPeers as Frontend
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe.Properties using (just-injective)
open import Data.Bool using (true; false)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (HandleId)
open import ConnectionManagement.IGTypes using (number)

module Front (io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 private module F = Frontend.Protocols b io capability using (Runtime; Call; calls; front; owner; mux; physical; base; forkPlan; enact; birth; Plan; cursor; controllerFree; forkReadyC; idleC; selectedC; tracingC; registeringC; failedC; thread; value; descriptor)
 CallOwner : F.Call → P.State → Set
 CallOwner saved s = Σ (A.Owner (F.owner saved) s) (λ own → A.Owner.mux own ≡ F.mux saved)
 Calls : F.Runtime → Set
 Calls s = All (λ { (rid , saved) → CallOwner saved (F.physical (F.base s)) }) (F.calls (F.front s))
 -- Selection uses the saved call's owner certificate. Establishing Calls for
 -- every frontend history remains a separate invariant, not a hidden premise.
 fork-preserves : ∀ w j s {plan} → F.forkPlan w j s ≡ just plan → Calls s →
   Up.Valid (F.physical (F.base s)) → ∀ {t} → F.enact plan s ≡ just t → Up.Valid (F.physical (F.base t))
 fork-preserves w j s selected calls valid enacted with F.cursor w (F.front s) | F.controllerFree w (F.base s) |
   lookup w (U.frames (P.base (F.physical (F.base s)))) in found
 ... | F.forkReadyC gen | true | just f with lookup gen (F.calls (F.front s)) in callFound |
   P.fresh j gen (F.physical (F.base s)) in fresh | P.noParent (P.poolAt w (F.physical (F.base s)))
 ...   | just saved | true | true with F.owner saved ≟ w | F.thread saved | F.value saved |
   Pool.step (Pool.fork j) (P.poolAt w (F.physical (F.base s))) in actual
 ...     | yes refl | nothing | nothing | just pool = case just-injective selected of λ { refl →
   case just-injective enacted of λ { refl → core-birth w f pool j gen Mux.initiatorJob (number (F.descriptor saved)) (F.mux saved)
     (F.physical (F.base s)) found (Jobs.CaptureIdentity.fresh-lookup j gen (F.physical (F.base s)) fresh) actual (proj₁ backing) (proj₂ backing) valid } }
   where backing = T.Rows.at (λ gen saved → CallOwner saved (F.physical (F.base s))) (F.calls (F.front s)) calls gen saved callFound
 ...     | no _ | _ | _ | _ = case selected of λ ()
 ...     | yes _ | just _ | _ | _ = case selected of λ ()
 ...     | yes _ | nothing | just _ | _ = case selected of λ ()
 ...     | yes _ | nothing | nothing | nothing = case selected of λ ()
 fork-preserves w j s selected calls valid enacted | F.forkReadyC gen | true | just f | nothing | _ | _ = case selected of λ ()
 fork-preserves w j s selected calls valid enacted | F.forkReadyC gen | true | just f | just saved | false | _ = case selected of λ ()
 fork-preserves w j s selected calls valid enacted | F.forkReadyC gen | true | just f | just saved | true | false = case selected of λ ()
 fork-preserves w j s selected calls valid enacted | F.idleC | _ | _ = case selected of λ ()
 fork-preserves w j s selected calls valid enacted | F.selectedC gen | _ | _ = case selected of λ ()
 fork-preserves w j s selected calls valid enacted | F.tracingC gen | _ | _ = case selected of λ ()
 fork-preserves w j s selected calls valid enacted | F.registeringC gen target | _ | _ = case selected of λ ()
 fork-preserves w j s selected calls valid enacted | F.failedC gen result | _ | _ = case selected of λ ()
 fork-preserves w j s selected calls valid enacted | F.forkReadyC gen | false | _ = case selected of λ ()
 fork-preserves w j s selected calls valid enacted | F.forkReadyC gen | true | nothing = case selected of λ ()
