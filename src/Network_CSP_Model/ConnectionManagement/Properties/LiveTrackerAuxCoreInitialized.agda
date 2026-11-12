{-# OPTIONS --guardedness #-}

-- Initialized typed protocol endpoint for the mutually supporting job/pool
-- invariant. This is a component, not the full ServerPeers frontend endpoint.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxCoreInitialized (b : ErrorId → Bool) where
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import ConnectionManagement.Properties.Stores using (UniqueKeys)
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Properties.MuxHandlerSupervision as MuxFacts
import ConnectionManagement.Properties.LiveTrackerAuxUpdates as Updates
import ConnectionManagement.Properties.LiveTrackerAuxContent as Content
module A = Content b
import ConnectionManagement.Properties.LiveTrackerAuxProtocol as Protocol
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Transport
module Up = Updates b
module T = Transport b
module U = P.U
module MF = MuxFacts Types.TypedResult

-- The actual mux initializer adopts no frame rows.
initial-frames : ∀ c {u} → U.initial c ≡ just u → U.frames u ≡ []
initial-frames c eq with IG.handles (IG.execution (M.inboundGovernor (O.core c))) |
 IG.muxes (IG.execution (M.inboundGovernor (O.core c))) | B.initial c
... | [] | [] | just lower = case just-injective eq of λ { refl → refl }
... | _ ∷ _ | _ | _ = case eq of λ ()
... | [] | _ ∷ _ | _ = case eq of λ ()
... | [] | [] | nothing = case eq of λ ()
initialized-valid : ∀ c {s} → P.initial c ≡ just s → Up.Valid s
initialized-valid c eq with U.initial c in actual
... | nothing = case eq of λ ()
... | just u = case just-injective eq of λ { refl → record
 { unique = subst UniqueKeys (sym (initial-frames c actual)) []
 ; frames = subst (All (λ { (w , f) → Up.Early f })) (sym (initial-frames c actual)) []
 ; jobs = []
 ; pools = λ w → Up.as-pool w (P.protocolState u [] [])
     (subst (Up.Kernel.Content (λ value → A.Completion w value (P.protocolState u [] [])))
       (sym (cong P.Startup.pool (MF.initial-startup c actual w))) (Up.Kernel.initial _)) } }

-- Every enabled writer preserves both core content and arbitrary old observers.
effect : ∀ a s {t} → P.step a s ≡ just t → Up.Valid s → T.Retains s t Data.Product.× Up.Valid t
effect a s actual valid with Protocol.For.step-preserves b (T.Retains s) (λ kept old → T.compose old kept)
 a s actual (valid , T.identity s)
... | next , retained = retained , next
step-preserves : ∀ a s {t} → P.step a s ≡ just t → Up.Valid s → Up.Valid t
step-preserves a s actual valid = proj₂ (effect a s actual valid)
run-preserves : ∀ {s actions t} → P.Executes s actions t → Up.Valid s → Up.Valid t
run-preserves P.done valid = valid
run-preserves (P.next {s = s} {a = a} actual path) valid = run-preserves path (step-preserves a s actual valid)
from-initial : ∀ c {start actions s} → P.initial c ≡ just start → P.Executes start actions s → Up.Valid s
from-initial c initialized path = run-preserves path (initialized-valid c initialized)

import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.Properties.LiveTrackerAuxMonitor as MonitorFacts
module MonitorEndpoint where
 private module W = MonitorModel b
 private module F = MonitorFacts b
 -- Includes every stored PC row, rather than only the default pcAt view.
 Valid : W.State → Set
 Valid s = Up.Valid (W.base s) Data.Product.× F.PCs (W.pcs s) (W.base s)
 monitor-step-preserves : ∀ a s {t} → W.step a s ≡ just t → Valid s → Valid t
 monitor-step-preserves a s actual (core , pcs) with F.For.step-preserves (λ _ → ⊤) (λ kept unit → unit) a s actual (core , pcs , tt)
 ... | next , covered , unit = next , covered
 monitor-run-preserves : ∀ {s actions t} → W.Executes s actions t → Valid s → Valid t
 monitor-run-preserves W.done valid = valid
 monitor-run-preserves (W.next {s = s} {a = a} actual path) valid = monitor-run-preserves path (monitor-step-preserves a s actual valid)
 monitor-initialized-valid : ∀ c {s} → W.initial c ≡ just s → Valid s
 monitor-initialized-valid c eq with P.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → initialized-valid c actual , [] }
 monitor-from-initial : ∀ c {start actions s} → W.initial c ≡ just start → W.Executes start actions s → Valid s
 monitor-from-initial c initialized path = monitor-run-preserves path (monitor-initialized-valid c initialized)
