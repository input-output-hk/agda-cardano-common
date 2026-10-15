{-# OPTIONS --guardedness #-}

-- A source-motivated allocation certificate; not a Haskell refinement theorem.
module ConnectionManagement.Properties.HandlerOrigin where

open import Data.Bool using (true; false)
open import Data.List using (List)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.HandlerResources
open import ConnectionManagement.Properties.HandlerEstablishment using (Prepared; install-prepares)
import ConnectionManagement.Properties.HandlerDispatcherInterference as Dispatcher
import ConnectionManagement.Properties.IGTableRetention as Table
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M

-- The descriptor records the bundle and flow omitted from reference-only Prepared.
record Origin (w : WorkerId) (hid : HandleId) (mid : MuxId)
              (ps : List Protocol) (flow : DataFlow) (c : Configuration) : Set where
  field
    prepared : Prepared w hid mid (world c) (inboundGovernor c)
    descriptor : lookup hid (IG.handles (IG.execution (inboundGovernor c))) ≡
      just (M.handleState mid ps flow)
open Origin public

-- Installation writes the exact descriptor, after both freshness guards pass.
install-descriptor-worker : ∀ hid mid k ps flow ig queue {ig′ queue′} →
  IG.stepWorker (IG.installHandle hid mid k ps flow) ig queue ≡ just (ig′ , queue′) →
  lookup hid (IG.handles (IG.execution ig′)) ≡ just (M.handleState mid ps flow)
install-descriptor-worker hid mid k ps flow ig queue eq
  with lookup hid (IG.handles (IG.execution ig)) | lookup mid (IG.muxes (IG.execution ig)) | IG.ordered ps | IG.supported ps
... | just _ | _ | _ | _ = case eq of λ ()
... | nothing | just _ | _ | _ = case eq of λ ()
... | nothing | nothing | false | _ = case eq of λ ()
... | nothing | nothing | true | false = case eq of λ ()
... | nothing | nothing | true | true with just-injective eq
...   | refl = lookup-put _ _ (IG.handles (IG.execution ig))
install-descriptor-mode : ∀ mode hid mid k ps flow ig queue {ig′ queue′} →
  IG.step mode (IG.installHandle hid mid k ps flow) ig queue ≡ just (ig′ , queue′) →
  lookup hid (IG.handles (IG.execution ig′)) ≡ just (M.handleState mid ps flow)
install-descriptor-mode noResponderMode hid mid k ps flow ig queue ()
install-descriptor-mode responderMode hid mid k ps flow ig queue eq =
  install-descriptor-worker hid mid k ps flow ig queue eq
install-descriptor : ∀ hid mid k ps flow c {c′} →
  advance (igStep (IG.installHandle hid mid k ps flow)) c ≡ just c′ →
  lookup hid (IG.handles (IG.execution (inboundGovernor c′))) ≡ just (M.handleState mid ps flow)
install-descriptor hid mid k ps flow c eq with IG.step (responder c)
  (IG.installHandle hid mid k ps flow) (inboundGovernor c) (inboundInfo (world c)) in stepped
... | nothing = case eq of λ ()
... | just (ig′ , queue′) with just-injective eq
...   | refl = install-descriptor-mode (responder c) hid mid k ps flow
  (inboundGovernor c) (inboundInfo (world c)) stepped

-- The allocation key is the key captured by this handler, not an arbitrary input.
install-origin : ∀ {w} hid mid ps flow c (r : Resources w (world c)) {c′} →
  advance (igStep (IG.installHandle hid mid (handlerKey (original r)) ps flow)) c ≡ just c′ →
  Origin w hid mid ps flow c′
install-origin hid mid ps flow c r eq = record
  { prepared = install-prepares hid mid ps flow c r eq
  ; descriptor = install-descriptor hid mid (handlerKey (original r)) ps flow c eq }

-- Any successful interleaving retains this exact handle value, even if the mux
-- is stopped or the socket closes. The certificate is not a readiness predicate.
origin-step : ∀ a c {c′ w hid mid ps flow} → advance a c ≡ just c′ →
  Origin w hid mid ps flow c → Origin w hid mid ps flow c′
origin-step a c eq o = record
  { prepared = Dispatcher.prepared-step a covered c eq (prepared o)
  ; descriptor = Table.handlesRetained (proj₂ (Dispatcher.step-effects a covered c eq)) _ _ (descriptor o) }
  where
  covered = case Dispatcher.all-actions (a Data.List.∷ Data.List.[]) of λ where
    (Dispatcher.more covered Dispatcher.empty) → covered
origin-exec : ∀ {c as c′ w hid mid ps flow} → Executes c as c′ →
  Origin w hid mid ps flow c → Origin w hid mid ps flow c′
origin-exec done o = o
origin-exec (next {c = c} {a = a} eq path) o = origin-exec path (origin-step a c eq o)
