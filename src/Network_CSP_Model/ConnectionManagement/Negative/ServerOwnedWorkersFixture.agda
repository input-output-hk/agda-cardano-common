{-# OPTIONS --guardedness #-}

-- The exact refused beginCM edge of Negative/ServerLateAdmission's prefix.
-- Its Server state is the original witness's actual pre-CM state. The result
-- holds for every surrounding IG-exit/context value, so no invented outer
-- initialization or fabricated exit state is needed for this local refusal.
module ConnectionManagement.Negative.ServerOwnedWorkersFixture where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Negative.ServerAdmission using (atAfterIG)
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.Variants.ServerOwnedWorkers as Variant
open Variant I.bearerClosed Prior.classify using
  (module S; module E; module K; State; state; step′; allJoined)
private module C = Context Prior.classify

-- Embed only the original pre-CM Server state, with arbitrary surrounding data.
before : E.Exit → C.Context → K.State
before e k = K.combined (E.igExitState (atAfterIG S.igJoined) e) k
after : E.Exit → C.Context → K.State
after e k = record (before e k) { server = E.igExitState
  (record (atAfterIG S.igJoined) { stage = S.closingCM }) e }

-- The source edge succeeds at every embedding; the ownership guard refuses it.
source-beginCM : ∀ e k → K.step (K.serverStep (E.run (S.scope S.beginCM))) (before e k) ≡ just (after e k)
source-beginCM e k = refl
not-joined : allJoined ((A.w₀ , false) ∷ (A.w₁ , false) ∷ []) ≡ false
not-joined = refl
late-beginCM-refused : ∀ e k → step′ (K.serverStep (E.run (S.scope S.beginCM)))
  (state (before e k) ((A.w₀ , false) ∷ (A.w₁ , false) ∷ [])) ≡ nothing
late-beginCM-refused e k = refl

-- Even granting worker zero a join cannot bypass worker one's retained handle.
worker-one-still-blocks : ∀ e k → step′ (K.serverStep (E.run (S.scope S.beginCM)))
  (state (before e k) ((A.w₀ , true) ∷ (A.w₁ , false) ∷ [])) ≡ nothing
worker-one-still-blocks e k = refl
