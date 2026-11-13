{-# OPTIONS --guardedness #-}

-- Exact bitmap observations determine session order under receive-side limits.
open import Data.Nat using (ℕ)
module Cardano_network.Replay.LeiosFetchObservationTransport (k : ℕ) where

open import Data.List using ([]; _∷_; map)
import Data.Bool
open import Cardano_network.Replay.LeiosFetchWords using (canonical)
open import Data.List.Properties using (∷-injective)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Product using (_,_; proj₂ )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import Cardano_network.Replay.LeiosFetchSession
open import Cardano_network.Replay.LeiosFetchObs using (forget; request-fields)
open import Cardano_network.Replay.LeiosFetchWireOK using (WireMsg; WireOK)
open Spec k
open import Semantics.Replay using (module Traces)
open Traces leiosFetch

-- Replace a step's forgotten fields using exact request fields or target receive limits.
step-transport : ∀ {s s′ e} → s -[ e ]→ s′ → (e′ : E) → forget e ≡ forget e′ → WireMsg e′ → s -[ e′ ]→ s′
step-transport (cSendBlockReq lt) (Send , MsgLeiosBlockRequest _ _) refl w = cSendBlockReq lt
step-transport (cSendTxsReq lt valid count cap) (Send , MsgLeiosBlockTxsRequest _ _ _ b) same w
  with request-fields (cong proj₂ same)
... | refl , refl , refl , offsets-eq , valid-eq = cSendTxsReq lt
  (subst Data.Bool.T valid-eq valid)
  (trans count (cong Data.List.length offsets-eq))
  (subst (λ os → Data.Bool.T (canonical os)) offsets-eq cap)
step-transport (cRecvBlock _) (Recv , MsgLeiosBlock _ _) refl cap = cRecvBlock cap
step-transport (cRecvTxs _ _) (Recv , MsgLeiosBlockTxs _ _) refl (cap , bytes) = cRecvTxs cap bytes
step-transport cSendDone (Send , MsgLeiosDone) refl w = cSendDone
step-transport (cDrainBlock _) (Recv , MsgLeiosBlock _ _) refl cap = cDrainBlock cap
step-transport (cDrainTxs _ _) (Recv , MsgLeiosBlockTxs _ _) refl (cap , bytes) = cDrainTxs cap bytes
step-transport cDrainDone (Send , MsgLeiosDone) refl w = cDrainDone
step-transport sRecvBlockReq (Recv , MsgLeiosBlockRequest _ _) refl w = sRecvBlockReq
step-transport (sRecvTxsReq valid count) (Recv , MsgLeiosBlockTxsRequest _ _ _ b) same w
  with request-fields (cong proj₂ same)
... | refl , refl , refl , offsets-eq , valid-eq = sRecvTxsReq
  (subst Data.Bool.T valid-eq valid)
  (trans count (cong Data.List.length offsets-eq))
step-transport sSendBlock (Send , MsgLeiosBlock _ _) refl w = sSendBlock
step-transport sSendTxs (Send , MsgLeiosBlockTxs _ _) refl w = sSendTxs
step-transport sRecvDone (Recv , MsgLeiosDone) refl w = sRecvDone

-- Transport a whole trace without changing its queue or terminal state.
trace-transport : ∀ {s s′ es es′} → s ⇒⟨ es ⟩ s′ → map forget es ≡ map forget es′ → WireOK es′ → s ⇒⟨ es′ ⟩ s′
trace-transport {es′ = []} done eq [] = done
trace-transport {es′ = _ ∷ _} done () w
trace-transport (tau step run) eq w = tau step (trace-transport run eq w)
trace-transport {es′ = []} (vis step run) () []
trace-transport {es′ = e ∷ es} (vis step run) eq (w ∷ ws) with ∷-injective eq
... | same , rest = vis (step-transport step e same w) (trace-transport run rest ws)

-- Acceptance is invariant under exact bitmap observation among wire-admissible logs.
accepted-transport : ∀ {s es es′} → HasTrace s es → map forget es ≡ map forget es′ → WireOK es′ → HasTrace s es′
accepted-transport (s′ , run) eq w = s′ , trace-transport run eq w
