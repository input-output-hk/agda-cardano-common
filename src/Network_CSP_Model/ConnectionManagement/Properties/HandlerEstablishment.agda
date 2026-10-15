{-# OPTIONS --guardedness #-}

-- Matched installation and publication establish a chain before attachment.
-- This constrains boundary inputs, not the executable machine's allowed actions.
module ConnectionManagement.Properties.HandlerEstablishment where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (Present; lookup-put)
open import ConnectionManagement.Properties.HandlerResources
open import ConnectionManagement.Properties.HandlerReferences using (Chain; TrackedChain)
open import ConnectionManagement.Properties.HandlerAttachment using (CreationPremises; advance-creates)
open import ConnectionManagement.Properties.HandlerManagement using (all-exec-preserves)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.Handshake as H

-- Installation yields the mutable lookups; no promise result is assumed here.
record Prepared (w : WorkerId) (hid : HandleId) (mid : MuxId) (s : State) (ig : IG.Runtime) : Set where
  field
    resources : Resources w s
    hd : M.Handle
    mx : M.Mux
    handleFound : lookup hid (IG.handles (IG.execution ig)) ≡ just hd
    handleMux : M.muxRef hd ≡ mid
    muxFound : lookup mid (IG.muxes (IG.execution ig)) ≡ just mx
    keyMatches : M.key mx ≡ handlerKey (original resources)
open Prepared public

install-worker : ∀ {w} hid mid ps flow ig queue s (r : Resources w s) {ig′ queue′} →
  IG.stepWorker (IG.installHandle hid mid (handlerKey (original r)) ps flow) ig queue ≡ just (ig′ , queue′) →
  Prepared w hid mid (record s { inboundInfo = queue′ }) ig′
install-worker hid mid ps flow ig queue s r eq
  with lookup hid (IG.handles (IG.execution ig)) | lookup mid (IG.muxes (IG.execution ig)) | IG.ordered ps | IG.supported ps
... | just _ | _ | _ | _ = case eq of λ ()
... | nothing | just _ | _ | _ = case eq of λ ()
... | nothing | nothing | false | _ = case eq of λ ()
... | nothing | nothing | true | false = case eq of λ ()
... | nothing | nothing | true | true with just-injective eq
...   | refl = record
  { resources = queue-resources queue r; hd = _; mx = _
  ; handleFound = lookup-put _ _ (IG.handles (IG.execution ig)); handleMux = refl
  ; muxFound = lookup-put _ _ (IG.muxes (IG.execution ig)); keyMatches = refl }

install-mode : ∀ mode {w} hid mid ps flow ig queue s (r : Resources w s) {ig′ queue′} →
  IG.step mode (IG.installHandle hid mid (handlerKey (original r)) ps flow) ig queue ≡ just (ig′ , queue′) →
  Prepared w hid mid (record s { inboundInfo = queue′ }) ig′
install-mode noResponderMode hid mid ps flow ig queue s r ()
install-mode responderMode hid mid ps flow ig queue s r eq = install-worker hid mid ps flow ig queue s r eq

install-prepares : ∀ {w} hid mid ps flow c (r : Resources w (world c)) {c′} →
  advance (igStep (IG.installHandle hid mid (handlerKey (original r)) ps flow)) c ≡ just c′ →
  Prepared w hid mid (world c′) (inboundGovernor c′)
install-prepares hid mid ps flow c r eq with IG.step (responder c)
  (IG.installHandle hid mid (handlerKey (original r)) ps flow)
  (inboundGovernor c) (inboundInfo (world c)) in stepped
... | nothing = case eq of λ ()
... | just (ig′ , queue′) with just-injective eq
...   | refl = install-mode (responder c) hid mid ps flow (inboundGovernor c) (inboundInfo (world c)) (world c) r stepped

-- Publication supplies the final lookup. The published handle must be the one
-- in Prepared; this is not checked by the abstract publication boundary itself.
publish-worker : ∀ w hid mid flow s ig (prepared : Prepared w hid mid s ig) {s′} →
  H.publishBoundary w (negotiated hid flow) s ≡ just (H.published s′) → Chain w mid s′ ig
publish-worker w hid mid flow s ig prepared eq rewrite found (resources prepared)
  with lookup w (cleanups s)
... | just _ = case eq of λ ()
... | nothing with any (λ p → does (p ≟ handlerPromise (original (resources prepared)))) (promises s)
...   | false = case eq of λ ()
...   | true with lookup (handlerPromise (original (resources prepared))) (handshakeResults s)
...     | just _ = case eq of λ ()
...     | nothing with just-injective eq
...       | refl = record
  { originalHandler = original (resources prepared); publishedHandle = hid; negotiatedFlow = flow
  ; handleValue = hd prepared; muxValue = mx prepared
  ; handlerFound = found (resources prepared); promiseFound = lookup-put _ _ (handshakeResults s)
  ; handleFound = handleFound prepared; handleMux = handleMux prepared
  ; muxFound = muxFound prepared; keyMatches = keyMatches prepared
  ; entryPresent = entryExists (resources prepared); socketPresent = socketExists (resources prepared) }

publication-creates : ∀ w hid mid flow c {c′} → Prepared w hid mid (world c) (inboundGovernor c) →
  advance (handlerPublication w (negotiated hid flow) resultWritten) c ≡ just c′ →
  Chain w mid (world c′) (inboundGovernor c′)
publication-creates w hid mid flow c prepared eq with any (λ v → does (v ≟ w)) (publicationFaults c)
... | true = case eq of λ ()
... | false with H.publishBoundary w (negotiated hid flow) (world c) in published
...   | nothing = case eq of λ ()
...   | just H.writerBlocked = case eq of λ ()
...   | just (H.published s′) with just-injective eq
...     | refl = publish-worker w hid mid flow (world c) (inboundGovernor c) prepared published

-- Functional lookups identify every queried value with the established chain.
chain-premises : ∀ {w mid s ig} → Chain w mid s ig → CreationPremises w s ig
chain-premises {w} {mid} {s} {ig} ch = record { resources = resourceProof; coherent = coherenceProof }
  where
  open Chain ch
  resourceProof : ∀ h → lookup w (handlers s) ≡ just h →
    Present (handlerEntry h) (entries (cm s)) × Present (handlerSocket h) (sockets s)
  resourceProof h eq with just-injective (trans (sym handlerFound) eq)
  ... | refl = entryPresent , socketPresent
  coherenceProof : ∀ h hid flow hd′ m → lookup w (handlers s) ≡ just h →
    lookup (handlerPromise h) (handshakeResults s) ≡ just (negotiated hid flow) →
    lookup hid (IG.handles (IG.execution ig)) ≡ just hd′ →
    lookup (M.muxRef hd′) (IG.muxes (IG.execution ig)) ≡ just m →
    M.key m ≡ handlerKey h
  coherenceProof h hid flow hd′ m hEq pEq hdEq mEq
    with just-injective (trans (sym handlerFound) hEq)
  ... | refl with just-injective (trans (sym promiseFound) pEq)
  ...   | refl with just-injective (trans (sym (Chain.handleFound ch)) hdEq)
  ...     | refl rewrite Chain.handleMux ch with just-injective (trans (sym (Chain.muxFound ch)) mEq)
  ...       | refl = Chain.keyMatches ch

-- Once attachment succeeds, the all-dispatcher theorem covers every suffix.
attach-established : ∀ w err c {mid c′} → Chain w mid (world c) (inboundGovernor c) →
  advance (handlerStep w (L.attach err)) c ≡ just c′ → TrackedChain w c′
attach-established w err c ch = advance-creates w err c (chain-premises ch)
