{-# OPTIONS --guardedness #-}

-- Bounded prototype Notify peers, retaining native wire payloads and API handoffs.
-- This is an explicit pipeline extension; it does not replace nodeBundleP peers.
open import Cardano_network.Params using (Params)
module Cardano_network.LeiosNotifyPipe (p : Params) where

open import Data.Nat using (ℕ; suc; _<ᵇ_)
open import Data.Bool using (true)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥-elim)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Unit using (tt)
import Data.Unit.Polymorphic as Poly
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI
open import Process_Trees using (PTree; ExtI; AnyTypes; ContinueType; ret; sil; react)
open import Cardano_network.Base using (Dir; Mode; FromInitiator; FromResponder)
open import Cardano_network.Data p
open import Cardano_network.Net p
open import Cardano_network.LeiosNotifyP p using (LNPEv; sendLNP; receiveLNP; apiLPev; doneLNP; Rr)
open Params p
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as LTS

-- Initiator consumes notifications; responder produces them.
data Peer : Set where
  consumer producer : Peer

-- The credit counter counts requests not yet answered on the wire.
data State : Set where
  openN : ℕ → State
  closed : State

-- Four native notification payloads, without any log-summary encoding.
data Notification : Set where
  announcement : Header → Notification
  offer : EBHash × LSlot → Size → Notification
  txsOffer : EBHash × LSlot → Notification
  votes : List VoteBlob → Notification

-- Preserve the exact protocol message represented by a notification.
message : Notification → MessageLeiosNotifyP
message (announcement h) = MsgLNPBlockAnnouncement h
message (offer pt sz) = MsgLNPBlockOffer pt sz
message (txsOffer pt) = MsgLNPBlockTxsOffer pt
message (votes vs) = MsgLNPVotes vs

-- Client delivery uses the same existing prototype API tags.
tag : Notification → ApiLPTag
tag (announcement _) = lnpRecvBlockAnnouncement
tag (offer _ _) = lnpRecvBlockOffer
tag (txsOffer _) = lnpRecvBlockTxsOffer
tag (votes _) = lnpRecvVotes

-- Each delivery forwards the native payload unchanged to its API carrier.
value : (m : Notification) → ApiLPCar (tag m)
value (announcement h) = h
value (offer pt sz) = pt , sz
value (txsOffer pt) = pt
value (votes vs) = vs

-- The exact output equality is explicit for each dependent delivery carrier.
deliveryEq : (m : Notification) → DecEq (ApiLPCar (tag m))
deliveryEq (announcement _) = DecEq-Header
deliveryEq (offer _ _) = DecEq-Offer
deliveryEq (txsOffer _) = DecEq-EBPoint
deliveryEq (votes _) = DecEqI.DecEq-List

-- Pending outputs and deliveries block the next menu until the handoff completes.
data Phase : Set where
  head loopBack : State → Phase
  sending : Mode → MessageLeiosNotifyP → State → Phase
  delivering : Notification → State → Phase
  doneNotice : Phase

-- The loop preserves the native alphabet and return type.
Proc : Set₁
Proc = PTree LNPEv (ExtI LNPEv) Rr

-- A fixed endpoint and depth determine the actual protocol menus.
module Machine (k : ℕ) (l : Link) (d : Dir) where
  -- The exact native payload emitted after an application command.
  packet : Mode → MessageLeiosNotifyP → Payload
  packet md m = time₀ , md , length₀ , leiosNotifyP m

  -- Independent step rules describe API selection, wire agency and delivery.
  data Step : Peer → Phase → LTS.Event → Phase → Set₁ where
    cRequest : ∀ {n} → (n <ᵇ k) ≡ true →
      Step consumer (head (openN n)) (LTS.evLabel _ (apiLPev l d lnpSendRequestNext) tt)
        (sending FromInitiator MsgLNPRequestNext (openN (suc n)))
    cDone : Step consumer (head (openN 0)) (LTS.evLabel _ (apiLPev l d lnpSendDone) tt)
      (sending FromInitiator MsgLNPDone closed)
    cNotification : ∀ {n t md len} (m : Notification) →
      Step consumer (head (openN (suc n)))
        (LTS.evLabel _ (receiveLNP l d) (t , md , len , leiosNotifyP (message m)))
        (delivering m (openN n))
    sRequest : ∀ {n t md len} → (n <ᵇ k) ≡ true →
      Step producer (head (openN n))
        (LTS.evLabel _ (receiveLNP l d) (t , md , len , leiosNotifyP MsgLNPRequestNext))
        (loopBack (openN (suc n)))
    sDone : ∀ {t md len} → Step producer (head (openN 0))
      (LTS.evLabel _ (receiveLNP l d) (t , md , len , leiosNotifyP MsgLNPDone)) doneNotice
    sAnnouncement : ∀ {n h} → Step producer (head (openN (suc n)))
      (LTS.evLabel _ (apiLPev l d lnpSendBlockAnnouncement) h)
      (sending FromResponder (message (announcement h)) (openN n))
    sOffer : ∀ {n pt sz} → Step producer (head (openN (suc n)))
      (LTS.evLabel _ (apiLPev l d lnpSendBlockOffer) (pt , sz))
      (sending FromResponder (message (offer pt sz)) (openN n))
    sTxsOffer : ∀ {n pt} → Step producer (head (openN (suc n)))
      (LTS.evLabel _ (apiLPev l d lnpSendBlockTxsOffer) pt)
      (sending FromResponder (message (txsOffer pt)) (openN n))
    sVotes : ∀ {n vs} → Step producer (head (openN (suc n)))
      (LTS.evLabel _ (apiLPev l d lnpSendVotes) vs)
      (sending FromResponder (message (votes vs)) (openN n))
    sent : ∀ {r md m s} → Step r (sending md m s)
      (LTS.evLabel _ (sendLNP l d) (packet md m)) (loopBack s)
    delivered : ∀ {r m s} → Step r (delivering m s)
      (LTS.evLabel _ (apiLPev l d (tag m)) (value m)) (loopBack s)
    noticed : ∀ {r} → Step r doneNotice (LTS.evLabel _ (doneLNP l d) tt) (loopBack closed)

  -- Only returning to the next menu is silent, as in the original iter peers.
  data Tau : Phase → Phase → Set where
    back : ∀ {s} → Tau (loopBack s) (head s)

  -- A guarded successful choice carries its independent transition evidence.
  checked : ∀ {r s e t} {P : Set} → Dec P → (P → Step r s e t) → Maybe (Σ[ u ∈ Phase ] Step r s e u)
  checked {t = t} (yes p) f = just (t , f p)
  checked (no _) _ = nothing

  -- Successful guards list the requested target regardless of proof identity.
  checked-target : ∀ {r s e t} {P : Set} (dec : Dec P) {f : P → Step r s e t} → P →
    map proj₁ (checked dec f) ≡ just t
  checked-target (yes _) _ = refl
  checked-target (no np) p = ⊥-elim (np p)

  -- Lookup preserves all offered native payloads and checks the selected endpoint.
  select : (r : Peer) (s : Phase) (e : LTS.Event) → Maybe (Σ[ u ∈ Phase ] Step r s e u)
  select r (sending md m s) (LTS.evLabel _ (sendLNP l′ d′) a) =
    checked {t = loopBack s} ((l′ ≟ l) ×-dec ((d′ ≟ d) ×-dec (a ≟ packet md m)))
      λ { (refl , refl , refl) → sent }
  select r (delivering m s) (LTS.evLabel _ (apiLPev l′ d′ t) a)
    with t ≟ tag m
  ... | no _ = nothing
  ... | yes refl = checked ((l′ ≟ l) ×-dec ((d′ ≟ d) ×-dec (_≟_ ⦃ deliveryEq m ⦄ a (value m))))
    λ { (refl , refl , refl) → delivered }
  select r doneNotice (LTS.evLabel _ (doneLNP l′ d′) _) =
    checked ((l′ ≟ l) ×-dec (d′ ≟ d)) λ { (refl , refl) → noticed }
  select consumer (head (openN n)) (LTS.evLabel _ (apiLPev l′ d′ lnpSendRequestNext) _) =
    checked ((l′ ≟ l) ×-dec ((d′ ≟ d) ×-dec ((n <ᵇ k) Bool.≟ true)))
      λ { (refl , refl , credit) → cRequest credit }
  select consumer (head (openN 0)) (LTS.evLabel _ (apiLPev l′ d′ lnpSendDone) _) =
    checked ((l′ ≟ l) ×-dec (d′ ≟ d)) λ { (refl , refl) → cDone }
  select consumer (head (openN (suc n)))
    (LTS.evLabel _ (receiveLNP l′ d′) (t , md , len , leiosNotifyP (MsgLNPBlockAnnouncement h))) =
    checked ((l′ ≟ l) ×-dec (d′ ≟ d)) λ { (refl , refl) → cNotification (announcement h) }
  select consumer (head (openN (suc n)))
    (LTS.evLabel _ (receiveLNP l′ d′) (t , md , len , leiosNotifyP (MsgLNPBlockOffer pt sz))) =
    checked ((l′ ≟ l) ×-dec (d′ ≟ d)) λ { (refl , refl) → cNotification (offer pt sz) }
  select consumer (head (openN (suc n)))
    (LTS.evLabel _ (receiveLNP l′ d′) (t , md , len , leiosNotifyP (MsgLNPBlockTxsOffer pt))) =
    checked ((l′ ≟ l) ×-dec (d′ ≟ d)) λ { (refl , refl) → cNotification (txsOffer pt) }
  select consumer (head (openN (suc n)))
    (LTS.evLabel _ (receiveLNP l′ d′) (t , md , len , leiosNotifyP (MsgLNPVotes vs))) =
    checked ((l′ ≟ l) ×-dec (d′ ≟ d)) λ { (refl , refl) → cNotification (votes vs) }
  select producer (head (openN n))
    (LTS.evLabel _ (receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP MsgLNPRequestNext)) =
    checked ((l′ ≟ l) ×-dec ((d′ ≟ d) ×-dec ((n <ᵇ k) Bool.≟ true)))
      λ { (refl , refl , credit) → sRequest credit }
  select producer (head (openN 0))
    (LTS.evLabel _ (receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP MsgLNPDone)) =
    checked ((l′ ≟ l) ×-dec (d′ ≟ d)) λ { (refl , refl) → sDone }
  select producer (head (openN (suc n))) (LTS.evLabel _ (apiLPev l′ d′ lnpSendBlockAnnouncement) h) =
    checked ((l′ ≟ l) ×-dec (d′ ≟ d)) λ { (refl , refl) → sAnnouncement }
  select producer (head (openN (suc n))) (LTS.evLabel _ (apiLPev l′ d′ lnpSendBlockOffer) (pt , sz)) =
    checked ((l′ ≟ l) ×-dec (d′ ≟ d)) λ { (refl , refl) → sOffer }
  select producer (head (openN (suc n))) (LTS.evLabel _ (apiLPev l′ d′ lnpSendBlockTxsOffer) pt) =
    checked ((l′ ≟ l) ×-dec (d′ ≟ d)) λ { (refl , refl) → sTxsOffer }
  select producer (head (openN (suc n))) (LTS.evLabel _ (apiLPev l′ d′ lnpSendVotes) vs) =
    checked ((l′ ≟ l) ×-dec (d′ ≟ d)) λ { (refl , refl) → sVotes }
  select _ _ _ = nothing

  -- Erase only the carried proof to obtain the exact executable target lookup.
  next : Peer → Phase → LTS.Event → Maybe Phase
  next r s e = map proj₁ (select r s e)

  -- Forward declarations put every recursive continuation beneath the PTree guard.
  tree : Peer → Phase → Proc
  offers : Peer → Phase → (at : AnyTypes LNPEv) → ContinueType at (Maybe Proc)

  -- A completed peer returns; loop-back is the original explicit silent action.
  PTree.force (tree r (head closed)) = ret Poly.tt
  PTree.force (tree r (loopBack s)) = sil (tree r (head s))
  PTree.force (tree r s@(head (openN _))) = react (offers r s) (λ _ _ → nothing)
  PTree.force (tree r s@(sending _ _ _)) = react (offers r s) (λ _ _ → nothing)
  PTree.force (tree r s@(delivering _ _)) = react (offers r s) (λ _ _ → nothing)
  PTree.force (tree r doneNotice) = react (offers r doneNotice) (λ _ _ → nothing)

  -- A visible continuation is offered exactly when its certified phase update succeeds.
  offers r s (X , ch) a with next r s (LTS.evLabel X ch a)
  ... | nothing = nothing
  ... | just t = just (tree r t)

-- Fresh consumer starts with no unanswered requests.
client : ℕ → Link → Dir → Proc
client k l d = Machine.tree k l d consumer (head (openN 0))

-- Fresh producer uses the same bound on its outstanding request credits.
server : ℕ → Link → Dir → Proc
server k l d = Machine.tree k l d producer (head (openN 0))
