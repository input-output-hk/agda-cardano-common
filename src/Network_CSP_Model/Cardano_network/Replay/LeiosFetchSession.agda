{-# OPTIONS --safe #-}

-- First-order session spec for ONE LeiosFetch session as seen in a node's
-- log (trace-replay Phase 3, amendments A1, A2, A8, A9), and its `Replay`
-- instance. One session is one `(connectionId, role)` stream: the peer is
-- the session key chosen by the log adapter, so it is NOT part of the
-- event type. The client role pipelines up to k requests (FIFO); the
-- server role holds at most one request, answered after an unlogged τ.
-- Imports only stdlib and Semantics.Replay.
module Cardano_network.Replay.LeiosFetchSession where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (_<?_) renaming (_≟_ to _≟ℕ_)
open import Data.List using (List; []; _∷_; [_]; _∷ʳ_; length; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.Any using (here)
import Data.List.Properties as Listₚ
open import Data.Product using (_×_; _,_; ∃; proj₁)
import Data.Product.Properties as Prodₚ
open import Data.Empty using (⊥-elim)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_)

open import Semantics.Replay

------------------------------------------------------------------------
-- Log-level events (A8)

-- Identifiers are ℕ: an `ebHash` is the 256-bit number its 64 hex digits
-- denote (parsed by the adapter, Phase 6), slots/sizes/counts are as logged.
-- ℕ equality is --safe and reduces at typecheck time (builtin `_≡ᵇ_`).

open import Cardano_network.Replay.Common using (Direction; Send; Recv) public

-- A LeiosFetch message as the tracer abstracts it (no EB / tx bodies).
data Msg : Set where
  -- MsgLeiosBlockRequest {ebHash, ebSlot}
  MsgLeiosBlockRequest    : (ebHash ebSlot : ℕ) → Msg
  -- MsgLeiosBlock {ebHash, ebBytesSize} (the log carries no slot)
  MsgLeiosBlock           : (ebHash ebBytesSize : ℕ) → Msg
  -- MsgLeiosBlockTxsRequest {ebHash, ebSlot, numTxs, bitmaps}
  MsgLeiosBlockTxsRequest : (ebHash ebSlot numTxs : ℕ)
                            (bitmaps : List (ℕ × ℕ)) → Msg
  -- MsgLeiosBlockTxs {ebHash, ebSlot, numTxs, txsBytesSize, bitmaps}
  MsgLeiosBlockTxs        : (ebHash ebSlot numTxs txsBytesSize : ℕ)
                            (bitmaps : List (ℕ × ℕ)) → Msg
  -- MsgLeiosDone
  MsgLeiosDone            : Msg

-- A replay event: direction and message.
E : Set
E = Direction × Msg

-- Decidable equality of directions.
_≟D_ : DecidableEquality Direction
Send ≟D Send = yes refl
Recv ≟D Recv = yes refl
Send ≟D Recv = no λ ()
Recv ≟D Send = no λ ()

-- Decidable equality of bitmaps (lists of (index, 64-bit word)).
_≟B_ : DecidableEquality (List (ℕ × ℕ))
_≟B_ = Listₚ.≡-dec (Prodₚ.≡-dec _≟ℕ_ _≟ℕ_)

-- Decidable equality of messages (by hand; same constructor: fieldwise).
_≟M_ : DecidableEquality Msg
MsgLeiosBlockRequest h s ≟M MsgLeiosBlockRequest h′ s′ =
  map′ (λ { (refl , refl) → refl }) (λ { refl → refl , refl })
       (h ≟ℕ h′ ×-dec s ≟ℕ s′)
MsgLeiosBlock h z ≟M MsgLeiosBlock h′ z′ =
  map′ (λ { (refl , refl) → refl }) (λ { refl → refl , refl })
       (h ≟ℕ h′ ×-dec z ≟ℕ z′)
MsgLeiosBlockTxsRequest h s n b ≟M MsgLeiosBlockTxsRequest h′ s′ n′ b′ =
  map′ (λ { (refl , refl , refl , refl) → refl })
       (λ { refl → refl , refl , refl , refl })
       (h ≟ℕ h′ ×-dec s ≟ℕ s′ ×-dec n ≟ℕ n′ ×-dec b ≟B b′)
MsgLeiosBlockTxs h s n z b ≟M MsgLeiosBlockTxs h′ s′ n′ z′ b′ =
  map′ (λ { (refl , refl , refl , refl , refl) → refl })
       (λ { refl → refl , refl , refl , refl , refl })
       (h ≟ℕ h′ ×-dec s ≟ℕ s′ ×-dec n ≟ℕ n′ ×-dec z ≟ℕ z′ ×-dec b ≟B b′)
MsgLeiosDone ≟M MsgLeiosDone = yes refl
MsgLeiosBlockRequest _ _          ≟M MsgLeiosBlock _ _                = no λ ()
MsgLeiosBlockRequest _ _          ≟M MsgLeiosBlockTxsRequest _ _ _ _  = no λ ()
MsgLeiosBlockRequest _ _          ≟M MsgLeiosBlockTxs _ _ _ _ _       = no λ ()
MsgLeiosBlockRequest _ _          ≟M MsgLeiosDone                     = no λ ()
MsgLeiosBlock _ _                 ≟M MsgLeiosBlockRequest _ _         = no λ ()
MsgLeiosBlock _ _                 ≟M MsgLeiosBlockTxsRequest _ _ _ _  = no λ ()
MsgLeiosBlock _ _                 ≟M MsgLeiosBlockTxs _ _ _ _ _       = no λ ()
MsgLeiosBlock _ _                 ≟M MsgLeiosDone                     = no λ ()
MsgLeiosBlockTxsRequest _ _ _ _   ≟M MsgLeiosBlockRequest _ _         = no λ ()
MsgLeiosBlockTxsRequest _ _ _ _   ≟M MsgLeiosBlock _ _                = no λ ()
MsgLeiosBlockTxsRequest _ _ _ _   ≟M MsgLeiosBlockTxs _ _ _ _ _       = no λ ()
MsgLeiosBlockTxsRequest _ _ _ _   ≟M MsgLeiosDone                     = no λ ()
MsgLeiosBlockTxs _ _ _ _ _        ≟M MsgLeiosBlockRequest _ _         = no λ ()
MsgLeiosBlockTxs _ _ _ _ _        ≟M MsgLeiosBlock _ _                = no λ ()
MsgLeiosBlockTxs _ _ _ _ _        ≟M MsgLeiosBlockTxsRequest _ _ _ _  = no λ ()
MsgLeiosBlockTxs _ _ _ _ _        ≟M MsgLeiosDone                     = no λ ()
MsgLeiosDone                      ≟M MsgLeiosBlockRequest _ _         = no λ ()
MsgLeiosDone                      ≟M MsgLeiosBlock _ _                = no λ ()
MsgLeiosDone                      ≟M MsgLeiosBlockTxsRequest _ _ _ _  = no λ ()
MsgLeiosDone                      ≟M MsgLeiosBlockTxs _ _ _ _ _       = no λ ()

-- Decidable equality of events.
_≟E_ : DecidableEquality E
_≟E_ = Prodₚ.≡-dec _≟D_ _≟M_

------------------------------------------------------------------------
-- Session states (A1, A2, A9)

-- An outstanding request: kind, ebHash and ebSlot.
data Req : Set where
  -- a BlockRequest for (ebHash, ebSlot)
  blockReq    : (ebHash ebSlot : ℕ) → Req
  -- a BlockTxsRequest for (ebHash, ebSlot)
  blockTxsReq : (ebHash ebSlot : ℕ) → Req

-- Session state, both roles: the client keeps a FIFO queue (head = oldest),
-- the server is idle, busy (request received, not yet served), ready
-- (application has answered, unlogged) or closed.
data St : Set where
  -- client, open, with its outstanding requests oldest first
  cOpen   : List Req → St
  -- client after sending Done
  cClosed : St
  -- server with no outstanding request
  sIdle   : St
  -- server holding a request the application has not yet answered
  sBusy   : Req → St
  -- server holding a request whose reply is ready to send
  sReady  : Req → St
  -- server after receiving Done
  sClosed : St

-- Initial state of a client-role session.
client₀ : St
client₀ = cOpen []

-- Initial state of a server-role session.
server₀ : St
server₀ = sIdle

------------------------------------------------------------------------
-- Steps, parametrised by the client pipelining bound k (the log needs k ≥ 4)

module Spec (k : ℕ) where

  infix 4 _-[_]→_ _-τ→_

  -- Visible steps. A response must answer the matching outstanding request
  -- on kind and ebHash (and ebSlot for BlockTxs); its other payload fields
  -- (sizes, numTxs, bitmaps) are unconstrained, since the log abstracts the
  -- payload and the request's numTxs/bitmaps need not be echoed.
  data _-[_]→_ : St → E → St → Set where
    -- client sends a BlockRequest while fewer than k are outstanding
    cSendBlockReq : ∀ {q h s} → length q < k →
      cOpen q -[ Send , MsgLeiosBlockRequest h s ]→ cOpen (q ∷ʳ blockReq h s)
    -- client sends a BlockTxsRequest while fewer than k are outstanding
    cSendTxsReq   : ∀ {q h s n b} → length q < k →
      cOpen q -[ Send , MsgLeiosBlockTxsRequest h s n b ]→
      cOpen (q ∷ʳ blockTxsReq h s)
    -- client receives the Block answering the oldest request
    cRecvBlock    : ∀ {q h s z} →
      cOpen (blockReq h s ∷ q) -[ Recv , MsgLeiosBlock h z ]→ cOpen q
    -- client receives the BlockTxs answering the oldest request
    cRecvTxs      : ∀ {q h s n z b} →
      cOpen (blockTxsReq h s ∷ q) -[ Recv , MsgLeiosBlockTxs h s n z b ]→
      cOpen q
    -- client sends Done with nothing outstanding
    cSendDone     : cOpen [] -[ Send , MsgLeiosDone ]→ cClosed
    -- idle server receives a BlockRequest
    sRecvBlockReq : ∀ {h s} →
      sIdle -[ Recv , MsgLeiosBlockRequest h s ]→ sBusy (blockReq h s)
    -- idle server receives a BlockTxsRequest
    sRecvTxsReq   : ∀ {h s n b} →
      sIdle -[ Recv , MsgLeiosBlockTxsRequest h s n b ]→
      sBusy (blockTxsReq h s)
    -- ready server sends the Block for its request
    sSendBlock    : ∀ {h s z} →
      sReady (blockReq h s) -[ Send , MsgLeiosBlock h z ]→ sIdle
    -- ready server sends the BlockTxs for its request
    sSendTxs      : ∀ {h s n z b} →
      sReady (blockTxsReq h s) -[ Send , MsgLeiosBlockTxs h s n z b ]→ sIdle
    -- idle server receives Done
    sRecvDone     : sIdle -[ Recv , MsgLeiosDone ]→ sClosed

  -- Silent steps: the unlogged application events (`apiLPev` request report
  -- and reply) that turn a received request into a ready reply.
  data _-τ→_ : St → St → Set where
    -- the application serves the outstanding request
    sServe : ∀ {r} → sBusy r -τ→ sReady r

  -- A step to x guarded by a decision: listed iff the decision is yes.
  guard : ∀ {P : Set} {s e} → Dec P → (x : St) → (P → s -[ e ]→ x) →
          List (∃ (s -[ e ]→_))
  guard (yes p) x f = [ x , f p ]
  guard (no _)  _ _ = []

  -- The guarded step is listed whenever its condition holds.
  guard-complete : ∀ {P : Set} {s e x} {f : P → s -[ e ]→ x} (d : Dec P) →
                   P → x ∈ map proj₁ (guard d x f)
  guard-complete (yes _) _ = here refl
  guard-complete (no ¬p) p = ⊥-elim (¬p p)

  -- Client receives a Block: the queue head must be a BlockRequest for it.
  recvBlock : ∀ q h z → List (∃ (cOpen q -[ Recv , MsgLeiosBlock h z ]→_))
  recvBlock (blockReq h′ _ ∷ q) h _ = guard (h′ ≟ℕ h) (cOpen q) λ { refl → cRecvBlock }
  recvBlock _                   _ _ = []

  -- Client receives a BlockTxs: the queue head must be a BlockTxsRequest for
  -- the same ebHash and ebSlot.
  recvTxs : ∀ q h s n z b →
            List (∃ (cOpen q -[ Recv , MsgLeiosBlockTxs h s n z b ]→_))
  recvTxs (blockTxsReq h′ s′ ∷ q) h s _ _ _ =
    guard (h′ ≟ℕ h ×-dec s′ ≟ℕ s) (cOpen q) λ { (refl , refl) → cRecvTxs }
  recvTxs _ _ _ _ _ _ = []

  -- Client sends Done: only with an empty queue.
  sendDone : ∀ q → List (∃ (cOpen q -[ Send , MsgLeiosDone ]→_))
  sendDone []      = [ cClosed , cSendDone ]
  sendDone (_ ∷ _) = []

  -- Server sends a Block: its ready request must be a BlockRequest for it.
  sendBlock : ∀ r h z → List (∃ (sReady r -[ Send , MsgLeiosBlock h z ]→_))
  sendBlock (blockReq h′ _) h _ = guard (h′ ≟ℕ h) sIdle λ { refl → sSendBlock }
  sendBlock (blockTxsReq _ _) _ _ = []

  -- Server sends a BlockTxs: its ready request must be a BlockTxsRequest for
  -- the same ebHash and ebSlot.
  sendTxs : ∀ r h s n z b →
            List (∃ (sReady r -[ Send , MsgLeiosBlockTxs h s n z b ]→_))
  sendTxs (blockTxsReq h′ s′) h s _ _ _ =
    guard (h′ ≟ℕ h ×-dec s′ ≟ℕ s) sIdle λ { (refl , refl) → sSendTxs }
  sendTxs (blockReq _ _) _ _ _ _ _ = []

  -- All e-steps out of s, each with its derivation (0 or 1 of them).
  steps : (s : St) (e : E) → List (∃ (s -[ e ]→_))
  steps (cOpen q) (Send , MsgLeiosBlockRequest h s) =
    guard (length q <? k) (cOpen (q ∷ʳ blockReq h s)) cSendBlockReq
  steps (cOpen q) (Send , MsgLeiosBlockTxsRequest h s n b) =
    guard (length q <? k) (cOpen (q ∷ʳ blockTxsReq h s)) cSendTxsReq
  steps (cOpen q) (Recv , MsgLeiosBlock h z)             = recvBlock q h z
  steps (cOpen q) (Recv , MsgLeiosBlockTxs h s n z b)    = recvTxs q h s n z b
  steps (cOpen q) (Send , MsgLeiosDone)                  = sendDone q
  steps sIdle (Recv , MsgLeiosBlockRequest h s)          = [ _ , sRecvBlockReq ]
  steps sIdle (Recv , MsgLeiosBlockTxsRequest h s n b)   = [ _ , sRecvTxsReq ]
  steps sIdle (Recv , MsgLeiosDone)                      = [ _ , sRecvDone ]
  steps (sReady r) (Send , MsgLeiosBlock h z)            = sendBlock r h z
  steps (sReady r) (Send , MsgLeiosBlockTxs h s n z b)   = sendTxs r h s n z b
  steps _ _ = []

  -- All τ-steps out of s, each with its derivation (0 or 1 of them).
  tauSteps : (s : St) → List (∃ (s -τ→_))
  tauSteps (sBusy r) = [ sReady r , sServe ]
  tauSteps _         = []

  -- e-successors of a state.
  after : St → E → List St
  after s e = map proj₁ (steps s e)

  -- τ-successors of a state.
  taus : St → List St
  taus s = map proj₁ (tauSteps s)

  -- Every listed e-successor is an e-step (the derivation is carried).
  after-sound : ∀ {s e s′} → s′ ∈ after s e → s -[ e ]→ s′
  after-sound m with ∈-map⁻ proj₁ m
  ... | (_ , st) , _ , refl = st

  -- Every listed τ-successor is a τ-step (the derivation is carried).
  taus-sound : ∀ {s s′} → s′ ∈ taus s → s -τ→ s′
  taus-sound m with ∈-map⁻ proj₁ m
  ... | (_ , st) , _ , refl = st

  -- Every e-step is listed.
  after-complete : ∀ {s e s′} → s -[ e ]→ s′ → s′ ∈ after s e
  after-complete (cSendBlockReq {q} lt)        = guard-complete (length q <? k) lt
  after-complete (cSendTxsReq {q} lt)          = guard-complete (length q <? k) lt
  after-complete (cRecvBlock {h = h})          = guard-complete (h ≟ℕ h) refl
  after-complete (cRecvTxs {h = h} {s = s})    =
    guard-complete (h ≟ℕ h ×-dec s ≟ℕ s) (refl , refl)
  after-complete cSendDone                     = here refl
  after-complete sRecvBlockReq                 = here refl
  after-complete sRecvTxsReq                   = here refl
  after-complete (sSendBlock {h = h})          = guard-complete (h ≟ℕ h) refl
  after-complete (sSendTxs {h = h} {s = s})    =
    guard-complete (h ≟ℕ h ×-dec s ≟ℕ s) (refl , refl)
  after-complete sRecvDone                     = here refl

  -- Every τ-step is listed.
  taus-complete : ∀ {s s′} → s -τ→ s′ → s′ ∈ taus s
  taus-complete sServe = here refl

  -- The replay instance for one LeiosFetch session (either role).
  leiosFetch : Replay 0ℓ St E
  leiosFetch = record
    { _-[_]→_        = _-[_]→_
    ; _-τ→_          = _-τ→_
    ; _≟E_           = _≟E_
    ; after          = after
    ; taus           = taus
    ; after-sound    = after-sound
    ; taus-sound     = taus-sound
    ; after-complete = after-complete
    ; taus-complete  = taus-complete
    }
