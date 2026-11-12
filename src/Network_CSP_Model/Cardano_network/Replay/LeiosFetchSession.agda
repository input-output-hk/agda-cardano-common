{-# OPTIONS --safe #-}

-- First-order session spec for ONE LeiosFetch session as seen in a node's
-- log (trace-replay Phase 3, amendments A1, A2, A8, A9), and its `Replay`
-- instance. One session is one `(connectionId, role)` stream: the peer is
-- the session key chosen by the log adapter, so it is NOT part of the
-- event type. The client role pipelines up to k requests (FIFO); the
-- server role holds at most one request, answered after an unlogged τ.
-- Aligned with upstream ouroboros-consensus e651152750388ccf20700eb28149751981a396f4.
-- Wire checks remain active while silently draining; client checks do not.
module Cardano_network.Replay.LeiosFetchSession where

open import Level using (0ℓ)
open import Data.Bool using (T; if_then_else_; _∧_)
open import Data.Nat using (ℕ; _<_; _≤_; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using (_<?_; _≤?_) renaming (_≟_ to _≟ℕ_)
open import Data.List using (List; []; _∷_; [_]; _∷ʳ_; length; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Properties as Listₚ
open import Data.Product using (_×_; _,_; ∃; proj₁)
import Data.Product.Properties as Prodₚ
open import Data.Empty using (⊥-elim)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_; T?; does)
open import Data.String using (String; _++_)

open import Cardano_network.Replay.LeiosFetchWire using
  (Bitmap; validᵇ; popcount; maxTxs; txsCap; ebCap)

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
                            (bitmaps : Bitmap) → Msg
  -- MsgLeiosBlockTxs {numTxs, txsBytesSize}: positional, with no echoed point.
  MsgLeiosBlockTxs        : (numTxs txsBytesSize : ℕ) → Msg
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
_≟B_ : DecidableEquality Bitmap
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
MsgLeiosBlockTxs n z ≟M MsgLeiosBlockTxs n′ z′ =
  map′ (λ { (refl , refl) → refl }) (λ { refl → refl , refl })
       (n ≟ℕ n′ ×-dec z ≟ℕ z′)
MsgLeiosDone ≟M MsgLeiosDone = yes refl
MsgLeiosBlockRequest _ _           ≟M MsgLeiosBlock _ _                  = no λ ()
MsgLeiosBlockRequest _ _           ≟M MsgLeiosBlockTxsRequest _ _ _ _    = no λ ()
MsgLeiosBlockRequest _ _           ≟M MsgLeiosBlockTxs _ _               = no λ ()
MsgLeiosBlockRequest _ _           ≟M MsgLeiosDone                       = no λ ()
MsgLeiosBlock _ _                  ≟M MsgLeiosBlockRequest _ _           = no λ ()
MsgLeiosBlock _ _                  ≟M MsgLeiosBlockTxsRequest _ _ _ _    = no λ ()
MsgLeiosBlock _ _                  ≟M MsgLeiosBlockTxs _ _               = no λ ()
MsgLeiosBlock _ _                  ≟M MsgLeiosDone                       = no λ ()
MsgLeiosBlockTxsRequest _ _ _ _    ≟M MsgLeiosBlockRequest _ _           = no λ ()
MsgLeiosBlockTxsRequest _ _ _ _    ≟M MsgLeiosBlock _ _                  = no λ ()
MsgLeiosBlockTxsRequest _ _ _ _    ≟M MsgLeiosBlockTxs _ _               = no λ ()
MsgLeiosBlockTxsRequest _ _ _ _    ≟M MsgLeiosDone                       = no λ ()
MsgLeiosBlockTxs _ _               ≟M MsgLeiosBlockRequest _ _           = no λ ()
MsgLeiosBlockTxs _ _               ≟M MsgLeiosBlock _ _                  = no λ ()
MsgLeiosBlockTxs _ _               ≟M MsgLeiosBlockTxsRequest _ _ _ _    = no λ ()
MsgLeiosBlockTxs _ _               ≟M MsgLeiosDone                       = no λ ()
MsgLeiosDone                       ≟M MsgLeiosBlockRequest _ _           = no λ ()
MsgLeiosDone                       ≟M MsgLeiosBlock _ _                  = no λ ()
MsgLeiosDone                       ≟M MsgLeiosBlockTxsRequest _ _ _ _    = no λ ()
MsgLeiosDone                       ≟M MsgLeiosBlockTxs _ _               = no λ ()

-- Decidable equality of events.
_≟E_ : DecidableEquality E
_≟E_ = Prodₚ.≡-dec _≟D_ _≟M_

------------------------------------------------------------------------
-- Session states (A1, A2, A9)

-- An outstanding request retains its point and, for transactions, its count.
data Req : Set where
  -- A BlockRequest for (ebHash, ebSlot).
  blockReq    : (ebHash ebSlot : ℕ) → Req
  -- A BlockTxsRequest whose reply is checked by count, positionally.
  blockTxsReq : (ebHash ebSlot numTxs : ℕ) → Req

-- The client either checks replies or drains them; the server may throw.
data St : Set where
  -- Client checking replies, with its outstanding requests oldest first.
  cOpen   : List Req → St
  -- Client draining replies without running client handlers.
  cDrain  : List Req → St
  -- Client after sending Done.
  cClosed : St
  -- Server with no outstanding request.
  sIdle   : St
  -- Server awaiting an application answer.
  sBusy   : Req → St
  -- Server holding a ready application answer.
  sReady  : Req → St
  -- Server after an application throw; no further events.
  sThrown : St
  -- Server after receiving Done.
  sClosed : St

-- Initial state of a client-role session.
client₀ : St
client₀ = cOpen []

-- Initial state of a server-role session.
server₀ : St
server₀ = sIdle

-- A compact state name for impossible-event diagnostics, independent of parsing.
stateName : St → String
stateName (cOpen _) = "client open"
stateName (cDrain _) = "client draining"
stateName cClosed = "client closed"
stateName sIdle = "server idle"
stateName (sBusy _) = "server busy"
stateName (sReady _) = "server ready"
stateName sThrown = "server thrown"
stateName sClosed = "server closed"

------------------------------------------------------------------------
-- Steps, parametrised by the client pipelining bound k.

module Spec (k : ℕ) where

  infix 4 _-[_]→_ _-τ→_

  -- Legal visible steps: wire caps, then the observable client checks.
  data _-[_]→_ : St → E → St → Set where
    -- Client sends a BlockRequest within its pipeline bound.
    cSendBlockReq : ∀ {q h s} → length q < k →
      cOpen q -[ Send , MsgLeiosBlockRequest h s ]→ cOpen (q ∷ʳ blockReq h s)
    -- Honest client requests fit maxTxs and agree with a valid wire bitmap.
    cSendTxsReq : ∀ {q h s n b} → length q < k → T (validᵇ b) → n ≡ popcount b → n ≤ maxTxs →
      cOpen q -[ Send , MsgLeiosBlockTxsRequest h s n b ]→
      cOpen (q ∷ʳ blockTxsReq h s n)
    -- Client checks the oldest Block request's hash and the wire byte cap.
    cRecvBlock : ∀ {q h s z} → z ≤ ebCap →
      cOpen (blockReq h s ∷ q) -[ Recv , MsgLeiosBlock h z ]→ cOpen q
    -- Client checks the oldest transaction request's count and wire caps.
    cRecvTxs : ∀ {q h s n z} → n ≤ maxTxs → z ≤ txsCap →
      cOpen (blockTxsReq h s n ∷ q) -[ Recv , MsgLeiosBlockTxs n z ]→ cOpen q
    -- Client may send Done once its checked queue is empty.
    cSendDone : cOpen [] -[ Send , MsgLeiosDone ]→ cClosed
    -- Draining consumes a Block by kind, without checking the hash.
    cDrainBlock : ∀ {q h s h′ z} → z ≤ ebCap →
      cDrain (blockReq h s ∷ q) -[ Recv , MsgLeiosBlock h′ z ]→ cDrain q
    -- Draining consumes transactions by kind, without checking their count.
    cDrainTxs : ∀ {q h s n n′ z} → n′ ≤ maxTxs → z ≤ txsCap →
      cDrain (blockTxsReq h s n ∷ q) -[ Recv , MsgLeiosBlockTxs n′ z ]→ cDrain q
    -- Draining ends with Done only after every outstanding reply.
    cDrainDone : cDrain [] -[ Send , MsgLeiosDone ]→ cClosed
    -- Idle server receives a Block request.
    sRecvBlockReq : ∀ {h s} →
      sIdle -[ Recv , MsgLeiosBlockRequest h s ]→ sBusy (blockReq h s)
    -- Server observation checks bitmap decoding and the logged request count.
    sRecvTxsReq : ∀ {h s n b} → T (validᵇ b) → n ≡ popcount b →
      sIdle -[ Recv , MsgLeiosBlockTxsRequest h s n b ]→ sBusy (blockTxsReq h s n)
    -- Ready server replies with the requested Block within the byte cap.
    sSendBlock : ∀ {h s z} → z ≤ ebCap →
      sReady (blockReq h s) -[ Send , MsgLeiosBlock h z ]→ sIdle
    -- Ready server replies positionally within both wire decoder caps.
    sSendTxs : ∀ {h s n z} → n ≤ maxTxs → z ≤ txsCap →
      sReady (blockTxsReq h s n) -[ Send , MsgLeiosBlockTxs n z ]→ sIdle
    -- Idle server receives Done.
    sRecvDone : sIdle -[ Recv , MsgLeiosDone ]→ sClosed

  -- Unlogged application service, throw, or client stop-and-drain.
  data _-τ→_ : St → St → Set where
    -- The application serves the outstanding request.
    sServe : ∀ {r} → sBusy r -τ→ sReady r
    -- The application cannot serve the request and closes the session.
    sThrow : ∀ {r} → sBusy r -τ→ sThrown
    -- Once stopped the client drains, with no further requests.
    cStop : ∀ {q} → cOpen q -τ→ cDrain q

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

  -- Checked Block replies require the oldest request's hash and byte cap.
  recvBlock : ∀ q h z → List (∃ (cOpen q -[ Recv , MsgLeiosBlock h z ]→_))
  recvBlock (blockReq h′ _ ∷ q) h z =
    guard (z ≤? ebCap ×-dec h′ ≟ℕ h) (cOpen q) λ { (cap , refl) → cRecvBlock cap }
  recvBlock _ _ _ = []

  -- Checked transaction replies require caps and the oldest request's count.
  recvTxs : ∀ q n z → List (∃ (cOpen q -[ Recv , MsgLeiosBlockTxs n z ]→_))
  recvTxs (blockTxsReq _ _ n′ ∷ q) n z =
    guard (n ≤? maxTxs ×-dec z ≤? txsCap ×-dec n′ ≟ℕ n) (cOpen q)
      λ { (countCap , byteCap , refl) → cRecvTxs countCap byteCap }
  recvTxs _ _ _ = []

  -- Checked Done is allowed only with an empty queue.
  sendDone : ∀ q → List (∃ (cOpen q -[ Send , MsgLeiosDone ]→_))
  sendDone [] = [ cClosed , cSendDone ]
  sendDone (_ ∷ _) = []

  -- Drained Block replies ignore hashes but retain the wire byte cap.
  drainBlock : ∀ q h z → List (∃ (cDrain q -[ Recv , MsgLeiosBlock h z ]→_))
  drainBlock (blockReq _ _ ∷ q) h z = guard (z ≤? ebCap) (cDrain q) cDrainBlock
  drainBlock _ _ _ = []

  -- Drained transaction replies ignore count matching but retain both wire caps.
  drainTxs : ∀ q n z → List (∃ (cDrain q -[ Recv , MsgLeiosBlockTxs n z ]→_))
  drainTxs (blockTxsReq _ _ _ ∷ q) n z =
    guard (n ≤? maxTxs ×-dec z ≤? txsCap) (cDrain q)
      λ { (countCap , byteCap) → cDrainTxs countCap byteCap }
  drainTxs _ _ _ = []

  -- Drained Done is allowed only with an empty queue.
  drainDone : ∀ q → List (∃ (cDrain q -[ Send , MsgLeiosDone ]→_))
  drainDone [] = [ cClosed , cDrainDone ]
  drainDone (_ ∷ _) = []

  -- Ready Block replies check their hash and the wire byte cap.
  sendBlock : ∀ r h z → List (∃ (sReady r -[ Send , MsgLeiosBlock h z ]→_))
  sendBlock (blockReq h′ _) h z =
    guard (z ≤? ebCap ×-dec h′ ≟ℕ h) sIdle λ { (cap , refl) → sSendBlock cap }
  sendBlock (blockTxsReq _ _ _) _ _ = []

  -- Ready transaction replies check both wire caps and their positional count.
  sendTxs : ∀ r n z → List (∃ (sReady r -[ Send , MsgLeiosBlockTxs n z ]→_))
  sendTxs (blockTxsReq _ _ n′) n z =
    guard (n ≤? maxTxs ×-dec z ≤? txsCap ×-dec n′ ≟ℕ n) sIdle
      λ { (countCap , byteCap , refl) → sSendTxs countCap byteCap }
  sendTxs (blockReq _ _) _ _ = []

  -- All e-steps out of s, each with its derivation (zero or one).
  steps : (s : St) (e : E) → List (∃ (s -[ e ]→_))
  steps (cOpen q) (Send , MsgLeiosBlockRequest h s) =
    guard (length q <? k) (cOpen (q ∷ʳ blockReq h s)) cSendBlockReq
  steps (cOpen q) (Send , MsgLeiosBlockTxsRequest h s n b) =
    guard (length q <? k ×-dec T? (validᵇ b) ×-dec n ≟ℕ popcount b ×-dec n ≤? maxTxs)
      (cOpen (q ∷ʳ blockTxsReq h s n))
      λ { (lt , valid , count , cap) → cSendTxsReq lt valid count cap }
  steps (cOpen q) (Recv , MsgLeiosBlock h z) = recvBlock q h z
  steps (cOpen q) (Recv , MsgLeiosBlockTxs n z) = recvTxs q n z
  steps (cOpen q) (Send , MsgLeiosDone) = sendDone q
  steps (cDrain q) (Recv , MsgLeiosBlock h z) = drainBlock q h z
  steps (cDrain q) (Recv , MsgLeiosBlockTxs n z) = drainTxs q n z
  steps (cDrain q) (Send , MsgLeiosDone) = drainDone q
  steps sIdle (Recv , MsgLeiosBlockRequest h s) = [ _ , sRecvBlockReq ]
  steps sIdle (Recv , MsgLeiosBlockTxsRequest h s n b) =
    guard (T? (validᵇ b) ×-dec n ≟ℕ popcount b) (sBusy (blockTxsReq h s n))
      λ { (valid , count) → sRecvTxsReq valid count }
  steps sIdle (Recv , MsgLeiosDone) = [ _ , sRecvDone ]
  steps (sReady r) (Send , MsgLeiosBlock h z) = sendBlock r h z
  steps (sReady r) (Send , MsgLeiosBlockTxs n z) = sendTxs r n z
  steps _ _ = []

  -- All τ-steps, including the server's alternative terminal throw.
  tauSteps : (s : St) → List (∃ (s -τ→_))
  tauSteps (sBusy r) = (sReady r , sServe) ∷ (sThrown , sThrow) ∷ []
  tauSteps (cOpen q) = [ cDrain q , cStop ]
  tauSteps _ = []

  -- Visible successors, extracted from proof-carrying enumeration.
  after : St → E → List St
  after s e = map proj₁ (steps s e)

  -- Silent successors, extracted from proof-carrying enumeration.
  taus : St → List St
  taus s = map proj₁ (tauSteps s)

  -- Every listed visible successor carries a legal step.
  after-sound : ∀ {s e s′} → s′ ∈ after s e → s -[ e ]→ s′
  after-sound m with ∈-map⁻ proj₁ m
  ... | (_ , st) , _ , refl = st

  -- Every listed silent successor carries a legal step.
  taus-sound : ∀ {s s′} → s′ ∈ taus s → s -τ→ s′
  taus-sound m with ∈-map⁻ proj₁ m
  ... | (_ , st) , _ , refl = st

  -- Every visible step passes the corresponding enumeration guards.
  after-complete : ∀ {s e s′} → s -[ e ]→ s′ → s′ ∈ after s e
  after-complete (cSendBlockReq {q} lt) = guard-complete (length q <? k) lt
  after-complete (cSendTxsReq {q} {n = n} {b} lt valid count cap) =
    guard-complete (length q <? k ×-dec T? (validᵇ b) ×-dec n ≟ℕ popcount b ×-dec n ≤? maxTxs)
      (lt , valid , count , cap)
  after-complete (cRecvBlock {h = h} {z = z} cap) =
    guard-complete (z ≤? ebCap ×-dec h ≟ℕ h) (cap , refl)
  after-complete (cRecvTxs {n = n} {z} countCap byteCap) =
    guard-complete (n ≤? maxTxs ×-dec z ≤? txsCap ×-dec n ≟ℕ n)
      (countCap , byteCap , refl)
  after-complete cSendDone = here refl
  after-complete (cDrainBlock {z = z} cap) = guard-complete (z ≤? ebCap) cap
  after-complete (cDrainTxs {n′ = n} {z} countCap byteCap) =
    guard-complete (n ≤? maxTxs ×-dec z ≤? txsCap) (countCap , byteCap)
  after-complete cDrainDone = here refl
  after-complete sRecvBlockReq = here refl
  after-complete (sRecvTxsReq {n = n} {b} valid count) =
    guard-complete (T? (validᵇ b) ×-dec n ≟ℕ popcount b) (valid , count)
  after-complete (sSendBlock {h = h} {z = z} cap) =
    guard-complete (z ≤? ebCap ×-dec h ≟ℕ h) (cap , refl)
  after-complete (sSendTxs {n = n} {z} countCap byteCap) =
    guard-complete (n ≤? maxTxs ×-dec z ≤? txsCap ×-dec n ≟ℕ n)
      (countCap , byteCap , refl)
  after-complete sRecvDone = here refl

  -- Every silent step appears in the enumeration, including throw.
  taus-complete : ∀ {s s′} → s -τ→ s′ → s′ ∈ taus s
  taus-complete sServe = here refl
  taus-complete sThrow = there (here refl)
  taus-complete cStop = here refl

  -- The replay interface for either role of one session.
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

  -- Request diagnostics check bitmap decoding before the logged popcount.
  requestWhy : ℕ → Bitmap → String
  requestWhy n b = if validᵇ b then
    (if n ≡ᵇ popcount b then "none: no failed check"
     else "client: request count differs from bitmap popcount")
    else "wire: invalid bitmap"

  -- Only honest client sends are capped; servers may receive and throw instead.
  clientRequestWhy : ℕ → Bitmap → String
  clientRequestWhy n b = if validᵇ b ∧ (n ≡ᵇ popcount b) then
    (if n ≤ᵇ maxTxs then "none: no failed check"
     else "client: request count exceeds maxTxs")
    else requestWhy n b

  -- Block diagnostics apply the wire cap before the client hash comparison.
  blockWhy : ℕ → ℕ → ℕ → String
  blockWhy expected actual z = if z ≤ᵇ ebCap then
    (if expected ≡ᵇ actual then "none: no failed check"
     else "client: block hash mismatch")
    else "wire: block byte cap exceeded"

  -- Transaction diagnostics apply both wire caps before the client count check.
  txsWhy : ℕ → ℕ → ℕ → String
  txsWhy expected actual z = if actual ≤ᵇ maxTxs then
    (if z ≤ᵇ txsCap then
      (if expected ≡ᵇ actual then "none: no failed check"
       else "client: reply count mismatch")
     else "wire: transaction byte cap exceeded")
    else "wire: transaction count cap exceeded"

  -- An impossible message kind or agency is labelled with the current state.
  noStepWhy : St → String
  noStepWhy s = "wire: no step from " ++ stateName s

  -- Diagnose a ready reply (also the possible service successor of busy).
  replyWhy : St → Req → E → String
  replyWhy st (blockReq h _) (Send , MsgLeiosBlock h′ z) = blockWhy h h′ z
  replyWhy st (blockTxsReq _ _ n) (Send , MsgLeiosBlockTxs n′ z) =
    txsWhy n n′ z
  replyWhy st _ (Recv , MsgLeiosBlockRequest _ _) = "wire: request while one is outstanding"
  replyWhy st _ (Recv , MsgLeiosBlockTxsRequest _ _ _ _) = "wire: request while one is outstanding"
  replyWhy st _ _ = noStepWhy st

  -- Best-effort first-failure explanation for the non-draining reading.
  -- Busy states are read through service; this function carries no proof.
  whyRejected : St → E → String
  whyRejected (cOpen q) (Send , MsgLeiosBlockRequest _ _) =
    if does (length q <? k) then "none: no failed check" else "wire: pipeline depth exceeded"
  whyRejected (cOpen q) (Send , MsgLeiosBlockTxsRequest _ _ n b) =
    if does (length q <? k) then clientRequestWhy n b else "wire: pipeline depth exceeded"
  whyRejected (cOpen (blockReq h _ ∷ q)) (Recv , MsgLeiosBlock h′ z) = blockWhy h h′ z
  whyRejected (cOpen (blockTxsReq _ _ n ∷ q)) (Recv , MsgLeiosBlockTxs n′ z) = txsWhy n n′ z
  whyRejected (cOpen []) (Send , MsgLeiosDone) = "none: no failed check"
  whyRejected (cOpen (_ ∷ _)) (Send , MsgLeiosDone) = "wire: Done with outstanding requests"
  whyRejected (cDrain q) (Send , MsgLeiosBlockRequest _ _) = "client: draining forbids new requests"
  whyRejected (cDrain q) (Send , MsgLeiosBlockTxsRequest _ _ _ _) = "client: draining forbids new requests"
  whyRejected (cDrain (blockReq _ _ ∷ q)) (Recv , MsgLeiosBlock _ z) =
    if z ≤ᵇ ebCap then "none: no failed check" else "wire: block byte cap exceeded"
  whyRejected (cDrain (blockTxsReq _ _ _ ∷ q)) (Recv , MsgLeiosBlockTxs n z) = txsWhy n n z
  whyRejected (cDrain []) (Send , MsgLeiosDone) = "none: no failed check"
  whyRejected (cDrain (_ ∷ _)) (Send , MsgLeiosDone) = "wire: Done with outstanding requests"
  whyRejected sIdle (Recv , MsgLeiosBlockRequest _ _) = "none: no failed check"
  whyRejected sIdle (Recv , MsgLeiosBlockTxsRequest _ _ n b) = requestWhy n b
  whyRejected sIdle (Recv , MsgLeiosDone) = "none: no failed check"
  whyRejected (sBusy r) e = replyWhy (sBusy r) r e
  whyRejected (sReady r) e = replyWhy (sReady r) r e
  whyRejected s _ = noStepWhy s
