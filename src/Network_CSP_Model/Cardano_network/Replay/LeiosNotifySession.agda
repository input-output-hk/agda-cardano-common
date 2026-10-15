{-# OPTIONS --safe #-}

-- Strict depth-one wire language of LeiosNotifyP, including RequestNext.
-- Payload fields are retained for diagnostics; agency and message kind govern steps.
module Cardano_network.Replay.LeiosNotifySession where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as Maybe
open import Data.Product using (_×_; _,_)
import Data.Product.Properties as Pair
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_)
open import Semantics.Replay
open import Semantics.Replay.Decide using (module Decider)
open import Cardano_network.Replay.Common public

-- Optional announcement metadata is exactly the point and size exposed by the logger.
Announcement : Set
Announcement = Maybe (ℕ × ℕ × ℕ)

-- Six prototype message forms; votes retain (RB hash, voter id), not signatures.
data Msg : Set where
  RequestNext : Msg
  BlockAnnouncement : Announcement → Msg
  BlockOffer : (hash slot bytes : ℕ) → Msg
  BlockTxsOffer : (hash slot : ℕ) → Msg
  Votes : List (ℕ × ℕ) → Msg
  Done : Msg

-- Observable control shapes used in the PTree bridge's explicit abstraction.
data Kind : Set where
  request announcement offer txsOffer votes doneK : Kind

-- Discard payload fields, which do not affect the peer's wire agency.
kind : Msg → Kind
kind RequestNext = request
kind (BlockAnnouncement _) = announcement
kind (BlockOffer _ _ _) = offer
kind (BlockTxsOffer _ _) = txsOffer
kind (Votes _) = votes
kind Done = doneK

-- Equality on direction tags.
dirEq : DecidableEquality Direction
dirEq Send Send = yes refl
dirEq Recv Recv = yes refl
dirEq Send Recv = no λ ()
dirEq Recv Send = no λ ()

-- Equality on retained message fields.
msgEq : DecidableEquality Msg
msgEq RequestNext RequestNext = yes refl
msgEq (BlockAnnouncement a) (BlockAnnouncement a′) = map′ (λ { (refl) → refl }) (λ { refl → (refl) })
  (Maybe.≡-dec (Pair.≡-dec _≟_ (Pair.≡-dec _≟_ _≟_)) a a′)
msgEq (BlockOffer h s z) (BlockOffer h′ s′ z′) = map′ (λ { (refl , refl , refl) → refl }) (λ { refl → (refl , refl , refl) })
  (h ≟ h′ ×-dec s ≟ s′ ×-dec z ≟ z′)
msgEq (BlockTxsOffer h s) (BlockTxsOffer h′ s′) = map′ (λ { (refl , refl) → refl }) (λ { refl → (refl , refl) })
  (h ≟ h′ ×-dec s ≟ s′)
msgEq (Votes vs) (Votes vs′) = map′ (λ { (refl) → refl }) (λ { refl → (refl) })
  (List.≡-dec (Pair.≡-dec _≟_ _≟_) vs vs′)
msgEq Done Done = yes refl
msgEq RequestNext (BlockAnnouncement _) = no λ ()
msgEq RequestNext (BlockOffer _ _ _) = no λ ()
msgEq RequestNext (BlockTxsOffer _ _) = no λ ()
msgEq RequestNext (Votes _) = no λ ()
msgEq RequestNext Done = no λ ()
msgEq (BlockAnnouncement _) RequestNext = no λ ()
msgEq (BlockAnnouncement _) (BlockOffer _ _ _) = no λ ()
msgEq (BlockAnnouncement _) (BlockTxsOffer _ _) = no λ ()
msgEq (BlockAnnouncement _) (Votes _) = no λ ()
msgEq (BlockAnnouncement _) Done = no λ ()
msgEq (BlockOffer _ _ _) RequestNext = no λ ()
msgEq (BlockOffer _ _ _) (BlockAnnouncement _) = no λ ()
msgEq (BlockOffer _ _ _) (BlockTxsOffer _ _) = no λ ()
msgEq (BlockOffer _ _ _) (Votes _) = no λ ()
msgEq (BlockOffer _ _ _) Done = no λ ()
msgEq (BlockTxsOffer _ _) RequestNext = no λ ()
msgEq (BlockTxsOffer _ _) (BlockAnnouncement _) = no λ ()
msgEq (BlockTxsOffer _ _) (BlockOffer _ _ _) = no λ ()
msgEq (BlockTxsOffer _ _) (Votes _) = no λ ()
msgEq (BlockTxsOffer _ _) Done = no λ ()
msgEq (Votes _) RequestNext = no λ ()
msgEq (Votes _) (BlockAnnouncement _) = no λ ()
msgEq (Votes _) (BlockOffer _ _ _) = no λ ()
msgEq (Votes _) (BlockTxsOffer _ _) = no λ ()
msgEq (Votes _) Done = no λ ()
msgEq Done RequestNext = no λ ()
msgEq Done (BlockAnnouncement _) = no λ ()
msgEq Done (BlockOffer _ _ _) = no λ ()
msgEq Done (BlockTxsOffer _ _) = no λ ()
msgEq Done (Votes _) = no λ ()

-- A log event retains the direction and its typed message.
E : Set
E = Direction × Msg

-- The common observation of a PTree wire event and a normalized log event.
Observed : Set
Observed = Direction × Kind

-- The bridge explicitly forgets notification payloads, retaining direction and kind.
forget : E → Observed
forget (d , m) = d , kind m

-- Both roles use three control states, with role-dependent wire agency.
data St : Set where
  idle busy closed : St

-- The initiating side requests and ends; the responder supplies notifications.
command : Role → Direction
command client = Send
command server = Recv

-- The notification travels in the opposite direction from RequestNext.
response : Role → Direction
response client = Recv
response server = Send

-- Classify the four notification forms without imposing payload validity checks.
notification : Kind → Maybe St
notification announcement = just idle
notification offer = just idle
notification txsOffer = just idle
notification votes = just idle
notification _ = nothing

-- Control transitions at the explicitly observed abstraction.
nextKind : Role → St → Observed → Maybe St
nextKind client idle (Send , request) = just busy
nextKind server idle (Recv , request) = just busy
nextKind client idle (Send , doneK) = just closed
nextKind server idle (Recv , doneK) = just closed
nextKind client busy (Recv , k) = notification k
nextKind server busy (Send , k) = notification k
nextKind _ _ _ = nothing

-- A per-role replay instance, with no silent steps at this wire abstraction.
module Spec (role : Role) where
  -- One visible step is exactly a successful control transition.
  Step : St → E → St → Set
  Step s e t = nextKind role s (forget e) ≡ just t

  -- Enumerate the optional successor of a supplied event, not all possible payloads.
  after : St → E → List St
  after s e with nextKind role s (forget e)
  ... | nothing = []
  ... | just t = t ∷ []

  -- Every enumerated successor is justified by the transition function.
  after-sound : ∀ {s e t} → t ∈ after s e → Step s e t
  after-sound {s} {e} m with nextKind role s (forget e)
  ... | nothing with () ← m
  ... | just t with m
  ...   | here refl = refl
  ...   | there ()

  -- Every successful transition appears in the successor list.
  after-complete : ∀ {s e t} → Step s e t → t ∈ after s e
  after-complete {s} {e} p with nextKind role s (forget e)
  ... | nothing with () ← p
  ... | just t with p
  ...   | refl = here refl

  -- The first-order instance for the strict LeiosNotifyP wire language.
  leiosNotify : Replay 0ℓ St E
  leiosNotify = record
    { _-[_]→_ = Step ; _-τ→_ = λ _ _ → ⊥
    ; _≟E_ = Pair.≡-dec dirEq msgEq
    ; after = after ; taus = λ _ → []
    ; after-sound = after-sound ; after-complete = after-complete
    ; taus-sound = λ () ; taus-complete = λ () }

  open Traces leiosNotify public
  open Decider leiosNotify public

  -- No state has a silent successor, hence all reachable states are accessible.
  cert : ∀ s → τAccReach s
  cert s = τAccReach-all (λ _ → acc λ ()) s

  -- Decide trace membership from the idle peer state, accepting finite prefixes.
  check : (es : List E) → Relation.Nullary.Dec (HasTrace idle es)
  check = hasTrace? (cert idle)
