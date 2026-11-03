{-# OPTIONS --safe #-}

-- Bounded Notify pipelining: requests are indistinguishable credits, not hashes.
module Cardano_network.Replay.LeiosNotifyPipeline where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_,_; Σ-syntax; _×_)
open import Function.Bundles using (_⇔_; mk⇔)
import Data.Product.Properties as Pair
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
import Relation.Nullary
open import Semantics.Replay
open import Semantics.Replay.Decide using (module Decider)
open import Cardano_network.Replay.LeiosNotifySession public
  using (Role; client; server; Direction; Send; Recv; E; Msg; Kind;
         request; announcement; offer; txsOffer; votes; quit; canceled; doneK;
         Observed; forget; dirEq; msgEq)
import Cardano_network.Replay.LeiosNotifySession as Strict

-- Open and quitting sessions count outstanding requests; closed offers nothing.
data St : Set where
  openN : ℕ → St
  quitting : ℕ → St
  closed : St

-- Every generation begins with no outstanding requests.
idle : St
idle = openN 0

-- Issue only below the bound; zero disables requests but permits Quit/Done shutdown.
issue : ℕ → ℕ → Maybe St
issue depth n with n <ᵇ depth
... | true = just (openN (suc n))
... | false = nothing

-- A notification or Canceled consumes exactly one request credit.
reply : ℕ → Kind → Maybe St
reply (suc n) announcement = just (openN n)
reply (suc n) offer = just (openN n)
reply (suc n) txsOffer = just (openN n)
reply (suc n) votes = just (openN n)
reply (suc n) canceled = just (openN n)
reply _ _ = nothing

-- Draining clients discard any owed response; read-ahead servers cancel the rest.
drain : ℕ → Kind → Maybe St
drain (suc n) announcement = just (quitting n)
drain (suc n) offer = just (quitting n)
drain (suc n) txsOffer = just (quitting n)
drain (suc n) votes = just (quitting n)
drain (suc n) canceled = just (quitting n)
drain _ _ = nothing

-- Quit freezes requests; Done has responder agency and requires a drained pipe.
nextKind : ℕ → Role → St → Observed → Maybe St
nextKind depth client (openN n) (Send , request) = issue depth n
nextKind depth server (openN n) (Recv , request) = issue depth n
nextKind depth client (openN n) (Send , quit) = just (quitting n)
nextKind depth server (openN n) (Recv , quit) = just (quitting n)
nextKind depth client (openN n) (Recv , k) = reply n k
nextKind depth server (openN n) (Send , k) = reply n k
nextKind depth client (quitting 0) (Recv , doneK) = just closed
nextKind depth server (quitting 0) (Send , doneK) = just closed
nextKind depth client (quitting n) (Recv , k) = drain n k
nextKind depth server (quitting (suc n)) (Send , canceled) = just (quitting n)
nextKind _ _ _ _ = nothing

-- A per-role replay instance, with no silent steps at this wire abstraction.
module Spec (depth : ℕ) (role : Role) where
  -- One visible step is exactly a successful control transition.
  Step : St → E → St → Set
  Step s e t = nextKind depth role s (forget e) ≡ just t

  -- Enumerate the optional successor of a supplied event, not all possible payloads.
  after : St → E → List St
  after s e with nextKind depth role s (forget e)
  ... | nothing = []
  ... | just t = t ∷ []

  -- Every enumerated successor is justified by the transition function.
  after-sound : ∀ {s e t} → t ∈ after s e → Step s e t
  after-sound {s} {e} m with nextKind depth role s (forget e)
  ... | nothing with () ← m
  ... | just t with m
  ...   | here refl = refl
  ...   | there ()

  -- Every successful transition appears in the successor list.
  after-complete : ∀ {s e t} → Step s e t → t ∈ after s e
  after-complete {s} {e} p with nextKind depth role s (forget e)
  ... | nothing with () ← p
  ... | just t with p
  ...   | refl = here refl

  -- The first-order instance for the bounded pipelined Notify wire language.
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

-- Embed the alternating table states into the bounded shutdown machine.
embed : Strict.St → St
embed Strict.idle = openN 0
embed Strict.busy = openN 1
embed Strict.quitting = quitting 0
embed Strict.closed = closed

-- Every alternating transition is also a depth-one pipelined transition.
strict-step : ∀ r s e t → Strict.nextKind r s e ≡ just t →
  nextKind 1 r (embed s) e ≡ just (embed t)
strict-step client Strict.idle (Send , request) _ refl = refl
strict-step client Strict.idle (Send , announcement) _ ()
strict-step client Strict.idle (Send , offer) _ ()
strict-step client Strict.idle (Send , txsOffer) _ ()
strict-step client Strict.idle (Send , votes) _ ()
strict-step client Strict.idle (Send , quit) _ refl = refl
strict-step client Strict.idle (Send , canceled) _ ()
strict-step client Strict.idle (Send , doneK) _ ()
strict-step client Strict.idle (Recv , request) _ ()
strict-step client Strict.idle (Recv , announcement) _ ()
strict-step client Strict.idle (Recv , offer) _ ()
strict-step client Strict.idle (Recv , txsOffer) _ ()
strict-step client Strict.idle (Recv , votes) _ ()
strict-step client Strict.idle (Recv , quit) _ ()
strict-step client Strict.idle (Recv , canceled) _ ()
strict-step client Strict.idle (Recv , doneK) _ ()
strict-step client Strict.busy (Send , request) _ ()
strict-step client Strict.busy (Send , announcement) _ ()
strict-step client Strict.busy (Send , offer) _ ()
strict-step client Strict.busy (Send , txsOffer) _ ()
strict-step client Strict.busy (Send , votes) _ ()
strict-step client Strict.busy (Send , quit) _ ()
strict-step client Strict.busy (Send , canceled) _ ()
strict-step client Strict.busy (Send , doneK) _ ()
strict-step client Strict.busy (Recv , request) _ ()
strict-step client Strict.busy (Recv , announcement) _ refl = refl
strict-step client Strict.busy (Recv , offer) _ refl = refl
strict-step client Strict.busy (Recv , txsOffer) _ refl = refl
strict-step client Strict.busy (Recv , votes) _ refl = refl
strict-step client Strict.busy (Recv , quit) _ ()
strict-step client Strict.busy (Recv , canceled) _ refl = refl
strict-step client Strict.busy (Recv , doneK) _ ()
strict-step client Strict.quitting (Send , request) _ ()
strict-step client Strict.quitting (Send , announcement) _ ()
strict-step client Strict.quitting (Send , offer) _ ()
strict-step client Strict.quitting (Send , txsOffer) _ ()
strict-step client Strict.quitting (Send , votes) _ ()
strict-step client Strict.quitting (Send , quit) _ ()
strict-step client Strict.quitting (Send , canceled) _ ()
strict-step client Strict.quitting (Send , doneK) _ ()
strict-step client Strict.quitting (Recv , request) _ ()
strict-step client Strict.quitting (Recv , announcement) _ ()
strict-step client Strict.quitting (Recv , offer) _ ()
strict-step client Strict.quitting (Recv , txsOffer) _ ()
strict-step client Strict.quitting (Recv , votes) _ ()
strict-step client Strict.quitting (Recv , quit) _ ()
strict-step client Strict.quitting (Recv , canceled) _ ()
strict-step client Strict.quitting (Recv , doneK) _ refl = refl
strict-step client Strict.closed (Send , request) _ ()
strict-step client Strict.closed (Send , announcement) _ ()
strict-step client Strict.closed (Send , offer) _ ()
strict-step client Strict.closed (Send , txsOffer) _ ()
strict-step client Strict.closed (Send , votes) _ ()
strict-step client Strict.closed (Send , quit) _ ()
strict-step client Strict.closed (Send , canceled) _ ()
strict-step client Strict.closed (Send , doneK) _ ()
strict-step client Strict.closed (Recv , request) _ ()
strict-step client Strict.closed (Recv , announcement) _ ()
strict-step client Strict.closed (Recv , offer) _ ()
strict-step client Strict.closed (Recv , txsOffer) _ ()
strict-step client Strict.closed (Recv , votes) _ ()
strict-step client Strict.closed (Recv , quit) _ ()
strict-step client Strict.closed (Recv , canceled) _ ()
strict-step client Strict.closed (Recv , doneK) _ ()
strict-step server Strict.idle (Send , request) _ ()
strict-step server Strict.idle (Send , announcement) _ ()
strict-step server Strict.idle (Send , offer) _ ()
strict-step server Strict.idle (Send , txsOffer) _ ()
strict-step server Strict.idle (Send , votes) _ ()
strict-step server Strict.idle (Send , quit) _ ()
strict-step server Strict.idle (Send , canceled) _ ()
strict-step server Strict.idle (Send , doneK) _ ()
strict-step server Strict.idle (Recv , request) _ refl = refl
strict-step server Strict.idle (Recv , announcement) _ ()
strict-step server Strict.idle (Recv , offer) _ ()
strict-step server Strict.idle (Recv , txsOffer) _ ()
strict-step server Strict.idle (Recv , votes) _ ()
strict-step server Strict.idle (Recv , quit) _ refl = refl
strict-step server Strict.idle (Recv , canceled) _ ()
strict-step server Strict.idle (Recv , doneK) _ ()
strict-step server Strict.busy (Send , request) _ ()
strict-step server Strict.busy (Send , announcement) _ refl = refl
strict-step server Strict.busy (Send , offer) _ refl = refl
strict-step server Strict.busy (Send , txsOffer) _ refl = refl
strict-step server Strict.busy (Send , votes) _ refl = refl
strict-step server Strict.busy (Send , quit) _ ()
strict-step server Strict.busy (Send , canceled) _ refl = refl
strict-step server Strict.busy (Send , doneK) _ ()
strict-step server Strict.busy (Recv , request) _ ()
strict-step server Strict.busy (Recv , announcement) _ ()
strict-step server Strict.busy (Recv , offer) _ ()
strict-step server Strict.busy (Recv , txsOffer) _ ()
strict-step server Strict.busy (Recv , votes) _ ()
strict-step server Strict.busy (Recv , quit) _ ()
strict-step server Strict.busy (Recv , canceled) _ ()
strict-step server Strict.busy (Recv , doneK) _ ()
strict-step server Strict.quitting (Send , request) _ ()
strict-step server Strict.quitting (Send , announcement) _ ()
strict-step server Strict.quitting (Send , offer) _ ()
strict-step server Strict.quitting (Send , txsOffer) _ ()
strict-step server Strict.quitting (Send , votes) _ ()
strict-step server Strict.quitting (Send , quit) _ ()
strict-step server Strict.quitting (Send , canceled) _ ()
strict-step server Strict.quitting (Send , doneK) _ refl = refl
strict-step server Strict.quitting (Recv , request) _ ()
strict-step server Strict.quitting (Recv , announcement) _ ()
strict-step server Strict.quitting (Recv , offer) _ ()
strict-step server Strict.quitting (Recv , txsOffer) _ ()
strict-step server Strict.quitting (Recv , votes) _ ()
strict-step server Strict.quitting (Recv , quit) _ ()
strict-step server Strict.quitting (Recv , canceled) _ ()
strict-step server Strict.quitting (Recv , doneK) _ ()
strict-step server Strict.closed (Send , request) _ ()
strict-step server Strict.closed (Send , announcement) _ ()
strict-step server Strict.closed (Send , offer) _ ()
strict-step server Strict.closed (Send , txsOffer) _ ()
strict-step server Strict.closed (Send , votes) _ ()
strict-step server Strict.closed (Send , quit) _ ()
strict-step server Strict.closed (Send , canceled) _ ()
strict-step server Strict.closed (Send , doneK) _ ()
strict-step server Strict.closed (Recv , request) _ ()
strict-step server Strict.closed (Recv , announcement) _ ()
strict-step server Strict.closed (Recv , offer) _ ()
strict-step server Strict.closed (Recv , txsOffer) _ ()
strict-step server Strict.closed (Recv , votes) _ ()
strict-step server Strict.closed (Recv , quit) _ ()
strict-step server Strict.closed (Recv , canceled) _ ()
strict-step server Strict.closed (Recv , doneK) _ ()

-- Lift alternating traces without asserting a converse for busy-state Quit.
lift-one : ∀ {r s t es} → Strict.Spec._⇒⟨_⟩_ r s es t →
           Spec._⇒⟨_⟩_ 1 r (embed s) es (embed t)
lift-one {r} Strict.Spec.done = Spec.done {depth = 1} {role = r}
lift-one (Strict.Spec.tau () _)
lift-one {r} {s} (Strict.Spec.vis {s′ = t} {e = e} st p) =
  Spec.vis {depth = 1} {role = r} (strict-step r s (forget e) t st) (lift-one {r = r} p)

-- Alternating traces are included; pipelined Quit prevents whole-language equality.
strict-into-pipeline : ∀ r es → Strict.Spec.HasTrace r Strict.idle es → Spec.HasTrace 1 r idle es
strict-into-pipeline r es (t , run) = embed t , lift-one {r = r} run
