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
         request; announcement; offer; txsOffer; votes; doneK;
         Observed; forget; dirEq; msgEq)
import Cardano_network.Replay.LeiosNotifySession as Strict

-- An open session counts outstanding requests; a closed session offers nothing.
data St : Set where
  openN : ℕ → St
  closed : St

-- Every generation begins with no outstanding requests.
idle : St
idle = openN 0

-- Issue only below the bound; zero disables requests but permits idle Done.
issue : ℕ → ℕ → Maybe St
issue depth n with n <ᵇ depth
... | true = just (openN (suc n))
... | false = nothing

-- Any of the four notification kinds consumes exactly one request credit.
reply : ℕ → Kind → Maybe St
reply (suc n) announcement = just (openN n)
reply (suc n) offer = just (openN n)
reply (suc n) txsOffer = just (openN n)
reply (suc n) votes = just (openN n)
reply _ _ = nothing

-- Request and Done have initiator agency; notifications have responder agency.
nextKind : ℕ → Role → St → Observed → Maybe St
nextKind depth client (openN n) (Send , request) = issue depth n
nextKind depth server (openN n) (Recv , request) = issue depth n
nextKind depth client (openN zero) (Send , doneK) = just closed
nextKind depth server (openN zero) (Recv , doneK) = just closed
nextKind depth client (openN n) (Recv , k) = reply n k
nextKind depth server (openN n) (Send , k) = reply n k
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

-- Embed the original depth-one peer states into the credit-counting model.
embed : Strict.St → St
embed Strict.idle = openN 0
embed Strict.busy = openN 1
embed Strict.closed = closed

-- At depth one, every embedded transition agrees with the original machine.
depth-one-step : ∀ r s e → nextKind 1 r (embed s) e ≡ map embed (Strict.nextKind r s e)
depth-one-step client Strict.idle (Send , request) = refl
depth-one-step client Strict.idle (Send , announcement) = refl
depth-one-step client Strict.idle (Send , offer) = refl
depth-one-step client Strict.idle (Send , txsOffer) = refl
depth-one-step client Strict.idle (Send , votes) = refl
depth-one-step client Strict.idle (Send , doneK) = refl
depth-one-step client Strict.idle (Recv , request) = refl
depth-one-step client Strict.idle (Recv , announcement) = refl
depth-one-step client Strict.idle (Recv , offer) = refl
depth-one-step client Strict.idle (Recv , txsOffer) = refl
depth-one-step client Strict.idle (Recv , votes) = refl
depth-one-step client Strict.idle (Recv , doneK) = refl
depth-one-step client Strict.busy (Send , request) = refl
depth-one-step client Strict.busy (Send , announcement) = refl
depth-one-step client Strict.busy (Send , offer) = refl
depth-one-step client Strict.busy (Send , txsOffer) = refl
depth-one-step client Strict.busy (Send , votes) = refl
depth-one-step client Strict.busy (Send , doneK) = refl
depth-one-step client Strict.busy (Recv , request) = refl
depth-one-step client Strict.busy (Recv , announcement) = refl
depth-one-step client Strict.busy (Recv , offer) = refl
depth-one-step client Strict.busy (Recv , txsOffer) = refl
depth-one-step client Strict.busy (Recv , votes) = refl
depth-one-step client Strict.busy (Recv , doneK) = refl
depth-one-step client Strict.closed (Send , request) = refl
depth-one-step client Strict.closed (Send , announcement) = refl
depth-one-step client Strict.closed (Send , offer) = refl
depth-one-step client Strict.closed (Send , txsOffer) = refl
depth-one-step client Strict.closed (Send , votes) = refl
depth-one-step client Strict.closed (Send , doneK) = refl
depth-one-step client Strict.closed (Recv , request) = refl
depth-one-step client Strict.closed (Recv , announcement) = refl
depth-one-step client Strict.closed (Recv , offer) = refl
depth-one-step client Strict.closed (Recv , txsOffer) = refl
depth-one-step client Strict.closed (Recv , votes) = refl
depth-one-step client Strict.closed (Recv , doneK) = refl
depth-one-step server Strict.idle (Send , request) = refl
depth-one-step server Strict.idle (Send , announcement) = refl
depth-one-step server Strict.idle (Send , offer) = refl
depth-one-step server Strict.idle (Send , txsOffer) = refl
depth-one-step server Strict.idle (Send , votes) = refl
depth-one-step server Strict.idle (Send , doneK) = refl
depth-one-step server Strict.idle (Recv , request) = refl
depth-one-step server Strict.idle (Recv , announcement) = refl
depth-one-step server Strict.idle (Recv , offer) = refl
depth-one-step server Strict.idle (Recv , txsOffer) = refl
depth-one-step server Strict.idle (Recv , votes) = refl
depth-one-step server Strict.idle (Recv , doneK) = refl
depth-one-step server Strict.busy (Send , request) = refl
depth-one-step server Strict.busy (Send , announcement) = refl
depth-one-step server Strict.busy (Send , offer) = refl
depth-one-step server Strict.busy (Send , txsOffer) = refl
depth-one-step server Strict.busy (Send , votes) = refl
depth-one-step server Strict.busy (Send , doneK) = refl
depth-one-step server Strict.busy (Recv , request) = refl
depth-one-step server Strict.busy (Recv , announcement) = refl
depth-one-step server Strict.busy (Recv , offer) = refl
depth-one-step server Strict.busy (Recv , txsOffer) = refl
depth-one-step server Strict.busy (Recv , votes) = refl
depth-one-step server Strict.busy (Recv , doneK) = refl
depth-one-step server Strict.closed (Send , request) = refl
depth-one-step server Strict.closed (Send , announcement) = refl
depth-one-step server Strict.closed (Send , offer) = refl
depth-one-step server Strict.closed (Send , txsOffer) = refl
depth-one-step server Strict.closed (Send , votes) = refl
depth-one-step server Strict.closed (Send , doneK) = refl
depth-one-step server Strict.closed (Recv , request) = refl
depth-one-step server Strict.closed (Recv , announcement) = refl
depth-one-step server Strict.closed (Recv , offer) = refl
depth-one-step server Strict.closed (Recv , txsOffer) = refl
depth-one-step server Strict.closed (Recv , votes) = refl
depth-one-step server Strict.closed (Recv , doneK) = refl

-- Lift strict depth-one traces through the state embedding.
lift-one : ∀ {r s t es} → Strict.Spec._⇒⟨_⟩_ r s es t →
           Spec._⇒⟨_⟩_ 1 r (embed s) es (embed t)
lift-one {r} Strict.Spec.done = Spec.done {depth = 1} {role = r}
lift-one (Strict.Spec.tau () _)
lift-one {r} {s} (Strict.Spec.vis {e = e} st p) =
  Spec.vis {depth = 1} {role = r}
    (trans (depth-one-step r s (forget e)) (cong (map embed) st)) (lift-one {r = r} p)

-- A successful mapped optional state exposes its strict predecessor state.
unmap-state : ∀ m {t} → map embed m ≡ just t →
              Σ[ u ∈ Strict.St ] (m ≡ just u × embed u ≡ t)
unmap-state nothing ()
unmap-state (just u) refl = u , refl , refl

-- Every depth-one run from an embedded state remains in the strict language.
lower-one : ∀ {r t es} (s : Strict.St) → Spec._⇒⟨_⟩_ 1 r (embed s) es t →
            Strict.Spec.HasTrace r s es
lower-one {r} s Spec.done = s , Strict.Spec.done {role = r}
lower-one s (Spec.tau () _)
lower-one {r} s (Spec.vis {e = e} st p)
  with unmap-state (Strict.nextKind r s (forget e)) (trans (sym (depth-one-step r s (forget e))) st)
... | u , q , refl with lower-one {r = r} u p
...   | v , run = v , Strict.Spec.vis {role = r} q run

-- Exact trace equivalence preserves the original peer bridge's depth-one scope.
depth-one-traces : ∀ r es → Strict.Spec.HasTrace r Strict.idle es ⇔ Spec.HasTrace 1 r idle es
depth-one-traces r es = mk⇔
  (λ { (t , run) → embed t , lift-one {r = r} run })
  (λ { (t , run) → lower-one {r = r} Strict.idle run })
