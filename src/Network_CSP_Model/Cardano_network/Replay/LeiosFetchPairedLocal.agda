{-# OPTIONS --safe #-}

-- Deterministic wire transitions with the unlogged server serve step normalized.
open import Data.Nat using (ℕ)
module Cardano_network.Replay.LeiosFetchPairedLocal (k : ℕ) where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function.Bundles using (_⇔_; mk⇔)
open import Data.Product using (∃; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import Cardano_network.Replay.Common using (Role)
open import Cardano_network.Replay.LeiosFetchSession
open Spec k
open import Semantics.Replay using (module Traces)
module Local = Traces leiosFetch

-- Serving is the only silent action, and never changes a retained message field.
normal : St → St
normal (sBusy r) = sReady r
normal s = s

-- Normalization is idempotent, including the already-ready server state.
normal-idem : ∀ s → normal (normal s) ≡ normal s
normal-idem (cOpen _) = refl
normal-idem cClosed = refl
normal-idem sIdle = refl
normal-idem (sBusy _) = refl
normal-idem (sReady _) = refl
normal-idem sClosed = refl

-- A finite invisible suffix realizes normalization in the original replay model.
settle : ∀ s → Local._⇒⟨_⟩_ s [] (normal s)
settle (cOpen _) = Local.done
settle cClosed = Local.done
settle sIdle = Local.done
settle (sBusy _) = Local.tau sServe Local.done
settle (sReady _) = Local.done
settle sClosed = Local.done

-- The original visible relation has at most one target for a fixed state/event.
unique : ∀ {s e t u} → s -[ e ]→ t → s -[ e ]→ u → t ≡ u
unique (cSendBlockReq _) (cSendBlockReq _) = refl
unique (cSendTxsReq _) (cSendTxsReq _) = refl
unique cRecvBlock cRecvBlock = refl
unique cRecvTxs cRecvTxs = refl
unique cSendDone cSendDone = refl
unique sRecvBlockReq sRecvBlockReq = refl
unique sRecvTxsReq sRecvTxsReq = refl
unique sSendBlock sSendBlock = refl
unique sSendTxs sSendTxs = refl
unique sRecvDone sRecvDone = refl

-- No visible step originates at sBusy, so normalizing its source preserves steps.
normal-step : ∀ {s e t} → s -[ e ]→ t → normal s -[ e ]→ t
normal-step p@(cSendBlockReq _) = p
normal-step p@(cSendTxsReq _) = p
normal-step p@cRecvBlock = p
normal-step p@cRecvTxs = p
normal-step cSendDone = cSendDone
normal-step sRecvBlockReq = sRecvBlockReq
normal-step sRecvTxsReq = sRecvTxsReq
normal-step sSendBlock = sSendBlock
normal-step sSendTxs = sSendTxs
normal-step sRecvDone = sRecvDone

-- Select the normalized target of the certified visible-successor enumeration.
choose : ∀ {s e} → List (∃ (s -[ e ]→_)) → Maybe St
choose [] = nothing
choose ((t , _) ∷ _) = just (normal t)

-- Each chosen successor has a visible derivation followed by permitted serving.
choose-sound : ∀ {s e t} (xs : List (∃ (s -[ e ]→_))) → choose xs ≡ just t →
  Local._⇒⟨_⟩_ s (e ∷ []) t
choose-sound [] ()
choose-sound ((t , p) ∷ _) refl = Local.vis p (settle t)

-- Determinism ensures that choosing the head loses no visible successor.
choose-complete : ∀ {s e t} (xs : List (∃ (s -[ e ]→_))) → s -[ e ]→ t →
  t ∈ map proj₁ xs → choose xs ≡ just (normal t)
choose-complete [] _ ()
choose-complete ((u , q) ∷ _) p _ = cong (λ x → just (normal x)) (unique q p)

-- Role is determined by the disjoint client/server states and their fresh starts.
next : Role → St → E → Maybe St
next _ s e = choose (steps (normal s) e)

-- A macro step expands to the original weak visible trace, including server τ.
next-sound : ∀ {r s e t} → next r s e ≡ just t →
  Local._⇒⟨_⟩_ (normal s) (e ∷ []) t
next-sound {s = s} {e} = choose-sound (steps (normal s) e)

-- Every original visible step is represented between normalized states.
next-complete : ∀ {r s e t} → s -[ e ]→ t → next r s e ≡ just (normal t)
next-complete {s = s} {e} p = choose-complete (steps (normal s) e)
  (normal-step p) (after-complete (normal-step p))

-- The sole original silent transition becomes equality under normalization.
tau-normal : ∀ {s t} → s -τ→ t → normal s ≡ normal t
tau-normal sServe = refl

-- Every successful macro target is normalized; paired states stay canonical.
choose-normal : ∀ {s e t} (xs : List (∃ (s -[ e ]→_))) → choose xs ≡ just t → normal t ≡ t
choose-normal [] ()
choose-normal ((t , _) ∷ _) refl = normal-idem t

-- The invariant lets consecutive macro expansions join in the original model.
next-normal : ∀ {r s e t} → next r s e ≡ just t → normal t ≡ t
next-normal {s = s} {e} = choose-normal (steps (normal s) e)

-- Running from an already-normalized state makes no further change to next.
normal-next : ∀ r s e → next r (normal s) e ≡ next r s e
normal-next r s e = cong (λ u → choose (steps u e)) (normal-idem s)

-- Finite runs of the deterministic macro machine retain the full wire alphabet.
data Run (r : Role) : St → List E → St → Set where
  finish : ∀ {s} → Run r s [] s
  visible : ∀ {s e t es u} → next r s e ≡ just t → Run r t es u → Run r s (e ∷ es) u

-- Every original weak run maps to a macro run; serving becomes invisible equality.
lower : ∀ {r s es t} → Local._⇒⟨_⟩_ s es t → Run r (normal s) es (normal t)
lower Local.done = finish
lower (Local.tau sServe run) = lower run
lower {r} {s} (Local.vis {e = e} p run) = visible
  (trans (normal-next r s e) (next-complete {r = r} p)) (lower run)

-- Every macro run expands to an original weak run between normalized states.
lift : ∀ {r s es t} → Run r s es t → Local._⇒⟨_⟩_ (normal s) es (normal t)
lift finish = Local.done
lift {r} {s} (visible p run) = Local.⇒-++ (next-sound {r = r} {s = s} p)
  (subst (λ u → Local._⇒⟨_⟩_ u _ _)
    (next-normal {r = r} {s = s} p) (lift run))

-- Normalization preserves exactly the original weak visible language, for either role.
wire-language : ∀ r s es → Local.HasTrace s es ⇔ (∃ (Run r (normal s) es))
wire-language r s es = mk⇔
  (λ { (t , run) → normal t , lower {r = r} run })
  (λ { (t , run) → normal t , Local.⇒-++ (settle s)
    (subst (λ u → Local._⇒⟨_⟩_ u es (normal t))
      (normal-idem s) (lift run)) })
