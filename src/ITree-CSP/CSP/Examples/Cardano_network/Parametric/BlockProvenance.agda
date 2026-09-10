{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — BLOCK PROVENANCE AS A PAYLOAD INVARIANT: the
-- assume-guarantee carrier `Wf`, and its congruences.
--
-- `Parametric.AnnounceSafeCarrier.Safe` demands `gate` — "every block
-- announced is well-announced" — of a process, and its congruences pass
-- `gate` DOWN to the operand that announced.  At the leaves that is
-- unprovable: `lnServerLoop` announces whatever block the store hands it,
-- the store holds whatever the client thread deposits, and the client
-- thread deposits whatever the BlockFetch client peer pins, which pins
-- whatever the medium delivered, which delivered whatever the far node's
-- server peer put on the wire.  Every one of those components is a RELAY:
-- it re-emits, in one step and from a register that outlives no prefix, a
-- value it just received.  The invariant therefore has to be stated as an
-- assume-guarantee pair on the block-carrying channels — "every block I
-- emit is well-announced, PROVIDED every block I was handed was" — and
-- closed around the loop.
--
-- WHY NO WELL-FOUNDED MEASURE.  The spec's minted set `ms` is GLOBAL, so
-- the rely of one component and the guarantee of the component that pins
-- the value are the SAME predicate `WellAnnounced ms` at the SAME index.
-- Assume-guarantee for a safety property then collapses to a plain
-- step-preserved invariant: the parallel congruence discharges the rely of
-- one operand with the guarantee of the other AT THE SAME STEP, and guarded
-- coinduction over the LTS is the whole induction.  The only SOURCE of
-- blocks — the store's mint clause — is already guarded by exactly
-- `WellAnnounced (mintedAfter mb ms) b` (`NodeLogic.acceptMint`), so the
-- seed is free.
--
-- THE CARRIER IS GENERIC.  `Carrier` below is parametric in the alphabet,
-- the state, the "which label carries which value" relation and the
-- per-state payload predicate, and depends on nothing Cardano-specific.
-- That is what the RENAMING congruence needs: the BlockFetch peers are
-- `renameMap`s of processes over `BFEv`, and their `Wf` fact is proved at
-- the SOURCE alphabet and transported — which takes TWO instances of the
-- carrier, so the carrier cannot be tied to `Net_Api`.  `Generic` at the
-- bottom is the Cardano instance.
--
-- TWO DEPARTURES FROM THE SKETCH THIS MODULE IMPLEMENTS.
--
--   * The sketch's `wf-Par : Wf G₁ P → Wf G₂ Q → Wf (G₁ ∪ G₂) (P ∥⇘ A ⇙ Q)`
--     is FALSE as stated: a label in `G₂ ∖ G₁` performed SOLO by `P` has no
--     guarantee anywhere (take `P = stGet ! bad ⟶ Stop` with `G₁ = ∅`).
--     `Sep` below is the alphabet-level side condition that excludes it —
--     OUTSIDE the synchronisation set the two guarantee alphabets must agree
--     on block-carrying labels.  It replaces the sketch's `CoversSync`,
--     which addressed a case that does not arise (the composite's `stepW`
--     RECEIVES the `BlockOK` of a synchronised label; nobody has to derive
--     it).  `Sep` is discharged by the alphabet discipline "a component's
--     guarantee alphabet is every block-carrying label except its own
--     relies, and a rely is always a synchronised input".
--
--   * `Wf` is CLOSED UPWARD IN THE STATE BY DEFINITION: both fields
--     quantify over every `s′ ≥ s`.  Monotonicity in the minted set is
--     FALSE for a naive rely-guarantee predicate (a process that checks its
--     input against a hard-coded `ms` is well-formed at `ms` and at no
--     superset), yet the parallel congruence needs it for the operand that
--     did NOT take part in a mint.  Building the closure into the record
--     makes `wf-mono` a two-line projection and costs the relay leaves
--     nothing — their registers are `WellAnnounced` at every superset by
--     `wellAnnounced-mono`.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.BlockProvenance where

open import Level using (Level; 0ℓ; _⊔_; lift) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (PTree; ptree; react; AnyTypes; ExtI; base; pair; fin; deadlock)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import Semantics.LTS as LTS
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
import CSP.Examples.Cardano_network.Parametric.AnnounceInvariant as AI

------------------------------------------------------------------------
-- The generic carrier
------------------------------------------------------------------------

-- the carrier, parametric in the alphabet `E`, the global state `S` (the spec's
-- minted set), the payload type `B` (blocks), the relation `Carries at a b` — "the
-- visible event `a` on channel `at` carries the value `b`" — the per-state payload
-- predicate `WA` (well-announced), the state update `next` a label performs (a mint
-- grows the minted set; everything else keeps it), and the growth order `_≤_`
module Carrier {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  (S B : Set)
  (Carries : (at : AnyTypes E) → proj₁ at → B → Set)
  (WA      : S → B → Set)
  (next    : LTS.Label {E = E} {I = ExtI E} (⊤ {0ℓ}) → S → S)
  (_≤_     : S → S → Set)
  (≤-trans : ∀ {s₁ s₂ s₃} → s₁ ≤ s₂ → s₂ ≤ s₃ → s₁ ≤ s₃)
  (next-≤  : ∀ a s → s ≤ next a s) where

  open O {E = E} E-≟
    using ( EventSet; ∅ES; Par; par-brBoth; _⦀_; _∥⇘_⇙_; _∖_; ⦀Fin; ⦀Fin⁺; ⦀⋆; Skip
          ; _△_; △-br2; ∅v )
  open import Semantics.LTS {E = E} {I = ExtI E}
    using (Label; ev; τ; evl; √; evLabel; _─[_]─►_; sRet; sSil; sVis; sTau)
  open import CSP.Laws.Bisim.DRCongruenceRep E-≟ using (Alpha)
  open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
    using (Par-τ-elim; τL; τR; Par-ev-elim; evSync; evL; evR; evBoth; ev√)
  open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
    using (brBoth-τ-elim; brBoth-no-ev; deadlock-no-τ; deadlock-no-ev)
  open import CSP.Laws.Traces.TraceLawsHide E-≟
    using (Hide-τ-elim; hτP; hτH; Hide-ev-elim; heV; he√)
  open import CSP.Laws.Traces.TraceLawsThrowInterrupt E-≟
    using ( △-τ-elim; △τP; △τQ; △τQret; △τ⊓P; △τ⊓Q
          ; △-ev-elim; △evP; △evQ; △evPQ )

  -- the processes the carrier is about: unit-returning trees over `E`
  Proc : Set (lsuc ℓ ⊔ ℓe)
  Proc = PTree E (ExtI E) (⊤ {0ℓ})

  -- the visible label of the event `a` on channel `e`
  lbl : ∀ {X} → E X → X → Label (⊤ {0ℓ})
  lbl {X} e a = ev (evl (evLabel X e a))

  ------------------------------------------------------------------------
  -- The label predicate
  ------------------------------------------------------------------------

  -- `OK s a`: whatever value the label `a` carries on a constrained channel satisfies
  -- the payload predicate at `s`.  τ and `√` carry nothing; a visible event on an
  -- unconstrained channel is trivially `OK` by the absence of a `Carries` witness.
  OK : S → Label (⊤ {0ℓ}) → Set
  OK s (ev (evl (evLabel X e a))) = ∀ {b} → Carries (X , e) a b → WA s b
  OK s _                          = ⊤

  ------------------------------------------------------------------------
  -- The carrier
  ------------------------------------------------------------------------

  -- `Wf G s M`: at every state `s′ ≥ s`, `M` GUARANTEES `OK s′` on every label of the
  -- alphabet `G` it can perform, and — given that the label it just performed was
  -- `OK s′` (the RELY: for a label outside `G` this is the hypothesis a receiving
  -- component lives on; for one inside `G` it is redundant) — every successor is
  -- well-formed at the state the label leads to.
  record Wf (G : Alpha) (s : S) (M : Proc) : Set (lsuc ℓ ⊔ ℓe) where
    coinductive
    field
      nowW  : ∀ {s′} → s ≤ s′ → ∀ {X} {e : E X} {a : X} {M′}
            → G (X , e) a → M ─[ lbl e a ]─► M′ → OK s′ (lbl e a)
      stepW : ∀ {s′} → s ≤ s′ → ∀ {a M′}
            → M ─[ a ]─► M′ → OK s′ a → Wf G (next a s′) M′
  open Wf public

  ------------------------------------------------------------------------
  -- Monotonicity
  ------------------------------------------------------------------------

  -- growing the state: the upward closure is built into both fields, so this is a
  -- projection, not a corecursion
  wf-mono : ∀ {G s s′ M} → s ≤ s′ → Wf G s M → Wf G s′ M
  wf-mono le w .nowW  le′ g st   = nowW  w (≤-trans le le′) g st
  wf-mono le w .stepW le′ st ok  = stepW w (≤-trans le le′) st ok

  -- shrinking the guarantee alphabet WEAKENS `nowW`, so `Wf` is anti-monotone in `G`
  wf-mono-G : ∀ {G G′ s M} → (∀ at a → G′ at a → G at a) → Wf G s M → Wf G′ s M
  wf-mono-G f w .nowW  le g st  = nowW w le (f _ _ g) st
  wf-mono-G f w .stepW le st ok = wf-mono-G f (stepW w le st ok)

  -- the deadlocked tree performs nothing, so it is well-formed on any alphabet at any
  -- state.  It is where `Par` and `∖` land after a `√`, so `Wf` — unlike `Safe` —
  -- carries no `noTick` obligation and holds of terminating peers too.
  wf-deadlock : ∀ {G s} → Wf G s deadlock
  wf-deadlock .nowW  _ _ st          = ⊥-elim (deadlock-no-ev st)
  wf-deadlock .stepW _ {a = τ}    st _ = ⊥-elim (deadlock-no-τ st)
  wf-deadlock .stepW _ {a = ev _} st _ = ⊥-elim (deadlock-no-ev st)

  -- `Skip` offers nothing and terminates at once, into `deadlock` — the filler of an
  -- unconfigured slot in a peer bundle
  wf-Skip : ∀ {G s} → Wf G s Skip
  wf-Skip .nowW  _ _ (sVis () _)
  wf-Skip .stepW _ (sRet _) _ = wf-deadlock
  wf-Skip .stepW _ (sSil ())
  wf-Skip .stepW _ (sVis () _)
  wf-Skip .stepW _ (sTau () _)

  ------------------------------------------------------------------------
  -- The parallel congruence
  ------------------------------------------------------------------------

  -- the union of two guarantee alphabets
  _∪α_ : Alpha → Alpha → Alpha
  (G₁ ∪α G₂) at a = G₁ at a ⊎ G₂ at a

  -- THE SIDE CONDITION OF PARALLEL: outside the synchronisation set the two guarantee
  -- alphabets agree on every block-carrying label.  A label one operand performs
  -- SOLO is guaranteed by that operand alone, so if it lies in the OTHER operand's
  -- alphabet it had better lie in the performer's too.  Quantifying over `Carries`
  -- rather than over all labels keeps the discharge a case split on the handful of
  -- block-carrying channel shapes, not on the whole alphabet.
  Sep : EventSet → Alpha → Alpha → Set (lsuc ℓ ⊔ ℓe)
  Sep A G₁ G₂ =
      (∀ {X} {e : E X} {a : X} {b} → Carries (X , e) a b
         → G₁ (X , e) a → ¬ EventSet.mem A (X , e) a → G₂ (X , e) a)
    × (∀ {X} {e : E X} {a : X} {b} → Carries (X , e) a b
         → G₂ (X , e) a → ¬ EventSet.mem A (X , e) a → G₁ (X , e) a)

  -- THE PARALLEL CONGRUENCE, and its collision companion, mutually corecursive — the
  -- shape of `AnnounceSafeCarrier.safe-Par`/`safe-both`.
  --
  -- `nowW`: a synchronised label is guaranteed by whichever operand's alphabet the
  -- caller's membership witness names; a solo label by its performer, with `Sep`
  -- rerouting a witness that names the other operand.  `stepW`: the `OK` of the
  -- label taken is handed to EVERY operand that took it — this is the assume-
  -- guarantee discharge, one argument, no measure — and an operand that stood still
  -- is carried to the new state by `wf-mono`, which is where the upward closure of
  -- `Wf` earns its keep.
  wf-Par  : ∀ {G₁ G₂ s} (A : EventSet) → Sep A G₁ G₂ → ∀ {P Q}
          → Wf G₁ s P → Wf G₂ s Q → Wf (G₁ ∪α G₂) s (P ∥⇘ A ⇙ Q)
  wf-both : ∀ {G₁ G₂ s} (A : EventSet) → Sep A G₁ G₂ → ∀ {P Q P′ Q′}
          → Wf G₁ s P → Wf G₂ s Q → Wf G₁ s P′ → Wf G₂ s Q′
          → Wf (G₁ ∪α G₂) s (ptree (react (λ _ _ → nothing)
                                    (par-brBoth A (λ _ _ → tt) P Q P′ Q′)))

  wf-Par A sep {P} {Q} wP wQ .nowW le (inj₁ g₁) st with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | evSync _  stP _   = nowW wP le g₁ stP
  ... | evL    _  stP     = nowW wP le g₁ stP
  ... | evR    ¬m stQ     = λ c → nowW wQ le (proj₁ sep c g₁ ¬m) stQ c
  ... | evBoth _  stP _   = nowW wP le g₁ stP
  wf-Par A sep {P} {Q} wP wQ .nowW le (inj₂ g₂) st with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | evSync _  _   stQ = nowW wQ le g₂ stQ
  ... | evL    ¬m stP     = λ c → nowW wP le (proj₂ sep c g₂ ¬m) stP c
  ... | evR    _  stQ     = nowW wQ le g₂ stQ
  ... | evBoth _  _   stQ = nowW wQ le g₂ stQ
  -- a τ of the composite is a τ of one operand; the other stands still
  wf-Par A sep {P} {Q} wP wQ .stepW {s′} le {a = τ} st ok
    with Par-τ-elim A (λ _ _ → tt) P Q st
  ... | τL P′ stP refl = wf-Par A sep (stepW wP le stP ok)
                                      (wf-mono (≤-trans le (next-≤ τ s′)) wQ)
  ... | τR Q′ stQ refl = wf-Par A sep (wf-mono (≤-trans le (next-≤ τ s′)) wP)
                                      (stepW wQ le stQ ok)
  -- a visible label: every operand that took it gets its `OK`
  wf-Par A sep {P} {Q} wP wQ .stepW {s′} le {a = ev (evl _)} st ok
    with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | evSync _ stP stQ = wf-Par A sep (stepW wP le stP ok) (stepW wQ le stQ ok)
  ... | evL    _ stP     = wf-Par A sep (stepW wP le stP ok)
                                        (wf-mono (≤-trans le (next-≤ _ s′)) wQ)
  ... | evR    _ stQ     = wf-Par A sep (wf-mono (≤-trans le (next-≤ _ s′)) wP)
                                        (stepW wQ le stQ ok)
  ... | evBoth _ stP stQ = wf-both A sep (wf-mono (≤-trans le (next-≤ _ s′)) wP)
                                         (wf-mono (≤-trans le (next-≤ _ s′)) wQ)
                                         (stepW wP le stP ok) (stepW wQ le stQ ok)
  -- a joint `√` lands in `deadlock`
  wf-Par A sep {P} {Q} wP wQ .stepW le {a = ev (√ _)} st ok
    with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | ev√ _ _ = wf-deadlock

  -- the collision node offers no visible event; its two committing τ's land back in
  -- `wf-Par`
  wf-both A sep {P} {Q} {P′} {Q′} wP wQ wP′ wQ′ .nowW _ _ st =
    ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
  wf-both A sep {P} {Q} {P′} {Q′} wP wQ wP′ wQ′ .stepW {s′} le {a = τ} st _
    with brBoth-τ-elim A (λ _ _ → tt) P Q P′ Q′ st
  ... | inj₁ refl = wf-Par A sep (wf-mono (≤-trans le (next-≤ τ s′)) wP′)
                                 (wf-mono (≤-trans le (next-≤ τ s′)) wQ)
  ... | inj₂ refl = wf-Par A sep (wf-mono (≤-trans le (next-≤ τ s′)) wP)
                                 (wf-mono (≤-trans le (next-≤ τ s′)) wQ′)
  wf-both A sep {P} {Q} {P′} {Q′} wP wQ wP′ wQ′ .stepW _ {a = ev _} st _ =
    ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)

  ------------------------------------------------------------------------
  -- Interleaving and its replicated form
  ------------------------------------------------------------------------

  -- INTERLEAVING of two operands on the SAME guarantee alphabet: nothing is
  -- synchronised, so `Sep` is the identity, and the union collapses back to `G`
  wf-⦀ : ∀ {G s P Q} → Wf G s P → Wf G s Q → Wf G s (P ⦀ Q)
  wf-⦀ wP wQ =
    wf-mono-G (λ _ _ → inj₁) (wf-Par ∅ES ((λ _ g _ → g) , (λ _ g _ → g)) wP wQ)

  -- REPLICATED INTERLEAVING: `⦀Fin⁺ (suc n) f = f fzero ⦀ ⦀Fin⁺ n (f ∘ fsuc)` is
  -- definitional, so this is plain `Fin` recursion on top of `wf-⦀`
  wf-⦀Fin⁺ : ∀ {G s} (n : ℕ) {f : Fin (suc n) → Proc}
           → (∀ i → Wf G s (f i)) → Wf G s (⦀Fin⁺ n f)
  wf-⦀Fin⁺ zero            h = h fzero
  wf-⦀Fin⁺ (suc n) {f = f} h =
    wf-⦀ (h fzero) (wf-⦀Fin⁺ n {f = λ i → f (fsuc i)} (λ i → h (fsuc i)))

  -- the list form over a mapped list (`⦀⋆ [] = Skip`): the shape of a configured
  -- peer bundle
  wf-⦀⋆ : ∀ {ℓa} {A : Set ℓa} {G s} (f : A → Proc) (xs : List A)
        → (∀ x → Wf G s (f x)) → Wf G s (⦀⋆ (map f xs))
  wf-⦀⋆ f []       h = wf-Skip
  wf-⦀⋆ f (x ∷ xs) h = wf-⦀ (h x) (wf-⦀⋆ f xs h)

  -- the POSSIBLY-EMPTY replicated form (`⦀Fin zero f = Skip`): the shape of the
  -- medium, one breakable cell per link
  wf-⦀Fin : ∀ {G s} (n : ℕ) {f : Fin n → Proc}
          → (∀ i → Wf G s (f i)) → Wf G s (⦀Fin n f)
  wf-⦀Fin zero            h = wf-Skip
  wf-⦀Fin (suc n) {f = f} h =
    wf-⦀ (h fzero) (wf-⦀Fin n {f = λ i → f (fsuc i)} (λ i → h (fsuc i)))

  ------------------------------------------------------------------------
  -- The interrupt congruence
  ------------------------------------------------------------------------

  -- THE INTERRUPT CONGRUENCE, and its both-offer companion, mutually corecursive
  -- (the shape of `DRCongruenceRep.OffersOnly-△`).  Nothing is synchronised, so
  -- both operands live on ONE alphabet and no `Sep` arises: a visible step of
  -- `P △ Q` is one operand's own step (`△-ev-elim`), guaranteed by that operand,
  -- which alone receives its `OK`; the other stands still and is carried to the
  -- new state by `wf-mono`.  The τ's that resolve the P⊓Q node (`P` terminated)
  -- and the √-interrupt (`Q` terminated) land on a bare operand.
  wf-△     : ∀ {G s P Q} → Wf G s P → Wf G s Q → Wf G s (P △ Q)
  -- the both-offer node `(P₁ △ Q) ⊓ Q₁` a visible event offered by BOTH operands
  -- produces: no visible offer, two committing τ's
  wf-△-br2 : ∀ {G s P₁ Q Q₁} → Wf G s P₁ → Wf G s Q → Wf G s Q₁
           → Wf G s (ptree (react ∅v (△-br2 P₁ Q Q₁)))

  wf-△ {P = P} {Q = Q} wP wQ .nowW le g st with △-ev-elim P Q st
  ... | △evP  stP   = nowW wP le g stP
  ... | △evQ  stQ   = nowW wQ le g stQ
  ... | △evPQ stP _ = nowW wP le g stP
  wf-△ {P = P} {Q = Q} wP wQ .stepW {s′} le {a = τ} st ok with △-τ-elim P Q st
  ... | △τP    stP = wf-△ (stepW wP le stP ok) (wf-mono (≤-trans le (next-≤ τ s′)) wQ)
  ... | △τQ    stQ = wf-△ (wf-mono (≤-trans le (next-≤ τ s′)) wP) (stepW wQ le stQ ok)
  ... | △τQret _   = wf-mono (≤-trans le (next-≤ τ s′)) wQ
  ... | △τ⊓P   _   = wf-mono (≤-trans le (next-≤ τ s′)) wP
  ... | △τ⊓Q   _   = wf-mono (≤-trans le (next-≤ τ s′)) wQ
  wf-△ {P = P} {Q = Q} wP wQ .stepW {s′} le {a = ev (evl _)} st ok with △-ev-elim P Q st
  ... | △evP  stP     = wf-△ (stepW wP le stP ok) (wf-mono (≤-trans le (next-≤ _ s′)) wQ)
  ... | △evQ  stQ     = stepW wQ le stQ ok
  ... | △evPQ stP stQ = wf-△-br2 (stepW wP le stP ok)
                                 (wf-mono (≤-trans le (next-≤ _ s′)) wQ)
                                 (stepW wQ le stQ ok)
  -- `_△_` never terminates by a bare `sRet` (every clause is a `react` node)
  wf-△ {P = P} {Q = Q} wP wQ .stepW le {a = ev (√ _)} st ok with △-ev-elim P Q st
  ... | ()

  wf-△-br2 wP₁ wQ wQ₁ .nowW  _ _ (sVis refl ())
  wf-△-br2 wP₁ wQ wQ₁ .stepW _ (sRet ())
  wf-△-br2 wP₁ wQ wQ₁ .stepW _ (sSil ())
  wf-△-br2 wP₁ wQ wQ₁ .stepW _ (sVis refl ())
  wf-△-br2 wP₁ wQ wQ₁ .stepW {s′} le (sTau {i = _ , fin} {a = lift fzero} refl refl) _ =
    wf-△ (wf-mono (≤-trans le (next-≤ τ s′)) wP₁) (wf-mono (≤-trans le (next-≤ τ s′)) wQ)
  wf-△-br2 wP₁ wQ wQ₁ .stepW {s′} le (sTau {i = _ , fin} {a = lift (fsuc fzero)} refl refl) _ =
    wf-mono (≤-trans le (next-≤ τ s′)) wQ₁
  wf-△-br2 wP₁ wQ wQ₁ .stepW _ (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl ())
  wf-△-br2 wP₁ wQ wQ₁ .stepW _ (sTau {i = _ , base _}   refl ())
  wf-△-br2 wP₁ wQ wQ₁ .stepW _ (sTau {i = _ , pair _ _} refl ())

  ------------------------------------------------------------------------
  -- Renamed components whose image touches no guaranteed block label
  ------------------------------------------------------------------------

  -- A `renameMap` along an injection `ι` from some other alphabet only ever
  -- performs labels in the image of `ι` (`ren-ev-inv`).  If no label of that image
  -- both lies in `G` and carries a block, the renamed process is well-formed on `G`
  -- for free, whatever it does — this is the shape of every non-BlockFetch peer
  -- (KA/CS/TS/LF carry no block at all; the LN server's announcement is its RELY,
  -- excluded from the peers' `G`).  Stated for the target carrier alone: no source
  -- carrier and no `Carries₁` are needed, so the module takes only the renaming.
  module Vacuous {ℓe₁} {E₁ : Set ℓ → Set ℓe₁}
    (ι      : ∀ {A} → E₁ A → E A)
    (ι⁻¹    : ∀ {A} → E A → Maybe (E₁ A))
    (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e) where

    -- (`ι-vis-inv` re-exported: the premise below is stated in it)
    open import CSP.Rename {E₁ = E₁} {E₂ = E} ι ι⁻¹ ι-linv using (renameMap; ι-vis-inv) public
    open import CSP.Laws.Traces.RenameDeadlock {E₁ = E₁} {E₂ = E} ι ι⁻¹ ι-linv
      using (ren-τ-inv; ren-ev-inv)

    -- every guaranteed label the image can perform carries no block ⇒ `Wf`, for ANY
    -- source process (the corecursive call changes `P`, which is why it is implicit)
    wf-renameMap-vacuous : ∀ {G s} {P : PTree E₁ (ExtI E₁) (⊤ {0ℓ})}
      → (∀ bt b at a → ι-vis-inv bt b ≡ just (at , a) → G bt b → ∀ {blk} → ¬ Carries bt b blk)
      → Wf G s (renameMap P)
    wf-renameMap-vacuous {P = P} h .nowW le g st with ren-ev-inv {inv = ι-vis-inv} {P = P} st
    ... | inj₁ (at , a , bt , b , P₁ , Pev , eqinv , refl , refl) =
      λ c → ⊥-elim (h bt b at a eqinv g c)
    wf-renameMap-vacuous {P = P} h .stepW le {a = τ} st _ with ren-τ-inv {inv = ι-vis-inv} {P = P} st
    ... | P₁ , Pτ , refl = wf-renameMap-vacuous h
    wf-renameMap-vacuous {P = P} h .stepW le {a = ev _} st _ with ren-ev-inv {inv = ι-vis-inv} {P = P} st
    ... | inj₁ (at , a , bt , b , P₁ , Pev , eqinv , refl , refl) = wf-renameMap-vacuous h
    ... | inj₂ (r , refl , _ , refl) = wf-deadlock

  ------------------------------------------------------------------------
  -- The hiding congruence
  ------------------------------------------------------------------------

  -- THE SIDE CONDITIONS OF HIDING.  A hidden visible step of `P` becomes a τ of
  -- `P ∖ A`, whose `stepW` receives only the vacuous `OK s′ τ`; the `OK` of the
  -- hidden label must therefore come from `P`'s OWN guarantee, so every hidden
  -- block-carrying label must be in `G` (`HideCov`).  And the state the hidden
  -- label leads to must be no larger than the state a τ leads to (`HideKeep`) —
  -- trivially so when neither moves it, which is the case for the io channels.
  HideCov : EventSet → Alpha → Set (lsuc ℓ ⊔ ℓe)
  HideCov A G = ∀ {X} {e : E X} {a : X} {b} → Carries (X , e) a b
              → EventSet.mem A (X , e) a → G (X , e) a

  HideKeep : EventSet → Set (lsuc ℓ ⊔ ℓe)
  HideKeep A = ∀ {X} {e : E X} {a : X} s
             → EventSet.mem A (X , e) a → next (lbl e a) s ≤ next τ s

  -- THE HIDING CONGRUENCE.  A visible step of `P ∖ A` is the same visible step of
  -- `P`; a τ of `P ∖ A` is either a τ of `P` or a hidden visible step, whose `OK` is
  -- `P`'s own guarantee via `HideCov`; a `√` lands in `deadlock`.
  wf-Hide : ∀ {G s} (A : EventSet) → HideCov A G → HideKeep A
          → ∀ {P} → Wf G s P → Wf G s (P ∖ A)
  wf-Hide A cov keep {P} w .nowW le g st with Hide-ev-elim A P st
  ... | heV P′ _ stP        = nowW w le g stP
  wf-Hide A cov keep {P} w .stepW {s′} le {a = τ} st ok with Hide-τ-elim A P st
  ... | hτP P′ stP refl     = wf-Hide A cov keep (stepW w le stP ok)
  ... | hτH P′ m stP refl   =
    wf-Hide A cov keep
      (wf-mono (keep s′ m) (stepW w le stP (λ c → nowW w le (cov c m) stP c)))
  wf-Hide A cov keep {P} w .stepW le {a = ev (evl _)} st ok with Hide-ev-elim A P st
  ... | heV P′ _ stP        = wf-Hide A cov keep (stepW w le stP ok)
  wf-Hide A cov keep {P} w .stepW le {a = ev (√ _)} st ok with Hide-ev-elim A P st
  ... | he√ _               = wf-deadlock

------------------------------------------------------------------------
-- Transport along an injective alphabet renaming
--
-- The BlockFetch peers are `renameMap`s of processes over `BFEv`; their `Wf`
-- fact is proved at the source alphabet and carried across here.  Two
-- instances of `Carrier` are involved, so this cannot live inside it — the
-- same reason `CSP.Laws.Bisim.RenameOffers` sits beside `DRCongruenceRep`.
-- The SOURCE carrier is state-agnostic (`next₁ = λ _ s → s`): a renamed
-- component never mints, and that is what keeps the transport premise-light.
------------------------------------------------------------------------

module Rename {ℓ ℓe₁ ℓe₂} {E₁ : Set ℓ → Set ℓe₁} {E₂ : Set ℓ → Set ℓe₂}
  (E₁-≟ : (x y : AnyTypes E₁) → Dec (x ≡ y))
  (E₂-≟ : (x y : AnyTypes E₂) → Dec (x ≡ y))
  (ι      : ∀ {A} → E₁ A → E₂ A)
  (ι⁻¹    : ∀ {A} → E₂ A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e)
  (S B : Set)
  (Carries₁ : (at : AnyTypes E₁) → proj₁ at → B → Set)
  (Carries₂ : (bt : AnyTypes E₂) → proj₁ bt → B → Set)
  (WA       : S → B → Set)
  (next₂    : LTS.Label {E = E₂} {I = ExtI E₂} (⊤ {0ℓ}) → S → S)
  (_≤_      : S → S → Set)
  (≤-refl   : ∀ {s} → s ≤ s)
  (≤-trans  : ∀ {s₁ s₂ s₃} → s₁ ≤ s₂ → s₂ ≤ s₃ → s₁ ≤ s₃)
  (next₂-≤  : ∀ a s → s ≤ next₂ a s) where

  open import CSP.Rename {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv
    using (ConcEvent₁; renameMap; ι-vis-inv)
  open import CSP.Laws.Traces.RenameDeadlock {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv
    using (_⟦_⟧ⁱ; ren-τ-inv; ren-ev-inv)
  import Semantics.LTS {E = E₂} {I = ExtI E₂} as L2
  import CSP.Laws.Bisim.DRCongruenceRep E₁-≟ as R1
  import CSP.Laws.Bisim.DRCongruenceRep E₂-≟ as R2
  -- the source carrier, state-agnostic; and the target carrier
  module C1 = Carrier E₁-≟ S B Carries₁ WA (λ _ s → s) _≤_ ≤-trans (λ _ _ → ≤-refl)
  module C2 = Carrier E₂-≟ S B Carries₂ WA next₂ _≤_ ≤-trans next₂-≤

  -- the per-target partial inverse that drives `renameInv` (as in `RenameOffers`)
  RenInv : Set (lsuc ℓ ⊔ ℓe₁ ⊔ ℓe₂)
  RenInv = (bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁

  -- THE TRANSPORT.  Every target step inverts to a source step on the `inv`-preimage
  -- event (`ren-ev-inv`/`ren-τ-inv`), so the three premises relate the label data
  -- ACROSS that preimage: the target alphabet pulls back into the source one, and the
  -- carried value is the same on both sides.  A target `√` lands in `deadlock`.  The
  -- source being state-agnostic, the target's state growth is absorbed by the SOURCE
  -- fact (`C1.wf-mono` on the hypothesis) so the corecursive call stays guarded.
  wf-renameInv : ∀ {inv : RenInv} {G₁ : R1.Alpha} {G₂ : R2.Alpha} {s}
                   {P : PTree E₁ (ExtI E₁) (⊤ {0ℓ})}
               → (∀ bt b at a → inv bt b ≡ just (at , a) → G₂ bt b → G₁ at a)
               → (∀ bt b at a → inv bt b ≡ just (at , a)
                    → ∀ {blk} → Carries₂ bt b blk → Carries₁ at a blk)
               → (∀ bt b at a → inv bt b ≡ just (at , a)
                    → ∀ {blk} → Carries₁ at a blk → Carries₂ bt b blk)
               → C1.Wf G₁ s P → C2.Wf G₂ s (P ⟦ inv ⟧ⁱ)
  wf-renameInv {inv} {P = P} al c→ c← w .C2.nowW le g st
    with ren-ev-inv {inv = inv} {P = P} st
  ... | inj₁ (at , a , bt , b , P₁ , Pev , eqinv , refl , refl) =
    λ c → C1.nowW w le (al bt b at a eqinv g) Pev (c→ bt b at a eqinv c)
  wf-renameInv {inv} {P = P} al c→ c← w .C2.stepW {s′} le {a = L2.τ} st ok
    with ren-τ-inv {inv = inv} {P = P} st
  ... | P₁ , Pτ , refl =
    wf-renameInv al c→ c← (C1.wf-mono (next₂-≤ L2.τ s′) (C1.stepW w le Pτ tt))
  wf-renameInv {inv} {P = P} al c→ c← w .C2.stepW {s′} le {a = L2.ev e′} st ok
    with ren-ev-inv {inv = inv} {P = P} st
  ... | inj₁ (at , a , bt , b , P₁ , Pev , eqinv , refl , refl) =
    wf-renameInv al c→ c←
      (C1.wf-mono (next₂-≤ _ s′) (C1.stepW w le Pev (λ c → ok (c← bt b at a eqinv c))))
  ... | inj₂ (r , refl , _ , refl) = C2.wf-deadlock

  -- the headline instance: the injective ALPHABET renaming induced by `ι`
  wf-renameMap : ∀ {G₁ : R1.Alpha} {G₂ : R2.Alpha} {s} {P : PTree E₁ (ExtI E₁) (⊤ {0ℓ})}
               → (∀ bt b at a → ι-vis-inv bt b ≡ just (at , a) → G₂ bt b → G₁ at a)
               → (∀ bt b at a → ι-vis-inv bt b ≡ just (at , a)
                    → ∀ {blk} → Carries₂ bt b blk → Carries₁ at a blk)
               → (∀ bt b at a → ι-vis-inv bt b ≡ just (at , a)
                    → ∀ {blk} → Carries₁ at a blk → Carries₂ bt b blk)
               → C1.Wf G₁ s P → C2.Wf G₂ s (renameMap P)
  wf-renameMap = wf-renameInv {inv = ι-vis-inv}

------------------------------------------------------------------------
-- The Cardano instance
------------------------------------------------------------------------

-- the instance, parametric in the network parameters, the topology and the api
-- alphabet — the same three parameters every other `Parametric.Announce*` module
-- takes, so `Minted`, `WellAnnounced`, `mintedAfter` and `Gated` are literally theirs
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open Params p using (Block; EB; EBHash; ebHash; Time; Length)
  open N p
    using ( Link; Net_Api; Net_Api-≟; env; envMint; apiLN; store; break
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLF
          ; stGet; stPut; sendBFBlock; recvBFBlock; sendLNBlockAnnouncement )
  open D p using (Payload; Header; header; blockFetch; MsgBlock)
  open import CSP.Examples.Cardano_network.Base using (Dir; Mode; N2N_BlockFetch)
  open import CSP.Examples.Cardano_network.NetCommon p using (ioES)
  open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Label; ev; τ; evl; √; evLabel; _─[_]─►_)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload}) using (Alpha)
  open AS.Generic p t apiES using (Minted)
  open AI.Generic p t apiES using (WellAnnounced; mintedAfter; Gated)
  open import Data.List using (List; []; _∷_; _++_)
  open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
  open import Data.List.Relation.Binary.Subset.Propositional.Properties
    using (⊆-refl; ⊆-trans)

  ------------------------------------------------------------------------
  -- Which events carry a block
  ------------------------------------------------------------------------

  -- THE PROVENANCE CHANNELS: the seven event shapes on which a `Block` travels from
  -- the store to an announcement — the store's two ends, the BlockFetch api in both
  -- directions, the BlockFetch wire in both directions, and the announcement itself.
  -- `env … envMint` is deliberately ABSENT: neither the mint thread nor the store pins
  -- that value, and `acceptMint`'s guard restores the invariant one step later; a
  -- constructor here would make every leaf fact about the mint FALSE.
  data Carries : (at : AnyTypes (Net_Api Payload)) → proj₁ at → Block → Set where
    c-stGet  : ∀ {l d b}    → Carries (_ , store l d stGet) b b
    c-stPut  : ∀ {l d b}    → Carries (_ , store l d stPut) b b
    c-sendBF : ∀ {l d b}    → Carries (_ , apiBF l d sendBFBlock) b b
    c-recvBF : ∀ {l d b}    → Carries (_ , apiBF l d recvBFBlock) b b
    c-ann    : ∀ {l d b}    → Carries (_ , apiLN l d sendLNBlockAnnouncement) (header b) b
    c-input  : ∀ {l d b} {tm : Time} {md : Mode} {ln : Length}
             → Carries (_ , input  l d N2N_BlockFetch) (tm , md , ln , blockFetch (MsgBlock b)) b
    c-output : ∀ {l d b} {tm : Time} {md : Mode} {ln : Length}
             → Carries (_ , output l d N2N_BlockFetch) (tm , md , ln , blockFetch (MsgBlock b)) b

  ------------------------------------------------------------------------
  -- The state update
  ------------------------------------------------------------------------

  -- the EB hashes a label mints: one for a mint announcing an EB, none otherwise
  mintOf : Label (⊤ {0ℓ}) → Minted
  mintOf (ev (evl (evLabel _ (env _ _ envMint) (just e , _)))) = ebHash e ∷ []
  mintOf _                                                      = []

  -- the minted set after a label: what it mints, prepended.  On a mint this IS
  -- `mintedAfter` (definitionally, `++` computing on the one-element list), and on
  -- every other label it is the identity — phrased through `mintOf` so that growth
  -- (`next-⊇`) is one stdlib lemma rather than a case split over the alphabet.
  next : Label (⊤ {0ℓ}) → Minted → Minted
  next a ms = mintOf a ++ ms

  -- `next` agrees with the spec's own state update on a mint
  next-mint : ∀ {l d} (mb : Maybe EB × Block) ms
            → next (ev (evl (evLabel _ (env l d envMint) mb))) ms ≡ mintedAfter mb ms
  next-mint (just _  , _) ms = refl
  next-mint (nothing , _) ms = refl

  -- the minted set only grows
  next-⊇ : ∀ a ms → ms ⊆ next a ms
  next-⊇ a ms = ∈-++⁺ʳ (mintOf a)

  ------------------------------------------------------------------------
  -- The carrier, instantiated
  ------------------------------------------------------------------------

  open Carrier (Net_Api-≟ {Payload}) Minted Block Carries WellAnnounced
               next _⊆_ ⊆-trans next-⊇ public

  -- `BlockOK ms a`: if the label `a` carries a block on a provenance channel, that
  -- block is well-announced against `ms` — the instance of the generic `OK`
  BlockOK : Minted → Label (⊤ {0ℓ}) → Set
  BlockOK = OK

  -- monotone in the minted set
  blockOK-mono : ∀ {ms ms′} a → ms ⊆ ms′ → BlockOK ms a → BlockOK ms′ a
  blockOK-mono (ev (evl _)) sub ok c = AI.Generic.wellAnnounced-mono p t apiES sub (ok c)
  blockOK-mono (ev (√ _))   sub ok   = tt
  blockOK-mono τ            sub ok   = tt

  ------------------------------------------------------------------------
  -- The payoff, and the hiding side condition at `ioES`
  ------------------------------------------------------------------------

  -- the announce channel is in a guarantee alphabet
  AnnIn : Alpha → Set
  AnnIn G = ∀ {l : Link} {d : Dir} (h : Header)
          → G (Header , apiLN l d sendLNBlockAnnouncement) h

  -- `Wf`'s guarantee on the announce channel IS `Safe`'s `gate`: `BlockOK` at an
  -- announcement of `header b` is `WellAnnounced ms b`, by `c-ann`
  wf→gate : ∀ {G ms M} → AnnIn G → Wf G ms M → Gated ms M
  wf→gate ann w st = nowW w ⊆-refl (ann _) st c-ann

  -- the system's own hiding keeps the minted set: `∖ ioES` hides only `input`/
  -- `output`, and a mint rides `env`.  One clause per `Net_Api` constructor, because
  -- `ioSet` does not reduce until the constructor is known (as `HideOK-ioES`).
  hideKeep-ioES : HideKeep ioES
  hideKeep-ioES {e = input  _ _ _} _ _  = λ q → q
  hideKeep-ioES {e = output _ _ _} _ _  = λ q → q
  hideKeep-ioES {e = sndmsg _ _ _} _ ()
  hideKeep-ioES {e = rcvmsg _ _ _} _ ()
  hideKeep-ioES {e = tx     _ _ _} _ ()
  hideKeep-ioES {e = sndack _ _ _} _ ()
  hideKeep-ioES {e = rcvack _ _ _} _ ()
  hideKeep-ioES {e = ack    _ _ _} _ ()
  hideKeep-ioES {e = done   _ _ _} _ ()
  hideKeep-ioES {e = apiCS  _ _ _} _ ()
  hideKeep-ioES {e = apiBF  _ _ _} _ ()
  hideKeep-ioES {e = apiTS  _ _ _} _ ()
  hideKeep-ioES {e = apiKA  _ _ _} _ ()
  hideKeep-ioES {e = apiLN  _ _ _} _ ()
  hideKeep-ioES {e = apiLF  _ _ _} _ ()
  hideKeep-ioES {e = store  _ _ _} _ ()
  hideKeep-ioES {e = env    _ _ _} _ ()
  hideKeep-ioES {e = break  _}     _ ()

  ------------------------------------------------------------------------
  -- Sanity: the exemptions really are exemptions
  ------------------------------------------------------------------------

  -- a mint carries no constrained block — the load-bearing exemption, as a refutation
  mint-free : ∀ {l d} {mb : Maybe EB × Block} {b} → Carries (_ , env l d envMint) mb b → ⊥
  mint-free ()

  -- …so a mint label is `BlockOK` against ANY minted set
  blockOK-mint : ∀ {ms l d} {mb : Maybe EB × Block}
               → BlockOK ms (ev (evl (evLabel _ (env l d envMint) mb)))
  blockOK-mint ()

  -- a non-provenance channel is `BlockOK` outright: the shape every vacuous leaf uses
  blockOK-apiCS : ∀ {ms l d m} {x} → BlockOK ms (ev (evl (evLabel _ (apiCS l d m) x)))
  blockOK-apiCS ()
