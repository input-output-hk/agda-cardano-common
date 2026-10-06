{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- τ-accessibility at every reachable state for the concrete media
-- `NetworkLinkA` and `NetworkLinkBreakableA` (NetCommon).
--
-- The medium hides internally (csSR, csRS inside each side; csTA between the
-- sides), so the τ form alone does not compose: the calculus runs modulo H.
--   TxSide inner  Inputs ∥_{csSR} (Trans ⦀ RcvAck)   at H = csSR ∪ csTA
--     (Inputs count all of H; Trans/RcvAck only their SOLO csTA events)
--   RxSide inner  Outputs ∥_{csRS} (Recv ⦀ SndAck)   at H = csRS ∪ csTA
--   hide csSR / csRS                                  ⇒ MAccR csTA
--   NetOneLink    TxSide ∥_{csTA} RxSide              at H = csTA, then hide ⇒ τ
--   ⦀Fin, renameMap, △                                ⇒ the two media
-- Every leaf is a `loop0` of a stable menu whose round contains an event
-- outside its counted set, discharged by `MAccR-loop0`.
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.NetworkVerification.MediumTauAcc (p : Params) where

open import Level using (0ℓ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; AnyTypes; ContinueType; ExtI)
open import Cardano_network.Base
open import Cardano_network.Net p
open Params p using (numLinks; linkConfig)

------------------------------------------------------------------------
-- §1. The pre-rename network over `Net Data`
------------------------------------------------------------------------

module Pre (Data : Set) ⦃ _ : DecEq Data ⦄ where

  import CSP.Operators {E = Net Data} (Net-≟ {Data}) as Op
  open Op using (EventSet; chanSet; ∅ES; _∖_; _∥⇘_⇙_; _⦀_; ⦀⋆; ⦀Fin; pchoice; Skip; loop0)
  open import Cardano_network.Network p Data
    using (NetProc; Menu; Input; Output; inputMenu; outputMenu
          ; csSR; csSR-dec; csRS; csRS-dec; csTA; csTA-dec)
  open import Cardano_network.NetworkLink p Data
  open import Semantics.DivergenceFree {E = Net Data} {I = ExtI (Net Data)} using (τ-AccReach)
  open import CSP.Laws.DivFree.ModAcc (Net-≟ {Data})
  open import CSP.Laws.DivFree.Reach (Net-≟ {Data})
  open import CSP.Laws.DivFree.Loop (Net-≟ {Data})

  -- the three internal channel sets
  SR RS TA : EventSet
  SR = chanSet csSR csSR-dec
  RS = chanSet csRS csRS-dec
  TA = chanSet csTA csTA-dec

  -- counted sets of the two sides' inner composites
  Htx Hrx : EventSet
  Htx = SR ∪H TA
  Hrx = RS ∪H TA

  -- `nothing` is not `just`
  case-nothing′ : ∀ {X : Set₁} {t : NetProc} → nothing ≡ just t → X
  case-nothing′ ()

  -- a list of processes all satisfying P, built by `map`
  all-map : ∀ {X : Set} {P : NetProc → Set₁} (f : X → NetProc)
          → (∀ x → P (f x)) → (xs : List X) → All P (map f xs)
  all-map f pf []       = []
  all-map f pf (x ∷ xs) = pf x ∷ all-map f pf xs

  ----------------------------------------------------------------------
  -- §1a. The six leaves
  ----------------------------------------------------------------------

  -- Input(l,d,id): input (visible) → sndmsg (csSR) → rcvack (csSR) → loop
  input-guard : ∀ {l d id B} {e : Net Data B} {a t′}
              → Htx .EventSet.mem (B , e) a → inputMenu l d id (B , e) a ≡ just t′ → Guarded Htx t′
  input-guard {e = input  _ _ _} (inj₁ ()) _
  input-guard {e = input  _ _ _} (inj₂ ()) _
  input-guard {e = output _ _ _} _ ()
  input-guard {e = sndmsg _ _ _} _ ()
  input-guard {e = rcvmsg _ _ _} _ ()
  input-guard {e = tx     _ _ _} _ ()
  input-guard {e = sndack _ _ _} _ ()
  input-guard {e = rcvack _ _ _} _ ()
  input-guard {e = ack    _ _ _} _ ()

  -- every continuation of Input's menu is accessible
  input-cont : ∀ {l d id at a t′} → inputMenu l d id at a ≡ just t′ → MAccR Htx t′
  input-cont {l} {d} {id} {_ , input l′ d′ id′} {x} eq with l′ ≟ l
  ... | no _ = case-nothing′ eq
  ... | yes refl with d′ ≟ d
  ...   | no _ = case-nothing′ eq
  ...   | yes refl with id′ ≟ id
  ...     | no _ = case-nothing′ eq
  ...     | yes refl = subst (MAccR Htx) (just-injective eq)
                         (MAccR-Output (sndmsg l d id) x (MAccR-⟶₀ (rcvack l d id) MAccR-Skip))
  input-cont {at = _ , output _ _ _} ()
  input-cont {at = _ , sndmsg _ _ _} ()
  input-cont {at = _ , rcvmsg _ _ _} ()
  input-cont {at = _ , tx     _ _ _} ()
  input-cont {at = _ , sndack _ _ _} ()
  input-cont {at = _ , rcvack _ _ _} ()
  input-cont {at = _ , ack    _ _ _} ()

  -- LEAF: Input
  input-ok : ∀ l d id → MAccR Htx (Input l d id)
  input-ok l d id =
    MAccR-loop0 (Guarded-react refl (λ {B} {e} {a} {t′} → input-guard {l} {d} {id} {B} {e} {a} {t′}))
                (MAccR-react refl (λ {at} {a} {t′} → input-cont {l} {d} {id} {at} {a} {t′}))

  -- Transmitterₗ: sndmsg (sync, NOT counted on this side) → tx (csTA) → loop
  trans-guard : ∀ {l B} {e : Net Data B} {a t′}
              → (Htx −H SR) .EventSet.mem (B , e) a → transmitterMenuₗ l (B , e) a ≡ just t′
              → Guarded (Htx −H SR) t′
  trans-guard {e = input  _ _ _} _ ()
  trans-guard {e = output _ _ _} _ ()
  trans-guard {e = sndmsg _ _ _} (_ , ¬sr) _ = ⊥-elim (¬sr tt)
  trans-guard {e = rcvmsg _ _ _} _ ()
  trans-guard {e = tx     _ _ _} _ ()
  trans-guard {e = sndack _ _ _} _ ()
  trans-guard {e = rcvack _ _ _} _ ()
  trans-guard {e = ack    _ _ _} _ ()

  -- every continuation of Transmitterₗ's menu is accessible
  trans-cont : ∀ {l at a t′} → transmitterMenuₗ l at a ≡ just t′ → MAccR (Htx −H SR) t′
  trans-cont {l} {_ , sndmsg l′ d id} {x} eq with l′ ≟ l
  ... | yes refl = subst (MAccR (Htx −H SR)) (just-injective eq) (MAccR-Output (tx l d id) x MAccR-Skip)
  ... | no _     = case-nothing′ eq
  trans-cont {at = _ , input  _ _ _} ()
  trans-cont {at = _ , output _ _ _} ()
  trans-cont {at = _ , rcvmsg _ _ _} ()
  trans-cont {at = _ , tx     _ _ _} ()
  trans-cont {at = _ , sndack _ _ _} ()
  trans-cont {at = _ , rcvack _ _ _} ()
  trans-cont {at = _ , ack    _ _ _} ()

  -- LEAF: Transmitterₗ
  trans-ok : ∀ l → MAccR (Htx −H SR) (Transmitterₗ l)
  trans-ok l =
    MAccR-loop0 (Guarded-react refl (λ {B} {e} {a} {t′} → trans-guard {l} {B} {e} {a} {t′}))
                (MAccR-react refl (λ {at} {a} {t′} → trans-cont {l} {at} {a} {t′}))

  -- RcvAckₗ: ack (csTA, counted) → rcvack (sync, NOT counted) → loop
  rcvack-guard : ∀ {l B} {e : Net Data B} {a t′}
               → (Htx −H SR) .EventSet.mem (B , e) a → rcvackMenuₗ l (B , e) a ≡ just t′
               → Guarded (Htx −H SR) t′
  rcvack-guard {e = input  _ _ _} _ ()
  rcvack-guard {e = output _ _ _} _ ()
  rcvack-guard {e = sndmsg _ _ _} _ ()
  rcvack-guard {e = rcvmsg _ _ _} _ ()
  rcvack-guard {e = tx     _ _ _} _ ()
  rcvack-guard {e = sndack _ _ _} _ ()
  rcvack-guard {e = rcvack _ _ _} _ ()
  rcvack-guard {l} {e = ack l′ d id} _ eq with l′ ≟ l
  ... | yes refl = subst (Guarded (Htx −H SR)) (just-injective eq)
                     (Guarded-⟶-vis (rcvack l d id) (λ x m → proj₂ m tt))
  ... | no _     = case-nothing′ eq

  -- every continuation of RcvAckₗ's menu is accessible
  rcvack-cont : ∀ {l at a t′} → rcvackMenuₗ l at a ≡ just t′ → MAccR (Htx −H SR) t′
  rcvack-cont {l} {_ , ack l′ d id} eq with l′ ≟ l
  ... | yes refl = subst (MAccR (Htx −H SR)) (just-injective eq) (MAccR-⟶₀ (rcvack l d id) MAccR-Skip)
  ... | no _     = case-nothing′ eq
  rcvack-cont {at = _ , input  _ _ _} ()
  rcvack-cont {at = _ , output _ _ _} ()
  rcvack-cont {at = _ , sndmsg _ _ _} ()
  rcvack-cont {at = _ , rcvmsg _ _ _} ()
  rcvack-cont {at = _ , tx     _ _ _} ()
  rcvack-cont {at = _ , sndack _ _ _} ()
  rcvack-cont {at = _ , rcvack _ _ _} ()

  -- LEAF: RcvAckₗ
  rcvack-ok : ∀ l → MAccR (Htx −H SR) (RcvAckₗ l)
  rcvack-ok l =
    MAccR-loop0 (Guarded-react refl (λ {B} {e} {a} {t′} → rcvack-guard {l} {B} {e} {a} {t′}))
                (MAccR-react refl (λ {at} {a} {t′} → rcvack-cont {l} {at} {a} {t′}))

  -- Output(l,d,id): rcvmsg (csRS) → output (visible) → sndack (csRS) → loop
  output-guard : ∀ {l d id B} {e : Net Data B} {a t′}
               → Hrx .EventSet.mem (B , e) a → outputMenu l d id (B , e) a ≡ just t′ → Guarded Hrx t′
  output-guard {e = input  _ _ _} _ ()
  output-guard {e = output _ _ _} _ ()
  output-guard {e = sndmsg _ _ _} _ ()
  output-guard {l} {d} {id} {e = rcvmsg l′ d′ id′} {x} _ eq with l′ ≟ l
  ... | no _ = case-nothing′ eq
  ... | yes refl with d′ ≟ d
  ...   | no _ = case-nothing′ eq
  ...   | yes refl with id′ ≟ id
  ...     | no _ = case-nothing′ eq
  ...     | yes refl = subst (Guarded Hrx) (just-injective eq)
                         (Guarded-Output-vis (output l d id) x (λ { y (inj₁ ()) ; y (inj₂ ()) }))
  output-guard {e = tx     _ _ _} _ ()
  output-guard {e = sndack _ _ _} _ ()
  output-guard {e = rcvack _ _ _} _ ()
  output-guard {e = ack    _ _ _} _ ()

  -- every continuation of Output's menu is accessible
  output-cont : ∀ {l d id at a t′} → outputMenu l d id at a ≡ just t′ → MAccR Hrx t′
  output-cont {l} {d} {id} {_ , rcvmsg l′ d′ id′} {x} eq with l′ ≟ l
  ... | no _ = case-nothing′ eq
  ... | yes refl with d′ ≟ d
  ...   | no _ = case-nothing′ eq
  ...   | yes refl with id′ ≟ id
  ...     | no _ = case-nothing′ eq
  ...     | yes refl = subst (MAccR Hrx) (just-injective eq)
                         (MAccR-Output (output l d id) x (MAccR-⟶₀ (sndack l d id) MAccR-Skip))
  output-cont {at = _ , input  _ _ _} ()
  output-cont {at = _ , output _ _ _} ()
  output-cont {at = _ , sndmsg _ _ _} ()
  output-cont {at = _ , tx     _ _ _} ()
  output-cont {at = _ , sndack _ _ _} ()
  output-cont {at = _ , rcvack _ _ _} ()
  output-cont {at = _ , ack    _ _ _} ()

  -- LEAF: Output
  output-ok : ∀ l d id → MAccR Hrx (Output l d id)
  output-ok l d id =
    MAccR-loop0 (Guarded-react refl (λ {B} {e} {a} {t′} → output-guard {l} {d} {id} {B} {e} {a} {t′}))
                (MAccR-react refl (λ {at} {a} {t′} → output-cont {l} {d} {id} {at} {a} {t′}))

  -- Receiverₗ: tx (csTA, counted) → rcvmsg (sync, NOT counted) → loop
  recv-guard : ∀ {l B} {e : Net Data B} {a t′}
             → (Hrx −H RS) .EventSet.mem (B , e) a → receiverMenuₗ l (B , e) a ≡ just t′
             → Guarded (Hrx −H RS) t′
  recv-guard {e = input  _ _ _} _ ()
  recv-guard {e = output _ _ _} _ ()
  recv-guard {e = sndmsg _ _ _} _ ()
  recv-guard {e = rcvmsg _ _ _} _ ()
  recv-guard {l} {e = tx l′ d id} {x} _ eq with l′ ≟ l
  ... | yes refl = subst (Guarded (Hrx −H RS)) (just-injective eq)
                     (Guarded-Output-vis (rcvmsg l d id) x (λ y m → proj₂ m tt))
  ... | no _     = case-nothing′ eq
  recv-guard {e = sndack _ _ _} _ ()
  recv-guard {e = rcvack _ _ _} _ ()
  recv-guard {e = ack    _ _ _} _ ()

  -- every continuation of Receiverₗ's menu is accessible
  recv-cont : ∀ {l at a t′} → receiverMenuₗ l at a ≡ just t′ → MAccR (Hrx −H RS) t′
  recv-cont {l} {_ , tx l′ d id} {x} eq with l′ ≟ l
  ... | yes refl = subst (MAccR (Hrx −H RS)) (just-injective eq) (MAccR-Output (rcvmsg l d id) x MAccR-Skip)
  ... | no _     = case-nothing′ eq
  recv-cont {at = _ , input  _ _ _} ()
  recv-cont {at = _ , output _ _ _} ()
  recv-cont {at = _ , sndmsg _ _ _} ()
  recv-cont {at = _ , rcvmsg _ _ _} ()
  recv-cont {at = _ , sndack _ _ _} ()
  recv-cont {at = _ , rcvack _ _ _} ()
  recv-cont {at = _ , ack    _ _ _} ()

  -- LEAF: Receiverₗ
  recv-ok : ∀ l → MAccR (Hrx −H RS) (Receiverₗ l)
  recv-ok l =
    MAccR-loop0 (Guarded-react refl (λ {B} {e} {a} {t′} → recv-guard {l} {B} {e} {a} {t′}))
                (MAccR-react refl (λ {at} {a} {t′} → recv-cont {l} {at} {a} {t′}))

  -- SndAckₗ: sndack (sync, NOT counted) → ack (csTA) → loop
  sndack-guard : ∀ {l B} {e : Net Data B} {a t′}
               → (Hrx −H RS) .EventSet.mem (B , e) a → sndackMenuₗ l (B , e) a ≡ just t′
               → Guarded (Hrx −H RS) t′
  sndack-guard {e = input  _ _ _} _ ()
  sndack-guard {e = output _ _ _} _ ()
  sndack-guard {e = sndmsg _ _ _} _ ()
  sndack-guard {e = rcvmsg _ _ _} _ ()
  sndack-guard {e = tx     _ _ _} _ ()
  sndack-guard {e = sndack _ _ _} (_ , ¬rs) _ = ⊥-elim (¬rs tt)
  sndack-guard {e = rcvack _ _ _} _ ()
  sndack-guard {e = ack    _ _ _} _ ()

  -- every continuation of SndAckₗ's menu is accessible
  sndack-cont : ∀ {l at a t′} → sndackMenuₗ l at a ≡ just t′ → MAccR (Hrx −H RS) t′
  sndack-cont {l} {_ , sndack l′ d id} eq with l′ ≟ l
  ... | yes refl = subst (MAccR (Hrx −H RS)) (just-injective eq) (MAccR-⟶₀ (ack l d id) MAccR-Skip)
  ... | no _     = case-nothing′ eq
  sndack-cont {at = _ , input  _ _ _} ()
  sndack-cont {at = _ , output _ _ _} ()
  sndack-cont {at = _ , sndmsg _ _ _} ()
  sndack-cont {at = _ , rcvmsg _ _ _} ()
  sndack-cont {at = _ , tx     _ _ _} ()
  sndack-cont {at = _ , rcvack _ _ _} ()
  sndack-cont {at = _ , ack    _ _ _} ()

  -- LEAF: SndAckₗ
  sndack-ok : ∀ l → MAccR (Hrx −H RS) (SndAckₗ l)
  sndack-ok l =
    MAccR-loop0 (Guarded-react refl (λ {B} {e} {a} {t′} → sndack-guard {l} {B} {e} {a} {t′}))
                (MAccR-react refl (λ {at} {a} {t′} → sndack-cont {l} {at} {a} {t′}))

  ----------------------------------------------------------------------
  -- §1b. Composition: the two sides, one link, the link-indexed network
  ----------------------------------------------------------------------

  -- the Tx side's inner composite, at H = csSR ∪ csTA
  txInner : ∀ l → MAccR Htx (Inputsₗ l ∥⇘ SR ⇙ (Transmitterₗ l ⦀ RcvAckₗ l))
  txInner l =
    MAccR-∥ SR Htx
      (MAccR-⦀⋆ Htx (all-map _ (λ x {s} {Q} r → input-ok l (proj₁ x) (proj₂ x) r) (linkConfig l)))
      (MAccR-⦀ (Htx −H SR) (trans-ok l) (rcvack-ok l))

  -- hiding csSR leaves csTA counted
  txSide : ∀ l → MAccR TA (TxSideₗ l)
  txSide l = MAccR-∖ SR TA (txInner l)

  -- the Rx side's inner composite, at H = csRS ∪ csTA
  rxInner : ∀ l → MAccR Hrx (Outputsₗ l ∥⇘ RS ⇙ (Receiverₗ l ⦀ SndAckₗ l))
  rxInner l =
    MAccR-∥ RS Hrx
      (MAccR-⦀⋆ Hrx (all-map _ (λ x {s} {Q} r → output-ok l (proj₁ x) (proj₂ x) r) (linkConfig l)))
      (MAccR-⦀ (Hrx −H RS) (recv-ok l) (sndack-ok l))

  -- hiding csRS leaves csTA counted
  rxSide : ∀ l → MAccR TA (RxSideₗ l)
  rxSide l = MAccR-∖ RS TA (rxInner l)

  -- one link: the two sides synchronised and hidden on csTA ⇒ plain τ-accessibility
  oneLink : ∀ l → MAccR ∅ES (NetOneLink l)
  oneLink l =
    MAccR-∖ TA ∅ES
      (MAccR-mono (λ { at a (inj₁ m) → m ; at a (inj₂ ()) })
        (MAccR-∥ TA TA (txSide l) (MAccR-mono (λ at a m → proj₁ m) (rxSide l))))

  -- the link-indexed network
  networkLink : τ-AccReach NetworkLink
  networkLink = MAccR→τ-AccReach (MAccR-⦀Fin ∅ES numLinks oneLink)

  -- one link (exported for the breakable medium)
  oneLink-τ : ∀ l → τ-AccReach (NetOneLink l)
  oneLink-τ l = MAccR→τ-AccReach (oneLink l)

------------------------------------------------------------------------
-- §2. The renamed media over `Net_Api Payload`
------------------------------------------------------------------------

open import Cardano_network.Data p using (Payload; DecEq-Payload)
open import Cardano_network.NetCommon p
  using (ιNet; ιNet⁻¹; ιNet-linv; NetworkLinkA; NetworkLinkBreakableA; breakableNetLinkA)
open import CSP.Laws.DivFree.ReachRename {E₁ = Net Payload} {E₂ = Net_Api Payload} ιNet ιNet⁻¹ ιNet-linv
  using (τ-AccReach-renameMap)
open import Semantics.DivergenceFree {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (τ-AccReach)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (∅ES)
open import CSP.Laws.DivFree.ModAcc (Net_Api-≟ {Payload}) using (MAccR→τ-AccReach; τ-AccReach→MAccR∅)
open import CSP.Laws.DivFree.Reach (Net_Api-≟ {Payload}) using (MAccR-⦀Fin; MAccR-Skip)
open import CSP.Laws.DivFree.Loop (Net_Api-≟ {Payload}) using (MAccR-⟶₀)
open import CSP.Laws.DivFree.ReachInterrupt (Net_Api-≟ {Payload}) using (τ-AccReach-△)

private
  module PP = Pre Payload

-- THE CONCRETE MEDIUM: τ-accessible at every reachable state
NetworkLinkA-τ-AccReach : τ-AccReach NetworkLinkA
NetworkLinkA-τ-AccReach = τ-AccReach-renameMap PP.networkLink

-- one breakable cell: the renamed link, interrupted by its `break`
breakableNetLinkA-τ-AccReach : ∀ l → τ-AccReach (breakableNetLinkA l)
breakableNetLinkA-τ-AccReach l =
  τ-AccReach-△ (τ-AccReach-renameMap (PP.oneLink-τ l))
               (MAccR→τ-AccReach (MAccR-⟶₀ (break l) (MAccR-Skip {H = ∅ES})))

-- THE BREAKABLE MEDIUM (Stage L): τ-accessible at every reachable state
NetworkLinkBreakableA-τ-AccReach : τ-AccReach NetworkLinkBreakableA
NetworkLinkBreakableA-τ-AccReach =
  MAccR→τ-AccReach
    (MAccR-⦀Fin ∅ES numLinks (λ l → τ-AccReach→MAccR∅ (breakableNetLinkA-τ-AccReach l)))
