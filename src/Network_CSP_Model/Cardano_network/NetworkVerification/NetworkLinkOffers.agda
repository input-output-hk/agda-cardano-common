{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — LINK ALPHABETS and `OffersOnly` confinement
-- of `NetOneLink l` / `linkCopy l`.
--
-- For each TCP link `l`, `linkAlpha l` is the value-level alphabet of all
-- events whose link component is `l` (across all eight `Net` channels).
-- The two headline results say the whole small network for one link, and
-- that link's copy bundle, only EVER offer link-`l` events:
--
--   oo-NetOneLink : (l : Link) → OffersOnly (linkAlpha l) (NetOneLink l)
--   oo-linkCopy   : (l : Link) → OffersOnly (linkAlpha l) (linkCopy   l)
--
-- Together with `linkAlpha-disj` (distinct links confine disjoint
-- alphabets) these discharge, in Task 7, the pairwise-`Disj` premises of
-- `cong-⦀Fin` when proving `NetworkLink ≈DR CopySpec` link-by-link.
--
-- The proofs are entirely structural: each leaf is a `loop0 (pchoice v)`,
-- confined via a `MenuConf` witness (the menu answers `just` only on its
-- own channel/link, continuing into a confined `Output`/prefix chain);
-- each composite is closed by the generic `OffersOnly-⦀`/`-Par`/`-∖`
-- lemmas of `DRCongruenceRep`.  No postulates, holes, or `NON_TERMINATING`.
------------------------------------------------------------------------

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (Dir; IDs)

module CSP.Examples.Cardano_network.NetworkVerification.NetworkLinkOffers
  (p : Params) (Data : Set) ⦃ _ : DecEq Data ⦄ where

open import CSP.Examples.Cardano_network.Net p
  using ( Net; Net-≟; Link
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open Params p using (linkConfig)

-- the generic `OffersOnly` confinement layer, instantiated at `E = Net Data`
open import CSP.Laws.Bisim.DRCongruenceRep (Net-≟ {Data})

import CSP.Operators {E = Net Data} (Net-≟ {Data}) as Op
open Op using (⦀⋆)

open import CSP.Examples.Cardano_network.Network p Data
open import CSP.Examples.Cardano_network.NetworkLink p Data

------------------------------------------------------------------------
-- Link alphabets.
------------------------------------------------------------------------

-- `linkAlpha l`: the value-level alphabet of every `Net` event whose link
-- component is `l` (all eight channels; the carried value is irrelevant).
linkAlpha : Link → Alpha
linkAlpha l (_ , input  l′ _ _) _ = l′ ≡ l
linkAlpha l (_ , output l′ _ _) _ = l′ ≡ l
linkAlpha l (_ , sndmsg l′ _ _) _ = l′ ≡ l
linkAlpha l (_ , rcvmsg l′ _ _) _ = l′ ≡ l
linkAlpha l (_ , tx     l′ _ _) _ = l′ ≡ l
linkAlpha l (_ , sndack l′ _ _) _ = l′ ≡ l
linkAlpha l (_ , rcvack l′ _ _) _ = l′ ≡ l
linkAlpha l (_ , ack    l′ _ _) _ = l′ ≡ l

-- distinct links confine disjoint alphabets: an event in both `linkAlpha l`
-- and `linkAlpha l′` has its link `≡ l` and `≡ l′`, forcing `l ≡ l′`.
linkAlpha-disj : ∀ {l l′} → l ≢ l′ → Disj (linkAlpha l) (linkAlpha l′)
linkAlpha-disj l≢l′ (_ , input  _ _ _) _ refl q = l≢l′ q
linkAlpha-disj l≢l′ (_ , output _ _ _) _ refl q = l≢l′ q
linkAlpha-disj l≢l′ (_ , sndmsg _ _ _) _ refl q = l≢l′ q
linkAlpha-disj l≢l′ (_ , rcvmsg _ _ _) _ refl q = l≢l′ q
linkAlpha-disj l≢l′ (_ , tx     _ _ _) _ refl q = l≢l′ q
linkAlpha-disj l≢l′ (_ , sndack _ _ _) _ refl q = l≢l′ q
linkAlpha-disj l≢l′ (_ , rcvack _ _ _) _ refl q = l≢l′ q
linkAlpha-disj l≢l′ (_ , ack    _ _ _) _ refl q = l≢l′ q

------------------------------------------------------------------------
-- Leaf `MenuConf` witnesses + `OffersOnly` for the per-link buffers.
--
-- Each menu answers `just` on exactly one channel filtered by `with l′ ≟ l`;
-- the `MenuConf` proof reproduces that split (to keep the hypothesis
-- reducing) and refutes every other `nothing`-branch with an absurd `()`.
------------------------------------------------------------------------

-- Transmitterₗ l answers only on `sndmsg` at link l, continuing to `tx`.
mcTransmitterₗ : (l : Link) → MenuConf (linkAlpha l) (transmitterMenuₗ l)
mcTransmitterₗ l (_ , sndmsg l′ d id) x eq   with l′ ≟ l
mcTransmitterₗ l (_ , sndmsg l′ d id) x refl | yes refl =
  refl , OffersOnly-Output refl OffersOnly-Skip
mcTransmitterₗ l (_ , sndmsg l′ d id) x ()   | no  _
mcTransmitterₗ l (_ , input  _ _ _) _ ()
mcTransmitterₗ l (_ , output _ _ _) _ ()
mcTransmitterₗ l (_ , rcvmsg _ _ _) _ ()
mcTransmitterₗ l (_ , tx     _ _ _) _ ()
mcTransmitterₗ l (_ , sndack _ _ _) _ ()
mcTransmitterₗ l (_ , rcvack _ _ _) _ ()
mcTransmitterₗ l (_ , ack    _ _ _) _ ()

-- link l's transmitter buffer confines to `linkAlpha l`.
oo-Transmitterₗ : (l : Link) → OffersOnly (linkAlpha l) (Transmitterₗ l)
oo-Transmitterₗ l = OffersOnly-loop0 (OffersOnly-pchoice (mcTransmitterₗ l))

-- RcvAckₗ l answers only on `ack` at link l, continuing to `rcvack`.
mcRcvAckₗ : (l : Link) → MenuConf (linkAlpha l) (rcvackMenuₗ l)
mcRcvAckₗ l (_ , ack l′ d id) a eq   with l′ ≟ l
mcRcvAckₗ l (_ , ack l′ d id) a refl | yes refl =
  refl , OffersOnly-Prefix₀ (λ _ → refl) OffersOnly-Skip
mcRcvAckₗ l (_ , ack l′ d id) a ()   | no  _
mcRcvAckₗ l (_ , input  _ _ _) _ ()
mcRcvAckₗ l (_ , output _ _ _) _ ()
mcRcvAckₗ l (_ , sndmsg _ _ _) _ ()
mcRcvAckₗ l (_ , rcvmsg _ _ _) _ ()
mcRcvAckₗ l (_ , tx     _ _ _) _ ()
mcRcvAckₗ l (_ , sndack _ _ _) _ ()
mcRcvAckₗ l (_ , rcvack _ _ _) _ ()

-- link l's receive-ack buffer confines to `linkAlpha l`.
oo-RcvAckₗ : (l : Link) → OffersOnly (linkAlpha l) (RcvAckₗ l)
oo-RcvAckₗ l = OffersOnly-loop0 (OffersOnly-pchoice (mcRcvAckₗ l))

-- Receiverₗ l answers only on `tx` at link l, continuing to `rcvmsg`.
mcReceiverₗ : (l : Link) → MenuConf (linkAlpha l) (receiverMenuₗ l)
mcReceiverₗ l (_ , tx l′ d id) x eq   with l′ ≟ l
mcReceiverₗ l (_ , tx l′ d id) x refl | yes refl =
  refl , OffersOnly-Output refl OffersOnly-Skip
mcReceiverₗ l (_ , tx l′ d id) x ()   | no  _
mcReceiverₗ l (_ , input  _ _ _) _ ()
mcReceiverₗ l (_ , output _ _ _) _ ()
mcReceiverₗ l (_ , sndmsg _ _ _) _ ()
mcReceiverₗ l (_ , rcvmsg _ _ _) _ ()
mcReceiverₗ l (_ , sndack _ _ _) _ ()
mcReceiverₗ l (_ , rcvack _ _ _) _ ()
mcReceiverₗ l (_ , ack    _ _ _) _ ()

-- link l's receiver buffer confines to `linkAlpha l`.
oo-Receiverₗ : (l : Link) → OffersOnly (linkAlpha l) (Receiverₗ l)
oo-Receiverₗ l = OffersOnly-loop0 (OffersOnly-pchoice (mcReceiverₗ l))

-- SndAckₗ l answers only on `sndack` at link l, continuing to `ack`.
mcSndAckₗ : (l : Link) → MenuConf (linkAlpha l) (sndackMenuₗ l)
mcSndAckₗ l (_ , sndack l′ d id) a eq   with l′ ≟ l
mcSndAckₗ l (_ , sndack l′ d id) a refl | yes refl =
  refl , OffersOnly-Prefix₀ (λ _ → refl) OffersOnly-Skip
mcSndAckₗ l (_ , sndack l′ d id) a ()   | no  _
mcSndAckₗ l (_ , input  _ _ _) _ ()
mcSndAckₗ l (_ , output _ _ _) _ ()
mcSndAckₗ l (_ , sndmsg _ _ _) _ ()
mcSndAckₗ l (_ , rcvmsg _ _ _) _ ()
mcSndAckₗ l (_ , tx     _ _ _) _ ()
mcSndAckₗ l (_ , rcvack _ _ _) _ ()
mcSndAckₗ l (_ , ack    _ _ _) _ ()

-- link l's send-ack buffer confines to `linkAlpha l`.
oo-SndAckₗ : (l : Link) → OffersOnly (linkAlpha l) (SndAckₗ l)
oo-SndAckₗ l = OffersOnly-loop0 (OffersOnly-pchoice (mcSndAckₗ l))

------------------------------------------------------------------------
-- Leaf `MenuConf` witnesses + `OffersOnly` for the per-instance cells
-- `Input`/`Output`/`Copy` (parametrised by the full `l d id` triple, whose
-- menus filter link, direction, and id via a nested `with`-chain).
------------------------------------------------------------------------

-- Input l d id answers only on `input l d id`, continuing `sndmsg → rcvack`.
mcInput : (l : Link) (d : Dir) (id : IDs) → MenuConf (linkAlpha l) (inputMenu l d id)
mcInput l d id (_ , input l′ d′ id′) x eq   with l′ ≟ l
mcInput l d id (_ , input l′ d′ id′) x ()   | no  _
mcInput l d id (_ , input l′ d′ id′) x eq   | yes refl with d′ ≟ d
mcInput l d id (_ , input l′ d′ id′) x ()   | yes refl | no  _
mcInput l d id (_ , input l′ d′ id′) x eq   | yes refl | yes refl with id′ ≟ id
mcInput l d id (_ , input l′ d′ id′) x ()   | yes refl | yes refl | no  _
mcInput l d id (_ , input l′ d′ id′) x refl | yes refl | yes refl | yes refl =
  refl , OffersOnly-Output refl (OffersOnly-Prefix₀ (λ _ → refl) OffersOnly-Skip)
mcInput l d id (_ , output _ _ _) _ ()
mcInput l d id (_ , sndmsg _ _ _) _ ()
mcInput l d id (_ , rcvmsg _ _ _) _ ()
mcInput l d id (_ , tx     _ _ _) _ ()
mcInput l d id (_ , sndack _ _ _) _ ()
mcInput l d id (_ , rcvack _ _ _) _ ()
mcInput l d id (_ , ack    _ _ _) _ ()

-- one Input cell confines to `linkAlpha l`.
oo-Input : (l : Link) (d : Dir) (id : IDs) → OffersOnly (linkAlpha l) (Input l d id)
oo-Input l d id = OffersOnly-loop0 (OffersOnly-pchoice (mcInput l d id))

-- Output l d id answers only on `rcvmsg l d id`, continuing `output → sndack`.
mcOutput : (l : Link) (d : Dir) (id : IDs) → MenuConf (linkAlpha l) (outputMenu l d id)
mcOutput l d id (_ , rcvmsg l′ d′ id′) x eq   with l′ ≟ l
mcOutput l d id (_ , rcvmsg l′ d′ id′) x ()   | no  _
mcOutput l d id (_ , rcvmsg l′ d′ id′) x eq   | yes refl with d′ ≟ d
mcOutput l d id (_ , rcvmsg l′ d′ id′) x ()   | yes refl | no  _
mcOutput l d id (_ , rcvmsg l′ d′ id′) x eq   | yes refl | yes refl with id′ ≟ id
mcOutput l d id (_ , rcvmsg l′ d′ id′) x ()   | yes refl | yes refl | no  _
mcOutput l d id (_ , rcvmsg l′ d′ id′) x refl | yes refl | yes refl | yes refl =
  refl , OffersOnly-Output refl (OffersOnly-Prefix₀ (λ _ → refl) OffersOnly-Skip)
mcOutput l d id (_ , input  _ _ _) _ ()
mcOutput l d id (_ , output _ _ _) _ ()
mcOutput l d id (_ , sndmsg _ _ _) _ ()
mcOutput l d id (_ , tx     _ _ _) _ ()
mcOutput l d id (_ , sndack _ _ _) _ ()
mcOutput l d id (_ , rcvack _ _ _) _ ()
mcOutput l d id (_ , ack    _ _ _) _ ()

-- one Output cell confines to `linkAlpha l`.
oo-Output : (l : Link) (d : Dir) (id : IDs) → OffersOnly (linkAlpha l) (Output l d id)
oo-Output l d id = OffersOnly-loop0 (OffersOnly-pchoice (mcOutput l d id))

-- Copy l d id answers only on `input l d id`, continuing to a single `output`.
mcCopy : (l : Link) (d : Dir) (id : IDs) → MenuConf (linkAlpha l) (copyMenu l d id)
mcCopy l d id (_ , input l′ d′ id′) x eq   with l′ ≟ l
mcCopy l d id (_ , input l′ d′ id′) x ()   | no  _
mcCopy l d id (_ , input l′ d′ id′) x eq   | yes refl with d′ ≟ d
mcCopy l d id (_ , input l′ d′ id′) x ()   | yes refl | no  _
mcCopy l d id (_ , input l′ d′ id′) x eq   | yes refl | yes refl with id′ ≟ id
mcCopy l d id (_ , input l′ d′ id′) x ()   | yes refl | yes refl | no  _
mcCopy l d id (_ , input l′ d′ id′) x refl | yes refl | yes refl | yes refl =
  refl , OffersOnly-Output refl OffersOnly-Skip
mcCopy l d id (_ , output _ _ _) _ ()
mcCopy l d id (_ , sndmsg _ _ _) _ ()
mcCopy l d id (_ , rcvmsg _ _ _) _ ()
mcCopy l d id (_ , tx     _ _ _) _ ()
mcCopy l d id (_ , sndack _ _ _) _ ()
mcCopy l d id (_ , rcvack _ _ _) _ ()
mcCopy l d id (_ , ack    _ _ _) _ ()

-- one Copy cell confines to `linkAlpha l`.
oo-Copy : (l : Link) (d : Dir) (id : IDs) → OffersOnly (linkAlpha l) (Copy l d id)
oo-Copy l d id = OffersOnly-loop0 (OffersOnly-pchoice (mcCopy l d id))

------------------------------------------------------------------------
-- Composite confinement.
------------------------------------------------------------------------

-- a `⦀⋆`-fold of a mapped list is α-confined when every mapped cell is;
-- `f` is inferred from the goal so the SAME inline builder is reused.
oo-⦀⋆-map : ∀ {B : Set} {α : Alpha} {f : B → NetProc}
          → (∀ b → OffersOnly α (f b)) → (xs : List B)
          → OffersOnly α (⦀⋆ (map f xs))
oo-⦀⋆-map hf []       = OffersOnly-Skip
oo-⦀⋆-map hf (x ∷ xs) = OffersOnly-⦀ (hf x) (oo-⦀⋆-map hf xs)

-- link l's configured Input bundle confines to `linkAlpha l`.
oo-Inputsₗ : (l : Link) → OffersOnly (linkAlpha l) (Inputsₗ l)
oo-Inputsₗ l = oo-⦀⋆-map (λ { (d , id) → oo-Input l d id }) (linkConfig l)

-- link l's configured Output bundle confines to `linkAlpha l`.
oo-Outputsₗ : (l : Link) → OffersOnly (linkAlpha l) (Outputsₗ l)
oo-Outputsₗ l = oo-⦀⋆-map (λ { (d , id) → oo-Output l d id }) (linkConfig l)

-- link l's whole small network only ever offers link-l events.  Its three
-- nested `Par`/hide layers are closed by `OffersOnly-∖`/`-Par`/`-⦀`.
oo-NetOneLink : (l : Link) → OffersOnly (linkAlpha l) (NetOneLink l)
oo-NetOneLink l =
  OffersOnly-∖ _ (OffersOnly-Par _ _
    (OffersOnly-∖ _ (OffersOnly-Par _ _
      (oo-Inputsₗ l) (OffersOnly-⦀ (oo-Transmitterₗ l) (oo-RcvAckₗ l))))
    (OffersOnly-∖ _ (OffersOnly-Par _ _
      (oo-Outputsₗ l) (OffersOnly-⦀ (oo-Receiverₗ l) (oo-SndAckₗ l)))))

-- link l's copy bundle only ever offers link-l events.
oo-linkCopy : (l : Link) → OffersOnly (linkAlpha l) (linkCopy l)
oo-linkCopy l = oo-⦀⋆-map (λ { (d , id) → oo-Copy l d id }) (linkConfig l)
