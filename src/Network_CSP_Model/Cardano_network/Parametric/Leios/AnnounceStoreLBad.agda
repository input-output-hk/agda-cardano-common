{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE NEGATIVE CONTROL FOR S0's STORE HALF:
-- `acceptForgeL`'s WITHHOLDING ARM is LOAD-BEARING.
--
-- `AnnounceStoreL.wf-blockStoreL` proves `Wf storeG ms (blockStoreL n held)`
-- for every `Params`, every `LeiosParams`, every topology, every node and
-- every well-announced store: the RB store of `nodeLogicL` never hands out a
-- block announcing an EB hash no forge produced.
--
-- Its forge arm has TWO branches, and only one of them is guarded.  A
-- certificate-free RB goes through `NodeLogic.acceptForge`, whose guard
-- `announcedEB b ≡ (ebHash <$> me)` IS the announcement seed.  A
-- CERTIFICATE-CARRYING RB is WITHHELD outright — `acceptForgeL` returns `held`
-- untouched — and that withholding is the only thing standing between the
-- store and an unchecked deposit, because the `env … envForge` channel is
-- deliberately absent from `BlockProvenance.Carries` and so carries no rely
-- whatsoever.  `acceptForgeLBad` below ADMITS the cert-carrying RB instead of
-- withholding it, changing nothing else, and the store invariant FAILS.
--
-- THE WRITE-UP RULE — READ THIS BEFORE QUOTING EITHER RESULT.
-- `wf-blockStoreL` is ∀-`Params`, ∀-`LeiosParams`, ∀-topology and ∀-node,
-- premise-free but for the store invariant it transports.  THE REFUTATION IS
-- NOT: it is at the concrete `leiosLParams` line, at node 0, at the shipped
-- `leiosLP`'s non-trivial `rbCert`, and it is a STORE-LEVEL fact — about
-- `blockStoreL` alone, not about a node and not about a system.  Never state
-- the two quantifications in one sentence, and never read a node- or
-- system-level break out of it.  Quote it as "the withholding arm of
-- `acceptForgeL` is load-bearing", never as "certificate RBs break
-- announcement safety".
--
-- WHAT THE REFUTATION SPENDS.  Three steps of the store ALONE, from the EMPTY
-- store and the EMPTY forged set:
--
--   1. the environment offers the forge `(nothing , bCert)`.  Its EB component
--      is `nothing`, so it forges NO EB and the forged set stays empty; its RB
--      component announces the EB hash `false`.  `blockOK-forge` discharges the
--      step's own obligation — there IS no rely at a forge.
--   2. the store's loop-back τ, which puts it back at its menu.
--   3. the menu now OFFERS `bCert` on `store … stGet`, which IS one of
--      `storeG`'s guarantee channels, so `nowW` demands `WellAnnounced [] bCert`.
--      It is false.
--
-- WHY THE HONEST BRANCH CANNOT BE BLAMED.  `withheld`/`admitted` below pin that
-- the two forge arms differ on this very offer, and `honest-branch-drops` pins
-- that `NodeLogic.acceptForge` would have dropped `bCert` too — so the defect is
-- located at the `rbCert b ≡ just _` arm and nowhere else.
--
-- `Parametric.Leios.NodeLogicL` itself is NOT modified: `acceptForgeL` and
-- `acceptForgeLBad` coexist, which is what lets the two be compared.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.AnnounceStoreLBad where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; reverse)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl)
-- the `DecEq (List Block)` instance the `□`s of the store step need (`Held` is a list)
open import Class.DecEq.Instances using (DecEq-List)

open import Process_Trees using (ExtI)
open import Cardano_network.Base using (Dir; lo)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine)
open import Cardano_network.Net leiosLParams
  using (Net_Api; Net_Api-≟; store; stGet; env; envForge)
open import Cardano_network.Data leiosLParams using (Payload)
open import Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc)
import CSP.Operators as O
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.AnnounceInvariant as AI
import Cardano_network.Parametric.BlockProvenance as BP
import Cardano_network.Parametric.BlockProvenanceNode as BPN
import Cardano_network.Parametric.Leios.AnnounceStoreL as ASL

open Params leiosLParams using (Block; EB)
open LeiosP.LeiosParams leiosLP using (rbCert)

open O {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (Ret; Prefix; _□_; loop)
open NL.Generic leiosLParams leiosLLine apiES
  using (Held; StoreProc; forgeEv; putEv; offerHeld; acceptForge)
open NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using (offerIx; getAtEv; acceptForgeL; blockStoreL; memberOf)
open AI.Generic leiosLParams leiosLLine apiES using (WellAnnounced)
open BP.Generic leiosLParams leiosLLine apiES
  using (Wf; nowW; stepW; blockOK-forge; c-stGet)
open BPN.Generic leiosLParams leiosLLine apiES using (storeG)
open ASL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n) using (wf-blockStoreL)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (Event√; ev; τ; evl; evLabel; _─[_]─►_; sVis; sSil)

------------------------------------------------------------------------
-- THE BREAK
------------------------------------------------------------------------

-- the node under test: node 0 of the Linear-Leios line, degree 1, its only endpoint
-- being `(link 0 , lo)` — so its store and env channels are `store/env fzero lo _`
nA : Fin 3
nA = fzero

-- THE CERTIFICATE-CARRYING BLOCK the environment offers.  At `leiosLParams`
-- `announcedEB` is the identity, so this block announces the EB hash `false`; nothing
-- has been forged, so it is not well-announced against the empty forged set.
bCert : Block
bCert = just false

-- NON-VACUITY: the block really does carry a certificate at the SHIPPED `leiosLP`, so
-- the store's forge arm really does take its withholding branch on this offer.  Were
-- `rbCert` ever weakened to `λ _ → nothing` this `refl` would go red, and so would the
-- refutation below — the control cannot silently become vacuous.
bCert-carries-cert : rbCert bCert ≡ just (just true)
bCert-carries-cert = refl

-- THE BREAK.  `NodeLogicL.acceptForgeL` WITHHOLDS a certificate-carrying forged RB —
-- the deposit is `forgeL`'s own, one `stHasCert` rendezvous later — so the store's
-- `held` is untouched and the announcement seed is never needed on that branch.  This
-- version ADMITS it instead.  The certificate-free branch is byte-identical to the
-- original's, so this is the single deliberate defect of the negative control.
acceptForgeLBad : Maybe EB × Block → Held → Held
acceptForgeLBad (me , b) held with rbCert b
... | just _  = b ∷ held
... | nothing = acceptForge (me , b) held

-- the two forge arms DIFFER on this very offer: the honest store withholds …
withheld : acceptForgeL (nothing , bCert) [] ≡ []
withheld = refl

-- … and the broken one admits, with no announcement check anywhere on the path
admitted : acceptForgeLBad (nothing , bCert) [] ≡ bCert ∷ []
admitted = refl

-- …and the HONEST branch cannot be blamed for the difference: `NodeLogic.acceptForge`,
-- which is what a certificate-FREE forge goes through, would have dropped `bCert` too.
-- So the defect is at the `rbCert b ≡ just _` arm and nowhere else.
honest-branch-drops : acceptForge (nothing , bCert) [] ≡ []
honest-branch-drops = refl

-- one step of the BROKEN RB store: `NodeLogicL.storeStepL` character for character,
-- with `acceptForgeLBad` in place of `acceptForgeL` in the forge clause
storeStepLBad : Fin 3 → Held → StoreProc
storeStepLBad n held =
    (forgeEv n ⟶ (λ mb → Ret (acceptForgeLBad mb held)))
  □ ((putEv n ⟶ (λ b → Ret (if memberOf b held then held else b ∷ held)))
  □ (offerHeld n held held
  □  offerIx (getAtEv n) (reverse held) 0 held))

-- the broken RB store holding `held`: `NodeLogicL.blockStoreL` over `storeStepLBad`
blockStoreLBad : Fin 3 → Held → Proc
blockStoreLBad n held = loop (storeStepLBad n) held

------------------------------------------------------------------------
-- The two visible events of the bad trace
------------------------------------------------------------------------

-- event 1: THE CERTIFICATE FORGE.  Its EB component is `nothing`, so it forges NO EB
-- and the forged set stays empty; its RB component is `bCert`, which announces `false`.
evForge : Event√ (⊤ {0ℓ})
evForge = evl (evLabel (Maybe EB × Block) (env fzero lo envForge) (nothing , bCert))

-- event 2: the store OFFERING the ill-announced block back out on `stGet` — one of
-- `storeG`'s own guarantee channels, which is what makes `nowW` bite
evGet : Event√ (⊤ {0ℓ})
evGet = evl (evLabel Block (store fzero lo stGet) bCert)

------------------------------------------------------------------------
-- The three steps of the store alone
------------------------------------------------------------------------

-- STEP 1.  The forge fires on the store's own first `□` operand, and `acceptForgeLBad`
-- admits `bCert` into `held` with no announcement check.
step₁ : Σ[ P₁ ∈ Proc ] (blockStoreLBad nA [] ─[ ev evForge ]─► P₁)
step₁ = _ , sVis refl refl

-- STEP 2.  The store's loop-back: having served the forge it returns the new `Held` to
-- `iter`, whose `sil` guard is one τ.  Without it the store is not back at its menu.
step₂ : Σ[ P₂ ∈ Proc ] (proj₁ step₁ ─[ τ ]─► P₂)
step₂ = _ , sSil refl

-- STEP 3.  THE MENU OFFERS THE ILL-ANNOUNCED BLOCK.  `offerHeld nA (bCert ∷ []) …`
-- offers `stGet ! bCert`, which is the whole content of the store's guarantee.
step₃ : Σ[ P₃ ∈ Proc ] (proj₁ step₂ ─[ ev evGet ]─► P₃)
step₃ = _ , sVis refl refl

------------------------------------------------------------------------
-- THE NEGATIVE CONTROL
------------------------------------------------------------------------

-- the ill-announced block is not well-announced against the EMPTY forged set: it
-- announces the EB hash `false` (`announcedEB` is the identity at `leiosLParams`,
-- `bCert = just false`), and nothing at all has been forged
¬wellAnnounced-bCert : ¬ WellAnnounced [] bCert
¬wellAnnounced-bCert (inj₁ ())
¬wellAnnounced-bCert (inj₂ (_ , _ , ()))

-- THE REFUTATION: admitting the certificate-carrying forge BREAKS the RB store's
-- announcement invariant.  Walk `stepW` over the forge (whose own label is
-- `blockOK-forge` — a forge carries no block, so the store learns nothing from it, and
-- since its EB component is `nothing` the forged set stays `[]`) and over the store's
-- loop-back τ; at the state so reached the broken store OFFERS `bCert` on `stGet`,
-- which IS in `storeG`, so `nowW` demands it be well-announced against `[]`.  It is not.
--
-- LEVEL: the RB STORE alone, the shape `wf-blockStoreL` has.  SCOPE: this instance,
-- this node, the shipped `rbCert`.  WRITE-UP RULE: never pair this with
-- `wf-blockStoreL`'s "∀ Params", and never quote it as a node- or system-level break.
¬wf-blockStoreLBad : ¬ Wf storeG [] (blockStoreLBad nA [])
¬wf-blockStoreLBad w =
  ¬wellAnnounced-bCert
    (nowW (stepW (stepW w ⊆-refl (proj₂ step₁) blockOK-forge) ⊆-refl (proj₂ step₂) tt)
          ⊆-refl tt (proj₂ step₃) c-stGet)

-- THE CONTROL'S OWN CONTROL — the POSITIVE ITSELF, at the same instance, the same node
-- and the same empty store: `AnnounceStoreL.wf-blockStoreL`, no separate assembly.  So
-- the pair above and below differs in exactly ONE branch of ONE definition.
wf-blockStoreL-good : Wf storeG [] (blockStoreL nA [])
wf-blockStoreL-good = wf-blockStoreL nA All.[]
