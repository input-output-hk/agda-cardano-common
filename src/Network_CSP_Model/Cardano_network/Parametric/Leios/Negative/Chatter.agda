{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — NEGATIVE FACT 1: THE UNCHANGED RELAY CHATTERS.
--
-- `Parametric.NodeLogic.lnServerLoop` takes a held block out of the store
-- and announces it, forever, and `NodeLogic.offerHeld` never removes a
-- block — so with ONE block in the store the announcer and the store can
-- rendezvous and announce for ever.  Hide the store and LeiosNotify
-- channels and that run is an infinite τ-path: `Diverges`.  Every `⊑FD`
-- liveness specification over such a composite is refuted outright (at
-- `⊑F` it would instead be satisfied VACUOUSLY, which is worse).
--
-- THIS IS WHY DESIGN LAW L EXISTS.  `NodeLogicL.lnServerLoopL` carries a
-- read pointer and so announces each held block ONCE per endpoint; with
-- the pointer caught up it BLOCKS at the store, and the cycle below cannot
-- be formed.  `pointer-exhausted` at the bottom is that contrast.
--
-- LEVEL: the THREAD/STORE PAIR, not `systemOf`.  Pair level; the
-- system-level statement would need the far node's LN client driven across
-- two hidden medium cells and is not established.  This is the same level
-- `Parametric.AnnounceSafeNegative` and `Parametric.RelayLive` reach, and
-- for the same reason.  Nothing here is a claim about `systemOf`.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.Negative.Chatter where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine)
open import Cardano_network.Base using (lo; hi)
open import Cardano_network.Net leiosLParams
  using ( Net_Api; Net_Api-≟; store; env; apiLN; apiCS; apiBF; apiTS; apiKA; apiLF; apiLP
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done; break
        ; sendLNBlockAnnouncement )
open import Cardano_network.Data leiosLParams using (Payload; Header; header)
open import Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc)
open import Cardano_network.Params using (Params)
open Params leiosLParams using (Block)

import Cardano_network.Parametric.NodeLogic as NL
open NL.Generic leiosLParams leiosLLine apiES
  using (lnServerLoop; blockStore; storeES; getEv)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using (blockStoreL; getAtEv)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (EventSet; chanSet; viewV; _∥⇘_⇙_; _∖_)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_─[_]─►_; τ; sVis; sSil)
open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (Diverges)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-sync; Par-soloL; Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload})
  using (Hide-τ; Hide-hidden)

-- a state with a τ-cycle of length four back to itself diverges.  The corecursive
-- call sits directly under the fourth `.rest` copattern, so it is guarded
-- (`Semantics.DRBisim.div-diverges`'s shape).
τ-cycle→Diverges : ∀ {P P₁ P₂ P₃ : Proc}
                 → P ─[ τ ]─► P₁ → P₁ ─[ τ ]─► P₂ → P₂ ─[ τ ]─► P₃ → P₃ ─[ τ ]─► P
                 → Diverges P
τ-cycle→Diverges {P₁ = P₁} s₁ s₂ s₃ s₄ .Diverges.next = P₁
τ-cycle→Diverges s₁ s₂ s₃ s₄ .Diverges.step = s₁
τ-cycle→Diverges {P₂ = P₂} s₁ s₂ s₃ s₄ .Diverges.rest .Diverges.next = P₂
τ-cycle→Diverges s₁ s₂ s₃ s₄ .Diverges.rest .Diverges.step = s₂
τ-cycle→Diverges {P₃ = P₃} s₁ s₂ s₃ s₄ .Diverges.rest .Diverges.rest .Diverges.next = P₃
τ-cycle→Diverges s₁ s₂ s₃ s₄ .Diverges.rest .Diverges.rest .Diverges.step = s₃
τ-cycle→Diverges {P = P} s₁ s₂ s₃ s₄ .Diverges.rest .Diverges.rest .Diverges.rest .Diverges.next = P
τ-cycle→Diverges s₁ s₂ s₃ s₄ .Diverges.rest .Diverges.rest .Diverges.rest .Diverges.step = s₄
τ-cycle→Diverges s₁ s₂ s₃ s₄ .Diverges.rest .Diverges.rest .Diverges.rest .Diverges.rest =
  τ-cycle→Diverges s₁ s₂ s₃ s₄

-- node 0 of the line: degree 1, its only endpoint is `(link 0 , lo)`
nA : Fin 3
nA = fzero

-- the one block in the store; `Block = Maybe Bool`, and any block will do
blk : Block
blk = just true

-- THE HIDDEN ALPHABET: every store channel and every LeiosNotify api channel.  These
-- are exactly the two channels the chatter cycle rides on; `env` is deliberately kept
-- VISIBLE, so nothing about the forge is hidden.
hideSet : AnyTypes (Net_Api Payload) → Set
hideSet (_ , store _ _ _) = ⊤
hideSet (_ , apiLN _ _ _) = ⊤
hideSet _                 = ⊥

-- decidability of `hideSet` membership (one clause per `Net_Api` constructor)
hideSet-dec : (at : AnyTypes (Net_Api Payload)) → Dec (hideSet at)
hideSet-dec (_ , store  _ _ _) = yes tt
hideSet-dec (_ , apiLN  _ _ _) = yes tt
hideSet-dec (_ , env    _ _ _) = no λ ()
hideSet-dec (_ , tx     _ _ _) = no λ ()
hideSet-dec (_ , input  _ _ _) = no λ ()
hideSet-dec (_ , output _ _ _) = no λ ()
hideSet-dec (_ , sndmsg _ _ _) = no λ ()
hideSet-dec (_ , rcvmsg _ _ _) = no λ ()
hideSet-dec (_ , sndack _ _ _) = no λ ()
hideSet-dec (_ , rcvack _ _ _) = no λ ()
hideSet-dec (_ , ack    _ _ _) = no λ ()
hideSet-dec (_ , done   _ _ _) = no λ ()
hideSet-dec (_ , apiCS  _ _ _) = no λ ()
hideSet-dec (_ , apiBF  _ _ _) = no λ ()
hideSet-dec (_ , apiTS  _ _ _) = no λ ()
hideSet-dec (_ , apiKA  _ _ _) = no λ ()
hideSet-dec (_ , apiLF  _ _ _) = no λ ()
hideSet-dec (_ , apiLP  _ _ _) = no λ ()
hideSet-dec (_ , break  _)     = no λ ()

-- the hidden alphabet as an `EventSet`
hideES : EventSet
hideES = chanSet hideSet hideSet-dec

-- THE OBJECT UNDER TEST: node 0's UNCHANGED LN announce thread against its UNCHANGED
-- block store holding one block, with the store and LeiosNotify channels hidden
chatterPair : Proc
chatterPair =
  (lnServerLoop nA (fzero , lo) ∥⇘ storeES ⇙ blockStore nA (blk ∷ [])) ∖ hideES

-- the announcement channel of node 0's only endpoint.  `lnServerLoop n (l , d)` drives
-- `opposite d`, so the LN SERVER peer of `(link 0 , lo)` sits at `hi`.
annEv : Net_Api Payload Header
annEv = apiLN fzero hi sendLNBlockAnnouncement

-- STEP 1 of the cycle: the hidden `stGet ! blk` rendezvous
τ₁ : Σ[ C₁ ∈ Proc ] (chatterPair ─[ τ ]─► C₁)

-- STEP 2: the store's loop-back `sil`, so it is back at its menu
τ₂ : Σ[ C₂ ∈ Proc ] (proj₁ τ₁ ─[ τ ]─► C₂)

-- STEP 3: the hidden announcement, taken solo by the thread
τ₃ : Σ[ C₃ ∈ Proc ] (proj₁ τ₂ ─[ τ ]─► C₃)

-- STEP 4: the thread's loop-back `sil` — and the pair is back where it started
τ₄ : proj₁ τ₃ ─[ τ ]─► chatterPair

-- the `stGet ! blk` is in `storeES`, so the announce thread and the store RENDEZVOUS
-- on it (`Par-sync`); it is in `hideES`, so the rendezvous becomes a τ.
τ₁ = _ , Hide-hidden hideES _ {e = getEv nA} {a = blk} tt
           (Par-sync storeES _ _ _ {e = getEv nA} {a = blk} tt
                     (sVis refl refl) (sVis refl refl))

-- having handed the block over, the store returns `Ret held` to `iter`, whose `sil`
-- guard is one τ on the RIGHT operand, which `Hide-τ` passes straight through.  Taken
-- BEFORE the announcement so that the store is back at a `react` menu when
-- `Par-soloL` has to observe that it offers no `apiLN`.
τ₂ = _ , Hide-τ hideES _ (Par-τ-R storeES _ _ _ (sSil refl))

-- `apiLN … sendLNBlockAnnouncement` is NOT in `storeES`, so the thread takes it alone
-- (`Par-soloL`, with `refl` witnessing that the store's menu offers nothing on that
-- channel); it IS in `hideES`, so it becomes a τ.
τ₃ = _ , Hide-hidden hideES _ {e = annEv} {a = header blk} tt
           (Par-soloL storeES _ _ _ {e = annEv} {a = header blk}
                      (λ ()) (sVis refl refl) refl)

-- the announce body ends in `Skip`, so `iter` loops back with one `sil` on the LEFT
-- operand — and both operands are now literally their initial terms again
τ₄ = Hide-τ hideES _ (Par-τ-L storeES _ _ _ (sSil refl))

-- THE NEGATIVE FACT: the unchanged announcer and the unchanged store, with one block
-- held and the store/LeiosNotify channels hidden, have an infinite τ-run
chatter-diverges : Diverges chatterPair
chatter-diverges = τ-cycle→Diverges (proj₂ τ₁) (proj₂ τ₂) (proj₂ τ₃) τ₄

-- THE CONTRAST (design law L).  The pointer-carrying store of `NodeLogicL` offers a
-- held block at its INDEX only: with one block held it offers `stGetAt 0` and nothing
-- at `stGetAt 1`.  So `lnServerLoopL`, having announced that block and advanced its
-- pointer to 1, BLOCKS at the store instead of re-announcing — no second rendezvous,
-- hence no τ-cycle of the shape above.
pointer-exhausted : viewV (PTree.force (blockStoreL nA (blk ∷ []))) (Block , getAtEv nA 1) blk
                  ≡ nothing
pointer-exhausted = refl
