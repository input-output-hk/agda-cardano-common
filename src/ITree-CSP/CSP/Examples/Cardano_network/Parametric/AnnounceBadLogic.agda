{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — A DELIBERATELY BROKEN RELAY LOGIC, for use
-- as the NEGATIVE CONTROL of the announcement-safety campaign.
--
-- WHY THIS MODULE EXISTS.  `Parametric.AnnounceSafeConcrete.announceSafeT`
-- proves that the N-node relay network never announces an EB hash that
-- no mint produced.  A safety theorem whose guarded event can never
-- occur is worthless, and this campaign has already shipped that failure
-- mode twice (a RUN-shaped spec that imposed an offer obligation instead
-- of a safety constraint; server threads driving the wrong direction over
-- a medium with no LeiosNotify cell, so no announcement was reachable at
-- all).  `Parametric.RelayLive` answers the "is the announcement
-- reachable?" half.  This module and `Parametric.AnnounceSafeNegative`
-- answer the other half: is the SAFETY GUARD load-bearing?
--
-- WHAT IS BROKEN, AND ONLY THAT.  Exactly one definition changes.
-- `NodeLogic.acceptMint` accepts a mint `(me , b)` only when
-- `announcedEB b ≡ (ebHash <$> me)` — the guard Task 5 identified as the
-- seed of the announcement invariant.  `acceptMintBad` DROPS that guard
-- and accepts every mint.  `storeStepBad`/`blockStoreBad`/`nodeLogicBad`
-- are otherwise character-for-character the originals, and reuse
-- `NodeLogic.Generic`'s own `mintEv`/`putEv`/`offerHeld`/`storeES`/
-- `mint`/`allThreads`, so nothing else can differ by accident.
--
-- `Parametric.NodeLogic` itself is NOT modified: the real logic and the
-- broken one coexist, which is what lets the two be compared.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.AnnounceBadLogic where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_; _,_)
-- the `DecEq (List Block)` instance the `□`s of the store step need (`Held` is a list)
open import Class.DecEq.Instances using (DecEq-List)

open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL

------------------------------------------------------------------------
-- The generic layer — same three parameters as `Parametric.NodeLogic.Generic`
------------------------------------------------------------------------

-- the BROKEN relay logic, parametric in the network parameters, the topology and
-- the api alphabet, so it slots into `Parametric.Node.node`/`systemOfWith` exactly
-- where the real `NodeLogic.Generic.nodeLogic` does
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open Params p using (Block; EB; decBlock)
  open N p using (Net_Api; Net_Api-≟)
  open D p using (Payload)
  open Topology t using (Node)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using (_∥⇘_⇙_; _⦀_; _□_; Ret; Prefix; loop)
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES using (Proc)
  open NL.Generic p t apiES
    using (Held; StoreProc; mintEv; putEv; offerHeld; storeES; mint; allThreads)

  -- THE BREAK.  `NodeLogic.acceptMint` keeps a minted RB only when its announcement
  -- matches the minted EB (`announcedEB b ≡ (ebHash <$> me)`); this version keeps
  -- EVERY minted RB, so a block announcing an EB that no mint produced can enter the
  -- store.  This is the single deliberate defect of the negative control.
  acceptMintBad : Maybe EB × Block → Held → Held
  acceptMintBad (_ , b) hs = b ∷ hs

  -- one store step of the broken store: identical to `NodeLogic.storeStep` except
  -- that the mint clause calls `acceptMintBad`
  storeStepBad : Node → Held → StoreProc
  storeStepBad n held =
      (mintEv n ⟶ (λ mb → Ret (acceptMintBad mb held)))
    □ ((putEv n ⟶ (λ b → Ret (b ∷ held)))
    □  offerHeld n held held)

  -- the broken block store holding `held`: `NodeLogic.blockStore` over `storeStepBad`
  blockStoreBad : Node → Held → Proc
  blockStoreBad n held = loop (storeStepBad n) held

  -- THE BROKEN RELAY NODE LOGIC: `NodeLogic.nodeLogic` with the broken store in place
  -- of the real one.  Every thread — mint, client, server, LN client, LN announcer —
  -- is `NodeLogic.Generic`'s own, unchanged.
  nodeLogicBad : Node → Held → Proc
  nodeLogicBad n held = (mint n ⦀ allThreads n) ∥⇘ storeES ⇙ blockStoreBad n held
