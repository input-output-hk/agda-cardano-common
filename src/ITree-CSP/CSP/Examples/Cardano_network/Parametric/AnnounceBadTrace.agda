{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE BAD TRACE: a machine-checked run of the
-- DELIBERATELY BROKEN relay logic (`Parametric.AnnounceBadLogic`) that
-- announces an EB hash no mint ever produced.
--
-- WHAT THIS MODULE PROVIDES.  One theorem, `bad-announce-fires`: the
-- four-event trace
--
--   ⟨ env 0 lo envMint ! (nothing , just true)
--   , output 0 hi N2N_LeiosNotify ! MsgLNRequestNext
--   , store 0 lo stGet ! (just true)
--   , apiLN 0 hi sendLNBlockAnnouncement ! header (just true) ⟩
--
-- is a trace of node 0 of the concrete Leios line running `nodeLogicBad`
-- from an EMPTY store.  The mint carries `nothing` as its EB, so it adds
-- NOTHING to the minted set, yet the announced RB `just true` announces
-- the EB hash `true`.  `Parametric.AnnounceSafeNegative` turns that into
-- the refutation; this module only exhibits the run.
--
-- WHY THE MINT IS THE FIRST EVENT.  `nodeLogicBad n []` starts with an
-- empty store, so `offerHeld` is `Stop` and no `getEv` is available.  The
-- mint is what puts the ill-announced block in: the real
-- `NodeLogic.acceptMint` would DISCARD it (`announcedEB (just true) =
-- just true` but `ebHash <$> nothing = nothing`), and `acceptMintBad`
-- keeps it.  That single difference is the whole negative control.
--
-- WHICH LEVEL.  The run is over ONE NODE — `node nA (nodeLogicBad nA [])`
-- — exactly the level `Parametric.RelayLive.announce-fires` reaches, and
-- for the same reason: a level-1 witness over `systemOf` would have to
-- drive the far node's LN client across two hidden medium cells, many
-- more steps each normalising a strictly larger term.  Nothing here
-- should be read as a claim about `systemOf`.
--
-- PROOF TECHNIQUE.  The six steps are assembled from the parallel
-- transition INTRO lemmas of `CSP.Laws.Traces.TraceLawsParallel`, exactly
-- as in `Parametric.RelayLive`; the last four are that module's four
-- steps, which go through unchanged because `nodeLogicBad` differs from
-- `nodeLogic` only inside the mint clause of the store.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.AnnounceBadTrace where

open import Level using (0ℓ)
import Data.Unit.Polymorphic as Poly
open import Data.Unit using (tt)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (refl)

open import Process_Trees using (ExtI)

open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.LeiosInstance
  using (leiosParams; leiosLine)
open import CSP.Examples.Cardano_network.Base
  using (lo; hi; N2N_LeiosNotify; FromInitiator)
open import CSP.Examples.Cardano_network.Net leiosParams
  using ( Net_Api; Net_Api-≟; output; store; env; apiLN
        ; stGet; envMint; sendLNBlockAnnouncement )
open import CSP.Examples.Cardano_network.Data leiosParams
  using (Payload; Header; header; leiosNotify; MsgLNRequestNext)
open import CSP.Examples.Cardano_network.ApiAlphabet leiosParams using (apiES)
open import CSP.Examples.Cardano_network.Parametric.Node leiosParams leiosLine apiES
  using (Proc; node)
import CSP.Examples.Cardano_network.Parametric.AnnounceBadLogic as BL
open BL.Generic leiosParams leiosLine apiES using (nodeLogicBad)

open Params leiosParams using (Block; EB)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Failures
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-sync; Par-soloL; Par-soloR; Par-τ-L; Par-τ-R)

------------------------------------------------------------------------
-- The scenario
------------------------------------------------------------------------

-- the node under test: node 0 of the Leios line, degree 1, its only endpoint being
-- `(link 0 , lo)` — so its server peers, and hence its announcements, sit at `hi`
nA : Fin 3
nA = fzero

-- the ill-announced ranking block: it announces the EB whose hash is `true`
-- (`leiosParams.announcedEB = λ b → b`, `Block = Maybe Bool`)
blk : Block
blk = just true

-- THE PROCESS UNDER TEST: node 0's whole link bundle synchronised on `apiES` with the
-- BROKEN relay logic, its store initially EMPTY
badNode : Proc
badNode = node nA (nodeLogicBad nA [])

------------------------------------------------------------------------
-- The four visible events of the bad trace
------------------------------------------------------------------------

-- event 1: THE ILL-ANNOUNCED MINT.  Its EB component is `nothing`, so it mints NO EB
-- at all and the specification's minted set stays empty; its RB component is `blk`,
-- which announces the EB hash `true`.  `NodeLogic.acceptMint` would drop the block;
-- `AnnounceBadLogic.acceptMintBad` stores it.
evMint : Event√ (Poly.⊤ {0ℓ})
evMint = evl (evLabel (Maybe EB × Block) (env fzero lo envMint) (nothing , blk))

-- the LeiosNotify request as it arrives off the wire at direction `hi`: the only thing
-- that moves an LN server peer out of `stIdle` (cf. `RelayLive.reqMsg`)
reqMsg : Payload
reqMsg = tt , FromInitiator , tt , leiosNotify MsgLNRequestNext

-- event 2: the request reaching node 0's LN server peer
evReq : Event√ (Poly.⊤ {0ℓ})
evReq = evl (evLabel Payload (output fzero hi N2N_LeiosNotify) reqMsg)

-- event 3: the announce thread taking the ill-announced block out of node 0's store
evGet : Event√ (Poly.⊤ {0ℓ})
evGet = evl (evLabel Block (store fzero lo stGet) blk)

-- event 4: THE UNSAFE ANNOUNCEMENT — an EB hash that no mint produced
evAnn : Event√ (Poly.⊤ {0ℓ})
evAnn = evl (evLabel Header (apiLN fzero hi sendLNBlockAnnouncement) (header blk))

------------------------------------------------------------------------
-- The six steps
--
-- Each is stated as "there is a state such that …", so the target of one step is
-- `proj₁` of it and the next step's source.
------------------------------------------------------------------------

-- STEP 1.  THE ILL-ANNOUNCED MINT.  `env ∉ apiES`, so the bundle stays put
-- (`Par-soloR`); inside the logic the event IS in `storeES`, so the mint thread (left
-- of the `⦀`) and the broken block store synchronise on it, and `acceptMintBad`
-- accepts `blk` into the store with no announcement check.
step₁ : Σ[ P₁ ∈ Proc ] (badNode ─[ ev evMint ]─► P₁)
step₁ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
      (sVis refl refl))
    refl

-- STEP 2.  The store's loop-back: having accepted the mint it returns the new `Held`
-- to `iter`, whose `sil` guard is one τ.  Without it the store is not back at its menu
-- and cannot offer the block.
step₂ : Σ[ P₂ ∈ Proc ] (proj₁ step₁ ─[ τ ]─► P₂)
step₂ = _ , Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (sSil refl))

-- STEP 3.  The LeiosNotify request arrives.  `output ∉ apiES`, so the bundle takes it
-- alone; inside the bundle only the LN server peer at `hi` offers it, so it rides past
-- the nine peers before it and the one after it.
step₃ : Σ[ P₃ ∈ Proc ] (proj₁ step₂ ─[ ev evReq ]─► P₃)
step₃ = _ ,
  Par-soloL _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
      refl) refl) refl) refl) refl) refl) refl) refl) refl)
    refl

-- STEP 4.  The LN server peer's loop-back: having consumed the request it returns
-- `stBusy` to `iter`, whose `sil` guard is one τ.
step₄ : Σ[ P₄ ∈ Proc ] (proj₁ step₃ ─[ τ ]─► P₄)
step₄ = _ ,
  Par-τ-L _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-L _ _ _ _ (sSil refl)))))))))))

-- STEP 5.  The announce thread takes the ill-announced block out of the store.
-- `store ∉ apiES` so the bundle stays put, while inside the logic the event IS in
-- `storeES`, so the thread group and the broken block store synchronise on it.
step₅ : Σ[ P₅ ∈ Proc ] (proj₁ step₄ ─[ ev evGet ]─► P₅)
step₅ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)
        refl) refl) refl)
      (sVis refl refl))
    refl

-- STEP 6.  THE UNSAFE ANNOUNCEMENT.  `apiLN ∈ apiES`, so this is a genuine rendezvous
-- between the LN server PEER (in `stBusy`, thanks to step 3) and the node's
-- `lnServerLoop` THREAD (holding the block, thanks to step 5).
step₆ : Σ[ P₆ ∈ Proc ] (proj₁ step₅ ─[ ev evAnn ]─► P₆)
step₆ = _ ,
  Par-sync _ _ _ _ _
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
      refl) refl) refl) refl) refl) refl) refl) refl) refl)
    (Par-soloL _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)
        refl) refl) refl)
      refl)

------------------------------------------------------------------------
-- THE BAD TRACE
------------------------------------------------------------------------

-- THE BROKEN NODE ANNOUNCES AN UNMINTED EB HASH.  Node 0 of the concrete Leios line,
-- running `nodeLogicBad` from an empty store, has a trace whose only mint carries NO
-- EB and whose last event announces the EB hash `true`.
--
-- LEVEL 2 of the acceptance ladder, not level 1: over `node n (nodeLogicBad n [])`,
-- not over `systemOf`.  See the module header.
bad-announce-fires : traces badNode (evMint ∷ evReq ∷ evGet ∷ evAnn ∷ [])
bad-announce-fires =
  _ , ⟹-ev (proj₂ step₁)
      (⟹-τ (proj₂ step₂)
      (⟹-ev (proj₂ step₃)
      (⟹-τ (proj₂ step₄)
      (⟹-ev (proj₂ step₅)
      (⟹-ev (proj₂ step₆) ⟹-refl)))))
