{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S0's REACHABILITY CONTROL: with the forge
-- route's ANNOUNCEMENT CHECK removed, THE GATED EVENT REALLY FIRES.
--
-- WHY THIS MODULE EXISTS.  Of the six network-wide theorems on this
-- branch, S0 (`Leios/AnnounceSystemL.annSafeLT`) was the one with no
-- theorem-shaped control: each of the other five has a `…-node-FAILS`
-- refutation of its own discipline at node level (S1
-- `BodyOriginBad.bodySound-node-FAILS`, S2
-- `VoteSoundBad.voteSound-node-FAILS`, S2′
-- `BlobOriginBad.blobSound-node-FAILS`, S3
-- `CertSoundBad.certSound-node-FAILS`, S4
-- `CertRbOriginBad.certRbSound-node-FAILS`), while S0 had only
-- `Leios/AnnounceStoreLBad.¬wf-blockStoreLBad` — a refutation of a
-- STORE-LEVEL LEMMA, not of anything shaped like the theorem.  What was
-- missing is machine-checked evidence that the announce gate is
-- REACHABLE AT ALL in the Leios composite, i.e. that S0 holds because
-- the system is safe and not because the gated event can never occur.
-- The campaign has reason to care: the original S0 brief would have
-- produced a VACUOUSLY TRUE theorem by three independent routes (the
-- wrong announce channel, the wrong peer bundle, and a premise false of
-- the shipped media), each of which would have typechecked green.
--
-- WHY A `traces` WITNESS AND NOT A `¬ _⊑T_`.  Announcement safety AT
-- NODE LEVEL is false-or-vacuous: keep the ungated wire deposit
-- (`storeStepL`'s `putEv` branch, which spec §4.5 requires) and a node
-- can announce a block a peer handed it, so a node-level S0 is FALSE;
-- remove it and the gate is unreachable, so a node-level S0 is VACUOUS.
-- There is therefore no node-level S0 to refute, and this control does
-- not try to state one.  It answers the other question instead — "once
-- the guard is gone, can the gated event happen?" — exactly as
-- `Parametric.AnnounceBadTrace.bad-announce-fires` does for the Praos
-- relay logic, whose shape (`traces badNode …`, not `¬ _⊑T_`) this
-- module follows deliberately.
--
-- WHAT IS BROKEN, AND ONLY THAT.  ONE guard.  `NodeLogicL.acceptForgeL`
-- dispatches on `rbCert b`: a certificate-carrying RB is WITHHELD, and a
-- certificate-free one goes through `NodeLogic.acceptForge`, whose guard
-- `announcedEB b ≡ (ebHash <$> me)` is the announcement seed.
-- `acceptForgeLAnnBad` below keeps the withholding arm BYTE-FOR-BYTE and
-- drops that one test, so an RB announcing an EB hash no forge produced
-- enters `held`.  The withholding arm is `AnnounceStoreLBad`'s guard and
-- has its own control; one guard, one control.  `forgeOK` — the SAME
-- test, inside the forge THREAD — is NOT touched either: it still
-- refuses the offer (`forgeOK-refuses` below), which is why the broken
-- node deposits nothing but the ranking block itself.
--
-- WHICH LEVEL — LEVEL 2 OF THE ACCEPTANCE LADDER.  The run below is over
-- `nodeP nA (nodeLogicLAnnBad nA st₀)`, i.e. ONE NODE: node 0 of the
-- concrete `leiosLParams`/`leiosLP` Leios line, its twelve prototype
-- peers synchronised on `apiES` with the Linear-Leios logic, every store
-- initially EMPTY.  It is NOT over `systemOfWithNode`, and nothing here
-- may be read as a fact about the network.
--
-- WHAT IT LICENSES, AND WHAT IT DOES NOT.  It licenses exactly this: with
-- the forge route's announcement check removed, the announcement gate IS
-- reachable — the node fires `apiLP … lnpSendBlockAnnouncement` carrying
-- the header of a block announcing an EB hash nothing forged, so S0's
-- gate is not idle machinery.  It is NOT a refutation of `annSafeLT`:
-- `annSafeLT` is about the UNBROKEN logic over the whole network, and
-- this run is over a BROKEN logic at one node of one instance.  WRITE-UP
-- RULE: never put this result and `annSafeLT`'s ∀-quantification in one
-- sentence.
--
-- `Parametric.Leios.NodeLogicL` is NOT modified: `acceptForgeL` and
-- `acceptForgeLAnnBad` coexist, which is what lets the two be compared.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.AnnounceReachLBad where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; if_then_else_)
import Data.Unit as U
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- the `DecEq (List Block)` instance the `□`s of the store step need (`Held` is a list)
open import Class.DecEq.Instances using (DecEq-List)

open import Process_Trees using (ExtI)
open import Cardano_network.Base
  using (lo; hi; N2N_LeiosNotify; FromInitiator)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine)
open import Cardano_network.Net leiosLParams
  using ( Net_Api; Net_Api-≟; store; stGetAt; env; envForge; output; apiLP
        ; lnpSendBlockAnnouncement )
open import Cardano_network.Data leiosLParams
  using (Payload; Header; header; leiosNotifyP; MsgLNPRequestNext)
open import Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc; nodeWith)
open import Cardano_network.Parametric.Leios.PeersP leiosLParams
  using (nodeBundleP)
import CSP.Operators as O
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.AnnounceSafe as AS

open Params leiosLParams using (Block; EB)
open LeiosP.LeiosParams leiosLP using (rbCert)

open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
  using (Ret; Prefix; _□_; loop; _⦀_; _∥⇘_⇙_)
open NL.Generic leiosLParams leiosLLine apiES
  using (Held; StoreProc; storeES; forgeEv; putEv; offerHeld; acceptForge)
open NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using ( StateL; st₀; offerIx; getAtEv; acceptForgeL; forgeOK; memberOf
        ; forgeL; ebIndex; voter; submit; certSink; allThreadsL
        ; blockStoreL; ebStore; bodyStore; mempool; voteStore )
-- S0's own announcement gate, at this instance: the `Bool` test `AnnounceSpecT`'s
-- offer map applies to `apiLP … lnpSendBlockAnnouncement`
open AS.Generic leiosLParams leiosLLine apiES using (announceOK)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Failures
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using ( Par-sync; Par-soloL; Par-soloR; Par-τ-L; Par-τ-R
        ; Par-brBoth; par-brNode-τL; par-brNode-τR )

------------------------------------------------------------------------
-- THE BREAK
------------------------------------------------------------------------

-- the node under test: node 0 of the Linear-Leios line, degree 1, its only endpoint
-- being `(link 0 , lo)` — so its store and env channels are `store/env fzero lo _`,
-- and its SERVER peers (hence its announcements) sit at `hi`
nA : Fin 3
nA = fzero

-- THE ILL-ANNOUNCED RANKING BLOCK.  `announcedEB` is the identity and `Block = Maybe
-- Bool` at `leiosLParams`, so this block announces the EB hash `true`.
blk : Block
blk = just true

-- it carries NO certificate at the shipped `leiosLP`, so `acceptForgeL`'s withholding
-- arm is not the arm under test here — the announcement test is
blk-cert-free : rbCert blk ≡ nothing
blk-cert-free = refl

-- THE BREAK.  `NodeLogicL.acceptForgeL` sends a certificate-FREE forged RB through
-- `NodeLogic.acceptForge`, whose guard is `announcedEB b ≡ (ebHash <$> me)`; this
-- version accepts it outright.  The certificate-carrying arm — the one
-- `AnnounceStoreLBad` breaks — is kept exactly as `acceptForgeL` has it, so this is
-- the single deliberate defect, and it is the announcement check and nothing else.
acceptForgeLAnnBad : Maybe EB × Block → Held → Held
acceptForgeLAnnBad (me , b) held with rbCert b
... | just _  = held
... | nothing = b ∷ held

-- THE HONEST GUARD REFUSES THE VERY SAME OFFER: with no EB forged alongside it, the
-- block's announcement cannot match, so `acceptForgeL` leaves the store empty …
honest-drops : acceptForgeL (nothing , blk) [] ≡ []
honest-drops = refl

-- … and the broken one admits it, with no announcement check anywhere on the path
admitted : acceptForgeLAnnBad (nothing , blk) [] ≡ blk ∷ []
admitted = refl

-- …AND THE HONEST GUARD IS NOT MERELY REFUSING EVERYTHING: offered the same block
-- TOGETHER WITH the EB it announces, `acceptForgeL` accepts it.  So what the break
-- removes is a real test, and what that test tests is the announcement.
honest-accepts-well-announced : acceptForgeL (just true , blk) [] ≡ blk ∷ []
honest-accepts-well-announced = refl

-- THE WITHHOLDING ARM IS UNTOUCHED: a certificate-carrying RB (`just false` at
-- `leiosLP`) is still withheld by the BROKEN store, exactly as `acceptForgeL` withholds
-- it.  This is what pins that the two S0 controls break DIFFERENT guards.
withholding-arm-intact : acceptForgeLAnnBad (nothing , just false) [] ≡ []
withholding-arm-intact = refl

-- THE FORGE THREAD'S COPY OF THE TEST IS UNTOUCHED TOO, and it still refuses: so the
-- broken node deposits no EB body and takes no certificate deposit on this pass, and
-- the only thing the defect lets through is the ranking block itself
forgeOK-refuses : forgeOK (nothing , blk) ≡ false
forgeOK-refuses = refl

-- one step of the BROKEN RB store: `NodeLogicL.storeStepL` character for character,
-- with `acceptForgeLAnnBad` in place of `acceptForgeL` in the forge clause
storeStepLAnnBad : Fin 3 → Held → StoreProc
storeStepLAnnBad n held =
    (forgeEv n ⟶ (λ mb → Ret (acceptForgeLAnnBad mb held)))
  □ ((putEv n ⟶ (λ b → Ret (if memberOf b held then held else b ∷ held)))
  □ (offerHeld n held held
  □  offerIx (getAtEv n) (reverse held) 0 held))

-- the broken RB store holding `held`: `NodeLogicL.blockStoreL` over `storeStepLAnnBad`
blockStoreLAnnBad : Fin 3 → Held → Proc
blockStoreLAnnBad n held = loop (storeStepLAnnBad n) held

-- THE CONTROL'S LOGIC: `nodeLogicL`'s composite EXACTLY — the five node-level threads,
-- the one incident endpoint's ten, and the same five stores on the same
-- `∥⇘ storeES ⇙` rendezvous — with ONE slot changed, `blockStoreLAnnBad` in place of
-- `blockStoreL`.  Nothing is pruned.
nodeLogicLAnnBad : Fin 3 → StateL → Proc
nodeLogicLAnnBad n (held , es , bs , ts , vs) =
  (forgeL n ⦀ (ebIndex n ⦀ (voter n ⦀ (submit n ⦀
     (certSink n ⦀ allThreadsL n)))))
    ∥⇘ storeES ⇙
  (blockStoreLAnnBad n held ⦀ (ebStore n es ⦀ (bodyStore n bs ⦀
     (mempool n ts ⦀ voteStore n vs))))

-- the node builder of the origin theorems and of `AnnounceSystemL.wf-nodeL`: the
-- twelve PROTOTYPE peers of one node synchronised on `apiES` with its logic
nodeP : Fin 3 → Proc → Proc
nodeP = nodeWith nodeBundleP

-- THE PROCESS UNDER TEST: node 0's prototype peer bundle synchronised on `apiES` with
-- the BROKEN logic, from `st₀` — no seeding, exactly the state `annSafeLT` is at
badNode : Proc
badNode = nodeP nA (nodeLogicLAnnBad nA st₀)

------------------------------------------------------------------------
-- NON-VACUITY OF THE GATE ITSELF
------------------------------------------------------------------------

-- THE LAST EVENT REALLY IS A VIOLATION: against the EMPTY forged set, S0's own gate
-- `announceOK` REFUSES the header of `blk`.  Were `announcedEB` ever weakened so that
-- `blk` announced nothing, this `refl` would go red and the run below would stop being
-- about announcement safety at all.
announce-refused : announceOK [] (header blk) ≡ false
announce-refused = refl

-- … and the gate is NOT constantly `false`: once the EB hash `true` has been forged the
-- very same header is licensed.  So what refuses the announcement is the MISSING FORGE
-- and nothing else.
announce-licensed : announceOK (true ∷ []) (header blk) ≡ true
announce-licensed = refl

------------------------------------------------------------------------
-- The four visible events of the run
------------------------------------------------------------------------

-- event 1: THE ILL-ANNOUNCED FORGE.  Its EB component is `nothing`, so it forges NO EB
-- and S0's forged set stays EMPTY; its RB component is `blk`, which announces the EB
-- hash `true`.  `acceptForgeL` would drop it; `acceptForgeLAnnBad` stores it.
evForge : Event√ (⊤ {0ℓ})
evForge = evl (evLabel (Maybe EB × Block) (env fzero lo envForge) (nothing , blk))

-- the prototype LeiosNotify RequestNext as it arrives off the wire at direction `hi`:
-- the only thing that moves the LeiosNotify PRODUCER peer out of `stIdle`, and hence
-- the only thing that makes it offer `lnpSendBlockAnnouncement` at all
reqMsg : Payload
reqMsg = tt , FromInitiator , tt , leiosNotifyP MsgLNPRequestNext

-- event 2: that request reaching node 0's LeiosNotify producer peer
evReq : Event√ (⊤ {0ℓ})
evReq = evl (evLabel Payload (output fzero hi N2N_LeiosNotify) reqMsg)

-- event 3: the announce thread taking the ill-announced block out of the broken store
-- by its read pointer (`stGetAt 0`), the honest `lnServerBodyL` read, untouched
evGetAt : Event√ (⊤ {0ℓ})
evGetAt = evl (evLabel Block (store fzero lo (stGetAt 0)) blk)

-- event 4: THE GATED EVENT — node 0 announces the header of a block whose announced EB
-- hash no `env … envForge` produced
evAnn : Event√ (⊤ {0ℓ})
evAnn = evl (evLabel Header (apiLP fzero hi lnpSendBlockAnnouncement) (header blk))

------------------------------------------------------------------------
-- The ten steps
--
-- Each is stated as "there is a state such that …", so the target of one step is
-- `proj₁` of it and the next step's source.  `env`/`store` are in `storeES` and OUTSIDE
-- `apiES`, so events 1 and 3 are `Par-soloR` past the peer bundle wrapping a `Par-sync`
-- of the thread group with the store group; `output` is in NEITHER set, so event 2 is a
-- `Par-soloL` into the bundle alone; `apiLP` IS in `apiES`, so event 4 is a genuine
-- rendezvous between the producer peer and `lnServerLoopL`.
------------------------------------------------------------------------

-- STEP 1.  THE ILL-ANNOUNCED FORGE: the forge thread (first of the node-level threads)
-- with the broken block store's forge arm (first of the five stores), which accepts
-- `blk` into `held` with no announcement check.
step₁ : Σ[ P₁ ∈ Proc ] (badNode ─[ ev evForge ]─► P₁)
step₁ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
      (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl))
    refl

-- STEP 2.  The block store's loop-back: having accepted the forge it returns the new
-- `Held` to `iter`, whose `sil` guard is one τ.  Without it the store is not back at its
-- menu and cannot offer the block on `stGetAt 0`.
step₂ : Σ[ P₂ ∈ Proc ] (proj₁ step₁ ─[ τ ]─► P₂)
step₂ = _ , Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _ (sSil refl)))

-- STEP 3.  The LeiosNotify request arrives.  `output` is in neither synchronisation
-- set, so the logic stays put and the bundle takes it alone; inside the bundle only the
-- producer peer at `hi` offers it, so it rides past the nine configured instances
-- before it (`leiosLCfg`: `(hi , N2N_LeiosNotify)` is the tenth entry).
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

-- STEP 4.  The producer peer's loop-back: having consumed the request it returns
-- `stBusy` to `iter`, whose `sil` guard is one τ.  Only in `stBusy` does it offer
-- `apiLP … lnpSendBlockAnnouncement`.
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

-- STEP 5.  The announce thread reads the ill-announced block, AND THIS IS A COLLISION:
-- `ebIndex`, `voter`, `lnServerLoopL` and `bodyOfferLoop` all offer `stGetAt 0` as plain
-- prefixes, and four threads offering one event outside the inner synchronisation set
-- means `par-pVis` neither refuses nor picks a side — it fires the event into an inline
-- internal choice, which steps 6-8 then resolve.
step₅ : Σ[ P₅ ∈ Proc ] (proj₁ step₄ ─[ ev evGetAt ]─► P₅)
step₅ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())                        -- past forgeL
        (Par-brBoth _ _ _ _ (λ ())                     -- ebIndex COLLIDES
          (sVis refl refl)
          (Par-brBoth _ _ _ _ (λ ())                   -- the voter COLLIDES
            (sVis refl refl)
            (Par-soloR _ _ _ _ (λ ())                  -- past submit
              (Par-soloR _ _ _ _ (λ ())                -- past certSink
                (Par-soloR _ _ _ _ (λ ())              -- past clientLoop
                  (Par-soloR _ _ _ _ (λ ())            -- past serverLoopL
                    (Par-soloR _ _ _ _ (λ ())          -- past lnClientLoopL
                      (Par-brBoth _ _ _ _ (λ ())       -- lnServerLoopL COLLIDES
                        (sVis refl refl)
                        (Par-soloL _ _ _ _ (λ ())      -- bodyOfferLoop, alone
                          (sVis refl refl) refl))
                      refl) refl) refl)
                refl) refl))) refl)
      (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl))
    refl

-- STEP 6.  Resolve the OUTERMOST collision to the RIGHT: `ebIndex` stands still.
step₆ : Σ[ P₆ ∈ Proc ] (proj₁ step₅ ─[ τ ]─► P₆)
step₆ = _ ,
  Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _
    (Par-τ-R _ _ _ _ (par-brNode-τR _ _ _ _ _ _)))

-- STEP 7.  Resolve the SECOND collision to the RIGHT: the voter stands still too.
step₇ : Σ[ P₇ ∈ Proc ] (proj₁ step₆ ─[ τ ]─► P₇)
step₇ = _ ,
  Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _
    (Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (par-brNode-τR _ _ _ _ _ _))))

-- STEP 8.  Resolve the THIRD collision to the LEFT: the ANNOUNCE thread advances, and
-- `bodyOfferLoop` and the five threads after it stand still.  It is `lnServerLoopL`
-- that now holds the ill-announced block.
step₈ : Σ[ P₈ ∈ Proc ] (proj₁ step₇ ─[ τ ]─► P₈)
step₈ = _ ,
  Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _
    (Par-τ-R _ _ _ _                                   -- past forgeL
    (Par-τ-R _ _ _ _                                   -- past ebIndex
    (Par-τ-R _ _ _ _                                   -- past voter
    (Par-τ-R _ _ _ _                                   -- past submit
    (Par-τ-R _ _ _ _                                   -- past certSink
    (Par-τ-R _ _ _ _                                   -- past clientLoop
    (Par-τ-R _ _ _ _                                   -- past serverLoopL
    (Par-τ-R _ _ _ _                                   -- past lnClientLoopL
      (par-brNode-τL _ _ _ _ _ _))))))))))

-- STEP 9.  The block store's second loop-back: having served the read pointer it
-- returns `held` to `iter`, one τ.
step₉ : Σ[ P₉ ∈ Proc ] (proj₁ step₈ ─[ τ ]─► P₉)
step₉ = _ , Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _ (sSil refl)))

-- STEP 10.  THE GATED EVENT FIRES.  `apiLP ∈ apiES`, so this is a genuine rendezvous
-- between the LeiosNotify PRODUCER peer (in `stBusy`, thanks to steps 3-4) and the
-- node's `lnServerLoopL` THREAD (holding the block, thanks to steps 5-8).
step₁₀ : Σ[ P₁₀ ∈ Proc ] (proj₁ step₉ ─[ ev evAnn ]─► P₁₀)
step₁₀ = _ ,
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
      (Par-soloR _ _ _ _ (λ ())                        -- past forgeL
      (Par-soloR _ _ _ _ (λ ())                        -- past ebIndex
      (Par-soloR _ _ _ _ (λ ())                        -- past voter
      (Par-soloR _ _ _ _ (λ ())                        -- past submit
      (Par-soloR _ _ _ _ (λ ())                        -- past certSink
      (Par-soloR _ _ _ _ (λ ())                        -- past clientLoop
      (Par-soloR _ _ _ _ (λ ())                        -- past serverLoopL
      (Par-soloR _ _ _ _ (λ ())                        -- past lnClientLoopL
      (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl) -- lnServerLoopL announces
        refl) refl) refl) refl) refl) refl) refl) refl)
      refl)

------------------------------------------------------------------------
-- THE REACHABILITY CONTROL
------------------------------------------------------------------------

-- THE ANNOUNCE GATE IS REACHABLE ONCE THE GUARD IS GONE.  Node 0 of the concrete Leios
-- line, its twelve prototype peers synchronised with the Linear-Leios logic whose RB
-- store has lost the forge route's announcement check, from EMPTY stores, has a trace
-- whose only forge carries NO EB and whose last event announces the EB hash `true`.
--
-- LEVEL 2 of the acceptance ladder: over `nodeP nA (nodeLogicLAnnBad nA st₀)`, at the
-- concrete `leiosLParams`/`leiosLP` line, at node 0 — NOT over `systemOfWithNode`.
-- SCOPE: this instance, this node, this one broken guard.
--
-- WHAT IT SHOWS: S0's gate is live machinery — the gated event can occur in this
-- composite when the guard is removed, so `annSafeLT` is not true merely because the
-- announcement is unreachable.  WHAT IT IS NOT: a refutation of `annSafeLT`, which is
-- about the UNBROKEN logic over the whole network.  WRITE-UP RULE: never state this
-- result and `annSafeLT`'s ∀-quantification in one sentence.
ann-gate-reachable : traces badNode (evForge ∷ evReq ∷ evGetAt ∷ evAnn ∷ [])
ann-gate-reachable =
  _ , ⟹-ev (proj₂ step₁)
        (⟹-τ (proj₂ step₂)
        (⟹-ev (proj₂ step₃)
        (⟹-τ (proj₂ step₄)
        (⟹-ev (proj₂ step₅)
        (⟹-τ (proj₂ step₆)
        (⟹-τ (proj₂ step₇)
        (⟹-τ (proj₂ step₈)
        (⟹-τ (proj₂ step₉)
        (⟹-ev (proj₂ step₁₀) ⟹-refl)))))))))
