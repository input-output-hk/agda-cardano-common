{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 Task D3 — node B/C/D visible api-event inversions
-- (`nodeB/C/D-ev-api`), the io-case node inversions, the top peel + L5.
--
-- These MIRROR the committed `nodeA-ev-api` (in `Praos.SysOracle`).  Kept in
-- THIS small module so `SysOracle` (8539 lines) stays cached and the edits
-- recompile only here.  `open import …SysOracle` brings every leaf lemma
-- (`bundle-{CS,BF}-ev-inv`, `apiLink-inj`, the driver ev-inversions/link
-- pinnings, `absBundleG-*-link-noIoOffer`, `noOffer→viewV`, the `ApiHasLink`/
-- `IsApiCSBF`/`BundleCSEvR`/`ConsDEvR`/`CPEvR` vocabulary, …) verbatim.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysRoute where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (⊤ to ⊤₀)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.Maybe.Properties using (just-injective)
open import Process_Trees using (PTree; ExtI; react; ret; react-injective)

-- links, api alphabet, block payloads
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD; Block₃; b1; produce )
open import CSP.Examples.Cardano_network.Net p using
  ( Net; Net-≟; Net_Api; Net_Api-≟; apiCS; apiBF; input; output; done; break; Link
  ; sndmsg; rcvmsg; tx; sndack; rcvack; ack; apiKA; apiTS; apiLN; apiLF
  -- the producer/consumer api tags (the role discriminator's index values)
  ; reqCSRequestNext; sendCSAwaitReply; sendCSRollForward
  ; sendCSRequestNext; recvCSRollforward; sendCSDone
  ; reqBFRange; sendBFStartBatch; sendBFBlock; sendBFBatchDone
  ; sendBFRequestRange; recvBFBlock; sendBFClientDone )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi; IDs
  ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission
  ; N2N_KeepAlive; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.NetworkPar p using
  ( ιCS; ιBF
  ; KAclientA; KAserverA; TSclientA; TSserverA
  ; LNclientA; LNserverA; LFclientA; LFserverA )
import CSP.Examples.Cardano_network.ChainSync  p as CS
import CSP.Examples.Cardano_network.BlockFetch p as BF
import CSP.Examples.Cardano_network.KeepAlive  p as KA
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.LeiosNotify p as LNp
import CSP.Examples.Cardano_network.LeiosFetch  p as LFp
import Semantics.LTS {E = KA.KAEv} {I = ExtI KA.KAEv} as KAL
import Semantics.LTS {E = TS.TSEv} {I = ExtI TS.TSEv} as TSL
import Semantics.LTS {E = LNp.LNEv} {I = ExtI LNp.LNEv} as LNL
import Semantics.LTS {E = LFp.LFEv} {I = ExtI LFp.LFEv} as LFL
open import Data.Bool using ( Bool; true; false )
open import Data.Nat using ( ℕ; zero; suc )
open import Data.Fin using ( Fin ) renaming ( zero to fzero; suc to fsuc )
open import Data.List using ( map )
open import Class.DecEq using ( _≟_ )
-- the breakable medium decode (for the medium api-non-offer leaf)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium
  using ( decMed; decLink; decCopy; MedState; mkMed; phase; broken; CopyPhase )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( numLinks; linkConfig )

-- Net_Api operators + the empty sync alphabet + the Par ev-elimination
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_; EventSet; ⦀Fin; Skip; _△_; △-merge; Prefix₀ )
open EventSet using ( mem )
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA
open Op using () renaming (∅ES to ∅ESa)
-- Net-level (pre-rename) operators: the copy fold `⦀⋆` for the medium leaf
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN
open OpN using ( ⦀⋆ )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; τ; evl; evLabel; sVis; ev-inv; Event√; √ )
-- the Hide visible-event inversion (for the `oev` √/io impossible-event refutations)
open import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload})
  using ( HideevR; Hide-ev-elim )
open HideevR using ( heV; he√ )

-- concrete node decodes + the generic bundle + the two drivers/phases
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( decNodeB; decNodeC; decNodeD; bundleG; decCP; decConsD
        ; consD; consuming; producing
        -- the two straight-chain drivers + their phase enumerations
        ; decProd; decCons; ProdPh; ConsPh
        ; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
        ; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        -- the renamed-peer sources (for the concrete bundle break-non-offer)
        ; decCSc-src; decCSs-src; decBFc-src; decBFs-src )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode as SN
-- the τ-free peer interpreter (`tableSpec`) + abstract positions/tables + the
-- inert KA/TS specs (for the ABSTRACT bundle break non-offer, `absBundleG` side)
import CSP.Examples.Cardano_network.NetworkVerification.Praos.NodeSpecs as NS

-- the Net_Api prefix (`⟶₀`) visible-step inversion (for the role discriminator)
import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload}) as PInv
open PInv using ( ⟶₀-ev-inv )
-- abstract node decodes + the abstract bundle + the io-offer predicate
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep
  using ( absNodeA; absNodeB; absNodeC; absNodeD; absBundleG; IoOffers )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep as SStep
-- the whole-system concrete decode + config record (for the top-level api peel)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
-- the shared io-hide alphabet (api events are disjoint from it)
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

-- every leaf lemma (bundle/driver ev-inversions, link-pinnings, non-offers, …)
-- + `NetProc` + the `ApiHasLink`/`IsApiCSBF`/`Bundle*EvR`/`ConsDEvR`/`CPEvR`
-- vocabulary, unqualified
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle

------------------------------------------------------------------------
-- ROLE DISCRIMINATOR (the node-value non-offer's engine).  On a SHARED link
-- (linkAB/AC/BD/CD) the producer node and the consumer node BOTH touch the same
-- (link, dir) but fire DISJOINT api tags: `produce`/`decProd` emits the SEVEN
-- server-role tags, `consume`/`decCons` the SIX client-role tags (Net.agda's
-- ApiCSTag/ApiBFTag are literally partitioned this way).  Hence for a FIXED api
-- event `e` at most one role offers it — the value-keyed disjointness the top
-- 4-node `⦀` `evBoth` refutation needs (link-disjointness alone fails on the
-- shared links).  These are textual mirrors of the committed `decX-apiCSBF`,
-- returning the role witness instead of `IsApiCSBF`.
------------------------------------------------------------------------

-- server/producer-role api events (exactly the tags `produce`/`decProd` fires)
data ApiIsProd : {X : Set 0ℓ} → Net_Api Payload X → Set₁ where
  aipCSreq   : ∀ {l d} → ApiIsProd (apiCS l d reqCSRequestNext)
  aipCSawait : ∀ {l d} → ApiIsProd (apiCS l d sendCSAwaitReply)
  aipCSroll  : ∀ {l d} → ApiIsProd (apiCS l d sendCSRollForward)
  aipBFreq   : ∀ {l d} → ApiIsProd (apiBF l d reqBFRange)
  aipBFstart : ∀ {l d} → ApiIsProd (apiBF l d sendBFStartBatch)
  aipBFblock : ∀ {l d} → ApiIsProd (apiBF l d sendBFBlock)
  aipBFdone  : ∀ {l d} → ApiIsProd (apiBF l d sendBFBatchDone)
  aipDone    : ∀ {l d ch} → ApiIsProd (done l d ch)   -- server-side done callback (produce receives it)

-- client/consumer-role api events (exactly the tags `consume`/`decCons` fires)
data ApiIsCons : {X : Set 0ℓ} → Net_Api Payload X → Set₁ where
  aicCSreq  : ∀ {l d} → ApiIsCons (apiCS l d sendCSRequestNext)
  aicCSroll : ∀ {l d} → ApiIsCons (apiCS l d recvCSRollforward)
  aicCSdone : ∀ {l d} → ApiIsCons (apiCS l d sendCSDone)
  aicBFreq  : ∀ {l d} → ApiIsCons (apiBF l d sendBFRequestRange)
  aicBFrecv : ∀ {l d} → ApiIsCons (apiBF l d recvBFBlock)
  aicBFdone : ∀ {l d} → ApiIsCons (apiBF l d sendBFClientDone)

-- producer and consumer roles are DISJOINT (distinct api tags per event)
prod≢cons : {X : Set 0ℓ} {e : Net_Api Payload X} → ApiIsProd e → ApiIsCons e → ⊥
prod≢cons aipCSreq   ()
prod≢cons aipCSawait ()
prod≢cons aipCSroll  ()
prod≢cons aipBFreq   ()
prod≢cons aipBFstart ()
prod≢cons aipBFblock ()
prod≢cons aipBFdone  ()
prod≢cons aipDone    ()

-- producer-driver role-pinning: every firing phase fires a server-role tag
decProd-ev-prod : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decProd l d blk pp ─[ ev (evl (evLabel X e a)) ]─► M → ApiIsProd e
decProd-ev-prod l d blk pp0 step with ⟶₀-ev-inv step
... | _ , refl , _ = aipCSreq
decProd-ev-prod l d blk pp1 step with ⟶₀-ev-inv step
... | _ , refl , _ = aipCSawait
decProd-ev-prod l d blk pp2 step with output-ev-lab step
... | refl = aipCSroll
decProd-ev-prod l d blk pp3 step with ⟶₀-ev-inv step
... | _ , refl , _ = aipBFreq
decProd-ev-prod l d blk pp4 step with output-ev-lab step
... | refl = aipBFstart
decProd-ev-prod l d blk pp5 step with output-ev-lab step
... | refl = aipBFblock
decProd-ev-prod l d blk pp6 step with output-ev-lab step
... | refl = aipBFdone
decProd-ev-prod l d blk pp7 step with ⟶₀-ev-inv step
... | _ , refl , _ = aipDone
decProd-ev-prod l d blk pp8 step with ⟶₀-ev-inv step
... | _ , refl , _ = aipDone
decProd-ev-prod l d blk pp9 step = ⊥-elim (ret-no-ev {P = decProd l d blk pp9} refl step)

-- consumer-driver role-pinning: every firing phase fires a client-role tag
decCons-ev-cons : (l : Link) (d : Dir) (b : Block₃) (cp : ConsPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → decCons l d b cp ─[ ev (evl (evLabel X e a)) ]─► M → ApiIsCons e
decCons-ev-cons l d b cp0 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicCSreq
decCons-ev-cons l d b cp1 step with prefix-ev-lab step
... | _ , refl = aicCSroll
decCons-ev-cons l d b cp2 step with output-ev-lab step
... | refl = aicBFreq
decCons-ev-cons l d b cp3 step with prefix-ev-lab step
... | _ , refl = aicBFrecv
decCons-ev-cons l d b cp4 step with output-ev-lab step
... | refl = aicBFdone
decCons-ev-cons l d b cp5 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicCSdone
decCons-ev-cons l d b cp6 step = ⊥-elim (ret-no-ev {P = decCons l d b cp6} refl step)

-- node-D consume-driver role-pinning (`decCons … >> Skip`): fire through the
-- bind, pin the inner consume event's client role
decConsD-ev-cons : (l : Link) (cph : SN.ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l cph ─[ ev (evl (evLabel X e a)) ]─► M → ApiIsCons e
decConsD-ev-cons l (consD b cp0) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp0) refl step
... | _ , sc , refl = decCons-ev-cons l hi b cp0 sc
decConsD-ev-cons l (consD b cp1) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp1) refl step
... | _ , sc , refl = decCons-ev-cons l hi b cp1 sc
decConsD-ev-cons l (consD b cp2) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp2) refl step
... | _ , sc , refl = decCons-ev-cons l hi b cp2 sc
decConsD-ev-cons l (consD b cp3) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp3) refl step
... | _ , sc , refl = decCons-ev-cons l hi b cp3 sc
decConsD-ev-cons l (consD b cp4) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp4) refl step
... | _ , sc , refl = decCons-ev-cons l hi b cp4 sc
decConsD-ev-cons l (consD b cp5) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp5) refl step
... | _ , sc , refl = decCons-ev-cons l hi b cp5 sc
decConsD-ev-cons l (consD b cp6) step = ⊥-elim (ret-no-ev {P = decConsD l (consD b cp6)} refl step)

-- relay-driver role-pinning (`consume l₁ hi >>= produce l₂ hi`): consuming fires
-- a client tag; the cp6 handoff + producing leg fire a server tag
decCP-ev-role : (l₁ l₂ : Link) (ph : SN.CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ ph ─[ ev (evl (evLabel X e a)) ]─► M → ApiIsCons e ⊎ ApiIsProd e
decCP-ev-role l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl = inj₁ (decCons-ev-cons l₁ hi b cp0 sc)
decCP-ev-role l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl = inj₁ (decCons-ev-cons l₁ hi b cp1 sc)
decCP-ev-role l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl = inj₁ (decCons-ev-cons l₁ hi b cp2 sc)
decCP-ev-role l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl = inj₁ (decCons-ev-cons l₁ hi b cp3 sc)
decCP-ev-role l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl = inj₁ (decCons-ev-cons l₁ hi b cp4 sc)
decCP-ev-role l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl = inj₁ (decCons-ev-cons l₁ hi b cp5 sc)
decCP-ev-role l₁ l₂ (consuming b cp6) step = inj₂ (decProd-ev-prod l₂ hi b pp0 (step-fcong refl step))
decCP-ev-role l₁ l₂ (producing b pp) step = inj₂ (decProd-ev-prod l₂ hi b pp step)

-- a relay driver `decCP l₁ l₂` fires `done` ONLY via the produce leg (link l₂):
-- it pins the event's link to l₂ AND its dir to hi, and identifies its protocol as
-- ChainSync (pp7) or BlockFetch (pp8).  The consume phases fire consumer-role events
-- (`decCons-ev-cons` ⇒ `ApiIsCons`, which has no `done` constructor ⇒ absurd).
decCP-done-inv : (l₁ l₂ : Link) (ph : SN.CPPh)
    {a : ⊤₀} {l′ : Link} {d′ : Dir} {ch : IDs} {M : NetProc}
  → decCP l₁ l₂ ph ─[ ev (evl (evLabel ⊤₀ (done l′ d′ ch) a)) ]─► M
  → ApiHasLink l₂ (done l′ d′ ch) × (d′ ≡ hi) × ((ch ≡ N2N_ChainSync) ⊎ (ch ≡ N2N_BlockFetch))
decCP-done-inv l₁ l₂ (consuming b cp0) step with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl with decCons-ev-cons l₁ hi b cp0 sc
... | ()
decCP-done-inv l₁ l₂ (consuming b cp1) step with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl with decCons-ev-cons l₁ hi b cp1 sc
... | ()
decCP-done-inv l₁ l₂ (consuming b cp2) step with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl with decCons-ev-cons l₁ hi b cp2 sc
... | ()
decCP-done-inv l₁ l₂ (consuming b cp3) step with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl with decCons-ev-cons l₁ hi b cp3 sc
... | ()
decCP-done-inv l₁ l₂ (consuming b cp4) step with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl with decCons-ev-cons l₁ hi b cp4 sc
... | ()
decCP-done-inv l₁ l₂ (consuming b cp5) step with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl with decCons-ev-cons l₁ hi b cp5 sc
... | ()
decCP-done-inv l₁ l₂ (consuming b cp6) step with decProd-ev-link l₂ hi b pp0 (step-fcong refl step)
... | ahlDone with decProd-done-inv l₂ hi b pp0 (step-fcong refl step)
...   | refl , inj₁ (refl , _) = ahlDone , refl , inj₁ refl
...   | refl , inj₂ (refl , _) = ahlDone , refl , inj₂ refl
decCP-done-inv l₁ l₂ (producing b pp) step with decProd-ev-link l₂ hi b pp step
... | ahlDone with decProd-done-inv l₂ hi b pp step
...   | refl , inj₁ (refl , _) = ahlDone , refl , inj₁ refl
...   | refl , inj₂ (refl , _) = ahlDone , refl , inj₂ refl

------------------------------------------------------------------------
-- NODE D — pure consumer on links BD, CD (two drivers `decConsD`), a VERBATIM
-- mirror of `nodeA-ev-api`: swap `bundleA l`→`bundleG l hi lo`,
-- `decProd l hi b1`→`decConsD l`, links AB/AC→BD/CD, `peR`→`cdR`, and thread
-- the received block via the `ConsDPh` `consD b′ cp′`.
------------------------------------------------------------------------

-- node-D visible-event result: the successor node-state + concrete/abstract match
data NodeDEvR (na : SN.NodeStateD) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (A′ : NetProc) : Set₁ where
  ndEv : (na′ : SN.NodeStateD) → A′ ≡ decNodeD na′
       → absNodeD na ─[ ev (evl (evLabel X e a)) ]─► absNodeD na′
       → NodeDEvR na e a A′

-- distinct node-D links
linkBD≢linkCD : ¬ (linkBD ≡ linkCD)
linkBD≢linkCD ()

-- driver on linkCD offers nothing on a linkBD-pinned api event
nodeD-drvCD-no : (na : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ApiHasLink linkBD e → ¬ IoOffers (decConsD linkCD (SN.NodeStateD.cons-CD na)) e a
nodeD-drvCD-no na ahl (_ , s) =
  linkBD≢linkCD (sym (apiLink-inj (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD na) s) ahl))

-- driver on linkBD offers nothing on a linkCD-pinned api event
nodeD-drvBD-no : (na : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ApiHasLink linkCD e → ¬ IoOffers (decConsD linkBD (SN.NodeStateD.cons-BD na)) e a
nodeD-drvBD-no na ahl (_ , s) =
  linkBD≢linkCD (apiLink-inj (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD na) s) ahl)

-- firing link = linkBD (mirror of nodeA-AB)
nodeD-BD : (na : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {B₁ D₁BD : NetProc}
  → apiES .mem (X , e) a
  → (bundleG linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na)
     ⦀ bundleG linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → decConsD linkBD (SN.NodeStateD.cons-BD na) ─[ ev (evl (evLabel X e a)) ]─► D₁BD
  → IsApiCSBF e → ApiHasLink linkBD e
  → NodeDEvR na e a (B₁ ∥⇘ apiES ⇙ (D₁BD ⦀ decConsD linkCD (SN.NodeStateD.cons-CD na)))
nodeD-BD na {X} {a = a} mem bStep sDBD aicCS (ahlCS {d} {m})
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na))
         (bundleG linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBBD sBCD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (bundleCS-ev-link linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na) {e₁ = CS.apiCSev linkBD d m} sBBD)
                     (bundleCS-ev-link linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na) {e₁ = CS.apiCSev linkBD d m} sBCD)))
... | PEA.evR _ sBCD = ⊥-elim (linkBD≢linkCD (sym
        (apiLink-inj (bundleCS-ev-link linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na) {e₁ = CS.apiCSev linkBD d m} sBCD) ahlCS)))
... | PEA.evL _ sBBD
    with bundle-CS-ev-inv linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na) {e₁ = CS.apiCSev linkBD d m} sBBD
       | decConsD-ev-inv linkBD (SN.NodeStateD.cons-BD na) sDBD
...   | bcscE csc′ refl aStepBD | cdR b′ cp′ refl =
        ndEv (SN.mkNodeD csc′ (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (consD b′ cp′) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.cons-CD na) (SN.NodeStateD.inert-BD na) (SN.NodeStateD.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na)) _
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na) (CS.apiCSev linkBD d m) linkBD≢linkCD)))
            (SStep.⦀-ev-L (decConsD linkBD (SN.NodeStateD.cons-BD na)) _ sDBD
               (noOffer→viewV _ (nodeD-drvCD-no na ahlCS))))
...   | bcssE css′ refl aStepBD | cdR b′ cp′ refl =
        ndEv (SN.mkNodeD (SN.NodeStateD.csC-BD na) css′ (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (consD b′ cp′) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.cons-CD na) (SN.NodeStateD.inert-BD na) (SN.NodeStateD.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na)) _
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na) (CS.apiCSev linkBD d m) linkBD≢linkCD)))
            (SStep.⦀-ev-L (decConsD linkBD (SN.NodeStateD.cons-BD na)) _ sDBD
               (noOffer→viewV _ (nodeD-drvCD-no na ahlCS))))
nodeD-BD na {X} {a = a} mem bStep sDBD aicBF (ahlBF {d} {m})
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na))
         (bundleG linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBBD sBCD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (bundleBF-ev-link linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na) {e₁ = BF.apiBFev linkBD d m} sBBD)
                     (bundleBF-ev-link linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na) {e₁ = BF.apiBFev linkBD d m} sBCD)))
... | PEA.evR _ sBCD = ⊥-elim (linkBD≢linkCD (sym
        (apiLink-inj (bundleBF-ev-link linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na) {e₁ = BF.apiBFev linkBD d m} sBCD) ahlBF)))
... | PEA.evL _ sBBD
    with bundle-BF-ev-inv linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na) {e₁ = BF.apiBFev linkBD d m} sBBD
       | decConsD-ev-inv linkBD (SN.NodeStateD.cons-BD na) sDBD
...   | bcbcE bfc′ refl aStepBD | cdR b′ cp′ refl =
        ndEv (SN.mkNodeD (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) bfc′ (SN.NodeStateD.bfS-BD na) (consD b′ cp′) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.cons-CD na) (SN.NodeStateD.inert-BD na) (SN.NodeStateD.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na)) _
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na) (BF.apiBFev linkBD d m) linkBD≢linkCD)))
            (SStep.⦀-ev-L (decConsD linkBD (SN.NodeStateD.cons-BD na)) _ sDBD
               (noOffer→viewV _ (nodeD-drvCD-no na ahlBF))))
...   | bcbsE bfs′ refl aStepBD | cdR b′ cp′ refl =
        ndEv (SN.mkNodeD (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) bfs′ (consD b′ cp′) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.cons-CD na) (SN.NodeStateD.inert-BD na) (SN.NodeStateD.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na)) _
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na) (BF.apiBFev linkBD d m) linkBD≢linkCD)))
            (SStep.⦀-ev-L (decConsD linkBD (SN.NodeStateD.cons-BD na)) _ sDBD
               (noOffer→viewV _ (nodeD-drvCD-no na ahlBF))))
-- `done`: node D is a pure consumer — its `consume` driver never offers `done`
-- (`decConsD-ev-cons` gives `ApiIsCons (done …)`, uninhabited), so this is vacuous
nodeD-BD na {X} {a = a} mem bStep sDBD aicDone (ahlDone {d} {ch})
  with decConsD-ev-cons linkBD (SN.NodeStateD.cons-BD na) sDBD
... | ()

-- firing link = linkCD (mirror of nodeA-AC via `⦀-ev-R`)
nodeD-CD : (na : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {B₁ D₁CD : NetProc}
  → apiES .mem (X , e) a
  → (bundleG linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na)
     ⦀ bundleG linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → decConsD linkCD (SN.NodeStateD.cons-CD na) ─[ ev (evl (evLabel X e a)) ]─► D₁CD
  → IsApiCSBF e → ApiHasLink linkCD e
  → NodeDEvR na e a (B₁ ∥⇘ apiES ⇙ (decConsD linkBD (SN.NodeStateD.cons-BD na) ⦀ D₁CD))
nodeD-CD na {X} {a = a} mem bStep sDCD aicCS (ahlCS {d} {m})
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na))
         (bundleG linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBBD sBCD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (bundleCS-ev-link linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na) {e₁ = CS.apiCSev linkCD d m} sBBD)
                     (bundleCS-ev-link linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na) {e₁ = CS.apiCSev linkCD d m} sBCD)))
... | PEA.evL _ sBBD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (bundleCS-ev-link linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na) {e₁ = CS.apiCSev linkCD d m} sBBD) ahlCS))
... | PEA.evR _ sBCD
    with bundle-CS-ev-inv linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na) {e₁ = CS.apiCSev linkCD d m} sBCD
       | decConsD-ev-inv linkCD (SN.NodeStateD.cons-CD na) sDCD
...   | bcscE csc′ refl aStepCD | cdR b′ cp′ refl =
        ndEv (SN.mkNodeD (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.cons-BD na) csc′ (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (consD b′ cp′) (SN.NodeStateD.inert-BD na) (SN.NodeStateD.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na))
               aStepCD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na) (CS.apiCSev linkCD d m) (λ q → linkBD≢linkCD (sym q)))))
            (SStep.⦀-ev-R _ (decConsD linkCD (SN.NodeStateD.cons-CD na)) sDCD
               (noOffer→viewV _ (nodeD-drvBD-no na ahlCS))))
...   | bcssE css′ refl aStepCD | cdR b′ cp′ refl =
        ndEv (SN.mkNodeD (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.cons-BD na) (SN.NodeStateD.csC-CD na) css′ (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (consD b′ cp′) (SN.NodeStateD.inert-BD na) (SN.NodeStateD.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na))
               aStepCD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na) (CS.apiCSev linkCD d m) (λ q → linkBD≢linkCD (sym q)))))
            (SStep.⦀-ev-R _ (decConsD linkCD (SN.NodeStateD.cons-CD na)) sDCD
               (noOffer→viewV _ (nodeD-drvBD-no na ahlCS))))
nodeD-CD na {X} {a = a} mem bStep sDCD aicBF (ahlBF {d} {m})
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na))
         (bundleG linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBBD sBCD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (bundleBF-ev-link linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na) {e₁ = BF.apiBFev linkCD d m} sBBD)
                     (bundleBF-ev-link linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na) {e₁ = BF.apiBFev linkCD d m} sBCD)))
... | PEA.evL _ sBBD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (bundleBF-ev-link linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na) {e₁ = BF.apiBFev linkCD d m} sBBD) ahlBF))
... | PEA.evR _ sBCD
    with bundle-BF-ev-inv linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na) {e₁ = BF.apiBFev linkCD d m} sBCD
       | decConsD-ev-inv linkCD (SN.NodeStateD.cons-CD na) sDCD
...   | bcbcE bfc′ refl aStepCD | cdR b′ cp′ refl =
        ndEv (SN.mkNodeD (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.cons-BD na) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) bfc′ (SN.NodeStateD.bfS-CD na) (consD b′ cp′) (SN.NodeStateD.inert-BD na) (SN.NodeStateD.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na))
               aStepCD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na) (BF.apiBFev linkCD d m) (λ q → linkBD≢linkCD (sym q)))))
            (SStep.⦀-ev-R _ (decConsD linkCD (SN.NodeStateD.cons-CD na)) sDCD
               (noOffer→viewV _ (nodeD-drvBD-no na ahlBF))))
...   | bcbsE bfs′ refl aStepCD | cdR b′ cp′ refl =
        ndEv (SN.mkNodeD (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.cons-BD na) (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) bfs′ (consD b′ cp′) (SN.NodeStateD.inert-BD na) (SN.NodeStateD.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na))
               aStepCD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na) (BF.apiBFev linkCD d m) (λ q → linkBD≢linkCD (sym q)))))
            (SStep.⦀-ev-R _ (decConsD linkCD (SN.NodeStateD.cons-CD na)) sDCD
               (noOffer→viewV _ (nodeD-drvBD-no na ahlBF))))
-- `done`: node D consumer — `consume` never offers `done` (vacuous)
nodeD-CD na {X} {a = a} mem bStep sDCD aicDone (ahlDone {d} {ch})
  with decConsD-ev-cons linkCD (SN.NodeStateD.cons-CD na) sDCD
... | ()

-- node-D api inversion: reflect the driver↔peer sync, peel the driver `⦀`, dispatch
nodeD-ev-api : (na : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a
  → decNodeD na ─[ ev (evl (evLabel X e a)) ]─► A′
  → NodeDEvR na e a A′
nodeD-ev-api na {X} {e} {a} mem step
  with SStep.reflect-node-api
         (bundleG linkBD hi lo (SN.NodeStateD.csC-BD na) (SN.NodeStateD.csS-BD na) (SN.NodeStateD.bfC-BD na) (SN.NodeStateD.bfS-BD na) (SN.NodeStateD.inert-BD na)
          ⦀ bundleG linkCD hi lo (SN.NodeStateD.csC-CD na) (SN.NodeStateD.csS-CD na) (SN.NodeStateD.bfC-CD na) (SN.NodeStateD.bfS-CD na) (SN.NodeStateD.inert-CD na))
         (decConsD linkBD (SN.NodeStateD.cons-BD na) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD na))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (decConsD linkBD (SN.NodeStateD.cons-BD na)) (decConsD linkCD (SN.NodeStateD.cons-CD na)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sDBD =
        nodeD-BD na mem bStep sDBD
          (decConsD-apiCSBF linkBD (SN.NodeStateD.cons-BD na) sDBD)
          (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD na) sDBD)
... | PEA.evR _ sDCD =
        nodeD-CD na mem bStep sDCD
          (decConsD-apiCSBF linkCD (SN.NodeStateD.cons-CD na) sDCD)
          (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD na) sDCD)
... | PEA.evBoth _ sDBD sDCD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD na) sDBD)
                     (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD na) sDCD)))

------------------------------------------------------------------------
-- NODE B — relay (consume AB, produce BD) with the SINGLE `decCP` driver.  No
-- driver `⦀` peel: `reflect-node-api` gives one driver step; `decCP-ev-link`'s
-- `⊎` picks the firing link (AB=consume/left, BD=produce/right); `decCP-ev-inv`
-- gives the successor phase (`consuming`/`producing`).  The bundle two-link `⦀`
-- is aligned to that link and inverted by `bundle-{CS,BF}-ev-inv`.
------------------------------------------------------------------------

-- node-B visible-event result
data NodeBEvR (na : SN.NodeStateB) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (A′ : NetProc) : Set₁ where
  nbEv : (na′ : SN.NodeStateB) → A′ ≡ decNodeB na′
       → absNodeB na ─[ ev (evl (evLabel X e a)) ]─► absNodeB na′
       → NodeBEvR na e a A′

-- distinct node-B links
linkAB≢linkBD : ¬ (linkAB ≡ linkBD)
linkAB≢linkBD ()

-- firing link = linkAB (consume leg, LEFT bundle); driver is the WHOLE `decCP`,
-- the successor phase read off the `CPEvR`
nodeB-fireAB : (na : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (bundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na)
     ⦀ bundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → decCP linkAB linkBD (SN.NodeStateB.cp-B na) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → IsApiCSBF e → ApiHasLink linkAB e
  → CPEvR linkAB linkBD (SN.NodeStateB.cp-B na) D₁
  → NodeBEvR na e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeB-fireAB na {X} {a = a} mem bStep dStep aicCS (ahlCS {d} {m}) cpr
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na))
         (bundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAB≢linkBD
        (apiLink-inj (bundleCS-ev-link linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) {e₁ = CS.apiCSev linkAB d m} sBAB)
                     (bundleCS-ev-link linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) {e₁ = CS.apiCSev linkAB d m} sBBD)))
... | PEA.evR _ sBBD = ⊥-elim (linkAB≢linkBD (sym
        (apiLink-inj (bundleCS-ev-link linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) {e₁ = CS.apiCSev linkAB d m} sBBD) ahlCS)))
... | PEA.evL _ sBAB
    with bundle-CS-ev-inv linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) {e₁ = CS.apiCSev linkAB d m} sBAB
       | cpr
...   | bcscE csc′ refl aStepAB | cpR-cons b′ cp′ refl =
        nbEv (SN.mkNodeB csc′ (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (consuming b′ cp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) (CS.apiCSev linkAB d m) linkAB≢linkBD)))
            dStep)
...   | bcscE csc′ refl aStepAB | cpR-prod b′ pp′ refl =
        nbEv (SN.mkNodeB csc′ (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (producing b′ pp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) (CS.apiCSev linkAB d m) linkAB≢linkBD)))
            dStep)
...   | bcssE css′ refl aStepAB | cpR-cons b′ cp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) css′ (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (consuming b′ cp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) (CS.apiCSev linkAB d m) linkAB≢linkBD)))
            dStep)
...   | bcssE css′ refl aStepAB | cpR-prod b′ pp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) css′ (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (producing b′ pp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) (CS.apiCSev linkAB d m) linkAB≢linkBD)))
            dStep)
nodeB-fireAB na {X} {a = a} mem bStep dStep aicBF (ahlBF {d} {m}) cpr
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na))
         (bundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAB≢linkBD
        (apiLink-inj (bundleBF-ev-link linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) {e₁ = BF.apiBFev linkAB d m} sBAB)
                     (bundleBF-ev-link linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) {e₁ = BF.apiBFev linkAB d m} sBBD)))
... | PEA.evR _ sBBD = ⊥-elim (linkAB≢linkBD (sym
        (apiLink-inj (bundleBF-ev-link linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) {e₁ = BF.apiBFev linkAB d m} sBBD) ahlBF)))
... | PEA.evL _ sBAB
    with bundle-BF-ev-inv linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) {e₁ = BF.apiBFev linkAB d m} sBAB
       | cpr
...   | bcbcE bfc′ refl aStepAB | cpR-cons b′ cp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) bfc′ (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (consuming b′ cp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) (BF.apiBFev linkAB d m) linkAB≢linkBD)))
            dStep)
...   | bcbcE bfc′ refl aStepAB | cpR-prod b′ pp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) bfc′ (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (producing b′ pp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) (BF.apiBFev linkAB d m) linkAB≢linkBD)))
            dStep)
...   | bcbsE bfs′ refl aStepAB | cpR-cons b′ cp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) bfs′ (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (consuming b′ cp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) (BF.apiBFev linkAB d m) linkAB≢linkBD)))
            dStep)
...   | bcbsE bfs′ refl aStepAB | cpR-prod b′ pp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) bfs′ (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (producing b′ pp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) (BF.apiBFev linkAB d m) linkAB≢linkBD)))
            dStep)
-- `done` on the consume leg (link AB) is impossible: `decCP` fires `done` only via
-- the produce leg (link BD), so the driver-pinned link contradicts `ahlDone`'s link AB
nodeB-fireAB na {X} {a = a} mem bStep dStep aicDone (ahlDone {d} {ch}) cpr =
  ⊥-elim (linkAB≢linkBD (apiLink-inj ahlDone (proj₁ (decCP-done-inv linkAB linkBD (SN.NodeStateB.cp-B na) dStep))))

-- firing link = linkBD (produce leg, RIGHT bundle)
nodeB-fireBD : (na : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (bundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na)
     ⦀ bundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → decCP linkAB linkBD (SN.NodeStateB.cp-B na) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → IsApiCSBF e → ApiHasLink linkBD e
  → CPEvR linkAB linkBD (SN.NodeStateB.cp-B na) D₁
  → NodeBEvR na e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeB-fireBD na {X} {a = a} mem bStep dStep aicCS (ahlCS {d} {m}) cpr
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na))
         (bundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAB≢linkBD
        (apiLink-inj (bundleCS-ev-link linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) {e₁ = CS.apiCSev linkBD d m} sBAB)
                     (bundleCS-ev-link linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) {e₁ = CS.apiCSev linkBD d m} sBBD)))
... | PEA.evL _ sBAB = ⊥-elim (linkAB≢linkBD
        (apiLink-inj (bundleCS-ev-link linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) {e₁ = CS.apiCSev linkBD d m} sBAB) ahlCS))
... | PEA.evR _ sBBD
    with bundle-CS-ev-inv linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) {e₁ = CS.apiCSev linkBD d m} sBBD
       | cpr
...   | bcscE csc′ refl aStepBD | cpR-cons b′ cp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) csc′ (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (consuming b′ cp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (CS.apiCSev linkBD d m) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
...   | bcscE csc′ refl aStepBD | cpR-prod b′ pp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) csc′ (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (producing b′ pp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (CS.apiCSev linkBD d m) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
...   | bcssE css′ refl aStepBD | cpR-cons b′ cp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) css′ (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (consuming b′ cp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (CS.apiCSev linkBD d m) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
...   | bcssE css′ refl aStepBD | cpR-prod b′ pp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) css′ (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (producing b′ pp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (CS.apiCSev linkBD d m) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
nodeB-fireBD na {X} {a = a} mem bStep dStep aicBF (ahlBF {d} {m}) cpr
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na))
         (bundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAB≢linkBD
        (apiLink-inj (bundleBF-ev-link linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) {e₁ = BF.apiBFev linkBD d m} sBAB)
                     (bundleBF-ev-link linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) {e₁ = BF.apiBFev linkBD d m} sBBD)))
... | PEA.evL _ sBAB = ⊥-elim (linkAB≢linkBD
        (apiLink-inj (bundleBF-ev-link linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) {e₁ = BF.apiBFev linkBD d m} sBAB) ahlBF))
... | PEA.evR _ sBBD
    with bundle-BF-ev-inv linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) {e₁ = BF.apiBFev linkBD d m} sBBD
       | cpr
...   | bcbcE bfc′ refl aStepBD | cpR-cons b′ cp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) bfc′ (SN.NodeStateB.bfS-BD na) (consuming b′ cp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (BF.apiBFev linkBD d m) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
...   | bcbcE bfc′ refl aStepBD | cpR-prod b′ pp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) bfc′ (SN.NodeStateB.bfS-BD na) (producing b′ pp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (BF.apiBFev linkBD d m) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
...   | bcbsE bfs′ refl aStepBD | cpR-cons b′ cp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) bfs′ (consuming b′ cp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (BF.apiBFev linkBD d m) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
...   | bcbsE bfs′ refl aStepBD | cpR-prod b′ pp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) bfs′ (producing b′ pp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (BF.apiBFev linkBD d m) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
-- `done` on the produce leg (link BD): CS/BF SERVER fires done, synced with the
-- produce driver's done-receipt (`decCP-done-inv` pins dir=hi, proto CS pp7 / BF pp8)
nodeB-fireBD na {X} {a = a} mem bStep dStep aicDone (ahlDone {d} {ch}) cpr
  with decCP-done-inv linkAB linkBD (SN.NodeStateB.cp-B na) dStep
nodeB-fireBD na {X} {a = a} mem bStep dStep aicDone (ahlDone {d} {ch}) cpr | _ , refl , inj₁ refl
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na))
         (bundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAB≢linkBD
        (apiLink-inj (bundleCS-ev-link linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) {e₁ = CS.doneCS linkBD hi} sBAB)
                     (bundleCS-ev-link linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) {e₁ = CS.doneCS linkBD hi} sBBD)))
... | PEA.evL _ sBAB = ⊥-elim (linkAB≢linkBD
        (apiLink-inj (bundleCS-ev-link linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) {e₁ = CS.doneCS linkBD hi} sBAB) (ahlDone {d = hi} {ch = N2N_ChainSync})))
... | PEA.evR _ sBBD
    with bundle-CS-ev-inv linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) {e₁ = CS.doneCS linkBD hi} sBBD
       | cpr
...   | bcscE csc′ refl aStepBD | cpR-cons b′ cp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) csc′ (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (consuming b′ cp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (CS.doneCS linkBD hi) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
...   | bcscE csc′ refl aStepBD | cpR-prod b′ pp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) csc′ (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (producing b′ pp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (CS.doneCS linkBD hi) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
...   | bcssE css′ refl aStepBD | cpR-cons b′ cp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) css′ (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (consuming b′ cp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (CS.doneCS linkBD hi) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
...   | bcssE css′ refl aStepBD | cpR-prod b′ pp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) css′ (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (producing b′ pp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (CS.doneCS linkBD hi) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
-- `done` on the produce leg (link BD, BlockFetch): BF SERVER fires doneBF, synced with produce pp8
nodeB-fireBD na {X} {a = a} mem bStep dStep aicDone (ahlDone {d} {ch}) cpr | _ , refl , inj₂ refl
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na))
         (bundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAB≢linkBD
        (apiLink-inj (bundleBF-ev-link linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) {e₁ = BF.doneBF linkBD hi} sBAB)
                     (bundleBF-ev-link linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) {e₁ = BF.doneBF linkBD hi} sBBD)))
... | PEA.evL _ sBAB = ⊥-elim (linkAB≢linkBD
        (apiLink-inj (bundleBF-ev-link linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) {e₁ = BF.doneBF linkBD hi} sBAB) (ahlDone {d = hi} {ch = N2N_BlockFetch})))
... | PEA.evR _ sBBD
    with bundle-BF-ev-inv linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na) {e₁ = BF.doneBF linkBD hi} sBBD
       | cpr
...   | bcbcE bfc′ refl aStepBD | cpR-cons b′ cp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) bfc′ (SN.NodeStateB.bfS-BD na) (consuming b′ cp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (BF.doneBF linkBD hi) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
...   | bcbcE bfc′ refl aStepBD | cpR-prod b′ pp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) bfc′ (SN.NodeStateB.bfS-BD na) (producing b′ pp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (BF.doneBF linkBD hi) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
...   | bcbsE bfs′ refl aStepBD | cpR-cons b′ cp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) bfs′ (consuming b′ cp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (BF.doneBF linkBD hi) (λ q → linkAB≢linkBD (sym q)))))
            dStep)
...   | bcbsE bfs′ refl aStepBD | cpR-prod b′ pp′ refl =
        nbEv (SN.mkNodeB (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) bfs′ (producing b′ pp′) (SN.NodeStateB.inert-AB na) (SN.NodeStateB.inert-BD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na) (BF.doneBF linkBD hi) (λ q → linkAB≢linkBD (sym q)))))
            dStep)

-- node-B api inversion: reflect the sync, pick the link via `decCP-ev-link`'s ⊎
nodeB-ev-api : (na : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a
  → decNodeB na ─[ ev (evl (evLabel X e a)) ]─► A′
  → NodeBEvR na e a A′
nodeB-ev-api na {X} {e} {a} mem step
  with SStep.reflect-node-api
         (bundleG linkAB hi lo (SN.NodeStateB.csC-AB na) (SN.NodeStateB.csS-AB na) (SN.NodeStateB.bfC-AB na) (SN.NodeStateB.bfS-AB na) (SN.NodeStateB.inert-AB na)
          ⦀ bundleG linkBD lo hi (SN.NodeStateB.csC-BD na) (SN.NodeStateB.csS-BD na) (SN.NodeStateB.bfC-BD na) (SN.NodeStateB.bfS-BD na) (SN.NodeStateB.inert-BD na))
         (decCP linkAB linkBD (SN.NodeStateB.cp-B na))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with decCP-ev-link linkAB linkBD (SN.NodeStateB.cp-B na) dStep
... | inj₁ ahl = nodeB-fireAB na mem bStep dStep (decCP-apiCSBF linkAB linkBD (SN.NodeStateB.cp-B na) dStep) ahl (decCP-ev-inv linkAB linkBD (SN.NodeStateB.cp-B na) dStep)
... | inj₂ ahl = nodeB-fireBD na mem bStep dStep (decCP-apiCSBF linkAB linkBD (SN.NodeStateB.cp-B na) dStep) ahl (decCP-ev-inv linkAB linkBD (SN.NodeStateB.cp-B na) dStep)

------------------------------------------------------------------------
-- NODE C — relay (consume AC, produce CD) with the SINGLE `decCP` driver.  No
-- driver `⦀` peel: `reflect-node-api` gives one driver step; `decCP-ev-link`'s
-- `⊎` picks the firing link (AB=consume/left, BD=produce/right); `decCP-ev-inv`
-- gives the successor phase (`consuming`/`producing`).  The bundle two-link `⦀`
-- is aligned to that link and inverted by `bundle-{CS,BF}-ev-inv`.
------------------------------------------------------------------------

-- node-B visible-event result
data NodeCEvR (na : SN.NodeStateC) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (A′ : NetProc) : Set₁ where
  ncEv : (na′ : SN.NodeStateC) → A′ ≡ decNodeC na′
       → absNodeC na ─[ ev (evl (evLabel X e a)) ]─► absNodeC na′
       → NodeCEvR na e a A′

-- distinct node-B links
linkAC≢linkCD : ¬ (linkAC ≡ linkCD)
linkAC≢linkCD ()

-- firing link = linkAC (consume leg, LEFT bundle); driver is the WHOLE `decCP`,
-- the successor phase read off the `CPEvR`
nodeC-fireAB : (na : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (bundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na)
     ⦀ bundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → decCP linkAC linkCD (SN.NodeStateC.cp-C na) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → IsApiCSBF e → ApiHasLink linkAC e
  → CPEvR linkAC linkCD (SN.NodeStateC.cp-C na) D₁
  → NodeCEvR na e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeC-fireAB na {X} {a = a} mem bStep dStep aicCS (ahlCS {d} {m}) cpr
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na))
         (bundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAC≢linkCD
        (apiLink-inj (bundleCS-ev-link linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) {e₁ = CS.apiCSev linkAC d m} sBAB)
                     (bundleCS-ev-link linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) {e₁ = CS.apiCSev linkAC d m} sBBD)))
... | PEA.evR _ sBBD = ⊥-elim (linkAC≢linkCD (sym
        (apiLink-inj (bundleCS-ev-link linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) {e₁ = CS.apiCSev linkAC d m} sBBD) ahlCS)))
... | PEA.evL _ sBAB
    with bundle-CS-ev-inv linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) {e₁ = CS.apiCSev linkAC d m} sBAB
       | cpr
...   | bcscE csc′ refl aStepAB | cpR-cons b′ cp′ refl =
        ncEv (SN.mkNodeC csc′ (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (consuming b′ cp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) (CS.apiCSev linkAC d m) linkAC≢linkCD)))
            dStep)
...   | bcscE csc′ refl aStepAB | cpR-prod b′ pp′ refl =
        ncEv (SN.mkNodeC csc′ (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (producing b′ pp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) (CS.apiCSev linkAC d m) linkAC≢linkCD)))
            dStep)
...   | bcssE css′ refl aStepAB | cpR-cons b′ cp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) css′ (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (consuming b′ cp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) (CS.apiCSev linkAC d m) linkAC≢linkCD)))
            dStep)
...   | bcssE css′ refl aStepAB | cpR-prod b′ pp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) css′ (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (producing b′ pp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) (CS.apiCSev linkAC d m) linkAC≢linkCD)))
            dStep)
nodeC-fireAB na {X} {a = a} mem bStep dStep aicBF (ahlBF {d} {m}) cpr
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na))
         (bundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAC≢linkCD
        (apiLink-inj (bundleBF-ev-link linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) {e₁ = BF.apiBFev linkAC d m} sBAB)
                     (bundleBF-ev-link linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) {e₁ = BF.apiBFev linkAC d m} sBBD)))
... | PEA.evR _ sBBD = ⊥-elim (linkAC≢linkCD (sym
        (apiLink-inj (bundleBF-ev-link linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) {e₁ = BF.apiBFev linkAC d m} sBBD) ahlBF)))
... | PEA.evL _ sBAB
    with bundle-BF-ev-inv linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) {e₁ = BF.apiBFev linkAC d m} sBAB
       | cpr
...   | bcbcE bfc′ refl aStepAB | cpR-cons b′ cp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) bfc′ (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (consuming b′ cp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) (BF.apiBFev linkAC d m) linkAC≢linkCD)))
            dStep)
...   | bcbcE bfc′ refl aStepAB | cpR-prod b′ pp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) bfc′ (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (producing b′ pp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) (BF.apiBFev linkAC d m) linkAC≢linkCD)))
            dStep)
...   | bcbsE bfs′ refl aStepAB | cpR-cons b′ cp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) bfs′ (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (consuming b′ cp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) (BF.apiBFev linkAC d m) linkAC≢linkCD)))
            dStep)
...   | bcbsE bfs′ refl aStepAB | cpR-prod b′ pp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) bfs′ (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (producing b′ pp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) (BF.apiBFev linkAC d m) linkAC≢linkCD)))
            dStep)
-- `done` on the consume leg (link AC) is impossible: `decCP` fires `done` only via
-- the produce leg (link CD), contradicting `ahlDone`'s link AC
nodeC-fireAB na {X} {a = a} mem bStep dStep aicDone (ahlDone {d} {ch}) cpr =
  ⊥-elim (linkAC≢linkCD (apiLink-inj ahlDone (proj₁ (decCP-done-inv linkAC linkCD (SN.NodeStateC.cp-C na) dStep))))

-- firing link = linkCD (produce leg, RIGHT bundle)
nodeC-fireBD : (na : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (bundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na)
     ⦀ bundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → decCP linkAC linkCD (SN.NodeStateC.cp-C na) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → IsApiCSBF e → ApiHasLink linkCD e
  → CPEvR linkAC linkCD (SN.NodeStateC.cp-C na) D₁
  → NodeCEvR na e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeC-fireBD na {X} {a = a} mem bStep dStep aicCS (ahlCS {d} {m}) cpr
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na))
         (bundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAC≢linkCD
        (apiLink-inj (bundleCS-ev-link linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) {e₁ = CS.apiCSev linkCD d m} sBAB)
                     (bundleCS-ev-link linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) {e₁ = CS.apiCSev linkCD d m} sBBD)))
... | PEA.evL _ sBAB = ⊥-elim (linkAC≢linkCD
        (apiLink-inj (bundleCS-ev-link linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) {e₁ = CS.apiCSev linkCD d m} sBAB) ahlCS))
... | PEA.evR _ sBBD
    with bundle-CS-ev-inv linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) {e₁ = CS.apiCSev linkCD d m} sBBD
       | cpr
...   | bcscE csc′ refl aStepBD | cpR-cons b′ cp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) csc′ (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (consuming b′ cp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (CS.apiCSev linkCD d m) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
...   | bcscE csc′ refl aStepBD | cpR-prod b′ pp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) csc′ (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (producing b′ pp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (CS.apiCSev linkCD d m) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
...   | bcssE css′ refl aStepBD | cpR-cons b′ cp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) css′ (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (consuming b′ cp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (CS.apiCSev linkCD d m) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
...   | bcssE css′ refl aStepBD | cpR-prod b′ pp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) css′ (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (producing b′ pp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (CS.apiCSev linkCD d m) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
nodeC-fireBD na {X} {a = a} mem bStep dStep aicBF (ahlBF {d} {m}) cpr
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na))
         (bundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAC≢linkCD
        (apiLink-inj (bundleBF-ev-link linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) {e₁ = BF.apiBFev linkCD d m} sBAB)
                     (bundleBF-ev-link linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) {e₁ = BF.apiBFev linkCD d m} sBBD)))
... | PEA.evL _ sBAB = ⊥-elim (linkAC≢linkCD
        (apiLink-inj (bundleBF-ev-link linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) {e₁ = BF.apiBFev linkCD d m} sBAB) ahlBF))
... | PEA.evR _ sBBD
    with bundle-BF-ev-inv linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) {e₁ = BF.apiBFev linkCD d m} sBBD
       | cpr
...   | bcbcE bfc′ refl aStepBD | cpR-cons b′ cp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) bfc′ (SN.NodeStateC.bfS-CD na) (consuming b′ cp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (BF.apiBFev linkCD d m) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
...   | bcbcE bfc′ refl aStepBD | cpR-prod b′ pp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) bfc′ (SN.NodeStateC.bfS-CD na) (producing b′ pp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (BF.apiBFev linkCD d m) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
...   | bcbsE bfs′ refl aStepBD | cpR-cons b′ cp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) bfs′ (consuming b′ cp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (BF.apiBFev linkCD d m) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
...   | bcbsE bfs′ refl aStepBD | cpR-prod b′ pp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) bfs′ (producing b′ pp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (BF.apiBFev linkCD d m) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
-- `done` on the produce leg (link CD): CS/BF SERVER done synced with produce pp7/pp8
nodeC-fireBD na {X} {a = a} mem bStep dStep aicDone (ahlDone {d} {ch}) cpr
  with decCP-done-inv linkAC linkCD (SN.NodeStateC.cp-C na) dStep
nodeC-fireBD na {X} {a = a} mem bStep dStep aicDone (ahlDone {d} {ch}) cpr | _ , refl , inj₁ refl
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na))
         (bundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAC≢linkCD
        (apiLink-inj (bundleCS-ev-link linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) {e₁ = CS.doneCS linkCD hi} sBAB)
                     (bundleCS-ev-link linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) {e₁ = CS.doneCS linkCD hi} sBBD)))
... | PEA.evL _ sBAB = ⊥-elim (linkAC≢linkCD
        (apiLink-inj (bundleCS-ev-link linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) {e₁ = CS.doneCS linkCD hi} sBAB) (ahlDone {d = hi} {ch = N2N_ChainSync})))
... | PEA.evR _ sBBD
    with bundle-CS-ev-inv linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) {e₁ = CS.doneCS linkCD hi} sBBD
       | cpr
...   | bcscE csc′ refl aStepBD | cpR-cons b′ cp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) csc′ (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (consuming b′ cp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (CS.doneCS linkCD hi) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
...   | bcscE csc′ refl aStepBD | cpR-prod b′ pp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) csc′ (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (producing b′ pp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (CS.doneCS linkCD hi) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
...   | bcssE css′ refl aStepBD | cpR-cons b′ cp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) css′ (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (consuming b′ cp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (CS.doneCS linkCD hi) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
...   | bcssE css′ refl aStepBD | cpR-prod b′ pp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) css′ (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (producing b′ pp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (CS.doneCS linkCD hi) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
-- `done` on the produce leg (link CD, BlockFetch): BF SERVER doneBF synced with produce pp8
nodeC-fireBD na {X} {a = a} mem bStep dStep aicDone (ahlDone {d} {ch}) cpr | _ , refl , inj₂ refl
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na))
         (bundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAC≢linkCD
        (apiLink-inj (bundleBF-ev-link linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) {e₁ = BF.doneBF linkCD hi} sBAB)
                     (bundleBF-ev-link linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) {e₁ = BF.doneBF linkCD hi} sBBD)))
... | PEA.evL _ sBAB = ⊥-elim (linkAC≢linkCD
        (apiLink-inj (bundleBF-ev-link linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) {e₁ = BF.doneBF linkCD hi} sBAB) (ahlDone {d = hi} {ch = N2N_BlockFetch})))
... | PEA.evR _ sBBD
    with bundle-BF-ev-inv linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na) {e₁ = BF.doneBF linkCD hi} sBBD
       | cpr
...   | bcbcE bfc′ refl aStepBD | cpR-cons b′ cp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) bfc′ (SN.NodeStateC.bfS-CD na) (consuming b′ cp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (BF.doneBF linkCD hi) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
...   | bcbcE bfc′ refl aStepBD | cpR-prod b′ pp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) bfc′ (SN.NodeStateC.bfS-CD na) (producing b′ pp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (BF.doneBF linkCD hi) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
...   | bcbsE bfs′ refl aStepBD | cpR-cons b′ cp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) bfs′ (consuming b′ cp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (BF.doneBF linkCD hi) (λ q → linkAC≢linkCD (sym q)))))
            dStep)
...   | bcbsE bfs′ refl aStepBD | cpR-prod b′ pp′ refl =
        ncEv (SN.mkNodeC (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) bfs′ (producing b′ pp′) (SN.NodeStateC.inert-AC na) (SN.NodeStateC.inert-CD na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
               aStepBD
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na) (BF.doneBF linkCD hi) (λ q → linkAC≢linkCD (sym q)))))
            dStep)

-- node-B api inversion: reflect the sync, pick the link via `decCP-ev-link`'s ⊎
nodeC-ev-api : (na : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a
  → decNodeC na ─[ ev (evl (evLabel X e a)) ]─► A′
  → NodeCEvR na e a A′
nodeC-ev-api na {X} {e} {a} mem step
  with SStep.reflect-node-api
         (bundleG linkAC hi lo (SN.NodeStateC.csC-AC na) (SN.NodeStateC.csS-AC na) (SN.NodeStateC.bfC-AC na) (SN.NodeStateC.bfS-AC na) (SN.NodeStateC.inert-AC na)
          ⦀ bundleG linkCD lo hi (SN.NodeStateC.csC-CD na) (SN.NodeStateC.csS-CD na) (SN.NodeStateC.bfC-CD na) (SN.NodeStateC.bfS-CD na) (SN.NodeStateC.inert-CD na))
         (decCP linkAC linkCD (SN.NodeStateC.cp-C na))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with decCP-ev-link linkAC linkCD (SN.NodeStateC.cp-C na) dStep
... | inj₁ ahl = nodeC-fireAB na mem bStep dStep (decCP-apiCSBF linkAC linkCD (SN.NodeStateC.cp-C na) dStep) ahl (decCP-ev-inv linkAC linkCD (SN.NodeStateC.cp-C na) dStep)
... | inj₂ ahl = nodeC-fireBD na mem bStep dStep (decCP-apiCSBF linkAC linkCD (SN.NodeStateC.cp-C na) dStep) ahl (decCP-ev-inv linkAC linkCD (SN.NodeStateC.cp-C na) dStep)


------------------------------------------------------------------------
-- NODE-VALUE NON-OFFER LEAF (top 4-node `⦀` evBoth refutation).  Each node
-- offers api events only on its two links with a fixed role per link
-- (fingerprint below).  Any two DISTINCT nodes have disjoint (link, role)
-- fingerprints — on a SHARED link the roles differ (`prod≢cons`), otherwise the
-- links differ (`apiLink-inj`) — so no api event is offered by two nodes.  The
-- per-node `nodeX-fp` reads the fingerprint off a step (reflect the driver sync,
-- pin link via `decX-ev-link` + role via `decX-ev-{prod,cons}`); the pairwise
-- `nodeY-no-when-X` and the group `groupX-no` compose them into the `¬ IoOffers`
-- the top peel + `⦀-ev-L/R` idle-sibling non-offers consume.
------------------------------------------------------------------------

-- remaining distinct-link disequalities (`linkAB≢linkAC` is re-exported from
-- SysOracle; the shared-link pairs already appear above)
linkAB≢linkCD : ¬ (linkAB ≡ linkCD)
linkAB≢linkCD ()
linkAC≢linkBD : ¬ (linkAC ≡ linkBD)
linkAC≢linkBD ()

-- relay-driver combined link+role pinning (consuming → client tag on `l₁`;
-- cp6 handoff + producing → server tag on `l₂`) — correlates link and role
decCP-ev-linkrole : (l₁ l₂ : Link) (ph : SN.CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ ph ─[ ev (evl (evLabel X e a)) ]─► M
  → (ApiIsCons e × ApiHasLink l₁ e) ⊎ (ApiIsProd e × ApiHasLink l₂ e)
decCP-ev-linkrole l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl = inj₁ (decCons-ev-cons l₁ hi b cp0 sc , decCons-ev-link l₁ hi b cp0 sc)
decCP-ev-linkrole l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl = inj₁ (decCons-ev-cons l₁ hi b cp1 sc , decCons-ev-link l₁ hi b cp1 sc)
decCP-ev-linkrole l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl = inj₁ (decCons-ev-cons l₁ hi b cp2 sc , decCons-ev-link l₁ hi b cp2 sc)
decCP-ev-linkrole l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl = inj₁ (decCons-ev-cons l₁ hi b cp3 sc , decCons-ev-link l₁ hi b cp3 sc)
decCP-ev-linkrole l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl = inj₁ (decCons-ev-cons l₁ hi b cp4 sc , decCons-ev-link l₁ hi b cp4 sc)
decCP-ev-linkrole l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl = inj₁ (decCons-ev-cons l₁ hi b cp5 sc , decCons-ev-link l₁ hi b cp5 sc)
decCP-ev-linkrole l₁ l₂ (consuming b cp6) step =
  inj₂ (decProd-ev-prod l₂ hi b pp0 (step-fcong refl step) , decProd-ev-link l₂ hi b pp0 (step-fcong refl step))
decCP-ev-linkrole l₁ l₂ (producing b pp) step =
  inj₂ (decProd-ev-prod l₂ hi b pp step , decProd-ev-link l₂ hi b pp step)

-- node-A fingerprint: a producer on either of its links AB / AC
nodeA-fp : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a → SN.decNodeA na ─[ ev (evl (evLabel X e a)) ]─► A′
  → ApiIsProd e × (ApiHasLink linkAB e ⊎ ApiHasLink linkAC e)
nodeA-fp na mem step
  with SStep.reflect-node-api
         (SN.bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ SN.bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi b1 (SN.NodeStateA.prod-AC na))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sAB = decProd-ev-prod linkAB hi b1 (SN.NodeStateA.prod-AB na) sAB , inj₁ (decProd-ev-link linkAB hi b1 (SN.NodeStateA.prod-AB na) sAB)
... | PEA.evR _ sAC = decProd-ev-prod linkAC hi b1 (SN.NodeStateA.prod-AC na) sAC , inj₂ (decProd-ev-link linkAC hi b1 (SN.NodeStateA.prod-AC na) sAC)
... | PEA.evBoth _ sAB sAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (decProd-ev-link linkAB hi b1 (SN.NodeStateA.prod-AB na) sAB)
                     (decProd-ev-link linkAC hi b1 (SN.NodeStateA.prod-AC na) sAC)))

-- node-D fingerprint: a consumer on either of its links BD / CD
nodeD-fp : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a → decNodeD nd ─[ ev (evl (evLabel X e a)) ]─► A′
  → ApiIsCons e × (ApiHasLink linkBD e ⊎ ApiHasLink linkCD e)
nodeD-fp nd mem step
  with SStep.reflect-node-api
         (bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ bundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (decConsD linkBD (SN.NodeStateD.cons-BD nd)) (decConsD linkCD (SN.NodeStateD.cons-CD nd)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sBD = decConsD-ev-cons linkBD (SN.NodeStateD.cons-BD nd) sBD , inj₁ (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sBD)
... | PEA.evR _ sCD = decConsD-ev-cons linkCD (SN.NodeStateD.cons-CD nd) sCD , inj₂ (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sCD)
... | PEA.evBoth _ sBD sCD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sBD)
                     (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sCD)))

-- node-B fingerprint: consumer on AB (relay consume leg) or producer on BD
nodeB-fp : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a → decNodeB nb ─[ ev (evl (evLabel X e a)) ]─► A′
  → (ApiIsCons e × ApiHasLink linkAB e) ⊎ (ApiIsProd e × ApiHasLink linkBD e)
nodeB-fp nb mem step
  with SStep.reflect-node-api
         (bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ bundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl = decCP-ev-linkrole linkAB linkBD (SN.NodeStateB.cp-B nb) dStep

-- node-C fingerprint: consumer on AC (relay consume leg) or producer on CD
nodeC-fp : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a → decNodeC nc ─[ ev (evl (evLabel X e a)) ]─► A′
  → (ApiIsCons e × ApiHasLink linkAC e) ⊎ (ApiIsProd e × ApiHasLink linkCD e)
nodeC-fp nc mem step
  with SStep.reflect-node-api
         (bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ bundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl = decCP-ev-linkrole linkAC linkCD (SN.NodeStateC.cp-C nc) dStep

-- pairwise non-offers: a node cannot offer an event fired by node A / B / C
-- (given the firing node's fingerprint).  Role clash on a shared link, else link.
nodeB-no-when-A : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ApiIsProd e × (ApiHasLink linkAB e ⊎ ApiHasLink linkAC e)
  → ¬ IoOffers (decNodeB nb) e a
nodeB-no-when-A nb mem (prodA , linkA) (M , step) with nodeB-fp nb mem step
... | inj₁ (consB , _) = prod≢cons prodA consB
... | inj₂ (_ , ahlBD) with linkA
...   | inj₁ ahlAB = linkAB≢linkBD (apiLink-inj ahlAB ahlBD)
...   | inj₂ ahlAC = linkAC≢linkBD (apiLink-inj ahlAC ahlBD)

nodeC-no-when-A : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ApiIsProd e × (ApiHasLink linkAB e ⊎ ApiHasLink linkAC e)
  → ¬ IoOffers (decNodeC nc) e a
nodeC-no-when-A nc mem (prodA , linkA) (M , step) with nodeC-fp nc mem step
... | inj₁ (consC , _) = prod≢cons prodA consC
... | inj₂ (_ , ahlCD) with linkA
...   | inj₁ ahlAB = linkAB≢linkCD (apiLink-inj ahlAB ahlCD)
...   | inj₂ ahlAC = linkAC≢linkCD (apiLink-inj ahlAC ahlCD)

nodeD-no-when-A : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ApiIsProd e × (ApiHasLink linkAB e ⊎ ApiHasLink linkAC e)
  → ¬ IoOffers (decNodeD nd) e a
nodeD-no-when-A nd mem (prodA , _) (M , step) with nodeD-fp nd mem step
... | consDd , _ = prod≢cons prodA consDd

nodeC-no-when-B : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → (ApiIsCons e × ApiHasLink linkAB e) ⊎ (ApiIsProd e × ApiHasLink linkBD e)
  → ¬ IoOffers (decNodeC nc) e a
nodeC-no-when-B nc mem fpB (M , step) with nodeC-fp nc mem step | fpB
... | inj₁ (consC , ahlAC) | inj₁ (_ , ahlAB) = linkAB≢linkAC (apiLink-inj ahlAB ahlAC)
... | inj₁ (consC , _)     | inj₂ (prodB , _) = prod≢cons prodB consC
... | inj₂ (prodC , _)     | inj₁ (consB , _) = prod≢cons prodC consB
... | inj₂ (prodC , ahlCD) | inj₂ (_ , ahlBD) = linkBD≢linkCD (apiLink-inj ahlBD ahlCD)

nodeD-no-when-B : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → (ApiIsCons e × ApiHasLink linkAB e) ⊎ (ApiIsProd e × ApiHasLink linkBD e)
  → ¬ IoOffers (decNodeD nd) e a
nodeD-no-when-B nd mem fpB (M , step) with nodeD-fp nd mem step | fpB
... | (_ , inj₁ ahlBD) | inj₁ (_ , ahlAB) = linkAB≢linkBD (apiLink-inj ahlAB ahlBD)
... | (_ , inj₂ ahlCD) | inj₁ (_ , ahlAB) = linkAB≢linkCD (apiLink-inj ahlAB ahlCD)
... | (consDd , _)     | inj₂ (prodB , _) = prod≢cons prodB consDd

nodeD-no-when-C : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → (ApiIsCons e × ApiHasLink linkAC e) ⊎ (ApiIsProd e × ApiHasLink linkCD e)
  → ¬ IoOffers (decNodeD nd) e a
nodeD-no-when-C nd mem fpC (M , step) with nodeD-fp nd mem step | fpC
... | (_ , inj₁ ahlBD) | inj₁ (_ , ahlAC) = linkAC≢linkBD (apiLink-inj ahlAC ahlBD)
... | (_ , inj₂ ahlCD) | inj₁ (_ , ahlAC) = linkAC≢linkCD (apiLink-inj ahlAC ahlCD)
... | (consDd , _)     | inj₂ (prodC , _) = prod≢cons prodC consDd

-- group non-offers: the sibling group of a firing node offers nothing on its
-- event (the `viewV … ≡ nothing` the top 4-node `⦀-ev-L/R` solo lift needs)
groupA-no : (na : SN.NodeStateA) (nb : SN.NodeStateB) (nc : SN.NodeStateC) (nd : SN.NodeStateD)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a → SN.decNodeA na ─[ ev (evl (evLabel X e a)) ]─► A′
  → ¬ IoOffers (decNodeB nb ⦀ (decNodeC nc ⦀ decNodeD nd)) e a
groupA-no na nb nc nd mem sA =
  SStep.⦀-noOffer (decNodeB nb) (decNodeC nc ⦀ decNodeD nd)
    (nodeB-no-when-A nb mem fpA)
    (SStep.⦀-noOffer (decNodeC nc) (decNodeD nd) (nodeC-no-when-A nc mem fpA) (nodeD-no-when-A nd mem fpA))
  where fpA = nodeA-fp na mem sA

groupB-no : (nb : SN.NodeStateB) (nc : SN.NodeStateC) (nd : SN.NodeStateD)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a → decNodeB nb ─[ ev (evl (evLabel X e a)) ]─► A′
  → ¬ IoOffers (decNodeC nc ⦀ decNodeD nd) e a
groupB-no nb nc nd mem sB =
  SStep.⦀-noOffer (decNodeC nc) (decNodeD nd) (nodeC-no-when-B nc mem fpB) (nodeD-no-when-B nd mem fpB)
  where fpB = nodeB-fp nb mem sB

------------------------------------------------------------------------
-- MEDIUM api-non-offer LEAF (top 4-node `⦀` disjointness: `reflect-top-ev`'s
-- `inj₁`).  The breakable medium `decMed m = ⦀Fin numLinks (λ l → decLink l …)`
-- fires only io (`input`/`output`) or `break`, never any apiCS/apiBF: each link
-- `decLink l ph false = renameMap (copy-fold) △ (break l ⟶₀ Skip)` peels its `△`
-- (break refuses the api tag), reflects the rename, and hits `ιNet⁻¹ (apiCS/apiBF)
-- ≡ nothing` (no copy-fold pre-image); the broken link is `Skip` (`ret`, no event).
-- `⦀Fin-noOffer` composes over the four links.
------------------------------------------------------------------------

-- an interleave `⦀Fin n f` offers nothing when every component `f i` does
-- (`⦀Fin (suc n) f = f fzero ⦀ ⦀Fin n …`; the empty tail is `Skip = ret`)
⦀Fin-noOffer : (n : ℕ) (f : Fin n → NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → (∀ i → ¬ IoOffers (f i) e a) → ¬ IoOffers (⦀Fin n f) e a
⦀Fin-noOffer zero    f h (M , step) = ret-no-ev {P = ⦀Fin zero f} refl step
⦀Fin-noOffer (suc n) f h =
  SStep.⦀-noOffer (f fzero) (⦀Fin n (λ i → f (fsuc i)))
    (h fzero)
    (⦀Fin-noOffer n (λ i → f (fsuc i)) (λ i → h (fsuc i)))

-- one breakable link offers no apiCS/apiBF: broken ⇒ `Skip`/`ret` (no event);
-- unbroken ⇒ `△-ev-elim` (break ≠ api) → `renameMap-ev-reflect-ι` → `ιNet⁻¹ api
-- ≡ nothing` refutes any copy-fold pre-image
decLink-no-api : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → IsApiCSBF e → ¬ IoOffers (decLink l ph b) e a
decLink-no-api l ph true  aic (M , step) = ret-no-ev {P = decLink l ph true} refl step
decLink-no-api l ph false aicCS (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , () , _
decLink-no-api l ph false aicBF (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , () , _
decLink-no-api l ph false aicDone (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , () , _

-- the breakable medium offers no apiCS/apiBF event (the `reflect-top-ev` `inj₁`)
medium-api-non-offer : (m : MedState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → IsApiCSBF e → ¬ IoOffers (decMed m) e a
medium-api-non-offer m aic =
  ⦀Fin-noOffer numLinks (λ l → decLink l (phase m l) (broken m l))
    (λ l → decLink-no-api l (phase m l) (broken m l) aic)

-- one breakable link offers no `done` (`ιNet⁻¹ (done …) ≡ nothing`, so the
-- copy-fold pre-image is refuted exactly as for apiCS/apiBF; broken ⇒ `ret`).
-- The `△`-Q break-side refuses `done` (`done ≠ break`, `refl`).
decLink-no-done : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decLink l ph b) (done l₀ d₀ id₀) a
decLink-no-done l ph true  (M , step) = ret-no-ev {P = decLink l ph true} refl step
decLink-no-done l ph false (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , () , _

-- the breakable medium offers no `done` (the `reflect-top-ev` `inj₁` for `done`)
medium-no-done : (m : MedState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decMed m) (done l₀ d₀ id₀) a
medium-no-done m =
  ⦀Fin-noOffer numLinks (λ l → decLink l (phase m l) (broken m l))
    (λ l → decLink-no-done l (phase m l) (broken m l))

-- the FROZEN KA/TS/LN/LF peers (`iter (…Step) initial`) fire no `doneX`: each
-- head vismap is the catch-all `nothing` on every `doneX` (the done branch is
-- reachable only AFTER a wire-`send…Done` prefix, so the frozen initial state
-- refuses it).  Force the iter head to its react, read the `nothing` off the
-- source vismap.  Uniform across the 8 peers (all `pchoice` heads).
ka-c-head-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀} {P₁ : PTree KA.KAEv (ExtI KA.KAEv) _}
  → KA.KAclientStClient l d KAL.─[ KAL.ev (KAL.evl (KAL.evLabel ⊤₀ (KA.doneKA l₀ d₀) a)) ]─► P₁ → ⊥
ka-c-head-no-done l d step with KAL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ka-s-head-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀} {P₁ : PTree KA.KAEv (ExtI KA.KAEv) _}
  → KA.KAserverStClient l d KAL.─[ KAL.ev (KAL.evl (KAL.evLabel ⊤₀ (KA.doneKA l₀ d₀) a)) ]─► P₁ → ⊥
ka-s-head-no-done l d step with KAL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ts-c-head-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀} {P₁ : PTree TS.TSEv (ExtI TS.TSEv) _}
  → TS.TSclientStClient l d TSL.─[ TSL.ev (TSL.evl (TSL.evLabel ⊤₀ (TS.doneTS l₀ d₀) a)) ]─► P₁ → ⊥
ts-c-head-no-done l d step with TSL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ts-s-head-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀} {P₁ : PTree TS.TSEv (ExtI TS.TSEv) _}
  → TS.TSserverStClient l d TSL.─[ TSL.ev (TSL.evl (TSL.evLabel ⊤₀ (TS.doneTS l₀ d₀) a)) ]─► P₁ → ⊥
ts-s-head-no-done l d step with TSL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ln-c-head-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀} {P₁ : PTree LNp.LNEv (ExtI LNp.LNEv) _}
  → LNp.LNclientStClient l d LNL.─[ LNL.ev (LNL.evl (LNL.evLabel ⊤₀ (LNp.doneLN l₀ d₀) a)) ]─► P₁ → ⊥
ln-c-head-no-done l d step with LNL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ln-s-head-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀} {P₁ : PTree LNp.LNEv (ExtI LNp.LNEv) _}
  → LNp.LNserverStClient l d LNL.─[ LNL.ev (LNL.evl (LNL.evLabel ⊤₀ (LNp.doneLN l₀ d₀) a)) ]─► P₁ → ⊥
ln-s-head-no-done l d step with LNL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
lf-c-head-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀} {P₁ : PTree LFp.LFEv (ExtI LFp.LFEv) _}
  → LFp.LFclientStClient l d LFL.─[ LFL.ev (LFL.evl (LFL.evLabel ⊤₀ (LFp.doneLF l₀ d₀) a)) ]─► P₁ → ⊥
lf-c-head-no-done l d step with LFL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
lf-s-head-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀} {P₁ : PTree LFp.LFEv (ExtI LFp.LFEv) _}
  → LFp.LFserverStClient l d LFL.─[ LFL.ev (LFL.evl (LFL.evLabel ⊤₀ (LFp.doneLF l₀ d₀) a)) ]─► P₁ → ⊥
lf-s-head-no-done l d step with LFL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()

-- the renamed frozen peers refuse `done…proto` (reflect through the rename to the
-- source `doneX`, then the head refutation).  `ιX⁻¹ (done l₀ d₀ N2N_X) ≡ just
-- (doneX l₀ d₀)` pins the source event by `refl`.
KAclientA-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (KAclientA l d) (done l₀ d₀ N2N_KeepAlive) a
KAclientA-no-done l d {l₀} {d₀} =
  KANOff.renameMap-noOffer (KA.KAclientStClient l d)
    (λ { .(KA.doneKA l₀ d₀) refl (P₁ , step) → ka-c-head-no-done l d step })
KAserverA-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (KAserverA l d) (done l₀ d₀ N2N_KeepAlive) a
KAserverA-no-done l d {l₀} {d₀} =
  KANOff.renameMap-noOffer (KA.KAserverStClient l d)
    (λ { .(KA.doneKA l₀ d₀) refl (P₁ , step) → ka-s-head-no-done l d step })
TSclientA-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (TSclientA l d) (done l₀ d₀ N2N_TxSubmission) a
TSclientA-no-done l d {l₀} {d₀} =
  TSNOff.renameMap-noOffer (TS.TSclientStClient l d)
    (λ { .(TS.doneTS l₀ d₀) refl (P₁ , step) → ts-c-head-no-done l d step })
TSserverA-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (TSserverA l d) (done l₀ d₀ N2N_TxSubmission) a
TSserverA-no-done l d {l₀} {d₀} =
  TSNOff.renameMap-noOffer (TS.TSserverStClient l d)
    (λ { .(TS.doneTS l₀ d₀) refl (P₁ , step) → ts-s-head-no-done l d step })

-- source-level: the TS client peer NEVER offers `doneTS` at any tracked position
-- (the client has no node-local done; every head/sil is a react/sil offering
-- wire/api events only).  Case the position; refute the offer via `TSL.ev-inv`.
ts-c-pos-no-doneTS : (l : Link) (d : Dir) (pos : SN.TScPos) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
    {P₁ : PTree TS.TSEv (ExtI TS.TSEv) _}
  → SN.decTSc-src l d pos TSL.─[ TSL.ev (TSL.evl (TSL.evLabel ⊤₀ (TS.doneTS l₀ d₀) a)) ]─► P₁ → ⊥
ts-c-pos-no-doneTS l d (SN.tcHead TS.stInit)             step with TSL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ts-c-pos-no-doneTS l d (SN.tcHead TS.stIdle)             step with TSL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ts-c-pos-no-doneTS l d (SN.tcHead TS.stTxIdsBlocking)    step with TSL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ts-c-pos-no-doneTS l d (SN.tcHead TS.stTxIdsNonBlocking) step with TSL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ts-c-pos-no-doneTS l d (SN.tcHead TS.stTxs)              step with TSL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ts-c-pos-no-doneTS l d (SN.tcHead TS.stDone)             step with TSL.ev-inv step
... | _ , _ , () , _
ts-c-pos-no-doneTS l d (SN.tcSil st)                     step with TSL.ev-inv step
... | _ , _ , () , _

-- source-level: the TS server peer NEVER offers `doneTS` at any tracked position
-- (`doneTS` only occurs behind an api prefix — a mid-leaf — never at a head/sil).
ts-s-pos-no-doneTS : (l : Link) (d : Dir) (pos : SN.TSsPos) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
    {P₁ : PTree TS.TSEv (ExtI TS.TSEv) _}
  → SN.decTSs-src l d pos TSL.─[ TSL.ev (TSL.evl (TSL.evLabel ⊤₀ (TS.doneTS l₀ d₀) a)) ]─► P₁ → ⊥
ts-s-pos-no-doneTS l d (SN.tsHead TS.stInit)             step with TSL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ts-s-pos-no-doneTS l d (SN.tsHead TS.stIdle)             step with TSL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ts-s-pos-no-doneTS l d (SN.tsHead TS.stTxIdsBlocking)    step with TSL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ts-s-pos-no-doneTS l d (SN.tsHead TS.stTxIdsNonBlocking) step with TSL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ts-s-pos-no-doneTS l d (SN.tsHead TS.stTxs)              step with TSL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ts-s-pos-no-doneTS l d (SN.tsHead TS.stDone)             step with TSL.ev-inv step
... | _ , _ , () , _
ts-s-pos-no-doneTS l d (SN.tsSil st)                     step with TSL.ev-inv step
... | _ , _ , () , _

-- position-general renamed TS no-done (mirror TSclientA-no-done over any position)
decTSc-no-done : (l : Link) (d : Dir) (pos : SN.TScPos) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (SN.decTSc l d pos) (done l₀ d₀ N2N_TxSubmission) a
decTSc-no-done l d pos {l₀} {d₀} =
  TSNOff.renameMap-noOffer (SN.decTSc-src l d pos)
    (λ { .(TS.doneTS l₀ d₀) refl (P₁ , step) → ts-c-pos-no-doneTS l d pos step })
decTSs-no-done : (l : Link) (d : Dir) (pos : SN.TSsPos) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (SN.decTSs l d pos) (done l₀ d₀ N2N_TxSubmission) a
decTSs-no-done l d pos {l₀} {d₀} =
  TSNOff.renameMap-noOffer (SN.decTSs-src l d pos)
    (λ { .(TS.doneTS l₀ d₀) refl (P₁ , step) → ts-s-pos-no-doneTS l d pos step })

-- source-level: the KA client peer NEVER offers `doneKA` at any tracked position
-- (the client only offers apiKAev / sendKA; every head/sil is a react/sil/ret)
ka-c-pos-no-doneKA : (l : Link) (d : Dir) (pos : SN.KAcPos) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
    {P₁ : PTree KA.KAEv (ExtI KA.KAEv) _}
  → SN.decKAc-src l d pos KAL.─[ KAL.ev (KAL.evl (KAL.evLabel ⊤₀ (KA.doneKA l₀ d₀) a)) ]─► P₁ → ⊥
ka-c-pos-no-doneKA l d (SN.kcHead KA.stClient)     step with KAL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ka-c-pos-no-doneKA l d (SN.kcHead (KA.stServer c)) step with KAL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ka-c-pos-no-doneKA l d (SN.kcHead KA.stDone)       step with KAL.ev-inv step
... | _ , _ , () , _
ka-c-pos-no-doneKA l d (SN.kcSil st)               step with KAL.ev-inv step
... | _ , _ , () , _

-- source-level: the KA server peer NEVER offers `doneKA` at any tracked position
-- (`doneKA` only occurs behind the `receiveKA` io — a mid-leaf — never at a head/sil)
ka-s-pos-no-doneKA : (l : Link) (d : Dir) (pos : SN.KAsPos) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
    {P₁ : PTree KA.KAEv (ExtI KA.KAEv) _}
  → SN.decKAs-src l d pos KAL.─[ KAL.ev (KAL.evl (KAL.evLabel ⊤₀ (KA.doneKA l₀ d₀) a)) ]─► P₁ → ⊥
ka-s-pos-no-doneKA l d (SN.ksHead KA.stClient)     step with KAL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ka-s-pos-no-doneKA l d (SN.ksHead (KA.stServer c)) step with KAL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ka-s-pos-no-doneKA l d (SN.ksHead KA.stDone)       step with KAL.ev-inv step
... | _ , _ , () , _
ka-s-pos-no-doneKA l d (SN.ksSil st)               step with KAL.ev-inv step
... | _ , _ , () , _

-- position-general renamed KA no-done (mirror decTSc-no-done over any position)
decKAc-no-done : (l : Link) (d : Dir) (pos : SN.KAcPos) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (SN.decKAc l d pos) (done l₀ d₀ N2N_KeepAlive) a
decKAc-no-done l d pos {l₀} {d₀} =
  KANOff.renameMap-noOffer (SN.decKAc-src l d pos)
    (λ { .(KA.doneKA l₀ d₀) refl (P₁ , step) → ka-c-pos-no-doneKA l d pos step })
decKAs-no-done : (l : Link) (d : Dir) (pos : SN.KAsPos) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (SN.decKAs l d pos) (done l₀ d₀ N2N_KeepAlive) a
decKAs-no-done l d pos {l₀} {d₀} =
  KANOff.renameMap-noOffer (SN.decKAs-src l d pos)
    (λ { .(KA.doneKA l₀ d₀) refl (P₁ , step) → ka-s-pos-no-doneKA l d pos step })

-- source-level: the LN client peer NEVER offers `doneLN` at any tracked position
ln-c-pos-no-doneLN : (l : Link) (d : Dir) (pos : SN.LNcPos) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
    {P₁ : PTree LNp.LNEv (ExtI LNp.LNEv) _}
  → SN.decLNc-src l d pos LNL.─[ LNL.ev (LNL.evl (LNL.evLabel ⊤₀ (LNp.doneLN l₀ d₀) a)) ]─► P₁ → ⊥
ln-c-pos-no-doneLN l d (SN.lncHead LNp.stIdle) step with LNL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ln-c-pos-no-doneLN l d (SN.lncHead LNp.stBusy) step with LNL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ln-c-pos-no-doneLN l d (SN.lncHead LNp.stDone) step with LNL.ev-inv step
... | _ , _ , () , _
ln-c-pos-no-doneLN l d (SN.lncSil st)          step with LNL.ev-inv step
... | _ , _ , () , _

-- source-level: the LN server peer NEVER offers `doneLN` at any tracked position
ln-s-pos-no-doneLN : (l : Link) (d : Dir) (pos : SN.LNsPos) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
    {P₁ : PTree LNp.LNEv (ExtI LNp.LNEv) _}
  → SN.decLNs-src l d pos LNL.─[ LNL.ev (LNL.evl (LNL.evLabel ⊤₀ (LNp.doneLN l₀ d₀) a)) ]─► P₁ → ⊥
ln-s-pos-no-doneLN l d (SN.lnsHead LNp.stIdle) step with LNL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ln-s-pos-no-doneLN l d (SN.lnsHead LNp.stBusy) step with LNL.ev-inv step
... | v , τc , feq , veq with react-injective feq
...   | refl , _ with veq
...     | ()
ln-s-pos-no-doneLN l d (SN.lnsHead LNp.stDone) step with LNL.ev-inv step
... | _ , _ , () , _
ln-s-pos-no-doneLN l d (SN.lnsSil st)          step with LNL.ev-inv step
... | _ , _ , () , _

-- position-general renamed LN no-done (mirror decKAc-no-done over any position)
decLNc-no-done : (l : Link) (d : Dir) (pos : SN.LNcPos) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (SN.decLNc l d pos) (done l₀ d₀ N2N_LeiosNotify) a
decLNc-no-done l d pos {l₀} {d₀} =
  LNNOff.renameMap-noOffer (SN.decLNc-src l d pos)
    (λ { .(LNp.doneLN l₀ d₀) refl (P₁ , step) → ln-c-pos-no-doneLN l d pos step })
decLNs-no-done : (l : Link) (d : Dir) (pos : SN.LNsPos) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (SN.decLNs l d pos) (done l₀ d₀ N2N_LeiosNotify) a
decLNs-no-done l d pos {l₀} {d₀} =
  LNNOff.renameMap-noOffer (SN.decLNs-src l d pos)
    (λ { .(LNp.doneLN l₀ d₀) refl (P₁ , step) → ln-s-pos-no-doneLN l d pos step })
LNclientA-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (LNclientA l d) (done l₀ d₀ N2N_LeiosNotify) a
LNclientA-no-done l d {l₀} {d₀} =
  LNNOff.renameMap-noOffer (LNp.LNclientStClient l d)
    (λ { .(LNp.doneLN l₀ d₀) refl (P₁ , step) → ln-c-head-no-done l d step })
LNserverA-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (LNserverA l d) (done l₀ d₀ N2N_LeiosNotify) a
LNserverA-no-done l d {l₀} {d₀} =
  LNNOff.renameMap-noOffer (LNp.LNserverStClient l d)
    (λ { .(LNp.doneLN l₀ d₀) refl (P₁ , step) → ln-s-head-no-done l d step })
LFclientA-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (LFclientA l d) (done l₀ d₀ N2N_LeiosFetch) a
LFclientA-no-done l d {l₀} {d₀} =
  LFNOff.renameMap-noOffer (LFp.LFclientStClient l d)
    (λ { .(LFp.doneLF l₀ d₀) refl (P₁ , step) → lf-c-head-no-done l d step })
LFserverA-no-done : (l : Link) (d : Dir) {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (LFserverA l d) (done l₀ d₀ N2N_LeiosFetch) a
LFserverA-no-done l d {l₀} {d₀} =
  LFNOff.renameMap-noOffer (LFp.LFserverStClient l d)
    (λ { .(LFp.doneLF l₀ d₀) refl (P₁ , step) → lf-s-head-no-done l d step })


-- the whole 12-peer bundle refuses `done…{KA,TS,LN,LF}`: the matching-protocol
-- peers are FROZEN (`*-no-done`), every other peer's ι-preimage is `nothing`
-- (`renameMap-noOffer-χ`/`*-noOffer`, `refl`).  The `reflect-top-ev` nodes-side
-- non-offer for the impossible `done…proto` events (proto ∉ {CS,BF}).
bundleG-no-done-KA : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) (done l₀ d₀ N2N_KeepAlive) a
bundleG-no-done-KA l cl sv csc css bfc bfs ip =
  SStep.⦀-noOffer _ _ (decKAc-no-done l cl (SN.kac ip))
   (SStep.⦀-noOffer _ _ (decKAs-no-done l sv (SN.kas ip))
    (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSc-src l cl csc) refl)
     (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSs-src l sv css) refl)
      (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFc-src l cl bfc) refl)
       (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFs-src l sv bfs) refl)
        (SStep.⦀-noOffer _ _ (decTSc-noOffer l cl (SN.tsc ip) refl)
         (SStep.⦀-noOffer _ _ (decTSs-noOffer l sv (SN.tss ip) refl)
          (SStep.⦀-noOffer _ _ (decLNc-noOffer l cl (SN.lnc ip) refl)
           (SStep.⦀-noOffer _ _ (decLNs-noOffer l sv (SN.lns ip) refl)
            (SStep.⦀-noOffer _ _ (LFclientA-noOffer l cl refl)
                                 (LFserverA-noOffer l sv refl)))))))))))
bundleG-no-done-TS : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) (done l₀ d₀ N2N_TxSubmission) a
bundleG-no-done-TS l cl sv csc css bfc bfs ip =
  SStep.⦀-noOffer _ _ (decKAc-noOffer l cl (SN.kac ip) refl)
   (SStep.⦀-noOffer _ _ (decKAs-noOffer l sv (SN.kas ip) refl)
    (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSc-src l cl csc) refl)
     (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSs-src l sv css) refl)
      (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFc-src l cl bfc) refl)
       (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFs-src l sv bfs) refl)
        (SStep.⦀-noOffer _ _ (decTSc-no-done l cl (SN.tsc ip))
         (SStep.⦀-noOffer _ _ (decTSs-no-done l sv (SN.tss ip))
          (SStep.⦀-noOffer _ _ (decLNc-noOffer l cl (SN.lnc ip) refl)
           (SStep.⦀-noOffer _ _ (decLNs-noOffer l sv (SN.lns ip) refl)
            (SStep.⦀-noOffer _ _ (LFclientA-noOffer l cl refl)
                                 (LFserverA-noOffer l sv refl)))))))))))
bundleG-no-done-LN : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) (done l₀ d₀ N2N_LeiosNotify) a
bundleG-no-done-LN l cl sv csc css bfc bfs ip =
  SStep.⦀-noOffer _ _ (decKAc-noOffer l cl (SN.kac ip) refl)
   (SStep.⦀-noOffer _ _ (decKAs-noOffer l sv (SN.kas ip) refl)
    (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSc-src l cl csc) refl)
     (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSs-src l sv css) refl)
      (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFc-src l cl bfc) refl)
       (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFs-src l sv bfs) refl)
        (SStep.⦀-noOffer _ _ (decTSc-noOffer l cl (SN.tsc ip) refl)
         (SStep.⦀-noOffer _ _ (decTSs-noOffer l sv (SN.tss ip) refl)
          (SStep.⦀-noOffer _ _ (decLNc-no-done l cl (SN.lnc ip))
           (SStep.⦀-noOffer _ _ (decLNs-no-done l sv (SN.lns ip))
            (SStep.⦀-noOffer _ _ (LFclientA-noOffer l cl refl)
                                 (LFserverA-noOffer l sv refl)))))))))))
bundleG-no-done-LF : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {l₀ : Link} {d₀ : Dir} {a : ⊤₀}
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) (done l₀ d₀ N2N_LeiosFetch) a
bundleG-no-done-LF l cl sv csc css bfc bfs ip =
  SStep.⦀-noOffer _ _ (decKAc-noOffer l cl (SN.kac ip) refl)
   (SStep.⦀-noOffer _ _ (decKAs-noOffer l sv (SN.kas ip) refl)
    (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSc-src l cl csc) refl)
     (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSs-src l sv css) refl)
      (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFc-src l cl bfc) refl)
       (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFs-src l sv bfs) refl)
        (SStep.⦀-noOffer _ _ (decTSc-noOffer l cl (SN.tsc ip) refl)
         (SStep.⦀-noOffer _ _ (decTSs-noOffer l sv (SN.tss ip) refl)
          (SStep.⦀-noOffer _ _ (decLNc-noOffer l cl (SN.lnc ip) refl)
           (SStep.⦀-noOffer _ _ (decLNs-noOffer l sv (SN.lns ip) refl)
            (SStep.⦀-noOffer _ _ (LFclientA-no-done l cl)
                                 (LFserverA-no-done l sv)))))))))))

------------------------------------------------------------------------
-- MEDIUM break ev-INVERSION LEAF (the `oev` break class).  A breakable link
-- `decLink l ph false = renameMap (copy-fold) △ (break l ⟶₀ Skip)` can fire the
-- `break l` INTERRUPT (the `△` RIGHT operand), continuing as `Skip` = the broken
-- link `decLink l ph true`.  The `△-ev-elim` committed in `SysOracle` handles
-- only the LEFT-fires (Q-non-offer) case; here we build the DUAL `△`-Q-fire
-- inversion (P = renameMap refuses `break`, since `ιNet⁻¹ (break l) ≡ nothing`,
-- so the merge commits Q's offer), then lift it through `⦀Fin` (link disjointness)
-- to a `MedState` successor with `broken l := true`.
------------------------------------------------------------------------

-- DUAL of `△-merge-ev-inv`: at an event the LEFT operand `P` does NOT offer
-- (`vP ≡ nothing`), the `△-merge` commits the RIGHT operand `Q`'s offer, so the
-- step is a `Q`-interrupt with `M ≡ Q′` (mirror of `△-merge-ev-inv`, sides flipped)
△-merge-Q-inv : (P : NetProc) (vP : VmapN) (τcP : TmapN) (vQ : VmapN) (τcQ : TmapN)
    (Q : NetProc) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) {M : NetProc}
  → PTree.force Q ≡ react vQ τcQ
  → vP (X , e) a ≡ nothing
  → △-merge (react vP τcP) (react vQ τcQ) Q (X , e) a ≡ just M
  → Σ[ Q′ ∈ NetProc ] (Q ─[ ev (evl (evLabel X e a)) ]─► Q′) × (M ≡ Q′)
△-merge-Q-inv P vP τcP vQ τcQ Q e a eqQ vPno meq rewrite vPno with vQ (_ , e) a in vqe
... | just Q′ = Q′ , sVis eqQ vqe , sym (just-injective meq)
... | nothing with meq
...   | ()

-- `△`-Q-ev-elim: a visible step of `P △ Q` (both reacts) at an event `P` refuses
-- is a right-`Q` interrupt ⇒ `M ≡ Q′` with a genuine `Q` step (mirror of `△-ev-elim`)
△-Q-ev-inv : {P Q M : NetProc} {vP : VmapN} {τcP : TmapN} {vQ : VmapN} {τcQ : TmapN}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
  → vP (X , e) a ≡ nothing
  → (P △ Q) ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ Q′ ∈ NetProc ] (Q ─[ ev (evl (evLabel X e a)) ]─► Q′) × (M ≡ Q′)
△-Q-ev-inv {P = P} {Q = Q} {vP = vP} {τcP = τcP} {vQ = vQ} {τcQ = τcQ} {X} {e} {a}
           eqP eqQ vPno step with ev-inv step
... | v , τc , feq , veq with react-injective (trans (sym feq) (force-△-react eqP eqQ))
...   | vEq , _ = △-merge-Q-inv P vP τcP vQ τcQ Q e a eqQ vPno
                     (trans (sym (cong (λ w → w (X , e) a) vEq)) veq)

-- inject the `break` constructor's link out of an equal event label
break-lbl-inj : {l i : Link} {a x : ⊤₀}
  → evl {R = ⊤ {0ℓ}} (evLabel ⊤₀ (break l) a) ≡ evl (evLabel ⊤₀ (break i) x) → i ≡ l
break-lbl-inj refl = refl

-- one breakable link fires `break l` only at its OWN link (`i ≡ l`), continuing as
-- `Skip`: broken (`Skip`/`ret`) has no step; unbroken peels the `△` RIGHT (renameMap
-- refuses `break` by `ιNet⁻¹ (break l) ≡ nothing`) and reads the prefix's link
link-break-chan : (i : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l : Link} {a : ⊤₀} {M : NetProc}
  → decLink i ph b ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► M
  → (i ≡ l) × (M ≡ Skip)
link-break-chan i ph true {l} step = ⊥-elim (ret-no-ev {P = decLink i ph true} refl step)
link-break-chan i ph false {l} {a} step with fold-react i ph
... | mkReactF V T feq
      with △-Q-ev-inv (MedNO.force-renameMap-react
             {P = ⦀⋆ (map (λ { (d , id) → decCopy i d id (ph d id) }) (linkConfig i))} feq)
             refl refl step
...   | Q′ , qStep , Meq with ⟶₀-ev-inv qStep
...     | _ , lblEq , Q′eq = break-lbl-inj lblEq , trans Meq Q′eq

-- two distinct links cannot both fire `break l` (each pins its own link to `l`)
break-noBoth : (m : MedState) {l : Link} {a : ⊤₀}
    (i j : Link) → i ≢ j → {Mi Mj : NetProc}
  → decLink i (phase m i) (broken m i) ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► Mi
  → decLink j (phase m j) (broken m j) ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► Mj → ⊥
break-noBoth m i j i≢j si sj =
  i≢j (trans (proj₁ (link-break-chan i (phase m i) (broken m i) si))
             (sym (proj₁ (link-break-chan j (phase m j) (broken m j) sj))))

-- flip the `broken` flag of link `i` to `true` (the medium break successor)
broken-upd : (Link → Bool) → Link → (Link → Bool)
broken-upd brk i l with l ≟ i
... | yes _ = true
... | no  _ = brk l

-- KEY↔POSITIONAL bridge for `broken-upd` (mirror `phaseUpd-finUpd`): decoding the
-- `broken`-updated medium at link `j` equals the positional `finUpd` to `Skip`.
-- The shared `j ≟ i` scrutinee auto-reduces `broken-upd`; the fired link decodes
-- to `Skip` (`decLink _ _ true = Skip`), matching `finUpd`'s hit
brokenUpd-finUpd : (m : MedState) (i j : Link)
  → decLink j (phase m j) (broken-upd (broken m) i j)
     ≡ finUpd (λ l → decLink l (phase m l) (broken m l)) i Skip j
brokenUpd-finUpd m i j with j ≟ i
... | yes refl = sym (finUpd-hit (λ l → decLink l (phase m l) (broken m l)) i Skip)
... | no ¬p =
      sym (finUpd-miss (λ l → decLink l (phase m l) (broken m l)) i j Skip (λ q → ¬p (sym q)))

-- reconstruct: the positional `⦀Fin`/`finUpd`-to-`Skip` target is the decode of
-- the `broken`-updated `MedState`
recon-decMed-brk : (m : MedState) (i : Link)
  → ⦀Fin numLinks (finUpd (λ l → decLink l (phase m l) (broken m l)) i Skip)
     ≡ decMed (mkMed (phase m) (broken-upd (broken m) i))
recon-decMed-brk m i =
  sym (⦀Fin-cong numLinks
         (λ l → decLink l (phase m l) (broken-upd (broken m) i l))
         (finUpd (λ l → decLink l (phase m l) (broken m l)) i Skip)
         (λ j → brokenUpd-finUpd m i j))

-- MEDIUM break ev-inversion: a `break l` of `decMed m` is one link's `△` interrupt;
-- the successor is `m` with `broken l := true`.  `⦀Fin-ev-inv` peels the four-link
-- interleave (evBoth refuted by `break-noBoth`); `link-break-chan` reads the fired
-- link's `Skip` residual; `recon-decMed-brk` rebuilds the `MedState`.
medium-break-ev-inv : (m : MedState) (l : Link) {a : ⊤₀} {M : NetProc}
  → decMed m ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► M
  → Σ[ m′ ∈ MedState ] (M ≡ decMed m′)
medium-break-ev-inv m l step
    with ⦀Fin-ev-inv numLinks (λ i → decLink i (phase m i) (broken m i)) (break-noBoth m) step
... | i , Mi , linkStep , Meq with link-break-chan i (phase m i) (broken m i) linkStep
...   | _ , MiSkip =
        mkMed (phase m) (broken-upd (broken m) i) ,
        trans Meq
          (trans (cong (λ z → ⦀Fin numLinks
                    (finUpd (λ k → decLink k (phase m k) (broken m k)) i z)) MiSkip)
                 (recon-decMed-brk m i))

------------------------------------------------------------------------
-- CONCRETE NODES break NON-OFFER (the `reflect-top-ev` `inj₂` for the break class,
-- and the `lift-med-whole-ev` medium-solo viewV-nothing).  A node offers only
-- apiCS/apiBF (∈ apiES, via its driver) and io (input/output, via its renamed
-- peers); `break` is neither — no renamed peer's ι-image contains `break`
-- (`ιX⁻¹ (break l) ≡ nothing`), and every driver phase fires apiCS/apiBF
-- (`decX-apiCSBF`, refuted since `IsApiCSBF (break l)` is uninhabited).
------------------------------------------------------------------------

-- `break l` is not a synchronising api event
break∉apiES : {l₀ : Link} {a : ⊤₀} → ¬ (apiES .mem (⊤₀ , break l₀) a)
break∉apiES ()

-- each renamed bundle peer refuses `break` (`ιX⁻¹ (break l) ≡ nothing`); every
-- driver phase refuses it (`decX-apiCSBF` gives an uninhabited `IsApiCSBF`)
bundleG-no-break : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) (break l₀) a
bundleG-no-break l cl sv csc css bfc bfs ip =
  SStep.⦀-noOffer _ _ (decKAc-noOffer l cl (SN.kac ip) refl)
   (SStep.⦀-noOffer _ _ (decKAs-noOffer l sv (SN.kas ip) refl)
    (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSc-src l cl csc) refl)
     (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSs-src l sv css) refl)
      (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFc-src l cl bfc) refl)
       (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFs-src l sv bfs) refl)
        (SStep.⦀-noOffer _ _ (decTSc-noOffer l cl (SN.tsc ip) refl)
         (SStep.⦀-noOffer _ _ (decTSs-noOffer l sv (SN.tss ip) refl)
          (SStep.⦀-noOffer _ _ (decLNc-noOffer l cl (SN.lnc ip) refl)
           (SStep.⦀-noOffer _ _ (decLNs-noOffer l sv (SN.lns ip) refl)
            (SStep.⦀-noOffer _ _ (LFclientA-noOffer l cl refl)
                                 (LFserverA-noOffer l sv refl)))))))))))

-- the three drivers refuse `break` (they fire only apiCS/apiBF)
decProd-no-break : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {l₀ : Link} {a : ⊤₀} → ¬ IoOffers (decProd l d blk pp) (break l₀) a
decProd-no-break l d blk pp (M , step) with decProd-apiCSBF l d blk pp step
... | ()

decCP-no-break : (l₁ l₂ : Link) (ph : SN.CPPh)
    {l₀ : Link} {a : ⊤₀} → ¬ IoOffers (decCP l₁ l₂ ph) (break l₀) a
decCP-no-break l₁ l₂ ph (M , step) with decCP-apiCSBF l₁ l₂ ph step
... | ()

decConsD-no-break : (l : Link) (cph : SN.ConsDPh)
    {l₀ : Link} {a : ⊤₀} → ¬ IoOffers (decConsD l cph) (break l₀) a
decConsD-no-break l cph (M , step) with decConsD-apiCSBF l cph step
... | ()

-- node-A refuses `break` (two producer legs)
nodeA-no-break : (na : SN.NodeStateA) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (SN.decNodeA na) (break l₀) a
nodeA-no-break na {l₀} {a} = SStep.∥⇘apiES⇙-noOffer {X = ⊤₀} {e = break l₀} {a = a} _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-break linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
    (bundleG-no-break linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)))
  (SStep.⦀-noOffer _ _
    (decProd-no-break linkAB hi b1 (SN.NodeStateA.prod-AB na))
    (decProd-no-break linkAC hi b1 (SN.NodeStateA.prod-AC na)))

-- node-B refuses `break` (consume-AB / produce-BD relay)
nodeB-no-break : (nb : SN.NodeStateB) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (decNodeB nb) (break l₀) a
nodeB-no-break nb {l₀} {a} = SStep.∥⇘apiES⇙-noOffer {X = ⊤₀} {e = break l₀} {a = a} _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-break linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
    (bundleG-no-break linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)))
  (decCP-no-break linkAB linkBD (SN.NodeStateB.cp-B nb))

-- node-C refuses `break` (consume-AC / produce-CD relay)
nodeC-no-break : (nc : SN.NodeStateC) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (decNodeC nc) (break l₀) a
nodeC-no-break nc {l₀} {a} = SStep.∥⇘apiES⇙-noOffer {X = ⊤₀} {e = break l₀} {a = a} _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-break linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
    (bundleG-no-break linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)))
  (decCP-no-break linkAC linkCD (SN.NodeStateC.cp-C nc))

-- node-D refuses `break` (two consumer legs)
nodeD-no-break : (nd : SN.NodeStateD) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (decNodeD nd) (break l₀) a
nodeD-no-break nd {l₀} {a} = SStep.∥⇘apiES⇙-noOffer {X = ⊤₀} {e = break l₀} {a = a} _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-break linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
    (bundleG-no-break linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)))
  (SStep.⦀-noOffer _ _
    (decConsD-no-break linkBD (SN.NodeStateD.cons-BD nd))
    (decConsD-no-break linkCD (SN.NodeStateD.cons-CD nd)))

-- the whole concrete nodes interleave refuses `break` (the `reflect-top-ev` `inj₂`)
nodes-no-break : (s : SysState) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (SStep.nodesOf s) (break l₀) a
nodes-no-break s =
  SStep.⦀-noOffer _ _ (nodeA-no-break (nA s))
    (SStep.⦀-noOffer _ _ (nodeB-no-break (nB s))
      (SStep.⦀-noOffer _ _ (nodeC-no-break (nC s)) (nodeD-no-break (nD s))))


------------------------------------------------------------------------
-- ABSTRACT-SIDE FINGERPRINTS + PAIRWISE NON-OFFERS (the `astep0` abstract 4-node
-- `⦀-ev-L/R` lift).  The abstract nodes `absNodeX` share the SAME drivers as the
-- concrete `decNodeX` (only the bundle side differs — `absBundleG` vs `bundleG`),
-- and the fingerprint reads off the DRIVER step (via `reflect-node-api`), so each
-- abstract fingerprint/non-offer is a VERBATIM duplicate of its concrete twin
-- with `SN.decNodeX`/`SN.bundleA`→`absNodeX`/`absBundleG`.  The FULL pairwise
-- matrix (each node idle when any other fires) is needed here because the
-- abstract lift touches every idle sibling, not just the contiguous right-group.
------------------------------------------------------------------------

-- abstract node-A fingerprint (producer on AB / AC)
absNodeA-fp : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► A′
  → ApiIsProd e × (ApiHasLink linkAB e ⊎ ApiHasLink linkAC e)
absNodeA-fp na mem step
  with SStep.reflect-node-api
         (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi b1 (SN.NodeStateA.prod-AC na))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sAB = decProd-ev-prod linkAB hi b1 (SN.NodeStateA.prod-AB na) sAB , inj₁ (decProd-ev-link linkAB hi b1 (SN.NodeStateA.prod-AB na) sAB)
... | PEA.evR _ sAC = decProd-ev-prod linkAC hi b1 (SN.NodeStateA.prod-AC na) sAC , inj₂ (decProd-ev-link linkAC hi b1 (SN.NodeStateA.prod-AC na) sAC)
... | PEA.evBoth _ sAB sAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (decProd-ev-link linkAB hi b1 (SN.NodeStateA.prod-AB na) sAB)
                     (decProd-ev-link linkAC hi b1 (SN.NodeStateA.prod-AC na) sAC)))

-- abstract node-D fingerprint (consumer on BD / CD)
absNodeD-fp : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► A′
  → ApiIsCons e × (ApiHasLink linkBD e ⊎ ApiHasLink linkCD e)
absNodeD-fp nd mem step
  with SStep.reflect-node-api
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (decConsD linkBD (SN.NodeStateD.cons-BD nd)) (decConsD linkCD (SN.NodeStateD.cons-CD nd)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sBD = decConsD-ev-cons linkBD (SN.NodeStateD.cons-BD nd) sBD , inj₁ (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sBD)
... | PEA.evR _ sCD = decConsD-ev-cons linkCD (SN.NodeStateD.cons-CD nd) sCD , inj₂ (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sCD)
... | PEA.evBoth _ sBD sCD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sBD)
                     (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sCD)))

-- abstract node-B fingerprint (consumer on AB or producer on BD)
absNodeB-fp : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► A′
  → (ApiIsCons e × ApiHasLink linkAB e) ⊎ (ApiIsProd e × ApiHasLink linkBD e)
absNodeB-fp nb mem step
  with SStep.reflect-node-api
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl = decCP-ev-linkrole linkAB linkBD (SN.NodeStateB.cp-B nb) dStep

-- abstract node-C fingerprint (consumer on AC or producer on CD)
absNodeC-fp : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► A′
  → (ApiIsCons e × ApiHasLink linkAC e) ⊎ (ApiIsProd e × ApiHasLink linkCD e)
absNodeC-fp nc mem step
  with SStep.reflect-node-api
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl = decCP-ev-linkrole linkAC linkCD (SN.NodeStateC.cp-C nc) dStep

-- pairwise abstract non-offers: a node cannot offer the event the fired node's
-- fingerprint pins (role clash on a shared link, else link disequality)
absNodeB-no-when-A : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ApiIsProd e × (ApiHasLink linkAB e ⊎ ApiHasLink linkAC e)
  → ¬ IoOffers (absNodeB nb) e a
absNodeB-no-when-A nb mem (prodA , linkA) (M , step) with absNodeB-fp nb mem step
... | inj₁ (consB , _) = prod≢cons prodA consB
... | inj₂ (_ , ahlBD) with linkA
...   | inj₁ ahlAB = linkAB≢linkBD (apiLink-inj ahlAB ahlBD)
...   | inj₂ ahlAC = linkAC≢linkBD (apiLink-inj ahlAC ahlBD)

absNodeC-no-when-A : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ApiIsProd e × (ApiHasLink linkAB e ⊎ ApiHasLink linkAC e)
  → ¬ IoOffers (absNodeC nc) e a
absNodeC-no-when-A nc mem (prodA , linkA) (M , step) with absNodeC-fp nc mem step
... | inj₁ (consC , _) = prod≢cons prodA consC
... | inj₂ (_ , ahlCD) with linkA
...   | inj₁ ahlAB = linkAB≢linkCD (apiLink-inj ahlAB ahlCD)
...   | inj₂ ahlAC = linkAC≢linkCD (apiLink-inj ahlAC ahlCD)

absNodeD-no-when-A : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ApiIsProd e × (ApiHasLink linkAB e ⊎ ApiHasLink linkAC e)
  → ¬ IoOffers (absNodeD nd) e a
absNodeD-no-when-A nd mem (prodA , _) (M , step) with absNodeD-fp nd mem step
... | consDd , _ = prod≢cons prodA consDd

absNodeC-no-when-B : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → (ApiIsCons e × ApiHasLink linkAB e) ⊎ (ApiIsProd e × ApiHasLink linkBD e)
  → ¬ IoOffers (absNodeC nc) e a
absNodeC-no-when-B nc mem fpB (M , step) with absNodeC-fp nc mem step | fpB
... | inj₁ (consC , ahlAC) | inj₁ (_ , ahlAB) = linkAB≢linkAC (apiLink-inj ahlAB ahlAC)
... | inj₁ (consC , _)     | inj₂ (prodB , _) = prod≢cons prodB consC
... | inj₂ (prodC , _)     | inj₁ (consB , _) = prod≢cons prodC consB
... | inj₂ (prodC , ahlCD) | inj₂ (_ , ahlBD) = linkBD≢linkCD (apiLink-inj ahlBD ahlCD)

absNodeD-no-when-B : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → (ApiIsCons e × ApiHasLink linkAB e) ⊎ (ApiIsProd e × ApiHasLink linkBD e)
  → ¬ IoOffers (absNodeD nd) e a
absNodeD-no-when-B nd mem fpB (M , step) with absNodeD-fp nd mem step | fpB
... | (_ , inj₁ ahlBD) | inj₁ (_ , ahlAB) = linkAB≢linkBD (apiLink-inj ahlAB ahlBD)
... | (_ , inj₂ ahlCD) | inj₁ (_ , ahlAB) = linkAB≢linkCD (apiLink-inj ahlAB ahlCD)
... | (consDd , _)     | inj₂ (prodB , _) = prod≢cons prodB consDd

absNodeD-no-when-C : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → (ApiIsCons e × ApiHasLink linkAC e) ⊎ (ApiIsProd e × ApiHasLink linkCD e)
  → ¬ IoOffers (absNodeD nd) e a
absNodeD-no-when-C nd mem fpC (M , step) with absNodeD-fp nd mem step | fpC
... | (_ , inj₁ ahlBD) | inj₁ (_ , ahlAC) = linkAC≢linkBD (apiLink-inj ahlAC ahlBD)
... | (_ , inj₂ ahlCD) | inj₁ (_ , ahlAC) = linkAC≢linkCD (apiLink-inj ahlAC ahlCD)
... | (consDd , _)     | inj₂ (prodC , _) = prod≢cons prodC consDd

-- lower-triangle: a node idle when a LATER node (in the nesting) fires
absNodeA-no-when-B : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → (ApiIsCons e × ApiHasLink linkAB e) ⊎ (ApiIsProd e × ApiHasLink linkBD e)
  → ¬ IoOffers (absNodeA na) e a
absNodeA-no-when-B na mem fpB (M , step) with absNodeA-fp na mem step | fpB
... | (prodA , _)      | inj₁ (consB , _) = prod≢cons prodA consB
... | (_ , inj₁ ahlAB) | inj₂ (_ , ahlBD) = linkAB≢linkBD (apiLink-inj ahlAB ahlBD)
... | (_ , inj₂ ahlAC) | inj₂ (_ , ahlBD) = linkAC≢linkBD (apiLink-inj ahlAC ahlBD)

absNodeA-no-when-C : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → (ApiIsCons e × ApiHasLink linkAC e) ⊎ (ApiIsProd e × ApiHasLink linkCD e)
  → ¬ IoOffers (absNodeA na) e a
absNodeA-no-when-C na mem fpC (M , step) with absNodeA-fp na mem step | fpC
... | (prodA , _)      | inj₁ (consC , _) = prod≢cons prodA consC
... | (_ , inj₁ ahlAB) | inj₂ (_ , ahlCD) = linkAB≢linkCD (apiLink-inj ahlAB ahlCD)
... | (_ , inj₂ ahlAC) | inj₂ (_ , ahlCD) = linkAC≢linkCD (apiLink-inj ahlAC ahlCD)

absNodeB-no-when-C : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → (ApiIsCons e × ApiHasLink linkAC e) ⊎ (ApiIsProd e × ApiHasLink linkCD e)
  → ¬ IoOffers (absNodeB nb) e a
absNodeB-no-when-C nb mem fpC (M , step) with absNodeB-fp nb mem step | fpC
... | inj₁ (_ , ahlAB) | inj₁ (_ , ahlAC) = linkAB≢linkAC (apiLink-inj ahlAB ahlAC)
... | inj₁ (consB , _) | inj₂ (prodC , _) = prod≢cons prodC consB
... | inj₂ (prodB , _) | inj₁ (consC , _) = prod≢cons prodB consC
... | inj₂ (_ , ahlBD) | inj₂ (_ , ahlCD) = linkBD≢linkCD (apiLink-inj ahlBD ahlCD)

absNodeA-no-when-D : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ApiIsCons e × (ApiHasLink linkBD e ⊎ ApiHasLink linkCD e)
  → ¬ IoOffers (absNodeA na) e a
absNodeA-no-when-D na mem (consDd , _) (M , step) with absNodeA-fp na mem step
... | (prodA , _) = prod≢cons prodA consDd

absNodeB-no-when-D : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ApiIsCons e × (ApiHasLink linkBD e ⊎ ApiHasLink linkCD e)
  → ¬ IoOffers (absNodeB nb) e a
absNodeB-no-when-D nb mem fpD (M , step) with absNodeB-fp nb mem step | fpD
... | inj₁ (_ , ahlAB) | (_ , inj₁ ahlBD) = linkAB≢linkBD (apiLink-inj ahlAB ahlBD)
... | inj₁ (_ , ahlAB) | (_ , inj₂ ahlCD) = linkAB≢linkCD (apiLink-inj ahlAB ahlCD)
... | inj₂ (prodB , _) | (consDd , _)      = prod≢cons prodB consDd

absNodeC-no-when-D : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ApiIsCons e × (ApiHasLink linkBD e ⊎ ApiHasLink linkCD e)
  → ¬ IoOffers (absNodeC nc) e a
absNodeC-no-when-D nc mem fpD (M , step) with absNodeC-fp nc mem step | fpD
... | inj₁ (_ , ahlAC) | (_ , inj₁ ahlBD) = linkAC≢linkBD (apiLink-inj ahlAC ahlBD)
... | inj₁ (_ , ahlAC) | (_ , inj₂ ahlCD) = linkAC≢linkCD (apiLink-inj ahlAC ahlCD)
... | inj₂ (prodC , _) | (consDd , _)      = prod≢cons prodC consDd

------------------------------------------------------------------------
-- TOP-LEVEL VISIBLE api CO-MOVE (the reflect-half of `oev`'s api class).
-- A visible apiCS/apiBF event of `⟦ s ⟧` is a nodes-solo through the io-gate
-- (the medium never offers api — `medium-api-non-offer`); peel the 4-node `⦀`
-- (`groupA/B-no` + `nodeD-no-when-C` refute the interleave overlap) to the ONE
-- firing node, invert it with `nodeX-ev-api` (target `≡ decNodeX na′` by `refl`),
-- and rebuild `s′` by that single field update — so `M ≡ ⟦ s′ ⟧` is `refl`.  The
-- ABSTRACT side (shared drivers) does the SAME node step lifted up `absNodesOf`
-- by `⦀-ev-L/R` (idle siblings via the abstract pairwise non-offers), then up the
-- whole stack by `lift-nodes-whole-ev` — giving `comove-ev`'s `astep0`.
------------------------------------------------------------------------

-- an apiCS/apiBF event is not in the io-hide alphabet `ioES`
api∉ioES : {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} → IsApiCSBF e → ¬ ioES .mem (X , e) a
api∉ioES aicCS ()
api∉ioES aicBF ()
api∉ioES aicDone ()

-- peel the 4-node interleave to the firing node + rebuild `s′` (single field
-- update) + the abstract nodes step (`absNodesOf s ─►absNodesOf s′`)
top-nodes : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {N₁ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → SStep.nodesOf s ─[ ev (evl (evLabel X e a)) ]─► N₁
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (N₁ ≡ SStep.nodesOf s′) × (SStep.absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► SStep.absNodesOf s′)
top-nodes s aic mem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (SN.decNodeA (nA s)) (decNodeB (nB s) ⦀ (decNodeC (nC s) ⦀ decNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (groupA-no (nA s) (nB s) (nC s) (nD s) mem sA (_ , sRest))
... | PEA.evL _ sA with nodeA-ev-api (nA s) mem sA
...   | naEv na′ refl absStepA =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl , refl ,
        SStep.⦀-ev-L (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))
          absStepA
          (noOffer→viewV _ (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
             (absNodeB-no-when-A (nB s) mem fpA)
             (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
                (absNodeC-no-when-A (nC s) mem fpA) (absNodeD-no-when-A (nD s) mem fpA))))
  where fpA = absNodeA-fp (nA s) mem absStepA
top-nodes s aic mem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (decNodeB (nB s)) (decNodeC (nC s) ⦀ decNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (groupB-no (nB s) (nC s) (nD s) mem sB (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-api (nB s) mem sB
...   | nbEv nb′ refl absStepB =
        mkSys (med s) (nA s) nb′ (nC s) (nD s) , refl , refl ,
        SStep.⦀-ev-R (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))
          (SStep.⦀-ev-L (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
             absStepB
             (noOffer→viewV _ (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
                (absNodeC-no-when-B (nC s) mem fpB) (absNodeD-no-when-B (nD s) mem fpB))))
          (noOffer→viewV _ (absNodeA-no-when-B (nA s) mem fpB))
  where fpB = absNodeB-fp (nB s) mem absStepB
top-nodes s aic mem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decNodeC (nC s)) (decNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (nodeD-no-when-C (nD s) mem (nodeC-fp (nC s) mem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-api (nC s) mem sC
...   | ncEv nc′ refl absStepC =
        mkSys (med s) (nA s) (nB s) nc′ (nD s) , refl , refl ,
        SStep.⦀-ev-R (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))
          (SStep.⦀-ev-R (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
             (SStep.⦀-ev-L (absNodeC (nC s)) (absNodeD (nD s))
                absStepC
                (noOffer→viewV _ (absNodeD-no-when-C (nD s) mem fpC)))
             (noOffer→viewV _ (absNodeB-no-when-C (nB s) mem fpC)))
          (noOffer→viewV _ (absNodeA-no-when-C (nA s) mem fpC))
  where fpC = absNodeC-fp (nC s) mem absStepC
top-nodes s aic mem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-api (nD s) mem sD
... | ndEv nd′ refl absStepD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl , refl ,
        SStep.⦀-ev-R (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))
          (SStep.⦀-ev-R (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
             (SStep.⦀-ev-R (absNodeC (nC s)) (absNodeD (nD s))
                absStepD
                (noOffer→viewV _ (absNodeC-no-when-D (nC s) mem fpD)))
             (noOffer→viewV _ (absNodeB-no-when-D (nB s) mem fpD)))
          (noOffer→viewV _ (absNodeA-no-when-D (nA s) mem fpD))
  where fpD = absNodeD-fp (nD s) mem absStepD

-- the top-level api co-move: reflect `⟦ s ⟧`'s visible api event to a nodes solo
-- (medium refuted by `medium-api-non-offer`), delegate the nodes peel to
-- `top-nodes`, and lift the abstract nodes step to the whole `absDec` stack.
-- Returns `s′`, `M ≡ ⟦ s′ ⟧` (`refl`), and the abstract whole-system step
-- (`comove-ev`'s `astep0`).
top-api-comove : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → ⟦ s ⟧ ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (M ≡ ⟦ s′ ⟧) × (SStep.absDec s ─[ ev (evl (evLabel X e a)) ]─► SStep.absDec s′)
top-api-comove s {X} {e} {a} aic mem step
  with SStep.reflect-top-ev (decMed (med s)) (SStep.nodesOf s)
         (inj₁ (medium-api-non-offer (med s) aic)) step
... | SStep.medEv M₁ medStep _ = ⊥-elim (medium-api-non-offer (med s) aic (M₁ , medStep))
... | SStep.nodesEv N₁ nodesStep refl with top-nodes s aic mem nodesStep
...   | s′ , medEq , nodesEq , absNodesStep =
        s′ ,
        cong₂ (λ mm nn → (decMed mm ∥⇘ ioES ⇙ nn) ∖ ioES) medEq nodesEq ,
        subst (λ mm → SStep.absDec s ─[ ev (evl (evLabel X e a)) ]─► ((decMed mm ∥⇘ ioES ⇙ SStep.absNodesOf s′) ∖ ioES))
          medEq
          (SStep.lift-nodes-whole-ev (decMed (med s)) (SStep.absNodesOf s)
            (api∉ioES {X} {e} {a} aic) absNodesStep
            (noOffer→viewV _ (medium-api-non-offer (med s) aic)))

------------------------------------------------------------------------
-- ABSTRACT-SIDE nodes break NON-OFFER (`top-break-comove`'s abstract operand).
-- The abstract nodes `absNodeX` share the SAME drivers (`decProd`/`decCP`/
-- `decConsD` — the committed `decX-no-break` reused verbatim) but a `tableSpec`
-- bundle (`absBundleG`, 8 spec peers: KA/CS/BF/TS ×{cl,sv}, no LN/LF).  Every
-- spec peer refuses `break`: its offer map is `tGo ∘ nxt`, and `break` has NO
-- table edge (`*Cnxt/*Snxt-break ≡ nothing` at every abstract position) — a
-- terminal (`isFin`) position offers nothing at all.
------------------------------------------------------------------------

-- csCnxt has no CS-client edge for a `break` event, at every abstract position
csCnxt-break : (l : Link) (d : Dir) (q : NS.CScPos) {l₀ : Link} {a : ⊤₀}
  → NS.csCnxt l d q (⊤₀ , break l₀) a ≡ nothing
csCnxt-break l d NS.ccIdle    = refl
csCnxt-break l d NS.ccWreq    = refl
csCnxt-break l d NS.ccAwait   = refl
csCnxt-break l d (NS.ccWfi _) = refl
csCnxt-break l d NS.ccInt     = refl
csCnxt-break l d NS.ccWdone   = refl
csCnxt-break l d NS.ccMust    = refl
csCnxt-break l d (NS.ccArf _) = refl
csCnxt-break l d (NS.ccArb _) = refl
csCnxt-break l d (NS.ccAif _) = refl
csCnxt-break l d (NS.ccAin _) = refl
csCnxt-break l d NS.ccTerm    = refl

-- csSnxt has no CS-server edge for a `break` event, at every abstract position
csSnxt-break : (l : Link) (d : Dir) (q : NS.CSsPos) {l₀ : Link} {a : ⊤₀}
  → NS.csSnxt l d q (⊤₀ , break l₀) a ≡ nothing
csSnxt-break l d NS.csIdle     = refl
csSnxt-break l d NS.csAreq     = refl
csSnxt-break l d NS.csCanAwait = refl
csSnxt-break l d (NS.csAfi _)  = refl
csSnxt-break l d NS.csInt      = refl
csSnxt-break l d NS.csDdone    = refl
csSnxt-break l d NS.csMust     = refl
csSnxt-break l d (NS.csWrf _)  = refl
csSnxt-break l d (NS.csWrb _)  = refl
csSnxt-break l d NS.csWar      = refl
csSnxt-break l d (NS.csWif _)  = refl
csSnxt-break l d (NS.csWin _)  = refl
csSnxt-break l d NS.csTerm     = refl

-- bfCnxt has no BF-client edge for a `break` event, at every abstract position
bfCnxt-break : (l : Link) (d : Dir) (q : NS.BFcPos) {l₀ : Link} {a : ⊤₀}
  → NS.bfCnxt l d q (⊤₀ , break l₀) a ≡ nothing
bfCnxt-break l d NS.bcIdle     = refl
bfCnxt-break l d (NS.bcWrr _)  = refl
bfCnxt-break l d NS.bcBusy     = refl
bfCnxt-break l d NS.bcWcd      = refl
bfCnxt-break l d NS.bcStream   = refl
bfCnxt-break l d (NS.bcAblk _) = refl
bfCnxt-break l d NS.bcTerm     = refl

-- bfSnxt has no BF-server edge for a `break` event, at every abstract position
bfSnxt-break : (l : Link) (d : Dir) (q : NS.BFsPos) {l₀ : Link} {a : ⊤₀}
  → NS.bfSnxt l d q (⊤₀ , break l₀) a ≡ nothing
bfSnxt-break l d NS.bsIdle     = refl
bfSnxt-break l d (NS.bsAreq _) = refl
bfSnxt-break l d NS.bsBusy     = refl
bfSnxt-break l d NS.bsDdone    = refl
bfSnxt-break l d NS.bsWsb      = refl
bfSnxt-break l d NS.bsStream   = refl
bfSnxt-break l d NS.bsWnb      = refl
bfSnxt-break l d (NS.bsWblk _) = refl
bfSnxt-break l d NS.bsWbd      = refl
bfSnxt-break l d NS.bsTerm     = refl

-- abstract CS-client peer refuses `break` (terminal ⇒ ret; else no csCnxt edge)
absCSc-no-break : (l : Link) (d : Dir) (q : SN.CScPos) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (SStep.absCSc l d q) (break l₀) a
absCSc-no-break l d q {l₀} {a} with NS.csCfin (SStep.coarsenCSc q) in fEq
... | true  = viewV→noOffer (SStep.absCSc l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (SStep.coarsenCSc q) {e = break l₀} {a = a} fEq)
... | false = viewV→noOffer (SStep.absCSc l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (SStep.coarsenCSc q) {e = break l₀} {a = a} fEq
                   (csCnxt-break l d (SStep.coarsenCSc q) {l₀} {a}))

-- abstract CS-server peer refuses `break`
absCSs-no-break : (l : Link) (d : Dir) (q : SN.CSsPos) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (SStep.absCSs l d q) (break l₀) a
absCSs-no-break l d q {l₀} {a} with NS.csSfin (SStep.coarsenCSs q) in fEq
... | true  = viewV→noOffer (SStep.absCSs l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (SStep.coarsenCSs q) {e = break l₀} {a = a} fEq)
... | false = viewV→noOffer (SStep.absCSs l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (SStep.coarsenCSs q) {e = break l₀} {a = a} fEq
                   (csSnxt-break l d (SStep.coarsenCSs q) {l₀} {a}))

-- abstract BF-client peer refuses `break`
absBFc-no-break : (l : Link) (d : Dir) (q : SN.BFcPos) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (SStep.absBFc l d q) (break l₀) a
absBFc-no-break l d q {l₀} {a} with NS.bfCfin (SStep.coarsenBFc q) in fEq
... | true  = viewV→noOffer (SStep.absBFc l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (SStep.coarsenBFc q) {e = break l₀} {a = a} fEq)
... | false = viewV→noOffer (SStep.absBFc l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (SStep.coarsenBFc q) {e = break l₀} {a = a} fEq
                   (bfCnxt-break l d (SStep.coarsenBFc q) {l₀} {a}))

-- abstract BF-server peer refuses `break`
absBFs-no-break : (l : Link) (d : Dir) (q : SN.BFsPos) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (SStep.absBFs l d q) (break l₀) a
absBFs-no-break l d q {l₀} {a} with NS.bfSfin (SStep.coarsenBFs q) in fEq
... | true  = viewV→noOffer (SStep.absBFs l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (SStep.coarsenBFs q) {e = break l₀} {a = a} fEq)
... | false = viewV→noOffer (SStep.absBFs l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (SStep.coarsenBFs q) {e = break l₀} {a = a} fEq
                   (bfSnxt-break l d (SStep.coarsenBFs q) {l₀} {a}))

-- fixed KA-client spec refuses `break` (kcClient non-terminal, no kaCnxt edge)
kaClientSpec-break : (l : Link) (d : Dir) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (NS.kaClientSpec l d) (break l₀) a
kaClientSpec-break l d {l₀} {a} = viewV→noOffer (NS.kaClientSpec l d) {e = break l₀} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
     NS.kcClient {e = break l₀} {a = a} refl refl)

-- fixed KA-server spec refuses `break`
kaServerSpec-break : (l : Link) (d : Dir) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (NS.kaServerSpec l d) (break l₀) a
kaServerSpec-break l d {l₀} {a} = viewV→noOffer (NS.kaServerSpec l d) {e = break l₀} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
     NS.ksClient {e = break l₀} {a = a} refl refl)

-- fixed TS-client spec refuses `break`
tsClientSpec-break : (l : Link) (d : Dir) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (NS.tsClientSpec l d) (break l₀) a
tsClientSpec-break l d {l₀} {a} = viewV→noOffer (NS.tsClientSpec l d) {e = break l₀} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
     NS.tcInit {e = break l₀} {a = a} refl refl)

-- fixed TS-server spec refuses `break`
tsServerSpec-break : (l : Link) (d : Dir) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (NS.tsServerSpec l d) (break l₀) a
tsServerSpec-break l d {l₀} {a} = viewV→noOffer (NS.tsServerSpec l d) {e = break l₀} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
     NS.tsInit {e = break l₀} {a = a} refl refl)

-- the whole 8-peer abstract bundle refuses `break` (all spec peers refuse it)
-- TS-client break next-table refl at the CONCRETE tracked positions (coarsenTSc
-- never yields `tcAri`, whose BlockingStyle enum would block reduction)
tsCnxt-break-c : (l : Link) (d : Dir) (q : SN.TScPos) {l₀ : Link} {a : ⊤₀}
  → NS.tsCnxt l d (SStep.coarsenTSc q) (⊤₀ , break l₀) a ≡ nothing
tsCnxt-break-c l d (SN.tcHead TS.stInit)             = refl
tsCnxt-break-c l d (SN.tcHead TS.stIdle)             = refl
tsCnxt-break-c l d (SN.tcHead TS.stTxIdsBlocking)    = refl
tsCnxt-break-c l d (SN.tcHead TS.stTxIdsNonBlocking) = refl
tsCnxt-break-c l d (SN.tcHead TS.stTxs)              = refl
tsCnxt-break-c l d (SN.tcHead TS.stDone)             = refl
tsCnxt-break-c l d (SN.tcSil TS.stInit)              = refl
tsCnxt-break-c l d (SN.tcSil TS.stIdle)              = refl
tsCnxt-break-c l d (SN.tcSil TS.stTxIdsBlocking)     = refl
tsCnxt-break-c l d (SN.tcSil TS.stTxIdsNonBlocking)  = refl
tsCnxt-break-c l d (SN.tcSil TS.stTxs)               = refl
tsCnxt-break-c l d (SN.tcSil TS.stDone)              = refl

-- TS-server break next-table refl at the CONCRETE tracked positions
tsSnxt-break-c : (l : Link) (d : Dir) (q : SN.TSsPos) {l₀ : Link} {a : ⊤₀}
  → NS.tsSnxt l d (SStep.coarsenTSs q) (⊤₀ , break l₀) a ≡ nothing
tsSnxt-break-c l d (SN.tsHead TS.stInit)             = refl
tsSnxt-break-c l d (SN.tsHead TS.stIdle)             = refl
tsSnxt-break-c l d (SN.tsHead TS.stTxIdsBlocking)    = refl
tsSnxt-break-c l d (SN.tsHead TS.stTxIdsNonBlocking) = refl
tsSnxt-break-c l d (SN.tsHead TS.stTxs)              = refl
tsSnxt-break-c l d (SN.tsHead TS.stDone)             = refl
tsSnxt-break-c l d (SN.tsSil TS.stInit)              = refl
tsSnxt-break-c l d (SN.tsSil TS.stIdle)              = refl
tsSnxt-break-c l d (SN.tsSil TS.stTxIdsBlocking)     = refl
tsSnxt-break-c l d (SN.tsSil TS.stTxIdsNonBlocking)  = refl
tsSnxt-break-c l d (SN.tsSil TS.stTxs)               = refl
tsSnxt-break-c l d (SN.tsSil TS.stDone)              = refl

-- abstract TS client refuses `break` at any tracked position (via concrete coarsen)
absTSc-no-break : (l : Link) (d : Dir) (q : SN.TScPos) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (SStep.absTSc l d q) (break l₀) a
absTSc-no-break l d q {l₀} {a} with NS.tsCfin (SStep.coarsenTSc q) in fEq
... | true  = viewV→noOffer (SStep.absTSc l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (SStep.coarsenTSc q) {e = break l₀} {a = a} fEq)
... | false = viewV→noOffer (SStep.absTSc l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (SStep.coarsenTSc q) {e = break l₀} {a = a} fEq
                   (tsCnxt-break-c l d q {l₀} {a}))

absTSs-no-break : (l : Link) (d : Dir) (q : SN.TSsPos) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (SStep.absTSs l d q) (break l₀) a
absTSs-no-break l d q {l₀} {a} with NS.tsSfin (SStep.coarsenTSs q) in fEq
... | true  = viewV→noOffer (SStep.absTSs l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (SStep.coarsenTSs q) {e = break l₀} {a = a} fEq)
... | false = viewV→noOffer (SStep.absTSs l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (SStep.coarsenTSs q) {e = break l₀} {a = a} fEq
                   (tsSnxt-break-c l d q {l₀} {a}))

-- KA-client break next-table refl at the CONCRETE tracked positions (via coarsen)
kaCnxt-break-c : (l : Link) (d : Dir) (q : SN.KAcPos) {l₀ : Link} {a : ⊤₀}
  → NS.kaCnxt l d (SStep.coarsenKAc q) (⊤₀ , break l₀) a ≡ nothing
kaCnxt-break-c l d (SN.kcHead KA.stClient)     = refl
kaCnxt-break-c l d (SN.kcHead (KA.stServer c)) = refl
kaCnxt-break-c l d (SN.kcHead KA.stDone)       = refl
kaCnxt-break-c l d (SN.kcSil KA.stClient)      = refl
kaCnxt-break-c l d (SN.kcSil (KA.stServer c))  = refl
kaCnxt-break-c l d (SN.kcSil KA.stDone)        = refl

-- KA-server break next-table refl at the CONCRETE tracked positions
kaSnxt-break-c : (l : Link) (d : Dir) (q : SN.KAsPos) {l₀ : Link} {a : ⊤₀}
  → NS.kaSnxt l d (SStep.coarsenKAs q) (⊤₀ , break l₀) a ≡ nothing
kaSnxt-break-c l d (SN.ksHead KA.stClient)     = refl
kaSnxt-break-c l d (SN.ksHead (KA.stServer c)) = refl
kaSnxt-break-c l d (SN.ksHead KA.stDone)       = refl
kaSnxt-break-c l d (SN.ksSil KA.stClient)      = refl
kaSnxt-break-c l d (SN.ksSil (KA.stServer c))  = refl
kaSnxt-break-c l d (SN.ksSil KA.stDone)        = refl

-- abstract KA client refuses `break` at any tracked position (via concrete coarsen)
absKAc-no-break : (l : Link) (d : Dir) (q : SN.KAcPos) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (SStep.absKAc l d q) (break l₀) a
absKAc-no-break l d q {l₀} {a} with NS.kaCfin (SStep.coarsenKAc q) in fEq
... | true  = viewV→noOffer (SStep.absKAc l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (SStep.coarsenKAc q) {e = break l₀} {a = a} fEq)
... | false = viewV→noOffer (SStep.absKAc l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (SStep.coarsenKAc q) {e = break l₀} {a = a} fEq
                   (kaCnxt-break-c l d q {l₀} {a}))

absKAs-no-break : (l : Link) (d : Dir) (q : SN.KAsPos) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (SStep.absKAs l d q) (break l₀) a
absKAs-no-break l d q {l₀} {a} with NS.kaSfin (SStep.coarsenKAs q) in fEq
... | true  = viewV→noOffer (SStep.absKAs l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (SStep.coarsenKAs q) {e = break l₀} {a = a} fEq)
... | false = viewV→noOffer (SStep.absKAs l d q) {e = break l₀} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (SStep.coarsenKAs q) {e = break l₀} {a = a} fEq
                   (kaSnxt-break-c l d q {l₀} {a}))

absBundleG-no-break : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (absBundleG l cl sv csc css bfc bfs ip) (break l₀) a
absBundleG-no-break l cl sv csc css bfc bfs ip =
  SStep.⦀-noOffer _ _ (absKAc-no-break l cl (SN.kac ip))
   (SStep.⦀-noOffer _ _ (absKAs-no-break l sv (SN.kas ip))
    (SStep.⦀-noOffer _ _ (absCSc-no-break l cl csc)
     (SStep.⦀-noOffer _ _ (absCSs-no-break l sv css)
      (SStep.⦀-noOffer _ _ (absBFc-no-break l cl bfc)
       (SStep.⦀-noOffer _ _ (absBFs-no-break l sv bfs)
        (SStep.⦀-noOffer _ _ (absTSc-no-break l cl (SN.tsc ip))
                             (absTSs-no-break l sv (SN.tss ip))))))))

-- abstract node-A refuses `break` (two producer legs; drivers shared)
absNodeA-no-break : (na : SN.NodeStateA) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (absNodeA na) (break l₀) a
absNodeA-no-break na {l₀} {a} = SStep.∥⇘apiES⇙-noOffer {X = ⊤₀} {e = break l₀} {a = a} _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (absBundleG-no-break linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
    (absBundleG-no-break linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)))
  (SStep.⦀-noOffer _ _
    (decProd-no-break linkAB hi b1 (SN.NodeStateA.prod-AB na))
    (decProd-no-break linkAC hi b1 (SN.NodeStateA.prod-AC na)))

-- abstract node-B refuses `break` (consume-AB / produce-BD relay)
absNodeB-no-break : (nb : SN.NodeStateB) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (absNodeB nb) (break l₀) a
absNodeB-no-break nb {l₀} {a} = SStep.∥⇘apiES⇙-noOffer {X = ⊤₀} {e = break l₀} {a = a} _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (absBundleG-no-break linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
    (absBundleG-no-break linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)))
  (decCP-no-break linkAB linkBD (SN.NodeStateB.cp-B nb))

-- abstract node-C refuses `break` (consume-AC / produce-CD relay)
absNodeC-no-break : (nc : SN.NodeStateC) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (absNodeC nc) (break l₀) a
absNodeC-no-break nc {l₀} {a} = SStep.∥⇘apiES⇙-noOffer {X = ⊤₀} {e = break l₀} {a = a} _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (absBundleG-no-break linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
    (absBundleG-no-break linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)))
  (decCP-no-break linkAC linkCD (SN.NodeStateC.cp-C nc))

-- abstract node-D refuses `break` (two consumer legs)
absNodeD-no-break : (nd : SN.NodeStateD) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (absNodeD nd) (break l₀) a
absNodeD-no-break nd {l₀} {a} = SStep.∥⇘apiES⇙-noOffer {X = ⊤₀} {e = break l₀} {a = a} _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (absBundleG-no-break linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
    (absBundleG-no-break linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)))
  (SStep.⦀-noOffer _ _
    (decConsD-no-break linkBD (SN.NodeStateD.cons-BD nd))
    (decConsD-no-break linkCD (SN.NodeStateD.cons-CD nd)))

-- the whole abstract nodes interleave refuses `break` (the `top-break-comove`
-- abstract operand of `lift-med-whole-ev`)
absnodes-no-break : (s : SysState) {l₀ : Link} {a : ⊤₀}
  → ¬ IoOffers (SStep.absNodesOf s) (break l₀) a
absnodes-no-break s =
  SStep.⦀-noOffer _ _ (absNodeA-no-break (nA s))
    (SStep.⦀-noOffer _ _ (absNodeB-no-break (nB s))
      (SStep.⦀-noOffer _ _ (absNodeC-no-break (nC s)) (absNodeD-no-break (nD s))))

------------------------------------------------------------------------
-- TOP-LEVEL VISIBLE break CO-MOVE (the reflect-half of `oev`'s break class).
-- A visible `break l` event of `⟦ s ⟧` is a MEDIUM solo through the io-gate
-- (the nodes never offer break — `nodes-no-break`); `reflect-top-ev` (with
-- `inj₂ nodes-no-break`) forces the medium side, `medium-break-ev-inv` gives
-- the `broken`-flipped successor medium `m′`, and `s′` is `s` with `med := m′`.
-- The ABSTRACT side SHARES the medium, so it does the IDENTICAL break step
-- (`lift-med-whole-ev` at the abstract nodes operand, which also refuse break).
------------------------------------------------------------------------

-- `break l` is not in the io-hide alphabet `ioES` (ioSet = input/output only)
break∉ioES : {l₀ : Link} {a : ⊤₀} → ¬ ioES .mem (⊤₀ , break l₀) a
break∉ioES ()

-- the top-level break co-move: reflect `⟦ s ⟧`'s visible break to a medium solo
-- (nodes refuted by `nodes-no-break`), invert the medium with
-- `medium-break-ev-inv`, rebuild `s′` by the single `med` field update, and lift
-- the SHARED medium break step to the abstract stack (`comove-ev`'s `astep0`).
top-break-comove : (s : SysState) (l : Link) {a : ⊤₀} {M : NetProc}
  → ⟦ s ⟧ ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► M
  → Σ[ s′ ∈ SysState ] (M ≡ ⟦ s′ ⟧)
      × (SStep.absDec s ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► SStep.absDec s′)
top-break-comove s l {a} step
  with SStep.reflect-top-ev (decMed (med s)) (SStep.nodesOf s)
         (inj₂ (nodes-no-break s)) step
... | SStep.nodesEv N₁ nodesStep _ = ⊥-elim (nodes-no-break s (N₁ , nodesStep))
... | SStep.medEv M₁ medStep refl with medium-break-ev-inv (med s) l medStep
...   | m′ , refl =
        mkSys m′ (nA s) (nB s) (nC s) (nD s) , refl ,
        SStep.lift-med-whole-ev (decMed (med s)) (SStep.absNodesOf s)
          (break∉ioES {l} {a}) medStep
          (noOffer→viewV _ (absnodes-no-break s))

------------------------------------------------------------------------
-- oev IMPOSSIBLE-EVENT REFUTATIONS (Task D3, `oev` totality).  A visible
-- top step of `⟦ s ⟧` whose label is neither an api event (apiCS/apiBF/done →
-- `top-api-comove`) nor `break` (→ `top-break-comove`) is IMPOSSIBLE: `√`
-- (the io-gated stack never rets), hidden io (input/output ∈ ioES), the inert
-- api events (apiKA/apiTS/apiLN/apiLF — undriven, node driver refuses the sync),
-- and the wire messages (sndmsg/…/ack — neither the copy medium nor any peer
-- fires them).  These are the refutation leaves feeding `oev-impl`.
------------------------------------------------------------------------

-- the KA-client renamed peer never rets (its iter-of-pchoice head is a react)
KAclientA-no-ret : (l : Link) (d : Dir) {r : ⊤ {0ℓ}}
  → PTree.force (KAclientA l d) ≡ ret r → ⊥
KAclientA-no-ret l d eq
  with trans (sym eq) (KANO.force-renameMap-react {P = KA.KAclientStClient l d} refl)
... | ()

-- the LN-client renamed peer never rets (frozen iter-of-pchoice head is a react);
-- used as the √-witness now that the KA head is a tracked position (which CAN ret
-- at `kcHead stDone`, so KA is no longer a valid always-non-ret witness)
LNclientA-no-ret : (l : Link) (d : Dir) {r : ⊤ {0ℓ}}
  → PTree.force (LNclientA l d) ≡ ret r → ⊥
LNclientA-no-ret l d eq
  with trans (sym eq) (LNNO.force-renameMap-react {P = LNp.LNclientStClient l d} refl)
... | ()

-- the LF-client renamed peer never rets (frozen iter-of-pchoice head is a react);
-- now the √-witness, since LN's head is a tracked position (CAN ret at lncHead stDone)
-- while LF stays a constant frozen peer until it too is tracked
LFclientA-no-ret : (l : Link) (d : Dir) {r : ⊤ {0ℓ}}
  → PTree.force (LFclientA l d) ≡ ret r → ⊥
LFclientA-no-ret l d eq
  with trans (sym eq) (LFNO.force-renameMap-react {P = LFp.LFclientStClient l d} refl)
... | ()

-- lazy left-/right-operand ret extractors for a `Par` (NO WHNF of the operands —
-- the concrete KA-heavy bundle trees are never forced, keeping the descent cheap)
parL-ret : (A : Op.EventSet) {mg : _} {P Q : NetProc} {x : ⊤ {0ℓ}}
  → PTree.force (Op.Par A mg P Q) ≡ ret x → Σ[ r ∈ ⊤ {0ℓ} ] PTree.force P ≡ ret r
parL-ret A eq = _ , proj₁ (proj₂ (proj₂ (PEA.Par-force-ret-inv A _ eq)))

parR-ret : (A : Op.EventSet) {mg : _} {P Q : NetProc} {x : ⊤ {0ℓ}}
  → PTree.force (Op.Par A mg P Q) ≡ ret x → Σ[ r ∈ ⊤ {0ℓ} ] PTree.force Q ≡ ret r
parR-ret A eq = _ , proj₁ (proj₂ (proj₂ (proj₂ (PEA.Par-force-ret-inv A _ eq))))

-- second half of the link-AB descent: peel BFc/BFs/TSc/TSs/LNc/LNs (parR) to
-- the still-frozen LF client (parL), which never rets (LN is now tracked, so
-- the descent goes one pair deeper to the LF client — still a constant peer).
bAB-tail4-no-ret : (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos) {r : ⊤ {0ℓ}}
  → PTree.force (SN.decBFc linkAB lo bfc ⦀ (SN.decBFs linkAB hi bfs ⦀ (SN.decTSc linkAB lo (SN.tsc ip) ⦀ (SN.decTSs linkAB hi (SN.tss ip) ⦀ (SN.decLNc linkAB lo (SN.lnc ip) ⦀ (SN.decLNs linkAB hi (SN.lns ip) ⦀ (LFclientA linkAB lo ⦀ LFserverA linkAB hi))))))) ≡ ret r → ⊥
bAB-tail4-no-ret bfc bfs ip eq = LFclientA-no-ret linkAB lo lfret
  where
  e1 : PTree.force (SN.decBFs linkAB hi bfs ⦀ (SN.decTSc linkAB lo (SN.tsc ip) ⦀ (SN.decTSs linkAB hi (SN.tss ip) ⦀ (SN.decLNc linkAB lo (SN.lnc ip) ⦀ (SN.decLNs linkAB hi (SN.lns ip) ⦀ (LFclientA linkAB lo ⦀ LFserverA linkAB hi)))))) ≡ ret _
  e1 = proj₂ (parR-ret ∅ESa eq)
  e2 : PTree.force (SN.decTSc linkAB lo (SN.tsc ip) ⦀ (SN.decTSs linkAB hi (SN.tss ip) ⦀ (SN.decLNc linkAB lo (SN.lnc ip) ⦀ (SN.decLNs linkAB hi (SN.lns ip) ⦀ (LFclientA linkAB lo ⦀ LFserverA linkAB hi))))) ≡ ret _
  e2 = proj₂ (parR-ret ∅ESa e1)
  e3 : PTree.force (SN.decTSs linkAB hi (SN.tss ip) ⦀ (SN.decLNc linkAB lo (SN.lnc ip) ⦀ (SN.decLNs linkAB hi (SN.lns ip) ⦀ (LFclientA linkAB lo ⦀ LFserverA linkAB hi)))) ≡ ret _
  e3 = proj₂ (parR-ret ∅ESa e2)
  e4 : PTree.force (SN.decLNc linkAB lo (SN.lnc ip) ⦀ (SN.decLNs linkAB hi (SN.lns ip) ⦀ (LFclientA linkAB lo ⦀ LFserverA linkAB hi))) ≡ ret _
  e4 = proj₂ (parR-ret ∅ESa e3)
  e5 : PTree.force (SN.decLNs linkAB hi (SN.lns ip) ⦀ (LFclientA linkAB lo ⦀ LFserverA linkAB hi)) ≡ ret _
  e5 = proj₂ (parR-ret ∅ESa e4)
  e6 : PTree.force (LFclientA linkAB lo ⦀ LFserverA linkAB hi) ≡ ret _
  e6 = proj₂ (parR-ret ∅ESa e5)
  lfret : PTree.force (LFclientA linkAB lo) ≡ ret _
  lfret = proj₂ (parL-ret ∅ESa {P = LFclientA linkAB lo} {Q = LFserverA linkAB hi} e6)

-- a link-AB bundle never rets: peel the first 4 peers KAc/KAs/CSc/CSs (parR),
-- then hand the concrete BF-onward tail to `bAB-tail4-no-ret`.  Explicit tail
-- types again, for the same direct-unification reason.
bundleA-AB-no-ret : (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos)
    (ip : SN.InertPos) {r : ⊤ {0ℓ}}
  → PTree.force (SN.bundleA linkAB csc css bfc bfs ip) ≡ ret r → ⊥
bundleA-AB-no-ret csc css bfc bfs ip eq = bAB-tail4-no-ret bfc bfs ip f4
  where
  f1 : PTree.force (SN.decKAs linkAB hi (SN.kas ip) ⦀ (SN.decCSc linkAB lo csc
        ⦀ (SN.decCSs linkAB hi css ⦀ (SN.decBFc linkAB lo bfc ⦀ (SN.decBFs linkAB hi bfs
        ⦀ (SN.decTSc linkAB lo (SN.tsc ip) ⦀ (SN.decTSs linkAB hi (SN.tss ip)
        ⦀ (SN.decLNc linkAB lo (SN.lnc ip) ⦀ (SN.decLNs linkAB hi (SN.lns ip)
        ⦀ (LFclientA linkAB lo ⦀ LFserverA linkAB hi)))))))))) ≡ ret _
  f1 = proj₂ (parR-ret ∅ESa eq)
  f2 : PTree.force (SN.decCSc linkAB lo csc ⦀ (SN.decCSs linkAB hi css
        ⦀ (SN.decBFc linkAB lo bfc ⦀ (SN.decBFs linkAB hi bfs
        ⦀ (SN.decTSc linkAB lo (SN.tsc ip) ⦀ (SN.decTSs linkAB hi (SN.tss ip)
        ⦀ (SN.decLNc linkAB lo (SN.lnc ip) ⦀ (SN.decLNs linkAB hi (SN.lns ip)
        ⦀ (LFclientA linkAB lo ⦀ LFserverA linkAB hi))))))))) ≡ ret _
  f2 = proj₂ (parR-ret ∅ESa f1)
  f3 : PTree.force (SN.decCSs linkAB hi css ⦀ (SN.decBFc linkAB lo bfc
        ⦀ (SN.decBFs linkAB hi bfs ⦀ (SN.decTSc linkAB lo (SN.tsc ip)
        ⦀ (SN.decTSs linkAB hi (SN.tss ip) ⦀ (SN.decLNc linkAB lo (SN.lnc ip)
        ⦀ (SN.decLNs linkAB hi (SN.lns ip) ⦀ (LFclientA linkAB lo ⦀ LFserverA linkAB hi)))))))) ≡ ret _
  f3 = proj₂ (parR-ret ∅ESa f2)
  f4 : PTree.force (SN.decBFc linkAB lo bfc ⦀ (SN.decBFs linkAB hi bfs
        ⦀ (SN.decTSc linkAB lo (SN.tsc ip) ⦀ (SN.decTSs linkAB hi (SN.tss ip)
        ⦀ (SN.decLNc linkAB lo (SN.lnc ip) ⦀ (SN.decLNs linkAB hi (SN.lns ip)
        ⦀ (LFclientA linkAB lo ⦀ LFserverA linkAB hi))))))) ≡ ret _
  f4 = proj₂ (parR-ret ∅ESa f3)

-- the √ tick of `⟦ s ⟧` is impossible: it needs `force (inner) ≡ ret`, but the
-- io-gated inner stack never rets (the node-A link-AB bundle never rets) —
-- descended lazily via `parR-ret`/`parL-ret`
oev-no-√ : (s : SysState) {r : ⊤ {0ℓ}} {M : NetProc}
  → ⟦ s ⟧ ─[ ev (√ r) ]─► M → ⊥
oev-no-√ s step with Hide-ev-elim ioES (decMed (med s) ∥⇘ ioES ⇙ SStep.nodesOf s) step
... | he√ feq =
      -- descend nodesOf → nodeA → (bAB⦀bAC) → bAB, then hand the CONCRETE
      -- link-AB bundle to `bundleA-AB-no-ret` (which peels the 8 tracked/driven
      -- peers to the still-frozen LF client — a valid never-ret witness, since the
      -- KA/CS/BF/TS/LN heads are now tracked positions that CAN ret at stDone)
      bundleA-AB-no-ret
        (SN.NodeStateA.csC-AB (nA s)) (SN.NodeStateA.csS-AB (nA s))
        (SN.NodeStateA.bfC-AB (nA s)) (SN.NodeStateA.bfS-AB (nA s))
        (SN.NodeStateA.inert-AB (nA s))
        (proj₂ (parL-ret ∅ESa
          (proj₂ (parL-ret apiES
            (proj₂ (parL-ret ∅ESa
              (proj₂ (parR-ret ioES feq))))))))

-- io refutation: a visible io of `⟦ s ⟧` is impossible (io ∈ ioES is hidden by ∖)
oev-no-io : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a → ⟦ s ⟧ ─[ ev (evl (evLabel X e a)) ]─► M → ⊥
oev-no-io s iomem step
  with Hide-ev-elim ioES (decMed (med s) ∥⇘ ioES ⇙ SStep.nodesOf s) step
... | heV P′ ¬mem _ = ¬mem iomem

-- generic top-level refutation for events offered by neither medium nor nodes
oev-refute : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ¬ IoOffers (decMed (med s)) e a → ¬ IoOffers (SStep.nodesOf s) e a
  → ⟦ s ⟧ ─[ ev (evl (evLabel X e a)) ]─► M → ⊥
oev-refute s mno nno step
  with SStep.reflect-top-ev (decMed (med s)) (SStep.nodesOf s) (inj₁ mno) step
... | SStep.medEv M₁ ms _   = mno (M₁ , ms)
... | SStep.nodesEv N₁ ns _ = nno (N₁ , ns)

-- node-A never offers a non-{apiCS,apiBF,done} api event (its driver refuses the sync)
nodeA-no-nonCSBF : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ¬ IsApiCSBF e → ¬ IoOffers (SN.decNodeA na) e a
nodeA-no-nonCSBF na mem ¬aic (M , step)
  with SStep.reflect-node-api
         (SN.bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ SN.bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi b1 (SN.NodeStateA.prod-AC na))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) dStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sAB    = ¬aic (decProd-apiCSBF linkAB hi b1 (SN.NodeStateA.prod-AB na) sAB)
...   | PEA.evR _ sAC    = ¬aic (decProd-apiCSBF linkAC hi b1 (SN.NodeStateA.prod-AC na) sAC)
...   | PEA.evBoth _ sAB _ = ¬aic (decProd-apiCSBF linkAB hi b1 (SN.NodeStateA.prod-AB na) sAB)

-- node-B never offers a non-CSBF api event (its CP driver refuses the sync)
nodeB-no-nonCSBF : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ¬ IsApiCSBF e → ¬ IoOffers (decNodeB nb) e a
nodeB-no-nonCSBF nb mem ¬aic (M , step)
  with SStep.reflect-node-api
         (bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ bundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl = ¬aic (decCP-apiCSBF linkAB linkBD (SN.NodeStateB.cp-B nb) dStep)

-- node-C never offers a non-CSBF api event
nodeC-no-nonCSBF : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ¬ IsApiCSBF e → ¬ IoOffers (decNodeC nc) e a
nodeC-no-nonCSBF nc mem ¬aic (M , step)
  with SStep.reflect-node-api
         (bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ bundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl = ¬aic (decCP-apiCSBF linkAC linkCD (SN.NodeStateC.cp-C nc) dStep)

-- node-D never offers a non-CSBF api event (two consumer drivers refuse the sync)
nodeD-no-nonCSBF : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ¬ IsApiCSBF e → ¬ IoOffers (decNodeD nd) e a
nodeD-no-nonCSBF nd mem ¬aic (M , step)
  with SStep.reflect-node-api
         (bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ bundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd)) mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (decConsD linkBD (SN.NodeStateD.cons-BD nd)) (decConsD linkCD (SN.NodeStateD.cons-CD nd)) dStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBD    = ¬aic (decConsD-apiCSBF linkBD (SN.NodeStateD.cons-BD nd) sBD)
...   | PEA.evR _ sCD    = ¬aic (decConsD-apiCSBF linkCD (SN.NodeStateD.cons-CD nd) sCD)
...   | PEA.evBoth _ sBD _ = ¬aic (decConsD-apiCSBF linkBD (SN.NodeStateD.cons-BD nd) sBD)

-- the whole nodes interleave never offers a non-CSBF api event
nodes-no-nonCSBF : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ¬ IsApiCSBF e → ¬ IoOffers (SStep.nodesOf s) e a
nodes-no-nonCSBF s mem ¬aic =
  SStep.⦀-noOffer _ _ (nodeA-no-nonCSBF (nA s) mem ¬aic)
    (SStep.⦀-noOffer _ _ (nodeB-no-nonCSBF (nB s) mem ¬aic)
      (SStep.⦀-noOffer _ _ (nodeC-no-nonCSBF (nC s) mem ¬aic) (nodeD-no-nonCSBF (nD s) mem ¬aic)))

-- one breakable link offers no `apiKA` (`ιNet⁻¹ (apiKA …) ≡ nothing`)
decLink-no-apiKA : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {m₀ : _} {a : _}
  → ¬ IoOffers (decLink l ph b) (apiKA l₀ d₀ m₀) a
decLink-no-apiKA l ph true  (M , step) = ret-no-ev {P = decLink l ph true} refl step
decLink-no-apiKA l ph false (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , () , _

-- the medium offers no `apiKA`
medium-no-apiKA : (m : MedState) {l₀ : Link} {d₀ : Dir} {m₀ : _} {a : _}
  → ¬ IoOffers (decMed m) (apiKA l₀ d₀ m₀) a
medium-no-apiKA m =
  ⦀Fin-noOffer numLinks (λ l → decLink l (phase m l) (broken m l))
    (λ l → decLink-no-apiKA l (phase m l) (broken m l))

-- one breakable link offers no `apiTS` (`ιNet⁻¹ (apiTS …) ≡ nothing`)
decLink-no-apiTS : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {m₀ : _} {a : _}
  → ¬ IoOffers (decLink l ph b) (apiTS l₀ d₀ m₀) a
decLink-no-apiTS l ph true  (M , step) = ret-no-ev {P = decLink l ph true} refl step
decLink-no-apiTS l ph false (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , () , _

-- the medium offers no `apiTS`
medium-no-apiTS : (m : MedState) {l₀ : Link} {d₀ : Dir} {m₀ : _} {a : _}
  → ¬ IoOffers (decMed m) (apiTS l₀ d₀ m₀) a
medium-no-apiTS m =
  ⦀Fin-noOffer numLinks (λ l → decLink l (phase m l) (broken m l))
    (λ l → decLink-no-apiTS l (phase m l) (broken m l))

-- one breakable link offers no `apiLN` (`ιNet⁻¹ (apiLN …) ≡ nothing`)
decLink-no-apiLN : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {m₀ : _} {a : _}
  → ¬ IoOffers (decLink l ph b) (apiLN l₀ d₀ m₀) a
decLink-no-apiLN l ph true  (M , step) = ret-no-ev {P = decLink l ph true} refl step
decLink-no-apiLN l ph false (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , () , _

-- the medium offers no `apiLN`
medium-no-apiLN : (m : MedState) {l₀ : Link} {d₀ : Dir} {m₀ : _} {a : _}
  → ¬ IoOffers (decMed m) (apiLN l₀ d₀ m₀) a
medium-no-apiLN m =
  ⦀Fin-noOffer numLinks (λ l → decLink l (phase m l) (broken m l))
    (λ l → decLink-no-apiLN l (phase m l) (broken m l))

-- one breakable link offers no `apiLF` (`ιNet⁻¹ (apiLF …) ≡ nothing`)
decLink-no-apiLF : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {m₀ : _} {a : _}
  → ¬ IoOffers (decLink l ph b) (apiLF l₀ d₀ m₀) a
decLink-no-apiLF l ph true  (M , step) = ret-no-ev {P = decLink l ph true} refl step
decLink-no-apiLF l ph false (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , () , _

-- the medium offers no `apiLF`
medium-no-apiLF : (m : MedState) {l₀ : Link} {d₀ : Dir} {m₀ : _} {a : _}
  → ¬ IoOffers (decMed m) (apiLF l₀ d₀ m₀) a
medium-no-apiLF m =
  ⦀Fin-noOffer numLinks (λ l → decLink l (phase m l) (broken m l))
    (λ l → decLink-no-apiLF l (phase m l) (broken m l))

-- one breakable link offers no `sndmsg` (copy cells fire only input/output)
decLink-no-sndmsg : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decLink l ph b) (sndmsg l₀ d₀ id₀) a
decLink-no-sndmsg l ph true  (M , step) = ret-no-ev {P = decLink l ph true} refl step
decLink-no-sndmsg l ph false (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , iota , srcStep , _ with just-injective iota
...       | refl with fold-key l (λ { (d , id) → decCopy l d id (ph d id) })
                          (λ { (d , id) s → cellChan→L l d id (cell-key l d id (ph d id) s) })
                          (linkConfig l) srcStep
...         | ()

-- the medium offers no `sndmsg`
medium-no-sndmsg : (m : MedState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decMed m) (sndmsg l₀ d₀ id₀) a
medium-no-sndmsg m =
  ⦀Fin-noOffer numLinks (λ l → decLink l (phase m l) (broken m l))
    (λ l → decLink-no-sndmsg l (phase m l) (broken m l))

-- one breakable link offers no `rcvmsg` (copy cells fire only input/output)
decLink-no-rcvmsg : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decLink l ph b) (rcvmsg l₀ d₀ id₀) a
decLink-no-rcvmsg l ph true  (M , step) = ret-no-ev {P = decLink l ph true} refl step
decLink-no-rcvmsg l ph false (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , iota , srcStep , _ with just-injective iota
...       | refl with fold-key l (λ { (d , id) → decCopy l d id (ph d id) })
                          (λ { (d , id) s → cellChan→L l d id (cell-key l d id (ph d id) s) })
                          (linkConfig l) srcStep
...         | ()

-- the medium offers no `rcvmsg`
medium-no-rcvmsg : (m : MedState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decMed m) (rcvmsg l₀ d₀ id₀) a
medium-no-rcvmsg m =
  ⦀Fin-noOffer numLinks (λ l → decLink l (phase m l) (broken m l))
    (λ l → decLink-no-rcvmsg l (phase m l) (broken m l))

-- one breakable link offers no `tx` (copy cells fire only input/output)
decLink-no-tx : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decLink l ph b) (tx l₀ d₀ id₀) a
decLink-no-tx l ph true  (M , step) = ret-no-ev {P = decLink l ph true} refl step
decLink-no-tx l ph false (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , iota , srcStep , _ with just-injective iota
...       | refl with fold-key l (λ { (d , id) → decCopy l d id (ph d id) })
                          (λ { (d , id) s → cellChan→L l d id (cell-key l d id (ph d id) s) })
                          (linkConfig l) srcStep
...         | ()

-- the medium offers no `tx`
medium-no-tx : (m : MedState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decMed m) (tx l₀ d₀ id₀) a
medium-no-tx m =
  ⦀Fin-noOffer numLinks (λ l → decLink l (phase m l) (broken m l))
    (λ l → decLink-no-tx l (phase m l) (broken m l))

-- one breakable link offers no `sndack` (copy cells fire only input/output)
decLink-no-sndack : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decLink l ph b) (sndack l₀ d₀ id₀) a
decLink-no-sndack l ph true  (M , step) = ret-no-ev {P = decLink l ph true} refl step
decLink-no-sndack l ph false (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , iota , srcStep , _ with just-injective iota
...       | refl with fold-key l (λ { (d , id) → decCopy l d id (ph d id) })
                          (λ { (d , id) s → cellChan→L l d id (cell-key l d id (ph d id) s) })
                          (linkConfig l) srcStep
...         | ()

-- the medium offers no `sndack`
medium-no-sndack : (m : MedState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decMed m) (sndack l₀ d₀ id₀) a
medium-no-sndack m =
  ⦀Fin-noOffer numLinks (λ l → decLink l (phase m l) (broken m l))
    (λ l → decLink-no-sndack l (phase m l) (broken m l))

-- one breakable link offers no `rcvack` (copy cells fire only input/output)
decLink-no-rcvack : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decLink l ph b) (rcvack l₀ d₀ id₀) a
decLink-no-rcvack l ph true  (M , step) = ret-no-ev {P = decLink l ph true} refl step
decLink-no-rcvack l ph false (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , iota , srcStep , _ with just-injective iota
...       | refl with fold-key l (λ { (d , id) → decCopy l d id (ph d id) })
                          (λ { (d , id) s → cellChan→L l d id (cell-key l d id (ph d id) s) })
                          (linkConfig l) srcStep
...         | ()

-- the medium offers no `rcvack`
medium-no-rcvack : (m : MedState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decMed m) (rcvack l₀ d₀ id₀) a
medium-no-rcvack m =
  ⦀Fin-noOffer numLinks (λ l → decLink l (phase m l) (broken m l))
    (λ l → decLink-no-rcvack l (phase m l) (broken m l))

-- one breakable link offers no `ack` (copy cells fire only input/output)
decLink-no-ack : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decLink l ph b) (ack l₀ d₀ id₀) a
decLink-no-ack l ph true  (M , step) = ret-no-ev {P = decLink l ph true} refl step
decLink-no-ack l ph false (M , step) with fold-react l ph
... | mkReactF V T feq with △-ev-elim (MedNO.force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
        refl refl step
...   | P′ , leftStep , _ with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , iota , srcStep , _ with just-injective iota
...       | refl with fold-key l (λ { (d , id) → decCopy l d id (ph d id) })
                          (λ { (d , id) s → cellChan→L l d id (cell-key l d id (ph d id) s) })
                          (linkConfig l) srcStep
...         | ()

-- the medium offers no `ack`
medium-no-ack : (m : MedState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decMed m) (ack l₀ d₀ id₀) a
medium-no-ack m =
  ⦀Fin-noOffer numLinks (λ l → decLink l (phase m l) (broken m l))
    (λ l → decLink-no-ack l (phase m l) (broken m l))

-- bundle refuses `sndmsg` (every renamed peer's ι-preimage is nothing)
bundleG-no-sndmsg : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) (sndmsg l₀ d₀ id₀) a
bundleG-no-sndmsg l cl sv csc css bfc bfs ip =
  SStep.⦀-noOffer _ _ (decKAc-noOffer l cl (SN.kac ip) refl)
   (SStep.⦀-noOffer _ _ (decKAs-noOffer l sv (SN.kas ip) refl)
    (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSc-src l cl csc) refl)
     (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSs-src l sv css) refl)
      (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFc-src l cl bfc) refl)
       (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFs-src l sv bfs) refl)
        (SStep.⦀-noOffer _ _ (decTSc-noOffer l cl (SN.tsc ip) refl)
         (SStep.⦀-noOffer _ _ (decTSs-noOffer l sv (SN.tss ip) refl)
          (SStep.⦀-noOffer _ _ (decLNc-noOffer l cl (SN.lnc ip) refl)
           (SStep.⦀-noOffer _ _ (decLNs-noOffer l sv (SN.lns ip) refl)
            (SStep.⦀-noOffer _ _ (LFclientA-noOffer l cl refl)
                                 (LFserverA-noOffer l sv refl)))))))))))

-- the three drivers refuse `sndmsg` (they fire only apiCS/apiBF/done)
decProd-no-sndmsg : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload} → ¬ IoOffers (decProd l d blk pp) (sndmsg l₀ d₀ id₀) a
decProd-no-sndmsg l d blk pp (M , step) with decProd-apiCSBF l d blk pp step
... | ()

decCP-no-sndmsg : (l₁ l₂ : Link) (ph : SN.CPPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload} → ¬ IoOffers (decCP l₁ l₂ ph) (sndmsg l₀ d₀ id₀) a
decCP-no-sndmsg l₁ l₂ ph (M , step) with decCP-apiCSBF l₁ l₂ ph step
... | ()

decConsD-no-sndmsg : (l : Link) (cph : SN.ConsDPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload} → ¬ IoOffers (decConsD l cph) (sndmsg l₀ d₀ id₀) a
decConsD-no-sndmsg l cph (M , step) with decConsD-apiCSBF l cph step
... | ()

-- node-A refuses `sndmsg`
nodeA-no-sndmsg : (na : SN.NodeStateA) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (SN.decNodeA na) (sndmsg l₀ d₀ id₀) a
nodeA-no-sndmsg na = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-sndmsg linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
    (bundleG-no-sndmsg linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)))
  (SStep.⦀-noOffer _ _
    (decProd-no-sndmsg linkAB hi b1 (SN.NodeStateA.prod-AB na))
    (decProd-no-sndmsg linkAC hi b1 (SN.NodeStateA.prod-AC na)))

-- node-B refuses `sndmsg`
nodeB-no-sndmsg : (nb : SN.NodeStateB) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decNodeB nb) (sndmsg l₀ d₀ id₀) a
nodeB-no-sndmsg nb = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-sndmsg linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
    (bundleG-no-sndmsg linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)))
  (decCP-no-sndmsg linkAB linkBD (SN.NodeStateB.cp-B nb))

-- node-C refuses `sndmsg`
nodeC-no-sndmsg : (nc : SN.NodeStateC) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decNodeC nc) (sndmsg l₀ d₀ id₀) a
nodeC-no-sndmsg nc = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-sndmsg linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
    (bundleG-no-sndmsg linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)))
  (decCP-no-sndmsg linkAC linkCD (SN.NodeStateC.cp-C nc))

-- node-D refuses `sndmsg`
nodeD-no-sndmsg : (nd : SN.NodeStateD) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decNodeD nd) (sndmsg l₀ d₀ id₀) a
nodeD-no-sndmsg nd = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-sndmsg linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
    (bundleG-no-sndmsg linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)))
  (SStep.⦀-noOffer _ _
    (decConsD-no-sndmsg linkBD (SN.NodeStateD.cons-BD nd))
    (decConsD-no-sndmsg linkCD (SN.NodeStateD.cons-CD nd)))

-- the whole nodes interleave refuses `sndmsg`
nodes-no-sndmsg : (s : SysState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (SStep.nodesOf s) (sndmsg l₀ d₀ id₀) a
nodes-no-sndmsg s =
  SStep.⦀-noOffer _ _ (nodeA-no-sndmsg (nA s))
    (SStep.⦀-noOffer _ _ (nodeB-no-sndmsg (nB s))
      (SStep.⦀-noOffer _ _ (nodeC-no-sndmsg (nC s)) (nodeD-no-sndmsg (nD s))))

-- bundle refuses `rcvmsg` (every renamed peer's ι-preimage is nothing)
bundleG-no-rcvmsg : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) (rcvmsg l₀ d₀ id₀) a
bundleG-no-rcvmsg l cl sv csc css bfc bfs ip =
  SStep.⦀-noOffer _ _ (decKAc-noOffer l cl (SN.kac ip) refl)
   (SStep.⦀-noOffer _ _ (decKAs-noOffer l sv (SN.kas ip) refl)
    (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSc-src l cl csc) refl)
     (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSs-src l sv css) refl)
      (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFc-src l cl bfc) refl)
       (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFs-src l sv bfs) refl)
        (SStep.⦀-noOffer _ _ (decTSc-noOffer l cl (SN.tsc ip) refl)
         (SStep.⦀-noOffer _ _ (decTSs-noOffer l sv (SN.tss ip) refl)
          (SStep.⦀-noOffer _ _ (decLNc-noOffer l cl (SN.lnc ip) refl)
           (SStep.⦀-noOffer _ _ (decLNs-noOffer l sv (SN.lns ip) refl)
            (SStep.⦀-noOffer _ _ (LFclientA-noOffer l cl refl)
                                 (LFserverA-noOffer l sv refl)))))))))))

-- the three drivers refuse `rcvmsg` (they fire only apiCS/apiBF/done)
decProd-no-rcvmsg : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload} → ¬ IoOffers (decProd l d blk pp) (rcvmsg l₀ d₀ id₀) a
decProd-no-rcvmsg l d blk pp (M , step) with decProd-apiCSBF l d blk pp step
... | ()

decCP-no-rcvmsg : (l₁ l₂ : Link) (ph : SN.CPPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload} → ¬ IoOffers (decCP l₁ l₂ ph) (rcvmsg l₀ d₀ id₀) a
decCP-no-rcvmsg l₁ l₂ ph (M , step) with decCP-apiCSBF l₁ l₂ ph step
... | ()

decConsD-no-rcvmsg : (l : Link) (cph : SN.ConsDPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload} → ¬ IoOffers (decConsD l cph) (rcvmsg l₀ d₀ id₀) a
decConsD-no-rcvmsg l cph (M , step) with decConsD-apiCSBF l cph step
... | ()

-- node-A refuses `rcvmsg`
nodeA-no-rcvmsg : (na : SN.NodeStateA) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (SN.decNodeA na) (rcvmsg l₀ d₀ id₀) a
nodeA-no-rcvmsg na = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-rcvmsg linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
    (bundleG-no-rcvmsg linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)))
  (SStep.⦀-noOffer _ _
    (decProd-no-rcvmsg linkAB hi b1 (SN.NodeStateA.prod-AB na))
    (decProd-no-rcvmsg linkAC hi b1 (SN.NodeStateA.prod-AC na)))

-- node-B refuses `rcvmsg`
nodeB-no-rcvmsg : (nb : SN.NodeStateB) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decNodeB nb) (rcvmsg l₀ d₀ id₀) a
nodeB-no-rcvmsg nb = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-rcvmsg linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
    (bundleG-no-rcvmsg linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)))
  (decCP-no-rcvmsg linkAB linkBD (SN.NodeStateB.cp-B nb))

-- node-C refuses `rcvmsg`
nodeC-no-rcvmsg : (nc : SN.NodeStateC) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decNodeC nc) (rcvmsg l₀ d₀ id₀) a
nodeC-no-rcvmsg nc = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-rcvmsg linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
    (bundleG-no-rcvmsg linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)))
  (decCP-no-rcvmsg linkAC linkCD (SN.NodeStateC.cp-C nc))

-- node-D refuses `rcvmsg`
nodeD-no-rcvmsg : (nd : SN.NodeStateD) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decNodeD nd) (rcvmsg l₀ d₀ id₀) a
nodeD-no-rcvmsg nd = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-rcvmsg linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
    (bundleG-no-rcvmsg linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)))
  (SStep.⦀-noOffer _ _
    (decConsD-no-rcvmsg linkBD (SN.NodeStateD.cons-BD nd))
    (decConsD-no-rcvmsg linkCD (SN.NodeStateD.cons-CD nd)))

-- the whole nodes interleave refuses `rcvmsg`
nodes-no-rcvmsg : (s : SysState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (SStep.nodesOf s) (rcvmsg l₀ d₀ id₀) a
nodes-no-rcvmsg s =
  SStep.⦀-noOffer _ _ (nodeA-no-rcvmsg (nA s))
    (SStep.⦀-noOffer _ _ (nodeB-no-rcvmsg (nB s))
      (SStep.⦀-noOffer _ _ (nodeC-no-rcvmsg (nC s)) (nodeD-no-rcvmsg (nD s))))

-- bundle refuses `tx` (every renamed peer's ι-preimage is nothing)
bundleG-no-tx : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) (tx l₀ d₀ id₀) a
bundleG-no-tx l cl sv csc css bfc bfs ip =
  SStep.⦀-noOffer _ _ (decKAc-noOffer l cl (SN.kac ip) refl)
   (SStep.⦀-noOffer _ _ (decKAs-noOffer l sv (SN.kas ip) refl)
    (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSc-src l cl csc) refl)
     (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSs-src l sv css) refl)
      (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFc-src l cl bfc) refl)
       (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFs-src l sv bfs) refl)
        (SStep.⦀-noOffer _ _ (decTSc-noOffer l cl (SN.tsc ip) refl)
         (SStep.⦀-noOffer _ _ (decTSs-noOffer l sv (SN.tss ip) refl)
          (SStep.⦀-noOffer _ _ (decLNc-noOffer l cl (SN.lnc ip) refl)
           (SStep.⦀-noOffer _ _ (decLNs-noOffer l sv (SN.lns ip) refl)
            (SStep.⦀-noOffer _ _ (LFclientA-noOffer l cl refl)
                                 (LFserverA-noOffer l sv refl)))))))))))

-- the three drivers refuse `tx` (they fire only apiCS/apiBF/done)
decProd-no-tx : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload} → ¬ IoOffers (decProd l d blk pp) (tx l₀ d₀ id₀) a
decProd-no-tx l d blk pp (M , step) with decProd-apiCSBF l d blk pp step
... | ()

decCP-no-tx : (l₁ l₂ : Link) (ph : SN.CPPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload} → ¬ IoOffers (decCP l₁ l₂ ph) (tx l₀ d₀ id₀) a
decCP-no-tx l₁ l₂ ph (M , step) with decCP-apiCSBF l₁ l₂ ph step
... | ()

decConsD-no-tx : (l : Link) (cph : SN.ConsDPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload} → ¬ IoOffers (decConsD l cph) (tx l₀ d₀ id₀) a
decConsD-no-tx l cph (M , step) with decConsD-apiCSBF l cph step
... | ()

-- node-A refuses `tx`
nodeA-no-tx : (na : SN.NodeStateA) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (SN.decNodeA na) (tx l₀ d₀ id₀) a
nodeA-no-tx na = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-tx linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
    (bundleG-no-tx linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)))
  (SStep.⦀-noOffer _ _
    (decProd-no-tx linkAB hi b1 (SN.NodeStateA.prod-AB na))
    (decProd-no-tx linkAC hi b1 (SN.NodeStateA.prod-AC na)))

-- node-B refuses `tx`
nodeB-no-tx : (nb : SN.NodeStateB) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decNodeB nb) (tx l₀ d₀ id₀) a
nodeB-no-tx nb = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-tx linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
    (bundleG-no-tx linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)))
  (decCP-no-tx linkAB linkBD (SN.NodeStateB.cp-B nb))

-- node-C refuses `tx`
nodeC-no-tx : (nc : SN.NodeStateC) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decNodeC nc) (tx l₀ d₀ id₀) a
nodeC-no-tx nc = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-tx linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
    (bundleG-no-tx linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)))
  (decCP-no-tx linkAC linkCD (SN.NodeStateC.cp-C nc))

-- node-D refuses `tx`
nodeD-no-tx : (nd : SN.NodeStateD) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (decNodeD nd) (tx l₀ d₀ id₀) a
nodeD-no-tx nd = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-tx linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
    (bundleG-no-tx linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)))
  (SStep.⦀-noOffer _ _
    (decConsD-no-tx linkBD (SN.NodeStateD.cons-BD nd))
    (decConsD-no-tx linkCD (SN.NodeStateD.cons-CD nd)))

-- the whole nodes interleave refuses `tx`
nodes-no-tx : (s : SysState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : Payload}
  → ¬ IoOffers (SStep.nodesOf s) (tx l₀ d₀ id₀) a
nodes-no-tx s =
  SStep.⦀-noOffer _ _ (nodeA-no-tx (nA s))
    (SStep.⦀-noOffer _ _ (nodeB-no-tx (nB s))
      (SStep.⦀-noOffer _ _ (nodeC-no-tx (nC s)) (nodeD-no-tx (nD s))))

-- bundle refuses `sndack` (every renamed peer's ι-preimage is nothing)
bundleG-no-sndack : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) (sndack l₀ d₀ id₀) a
bundleG-no-sndack l cl sv csc css bfc bfs ip =
  SStep.⦀-noOffer _ _ (decKAc-noOffer l cl (SN.kac ip) refl)
   (SStep.⦀-noOffer _ _ (decKAs-noOffer l sv (SN.kas ip) refl)
    (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSc-src l cl csc) refl)
     (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSs-src l sv css) refl)
      (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFc-src l cl bfc) refl)
       (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFs-src l sv bfs) refl)
        (SStep.⦀-noOffer _ _ (decTSc-noOffer l cl (SN.tsc ip) refl)
         (SStep.⦀-noOffer _ _ (decTSs-noOffer l sv (SN.tss ip) refl)
          (SStep.⦀-noOffer _ _ (decLNc-noOffer l cl (SN.lnc ip) refl)
           (SStep.⦀-noOffer _ _ (decLNs-noOffer l sv (SN.lns ip) refl)
            (SStep.⦀-noOffer _ _ (LFclientA-noOffer l cl refl)
                                 (LFserverA-noOffer l sv refl)))))))))))

-- the three drivers refuse `sndack` (they fire only apiCS/apiBF/done)
decProd-no-sndack : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀} → ¬ IoOffers (decProd l d blk pp) (sndack l₀ d₀ id₀) a
decProd-no-sndack l d blk pp (M , step) with decProd-apiCSBF l d blk pp step
... | ()

decCP-no-sndack : (l₁ l₂ : Link) (ph : SN.CPPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀} → ¬ IoOffers (decCP l₁ l₂ ph) (sndack l₀ d₀ id₀) a
decCP-no-sndack l₁ l₂ ph (M , step) with decCP-apiCSBF l₁ l₂ ph step
... | ()

decConsD-no-sndack : (l : Link) (cph : SN.ConsDPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀} → ¬ IoOffers (decConsD l cph) (sndack l₀ d₀ id₀) a
decConsD-no-sndack l cph (M , step) with decConsD-apiCSBF l cph step
... | ()

-- node-A refuses `sndack`
nodeA-no-sndack : (na : SN.NodeStateA) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (SN.decNodeA na) (sndack l₀ d₀ id₀) a
nodeA-no-sndack na = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-sndack linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
    (bundleG-no-sndack linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)))
  (SStep.⦀-noOffer _ _
    (decProd-no-sndack linkAB hi b1 (SN.NodeStateA.prod-AB na))
    (decProd-no-sndack linkAC hi b1 (SN.NodeStateA.prod-AC na)))

-- node-B refuses `sndack`
nodeB-no-sndack : (nb : SN.NodeStateB) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decNodeB nb) (sndack l₀ d₀ id₀) a
nodeB-no-sndack nb = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-sndack linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
    (bundleG-no-sndack linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)))
  (decCP-no-sndack linkAB linkBD (SN.NodeStateB.cp-B nb))

-- node-C refuses `sndack`
nodeC-no-sndack : (nc : SN.NodeStateC) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decNodeC nc) (sndack l₀ d₀ id₀) a
nodeC-no-sndack nc = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-sndack linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
    (bundleG-no-sndack linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)))
  (decCP-no-sndack linkAC linkCD (SN.NodeStateC.cp-C nc))

-- node-D refuses `sndack`
nodeD-no-sndack : (nd : SN.NodeStateD) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decNodeD nd) (sndack l₀ d₀ id₀) a
nodeD-no-sndack nd = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-sndack linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
    (bundleG-no-sndack linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)))
  (SStep.⦀-noOffer _ _
    (decConsD-no-sndack linkBD (SN.NodeStateD.cons-BD nd))
    (decConsD-no-sndack linkCD (SN.NodeStateD.cons-CD nd)))

-- the whole nodes interleave refuses `sndack`
nodes-no-sndack : (s : SysState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (SStep.nodesOf s) (sndack l₀ d₀ id₀) a
nodes-no-sndack s =
  SStep.⦀-noOffer _ _ (nodeA-no-sndack (nA s))
    (SStep.⦀-noOffer _ _ (nodeB-no-sndack (nB s))
      (SStep.⦀-noOffer _ _ (nodeC-no-sndack (nC s)) (nodeD-no-sndack (nD s))))

-- bundle refuses `rcvack` (every renamed peer's ι-preimage is nothing)
bundleG-no-rcvack : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) (rcvack l₀ d₀ id₀) a
bundleG-no-rcvack l cl sv csc css bfc bfs ip =
  SStep.⦀-noOffer _ _ (decKAc-noOffer l cl (SN.kac ip) refl)
   (SStep.⦀-noOffer _ _ (decKAs-noOffer l sv (SN.kas ip) refl)
    (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSc-src l cl csc) refl)
     (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSs-src l sv css) refl)
      (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFc-src l cl bfc) refl)
       (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFs-src l sv bfs) refl)
        (SStep.⦀-noOffer _ _ (decTSc-noOffer l cl (SN.tsc ip) refl)
         (SStep.⦀-noOffer _ _ (decTSs-noOffer l sv (SN.tss ip) refl)
          (SStep.⦀-noOffer _ _ (decLNc-noOffer l cl (SN.lnc ip) refl)
           (SStep.⦀-noOffer _ _ (decLNs-noOffer l sv (SN.lns ip) refl)
            (SStep.⦀-noOffer _ _ (LFclientA-noOffer l cl refl)
                                 (LFserverA-noOffer l sv refl)))))))))))

-- the three drivers refuse `rcvack` (they fire only apiCS/apiBF/done)
decProd-no-rcvack : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀} → ¬ IoOffers (decProd l d blk pp) (rcvack l₀ d₀ id₀) a
decProd-no-rcvack l d blk pp (M , step) with decProd-apiCSBF l d blk pp step
... | ()

decCP-no-rcvack : (l₁ l₂ : Link) (ph : SN.CPPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀} → ¬ IoOffers (decCP l₁ l₂ ph) (rcvack l₀ d₀ id₀) a
decCP-no-rcvack l₁ l₂ ph (M , step) with decCP-apiCSBF l₁ l₂ ph step
... | ()

decConsD-no-rcvack : (l : Link) (cph : SN.ConsDPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀} → ¬ IoOffers (decConsD l cph) (rcvack l₀ d₀ id₀) a
decConsD-no-rcvack l cph (M , step) with decConsD-apiCSBF l cph step
... | ()

-- node-A refuses `rcvack`
nodeA-no-rcvack : (na : SN.NodeStateA) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (SN.decNodeA na) (rcvack l₀ d₀ id₀) a
nodeA-no-rcvack na = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-rcvack linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
    (bundleG-no-rcvack linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)))
  (SStep.⦀-noOffer _ _
    (decProd-no-rcvack linkAB hi b1 (SN.NodeStateA.prod-AB na))
    (decProd-no-rcvack linkAC hi b1 (SN.NodeStateA.prod-AC na)))

-- node-B refuses `rcvack`
nodeB-no-rcvack : (nb : SN.NodeStateB) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decNodeB nb) (rcvack l₀ d₀ id₀) a
nodeB-no-rcvack nb = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-rcvack linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
    (bundleG-no-rcvack linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)))
  (decCP-no-rcvack linkAB linkBD (SN.NodeStateB.cp-B nb))

-- node-C refuses `rcvack`
nodeC-no-rcvack : (nc : SN.NodeStateC) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decNodeC nc) (rcvack l₀ d₀ id₀) a
nodeC-no-rcvack nc = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-rcvack linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
    (bundleG-no-rcvack linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)))
  (decCP-no-rcvack linkAC linkCD (SN.NodeStateC.cp-C nc))

-- node-D refuses `rcvack`
nodeD-no-rcvack : (nd : SN.NodeStateD) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decNodeD nd) (rcvack l₀ d₀ id₀) a
nodeD-no-rcvack nd = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-rcvack linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
    (bundleG-no-rcvack linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)))
  (SStep.⦀-noOffer _ _
    (decConsD-no-rcvack linkBD (SN.NodeStateD.cons-BD nd))
    (decConsD-no-rcvack linkCD (SN.NodeStateD.cons-CD nd)))

-- the whole nodes interleave refuses `rcvack`
nodes-no-rcvack : (s : SysState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (SStep.nodesOf s) (rcvack l₀ d₀ id₀) a
nodes-no-rcvack s =
  SStep.⦀-noOffer _ _ (nodeA-no-rcvack (nA s))
    (SStep.⦀-noOffer _ _ (nodeB-no-rcvack (nB s))
      (SStep.⦀-noOffer _ _ (nodeC-no-rcvack (nC s)) (nodeD-no-rcvack (nD s))))

-- bundle refuses `ack` (every renamed peer's ι-preimage is nothing)
bundleG-no-ack : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) (ack l₀ d₀ id₀) a
bundleG-no-ack l cl sv csc css bfc bfs ip =
  SStep.⦀-noOffer _ _ (decKAc-noOffer l cl (SN.kac ip) refl)
   (SStep.⦀-noOffer _ _ (decKAs-noOffer l sv (SN.kas ip) refl)
    (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSc-src l cl csc) refl)
     (SStep.⦀-noOffer _ _ (SStep.CSNO.renameMap-noOffer-χ (decCSs-src l sv css) refl)
      (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFc-src l cl bfc) refl)
       (SStep.⦀-noOffer _ _ (SStep.BFNO.renameMap-noOffer-χ (decBFs-src l sv bfs) refl)
        (SStep.⦀-noOffer _ _ (decTSc-noOffer l cl (SN.tsc ip) refl)
         (SStep.⦀-noOffer _ _ (decTSs-noOffer l sv (SN.tss ip) refl)
          (SStep.⦀-noOffer _ _ (decLNc-noOffer l cl (SN.lnc ip) refl)
           (SStep.⦀-noOffer _ _ (decLNs-noOffer l sv (SN.lns ip) refl)
            (SStep.⦀-noOffer _ _ (LFclientA-noOffer l cl refl)
                                 (LFserverA-noOffer l sv refl)))))))))))

-- the three drivers refuse `ack` (they fire only apiCS/apiBF/done)
decProd-no-ack : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀} → ¬ IoOffers (decProd l d blk pp) (ack l₀ d₀ id₀) a
decProd-no-ack l d blk pp (M , step) with decProd-apiCSBF l d blk pp step
... | ()

decCP-no-ack : (l₁ l₂ : Link) (ph : SN.CPPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀} → ¬ IoOffers (decCP l₁ l₂ ph) (ack l₀ d₀ id₀) a
decCP-no-ack l₁ l₂ ph (M , step) with decCP-apiCSBF l₁ l₂ ph step
... | ()

decConsD-no-ack : (l : Link) (cph : SN.ConsDPh)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀} → ¬ IoOffers (decConsD l cph) (ack l₀ d₀ id₀) a
decConsD-no-ack l cph (M , step) with decConsD-apiCSBF l cph step
... | ()

-- node-A refuses `ack`
nodeA-no-ack : (na : SN.NodeStateA) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (SN.decNodeA na) (ack l₀ d₀ id₀) a
nodeA-no-ack na = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-ack linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
    (bundleG-no-ack linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)))
  (SStep.⦀-noOffer _ _
    (decProd-no-ack linkAB hi b1 (SN.NodeStateA.prod-AB na))
    (decProd-no-ack linkAC hi b1 (SN.NodeStateA.prod-AC na)))

-- node-B refuses `ack`
nodeB-no-ack : (nb : SN.NodeStateB) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decNodeB nb) (ack l₀ d₀ id₀) a
nodeB-no-ack nb = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-ack linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
    (bundleG-no-ack linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)))
  (decCP-no-ack linkAB linkBD (SN.NodeStateB.cp-B nb))

-- node-C refuses `ack`
nodeC-no-ack : (nc : SN.NodeStateC) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decNodeC nc) (ack l₀ d₀ id₀) a
nodeC-no-ack nc = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-ack linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
    (bundleG-no-ack linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)))
  (decCP-no-ack linkAC linkCD (SN.NodeStateC.cp-C nc))

-- node-D refuses `ack`
nodeD-no-ack : (nd : SN.NodeStateD) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (decNodeD nd) (ack l₀ d₀ id₀) a
nodeD-no-ack nd = SStep.∥⇘apiES⇙-noOffer _ _ (λ ())
  (SStep.⦀-noOffer _ _
    (bundleG-no-ack linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
    (bundleG-no-ack linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)))
  (SStep.⦀-noOffer _ _
    (decConsD-no-ack linkBD (SN.NodeStateD.cons-BD nd))
    (decConsD-no-ack linkCD (SN.NodeStateD.cons-CD nd)))

-- the whole nodes interleave refuses `ack`
nodes-no-ack : (s : SysState) {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {a : ⊤₀}
  → ¬ IoOffers (SStep.nodesOf s) (ack l₀ d₀ id₀) a
nodes-no-ack s =
  SStep.⦀-noOffer _ _ (nodeA-no-ack (nA s))
    (SStep.⦀-noOffer _ _ (nodeB-no-ack (nB s))
      (SStep.⦀-noOffer _ _ (nodeC-no-ack (nC s)) (nodeD-no-ack (nD s))))

