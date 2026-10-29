{-# OPTIONS --guardedness #-}

-- Bidirectional paired replay correspondence with the existing peers and FIFOs.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.BlockFetchPairedBridge (p : Params) where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map; mapMaybe)
open import Data.List.Properties using (map-id)
open import Data.List.Relation.Unary.All using (universal)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (⊤; tt)
open import Function using (id)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base
open import Cardano_network.Data p
open import Cardano_network.Net p using (Link)
open Params p using (Block)
open import Cardano_network.BlockFetch p using (BFEv)
import Cardano_network.BlockFetchPipe p as Pipe
import Cardano_network.Replay.BlockFetchClientSession as Ctl
open import Cardano_network.Replay.Common
open import Cardano_network.Replay.BlockFetchPairedModel p using (Proc; PairEv; PairI; atClient; atServer; compose; queues)
import Cardano_network.Replay.BlockFetchPairedTrace p as Trace
import Cardano_network.Replay.BlockFetchPairedPackets p as Packets
import Cardano_network.Replay.BlockFetchPairedSession as Paired
import Cardano_network.Replay.BlockFetchClientBridge p as C
import Cardano_network.Replay.BlockFetchServerBridge p as S
import Cardano_network.Replay.BlockFetchServerSession as ServerCtl
import Cardano_network.Replay.BlockFetchPairedLocal as Wire
import Cardano_network.Replay.BlockFetchPairedCanonical p as Canon
open import Cardano_network.Replay.BlockFetchPairedSound p using (classify; Obs; system; sound; model-certificate) public
import Semantics.LTS {E = BFEv} {I = ExtI BFEv} as Local
import Semantics.LTS {E = PairEv} {I = PairI} as Pair
import Semantics.Deadlock {E = PairEv} {I = PairI} as Dead
open Dead using (_⟹∖√⟨_⟩_)
import Semantics.Replay.Bridge {E = PairEv} {I = PairI} as Bridge
open import Semantics.Replay using (Replay)

-- Tagging an actual local trace commutes with control observation.
client-observation : ∀ t → mapMaybe classify (Trace.clientEvents t) ≡ map (client ,_) (mapMaybe C.cls t)
client-observation [] = refl
client-observation (e@(Local.evLabel X ch a) ∷ t) with C.cls e
... | nothing = client-observation t
... | just m = cong ((client , m) ∷_) (client-observation t)

-- The server-tagged trace retains exactly the server's local observations.
server-observation : ∀ t → mapMaybe classify (Trace.serverEvents t) ≡ map (server ,_) (mapMaybe S.cls t)
server-observation [] = refl
server-observation (e@(Local.evLabel X ch a) ∷ t) with S.cls e
... | nothing = server-observation t
... | just m = cong ((server , m) ∷_) (server-observation t)

module _ (k : ℕ) (cl sl : Link) (cd sd : Dir) (b₀ : Block) where
  module R = Paired k

  -- Canonical representatives use the existing local completeness relations.
  -- Their network queues hold shared full payload witnesses for each abstract kind.
  data RelC : PTree PairEv PairI ⊤ → R.State → Set₁ where
    linked : ∀ {c s cs ss ctos stoc} → C.RelC k cl cd c cs → S.RelC sl sd s ss →
      RelC (compose c s (queues (Canon.queue b₀ ctos) (Canon.queue b₀ stoc)))
        (R.paired (R.clientS cs) (R.serverS ss) ctos stoc)

  -- Realise a client control event together with its actual API and silent steps.
  client-macro : ∀ {c s cs cs′ ss ctos stoc ctos′ stoc′ e} →
    C.RelC k cl cd c cs → S.RelC sl sd s ss → Ctl.Step k cs e cs′ →
    Packets.clientPacket (Canon.packet b₀ e) (queues (Canon.queue b₀ ctos) (Canon.queue b₀ stoc)) ≡
      just (queues (Canon.queue b₀ ctos′) (Canon.queue b₀ stoc′)) →
    ∃[ T ] ∃[ t ]
      (compose c s (queues (Canon.queue b₀ ctos) (Canon.queue b₀ stoc)) ⟹∖√⟨ t ⟩ T ×
       Obs t ((client , e) ∷ []) × RelC T (R.paired (R.clientS cs′) (R.serverS ss) ctos′ stoc′))
  client-macro {s = s} cr sr pr gate with C.co-ev k cl cd b₀ cr tt pr |
    Canon.client-packet b₀ k cl cd cr pr
  ... | c′ , t , run , obs , cr′ | exact = _ , _ ,
    Trace.complete (Trace.lift-client {s = s} run (Packets.one-client t exact gate)) ,
    trans (client-observation t) (cong (map (client ,_)) obs) , linked cr′ sr

  -- The server macro uses the same packet witnesses, rather than independent data.
  server-macro : ∀ {c s cs ss ss′ ctos stoc ctos′ stoc′ e} →
    C.RelC k cl cd c cs → S.RelC sl sd s ss → ServerCtl.Step ss e ss′ →
    Packets.serverPacket (Canon.packet b₀ e) (queues (Canon.queue b₀ ctos) (Canon.queue b₀ stoc)) ≡
      just (queues (Canon.queue b₀ ctos′) (Canon.queue b₀ stoc′)) →
    ∃[ T ] ∃[ t ]
      (compose c s (queues (Canon.queue b₀ ctos) (Canon.queue b₀ stoc)) ⟹∖√⟨ t ⟩ T ×
       Obs t ((server , e) ∷ []) × RelC T (R.paired (R.clientS cs) (R.serverS ss′) ctos′ stoc′))
  server-macro {c = c} cr sr pr gate with S.co-ev sl sd b₀ sr tt pr |
    Canon.server-packet b₀ k sl sd sr pr
  ... | s′ , t , run , obs , sr′ | exact = _ , _ ,
    Trace.complete (Trace.lift-server {c = c} run (Packets.one-server t exact gate)) ,
    trans (server-observation t) (cong (map (server ,_)) obs) , linked cr sr′

  -- The paired first-order model has no internal transitions to realise.
  co-τ : ∀ {T s s′} → RelC T s → Replay._-τ→_ R.model s s′ →
    ∃[ T′ ] ∃[ t ] (T ⟹∖√⟨ t ⟩ T′ × Obs t [] × RelC T′ s′)
  co-τ _ ()

  -- All four endpoint/direction cases synchronise exact packet queue updates.
  co-ev : ∀ {T s s′ e} → RelC T s → ⊤ → R.Step s e s′ →
    ∃[ T′ ] ∃[ t ] (T ⟹∖√⟨ t ⟩ T′ × Obs t (e ∷ []) × RelC T′ s′)
  co-ev (linked {cs = cs} cr sr) _ st@(R.clientSend pr) with Wire.client-target k {s = R.clientS cs} pr
  ... | c′ , refl = client-macro cr sr (Wire.client-sound k {s = R.clientS cs} pr) (Canon.client-gate b₀ k st)
  co-ev (linked {cs = cs} cr sr) _ st@(R.clientRecv pr) with Wire.client-target k {s = R.clientS cs} pr
  ... | c′ , refl = client-macro cr sr (Wire.client-sound k {s = R.clientS cs} pr) (Canon.client-gate b₀ k st)
  co-ev (linked {ss = ss} cr sr) _ st@(R.serverSend pr) with Wire.server-target k {s = R.serverS ss} pr
  ... | s′ , refl = server-macro cr sr (Wire.server-sound k {s = R.serverS ss} pr) (Canon.server-gate b₀ k st)
  co-ev (linked {ss = ss} cr sr) _ st@(R.serverRecv pr) with Wire.server-target k {s = R.serverS ss} pr
  ... | s′ , refl = server-macro cr sr (Wire.server-sound k {s = R.serverS ss} pr) (Canon.server-gate b₀ k st)

  -- Original peer PTrees with exact-payload FIFOs co-simulate paired replay.
  cosimulation : Bridge.CoSim R.model classify id RelC (λ _ → ⊤)
  cosimulation = record { co-τ = co-τ ; co-ev = co-ev }

  -- Every accepted paired control trace has a concrete composed PTree execution.
  complete : ∀ {es} → R.HasTrace R.initial es →
    ∃[ t ] ∃[ T ] (system k cl sl cd sd ⟹∖√⟨ t ⟩ T × Obs t es)
  complete {es} (_ , run) with Bridge.complete R.model classify id cosimulation
    (linked (C.cWait C.emptyQ) S.cIdle) (universal (λ _ → tt) es) run
  ... | T , t , concrete , obs , _ = t , T , concrete , obs

  -- Exact finite observed trace correspondence for the specified FIFO product.
  bridge : ∀ {es} → R.HasTrace R.initial es ⇔
    (∃[ t ] ∃[ T ] (system k cl sl cd sd ⟹∖√⟨ t ⟩ T × Obs t es))
  bridge = mk⇔ complete (λ { (t , T , run , obs) → sound k cl sl cd sd run obs })

  -- A composed trace witnesses compatibility of the two complete local inputs.
  Inputs : List Ctl.E → List Ctl.E → Set₁
  Inputs cs ss = ∃[ t ] ∃[ T ] ∃[ es ]
    (system k cl sl cd sd ⟹∖√⟨ t ⟩ T × Obs t es × R.project client es ≡ cs × R.project server es ≡ ss)

  -- Paired-checker acceptance constructs a single full-payload composed run.
  inputs-complete : ∀ {cs ss} → R.Compatible R.initial cs ss → Inputs cs ss
  inputs-complete run with complete (R.merge-run run)
  ... | t , T , concrete , obs = t , T , R.merge run , concrete , obs , R.client-projection run , R.server-projection run

  -- Every concrete witness is covered by the exhaustive input-merge checker.
  inputs-sound : ∀ {cs ss} → Inputs cs ss → R.Compatible R.initial cs ss
  inputs-sound (t , T , es , run , obs , co , so) = R.fromWitness
    (R.witness es co so (sound k cl sl cd sd run obs))

  -- Bidirectional checker correspondence, including the existential merge order.
  inputs-bridge : ∀ {cs ss} → R.Compatible R.initial cs ss ⇔ Inputs cs ss
  inputs-bridge = mk⇔ inputs-complete inputs-sound

  -- Checker soundness: an accepted certificate denotes one joint PTree run.
  checker-sound : ∀ {cs ss} → R.Witness R.initial cs ss → Inputs cs ss
  checker-sound w = inputs-complete (R.fromWitness w)

  -- Checker completeness: every observed joint run yields a replay certificate.
  checker-complete : ∀ {cs ss} → Inputs cs ss → R.Witness R.initial cs ss
  checker-complete input = R.toWitness (inputs-sound input)

  -- The actual merge-search certificate has exactly this composed meaning.
  certificate-bridge : ∀ {cs ss} → R.Witness R.initial cs ss ⇔ Inputs cs ss
  certificate-bridge = mk⇔ checker-sound checker-complete
