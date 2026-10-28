{-# OPTIONS --guardedness #-}

-- Bidirectional paired replay correspondence with two original peers and FIFOs.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.ChainSyncPairedBridge (p : Params) where

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
open import Cardano_network.ChainSync p using (CSEv)
import Cardano_network.ChainSyncPipe p as Pipe
import Cardano_network.Replay.ChainSyncSession as CS
open import Cardano_network.Replay.Common
open import Cardano_network.Replay.ChainSyncPairedModel p using (Proc; PairEv; PairI; atClient; atServer; compose; queues)
import Cardano_network.Replay.ChainSyncPairedTrace p as Trace
import Cardano_network.Replay.ChainSyncPairedPackets p as Packets
import Cardano_network.Replay.ChainSyncPairedSession as Paired
import Cardano_network.Replay.ChainSyncClientBridge p as C
import Cardano_network.Replay.ChainSyncServerBridge p as S
import Cardano_network.Replay.ChainSyncStepView as View
import Cardano_network.Replay.ChainSyncPairedCanonical p as Canon
open import Cardano_network.Replay.ChainSyncPairedSound p using (classify; Obs; system; sound) public
import Semantics.LTS {E = CSEv} {I = ExtI CSEv} as Local
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
    linked : ∀ {c s cs ss ctos stoc} → C.RelC k cl cd c cs → S.RelC k sl sd s ss →
      RelC (compose c s (queues (Canon.queue b₀ ctos) (Canon.queue b₀ stoc)))
        (R.paired cs ss ctos stoc)

  -- Realise a client control event together with its actual API and silent steps.
  client-macro : ∀ {c s cs cs′ ss ctos stoc ctos′ stoc′ e} →
    C.RelC k cl cd c cs → S.RelC k sl sd s ss → CS.Spec.Step k client cs e cs′ →
    Packets.clientPacket (Canon.packet b₀ e) (queues (Canon.queue b₀ ctos) (Canon.queue b₀ stoc)) ≡
      just (queues (Canon.queue b₀ ctos′) (Canon.queue b₀ stoc′)) →
    ∃[ T ] ∃[ t ]
      (compose c s (queues (Canon.queue b₀ ctos) (Canon.queue b₀ stoc)) ⟹∖√⟨ t ⟩ T ×
       Obs t ((client , e) ∷ []) × RelC T (R.paired cs′ ss ctos′ stoc′))
  client-macro {s = s} cr sr pr gate with C.co-view k cl cd b₀ cr (View.view pr) |
    Canon.client-packet b₀ k cl cd cr (View.view pr)
  ... | c′ , t , run , obs , cr′ | exact = _ , _ ,
    Trace.complete (Trace.lift-client {s = s} run (Packets.one-client t exact gate)) ,
    trans (client-observation t) (cong (map (client ,_)) obs) , linked cr′ sr

  -- The server macro uses the same packet witnesses, rather than independent data.
  server-macro : ∀ {c s cs ss ss′ ctos stoc ctos′ stoc′ e} →
    C.RelC k cl cd c cs → S.RelC k sl sd s ss → CS.Spec.Step k server ss e ss′ →
    Packets.serverPacket (Canon.packet b₀ e) (queues (Canon.queue b₀ ctos) (Canon.queue b₀ stoc)) ≡
      just (queues (Canon.queue b₀ ctos′) (Canon.queue b₀ stoc′)) →
    ∃[ T ] ∃[ t ]
      (compose c s (queues (Canon.queue b₀ ctos) (Canon.queue b₀ stoc)) ⟹∖√⟨ t ⟩ T ×
       Obs t ((server , e) ∷ []) × RelC T (R.paired cs ss′ ctos′ stoc′))
  server-macro {c = c} cr sr pr gate with S.co-ev k sl sd b₀ sr tt pr |
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
  co-ev (linked cr sr) _ st@(R.clientSend pr) = client-macro cr sr pr (Canon.client-gate b₀ k st)
  co-ev (linked cr sr) _ st@(R.clientRecv pr) = client-macro cr sr pr (Canon.client-gate b₀ k st)
  co-ev (linked cr sr) _ st@(R.serverSend pr) = server-macro cr sr pr (Canon.server-gate b₀ k st)
  co-ev (linked cr sr) _ st@(R.serverRecv pr) = server-macro cr sr pr (Canon.server-gate b₀ k st)

  -- Original peer PTrees with exact-payload FIFOs co-simulate paired replay.
  cosimulation : Bridge.CoSim R.model classify id RelC (λ _ → ⊤)
  cosimulation = record { co-τ = co-τ ; co-ev = co-ev }

  -- Every accepted paired control trace has a concrete composed PTree execution.
  complete : ∀ {es} → R.HasTrace R.initial es →
    ∃[ t ] ∃[ T ] (system k cl sl cd sd ⟹∖√⟨ t ⟩ T × Obs t es)
  complete {es} (_ , run) with Bridge.complete R.model classify id cosimulation
    (linked (C.cCan 0) (S.cstIdle)) (universal (λ _ → tt) es) run
  ... | T , t , concrete , obs , _ = t , T , concrete , obs

  -- Exact finite observed trace correspondence for the specified FIFO product.
  bridge : ∀ {es} → R.HasTrace R.initial es ⇔
    (∃[ t ] ∃[ T ] (system k cl sl cd sd ⟹∖√⟨ t ⟩ T × Obs t es))
  bridge = mk⇔ complete (λ { (t , T , run , obs) → sound k cl sl cd sd run obs })

  -- A composed trace witnesses compatibility of the two complete local inputs.
  Inputs : List CS.E → List CS.E → Set₁
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
