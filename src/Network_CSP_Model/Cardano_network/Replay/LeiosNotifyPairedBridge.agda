{-# OPTIONS --guardedness #-}

-- Exact-field paired replay equivalence with native bounded Notify peers and FIFOs.
open import Cardano_network.Replay.LeiosNotifyExactParams renaming (exactParams to p)
module Cardano_network.Replay.LeiosNotifyPairedBridge where

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
open import Cardano_network.LeiosNotifyP p using (LNPEv)
open import Cardano_network.LeiosNotifyPipe p using (consumer; producer)
import Cardano_network.LeiosNotifyPipe p as Pipe
import Cardano_network.Replay.LeiosNotifyPipeline as N
open import Cardano_network.Replay.Common
open import Cardano_network.Replay.LeiosNotifyPairedModel p using (Proc; PairEv; PairI; atClient; atServer; compose; queues)
import Cardano_network.Replay.LeiosNotifyPairedTrace p as Trace
import Cardano_network.Replay.LeiosNotifyExactPackets as Packets
import Cardano_network.Replay.LeiosNotifyPairedSession as Paired
import Cardano_network.Replay.LeiosNotifyExactLocal as LocalBridge
import Cardano_network.Replay.LeiosNotifyExactObservation as O
import Cardano_network.Replay.LeiosNotifyExactCanonical as Canon
open import Cardano_network.Replay.LeiosNotifyExactSound using (classify; Obs; system; sound) public
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as Local
import Semantics.LTS {E = PairEv} {I = PairI} as Pair
import Semantics.Deadlock {E = PairEv} {I = PairI} as Dead
open Dead using (_⟹∖√⟨_⟩_)
import Semantics.Replay.Bridge {E = PairEv} {I = PairI} as Bridge
open import Semantics.Replay using (Replay)

-- Tagging an actual local trace commutes with exact-field observation.
client-observation : ∀ t → mapMaybe classify (Trace.clientEvents t) ≡ map (client ,_) (mapMaybe O.classify t)
client-observation [] = refl
client-observation (e@(Local.evLabel X ch a) ∷ t) with O.classify e
... | nothing = client-observation t
... | just m = cong ((client , m) ∷_) (client-observation t)

-- The server-tagged trace retains exactly the server's local observations.
server-observation : ∀ t → mapMaybe classify (Trace.serverEvents t) ≡ map (server ,_) (mapMaybe O.classify t)
server-observation [] = refl
server-observation (e@(Local.evLabel X ch a) ∷ t) with O.classify e
... | nothing = server-observation t
... | just m = cong ((server , m) ∷_) (server-observation t)

module _ (k : ℕ) (cl sl : Link) (cd sd : Dir) where
  module R = Paired k
  module C = LocalBridge k cl cd
  module S = LocalBridge k sl sd

  -- Canonical representatives use the existing local completeness relations.
  -- Their network queues hold shared full payload witnesses for each retained message.
  data RelC : PTree PairEv PairI ⊤ → R.State → Set₁ where
    linked : ∀ {c s cs ss ctos stoc} → C.CoRel consumer c cs → S.CoRel producer s ss →
      RelC (compose c s (queues (Canon.queue ctos) (Canon.queue stoc)))
        (R.paired cs ss ctos stoc)

  -- Realise a client exact event together with its actual API and silent steps, preserving every retained field.
  client-macro : ∀ {c s cs cs′ ss ctos stoc ctos′ stoc′ e} →
    C.CoRel consumer c cs → S.CoRel producer s ss → N.Spec.Step k client cs e cs′ →
    Packets.clientPacket (Canon.packet e) (queues (Canon.queue ctos) (Canon.queue stoc)) ≡
      just (queues (Canon.queue ctos′) (Canon.queue stoc′)) →
    ∃[ T ] ∃[ t ]
      (compose c s (queues (Canon.queue ctos) (Canon.queue stoc)) ⟹∖√⟨ t ⟩ T ×
       Obs t ((client , e) ∷ []) × RelC T (R.paired cs′ ss ctos′ stoc′))
  client-macro {s = s} cr sr pr gate with C.coEv cr tt pr |
    Canon.one-packet k cl cd cr pr
  ... | c′ , t , run , obs , cr′ | exact = _ , _ ,
    Trace.complete (Trace.lift-client {s = s} run (Packets.one-client t exact gate)) ,
    trans (client-observation t) (cong (map (client ,_)) obs) , linked cr′ sr

  -- The server macro uses the same packet witnesses, with identical retained fields at both endpoints.
  server-macro : ∀ {c s cs ss ss′ ctos stoc ctos′ stoc′ e} →
    C.CoRel consumer c cs → S.CoRel producer s ss → N.Spec.Step k server ss e ss′ →
    Packets.serverPacket (Canon.packet e) (queues (Canon.queue ctos) (Canon.queue stoc)) ≡
      just (queues (Canon.queue ctos′) (Canon.queue stoc′)) →
    ∃[ T ] ∃[ t ]
      (compose c s (queues (Canon.queue ctos) (Canon.queue stoc)) ⟹∖√⟨ t ⟩ T ×
       Obs t ((server , e) ∷ []) × RelC T (R.paired cs ss′ ctos′ stoc′))
  server-macro {c = c} cr sr pr gate with S.coEv sr tt pr |
    Canon.one-packet k sl sd sr pr
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
  co-ev (linked cr sr) _ st@(R.clientSend pr) = client-macro cr sr pr (Canon.client-gate k st)
  co-ev (linked cr sr) _ st@(R.clientRecv pr) = client-macro cr sr pr (Canon.client-gate k st)
  co-ev (linked cr sr) _ st@(R.serverSend pr) = server-macro cr sr pr (Canon.server-gate k st)
  co-ev (linked cr sr) _ st@(R.serverRecv pr) = server-macro cr sr pr (Canon.server-gate k st)

  -- Native bounded peer PTrees with exact-payload FIFOs co-simulate paired replay.
  cosimulation : Bridge.CoSim R.model classify id RelC (λ _ → ⊤)
  cosimulation = record { co-τ = co-τ ; co-ev = co-ev }

  -- Every accepted paired exact-field trace has a concrete composed PTree execution.
  complete : ∀ {es} → R.HasTrace R.initial es →
    ∃[ t ] ∃[ T ] (system k cl sl cd sd ⟹∖√⟨ t ⟩ T × Obs t es)
  complete {es} (_ , run) with Bridge.complete R.model classify id cosimulation
    (linked C.headC S.headC) (universal (λ _ → tt) es) run
  ... | T , t , concrete , obs , _ = t , T , concrete , obs

  -- Exact finite observed trace correspondence for the specified FIFO product.
  bridge : ∀ {es} → R.HasTrace R.initial es ⇔
    (∃[ t ] ∃[ T ] (system k cl sl cd sd ⟹∖√⟨ t ⟩ T × Obs t es))
  bridge = mk⇔ complete (λ { (t , T , run , obs) → sound k cl sl cd sd run obs })

  -- A composed trace witnesses compatibility of the two complete local inputs.
  Inputs : List N.E → List N.E → Set₁
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

  -- The exact certificate returned by witness search has the same composed meaning.
  certificate-bridge : ∀ {cs ss} → R.Witness R.initial cs ss ⇔ Inputs cs ss
  certificate-bridge = mk⇔
    (λ w → inputs-complete (R.fromWitness w))
    (λ input → R.toWitness (inputs-sound input))
