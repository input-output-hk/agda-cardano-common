{-# OPTIONS --guardedness #-}

-- Exact-field soundness of the native bounded Notify peer/FIFO product.
open import Cardano_network.Replay.LeiosNotifyExactParams renaming (exactParams to p)
module Cardano_network.Replay.LeiosNotifyExactSound where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map; mapMaybe)
open import Data.List.Properties using (map-id)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapM)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyP p using (LNPEv)
open import Cardano_network.LeiosNotifyPipe p using (consumer; producer)
import Cardano_network.LeiosNotifyPipe p as Pipe
open import Cardano_network.Replay.Common
open import Cardano_network.Replay.LeiosNotifyPairedModel p hiding (system)
open import Cardano_network.Replay.LeiosNotifyPairedParts p
open import Cardano_network.Replay.LeiosNotifyExactPackets using (queue; BufferStep; unchanged; sentC; recvC; sentS; recvS; client-gate-sound; server-gate-sound)
import Cardano_network.Replay.LeiosNotifyPipeline as N
import Cardano_network.Replay.LeiosNotifyPairedSession as Paired
import Cardano_network.Replay.LeiosNotifyExactLocal as B
import Cardano_network.Replay.LeiosNotifyExactObservation as O
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as Local
import Semantics.LTS {E = PairEv} {I = PairI} as Pair
open import Semantics.Deadlock {E = PairEv} {I = PairI} using (_⟹∖√⟨_⟩_)
import Semantics.Replay.Bridge {E = PairEv} {I = PairI} as Bridge

-- The final observation retains endpoint, wire direction and every retained message field.
classify : Pair.Event → Maybe (Role × N.E)
classify (Pair.evLabel X (atClient ch) a) = mapM (client ,_) (O.classify (Local.evLabel X ch a))
classify (Pair.evLabel X (atServer ch) a) = mapM (server ,_) (O.classify (Local.evLabel X ch a))

-- Finite trace comparison hides APIs and semantic termination only.
Obs : List Pair.Event → List (Role × N.E) → Set
Obs = Bridge.Obs classify id

-- One optional local observation gives zero or one replay events.
one : Maybe N.E → List N.E
one nothing = []
one (just e) = e ∷ []

-- Endpoint tagging preserves all retained summary fields.
tag : Role → Maybe N.E → List (Role × N.E)
tag r nothing = []
tag r (just e) = (r , e) ∷ []

-- A concrete client event has exactly its endpoint-tagged observation.
obs-client : ∀ {X} (ch : LNPEv X) a → Obs (Pair.evLabel X (atClient ch) a ∷ [])
  (tag client (O.classify (Local.evLabel X ch a)))
obs-client ch a with O.classify (Local.evLabel _ ch a)
... | nothing = refl
... | just e = refl

-- The server observation obeys the same rule independently of peer state.
obs-server : ∀ {X} (ch : LNPEv X) a → Obs (Pair.evLabel X (atServer ch) a ∷ [])
  (tag server (O.classify (Local.evLabel X ch a)))
obs-server ch a with O.classify (Local.evLabel _ ch a)
... | nothing = refl
... | just e = refl

module _ (k : ℕ) where
  module R = Paired k
  module Client = N.Spec k client
  module Server = N.Spec k server

  -- Local replay has no silent transitions, so an empty run preserves state.
  empty-local : ∀ r {s s′} → N.Spec._⇒⟨_⟩_ k r s [] s′ → s ≡ s′
  empty-local r N.Spec.done = refl
  empty-local r (N.Spec.tau () _)

  -- A singleton local run witnesses exactly one original local update.
  single-local : ∀ r {s s′ e} → N.Spec._⇒⟨_⟩_ k r s (e ∷ []) s′ → N.nextKind k r s (N.forget e) ≡ just s′
  single-local r (N.Spec.tau () _)
  single-local r (N.Spec.vis pr rest) with empty-local r rest
  ... | refl = pr

  -- Normalize the old local bridge's identity-mapped observation equality.
  normalize : ∀ r {s s′ es e} → N.Spec._⇒⟨_⟩_ k r s es s′ → mapMaybe O.classify (e ∷ []) ≡ map id es →
    N.Spec._⇒⟨_⟩_ k r s (one (O.classify e)) s′
  normalize r {es = es} {e} run obs with O.classify e
  ... | nothing = subst (λ t → N.Spec._⇒⟨_⟩_ k r _ t _) (trans (sym (map-id es)) (sym obs)) run
  ... | just e′ = subst (λ t → N.Spec._⇒⟨_⟩_ k r _ t _) (trans (sym (map-id es)) (sym obs)) run

  -- A local client update plus an abstract FIFO move is a paired run.
  advance-client : ∀ {cs sc cs′ sc′ ob c c′ s} → BufferStep client cs sc ob cs′ sc′ →
    Client._⇒⟨_⟩_ c (one ob) c′ →
    R._⇒⟨_⟩_ (R.paired c s cs sc) (tag client ob) (R.paired c′ s cs′ sc′)
  advance-client unchanged run with empty-local client run
  ... | refl = R.done
  advance-client sentC run = R.vis (R.clientSend (single-local client run)) R.done
  advance-client recvC run = R.vis (R.clientRecv (single-local client run)) R.done

  -- The symmetric server update preserves the opposite local peer state.
  advance-server : ∀ {cs sc cs′ sc′ ob c s s′} → BufferStep server cs sc ob cs′ sc′ →
    Server._⇒⟨_⟩_ s (one ob) s′ →
    R._⇒⟨_⟩_ (R.paired c s cs sc) (tag server ob) (R.paired c s′ cs′ sc′)
  advance-server unchanged run with empty-local server run
  ... | refl = R.done
  advance-server sentS run = R.vis (R.serverSend (single-local server run)) R.done
  advance-server recvS run = R.vis (R.serverRecv (single-local server run)) R.done

  module _ (cl sl : Link) (cd sd : Dir) where
    module C = B k cl cd
    module S = B k sl sd

    -- Relate actual composed residuals to both local simulations and FIFO views.
    data Rel : PTree PairEv PairI ⊤ → R.State → Set₁ where
      linked : ∀ {c s cs ss q} → C.Rel consumer c cs → S.Rel producer s ss →
        Rel (compose c s q) (R.paired cs ss (queue (clientToServer q)) (queue (serverToClient q)))

    -- Product silent transitions are exactly original silent peer transitions.
    sim-τ : ∀ {T T′ s} → Rel T s → T Pair.─[ Pair.τ ]─► T′ →
      Σ[ s′ ∈ R.State ] (R._⇒⟨_⟩_ s [] s′ × Rel T′ s′)
    sim-τ (linked cr sr) st with silent-inv st
    ... | c′ , s′ , clientτ local , refl with C.simTau cr local
    ...   | cs′ , run , cr′ with empty-local client run
    ...     | refl = _ , R.done , linked cr′ sr
    sim-τ (linked cr sr) st | c′ , s′ , serverτ local , refl with S.simTau sr local
    ... | ss′ , run , sr′ with empty-local server run
    ...   | refl = _ , R.done , linked cr sr′

    -- Full payload equality at the medium entails exact-field FIFO consistency.
    sim-ev : ∀ {T T′ s e} → Rel T s → T Pair.─[ Pair.ev (Pair.evl e) ]─► T′ →
      Σ[ es ∈ List (Role × N.E) ] Σ[ s′ ∈ R.State ] (Obs (e ∷ []) es × R._⇒⟨_⟩_ s es s′ × Rel T′ s′)
    sim-ev (linked cr sr) st with visible-inv st
    ... | c′ , s′ , q′ , client {ch = ch} {a = a} local gate , refl with C.simEv cr local
    ...   | es , cs′ , obs , run , cr′ = _ , _ , obs-client ch a ,
      advance-client (client-gate-sound _ gate) (normalize client run obs) , linked cr′ sr
    sim-ev (linked cr sr) st | c′ , s′ , q′ , server {ch = ch} {a = a} local gate , refl with S.simEv sr local
    ... | es , ss′ , obs , run , sr′ = _ , _ , obs-server ch a ,
      advance-server (server-gate-sound _ gate) (normalize server run obs) , linked cr sr′

    -- The paired replay model simulates the actual asynchronous peer product.
    simulation : Bridge.Sim R.model classify id Rel
    simulation = record { sim-τ = sim-τ ; sim-ev = sim-ev }

    -- Both supplied peers are the native depth-k pipeline extension.
    system : PTree PairEv PairI ⊤
    system = pipelined-system k cl sl cd sd

    -- Every observed concrete composed trace is legal in paired replay.
    sound : ∀ {t T es} → system ⟹∖√⟨ t ⟩ T → Obs t es → R.HasTrace R.initial es
    sound {es = es} run obs with Bridge.sound R.model classify id simulation
      (linked (C.at C.ready) (S.at S.ready)) run
    ... | es′ , s′ , obs′ , replay , _ = s′ , subst (λ t → R._⇒⟨_⟩_ R.initial t s′)
      (trans (sym (map-id es′)) (trans (sym obs′) (trans obs (map-id es)))) replay
