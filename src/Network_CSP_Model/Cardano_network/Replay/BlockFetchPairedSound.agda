{-# OPTIONS --guardedness #-}

-- Simulation from the existing full-payload peer/FIFO product to paired replay.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.BlockFetchPairedSound (p : Params) where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map)
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
open import Cardano_network.BlockFetch p using (BFEv; stIdle)
import Cardano_network.BlockFetchPipe p as Pipe
open import Cardano_network.Replay.Common
open import Cardano_network.Replay.BlockFetchPairedModel p
open import Cardano_network.Replay.BlockFetchPairedParts p
open import Cardano_network.Replay.BlockFetchPairedPackets p using (queue; BufferStep; unchanged; sentC; recvC; sentS; recvS; client-gate-sound; server-gate-sound)
import Cardano_network.Replay.BlockFetchClientSession as Ctl
import Cardano_network.Replay.BlockFetchPairedSession as Paired
import Cardano_network.Replay.BlockFetchClientBridge p as C
import Cardano_network.Replay.BlockFetchServerSession as ServerCtl
import Cardano_network.Replay.BlockFetchPairedLocal as Wire
import Cardano_network.Replay.BlockFetchServerBridge p as S
import Semantics.LTS {E = BFEv} {I = ExtI BFEv} as Local
import Semantics.LTS {E = PairEv} {I = PairI} as Pair
open import Semantics.Deadlock {E = PairEv} {I = PairI} using (_⟹∖√⟨_⟩_)
import Semantics.Replay.Bridge {E = PairEv} {I = PairI} as Bridge

-- The final observation retains endpoint, wire direction and retained control shape.
classify : Pair.Event → Maybe (Role × Ctl.E)
classify (Pair.evLabel X (atClient ch) a) = mapM (client ,_) (C.cls (Local.evLabel X ch a))
classify (Pair.evLabel X (atServer ch) a) = mapM (server ,_) (S.cls (Local.evLabel X ch a))

-- Compare finite traces after erasing APIs and unretained payload fields.
Obs : List Pair.Event → List (Role × Ctl.E) → Set
Obs = Bridge.Obs classify id

-- One optional local observation gives zero or one replay events.
one : Maybe Ctl.E → List Ctl.E
one nothing = []
one (just e) = e ∷ []

-- Endpoint tagging preserves all retained control distinctions.
tag : Role → Maybe Ctl.E → List (Role × Ctl.E)
tag r nothing = []
tag r (just e) = (r , e) ∷ []

-- A concrete client event has exactly its endpoint-tagged observation.
obs-client : ∀ {X} (ch : BFEv X) a → Obs (Pair.evLabel X (atClient ch) a ∷ [])
  (tag client (C.cls (Local.evLabel X ch a)))
obs-client ch a with C.cls (Local.evLabel _ ch a)
... | nothing = refl
... | just e = refl

-- The server observation obeys the same rule independently of peer state.
obs-server : ∀ {X} (ch : BFEv X) a → Obs (Pair.evLabel X (atServer ch) a ∷ [])
  (tag server (S.cls (Local.evLabel X ch a)))
obs-server ch a with S.cls (Local.evLabel _ ch a)
... | nothing = refl
... | just e = refl

module _ (k : ℕ) where
  module R = Paired k
  module Client = Ctl.Spec k
  module Server = ServerCtl

  -- With no local silent moves, an empty client trace preserves its state.
  empty-client : ∀ {s s′} → Client._⇒⟨_⟩_ s [] s′ → s ≡ s′
  empty-client Client.done = refl
  empty-client (Client.tau () _)

  -- The sequential server likewise has no wire-level silent transitions.
  empty-server : ∀ {s s′} → Server._⇒⟨_⟩_ s [] s′ → s ≡ s′
  empty-server Server.done = refl
  empty-server (Server.tau () _)

  -- A singleton client trace contains exactly one original protocol step.
  single-client : ∀ {s s′ e} → Client._⇒⟨_⟩_ s (e ∷ []) s′ → Ctl.Step k s e s′
  single-client (Client.tau () _)
  single-client (Client.vis pr rest) with empty-client rest
  ... | refl = pr

  -- The analogous server fact retains the original inductive transition.
  single-server : ∀ {s s′ e} → Server._⇒⟨_⟩_ s (e ∷ []) s′ → Server.Step s e s′
  single-server (Server.tau () _)
  single-server (Server.vis pr rest) with empty-server rest
  ... | refl = pr

  -- Remove the identity-map noise in the existing client observation theorem.
  normalize-client : ∀ {s s′ es e} → Client._⇒⟨_⟩_ s es s′ → C.Obs (e ∷ []) es →
    Client._⇒⟨_⟩_ s (one (C.cls e)) s′
  normalize-client {es = es} {e} run obs with C.cls e
  ... | nothing = subst (λ t → Client._⇒⟨_⟩_ _ t _) (trans (sym (map-id es)) (sym obs)) run
  ... | just e′ = subst (λ t → Client._⇒⟨_⟩_ _ t _) (trans (sym (map-id es)) (sym obs)) run

  -- The server uses the same event classifier but its own local state type.
  normalize-server : ∀ {s s′ es e} → Server._⇒⟨_⟩_ s es s′ → S.Obs (e ∷ []) es →
    Server._⇒⟨_⟩_ s (one (S.cls e)) s′
  normalize-server {es = es} {e} run obs with S.cls e
  ... | nothing = subst (λ t → Server._⇒⟨_⟩_ _ t _) (trans (sym (map-id es)) (sym obs)) run
  ... | just e′ = subst (λ t → Server._⇒⟨_⟩_ _ t _) (trans (sym (map-id es)) (sym obs)) run

  -- Local client legality and packet matching jointly give a paired step.
  advance-client : ∀ {cs sc cs′ sc′ ob c c′ s} → BufferStep client cs sc ob cs′ sc′ →
    Client._⇒⟨_⟩_ c (one ob) c′ →
    R._⇒⟨_⟩_ (R.paired (R.clientS c) (R.serverS s) cs sc) (tag client ob)
      (R.paired (R.clientS c′) (R.serverS s) cs′ sc′)
  advance-client unchanged run with empty-client run
  ... | refl = R.done
  advance-client sentC run = R.vis (R.clientSend (Wire.client-complete k (single-client run))) R.done
  advance-client recvC run = R.vis (R.clientRecv (Wire.client-complete k (single-client run))) R.done

  -- The server adapter preserves the same exact packet movement.
  advance-server : ∀ {cs sc cs′ sc′ ob c s s′} → BufferStep server cs sc ob cs′ sc′ →
    Server._⇒⟨_⟩_ s (one ob) s′ →
    R._⇒⟨_⟩_ (R.paired (R.clientS c) (R.serverS s) cs sc) (tag server ob)
      (R.paired (R.clientS c) (R.serverS s′) cs′ sc′)
  advance-server unchanged run with empty-server run
  ... | refl = R.done
  advance-server sentS run = R.vis (R.serverSend (Wire.server-complete k (single-server run))) R.done
  advance-server recvS run = R.vis (R.serverRecv (Wire.server-complete k (single-server run))) R.done

  module _ (cl sl : Link) (cd sd : Dir) where
    -- Relate actual composed residuals to both local simulations and FIFO views.
    data Rel : PTree PairEv PairI ⊤ → R.State → Set₁ where
      linked : ∀ {c s cs ss q} → C.Rel k cl cd c cs → S.Rel sl sd s ss →
        Rel (compose c s q) (R.paired (R.clientS cs) (R.serverS ss) (queue (clientToServer q)) (queue (serverToClient q)))

    -- Product silent transitions are exactly original silent peer transitions.
    sim-τ : ∀ {T T′ s} → Rel T s → T Pair.─[ Pair.τ ]─► T′ →
      Σ[ s′ ∈ R.State ] (R._⇒⟨_⟩_ s [] s′ × Rel T′ s′)
    sim-τ (linked cr sr) st with silent-inv st
    ... | c′ , s′ , clientτ local , refl with C.sim-τ k cl cd cr local
    ...   | cs′ , run , cr′ with empty-client run
    ...     | refl = _ , R.done , linked cr′ sr
    sim-τ (linked cr sr) st | c′ , s′ , serverτ local , refl with S.sim-τ sl sd sr local
    ... | ss′ , run , sr′ with empty-server run
    ...   | refl = _ , R.done , linked cr sr′

    -- Full payload equality at the medium entails control-FIFO consistency.
    sim-ev : ∀ {T T′ s e} → Rel T s → T Pair.─[ Pair.ev (Pair.evl e) ]─► T′ →
      Σ[ es ∈ List (Role × Ctl.E) ] Σ[ s′ ∈ R.State ] (Obs (e ∷ []) es × R._⇒⟨_⟩_ s es s′ × Rel T′ s′)
    sim-ev (linked cr sr) st with visible-inv st
    ... | c′ , s′ , q′ , client {ch = ch} {a = a} local gate , refl with C.sim-ev k cl cd cr local
    ...   | es , cs′ , obs , run , cr′ = _ , _ , obs-client ch a ,
      advance-client (client-gate-sound _ gate) (normalize-client run obs) , linked cr′ sr
    sim-ev (linked cr sr) st | c′ , s′ , q′ , server {ch = ch} {a = a} local gate , refl with S.sim-ev sl sd sr local
    ... | es , ss′ , obs , run , sr′ = _ , _ , obs-server ch a ,
      advance-server (server-gate-sound _ gate) (normalize-server run obs) , linked cr sr′

    -- The paired replay model simulates the actual asynchronous peer product.
    simulation : Bridge.Sim R.model classify id Rel
    simulation = record { sim-τ = sim-τ ; sim-ev = sim-ev }

    -- The source contains the original pipeline and original sequential server.
    system : PTree PairEv PairI ⊤
    system = compose (Pipe.client k cl cd) (Pipe.server sl sd) empty

    -- Every observed concrete composed trace is legal in paired replay.
    sound : ∀ {t T es} → system ⟹∖√⟨ t ⟩ T → Obs t es → R.HasTrace R.initial es
    sound {es = es} run obs with Bridge.sound R.model classify id simulation
      (linked (C.head Pipe.initial) (S.head {a = stIdle})) run
    ... | es′ , s′ , obs′ , replay , _ = s′ , subst (λ t → R._⇒⟨_⟩_ R.initial t s′)
      (trans (sym (map-id es′)) (trans (sym obs′) (trans obs (map-id es)))) replay


    -- Every observed joint execution yields a certificate without payload premises.
    model-certificate : ∀ {t T es cs ss} → system ⟹∖√⟨ t ⟩ T → Obs t es →
      R.project client es ≡ cs → R.project server es ≡ ss → R.Witness R.initial cs ss
    model-certificate {es = es} run obs co so = R.witness es co so (sound run obs)
