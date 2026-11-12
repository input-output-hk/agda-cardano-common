{-# OPTIONS --guardedness #-}

-- Restated c2: at a completed initialized outer shutdown, every retained CM
-- acquiring/releasing frame is foreign to both historical peer-owner tables.
-- Both empty-result consequences are retained. This is a finite-run safety
-- theorem, with no eventual-shutdown or implementation-fidelity claim.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ForeignFrames
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import ConnectionManagement.Domain using (HandleId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerPeersRelays as Relays
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesRuntimeSelection as LiftFacts
import ConnectionManagement.Properties.ServerPeers as SharedFacts
import ConnectionManagement.Properties.PeerSupervision as PeerFacts
import ConnectionManagement.Properties.ServerShutdownComplete as ShutdownFacts
import ConnectionManagement.Properties.JobPoolLive as LiveFacts
open Frames isBearerClosed isIOManagerError using
  (module K; module PS; module GP; module C; Foreign; Owner; JobAwait; FollowAwait; acquire-owner; release-owner)
private
  module E = Exit isBearerClosed
  module Facts = SharedFacts isBearerClosed isIOManagerError
  module Peers = PeerFacts isIOManagerError
  module GLive = LiveFacts GP.Body true
  module MLive = LiveFacts (Maybe ErrorId) false
  module SR = Relays isBearerClosed isIOManagerError

-- All historical handles, including those outside a close snapshot, are dead.
record Dead (k : C.Context) : Set where
  field
    governor-dead : ∀ j → GLive.live (lookup j (GP.Pool.handles (C.governorPool k))) ≡ false
    monitor-dead : ∀ j → MLive.live (lookup j (PS.Pool.handles (C.monitorPool k))) ≡ false

-- A running physical handle contradicts closed-dead, leaving exactly Foreign.
owner-foreign : ∀ k → Dead k → ∀ w pc → Owner w pc k → Foreign w k
owner-foreign k dead w pc (inj₁ foreign) = foreign
owner-foreign k dead w pc (inj₂ (inj₁ job)) = case trans
  (sym (cong GLive.live (JobAwait.running job))) (Dead.governor-dead dead (JobAwait.job job)) of λ ()
owner-foreign k dead w pc (inj₂ (inj₂ follow)) = case trans
  (sym (cong MLive.live (FollowAwait.running follow))) (Dead.monitor-dead dead (FollowAwait.tid follow)) of λ ()

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  private
    module T = K.Protocols canInitiate
    module Outer = SR.Protocols canInitiate
    module Runtime = Facts.Protocols canInitiate
  open LiftFacts.Protocols isBearerClosed isIOManagerError canInitiate using (runs-inv; initial-inv)
  open ShutdownFacts.Protocols isBearerClosed isIOManagerError canInitiate using (Complete; complete; outer-runs)

  -- Reuse the real pool/scope executions, now rooted at the initialized pools.
  initial-paths : ∀ c g {s as t} → T.initialize c g ≡ just s → T.Runs s as t →
    Peers.Paths (Peers.view (PS.initial c g)) (Facts.view (T.base t))
  initial-paths c g initialized path with E.initial c
  ... | nothing = case initialized of λ ()
  ... | just e with just-injective initialized
  ...   | refl = Runtime.run-projects path

  -- SI5's peerClosed plus those executions closes both pools from their initial
  -- states; no extra pool-reachability premise is required of the endpoint.
  closed-dead : ∀ {c g start as final} → T.initialize c g ≡ just start → T.Runs start as final →
    K.peerClosed (T.base final) ≡ true → Dead (K.context (T.base final))
  closed-dead {c} {g} {final = final} initialized path closed with
    initial-paths c g initialized path | Facts.closure-observation (T.base final) closed
  ... | Peers.paths (ga , gp) (ma , mp) (sa , sp) | gov , mon , scopes = record
    { governor-dead = GLive.closed-dead gp gov
    ; monitor-dead = MLive.closed-dead mp mon }

  -- Frame presence entails both the pending result cell and foreign ownership.
  record ForeignFrames (final : T.Runtime) : Set where
    field
      acquiring : ∀ w f → lookup w (O.acquiring (T.sourceOf final)) ≡ just f →
        lookup w (O.acquired (T.sourceOf final)) ≡ nothing × Foreign w (K.context (T.base final))
      releasing : ∀ w f → lookup w (O.releasing (T.sourceOf final)) ≡ just f →
        lookup w (O.released (T.sourceOf final)) ≡ nothing × Foreign w (K.context (T.base final))

  -- Every initialized completed outer run satisfies the approved restated c2.
  foreign-frames : ∀ {c₀ g start scheduled as final t} → T.initialize (O.initial c₀) g ≡ just start →
    Outer.Executes (Outer.outer start (RR.initial scheduled)) as (Outer.outer final (RR.relaysState t RR.finished)) →
    ForeignFrames final
  foreign-frames {c₀} {g} {final = final} initialized path with outer-runs path | complete initialized path
  ... | events , inner | certificate = record
    { acquiring = λ w f found → let pending , owner = acquire-owner (T.base final) held w f found
      in pending , owner-foreign (K.context (T.base final)) dead w _ owner
    ; releasing = λ w f found → let pending , owner = release-owner (T.base final) held w f found
      in pending , owner-foreign (K.context (T.base final)) dead w _ owner }
    where
    held = proj₁ (runs-inv inner (initial-inv c₀ g initialized))
    dead = closed-dead initialized inner (Complete.peerClosed certificate)
