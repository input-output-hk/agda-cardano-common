{-# OPTIONS --guardedness #-}

-- K's actual allocation guards imply the caller freshness required by birth.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesFresh
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesCore as Core
import ConnectionManagement.Properties.OwnedFramesJobBirth as Birth
open Frames isBearerClosed isIOManagerError
private
  module S = Server isBearerClosed
  module E = Exit isBearerClosed
  module B = Core isBearerClosed isIOManagerError
  module F = Birth isBearerClosed isIOManagerError

-- The middle conjunct of K.fresh is the actual physical peer freshness guard.
fresh-peer : ∀ w s → K.fresh w s ≡ true → PS.freshWorker w (K.peers s) ≡ true
fresh-peer w s permit = proj₁ (B.and-true (PS.freshWorker w (K.peers s)) (K.acquireChildFree w (O.acquiring (K.source s)))
  (proj₂ (B.and-true (S.fresh w (E.base (K.server s)))
    (PS.freshWorker w (K.peers s) ∧ K.acquireChildFree w (O.acquiring (K.source s))) permit)))

-- Establishing jobs use the stronger two-actor/socket guard, which includes it.
actors-fresh : ∀ w child sock s → K.newActors w child sock s ≡ true → K.fresh w s ≡ true
actors-fresh w child sock s permit with w ≟ child | lookup sock (Shared.sockets (S.shared (E.base (K.server s))))
... | no apart | nothing = proj₁ (B.and-true (K.fresh w s) (K.fresh child s ∧ K.peerSocketFree sock s) permit)
... | yes same | socket = case permit of λ ()
... | no apart | just socket = case permit of λ ()

-- Every successful forkJobAllowed branch requires its caller to be K.fresh.
fork-fresh : ∀ w child sock s → K.forkJobAllowed w child sock s ≡ true → K.fresh w s ≡ true
fork-fresh w child sock s permit with Sub.pc (PS.machine (K.peers s))
... | Sub.launch (work ∷ rest) with G.kind work
...   | G.establish = actors-fresh w child sock s permit
...   | G.forget = permit
...   | G.activate = permit
...   | G.close = permit
...   | G.deactivate = permit
fork-fresh w child sock s permit | Sub.publishPublic = case permit of λ ()
fork-fresh w child sock s permit | Sub.sampleInputs = case permit of λ ()
fork-fresh w child sock s permit | Sub.prepareWait = case permit of λ ()
fork-fresh w child sock s permit | Sub.selecting = case permit of λ ()
fork-fresh w child sock s permit | (Sub.cancelTimer selected) = case permit of λ ()
fork-fresh w child sock s permit | (Sub.apply selected) = case permit of λ ()
fork-fresh w child sock s permit | (Sub.publishView work) = case permit of λ ()
fork-fresh w child sock s permit | (Sub.traceDecision work) = case permit of λ ()
fork-fresh w child sock s permit | (Sub.launch []) = case permit of λ ()
fork-fresh w child sock s permit | (Sub.register j rest) = case permit of λ ()
fork-fresh w child sock s permit | (Sub.completionAssertionFailed result) = case permit of λ ()

-- This is the complete caller certificate consumed by the logical birth proof.
fork-free : ∀ w child sock s → K.peerAllowed (PS.run (GP.run (Sub.forkJob w child sock))) s ≡ true →
  F.Free w (K.source s) (K.context s)
fork-free w child sock s permit = F.fresh-worker w (K.peers s) (fresh-peer w s (fork-fresh w child sock s permit))
