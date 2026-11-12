{-# OPTIONS --guardedness #-}

-- Positive instances of restated c2, including the nonempty foreign residue.
-- All ownership and pending-result conclusions come from the endpoint theorem.
module ConnectionManagement.Negative.ForeignFramesFixture where

open import Data.Bool using (true)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain using (ident)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
open Protocols.StartTrace.ScopedCM.Completion using (serverFinished)
import ConnectionManagement.Negative.PoolRelays as Relays
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
import ConnectionManagement.Negative.ForeignCallerResidue as Residue
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.ForeignFrames as C2
import ConnectionManagement.Rules.PoolRelays as RR
private
  module K = Combined I.bearerClosed Prior.classify
  module T = K.Protocols Protocols.capability
open Frames I.bearerClosed Prior.classify using (Foreign)
open C2.Protocols I.bearerClosed Prior.classify Protocols.capability using (ForeignFrames; foreign-frames)

-- The scheduled outer close used by the c1 fixture satisfies restated c2.
scheduled-close : ForeignFrames serverFinished
scheduled-close = foreign-frames {scheduled = true} {t = just RR.joined}
  Protocols.initializer Relays.Initialized.initialized-relays-close

-- The inserted foreign caller's entire initialized outer run is also covered.
foreign-close : ForeignFrames Residue.final
foreign-close = foreign-frames {scheduled = true} {t = just RR.joined}
  Protocols.initializer Residue.initialized-close

-- Presence of the surviving frame gives the pending result and Foreign worker.
surviving-caller : lookup (ident 900) (O.acquired (T.sourceOf Residue.final)) ≡ nothing ×
  Foreign (ident 900) (K.context (T.base Residue.final))
surviving-caller = ForeignFrames.acquiring foreign-close Residue.foreignWorker Residue.foreignFrame Residue.frame-left

-- In particular, ident 900 is foreign by the universal endpoint theorem.
foreign-worker : Foreign (ident 900) (K.context (T.base Residue.final))
foreign-worker = proj₂ surviving-caller
