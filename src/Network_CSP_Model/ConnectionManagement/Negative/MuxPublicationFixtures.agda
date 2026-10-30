{-# OPTIONS --guardedness #-}

-- Data-only pre-publication snapshots. Acceptance proves every initialized
-- transition; these builders do not adopt a physical handler or supply a run.
module ConnectionManagement.Negative.MuxPublicationFixtures where

open import Data.Bool using (Bool)
import Data.Nat as Nat
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (does)
open import ConnectionManagement.Domain
import ConnectionManagement.Negative.MuxProtocolFixtures as Proto
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.OutboundMachine as O

-- Same fixture exception classification as the existing mux acceptance tests.
bearerClosed : ErrorId → Bool
bearerClosed err = does (ErrorId.errorNumber err Nat.≟ 999)
module N = Publication bearerClosed
module C = N.C
module D = N.D
module R = N.R
module W = N.W
module G = N.G
module M = N.M
module P = N.P
module U = N.U
module S = N.S
module Prior = Proto.Prior
module Fixture = Proto.Fixture
module F = Proto.F
owner : WorkerId
owner = Fixture.child
mid : MuxId
mid = Proto.G.mid

delta : P.State → D.State
delta p = D.deltaQState (R.unwinding
  (W.handlerExitState (G.shutdownState (M.monitorState p []) []) []) []) []
b0 : P.State
b0 = P.protocolState Proto.q₀ [] []
b1 : P.State
b1 = P.protocolState Proto.q1 [] []
b2 : P.State
b2 = P.protocolState Proto.q2 [] []
b3 : P.State
b3 = P.protocolState Proto.q3 [] []
b4 : P.State
b4 = P.protocolState Proto.q4 [] []
b5 : P.State
b5 = P.protocolState Proto.q5 [] []
b6 : P.State
b6 = P.protocolState Proto.q6 [] []
b7 : P.State
b7 = P.protocolState Proto.q7 [] []
b8 : P.State
b8 = P.protocolState Proto.q8 [] []
b9 : P.State
b9 = P.protocolState Proto.q9 [] []
b10 : P.State
b10 = P.protocolState Proto.q10 [] []
b11 : P.State
b11 = P.protocolState Proto.q11 [] []
b12 : P.State
b12 = P.protocolState Proto.q12 [] []
b13 b14 b15 : P.State
b13 = P.protocolState (U.supervised Prior.p12 Proto.born
  ((owner , U.frame Prior.captured outbound Proto.ps duplex U.returnedSuccess S.initial) ∷ [])) [] []
b14 = P.protocolState (U.supervised Proto.allocatedBase Proto.born
  ((owner , U.frame Prior.captured outbound Proto.ps duplex (U.handleAllocated (ident 0) mid) S.initial) ∷ [])) [] []
b15 = P.protocolState (U.supervised Proto.publishedBase Proto.born
  ((owner , U.frame Prior.captured outbound Proto.ps duplex (U.promisePublished (ident 0) mid)
    (S.startupState S.published S.Pool.initial)) ∷ [])) [] []
