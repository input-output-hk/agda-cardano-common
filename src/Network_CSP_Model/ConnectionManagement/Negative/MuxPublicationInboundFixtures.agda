{-# OPTIONS --guardedness #-}

-- Data-only inbound birth/negotiation snapshots. The acceptance module proves
-- every admission/fork step; none of these builders supplies a physical history.
module ConnectionManagement.Negative.MuxPublicationInboundFixtures where

open import Data.Bool using (Bool)
import Data.Nat as Nat
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (does)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes using (Protocol; protocol; hot; onDemand)
import ConnectionManagement.CSP.Fixtures as Source
import ConnectionManagement.Machine as Machine
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Rules.CMShutdown as Close
open import ConnectionManagement.Scenarios.Admission using (w₀; child₀; key₀)

bearerClosed : ErrorId → Bool
bearerClosed err = does (ErrorId.errorNumber err Nat.≟ 999)
private
  module N = Publication bearerClosed
  module P = N.P
  module U = N.U
  module S = N.S
owner : WorkerId
owner = child₀
captured : Shared.HandlerStart
captured = Shared.handlerStart (ident 0) (ident 0) (ident 0) key₀
ps : List Protocol
ps = protocol 1 hot onDemand ∷ []
successFrame : U.Frame
successFrame = U.frame captured inbound ps duplex U.returnedSuccess S.initial

-- Separate pre-fork and post-fork records make the historical birth explicit.
pre : Machine.Configuration → P.State
pre c = P.protocolState (U.supervised (B.supervised (O.initial c) [] Close.initialState) [] []) [] []
born : Machine.Configuration → H.Phase → P.State
born c pc = P.protocolState (U.supervised
  (B.supervised (O.initial c) ((owner , H.handlerThread captured pc) ∷ []) Close.initialState)
  ((owner , inbound) ∷ []) []) [] []
p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : P.State
p0 = pre Source.start
p1 = pre (Source.pre (Shared.cmStore (Shared.taken w₀) [] 0) (Shared.count Source.parentLease) [] 0)
p2 = pre (Source.pre (Shared.cmStore (Shared.taken w₀) [] 0) (Shared.prepare Source.parentLease) [] 0)
p3 = pre (Source.pre (Shared.cmStore (Shared.taken w₀) [] 0)
  (Shared.selectEntry Source.parentLease (ident 0)) (ident 0 ∷ []) 1)
p4 = pre (Source.pre (Shared.cmStore (Shared.taken w₀) ((ident 0 , Source.unneg) ∷ []) 1)
  (Shared.forkHandler Source.parentLease (ident 0) (ident 0)) (ident 0 ∷ []) 1)
p5 = born (Source.snapshot Source.unneg (Shared.taken w₀)
  (Shared.publish Source.parentLease (ident 0) (ident 0)) (Shared.handling owner) [] [] []) H.maskedSetup
p6 = born (Source.snapshot Source.unneg (Shared.full Source.binding)
  (Shared.countPublished (ident 0) (ident 0)) (Shared.handling owner) [] [] []) H.maskedSetup
p7 = born Source.waiting H.maskedSetup
p8 = born Source.waiting H.handshaking
p9 = P.protocolState (record (P.base p8) { frames = (owner , successFrame) ∷ [] }) [] []
