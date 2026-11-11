{-# OPTIONS --guardedness #-}

-- Residue c2 counterexample. "No outbound acquire or release frame is left at
-- the end of the outer shutdown" is false in the model: a foreign CM caller,
-- a worker owned by no peer job or monitor, may begin an outbound acquire
-- while the peer side is open (ServerPeers.coreAllowed). No shutdown gate
-- inspects O.acquiring, and only the caller's own return or a job/monitor
-- cancellation deletes a frame, so the frame survives the whole scheduled
-- close of Negative/PoolRelays. Every edge after the inserted begin is the
-- fixture's own event, re-checked on the state carrying the extra frame. The
-- SI5b certificate and residue c1 still hold at the end.
module ConnectionManagement.Negative.ForeignCallerResidue where

open import Data.Bool using (true)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (WorkerId; ident; remote; outbound)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
import ConnectionManagement.Negative.PoolRelays as Relays
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Rules.OutboundAcquire as Acquire
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerPeersRelays as RelaysModel
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.Scenarios.Admission as Actors
import ConnectionManagement.Properties.PoolRelays as RelaysProof
import ConnectionManagement.Properties.ServerShutdownCoordinator as SI5
import ConnectionManagement.Properties.IGPendingQuiet as C1
private
  module K = Combined I.bearerClosed Prior.classify
  module C = Context Prior.classify
  module X = RelaysModel.Protocols I.bearerClosed Prior.classify Protocols.capability
  module V = X.V
  module Cert = RelaysProof.Certified X.V.advance X.runtimeReturned
  module Trace = Protocols.StartTrace
  module Scoped = Trace.ScopedCM
  module Done = Scoped.Completion
  module Shutdown = SI5 I.bearerClosed Prior.classify
  module Certificate = Shutdown.Protocols Protocols.capability
  module Residue = C1 I.bearerClosed Prior.classify
  module Quiet = Residue.Protocols Protocols.capability

-- The foreign caller and its request use identifiers unused by the fixture.
foreignWorker foreignChild : WorkerId
foreignWorker = ident 900
foreignChild = ident 901
foreignRequest : Acquire.Request
foreignRequest = Acquire.acquireRequest (remote Actors.key₁) foreignChild (ident 902) outbound nothing
foreignFrame : Acquire.Frame
foreignFrame = Acquire.frame foreignRequest Acquire.selecting

-- The fixture state plus the frame and cancellation region that the begin
-- step writes; both are appended, as put does for a fresh key.
foreign : V.Runtime → V.Runtime
foreign s = record s { base = K.combined (K.setSource source′ (K.server b))
  (record (K.context b) { regions = C.regions (K.context b) ++ ((foreignWorker , Cancel.ordinary) ∷ []) }) }
  where
  b = V.base s
  source = K.source b
  source′ = record source { acquiring = O.acquiring source ++ ((foreignWorker , foreignFrame) ∷ []) }

-- Index projections of an existing run, so fixture names need not be restated.
endOf : ∀ {s as t} → V.Runs s as t → V.Runtime
endOf {t = t} _ = t
eventsOf : ∀ {s as t} → V.Runs s as t → List V.Event
eventsOf {as = as} _ = as

-- The last fixture state before the peer scopes unwind; the peer side is open.
start : V.Runtime
start = endOf Trace.tracePrefix
foreignEvent : V.Event
foreignEvent = V.dispatch (K.coreStep (O.beginAcquire foreignWorker foreignRequest))
begin : V.advance foreignEvent start ≡ just (foreign start)
begin = refl

-- Each fixture edge fixes its target once its event and source are given.
targetOf : ∀ e s {s′} → V.advance e s ≡ just s′ → V.Runtime
targetOf e s {s′} _ = s′

suffixActions : List V.Event
suffixActions = Scoped.peerScopeActions ++ Scoped.serverScopeActions ++ Scoped.cmReceiptActions ++
  Scoped.physicalActions ++ Scoped.scopedCatchActions ++ Done.finishActions

-- The k-th event of the replayed suffix.
nth : ℕ → List V.Event → V.Event
nth _ [] = foreignEvent
nth zero (e ∷ _) = e
nth (suc k) (_ ∷ es) = nth k es
event : ℕ → V.Event
event k = nth k suffixActions

s1 : V.Runtime
s1 = targetOf (event 0) start Scoped.peerEdge1
f1 : V.advance (event 0) (foreign start) ≡ just (foreign s1)
f1 = refl
s2 : V.Runtime
s2 = targetOf (event 1) s1 Scoped.peerEdge2
f2 : V.advance (event 1) (foreign s1) ≡ just (foreign s2)
f2 = refl
s3 : V.Runtime
s3 = targetOf (event 2) s2 Scoped.peerEdge3
f3 : V.advance (event 2) (foreign s2) ≡ just (foreign s3)
f3 = refl
s4 : V.Runtime
s4 = targetOf (event 3) s3 Scoped.peerEdge4
f4 : V.advance (event 3) (foreign s3) ≡ just (foreign s4)
f4 = refl
s5 : V.Runtime
s5 = targetOf (event 4) s4 Scoped.peerEdge5
f5 : V.advance (event 4) (foreign s4) ≡ just (foreign s5)
f5 = refl
s6 : V.Runtime
s6 = targetOf (event 5) s5 Scoped.peerEdge6
f6 : V.advance (event 5) (foreign s5) ≡ just (foreign s6)
f6 = refl
s7 : V.Runtime
s7 = targetOf (event 6) s6 Scoped.peerEdge7
f7 : V.advance (event 6) (foreign s6) ≡ just (foreign s7)
f7 = refl
s8 : V.Runtime
s8 = targetOf (event 7) s7 Scoped.peerEdge8
f8 : V.advance (event 7) (foreign s7) ≡ just (foreign s8)
f8 = refl
s9 : V.Runtime
s9 = targetOf (event 8) s8 Scoped.peerEdge9
f9 : V.advance (event 8) (foreign s8) ≡ just (foreign s9)
f9 = refl
s10 : V.Runtime
s10 = targetOf (event 9) s9 Scoped.peerEdge10
f10 : V.advance (event 9) (foreign s9) ≡ just (foreign s10)
f10 = refl
s11 : V.Runtime
s11 = targetOf (event 10) s10 Scoped.peerEdge11
f11 : V.advance (event 10) (foreign s10) ≡ just (foreign s11)
f11 = refl
s12 : V.Runtime
s12 = targetOf (event 11) s11 Scoped.peerEdge12
f12 : V.advance (event 11) (foreign s11) ≡ just (foreign s12)
f12 = refl
s13 : V.Runtime
s13 = targetOf (event 12) s12 Scoped.peerEdge13
f13 : V.advance (event 12) (foreign s12) ≡ just (foreign s13)
f13 = refl
s14 : V.Runtime
s14 = targetOf (event 13) s13 Scoped.peerEdge14
f14 : V.advance (event 13) (foreign s13) ≡ just (foreign s14)
f14 = refl
s15 : V.Runtime
s15 = targetOf (event 14) s14 Scoped.peerEdge15
f15 : V.advance (event 14) (foreign s14) ≡ just (foreign s15)
f15 = refl
s16 : V.Runtime
s16 = targetOf (event 15) s15 Scoped.peerEdge16
f16 : V.advance (event 15) (foreign s15) ≡ just (foreign s16)
f16 = refl
s17 : V.Runtime
s17 = targetOf (event 16) s16 Scoped.peerEdge17
f17 : V.advance (event 16) (foreign s16) ≡ just (foreign s17)
f17 = refl
s18 : V.Runtime
s18 = targetOf (event 17) s17 Scoped.peerEdge18
f18 : V.advance (event 17) (foreign s17) ≡ just (foreign s18)
f18 = refl
s19 : V.Runtime
s19 = targetOf (event 18) s18 Scoped.peerEdge19
f19 : V.advance (event 18) (foreign s18) ≡ just (foreign s19)
f19 = refl
s20 : V.Runtime
s20 = targetOf (event 19) s19 Scoped.peerEdge20
f20 : V.advance (event 19) (foreign s19) ≡ just (foreign s20)
f20 = refl
s21 : V.Runtime
s21 = targetOf (event 20) s20 Scoped.peerEdge21
f21 : V.advance (event 20) (foreign s20) ≡ just (foreign s21)
f21 = refl
s22 : V.Runtime
s22 = targetOf (event 21) s21 Scoped.peerEdge22
f22 : V.advance (event 21) (foreign s21) ≡ just (foreign s22)
f22 = refl
s23 : V.Runtime
s23 = targetOf (event 22) s22 Scoped.peerEdge23
f23 : V.advance (event 22) (foreign s22) ≡ just (foreign s23)
f23 = refl
s24 : V.Runtime
s24 = targetOf (event 23) s23 Scoped.peerEdge24
f24 : V.advance (event 23) (foreign s23) ≡ just (foreign s24)
f24 = refl
s25 : V.Runtime
s25 = targetOf (event 24) s24 Scoped.peerEdge25
f25 : V.advance (event 24) (foreign s24) ≡ just (foreign s25)
f25 = refl
s26 : V.Runtime
s26 = targetOf (event 25) s25 Scoped.peerEdge26
f26 : V.advance (event 25) (foreign s25) ≡ just (foreign s26)
f26 = refl
s27 : V.Runtime
s27 = targetOf (event 26) s26 Scoped.peerEdge27
f27 : V.advance (event 26) (foreign s26) ≡ just (foreign s27)
f27 = refl
s28 : V.Runtime
s28 = targetOf (event 27) s27 Scoped.peerEdge28
f28 : V.advance (event 27) (foreign s27) ≡ just (foreign s28)
f28 = refl
s29 : V.Runtime
s29 = targetOf (event 28) s28 Scoped.peerEdge29
f29 : V.advance (event 28) (foreign s28) ≡ just (foreign s29)
f29 = refl
s30 : V.Runtime
s30 = targetOf (event 29) s29 Scoped.peerEdge30
f30 : V.advance (event 29) (foreign s29) ≡ just (foreign s30)
f30 = refl
s31 : V.Runtime
s31 = targetOf (event 30) s30 Scoped.peerEdge31
f31 : V.advance (event 30) (foreign s30) ≡ just (foreign s31)
f31 = refl
s32 : V.Runtime
s32 = targetOf (event 31) s31 Scoped.peerEdge32
f32 : V.advance (event 31) (foreign s31) ≡ just (foreign s32)
f32 = refl
s33 : V.Runtime
s33 = targetOf (event 32) s32 Scoped.peerEdge33
f33 : V.advance (event 32) (foreign s32) ≡ just (foreign s33)
f33 = refl
s34 : V.Runtime
s34 = targetOf (event 33) s33 Scoped.peerEdge34
f34 : V.advance (event 33) (foreign s33) ≡ just (foreign s34)
f34 = refl
s35 : V.Runtime
s35 = targetOf (event 34) s34 Scoped.peerEdge35
f35 : V.advance (event 34) (foreign s34) ≡ just (foreign s35)
f35 = refl
s36 : V.Runtime
s36 = targetOf (event 35) s35 Scoped.peerEdge36
f36 : V.advance (event 35) (foreign s35) ≡ just (foreign s36)
f36 = refl
s37 : V.Runtime
s37 = targetOf (event 36) s36 Scoped.peerEdge37
f37 : V.advance (event 36) (foreign s36) ≡ just (foreign s37)
f37 = refl
s38 : V.Runtime
s38 = targetOf (event 37) s37 Scoped.peerEdge38
f38 : V.advance (event 37) (foreign s37) ≡ just (foreign s38)
f38 = refl
s39 : V.Runtime
s39 = targetOf (event 38) s38 Scoped.peerEdge39
f39 : V.advance (event 38) (foreign s38) ≡ just (foreign s39)
f39 = refl
s40 : V.Runtime
s40 = targetOf (event 39) s39 Scoped.serverEdge1
f40 : V.advance (event 39) (foreign s39) ≡ just (foreign s40)
f40 = refl
s41 : V.Runtime
s41 = targetOf (event 40) s40 Scoped.serverEdge2
f41 : V.advance (event 40) (foreign s40) ≡ just (foreign s41)
f41 = refl
s42 : V.Runtime
s42 = targetOf (event 41) s41 Scoped.serverEdge3
f42 : V.advance (event 41) (foreign s41) ≡ just (foreign s42)
f42 = refl
s43 : V.Runtime
s43 = targetOf (event 42) s42 Scoped.serverEdge4
f43 : V.advance (event 42) (foreign s42) ≡ just (foreign s43)
f43 = refl
s44 : V.Runtime
s44 = targetOf (event 43) s43 Scoped.serverEdge5
f44 : V.advance (event 43) (foreign s43) ≡ just (foreign s44)
f44 = refl
s45 : V.Runtime
s45 = targetOf (event 44) s44 Scoped.serverEdge6
f45 : V.advance (event 44) (foreign s44) ≡ just (foreign s45)
f45 = refl
s46 : V.Runtime
s46 = targetOf (event 45) s45 Scoped.serverEdge7
f46 : V.advance (event 45) (foreign s45) ≡ just (foreign s46)
f46 = refl
s47 : V.Runtime
s47 = targetOf (event 46) s46 Scoped.serverEdge8
f47 : V.advance (event 46) (foreign s46) ≡ just (foreign s47)
f47 = refl
s48 : V.Runtime
s48 = targetOf (event 47) s47 Scoped.serverEdge9
f48 : V.advance (event 47) (foreign s47) ≡ just (foreign s48)
f48 = refl
s49 : V.Runtime
s49 = targetOf (event 48) s48 Scoped.serverEdge10
f49 : V.advance (event 48) (foreign s48) ≡ just (foreign s49)
f49 = refl
s50 : V.Runtime
s50 = targetOf (event 49) s49 Scoped.serverEdge11
f50 : V.advance (event 49) (foreign s49) ≡ just (foreign s50)
f50 = refl
s51 : V.Runtime
s51 = targetOf (event 50) s50 Scoped.serverEdge12
f51 : V.advance (event 50) (foreign s50) ≡ just (foreign s51)
f51 = refl
s52 : V.Runtime
s52 = targetOf (event 51) s51 Scoped.serverEdge13
f52 : V.advance (event 51) (foreign s51) ≡ just (foreign s52)
f52 = refl
s53 : V.Runtime
s53 = targetOf (event 52) s52 Scoped.serverEdge14
f53 : V.advance (event 52) (foreign s52) ≡ just (foreign s53)
f53 = refl
s54 : V.Runtime
s54 = targetOf (event 53) s53 Scoped.serverEdge15
f54 : V.advance (event 53) (foreign s53) ≡ just (foreign s54)
f54 = refl
s55 : V.Runtime
s55 = targetOf (event 54) s54 Scoped.serverEdge16
f55 : V.advance (event 54) (foreign s54) ≡ just (foreign s55)
f55 = refl
s56 : V.Runtime
s56 = targetOf (event 55) s55 Scoped.serverEdge17
f56 : V.advance (event 55) (foreign s55) ≡ just (foreign s56)
f56 = refl
s57 : V.Runtime
s57 = targetOf (event 56) s56 Scoped.serverEdge18
f57 : V.advance (event 56) (foreign s56) ≡ just (foreign s57)
f57 = refl
s58 : V.Runtime
s58 = targetOf (event 57) s57 Scoped.serverEdge19
f58 : V.advance (event 57) (foreign s57) ≡ just (foreign s58)
f58 = refl
s59 : V.Runtime
s59 = targetOf (event 58) s58 Scoped.serverEdge20
f59 : V.advance (event 58) (foreign s58) ≡ just (foreign s59)
f59 = refl
s60 : V.Runtime
s60 = targetOf (event 59) s59 Scoped.cmEdge1
f60 : V.advance (event 59) (foreign s59) ≡ just (foreign s60)
f60 = refl
s61 : V.Runtime
s61 = targetOf (event 60) s60 Scoped.cmEdge2
f61 : V.advance (event 60) (foreign s60) ≡ just (foreign s61)
f61 = refl
s62 : V.Runtime
s62 = targetOf (event 61) s61 Scoped.cmEdge3
f62 : V.advance (event 61) (foreign s61) ≡ just (foreign s62)
f62 = refl
s63 : V.Runtime
s63 = targetOf (event 62) s62 Scoped.cmEdge4
f63 : V.advance (event 62) (foreign s62) ≡ just (foreign s63)
f63 = refl
s64 : V.Runtime
s64 = targetOf (event 63) s63 Scoped.cmEdge5
f64 : V.advance (event 63) (foreign s63) ≡ just (foreign s64)
f64 = refl
s65 : V.Runtime
s65 = targetOf (event 64) s64 Scoped.physicalEdge1
f65 : V.advance (event 64) (foreign s64) ≡ just (foreign s65)
f65 = refl
s66 : V.Runtime
s66 = targetOf (event 65) s65 Scoped.physicalEdge2
f66 : V.advance (event 65) (foreign s65) ≡ just (foreign s66)
f66 = refl
s67 : V.Runtime
s67 = targetOf (event 66) s66 Scoped.physicalEdge3
f67 : V.advance (event 66) (foreign s66) ≡ just (foreign s67)
f67 = refl
s68 : V.Runtime
s68 = targetOf (event 67) s67 Scoped.physicalEdge4
f68 : V.advance (event 67) (foreign s67) ≡ just (foreign s68)
f68 = refl
s69 : V.Runtime
s69 = targetOf (event 68) s68 Scoped.physicalEdge5
f69 : V.advance (event 68) (foreign s68) ≡ just (foreign s69)
f69 = refl
s70 : V.Runtime
s70 = targetOf (event 69) s69 Scoped.physicalEdge6
f70 : V.advance (event 69) (foreign s69) ≡ just (foreign s70)
f70 = refl
s71 : V.Runtime
s71 = targetOf (event 70) s70 Scoped.physicalEdge7
f71 : V.advance (event 70) (foreign s70) ≡ just (foreign s71)
f71 = refl
s72 : V.Runtime
s72 = targetOf (event 71) s71 Scoped.physicalEdge8
f72 : V.advance (event 71) (foreign s71) ≡ just (foreign s72)
f72 = refl
s73 : V.Runtime
s73 = targetOf (event 72) s72 Scoped.physicalEdge9
f73 : V.advance (event 72) (foreign s72) ≡ just (foreign s73)
f73 = refl
s74 : V.Runtime
s74 = targetOf (event 73) s73 Scoped.physicalEdge10
f74 : V.advance (event 73) (foreign s73) ≡ just (foreign s74)
f74 = refl
s75 : V.Runtime
s75 = targetOf (event 74) s74 Scoped.physicalEdge11
f75 : V.advance (event 74) (foreign s74) ≡ just (foreign s75)
f75 = refl
s76 : V.Runtime
s76 = targetOf (event 75) s75 Scoped.physicalEdge12
f76 : V.advance (event 75) (foreign s75) ≡ just (foreign s76)
f76 = refl
s77 : V.Runtime
s77 = targetOf (event 76) s76 Scoped.physicalEdge13
f77 : V.advance (event 76) (foreign s76) ≡ just (foreign s77)
f77 = refl
s78 : V.Runtime
s78 = targetOf (event 77) s77 Scoped.physicalEdge14
f78 : V.advance (event 77) (foreign s77) ≡ just (foreign s78)
f78 = refl
s79 : V.Runtime
s79 = targetOf (event 78) s78 Scoped.catchEdge1
f79 : V.advance (event 78) (foreign s78) ≡ just (foreign s79)
f79 = refl
s80 : V.Runtime
s80 = targetOf (event 79) s79 Scoped.catchEdge2
f80 : V.advance (event 79) (foreign s79) ≡ just (foreign s80)
f80 = refl
s81 : V.Runtime
s81 = targetOf (event 80) s80 Scoped.catchEdge3
f81 : V.advance (event 80) (foreign s80) ≡ just (foreign s81)
f81 = refl
s82 : V.Runtime
s82 = targetOf (event 81) s81 Scoped.catchEdge4
f82 : V.advance (event 81) (foreign s81) ≡ just (foreign s82)
f82 = refl
s83 : V.Runtime
s83 = targetOf (event 82) s82 Scoped.catchEdge5
f83 : V.advance (event 82) (foreign s82) ≡ just (foreign s83)
f83 = refl
s84 : V.Runtime
s84 = targetOf (event 83) s83 Done.finishEdge1
f84 : V.advance (event 83) (foreign s83) ≡ just (foreign s84)
f84 = refl
s85 : V.Runtime
s85 = targetOf (event 84) s84 Done.finishEdge2
f85 : V.advance (event 84) (foreign s84) ≡ just (foreign s85)
f85 = refl
s86 : V.Runtime
s86 = targetOf (event 85) s85 Done.finishEdge3
f86 : V.advance (event 85) (foreign s85) ≡ just (foreign s86)
f86 = refl
s87 : V.Runtime
s87 = targetOf (event 86) s86 Done.finishEdge4
f87 : V.advance (event 86) (foreign s86) ≡ just (foreign s87)
f87 = refl
s88 : V.Runtime
s88 = targetOf (event 87) s87 Done.finishEdge5
f88 : V.advance (event 87) (foreign s87) ≡ just (foreign s88)
f88 = refl
s89 : V.Runtime
s89 = targetOf (event 88) s88 Done.finishEdge6
f89 : V.advance (event 88) (foreign s88) ≡ just (foreign s89)
f89 = refl
s90 : V.Runtime
s90 = targetOf (event 89) s89 Done.finishEdge7
f90 : V.advance (event 89) (foreign s89) ≡ just (foreign s90)
f90 = refl
s91 : V.Runtime
s91 = targetOf (event 90) s90 Done.finishEdge8
f91 : V.advance (event 90) (foreign s90) ≡ just (foreign s91)
f91 = refl
s92 : V.Runtime
s92 = targetOf (event 91) s91 Done.finishEdge9
f92 : V.advance (event 91) (foreign s91) ≡ just (foreign s92)
f92 = refl
s93 : V.Runtime
s93 = targetOf (event 92) s92 Done.finishEdge10
f93 : V.advance (event 92) (foreign s92) ≡ just (foreign s93)
f93 = refl
s94 : V.Runtime
s94 = targetOf (event 93) s93 Done.finishEdge11
f94 : V.advance (event 93) (foreign s93) ≡ just (foreign s94)
f94 = refl
s95 : V.Runtime
s95 = targetOf (event 94) s94 Done.finishEdge12
f95 : V.advance (event 94) (foreign s94) ≡ just (foreign s95)
f95 = refl
-- The fixture's last edge ends at its Server-returned state.
last : s95 ≡ Done.serverFinished
last = refl
abstract
  suffixPath : V.Runs (foreign start) suffixActions (foreign Done.serverFinished)
  suffixPath = V.more f1 (V.more f2 (V.more f3 (V.more f4 (V.more f5 (V.more f6 (V.more f7 (V.more f8 (V.more f9 (V.more f10 (V.more f11 (V.more f12 (V.more f13 (V.more f14 (V.more f15 (V.more f16 (V.more f17 (V.more f18 (V.more f19 (V.more f20 (V.more f21 (V.more f22 (V.more f23 (V.more f24 (V.more f25 (V.more f26 (V.more f27 (V.more f28 (V.more f29 (V.more f30 (V.more f31 (V.more f32 (V.more f33 (V.more f34 (V.more f35 (V.more f36 (V.more f37 (V.more f38 (V.more f39 (V.more f40 (V.more f41 (V.more f42 (V.more f43 (V.more f44 (V.more f45 (V.more f46 (V.more f47 (V.more f48 (V.more f49 (V.more f50 (V.more f51 (V.more f52 (V.more f53 (V.more f54 (V.more f55 (V.more f56 (V.more f57 (V.more f58 (V.more f59 (V.more f60 (V.more f61 (V.more f62 (V.more f63 (V.more f64 (V.more f65 (V.more f66 (V.more f67 (V.more f68 (V.more f69 (V.more f70 (V.more f71 (V.more f72 (V.more f73 (V.more f74 (V.more f75 (V.more f76 (V.more f77 (V.more f78 (V.more f79 (V.more f80 (V.more f81 (V.more f82 (V.more f83 (V.more f84 (V.more f85 (V.more f86 (V.more f87 (V.more f88 (V.more f89 (V.more f90 (V.more f91 (V.more f92 (V.more f93 (V.more f94 (V.more f95 (V.stop)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

append : ∀ {s as t bs u} → V.Runs s as t → V.Runs t bs u → V.Runs s (as ++ bs) u
append V.stop rest = rest
append (V.more eq path) rest = V.more eq (append path rest)

final : V.Runtime
final = foreign Done.serverFinished
innerActions : List V.Event
innerActions = eventsOf Trace.tracePrefix ++ (foreignEvent ∷ suffixActions)
abstract
  initialized-foreign : V.Runs Protocols.initial innerActions final
  initialized-foreign = append Trace.tracePrefix (V.more begin suffixPath)

-- Relays cancel, join and finish exactly as in Negative/PoolRelays.
returned : X.runtimeReturned final ≡ true
returned = refl
up : ∀ a r {r′} → RR.step true a r ≡ just r′ → X.outerStep (X.relaysAct a) (X.outer final r) ≡ just (X.outer final r′)
up a r = Cert.lift-relays a final r returned
closed : X.Outer
closed = X.outer final (RR.relaysState (just RR.joined) RR.finished)
closePath : X.Executes (X.outer final (RR.initial true)) Relays.Initialized.closeActions closed
closePath = X.next (up RR.requestCancel (RR.initial true) Relays.Rules.c1)
  (X.next (up (RR.threadAct RR.deliverCancel) (RR.relaysState (just RR.cancelRequested) RR.cancelling) Relays.Rules.c2)
  (X.next (up (RR.threadAct RR.bodyExit) (RR.relaysState (just RR.cancelDelivered) RR.cancelling) Relays.Rules.c3)
  (X.next (up (RR.threadAct RR.publishResult) (RR.relaysState (just RR.bodyExited) RR.cancelling) Relays.Rules.c4)
  (X.next (up (RR.threadAct RR.join) (RR.relaysState (just RR.resultAvailable) RR.cancelling) Relays.Rules.c5)
  (X.next (up RR.finish (RR.relaysState (just RR.joined) RR.cancelling) Relays.Rules.c6) X.done)))))
abstract
  initialized-close : X.Executes (X.outer Protocols.initial (RR.initial true))
    (map X.innerAct innerActions ++ Relays.Initialized.closeActions) closed
  initialized-close = Cert.append (Relays.Initialized.lift (just RR.running) initialized-foreign) closePath

-- The SI5 certificate (Server returned, peers closed, relays joined, CM
-- coordinator closed and drained) and residue c1 hold at the end of the run.
certified : Certificate.Complete true final (just RR.joined)
certified = Certificate.complete Protocols.initializer initialized-close
ig-quiet : Quiet.IGQuiet final
ig-quiet = Quiet.ig-quiet {scheduled = true} {t = just RR.joined} Protocols.initializer initialized-close

-- Yet the foreign acquisition frame is still pending in the final CM source.
frame-left : lookup foreignWorker (O.acquiring (K.source (V.base final))) ≡ just foreignFrame
frame-left = refl
acquiring-nonempty : O.acquiring (K.source (V.base final)) ≡ (foreignWorker , foreignFrame) ∷ []
acquiring-nonempty = refl
