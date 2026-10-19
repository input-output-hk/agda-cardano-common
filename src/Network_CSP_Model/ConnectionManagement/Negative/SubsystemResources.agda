{-# OPTIONS --guardedness #-}

-- Existing-resource preservation and injected scope/guard controls.
module ConnectionManagement.Negative.SubsystemResources where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (put; lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
open import ConnectionManagement.Properties.HandlerResources using (Resources)
open import ConnectionManagement.Properties.HandlerResourceFacts
import ConnectionManagement.Properties.SubsystemResources as Keep
import ConnectionManagement.CSP.OutboundAdmission as Out
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.CSP.OutboundReleaseScenarios as Release
import ConnectionManagement.Negative.Subsystem as Race
open import ConnectionManagement.Scenarios.Admission using (key₀)

-- Begin after the real outbound fork, not at an empty state with no handler.
shared : Sub.Configuration → S.State
shared c = I.world (O.core (J.cm (Sub.world c)))
descriptor : S.HandlerStart
descriptor = S.handlerStart (ident 0) Out.sock (ident 0) key₀
forked-facts : Facts L.child descriptor (shared L.c19)
forked-facts = refl , (S.reservedOutbound , refl) , (S.handling L.child , refl)

-- Checked existing lifecycle suffix: all subsequent job/governor/CM actions.
suffix : List Sub.Action
suffix = L.a20 ∷ L.a21 ∷ L.a22 ∷ L.a23 ∷ L.a24 ∷ L.a25 ∷ L.a26 ∷ L.a27 ∷ L.a28 ∷ L.a29 ∷ L.a30 ∷ L.a31 ∷ L.a32 ∷ L.a33 ∷ L.a34 ∷ L.a35 ∷ L.a36 ∷ L.a37 ∷ L.a38 ∷ L.a39 ∷ L.a40 ∷ L.a41 ∷ L.a42 ∷ L.a43 ∷ L.a44 ∷ L.a45 ∷ L.a46 ∷ L.a47 ∷ L.a48 ∷ L.a49 ∷ L.a50 ∷ L.a51 ∷ L.a52 ∷ L.a53 ∷ L.a54 ∷ L.a55 ∷ L.a56 ∷ L.a57 ∷ L.a58 ∷ L.a59 ∷ L.a60 ∷ L.a61 ∷ L.a62 ∷ L.a63 ∷ L.a64 ∷ L.a65 ∷ L.a66 ∷ L.a67 ∷ L.a68 ∷ L.a69 ∷ L.a70 ∷ L.a71 ∷ L.a72 ∷ L.a73 ∷ L.a74 ∷ L.a75 ∷ L.a76 ∷ L.a77 ∷ L.a78 ∷ L.a79 ∷ L.a80 ∷ L.a81 ∷ L.a82 ∷ L.a83 ∷ L.a84 ∷ L.a85 ∷ L.a86 ∷ L.a87 ∷ L.a88 ∷ L.a89 ∷ L.a90 ∷ L.a91 ∷ L.a92 ∷ L.a93 ∷ L.a94 ∷ L.a95 ∷ L.a96 ∷ L.a97 ∷ L.a98 ∷ L.a99 ∷ L.a100 ∷ L.a101 ∷ L.a102 ∷ L.a103 ∷ L.a104 ∷ L.a105 ∷ L.a106 ∷ L.a107 ∷ L.a108 ∷ L.a109 ∷ L.a110 ∷ L.a111 ∷ L.a112 ∷ L.a113 ∷ L.a114 ∷ L.a115 ∷ L.a116 ∷ L.a117 ∷ L.a118 ∷ L.a119 ∷ L.a120 ∷ L.a121 ∷ L.a122 ∷ L.a123 ∷ L.a124 ∷ L.a125 ∷ L.a126 ∷ L.a127 ∷ L.a128 ∷ L.a129 ∷ L.a130 ∷ L.a131 ∷ L.a132 ∷ L.a133 ∷ L.a134 ∷ L.a135 ∷ L.a136 ∷ L.a137 ∷ L.a138 ∷ L.a139 ∷ L.a140 ∷ L.a141 ∷ L.a142 ∷ L.a143 ∷ L.a144 ∷ L.a145 ∷ L.a146 ∷ []
suffix-path : Sub.Executes L.c19 suffix L.final
suffix-path = Sub.next L.step20 (Sub.next L.step21 (Sub.next L.step22 (Sub.next L.step23 (Sub.next L.step24 (Sub.next L.step25 (Sub.next L.step26 (Sub.next L.step27 (Sub.next L.step28 (Sub.next L.step29 (Sub.next L.step30 (Sub.next L.step31 (Sub.next L.step32 (Sub.next L.step33 (Sub.next L.step34 (Sub.next L.step35 (Sub.next L.step36 (Sub.next L.step37 (Sub.next L.step38 (Sub.next L.step39 (Sub.next L.step40 (Sub.next L.step41 (Sub.next L.step42 (Sub.next L.step43 (Sub.next L.step44 (Sub.next L.step45 (Sub.next L.step46 (Sub.next L.step47 (Sub.next L.step48 (Sub.next L.step49 (Sub.next L.step50 (Sub.next L.step51 (Sub.next L.step52 (Sub.next L.step53 (Sub.next L.step54 (Sub.next L.step55 (Sub.next L.step56 (Sub.next L.step57 (Sub.next L.step58 (Sub.next L.step59 (Sub.next L.step60 (Sub.next L.step61 (Sub.next L.step62 (Sub.next L.step63 (Sub.next L.step64 (Sub.next L.step65 (Sub.next L.step66 (Sub.next L.step67 (Sub.next L.step68 (Sub.next L.step69 (Sub.next L.step70 (Sub.next L.step71 (Sub.next L.step72 (Sub.next L.step73 (Sub.next L.step74 (Sub.next L.step75 (Sub.next L.step76 (Sub.next L.step77 (Sub.next L.step78 (Sub.next L.step79 (Sub.next L.step80 (Sub.next L.step81 (Sub.next L.step82 (Sub.next L.step83 (Sub.next L.step84 (Sub.next L.step85 (Sub.next L.step86 (Sub.next L.step87 (Sub.next L.step88 (Sub.next L.step89 (Sub.next L.step90 (Sub.next L.step91 (Sub.next L.step92 (Sub.next L.step93 (Sub.next L.step94 (Sub.next L.step95 (Sub.next L.step96 (Sub.next L.step97 (Sub.next L.step98 (Sub.next L.step99 (Sub.next L.step100 (Sub.next L.step101 (Sub.next L.step102 (Sub.next L.step103 (Sub.next L.step104 (Sub.next L.step105 (Sub.next L.step106 (Sub.next L.step107 (Sub.next L.step108 (Sub.next L.step109 (Sub.next L.step110 (Sub.next L.step111 (Sub.next L.step112 (Sub.next L.step113 (Sub.next L.step114 (Sub.next L.step115 (Sub.next L.step116 (Sub.next L.step117 (Sub.next L.step118 (Sub.next L.step119 (Sub.next L.step120 (Sub.next L.step121 (Sub.next L.step122 (Sub.next L.step123 (Sub.next L.step124 (Sub.next L.step125 (Sub.next L.step126 (Sub.next L.step127 (Sub.next L.step128 (Sub.next L.step129 (Sub.next L.step130 (Sub.next L.step131 (Sub.next L.step132 (Sub.next L.step133 (Sub.next L.step134 (Sub.next L.step135 (Sub.next L.step136 (Sub.next L.step137 (Sub.next L.step138 (Sub.next L.step139 (Sub.next L.step140 (Sub.next L.step141 (Sub.next L.step142 (Sub.next L.step143 (Sub.next L.step144 (Sub.next L.step145 (Sub.next L.step146 (Sub.done)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

lifecycle-facts : Facts L.child descriptor (shared L.final)
lifecycle-facts = Keep.For.exec-preserves L.child descriptor forked-facts suffix-path
lifecycle-resources : Resources L.child (shared L.final)
lifecycle-resources = Keep.resources-exec suffix-path (to-resources forked-facts)

-- Parent registration is delayed while the child performs the same actions.
race-suffix : List Sub.Action
race-suffix = L.a20 ∷ L.a21 ∷ L.a22 ∷ L.a23 ∷ L.a24 ∷ L.a25 ∷ L.a26 ∷ L.a27 ∷ L.a28 ∷ L.a29 ∷ L.a30 ∷ L.a31 ∷ L.a32 ∷ L.a33 ∷ L.a34 ∷ L.a35 ∷ L.a36 ∷ L.a37 ∷ L.a38 ∷ L.a39 ∷ L.a40 ∷ L.a41 ∷ []
race-suffix-path : Sub.Executes (Race.held L.c19) race-suffix (Race.held L.c41)
race-suffix-path = Sub.next {c₁ = Race.held L.c20} refl (Sub.next {c₁ = Race.held L.c21} refl (Sub.next {c₁ = Race.held L.c22} refl (Sub.next {c₁ = Race.held L.c23} refl (Sub.next {c₁ = Race.held L.c24} refl (Sub.next {c₁ = Race.held L.c25} refl (Sub.next {c₁ = Race.held L.c26} refl (Sub.next {c₁ = Race.held L.c27} refl (Sub.next {c₁ = Race.held L.c28} refl (Sub.next {c₁ = Race.held L.c29} refl (Sub.next {c₁ = Race.held L.c30} refl (Sub.next {c₁ = Race.held L.c31} refl (Sub.next {c₁ = Race.held L.c32} refl (Sub.next {c₁ = Race.held L.c33} refl (Sub.next {c₁ = Race.held L.c34} refl (Sub.next {c₁ = Race.held L.c35} refl (Sub.next {c₁ = Race.held L.c36} refl (Sub.next {c₁ = Race.held L.c37} refl (Sub.next {c₁ = Race.held L.c38} refl (Sub.next {c₁ = Race.held L.c39} refl (Sub.next {c₁ = Race.held L.c40} refl (Sub.next {c₁ = Race.held L.c41} refl (Sub.done))))))))))))))))))))))
race-facts : Facts L.child descriptor (shared (Race.held L.c41))
race-facts = Keep.For.exec-preserves L.child descriptor forked-facts race-suffix-path

-- Inject an error-close continuation sharing this handler's socket. Such
-- arbitrary frames are covered by preservation but are not reachability claims.
closingWorld : S.State
closingWorld = Out.forked
closedWorld : S.State
closedWorld = record closingWorld { sockets = put Out.sock S.closed (S.sockets closingWorld) }
uncertainWorld : S.State
uncertainWorld = record closingWorld { sockets = put Out.sock (S.closeUncertain (errorId 9)) (S.sockets closingWorld) }
removedWorld : S.State
removedWorld = record closedWorld { cm = record (S.cm closedWorld)
  { mapCell = S.full []; entries = put (ident 0) (S.terminated nothing) (S.entries (S.cm closedWorld)) } }
closing closed removed uncertain : Sub.Configuration
closing = Sub.initial (Out.at (A.closeError (ident 0) C.connectionExists) closingWorld) L.settings
closed = Sub.initial (Out.at (A.removeError (ident 0) C.connectionExists) closedWorld) L.settings
removed = Sub.initial (Out.at (A.count (A.complete (C.raised C.connectionExists))) removedWorld) L.settings
uncertain = Sub.initial (Out.at (A.complete (C.raised (C.ioFailure (errorId 9)))) uncertainWorld) L.settings
close-step : Sub.advance (Sub.core (O.acquire Out.caller A.closeOK)) closing ≡ just closed
close-step = refl
close-failed-step : Sub.advance (Sub.core (O.acquire Out.caller (A.closeFailed (errorId 9)))) closing ≡ just uncertain
close-failed-step = refl
remove-step : Sub.advance (Sub.core (O.acquire Out.caller A.removeReservation)) closed ≡ just removed
remove-step = refl
closing-facts : Facts L.child descriptor (shared closing)
closing-facts = forked-facts
closed-facts : Facts L.child descriptor (shared closed)
closed-facts = Keep.For.advance-preserves L.child descriptor (Sub.core (O.acquire Out.caller A.closeOK)) closing close-step closing-facts
uncertain-facts : Facts L.child descriptor (shared uncertain)
uncertain-facts = Keep.For.advance-preserves L.child descriptor (Sub.core (O.acquire Out.caller (A.closeFailed (errorId 9)))) closing close-failed-step closing-facts
removed-facts : Facts L.child descriptor (shared removed)
removed-facts = Keep.For.advance-preserves L.child descriptor (Sub.core (O.acquire Out.caller A.removeReservation)) closed remove-step closed-facts

-- Stored presence remains true when the socket is closed and the binding gone.
socket-closed : lookup Out.sock (S.sockets (shared removed)) ≡ just S.closed
socket-closed = refl
map-empty : S.mapCell (S.cm (shared removed)) ≡ S.full []
map-empty = refl

-- The absent-child guard rejects replacing the existing descriptor.
reusedChild : Sub.Configuration
reusedChild = Sub.initial (Out.at (A.forkHandler (ident 0) (ident 0) key₀) Out.forked) L.settings
reused-child-refused : Sub.advance (Sub.core (O.acquire Out.caller A.forkOK)) reusedChild ≡ nothing
reused-child-refused = refl

-- Inject missing records to check that the certificate has the intended scope.
missingEntry missingSocket replacedHandler : S.State
missingEntry = record (shared closing) { cm = record (S.cm (shared closing)) { entries = [] } }
missingSocket = record (shared closing) { sockets = [] }
replacedHandler = record (shared closing)
  { handlers = (L.child , S.handlerStart (ident 99) Out.sock (ident 0) key₀) ∷ [] }
missing-entry-invalid : ¬ Facts L.child descriptor missingEntry
missing-entry-invalid (_ , (_ , ()) , _)
missing-socket-invalid : ¬ Facts L.child descriptor missingSocket
missing-socket-invalid (_ , _ , (_ , ()))
retargeted-invalid : ¬ Facts L.child descriptor replacedHandler
retargeted-invalid (() , _)

-- Every arbitrary finite continuation from certified resources excludes a target
-- missing the fixed handler/resource facts; no scheduling premise is added.
invalid-unreachable : ∀ q h c target actions → Facts q h (shared c) →
  ¬ Facts q h (shared target) → ¬ Sub.Executes c actions target
invalid-unreachable q h c target actions facts invalid path =
  invalid (Keep.For.exec-preserves q h facts path)

-- Lift existing conditional outbound release paths through the real subsystem
-- core transition; governor and peer-job fields remain at their initial values.
embed : O.Configuration → Sub.Configuration
embed c = Sub.initial c L.settings
core-step : ∀ a c {c′} → O.advance a c ≡ just c′ →
  Sub.advance (Sub.core a) (embed c) ≡ just (embed c′)
core-step a c eq rewrite eq = refl
core-path : ∀ {c actions c′} → O.Executes c actions c′ →
  Sub.Executes (embed c) (map Sub.core actions) (embed c′)
core-path O.done = Sub.done
core-path (O.next {c = c} {c₁ = c₁} {a = a} eq rest) =
  Sub.next {c₁ = embed c₁} (core-step a c eq) (core-path rest)

timeout-start : Facts L.child descriptor (shared (embed Release.initialUni))
timeout-start = refl , (S.outboundUni key₀ L.child (ident 0) , refl) , (S.handling L.child , refl)
pruning-start : Facts L.child descriptor (shared (embed Release.pruneInitial))
pruning-start = refl , (S.outboundDup key₀ L.child (ident 0) ticking , refl) , (S.handling L.child , refl)
timeout-facts : Facts L.child descriptor (shared (embed Release.t11))
timeout-facts = Keep.For.exec-preserves L.child descriptor timeout-start (core-path Release.tPath)
pruning-facts : Facts L.child descriptor (shared (embed Release.p7))
pruning-facts = Keep.For.exec-preserves L.child descriptor pruning-start (core-path Release.pPath)
