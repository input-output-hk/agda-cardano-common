{-# OPTIONS --guardedness #-}

-- Combined preservation applications and injected reference/mux controls.
module ConnectionManagement.Negative.SubsystemReferences where

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (put)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.IGTypes as T
open import ConnectionManagement.Properties.HandlerEstablishment using (Prepared)
open import ConnectionManagement.Properties.HandlerReferences using (Chain)
open import ConnectionManagement.Properties.SubsystemReferences
import ConnectionManagement.CSP.OutboundAdmission as Out
import ConnectionManagement.CSP.IGRegistration as Fixture
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.Negative.Subsystem as Race
open import ConnectionManagement.Scenarios.Admission using (key₀; key₁)

-- Installation and publication are distinct actual lifecycle boundaries.
installed-prepared : Prepared L.child (ident 0) Fixture.mid (shared L.c22) (governor L.c22)
installed-prepared = record
  { resources = record { original = S.handlerStart (ident 0) Out.sock (ident 0) key₀
      ; found = refl; entryExists = S.unnegotiated outbound key₀ L.child , refl
      ; socketExists = S.handling L.child , refl }
  ; hd = _; mx = _; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl }
published-chain : Chain L.child Fixture.mid (shared L.c23) (governor L.c23)
published-chain = record
  { originalHandler = S.handlerStart (ident 0) Out.sock (ident 0) key₀
  ; publishedHandle = ident 0; negotiatedFlow = duplex; handleValue = _; muxValue = _
  ; handlerFound = refl; promiseFound = refl; handleFound = refl; handleMux = refl
  ; muxFound = refl; keyMatches = refl
  ; entryPresent = S.unnegotiated outbound key₀ L.child , refl
  ; socketPresent = S.handling L.child , refl }

-- Preserve preparation across publication and every later lifecycle action.
prepared-suffix : List Sub.Action
prepared-suffix = L.a23 ∷ L.a24 ∷ L.a25 ∷ L.a26 ∷ L.a27 ∷ L.a28 ∷ L.a29 ∷ L.a30 ∷ L.a31 ∷ L.a32 ∷ L.a33 ∷ L.a34 ∷ L.a35 ∷ L.a36 ∷ L.a37 ∷ L.a38 ∷ L.a39 ∷ L.a40 ∷ L.a41 ∷ L.a42 ∷ L.a43 ∷ L.a44 ∷ L.a45 ∷ L.a46 ∷ L.a47 ∷ L.a48 ∷ L.a49 ∷ L.a50 ∷ L.a51 ∷ L.a52 ∷ L.a53 ∷ L.a54 ∷ L.a55 ∷ L.a56 ∷ L.a57 ∷ L.a58 ∷ L.a59 ∷ L.a60 ∷ L.a61 ∷ L.a62 ∷ L.a63 ∷ L.a64 ∷ L.a65 ∷ L.a66 ∷ L.a67 ∷ L.a68 ∷ L.a69 ∷ L.a70 ∷ L.a71 ∷ L.a72 ∷ L.a73 ∷ L.a74 ∷ L.a75 ∷ L.a76 ∷ L.a77 ∷ L.a78 ∷ L.a79 ∷ L.a80 ∷ L.a81 ∷ L.a82 ∷ L.a83 ∷ L.a84 ∷ L.a85 ∷ L.a86 ∷ L.a87 ∷ L.a88 ∷ L.a89 ∷ L.a90 ∷ L.a91 ∷ L.a92 ∷ L.a93 ∷ L.a94 ∷ L.a95 ∷ L.a96 ∷ L.a97 ∷ L.a98 ∷ L.a99 ∷ L.a100 ∷ L.a101 ∷ L.a102 ∷ L.a103 ∷ L.a104 ∷ L.a105 ∷ L.a106 ∷ L.a107 ∷ L.a108 ∷ L.a109 ∷ L.a110 ∷ L.a111 ∷ L.a112 ∷ L.a113 ∷ L.a114 ∷ L.a115 ∷ L.a116 ∷ L.a117 ∷ L.a118 ∷ L.a119 ∷ L.a120 ∷ L.a121 ∷ L.a122 ∷ L.a123 ∷ L.a124 ∷ L.a125 ∷ L.a126 ∷ L.a127 ∷ L.a128 ∷ L.a129 ∷ L.a130 ∷ L.a131 ∷ L.a132 ∷ L.a133 ∷ L.a134 ∷ L.a135 ∷ L.a136 ∷ L.a137 ∷ L.a138 ∷ L.a139 ∷ L.a140 ∷ L.a141 ∷ L.a142 ∷ L.a143 ∷ L.a144 ∷ L.a145 ∷ L.a146 ∷ []
prepared-path : Sub.Executes L.c22 prepared-suffix L.final
prepared-path = Sub.next L.step23 (Sub.next L.step24 (Sub.next L.step25 (Sub.next L.step26 (Sub.next L.step27 (Sub.next L.step28 (Sub.next L.step29 (Sub.next L.step30 (Sub.next L.step31 (Sub.next L.step32 (Sub.next L.step33 (Sub.next L.step34 (Sub.next L.step35 (Sub.next L.step36 (Sub.next L.step37 (Sub.next L.step38 (Sub.next L.step39 (Sub.next L.step40 (Sub.next L.step41 (Sub.next L.step42 (Sub.next L.step43 (Sub.next L.step44 (Sub.next L.step45 (Sub.next L.step46 (Sub.next L.step47 (Sub.next L.step48 (Sub.next L.step49 (Sub.next L.step50 (Sub.next L.step51 (Sub.next L.step52 (Sub.next L.step53 (Sub.next L.step54 (Sub.next L.step55 (Sub.next L.step56 (Sub.next L.step57 (Sub.next L.step58 (Sub.next L.step59 (Sub.next L.step60 (Sub.next L.step61 (Sub.next L.step62 (Sub.next L.step63 (Sub.next L.step64 (Sub.next L.step65 (Sub.next L.step66 (Sub.next L.step67 (Sub.next L.step68 (Sub.next L.step69 (Sub.next L.step70 (Sub.next L.step71 (Sub.next L.step72 (Sub.next L.step73 (Sub.next L.step74 (Sub.next L.step75 (Sub.next L.step76 (Sub.next L.step77 (Sub.next L.step78 (Sub.next L.step79 (Sub.next L.step80 (Sub.next L.step81 (Sub.next L.step82 (Sub.next L.step83 (Sub.next L.step84 (Sub.next L.step85 (Sub.next L.step86 (Sub.next L.step87 (Sub.next L.step88 (Sub.next L.step89 (Sub.next L.step90 (Sub.next L.step91 (Sub.next L.step92 (Sub.next L.step93 (Sub.next L.step94 (Sub.next L.step95 (Sub.next L.step96 (Sub.next L.step97 (Sub.next L.step98 (Sub.next L.step99 (Sub.next L.step100 (Sub.next L.step101 (Sub.next L.step102 (Sub.next L.step103 (Sub.next L.step104 (Sub.next L.step105 (Sub.next L.step106 (Sub.next L.step107 (Sub.next L.step108 (Sub.next L.step109 (Sub.next L.step110 (Sub.next L.step111 (Sub.next L.step112 (Sub.next L.step113 (Sub.next L.step114 (Sub.next L.step115 (Sub.next L.step116 (Sub.next L.step117 (Sub.next L.step118 (Sub.next L.step119 (Sub.next L.step120 (Sub.next L.step121 (Sub.next L.step122 (Sub.next L.step123 (Sub.next L.step124 (Sub.next L.step125 (Sub.next L.step126 (Sub.next L.step127 (Sub.next L.step128 (Sub.next L.step129 (Sub.next L.step130 (Sub.next L.step131 (Sub.next L.step132 (Sub.next L.step133 (Sub.next L.step134 (Sub.next L.step135 (Sub.next L.step136 (Sub.next L.step137 (Sub.next L.step138 (Sub.next L.step139 (Sub.next L.step140 (Sub.next L.step141 (Sub.next L.step142 (Sub.next L.step143 (Sub.next L.step144 (Sub.next L.step145 (Sub.next L.step146 (Sub.done))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
chain-suffix : List Sub.Action
chain-suffix = L.a24 ∷ L.a25 ∷ L.a26 ∷ L.a27 ∷ L.a28 ∷ L.a29 ∷ L.a30 ∷ L.a31 ∷ L.a32 ∷ L.a33 ∷ L.a34 ∷ L.a35 ∷ L.a36 ∷ L.a37 ∷ L.a38 ∷ L.a39 ∷ L.a40 ∷ L.a41 ∷ L.a42 ∷ L.a43 ∷ L.a44 ∷ L.a45 ∷ L.a46 ∷ L.a47 ∷ L.a48 ∷ L.a49 ∷ L.a50 ∷ L.a51 ∷ L.a52 ∷ L.a53 ∷ L.a54 ∷ L.a55 ∷ L.a56 ∷ L.a57 ∷ L.a58 ∷ L.a59 ∷ L.a60 ∷ L.a61 ∷ L.a62 ∷ L.a63 ∷ L.a64 ∷ L.a65 ∷ L.a66 ∷ L.a67 ∷ L.a68 ∷ L.a69 ∷ L.a70 ∷ L.a71 ∷ L.a72 ∷ L.a73 ∷ L.a74 ∷ L.a75 ∷ L.a76 ∷ L.a77 ∷ L.a78 ∷ L.a79 ∷ L.a80 ∷ L.a81 ∷ L.a82 ∷ L.a83 ∷ L.a84 ∷ L.a85 ∷ L.a86 ∷ L.a87 ∷ L.a88 ∷ L.a89 ∷ L.a90 ∷ L.a91 ∷ L.a92 ∷ L.a93 ∷ L.a94 ∷ L.a95 ∷ L.a96 ∷ L.a97 ∷ L.a98 ∷ L.a99 ∷ L.a100 ∷ L.a101 ∷ L.a102 ∷ L.a103 ∷ L.a104 ∷ L.a105 ∷ L.a106 ∷ L.a107 ∷ L.a108 ∷ L.a109 ∷ L.a110 ∷ L.a111 ∷ L.a112 ∷ L.a113 ∷ L.a114 ∷ L.a115 ∷ L.a116 ∷ L.a117 ∷ L.a118 ∷ L.a119 ∷ L.a120 ∷ L.a121 ∷ L.a122 ∷ L.a123 ∷ L.a124 ∷ L.a125 ∷ L.a126 ∷ L.a127 ∷ L.a128 ∷ L.a129 ∷ L.a130 ∷ L.a131 ∷ L.a132 ∷ L.a133 ∷ L.a134 ∷ L.a135 ∷ L.a136 ∷ L.a137 ∷ L.a138 ∷ L.a139 ∷ L.a140 ∷ L.a141 ∷ L.a142 ∷ L.a143 ∷ L.a144 ∷ L.a145 ∷ L.a146 ∷ []
chain-path : Sub.Executes L.c23 chain-suffix L.final
chain-path = Sub.next L.step24 (Sub.next L.step25 (Sub.next L.step26 (Sub.next L.step27 (Sub.next L.step28 (Sub.next L.step29 (Sub.next L.step30 (Sub.next L.step31 (Sub.next L.step32 (Sub.next L.step33 (Sub.next L.step34 (Sub.next L.step35 (Sub.next L.step36 (Sub.next L.step37 (Sub.next L.step38 (Sub.next L.step39 (Sub.next L.step40 (Sub.next L.step41 (Sub.next L.step42 (Sub.next L.step43 (Sub.next L.step44 (Sub.next L.step45 (Sub.next L.step46 (Sub.next L.step47 (Sub.next L.step48 (Sub.next L.step49 (Sub.next L.step50 (Sub.next L.step51 (Sub.next L.step52 (Sub.next L.step53 (Sub.next L.step54 (Sub.next L.step55 (Sub.next L.step56 (Sub.next L.step57 (Sub.next L.step58 (Sub.next L.step59 (Sub.next L.step60 (Sub.next L.step61 (Sub.next L.step62 (Sub.next L.step63 (Sub.next L.step64 (Sub.next L.step65 (Sub.next L.step66 (Sub.next L.step67 (Sub.next L.step68 (Sub.next L.step69 (Sub.next L.step70 (Sub.next L.step71 (Sub.next L.step72 (Sub.next L.step73 (Sub.next L.step74 (Sub.next L.step75 (Sub.next L.step76 (Sub.next L.step77 (Sub.next L.step78 (Sub.next L.step79 (Sub.next L.step80 (Sub.next L.step81 (Sub.next L.step82 (Sub.next L.step83 (Sub.next L.step84 (Sub.next L.step85 (Sub.next L.step86 (Sub.next L.step87 (Sub.next L.step88 (Sub.next L.step89 (Sub.next L.step90 (Sub.next L.step91 (Sub.next L.step92 (Sub.next L.step93 (Sub.next L.step94 (Sub.next L.step95 (Sub.next L.step96 (Sub.next L.step97 (Sub.next L.step98 (Sub.next L.step99 (Sub.next L.step100 (Sub.next L.step101 (Sub.next L.step102 (Sub.next L.step103 (Sub.next L.step104 (Sub.next L.step105 (Sub.next L.step106 (Sub.next L.step107 (Sub.next L.step108 (Sub.next L.step109 (Sub.next L.step110 (Sub.next L.step111 (Sub.next L.step112 (Sub.next L.step113 (Sub.next L.step114 (Sub.next L.step115 (Sub.next L.step116 (Sub.next L.step117 (Sub.next L.step118 (Sub.next L.step119 (Sub.next L.step120 (Sub.next L.step121 (Sub.next L.step122 (Sub.next L.step123 (Sub.next L.step124 (Sub.next L.step125 (Sub.next L.step126 (Sub.next L.step127 (Sub.next L.step128 (Sub.next L.step129 (Sub.next L.step130 (Sub.next L.step131 (Sub.next L.step132 (Sub.next L.step133 (Sub.next L.step134 (Sub.next L.step135 (Sub.next L.step136 (Sub.next L.step137 (Sub.next L.step138 (Sub.next L.step139 (Sub.next L.step140 (Sub.next L.step141 (Sub.next L.step142 (Sub.next L.step143 (Sub.next L.step144 (Sub.next L.step145 (Sub.next L.step146 (Sub.done)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
final-prepared : Prepared L.child (ident 0) Fixture.mid (shared L.final) (governor L.final)
final-prepared = prepared-exec prepared-path installed-prepared
final-chain : Chain L.child Fixture.mid (shared L.final) (governor L.final)
final-chain = chain-exec chain-path published-chain

-- Delay parent registration while the child runs and publishes completion.
race-actions : List Sub.Action
race-actions = L.a24 ∷ L.a25 ∷ L.a26 ∷ L.a27 ∷ L.a28 ∷ L.a29 ∷ L.a30 ∷ L.a31 ∷ L.a32 ∷ L.a33 ∷ L.a34 ∷ L.a35 ∷ L.a36 ∷ L.a37 ∷ L.a38 ∷ L.a39 ∷ L.a40 ∷ L.a41 ∷ []
race-path : Sub.Executes (Race.held L.c23) race-actions (Race.held L.c41)
race-path = Sub.next {c₁ = Race.held L.c24} refl (Sub.next {c₁ = Race.held L.c25} refl (Sub.next {c₁ = Race.held L.c26} refl (Sub.next {c₁ = Race.held L.c27} refl (Sub.next {c₁ = Race.held L.c28} refl (Sub.next {c₁ = Race.held L.c29} refl (Sub.next {c₁ = Race.held L.c30} refl (Sub.next {c₁ = Race.held L.c31} refl (Sub.next {c₁ = Race.held L.c32} refl (Sub.next {c₁ = Race.held L.c33} refl (Sub.next {c₁ = Race.held L.c34} refl (Sub.next {c₁ = Race.held L.c35} refl (Sub.next {c₁ = Race.held L.c36} refl (Sub.next {c₁ = Race.held L.c37} refl (Sub.next {c₁ = Race.held L.c38} refl (Sub.next {c₁ = Race.held L.c39} refl (Sub.next {c₁ = Race.held L.c40} refl (Sub.next {c₁ = Race.held L.c41} refl (Sub.done))))))))))))))))))
race-chain : Chain L.child Fixture.mid (shared (Race.held L.c41)) (governor (Race.held L.c41))
race-chain = chain-exec race-path published-chain

-- Inject a close/error continuation with coherent existing references.
closingWorld : S.State
closingWorld = Out.published
closedWorld : S.State
closedWorld = record closingWorld { sockets = put Out.sock S.closed (S.sockets closingWorld) }
uncertainWorld : S.State
uncertainWorld = record closingWorld { sockets = put Out.sock (S.closeUncertain (errorId 9)) (S.sockets closingWorld) }
removedWorld : S.State
removedWorld = record closedWorld { cm = record (S.cm closedWorld)
  { mapCell = S.full []; entries = put (ident 0) (S.terminated nothing) (S.entries (S.cm closedWorld)) } }
wrap : A.PC → S.State → Sub.Configuration
wrap pc s = Sub.initial (Out.withHandle (Out.at pc s)) L.settings
closing closed removed uncertain : Sub.Configuration
closing = wrap (A.closeError (ident 0) C.connectionExists) closingWorld
closed = wrap (A.removeError (ident 0) C.connectionExists) closedWorld
removed = wrap (A.count (A.complete (C.raised C.connectionExists))) removedWorld
uncertain = wrap (A.complete (C.raised (C.ioFailure (errorId 9)))) uncertainWorld
close-step : Sub.advance (Sub.core (O.acquire Out.caller A.closeOK)) closing ≡ just closed
close-step = refl
failed-step : Sub.advance (Sub.core (O.acquire Out.caller (A.closeFailed (errorId 9)))) closing ≡ just uncertain
failed-step = refl
remove-step : Sub.advance (Sub.core (O.acquire Out.caller A.removeReservation)) closed ≡ just removed
remove-step = refl
closed-chain : Chain L.child Fixture.mid (shared closed) (governor closed)
closed-chain = chain-step (Sub.core (O.acquire Out.caller A.closeOK)) closing close-step published-chain
uncertain-chain : Chain L.child Fixture.mid (shared uncertain) (governor uncertain)
uncertain-chain = chain-step (Sub.core (O.acquire Out.caller (A.closeFailed (errorId 9)))) closing failed-step published-chain
removed-chain : Chain L.child Fixture.mid (shared removed) (governor removed)
removed-chain = chain-step (Sub.core (O.acquire Out.caller A.removeReservation)) closed remove-step closed-chain

-- Exercise the subsystem's direct initiator-failure mux write.
peer : P.Peer
peer = record (P.initialPeer key₀ (ident 0) (M.handleState Fixture.mid (Fixture.proto ∷ []) duplex))
  { status = P.peerHot
  ; runs = P.protocolRun Fixture.proto (P.returned (T.errored (errorId 7))) P.running ∷ [] }
failureBefore : Sub.Configuration
failureBefore = record L.c23 { world = record (Sub.world L.c23) { peers = (ident 0 , peer) ∷ [] } }
failureAfter : Sub.Configuration
failureAfter = record failureBefore { world = record (Sub.world failureBefore)
  { cm = record (J.cm (Sub.world failureBefore)) { core = record (O.core (J.cm (Sub.world failureBefore)))
    { inboundGovernor = IG.setMux Fixture.mid
      (record Fixture.newMux { status = M.failed (errorId 7); callback = M.readActive M.muxStopped })
      (governor failureBefore) } } } }
observe-step : Sub.advance (Sub.observeInitiatorFailure (ident 0)) failureBefore ≡ just failureAfter
observe-step = refl
failure-chain : Chain L.child Fixture.mid (shared failureAfter) (governor failureAfter)
failure-chain = chain-step (Sub.observeInitiatorFailure (ident 0)) failureBefore observe-step published-chain

-- Key and handle/mux identity are real certificate obligations, even though
-- the executable open model permits injecting inconsistent installations.
wrongKey wrongHandle : Sub.Configuration
wrongKey = record L.c23 { world = record (Sub.world L.c23)
  { cm = record (J.cm (Sub.world L.c23)) { core = record (O.core (J.cm (Sub.world L.c23)))
    { inboundGovernor = IG.setMux Fixture.mid (record Fixture.newMux { key = key₁ }) (governor L.c23) } } } }
wrongHandle = record L.c22 { world = record (Sub.world L.c22)
  { cm = record (J.cm (Sub.world L.c22)) { core = record (O.core (J.cm (Sub.world L.c22)))
    { inboundGovernor = record (governor L.c22) { execution = record (IG.execution (governor L.c22))
      { handles = (ident 0 , M.handleState (ident 99) (Fixture.proto ∷ []) duplex) ∷ [] } } } } } }
wrong-key-invalid : ¬ Chain L.child Fixture.mid (shared wrongKey) (governor wrongKey)
wrong-key-invalid chain with just-injective (Chain.handlerFound chain) | just-injective (Chain.muxFound chain)
... | refl | refl with Chain.keyMatches chain
... | ()
wrong-handle-invalid : ¬ Prepared L.child (ident 0) Fixture.mid (shared wrongHandle) (governor wrongHandle)
wrong-handle-invalid p with just-injective (Prepared.handleFound p)
... | refl with Prepared.handleMux p
... | ()

-- A conditional job timeout exercises the second IG writer: shutdown is queued
-- on the looked-up mux without changing its key or replacing its handle.
timeoutWorker : J.Frame
timeoutWorker = J.frame (G.job G.deactivate (remote key₀) (just (ident 0)))
  L.caller L.child Out.sock (ident 0) J.awaitHot
timeoutBefore : Sub.Configuration
timeoutBefore = record failureBefore
  { jobs = (ident 0 , Sub.jobFrame timeoutWorker false false) ∷ [] }
timeoutWorld : J.World
timeoutWorld = record (Sub.world timeoutBefore)
  { peers = (ident 0 , P.cool peer) ∷ []
  ; cm = record (J.cm (Sub.world timeoutBefore)) { core = record (O.core (J.cm (Sub.world timeoutBefore)))
    { inboundGovernor = IG.setMux Fixture.mid
      (record Fixture.newMux { commands = M.shutdown ∷ [] }) (governor timeoutBefore) } } }
timeoutAfter : Sub.Configuration
timeoutAfter = record timeoutBefore { world = timeoutWorld
  ; jobs = (ident 0 , Sub.jobFrame (record timeoutWorker { pc = J.awaitCold G.failed }) false false) ∷ [] }
timeout-step : Sub.advance (Sub.jobStep (ident 0) J.operationTimeout) timeoutBefore ≡ just timeoutAfter
timeout-step = refl
timeout-chain : Chain L.child Fixture.mid (shared timeoutAfter) (governor timeoutAfter)
timeout-chain = chain-step (Sub.jobStep (ident 0) J.operationTimeout) timeoutBefore timeout-step published-chain
