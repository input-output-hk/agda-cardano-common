{-# OPTIONS --guardedness #-}

-- G1 F2: actual configured/counter snapshots from the existing checked
-- startup fixture. This local suffix checks receipt, empty entered-pool close,
-- the async catch, byte-cell retirement and only then buffer handoff. It does
-- not assert a new initialized whole-System lifecycle or eventual shutdown.
module ConnectionManagement.Negative.PrimitiveConfiguredRetirement where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import ConnectionManagement.Store using (Store)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (errorId; MuxId)
import ConnectionManagement.Negative.MuxConfiguredCounters as C
import ConnectionManagement.Negative.MuxResultMonitor as F
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.MuxExitCancellation as Cancel
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
module R = Unwind F.bearerClosed
module W = Exit F.bearerClosed
module X = Cancel F.bearerClosed
module G = W.G
module M = G.M
module P = G.P

wrap : P.State → R.State
wrap p = R.unwinding (W.handlerExitState (G.shutdownState (M.monitorState p []) []) []) []
after : R.Action → R.State → R.State
after a s with R.step a s
... | just t = t
... | nothing = s
isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing = false
start r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : R.State
start = wrap C.k2
r0 = C.snapshot (after (R.observeCancellation C.owner R.unmaskedConfiguredStartup (errorId 20)) start)
r1 = C.snapshot (after (R.beginClose C.owner []) r0)
r2 = C.snapshot (after (R.finishClose C.owner) r1)
r3 = C.snapshot (after (R.writeAsyncFailure C.owner) r2)
r4 = C.snapshot (after (R.beginDead C.owner) r3)
r5 = C.snapshot (after (R.sampleDead C.owner) r4)
r6 = C.snapshot (after (R.commitDead C.owner) r5)
r7 = C.snapshot (after (R.finishDead C.owner) r6)
r8 = C.snapshot (after (R.handoff C.owner) r7)
r9 = C.snapshot (after (R.handoff C.owner) r8)

receipt : R.step (R.observeCancellation C.owner R.unmaskedConfiguredStartup (errorId 20)) start ≡ just r0
receipt = refl
close-entered-pool : R.step (R.beginClose C.owner []) r0 ≡ just r1
close-entered-pool = refl
close-finished : R.step (R.finishClose C.owner) r1 ≡ just r2
close-finished = refl
catch-status : R.step (R.writeAsyncFailure C.owner) r2 ≡ just r3
catch-status = refl
catch-dead : R.step (R.beginDead C.owner) r3 ≡ just r4
catch-dead = refl
catch-sample : R.step (R.sampleDead C.owner) r4 ≡ just r5
catch-sample = refl
catch-commit : R.step (R.commitDead C.owner) r5 ≡ just r6
catch-commit = refl
catch-finish : R.step (R.finishDead C.owner) r6 ≡ just r7
catch-finish = refl
retire-before-handoff : R.step (R.handoff C.owner) r7 ≡ just r8
retire-before-handoff = refl
handoff-after-retirement : R.step (R.handoff C.owner) r8 ≡ just r9
handoff-after-retirement = refl
rows : R.State → Store ℕ MuxId
rows s = IG.counterRows (IG.execution (Machine.inboundGovernor (O.core (R.source s))))
row-kept-through-catch : rows r7 ≡ rows start
row-kept-through-catch = refl
row-retired : rows r8 ≡ []
row-retired = refl
no-early-handoff : R.step (R.handoff C.owner) r0 ≡ nothing
no-early-handoff = refl
no-handoff-twice : R.step (R.handoff C.owner) r9 ≡ nothing
no-handoff-twice = refl
before-cells-enabled : isJust (R.step (R.observeCancellation C.owner R.unmaskedConfiguredBeforePool (errorId 20)) (wrap C.k0)) ≡ true
before-cells-enabled = refl
registered-acquisition-refused : R.step (R.observeCancellation C.owner R.unmaskedConfiguredBeforePool (errorId 20)) (wrap C.k1) ≡ nothing
registered-acquisition-refused = refl
masked-registration-refused : R.step (R.observeCancellation C.owner R.unmaskedConfiguredStartup (errorId 20)) (wrap C.k3) ≡ nothing
masked-registration-refused = refl
partial-settled-enabled : isJust (R.step (R.observeCancellation C.owner R.unmaskedConfiguredStartup (errorId 20)) (wrap C.k4)) ≡ true
partial-settled-enabled = refl
mature-enabled : isJust (R.step (R.observeCancellation C.owner R.unmaskedConfiguredStartup (errorId 20)) (wrap C.k9)) ≡ true
mature-enabled = refl

-- Before acquiring the brackets, receipt cannot invent an entered/closed pool.
beforeCells : R.State
beforeCells = after (R.observeCancellation C.owner R.unmaskedConfiguredBeforePool (errorId 20)) (wrap C.k0)
no-pre-pool-close : R.step (R.beginClose C.owner []) beforeCells ≡ nothing
no-pre-pool-close = refl
partialReceipt : R.State
partialReceipt = after (R.observeCancellation C.owner R.unmaskedConfiguredStartup (errorId 20)) (wrap C.k4)
partial-pool-retained : R.poolAt C.owner partialReceipt ≡ R.poolAt C.owner (wrap C.k4)
partial-pool-retained = refl

counter-registration-sealed : R.allowedP (P.run (P.U.registerCounters C.owner)) beforeCells ≡ false
counter-registration-sealed = refl
