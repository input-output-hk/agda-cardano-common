{-# OPTIONS --guardedness #-}

-- Executable diagnostics for tracked handler slices, not a global invariant.
-- Never use this predicate to filter Machine.advance: failures must stay visible.
module ConnectionManagement.Properties.HandlerValidity where

import Data.Nat as Nat
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (does)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (Store; lookup)
open import ConnectionManagement.Machine using (Configuration; world; inboundGovernor; handlerLifecycles)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.IGRegistration as IG

-- Stores built by put have unique keys; fixtures can violate that assumption.
uniqueOwners : L.Runtime → Bool
uniqueOwners [] = true
uniqueOwners ((w , f) ∷ rest) with lookup w rest
... | just _ = false
... | nothing = not (L.hasMux (L.capturedMux f) rest) ∧ uniqueOwners rest

poolEmpty : M.Mux → Bool
poolEmpty m with M.runningJobs m | M.waiting m
... | [] | [] = true
... | _ | _ = false
normalTerminal : M.Mux → Bool
normalTerminal m with M.status m | M.callback m
... | M.stopped | M.returned = true
... | _ | _ = false
syncTerminal : ErrorId → M.Mux → Bool
syncTerminal err m with M.callback m
... | M.tracerFailed _ = true -- synchronous tracer errors need not write Failed
... | M.returned with M.status m
...   | M.failed actual = does (ErrorId.errorNumber err Nat.≟ ErrorId.errorNumber actual)
...   | _ = false
syncTerminal _ _ | _ = false
asyncTerminal : ErrorId → M.Mux → Bool
asyncTerminal err m with M.status m | M.callback m
... | M.failed actual | M.readActive M.muxStopped = does (ErrorId.errorNumber err Nat.≟ ErrorId.errorNumber actual)
... | M.failed actual | M.commitTrace _ M.muxStopped = does (ErrorId.errorNumber err Nat.≟ ErrorId.errorNumber actual)
... | M.failed actual | M.returned = does (ErrorId.errorNumber err Nat.≟ ErrorId.errorNumber actual)
... | _ | _ = false

-- Exhaustive phase cases make additions to lifecycle control reviewable.
phaseValid : L.Frame → M.Mux → Bool
phaseValid f m with L.phase f
... | L.monitoring = true
... | L.poolClosing = true
... | L.poolClosed = poolEmpty m
... | L.deadTracing = poolEmpty m ∧ asyncTerminal (L.cancellationError f) m
... | L.bodyExited with M.callback m
...   | M.returned = poolEmpty m ∧ asyncTerminal (L.cancellationError f) m
...   | _ = false
phaseValid f m | L.normalClosing = normalTerminal m
phaseValid f m | L.normalClosed = poolEmpty m ∧ normalTerminal m
phaseValid f m | L.normalBodyExited = poolEmpty m ∧ normalTerminal m
phaseValid f m | L.syncClosing err = syncTerminal err m
phaseValid f m | L.syncClosed err = poolEmpty m ∧ syncTerminal err m
phaseValid f m | L.classifying err = poolEmpty m ∧ syncTerminal err m
phaseValid f m | L.peerRethrow err = poolEmpty m ∧ syncTerminal err m
phaseValid f m | L.nodeDelivery err = poolEmpty m ∧ syncTerminal err m
phaseValid f m | L.nodeRethrow err = poolEmpty m ∧ syncTerminal err m
phaseValid f m | L.peerBodyExited err = poolEmpty m ∧ syncTerminal err m
phaseValid f m | L.nodeBodyExited err = poolEmpty m ∧ syncTerminal err m
phaseValid f m | L.finalizing = poolEmpty m

cleanupValid : WorkerId → L.Phase → State → Bool
cleanupValid w L.finalizing s with lookup w (cleanups s)
... | just _ = true
... | nothing = false
cleanupValid w _ s with lookup w (cleanups s)
... | just _ = false
... | nothing = true

-- Captured resources remain allocated even after their map binding is purged.
resourcesPresent : HandlerStart → State → Bool
resourcesPresent h s with lookup (handlerEntry h) (entries (cm s)) | lookup (handlerSocket h) (sockets s)
... | just _ | just _ = true
... | _ | _ = false

-- Resolve ORIGINAL handler -> promise -> handle -> mux. Current CM map entries
-- and IG registration are deliberately not used: replacements are legitimate.
frameValid : WorkerId → L.Frame → Configuration → Bool
frameValid w f c with lookup w (handlers (world c))
... | nothing = false
... | just h with lookup (handlerPromise h) (handshakeResults (world c))
...   | just (negotiated hid _) with lookup hid (IG.handles (IG.execution (inboundGovernor c)))
...     | nothing = false
...     | just hd with lookup (L.capturedMux f) (IG.muxes (IG.execution (inboundGovernor c)))
...       | nothing = false
...       | just m = does (M.muxRef hd ≟ L.capturedMux f) ∧
          does (M.key m ≟ handlerKey h) ∧ resourcesPresent h (world c) ∧ phaseValid f m ∧ cleanupValid w (L.phase f) (world c)
frameValid w f c | just h | _ = false
framesValid : L.Runtime → Configuration → Bool
framesValid [] c = true
framesValid ((w , f) ∷ rest) c = frameValid w f c ∧ framesValid rest c
valid : Configuration → Bool
valid c = uniqueOwners (handlerLifecycles c) ∧ framesValid (handlerLifecycles c) c

-- Stronger coverage for a post-attachment segment: every installed mux has a
-- tracked owner. It is false during allocation-before-attachment by design.
covered : Store MuxId M.Mux → L.Runtime → Bool
covered [] rt = true
covered ((mid , _) ∷ rest) rt = L.hasMux mid rt ∧ covered rest rt
fullyTracked : Configuration → Bool
fullyTracked c = valid c ∧ covered (IG.muxes (IG.execution (inboundGovernor c))) (handlerLifecycles c)
