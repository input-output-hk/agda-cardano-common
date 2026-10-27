{-# OPTIONS --guardedness #-}

-- CM's bulk-send/collective-wait coordinator at Core.hs:523-550. Snapshot
-- controls are local source-model fixtures; the final product witness pairs
-- actual admission steps with an already closed empty coordinator. It is not
-- a full Server execution or a completed whole-node shutdown theorem.
module ConnectionManagement.Negative.CMShutdown where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (put; lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.CSP.Fixtures as F
open import ConnectionManagement.Scenarios.Admission using (key₀; key₁; child₀)

e₀ e₁ e₂ : EntryId
e₀ = ident 0
e₁ = ident 1
e₂ = ident 2
w₀ w₁ historical : WorkerId
w₀ = ident 10
w₁ = ident 11
historical = ident 12
noneAvailable allAvailable firstAvailable : WorkerId → Bool
noneAvailable _ = false
allAvailable _ = true
firstAvailable (ident 10) = true
firstAvailable _ = false

-- e₂'s handler is still in the heap, but its entry is absent from the map.
-- The second captured entry has no handler at snapshot time.
current : S.CMStore
current = S.cmStore (S.full (S.insertConnection key₁ e₁ (S.insertConnection key₀ e₀ [])))
  ((e₀ , S.unnegotiated outbound key₀ w₀) ∷
   (e₁ , S.reservedOutbound) ∷
   (e₂ , S.unnegotiated outbound key₁ historical) ∷ []) 3
late : S.CMStore
late = record current { entries = put e₁ (S.unnegotiated outbound key₁ w₁) (S.entries current) }
removed : S.CMStore
removed = record current { entries = put e₀ (S.terminated nothing) (S.entries current) }
n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 : Close.State
n1 = Close.shutdownState Close.reading (e₀ ∷ e₁ ∷ []) (e₀ ∷ e₁ ∷ []) []
n2 = Close.shutdownState (Close.sendReady e₀ w₀) (e₀ ∷ e₁ ∷ []) (e₁ ∷ []) []
n3 = record n2 { phase = Close.awaitDelivery e₀ w₀ }
n4 = Close.shutdownState Close.reading (e₀ ∷ e₁ ∷ []) (e₁ ∷ []) (w₀ ∷ [])
n5 = Close.shutdownState (Close.sendReady e₁ w₁) (e₀ ∷ e₁ ∷ []) [] (w₀ ∷ [])
n6 = record n5 { phase = Close.awaitDelivery e₁ w₁ }
n7 = Close.shutdownState Close.reading (e₀ ∷ e₁ ∷ []) [] (w₀ ∷ w₁ ∷ [])
n8 = record n7 { phase = Close.awaitResults }
n9 = record n8 { phase = Close.closed }
n10 = record n1 { remaining = e₁ ∷ [] }
capture-current-map : Close.step current noneAvailable Close.captureSnapshot Close.initialState ≡ just n1
capture-current-map = refl
first-late-read : Close.step current noneAvailable Close.readEntry n1 ≡ just n2
first-late-read = refl
first-send : Close.step current noneAvailable Close.requestCancellation n2 ≡ just n3
first-send = refl
first-receipt : Close.step current noneAvailable Close.acknowledgeDelivery n3 ≡ just n4
first-receipt = refl
second-state-read-late : Close.step late noneAvailable Close.readEntry n4 ≡ just n5
second-state-read-late = refl
second-send : Close.step late noneAvailable Close.requestCancellation n5 ≡ just n6
second-send = refl
second-receipt : Close.step late noneAvailable Close.acknowledgeDelivery n6 ≡ just n7
second-receipt = refl
all-sends-before-wait : Close.step late noneAvailable Close.finishTraversal n7 ≡ just n8
all-sends-before-wait = refl
collective-result-wait : Close.step late allAvailable Close.finishClose n8 ≡ just n9
collective-result-wait = refl
no-wait-before-second-send : Close.step current allAvailable Close.finishTraversal n4 ≡ nothing
no-wait-before-second-send = refl
no-close-before-second-send : Close.step current allAvailable Close.finishClose n4 ≡ nothing
no-close-before-second-send = refl
receipt-is-not-result : Close.step late noneAvailable Close.finishClose n8 ≡ nothing
receipt-is-not-result = refl
one-result-is-not-all-results : Close.step late firstAvailable Close.finishClose n8 ≡ nothing
one-result-is-not-all-results = refl
removed-state-read-skips-handler : Close.step removed noneAvailable Close.readEntry n1 ≡ just n10
removed-state-read-skips-handler = refl
historical-handler-excluded : Close.collected n9 ≡ w₀ ∷ w₁ ∷ []
historical-handler-excluded = refl
no-second-map-snapshot : Close.step late allAvailable Close.captureSnapshot n8 ≡ nothing
no-second-map-snapshot = refl
map-lock-blocks-snapshot : Close.step (record current { mapCell = S.taken w₀ }) noneAvailable Close.captureSnapshot Close.initialState ≡ nothing
map-lock-blocks-snapshot = refl

bulkActions : List Close.Action
bulkActions = Close.captureSnapshot ∷ Close.readEntry ∷ Close.requestCancellation ∷
  Close.acknowledgeDelivery ∷ Close.readEntry ∷ Close.requestCancellation ∷
  Close.acknowledgeDelivery ∷ Close.finishTraversal ∷ Close.finishClose ∷ []
bulk-path : Close.Executes Close.initialState bulkActions n9
bulk-path = Close.next {current = current} {available = noneAvailable} capture-current-map
  (Close.next {current = current} {available = noneAvailable} first-late-read
  (Close.next {current = current} {available = noneAvailable} first-send
  (Close.next {current = current} {available = noneAvailable} first-receipt
  (Close.next {current = late} {available = noneAvailable} second-state-read-late
  (Close.next {current = late} {available = noneAvailable} second-send
  (Close.next {current = late} {available = noneAvailable} second-receipt
  (Close.next {current = late} {available = noneAvailable} all-sends-before-wait
  (Close.next {current = late} {available = allAvailable} collective-result-wait Close.done))))))))

-- Different captured bindings may refer to the same TVar/Async. Preserve both
-- reads and both sends instead of silently replacing source traversal by a set.
duplicateStore : S.CMStore
duplicateStore = record current { mapCell = S.full
  (S.insertConnection key₁ e₀ (S.insertConnection key₀ e₀ [])) }
d1 d2 d3 d4 d5 d6 d7 : Close.State
d1 = Close.shutdownState Close.reading (e₀ ∷ e₀ ∷ []) (e₀ ∷ e₀ ∷ []) []
d2 = Close.shutdownState (Close.sendReady e₀ w₀) (e₀ ∷ e₀ ∷ []) (e₀ ∷ []) []
d3 = record d2 { phase = Close.awaitDelivery e₀ w₀ }
d4 = Close.shutdownState Close.reading (e₀ ∷ e₀ ∷ []) (e₀ ∷ []) (w₀ ∷ [])
d5 = Close.shutdownState (Close.sendReady e₀ w₀) (e₀ ∷ e₀ ∷ []) [] (w₀ ∷ [])
d6 = record d5 { phase = Close.awaitDelivery e₀ w₀ }
d7 = Close.shutdownState Close.reading (e₀ ∷ e₀ ∷ []) [] (w₀ ∷ w₀ ∷ [])
duplicate-snapshot : Close.step duplicateStore noneAvailable Close.captureSnapshot Close.initialState ≡ just d1
duplicate-snapshot = refl
duplicate-read1 : Close.step duplicateStore noneAvailable Close.readEntry d1 ≡ just d2
duplicate-read1 = refl
duplicate-send1 : Close.step duplicateStore noneAvailable Close.requestCancellation d2 ≡ just d3
duplicate-send1 = refl
duplicate-receipt1 : Close.step duplicateStore noneAvailable Close.acknowledgeDelivery d3 ≡ just d4
duplicate-receipt1 = refl
duplicate-read2 : Close.step duplicateStore noneAvailable Close.readEntry d4 ≡ just d5
duplicate-read2 = refl
duplicate-send2 : Close.step duplicateStore noneAvailable Close.requestCancellation d5 ≡ just d6
duplicate-send2 = refl
duplicate-receipt2 : Close.step duplicateStore noneAvailable Close.acknowledgeDelivery d6 ≡ just d7
duplicate-receipt2 = refl
duplicate-async-refs-retained : Close.collected d7 ≡ w₀ ∷ w₀ ∷ []
duplicate-async-refs-retained = refl

-- A tiny executable product exposes the actual chronological boundary. Its
-- runtime side delegates to Inbound.advance; no Server entry or result is
-- fabricated, and coordinator closure never freezes that independent side.
record Pair : Set where
  constructor paired
  field runtime : Inbound.Configuration
        coordinator : Close.State
open Pair public
data Event : Set where
  core : Inbound.Action → Event
  shutdown : Close.Action → Event
step : Event → Pair → Maybe Pair
step (core action) (paired runtime owner) with Inbound.advance action runtime
... | nothing = nothing
... | just runtime′ = just (paired runtime′ owner)
step (shutdown action) (paired runtime owner) with Close.step (S.cm (Inbound.world runtime)) noneAvailable action owner
... | nothing = nothing
... | just owner′ = just (paired runtime owner′)
data Interleaves : Pair → List Event → Pair → Set where
  done : ∀ {s} → Interleaves s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Interleaves s₁ as s₂ → Interleaves s (a ∷ as) s₂
append : ∀ {s as t bs u} → Interleaves s as t → Interleaves t bs u → Interleaves s (as ++ bs) u
append done right = right
append (next eq left) right = next eq (append left right)
core-step : ∀ {runtime runtime′ owner action} → Inbound.advance action runtime ≡ just runtime′ →
  step (core action) (paired runtime owner) ≡ just (paired runtime′ owner)
core-step eq rewrite eq = refl
lift-core : ∀ {runtime runtime′ actions owner} → Inbound.Executes runtime actions runtime′ →
  Interleaves (paired runtime owner) (map core actions) (paired runtime′ owner)
lift-core Inbound.done = done
lift-core {owner = owner} (Inbound.next {c = before} {c₁ = after} {a = action} eq rest) =
  next (core-step {runtime = before} {runtime′ = after} {owner = owner} {action = action} eq) (lift-core rest)
emptyCaptured emptyWaiting emptyClosed : Close.State
emptyCaptured = Close.shutdownState Close.reading [] [] []
emptyWaiting = Close.shutdownState Close.awaitResults [] [] []
emptyClosed = Close.shutdownState Close.closed [] [] []
empty-capture : step (shutdown Close.captureSnapshot) (paired F.start Close.initialState) ≡ just (paired F.start emptyCaptured)
empty-capture = refl
empty-traversal : step (shutdown Close.finishTraversal) (paired F.start emptyCaptured) ≡ just (paired F.start emptyWaiting)
empty-traversal = refl
empty-close-with-no-results : step (shutdown Close.finishClose) (paired F.start emptyWaiting) ≡ just (paired F.start emptyClosed)
empty-close-with-no-results = refl
emptyCloseActions : List Event
emptyCloseActions = shutdown Close.captureSnapshot ∷ shutdown Close.finishTraversal ∷ shutdown Close.finishClose ∷ []
empty-close-path : Interleaves (paired F.start Close.initialState) emptyCloseActions (paired F.start emptyClosed)
empty-close-path = next empty-capture (next empty-traversal (next empty-close-with-no-results done))
server-after-empty-close : Interleaves (paired F.start emptyClosed) (map core F.admit) (paired F.waiting emptyClosed)
server-after-empty-close = lift-core F.admit-path
chronological-closed-then-admitted : Interleaves (paired F.start Close.initialState)
  (emptyCloseActions ++ map core F.admit) (paired F.waiting emptyClosed)
chronological-closed-then-admitted = append empty-close-path server-after-empty-close
late-handler-exists : lookup child₀ (S.handlers (Inbound.world (runtime (paired F.waiting emptyClosed)))) ≡
  just (S.handlerStart (ident 0) (ident 0) (ident 0) key₀)
late-handler-exists = refl
late-socket-is-owned : lookup (ident 0) (S.sockets (Inbound.world F.waiting)) ≡ just (S.handling child₀)
late-socket-is-owned = refl
closed-snapshot-still-empty : Close.snapshot (coordinator (paired F.waiting emptyClosed)) ≡ []
closed-snapshot-still-empty = refl

-- Exercise the generic certificate: closure retains the actual final oracle
-- observation and a drained traversal, rather than assuming delivery is join.
import ConnectionManagement.Properties.CMShutdown as Facts
open import Data.Product using (_×_; proj₂)
bulk-close-certificate : (Close.remaining n9 ≡ []) × Facts.FinalWait n9
bulk-close-certificate = Facts.closed-from-initial bulk-path refl
bulk-observed-at-its-final-wait : Facts.Observed (Facts.available (proj₂ bulk-close-certificate)) n9
bulk-observed-at-its-final-wait = Facts.observed-at-wait (proj₂ bulk-close-certificate)
