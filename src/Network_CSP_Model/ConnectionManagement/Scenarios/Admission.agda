{-# OPTIONS --guardedness #-}

-- Executable prefix witnesses and negative controls. Fixtures begin after
-- accepted-socket handoff; handshake, IG and OG are not executed here.
module ConnectionManagement.Scenarios.Admission where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Rules.CM
open import ConnectionManagement.Rules.Server
open import ConnectionManagement.Properties.MapLocks using
  (taken-blocks; restore-preserves-heap; other-owner-cannot-put;
   captured-write-preserves-lock)

-- This finite driver propagates failure rather than substituting a default state.
runPrefix : List (WorkerId × AdmissionAction) → State → Maybe State
runPrefix [] s = just s
runPrefix ((w , a) ∷ as) s with stepPrefix w a s
... | nothing = nothing
... | just s′ = runPrefix as s′

localAddr remoteAddr otherRemote : PeerAddr
localAddr = addr ipv4 0 3001
remoteAddr = addr ipv4 1 3001
otherRemote = addr ipv4 2 3001

key₀ key₁ : ConnectionKey
key₀ = connection localAddr remoteAddr
key₁ = connection localAddr otherRemote

w₀ w₁ child₀ child₁ oldChild : WorkerId
w₀ = ident 0
w₁ = ident 1
child₀ = ident 2
child₁ = ident 3
oldChild = ident 4

r₀ r₁ : Admission
r₀ = admission key₀ (ident 0) child₀ 10
r₁ = admission key₁ (ident 1) child₁ 10

-- Both sockets are already accepted; workers are ready to call include.
fixture : CMStore → State
fixture c = state c
  ((w₀ , admissionWorker r₀ acquireMap) ∷ (w₁ , admissionWorker r₁ acquireMap) ∷ [])
  [] ((ident 0 , admitting w₀) ∷ (ident 1 , admitting w₁) ∷ []) [] 0 [] [] []

emptyCM : CMStore
emptyCM = cmStore (full []) [] 0

prefix₀ : List (WorkerId × AdmissionAction)
prefix₀ = (w₀ , take) ∷ (w₀ , countLimit) ∷ (w₀ , allocatePromise) ∷
          (w₀ , chooseEntry) ∷ (w₀ , fork) ∷ (w₀ , putMapBack) ∷
          (w₀ , readCounters) ∷ []

-- Successful prefix reaches the actual next wait, with the child recorded.
admission-reaches-handshake :
  map (λ s → map pc (lookup w₀ (admissions s))) (runPrefix prefix₀ (fixture emptyCM))
  ≡ just (just (awaitHandshake (ident 0) (ident 0)))
admission-reaches-handshake = refl

child-gets-selected-entry :
  map (λ s → lookup child₀ (handlers s)) (runPrefix prefix₀ (fixture emptyCM))
  ≡ just (just (handlerStart (ident 0) (ident 0) (ident 0) key₀))
child-gets-selected-entry = refl

-- An entry constructor has the exact inbound-counter projection of Core.hs.
counterExample : ℕ × ℕ
counterExample = (inboundCount (outboundDup key₀ oldChild (ident 0) ticking) ,
                  inboundCount (duplexActive key₀ oldChild (ident 0)))

counters-distinguish-capability-from-use : counterExample ≡ (0 , 1)
counters-distinguish-capability-from-use = refl

withOld : ConnectionState → CMStore
withOld st = cmStore (full (insertConnection key₀ (ident 0) []))
                    ((ident 0 , st) ∷ []) 1

-- Overwrite keeps the entry, whereas replacing a terminating entry is fresh.
reserved-keeps-entry :
  map (λ s → nextEntry (cm s)) (runPrefix prefix₀ (fixture (withOld reservedOutbound))) ≡ just 1
reserved-keeps-entry = refl

unnegotiated-keeps-entry :
  map (λ s → lookup (ident 0) (entries (cm s)))
      (runPrefix prefix₀ (fixture (withOld (unnegotiated outbound key₀ oldChild))))
  ≡ just (just (unnegotiated inbound key₀ child₀))
unnegotiated-keeps-entry = refl

terminating-replaced :
  map (λ s → mapCell (cm s))
      (runPrefix prefix₀ (fixture (withOld (terminating key₀ oldChild nothing))))
  ≡ just (full (insertConnection key₀ (ident 1) []))
terminating-replaced = refl

old-entry-survives-replacement :
  map (λ s → lookup (ident 0) (entries (cm s)))
      (runPrefix prefix₀ (fixture (withOld (terminating key₀ oldChild nothing))))
  ≡ just (just (terminating key₀ oldChild nothing))
old-entry-survives-replacement = refl

-- A source lookup at a known local address must not consume a wildcard entry.
unknown-local-is-not-exact :
  lookupConnection key₀ (insertLocal remoteAddr unknownLocal (ident 0) []) ≡ nothing
unknown-local-is-not-exact = refl

reject₀ : List (WorkerId × AdmissionAction)
reject₀ = (w₀ , take) ∷ (w₀ , countLimit) ∷ (w₀ , allocatePromise) ∷
          (w₀ , chooseEntry) ∷ (w₀ , restore) ∷ (w₀ , close) ∷ []

established-rejected-and-closed :
  map (λ s → lookup (ident 0) (sockets s))
      (runPrefix reject₀ (fixture (withOld (inboundIdle key₀ oldChild (ident 0) duplex))))
  ≡ just (just closed)
established-rejected-and-closed = refl

rejection-keeps-old-entry :
  map (λ s → lookup (ident 0) (entries (cm s)))
      (runPrefix reject₀ (fixture (withOld (inboundIdle key₀ oldChild (ident 0) duplex))))
  ≡ just (just (inboundIdle key₀ oldChild (ident 0) duplex))
rejection-keeps-old-entry = refl

-- Failure after the entry commit restores only the map, not the overwritten TVar.
forkFailure₀ : List (WorkerId × AdmissionAction)
forkFailure₀ = (w₀ , take) ∷ (w₀ , countLimit) ∷ (w₀ , allocatePromise) ∷
               (w₀ , chooseEntry) ∷ (w₀ , failFork) ∷ (w₀ , restore) ∷ (w₀ , close) ∷ []

failed-fork-retains-committed-write :
  map (λ s → lookup (ident 0) (entries (cm s)))
      (runPrefix forkFailure₀ (fixture (withOld reservedOutbound)))
  ≡ just (just (unnegotiated inbound key₀ child₀))
failed-fork-retains-committed-write = refl

-- A second caller cannot take the map during the first caller's IO body.
second-take-blocked :
  runPrefix ((w₀ , take) ∷ (w₁ , take) ∷ []) (fixture emptyCM) ≡ nothing
second-take-blocked = refl

-- Source traceCounters is a separate map read after the first caller's put.
post-publication-count-can-block :
  runPrefix ((w₀ , take) ∷ (w₀ , countLimit) ∷ (w₀ , allocatePromise) ∷
             (w₀ , chooseEntry) ∷ (w₀ , fork) ∷ (w₀ , putMapBack) ∷
             (w₁ , take) ∷ (w₀ , readCounters) ∷ []) (fixture emptyCM) ≡ nothing
post-publication-count-can-block = refl

-- Hard-limit rejection occurs before promise/entry/handler allocation.
limitFixture : State
limitFixture = record (fixture emptyCM)
  { admissions = (w₀ , admissionWorker (record r₀ { hardLimit = 0 }) acquireMap) ∷ [] }

hard-limit-closes-without-handler :
  map (λ s → handlers s , promises s)
    (runPrefix ((w₀ , take) ∷ (w₀ , countLimit) ∷ (w₀ , putMapBack) ∷
                (w₀ , close) ∷ []) limitFixture) ≡ just ([] , [])
hard-limit-closes-without-handler = refl

-- Both admissions can publish without losing the other remote's binding.
prefix₁ : List (WorkerId × AdmissionAction)
prefix₁ = (w₁ , take) ∷ (w₁ , countLimit) ∷ (w₁ , allocatePromise) ∷
          (w₁ , chooseEntry) ∷ (w₁ , fork) ∷ (w₁ , putMapBack) ∷
          (w₁ , readCounters) ∷ []

open import Data.Maybe using (_>>=_)

bothPublished : Maybe State
bothPublished = runPrefix prefix₀ (fixture emptyCM) >>= runPrefix prefix₁

two-callers-publish-distinct-entries :
  map (λ s → nextEntry (cm s)) bothPublished ≡ just 2
two-callers-publish-distinct-entries = refl

first-caller-binding-retained :
  map (λ s → mapCell (cm s)) bothPublished ≡ just
    (full (insertConnection key₁ (ident 1) (insertConnection key₀ (ident 0) [])))
first-caller-binding-retained = refl
