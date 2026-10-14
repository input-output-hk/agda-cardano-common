{-# OPTIONS --guardedness #-}

-- Prefix-composed witnesses are conditional on the abstract handler publication
-- boundary. Direct branch fixtures below do not assert whole-source reachability.
module ConnectionManagement.Scenarios.Handshake where

open import Data.List using (List; []; _∷_; replicate)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Rules.Server using (stepPrefix; take)
import ConnectionManagement.Rules.Server as Server
open import ConnectionManagement.Rules.Handshake
open import ConnectionManagement.Scenarios.Admission using
  (runPrefix; prefix₀; fixture; emptyCM; w₀; w₁; child₀; oldChild; r₀; key₀)
open import ConnectionManagement.Properties.Entries using
  (heap-update-preserves-map-references)
open import ConnectionManagement.Properties.Handshake using
  (success-preserves-map; success-preserves-references)

-- Failure propagation keeps failed setup from becoming a successful witness.
bind : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
bind nothing f = nothing
bind (just x) f = f x

deliver : HandshakeResult → State → Maybe State
deliver result s with publishBoundary child₀ result s
... | just (published s′) = just s′
... | _ = nothing

runHandshake : ResponderMode → List HandshakeAction → State → Maybe State
runHandshake mode [] s = just s
runHandshake mode (a ∷ as) s =
  bind (stepHandshake mode w₀ a s) (runHandshake mode as)

waiting : Maybe State
waiting = runPrefix prefix₀ (fixture emptyCM)

success : HandshakeResult
success = negotiated (ident 0) duplex

info : NewConnectionInfo
info = newConnectionInfo inbound key₀ duplex (ident 0)

resume : HandshakeResult → ResponderMode → List HandshakeAction → Maybe State
resume result mode actions =
  bind (bind waiting (deliver result)) (runHandshake mode actions)

successActions : List HandshakeAction
successActions = readResult ∷ commitResult ∷ readResultCounters ∷ enqueueInbound ∷ returnResult ∷ []

resultPC : State → Maybe AdmissionPC
resultPC s = map pc (lookup w₀ (admissions s))

success-completes : map resultPC (resume success responderMode successActions)
  ≡ just (just (completedHandshake (connected info)))
success-completes = refl

success-notifies : map inboundInfo (resume success responderMode successActions)
  ≡ just (info ∷ [])
success-notifies = refl

success-updates-captured-entry :
  map (λ s → lookup (ident 0) (entries (cm s))) (resume success responderMode successActions)
  ≡ just (just (inboundIdle key₀ child₀ (ident 0) duplex))
success-updates-captured-entry = refl

-- Reading a promise leaves its result available; no implicit consumption.
promise-survives-read :
  map (λ s → lookup (ident 0) (handshakeResults s))
    (resume success responderMode (readResult ∷ [])) ≡ just (just success)
promise-survives-read = refl

empty-promise-waits : bind waiting (stepHandshake responderMode w₀ readResult) ≡ nothing
empty-promise-waits = refl

duplicate-publication-throws :
  bind (bind waiting (deliver success)) (publishBoundary child₀ query) ≡ just writerBlocked
duplicate-publication-throws = refl

-- The child's publication can precede the parent's map publication. It does not
-- require lookup of the connection's map binding.
earlyPublication : Maybe State
earlyPublication = bind
  (bind (runPrefix ((w₀ , Server.take) ∷ (w₀ , Server.countLimit) ∷
    (w₀ , Server.allocatePromise) ∷ (w₀ , Server.chooseEntry) ∷
    (w₀ , Server.fork) ∷ []) (fixture emptyCM)) (deliver success))
  (runPrefix ((w₀ , Server.putMapBack) ∷ (w₀ , Server.readCounters) ∷ []))

early-publication-is-readable :
  map resultPC (bind earlyPublication (stepHandshake responderMode w₀ readResult))
  ≡ just (just (commitHandshake (ident 0) success))
early-publication-is-readable = refl

-- Second caller really takes the map between result read and entry commit.
lockedAfterRead : HandshakeResult → Maybe State
lockedAfterRead result = bind (resume result responderMode (readResult ∷ [])) (stepPrefix w₁ take)

success-commit-under-lock :
  map (λ s → lookup (ident 0) (entries (cm s)))
    (bind (lockedAfterRead success) (stepHandshake responderMode w₀ commitResult))
  ≡ just (just (inboundIdle key₀ child₀ (ident 0) duplex))
success-commit-under-lock = refl

counter-read-waits-for-map :
  bind (lockedAfterRead success)
    (runHandshake responderMode (commitResult ∷ readResultCounters ∷ [])) ≡ nothing
counter-read-waits-for-map = refl

query-commit-needs-map :
  bind (lockedAfterRead query) (stepHandshake responderMode w₀ commitResult) ≡ nothing
query-commit-needs-map = refl

failureActions : List HandshakeAction
failureActions = readResult ∷ commitResult ∷ readResultCounters ∷ returnResult ∷ []

query-completes-disconnected : map resultPC (resume query responderMode failureActions)
  ≡ just (just (completedHandshake (disconnected handshakeQuery)))
query-completes-disconnected = refl

query-removes-map-binding : map (λ s → mapCell (cm s)) (resume query responderMode failureActions)
  ≡ just (full [])
query-removes-map-binding = refl

query-retains-terminated-entry :
  map (λ s → lookup (ident 0) (entries (cm s))) (resume query responderMode failureActions)
  ≡ just (just (terminated nothing))
query-retains-terminated-entry = refl

failure-enters-terminating :
  map (λ s → lookup (ident 0) (entries (cm s)))
    (resume (handlerError negotiationFailure (errorId 7)) responderMode failureActions)
  ≡ just (just (terminating key₀ child₀ (just (errorId 7))))
failure-enters-terminating = refl

violation-enters-terminated :
  map (λ s → lookup (ident 0) (entries (cm s)))
    (resume (handlerError protocolViolation (errorId 7)) responderMode failureActions)
  ≡ just (just (terminated (just (errorId 7))))
violation-enters-terminated = refl

no-responder-skips-queue :
  map inboundInfo (resume success noResponderMode failureActions) ≡ just []
no-responder-skips-queue = refl

-- Direct guard fixture: the production channel capacity is 100, not a finite
-- explorer cutoff. IG draining will be modeled separately.
fullQueue : State → State
fullQueue s = record s { inboundInfo = replicate 100 info }

full-info-queue-waits :
  bind (map fullQueue (resume success responderMode
      (readResult ∷ commitResult ∷ readResultCounters ∷ [])))
    (stepHandshake responderMode w₀ enqueueInbound) ≡ nothing
full-info-queue-waits = refl

-- Direct source-branch checks, especially the self-connection race cases.
reserved-is-exception : decideSuccess r₀ (ident 0) duplex reservedOutbound ≡ impossible
reserved-is-exception = refl

outbound-uni-retained :
  decideSuccess r₀ (ident 0) duplex (outboundUni key₀ oldChild (ident 1)) ≡ retain outbound
outbound-uni-retained = refl

outbound-dup-retained :
  decideSuccess r₀ (ident 0) duplex (outboundDup key₀ oldChild (ident 1) ticking) ≡ retain outbound
outbound-dup-retained = refl

outbound-idle-keeps-old-flow :
  decideSuccess r₀ (ident 0) duplex (outboundIdle key₀ oldChild (ident 1) unidirectional)
  ≡ update (inboundIdle key₀ child₀ (ident 0) unidirectional) outbound
outbound-idle-keeps-old-flow = refl

inbound-idle-is-exception :
  decideSuccess r₀ (ident 0) duplex (inboundIdle key₀ oldChild (ident 1) duplex) ≡ impossible
inbound-idle-is-exception = refl

inbound-active-is-exception :
  decideSuccess r₀ (ident 0) duplex (inboundActive key₀ oldChild (ident 1) duplex) ≡ impossible
inbound-active-is-exception = refl

duplex-is-exception :
  decideSuccess r₀ (ident 0) duplex (duplexActive key₀ oldChild (ident 1)) ≡ impossible
duplex-is-exception = refl

terminating-disconnects :
  decideSuccess r₀ (ident 0) duplex (terminating key₀ oldChild nothing)
  ≡ disconnect (inTerminating nothing)
terminating-disconnects = refl

terminated-disconnects :
  decideSuccess r₀ (ident 0) duplex (terminated nothing) ≡ disconnect (inTerminated nothing)
terminated-disconnects = refl

-- Replacement fixture: this is an assumed concurrent update, not yet a trace
-- generated by handler cleanup/outbound rules. Error processing must not purge it.
replaceBinding : State → State
replaceBinding s = record s { cm = record (cm s)
  { mapCell = full (insertConnection key₀ (ident 1) [])
  ; entries = put (ident 1) reservedOutbound (entries (cm s))
  ; nextEntry = 2 } }

staleQuery : Maybe State
staleQuery = bind (map replaceBinding (resume query responderMode (readResult ∷ [])))
  (stepHandshake responderMode w₀ commitResult)

stale-error-preserves-map : map (λ s → mapCell (cm s)) staleQuery
  ≡ just (full (insertConnection key₀ (ident 1) []))
stale-error-preserves-map = refl

stale-error-preserves-old-entry : map (λ s → lookup (ident 0) (entries (cm s))) staleQuery
  ≡ just (just (unnegotiated inbound key₀ child₀))
stale-error-preserves-old-entry = refl

-- OutboundIdle's stored flow and the reported negotiated flow deliberately differ
-- in this branch fixture: the source uses oldFlow for the entry, result flow for
-- NewConnection/Connected. This is branch coverage, not a claimed source defect.
outboundIdleAfterRead : State → State
outboundIdleAfterRead s = record s { cm = record (cm s)
  { entries = put (ident 0) (outboundIdle key₀ oldChild (ident 1) unidirectional)
                  (entries (cm s)) } }

outboundRace : Maybe State
outboundRace = bind (map outboundIdleAfterRead
    (resume success responderMode (readResult ∷ [])))
  (runHandshake responderMode (commitResult ∷ readResultCounters ∷ enqueueInbound ∷ returnResult ∷ []))

outbound-race-reports-result-flow : map inboundInfo outboundRace
  ≡ just (newConnectionInfo outbound key₀ duplex (ident 0) ∷ [])
outbound-race-reports-result-flow = refl

outbound-race-retains-entry-flow : map (λ s → lookup (ident 0) (entries (cm s))) outboundRace
  ≡ just (just (inboundIdle key₀ child₀ (ident 0) unidirectional))
outbound-race-retains-entry-flow = refl
