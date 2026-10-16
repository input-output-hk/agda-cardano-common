{-# OPTIONS --guardedness #-}

-- Candidate: bracketOnError cannot release a socket whose acquisition threw.
-- This checked model trace is not an IOSim replay or a confirmed source defect.
module ConnectionManagement.CSP.OutboundOpenFailure where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.Machine as Inbound
open import ConnectionManagement.OutboundMachine
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.CSP.OutboundAdmission as O
import ConnectionManagement.CSP.Fixtures as F
open import ConnectionManagement.Scenarios.Admission using (key₀)
open import ConnectionManagement.CSP.Outbound using (Process; trace-intro; Channel; label)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

failed returned retrying rejected counted doneRetry : Configuration
failed = O.at (A.complete (C.raised (C.ioFailure (errorId 1)))) O.promised
returned = record failed { acquiring = []; acquired = (O.caller , C.raised (C.ioFailure (errorId 1))) ∷ [] }
retrying = record returned { acquiring = (ident 20 , A.frame O.req A.selecting) ∷ [] }
rejected = record returned { acquiring = (ident 20 , A.frame O.req (A.count (A.complete (C.raised C.connectionExists)))) ∷ []; randomGeneration = 2 }
counted = record rejected { acquiring = (ident 20 , A.frame O.req (A.complete (C.raised C.connectionExists))) ∷ [] }
doneRetry = record counted { acquiring = []; acquired = put (ident 20) (C.raised C.connectionExists) (acquired returned) }
schedule : List Action
schedule = beginAcquire O.caller O.req ∷ acquire O.caller (A.select nothing) ∷
  acquire O.caller A.readCounters ∷ acquire O.caller A.newPromise ∷
  acquire O.caller (A.failIO (errorId 1)) ∷ acquire O.caller A.returnResult ∷
  beginAcquire (ident 20) O.req ∷ acquire (ident 20) (A.select (just (ident 0))) ∷
  acquire (ident 20) A.readCounters ∷ acquire (ident 20) A.returnResult ∷ []
path : Executes (initial F.start) schedule doneRetry
path = next {c₁ = O.begun} refl
  (next {c₁ = O.at (A.count (A.allocatePromise (ident 0))) O.reserved} refl
  (next {c₁ = O.at (A.allocatePromise (ident 0)) O.reserved} refl
  (next {c₁ = O.at (A.openSocket (ident 0) (ident 0)) O.promised} refl
  (next {c₁ = failed} refl (next {c₁ = returned} refl (next {c₁ = retrying} refl
  (next {c₁ = rejected} refl (next {c₁ = counted} refl (next refl done)))))))))
accepted : traces (Process (initial F.start)) (map label schedule)
accepted = trace-intro path
reservation-remains : S.mapCell (S.cm (Inbound.world (core doneRetry))) ≡
  S.full (S.insertLocal (remote key₀) unknownLocal (ident 0) [])
reservation-remains = refl
entry-remains : lookup (ident 0) (S.entries (S.cm (Inbound.world (core doneRetry)))) ≡ just S.reservedOutbound
entry-remains = refl
no-socket-to-clean : lookup O.sock (S.sockets (Inbound.world (core doneRetry))) ≡ nothing
no-socket-to-clean = refl
retry-rejected : lookup (ident 20) (acquired doneRetry) ≡ just (C.raised C.connectionExists)
retry-rejected = refl
