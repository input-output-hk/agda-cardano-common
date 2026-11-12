{-# OPTIONS --guardedness #-}

-- Source-independent transport for the auxiliary reference predicates. Job
-- phases may advance, but a captured result and a published mux remain fixed.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxTransport (b : ErrorId → Bool) where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (WorkerId; JobId)
open import ConnectionManagement.Store using (lookup; put)
import Class.DecEq
import Relation.Nullary
open import Function using (case_of_)
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.MuxJobTypes as Types
open import ConnectionManagement.Properties.LiveTrackerAuxContent b
 using (Owner; owner; JobContent; job-content; Completion; ProtocolResult; Infrastructure;
 ControlContent; PCContent; TicketContent; CancelContent)
module U = P.U
module Pool = P.Pool
import ConnectionManagement.MuxResultMonitor as Monitor
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.MuxDeltaQ as Delta
module M = Monitor b
module G = Group b
module D = Delta b

-- A retained owner can move its startup continuation, retaining every role
-- already born. Captures are not compared to mutable continuation snapshots.
record OwnerKept {w s t} (old : Owner w s) (new : Owner w t) : Set where
 field same-mux : Owner.mux new ≡ Owner.mux old
       roles : ∀ role j → P.infraId role (P.Startup.phase (U.startup (Owner.frame old))) ≡ just j →
          P.infraId role (P.Startup.phase (U.startup (Owner.frame new))) ≡ just j
record Retains (s t : P.State) : Set where
 field owners : ∀ w (old : Owner w s) → Σ (Owner w t) (OwnerKept old)
       handles : ∀ w j phase → lookup j (Pool.handles (P.poolAt w s)) ≡ just phase →
          Σ Pool.ThreadPhase (λ next → lookup j (Pool.handles (P.poolAt w t)) ≡ just next)
       jobs : ∀ j job → lookup j (P.jobs s) ≡ just job →
          Σ Types.BodyPhase (λ phase → lookup j (P.jobs t) ≡ just (record job { phase = phase }))
       captured : ∀ j w mid dir n gen result →
          lookup j (P.jobs s) ≡ just (Types.protocolJob w mid dir n gen (Types.resultCaptured result)) →
          lookup j (P.jobs t) ≡ just (Types.protocolJob w mid dir n gen (Types.resultCaptured result))

-- JobContent itself does not constrain the current body phase.
job-phase : ∀ j job phase s → JobContent j job s → JobContent j (record job { phase = phase }) s
job-phase j job phase s good = job-content (JobContent.owner-reference good)
 (JobContent.mux-matches good) (JobContent.physical-phase good) (JobContent.physical-found good)
job-kept : ∀ {s t} → Retains s t → ∀ j job → JobContent j job s → JobContent j job t
job-kept {s} {t} kept j job good with Retains.owners kept (Types.owner job) (JobContent.owner-reference good)
... | own , same with Retains.handles kept (Types.owner job) j (JobContent.physical-phase good) (JobContent.physical-found good)
... | phase , found = job-content own
 (trans (OwnerKept.same-mux same) (JobContent.mux-matches good)) phase found
infra-kept : ∀ {s t} → Retains s t → ∀ w item → Infrastructure w item s → Infrastructure w item t
infra-kept kept w item good with Retains.owners kept w (Infrastructure.owner-reference good)
... | own , same with Retains.handles kept w (Infrastructure.job good) (Infrastructure.physical-phase good) (Infrastructure.physical-found good)
... | phase , found = record
 { owner-reference = own; role = Infrastructure.role good; job = Infrastructure.job good
 ; error = Infrastructure.error good; tagged = Infrastructure.tagged good
 ; role-found = OwnerKept.roles same _ _ (Infrastructure.role-found good)
 ; physical-phase = phase; physical-found = found }
completion-kept : ∀ {s t} → Retains s t → ∀ w item → Completion w item s → Completion w item t
completion-kept kept w (Types.protocolCompletion dir n gen result) (j , mid , found , good) =
 j , mid , Retains.captured kept j w mid dir n gen result found , job-kept kept j _ good
completion-kept kept w (Types.infraMuxer err) good = infra-kept kept w _ good
completion-kept kept w (Types.infraDemuxer err) good = infra-kept kept w _ good
cancel-kept : ∀ {s t} → Retains s t → ∀ w pc → CancelContent w pc s → CancelContent w pc t
cancel-kept kept w G.ready good = tt
cancel-kept kept w (G.requested j) (phase , found) = Retains.handles kept w j phase found
cancel-kept kept w (G.delivered j) (phase , found) = Retains.handles kept w j phase found
control-kept : ∀ {s t} → Retains s t → ∀ w row → ControlContent w row s → ControlContent w row t
control-kept {s} {t} kept w row good = record
 { owner-reference = proj₁ (Retains.owners kept w (ControlContent.owner-reference good))
 ; cancellation-backed = cancel-kept kept w _ (ControlContent.cancellation-backed good)
 ; snapshot-backed = All.map snapshot (ControlContent.snapshot-backed good)
 ; remaining-backed = All.map (λ { {j} (phase , found) → Retains.handles kept w j phase found }) (ControlContent.remaining-backed good)
 ; joined-backed = All.map (λ { {j} (phase , found) → Retains.handles kept w j phase found }) (ControlContent.joined-backed good) }
 where
 snapshot : ∀ {j} → Σ Types.ProtocolJob (λ job → lookup j (P.jobs s) ≡ just job × Types.owner job ≡ w × JobContent j job s) →
   Σ Types.ProtocolJob (λ job → lookup j (P.jobs t) ≡ just job × Types.owner job ≡ w × JobContent j job t)
 snapshot {j} (job , found , owned , content) with Retains.jobs kept j job found
 ... | phase , next = record job { phase = phase } , next , owned , job-phase j job phase t (job-kept kept j job content)
pc-kept : ∀ {s t} → Retains s t → ∀ w pc → PCContent w pc s → PCContent w pc t
pc-kept kept w pc good = record
 { owner-reference = proj₁ (Retains.owners kept w (PCContent.owner-reference good))
 ; selected-backed = λ item eq → completion-kept kept w item (PCContent.selected-backed good item eq) }
ticket-kept : ∀ {s t} → Retains s t → ∀ w ticket → TicketContent w ticket s → TicketContent w ticket t
ticket-kept kept w saved good = record
 { owner-reference = proj₁ (Retains.owners kept w (TicketContent.owner-reference good))
 ; payload-backed = completion-kept kept w _ (TicketContent.payload-backed good) }

-- These identities let the upper source/peer observers ignore all CM fields.
identity : ∀ s → Retains s s
identity s = record
 { owners = λ w own → own , record { same-mux = refl; roles = λ role j found → found }
 ; handles = λ w j phase found → phase , found
 ; jobs = λ j job found → Types.phase job , found
 ; captured = λ j w mid dir n gen result found → found }
source : ∀ c s → Retains s (P.setSource c s)
source c s = record
 { owners = λ w old → owner (Owner.frame old) (Owner.handle old) (Owner.mux old)
     (Owner.found old) (Owner.published old) , record { same-mux = refl; roles = λ role j found → found }
 ; handles = λ w j phase found → phase , found
 ; jobs = λ j job found → Types.phase job , found
 ; captured = λ j w mid dir n gen result found → found }

-- Composition follows actual component writes; no whole-runtime equality is
-- required between them.
compose : ∀ {s t u} → Retains s t → Retains t u → Retains s u
compose first second = record
 { owners = λ w old → let a = Retains.owners first w old; z = Retains.owners second w (proj₁ a) in
     proj₁ z , record
       { same-mux = trans (OwnerKept.same-mux (proj₂ z)) (OwnerKept.same-mux (proj₂ a))
       ; roles = λ role j found → OwnerKept.roles (proj₂ z) role j (OwnerKept.roles (proj₂ a) role j found) }
 ; handles = λ w j phase found → let next = Retains.handles first w j phase found in
     Retains.handles second w j (proj₁ next) (proj₂ next)
 ; jobs = λ j job found → let next = Retains.jobs first j job found in
     Retains.jobs second j (record job { phase = proj₁ next }) (proj₂ next)
 ; captured = λ j w mid dir n gen result found → Retains.captured second j w mid dir n gen result
     (Retains.captured first j w mid dir n gen result found) }

-- Rebuilding indexed records is essential even for unchanged observed stores.
by-fields : ∀ s t → U.frames (P.base t) ≡ U.frames (P.base s) →
 (∀ w j phase → lookup j (Pool.handles (P.poolAt w s)) ≡ just phase →
   Σ Pool.ThreadPhase (λ next → lookup j (Pool.handles (P.poolAt w t)) ≡ just next)) →
 (∀ j job → lookup j (P.jobs s) ≡ just job →
   Σ Types.BodyPhase (λ phase → lookup j (P.jobs t) ≡ just (record job { phase = phase }))) →
 (∀ j w mid dir n gen result →
   lookup j (P.jobs s) ≡ just (Types.protocolJob w mid dir n gen (Types.resultCaptured result)) →
   lookup j (P.jobs t) ≡ just (Types.protocolJob w mid dir n gen (Types.resultCaptured result))) → Retains s t
by-fields s t frames handles jobs captured = record
 { owners = λ w old → owner (Owner.frame old) (Owner.handle old) (Owner.mux old)
     (trans (cong (lookup w) frames) (Owner.found old)) (Owner.published old) ,
     record { same-mux = refl; roles = λ role j found → found }
 ; handles = handles; jobs = jobs; captured = captured }

-- Uniform traversal-row access and replacement for controls, PCs and tickets.
module Rows {K V : Set} ⦃ dec : Class.DecEq.DecEq K ⦄ (C : K → V → Set) where
 at : ∀ rows → All (λ { (k , value) → C k value }) rows → ∀ k value → lookup k rows ≡ just value → C k value
 at [] [] k value ()
 at ((q , first) ∷ rows) (good ∷ rest) k value found with k Class.DecEq.≟ q
 ... | Relation.Nullary.yes refl = case just-injective found of λ { refl → good }
 ... | Relation.Nullary.no _ = at rows rest k value found
 insert : ∀ k value rows → C k value → All (λ { (k , value) → C k value }) rows →
   All (λ { (k , value) → C k value }) (ConnectionManagement.Store.put k value rows)
 insert k value [] good [] = good ∷ []
 insert k value ((q , first) ∷ rows) good (old ∷ rest) with k Class.DecEq.≟ q
 ... | Relation.Nullary.yes refl = good ∷ rest
 ... | Relation.Nullary.no _ = old ∷ insert k value rows good rest
