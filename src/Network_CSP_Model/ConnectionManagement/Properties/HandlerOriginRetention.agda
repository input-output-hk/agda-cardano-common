{-# OPTIONS --guardedness #-}

-- Stored entry identities survive enabled gaps in handler-origin histories.
-- A positive selection PC identifies the successful branch, not an oracle.
module ConnectionManagement.Properties.HandlerOriginRetention where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import ConnectionManagement.Domain using (EntryId; ErrorId; HandleId; WorkerId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (Present; lookup-put)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundAcquire as Acquire
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.CM as CM
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Properties.StateRetention as Retention
import ConnectionManagement.Properties.IGTableRetention as Tables
import ConnectionManagement.Properties.OutboundWorldInvariant as World
import ConnectionManagement.Properties.SubsystemInvariant as Subsystem
import ConnectionManagement.Properties.CallerCancellationCapture as CancelCapture
import ConnectionManagement.Properties.CallerCancellation as CancelWriter
import ConnectionManagement.Properties.ServerIGExitEntries as ServerEntries
import ConnectionManagement.Properties.ServerPeersHandlerResources as Origins
import ConnectionManagement.Properties.HandlerResources as Selection
import ConnectionManagement.ServerPeers as SharedModel

-- The generic observer covers source, detached cleanup and Server writers.
private module EntryLift (b io : ErrorId → Bool) (canInitiate : HandleId → ℕ → Bool) (entry : EntryId) where
 Predicate : S.State → IG.Runtime → Set
 Predicate world governor = Present entry (S.entries (S.cm world))
 stable : ∀ {before after governor next} → Retention.Retains before after → Tables.Retains governor next →
   Predicate before governor → Predicate after next
 stable retained tables = Retention.entriesRetained retained entry
 private module Raw = World.Lift Predicate stable using (advance-preserves)
 Q : Acquire.Runtime → S.State → Set
 Q runtime world = Present entry (S.entries (S.cm world))
 private module Sub = Subsystem.Lift Q Raw.advance-preserves using (advance-preserves)
 cleanup-preserves : ∀ action frame c {frame′ c′} → Cancel.step action frame c ≡ just (frame′ , c′) →
   Q (O.acquiring c) (I.world (O.core c)) → Q (O.acquiring c′) (I.world (O.core c′))
 cleanup-preserves action frame c actual = CancelCapture.step-retains action frame c actual entry
 start-preserves : ∀ worker err context c {frame c′} → Cancel.start worker err context c ≡ just (frame , c′) →
   Q (O.acquiring c) (I.world (O.core c)) → Q (O.acquiring c′) (I.world (O.core c′))
 start-preserves worker err context c actual present = subst
   (λ core → Present entry (S.entries (S.cm (I.world core))))
   (sym (CancelWriter.start-core worker err context c actual)) present
 private module Lift = Origins.Observer.Frontend b io Q Sub.advance-preserves cleanup-preserves start-preserves (ServerEntries.Entry.step-preserves b entry) canInitiate using (run-preserves)
 private module K = SharedModel b io using (source)
 private module T = SharedModel.Protocols b io canInitiate using (Runs; base)
 retained : ∀ {before gap after} → T.Runs before gap after →
   Present entry (S.entries (S.cm (I.world (O.core (K.source (T.base before)))))) →
   Present entry (S.entries (S.cm (I.world (O.core (K.source (T.base after))))))
 retained = Lift.run-preserves

module Frontend (b io : ErrorId → Bool) (canInitiate : HandleId → ℕ → Bool) where
 private module K = SharedModel b io using (serverStep; source)
 private module T = SharedModel.Protocols b io canInitiate using (Event; Runs; Runtime; advance; base)
 private module Old = Origins.Frontend b io canInitiate using (event; selection-lower)
 shared : T.Runtime → S.State
 shared state = I.world (O.core (K.source (T.base state)))
 core : T.Runtime → I.Configuration
 core state = O.core (K.source (T.base state))
 event : WorkerId → Admission.AdmissionAction → T.Event
 event = Old.event

 -- Entry presence is historical; neither map ownership nor initialization is needed.
 entry-retained : ∀ {before gap after entry} → T.Runs before gap after →
   Present entry (S.entries (S.cm (shared before))) → Present entry (S.entries (S.cm (shared after)))
 entry-retained {entry = entry} = EntryLift.retained b io canInitiate entry

 -- Selection may be denied. Its positive post-PC identifies the selected ID.
 private
  selected-source : ∀ worker req savedLease promise entry c {selected} →
    lookup worker (S.admissions (I.world c)) ≡ just (S.admissionWorker req (S.selectEntry savedLease promise)) →
    I.advance (I.admissionStep worker Admission.chooseEntry) c ≡ just selected →
    lookup worker (S.admissions (I.world selected)) ≡ just (S.admissionWorker req (S.forkHandler savedLease promise entry)) →
    Present entry (S.entries (S.cm (I.world selected)))
  selected-source worker req savedLease promise entry c owned actual selectedPC rewrite owned
    with CM.selectInbound savedLease req (S.cm (I.world c)) in chosen
  ... | nothing = case actual of λ ()
  ... | just CM.denied with just-injective actual
  ...   | refl = case just-injective (trans
    (sym (lookup-put worker (S.admissionWorker req (S.reject savedLease S.forbidden)) (S.admissions (I.world c)))) selectedPC) of λ ()
  selected-source worker req savedLease promise entry c owned actual selectedPC | just (CM.selected selectedEntry current) with just-injective actual
  ... | refl with just-injective (trans
    (sym (lookup-put worker (S.admissionWorker req (S.forkHandler savedLease promise selectedEntry)) (S.admissions (I.world c)))) selectedPC)
  ...   | refl = Selection.selected-exists savedLease req (S.cm (I.world c)) chosen

 -- Alias-aware history reconstruction supplies the actual primitive equation.
 -- Reuse the same positive-branch proof without substituting a canonical label.
 selected-entry-from-source : ∀ worker req savedLease promise entry c {selected} →
   lookup worker (S.admissions (I.world c)) ≡ just (S.admissionWorker req (S.selectEntry savedLease promise)) →
   I.advance (I.admissionStep worker Admission.chooseEntry) c ≡ just selected →
   lookup worker (S.admissions (I.world selected)) ≡ just (S.admissionWorker req (S.forkHandler savedLease promise entry)) →
   Present entry (S.entries (S.cm (I.world selected)))
 selected-entry-from-source = selected-source

 -- The enabled frontend event supplies the primitive selection computation.
 selected-entry-present : ∀ worker req savedLease promise entry before {selected} →
   lookup worker (S.admissions (shared before)) ≡ just (S.admissionWorker req (S.selectEntry savedLease promise)) →
   T.advance (event worker Admission.chooseEntry) before ≡ just selected →
   lookup worker (S.admissions (shared selected)) ≡ just (S.admissionWorker req (S.forkHandler savedLease promise entry)) →
   Present entry (S.entries (S.cm (shared selected)))
 selected-entry-present worker req savedLease promise entry before owned actual selectedPC =
   selected-source worker req savedLease promise entry (core before) owned
     (Old.selection-lower worker before actual) selectedPC
