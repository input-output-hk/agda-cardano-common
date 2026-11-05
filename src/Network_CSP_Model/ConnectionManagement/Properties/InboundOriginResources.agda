{-# OPTIONS --guardedness #-}

-- Resource consequences of reconstructed inbound occurrences. Actual frontend
-- labels remain in the history layer; this bridge uses its primitive equations.
module ConnectionManagement.Properties.InboundOriginResources where

open import Data.Bool using (Bool; true)
open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (proj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (ErrorId; HandleId; WorkerId; EntryId; PromiseId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.HandlerResourceFacts using (Facts)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Properties.InboundOriginRuntime as Runtime
import ConnectionManagement.Properties.HandlerOriginHistory as Witnessed
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.Properties.ServerPeers as SharedFacts
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Properties.HandlerOriginRetention as Retention
import ConnectionManagement.Properties.ServerPeersHandlerResources as Resources

module Frontend (b io : ErrorId → Bool) (canInitiate : HandleId → ℕ → Bool) where
 private module T = Combined.Protocols b io canInitiate using (Runtime; Event; Runs; more; advance; initialize; dispatch; base; front; runtime; noteLegacy)
 private module Old = Resources b io using (allocated-frame; fork-facts)
 private module Keep = Retention.Frontend b io canInitiate using (core; shared; event; entry-retained; selected-entry-from-source)
 open Keep public using (core; shared; event)

 -- The reconstructed positive selection fixes the entry; enabled interference
 -- retains its stored identity until the actual fork creates handler and socket.
 at-fork : ∀ parent request savedLease promise entry {beforeSelect selected beforeFork born gap} →
   lookup parent (S.admissions (shared beforeSelect)) ≡ just (S.admissionWorker request (S.selectEntry savedLease promise)) →
   M.advance (M.admissionStep parent Admission.chooseEntry) (core beforeSelect) ≡ just (core selected) →
   lookup parent (S.admissions (shared selected)) ≡ just (S.admissionWorker request (S.forkHandler savedLease promise entry)) →
   T.Runs selected gap beforeFork →
   lookup parent (S.admissions (shared beforeFork)) ≡ just (S.admissionWorker request (S.forkHandler savedLease promise entry)) →
   M.advance (M.admissionStep parent Admission.fork) (core beforeFork) ≡ just (core born) →
   Facts (S.child request) (S.handlerStart entry (S.socketRef request) promise (S.key request)) (shared born)
 at-fork parent request savedLease promise entry {beforeSelect} {selected} {beforeFork} {born} {gap}
   beforePC selection selectedPC interference forkPC fork =
     Old.fork-facts parent request savedLease promise entry (core beforeFork) forkPC
       (Keep.entry-retained {before = selected} {gap = gap} {after = beforeFork} {entry = entry} interference
         (Keep.selected-entry-from-source parent request savedLease promise entry (core beforeSelect) beforePC selection selectedPC)) fork

 -- Preserve the same descriptor through every enabled post-birth suffix.
 retain : ∀ worker captured {before events after} → T.Runs before events after →
   Facts worker captured (shared before) → Facts worker captured (shared after)
 retain worker captured = Resources.For.Frontend.run-preserves b io worker captured canInitiate

 -- The closed runtime observer supplies the actual labels and PC alignment.
 private
  module Located = Runtime.Frontend.Located b io canInitiate using (ForkOrigin; from-runs; initialized-fork-origin)
  module F = Runtime.Frontend.Located.ForkOrigin b io canInitiate using (request; heldLease; promise; entry; selection; fork-event; fork-source)
  module H = Runtime.Frontend.Located.History.SelectedOrigin b io canInitiate using (allocationBefore; allocationAfter; selectionBefore; selectionAfter; allocationLabel; selectionLabel; prefix; allocationGap; forkGap; decomposition; prefix-run; allocation-event; allocation-source; before-allocation-PC; promise-input; allocated-PC; allocation-gap-run; before-selection-PC; selection-event; selection-source; selected-PC; fork-gap-run; current-PC)
  module Prior = Witnessed.Frontend b io canInitiate using (History; append)

 -- Canonical and core-dispatch forms retain their original frontend labels.
 private
  module K = Combined b io using (Action; coreStep; serverStep; combined; context; server; coreAction; step)
  module E = Exit b using (State; run; step)
  module ServerModel = Server b using (run; runMachine)
  module Source = Resources.Frontend b io canInitiate using (fork-lower; core-delegated)
 server-action : WorkerId → K.Action
 server-action parent = K.serverStep (E.run (ServerModel.run (ServerModel.runMachine (M.admissionStep parent Admission.fork))))
 core-event : WorkerId → Admission.AdmissionAction → T.Event
 core-event parent action = T.dispatch (K.coreStep (O.inbound (M.admissionStep parent action)))
 data ForkLabel (parent : WorkerId) : T.Event → Set where
  canonicalFork : ForkLabel parent (event parent Admission.fork)
  coreFork : ForkLabel parent (core-event parent Admission.fork)

 -- A synthetic canonical transition is used solely to invert the same lower
 -- Server effect. The actual event retained in ForkOrigin is never replaced.
 private
  canonical-after : WorkerId → E.State → T.Runtime → T.Runtime
  canonical-after parent e before = T.runtime (K.combined e (K.context (T.base before)))
    (T.noteLegacy (server-action parent) (T.front before))
  canonical-base : ∀ parent before {e} →
    E.step (K.coreAction (O.inbound (M.admissionStep parent Admission.fork))) (K.server (T.base before)) ≡ just e →
    K.step (server-action parent) (T.base before) ≡ just (K.combined e (K.context (T.base before)))
  canonical-base parent before actual rewrite actual = refl
  canonical-lift : ∀ parent before {e} →
    E.step (K.coreAction (O.inbound (M.admissionStep parent Admission.fork))) (K.server (T.base before)) ≡ just e →
    T.advance (event parent Admission.fork) before ≡ just (canonical-after parent e before)
  canonical-lift parent before actual = SharedFacts.Protocols.lift-dispatch b io canInitiate
    (server-action parent) (T.base before) (T.front before) refl (canonical-base parent before actual)
  core-fork-lower : ∀ parent before {after} → T.advance (core-event parent Admission.fork) before ≡ just after →
    M.advance (M.admissionStep parent Admission.fork) (core before) ≡ just (core after)
  core-fork-lower parent before actual = Source.fork-lower parent before (canonical-lift parent before
    (Source.core-delegated (O.inbound (M.admissionStep parent Admission.fork)) before actual))

 fork-source : ∀ parent label before {after} → ForkLabel parent label → T.advance label before ≡ just after →
   M.advance (M.admissionStep parent Admission.fork) (core before) ≡ just (core after)
 fork-source parent label before canonicalFork actual = Source.fork-lower parent before actual
 fork-source parent label before coreFork actual = core-fork-lower parent before actual

 -- Every continuation and primitive equation is recovered from the enabled
 -- labeled fork, rather than supplied as an operational alignment premise.
 initialized-fork-origin : ∀ inputConfig governor {start observed before born parent label} →
   T.initialize inputConfig governor ≡ just start → T.Runs start observed before →
   ForkLabel parent label → T.advance label before ≡ just born →
   Located.ForkOrigin start observed before born parent label
 initialized-fork-origin inputConfig governor {before = before} {parent = parent} {label = label}
   initialized prefixRun labelClass actual = Located.initialized-fork-origin inputConfig governor
     initialized prefixRun actual (fork-source parent label before labelClass actual)

 -- The packet retains exact observed-label decomposition and historical cell
 -- allocation. Membership here is at allocation time; no freshness is asserted.
 record RecoveredOrigin (inputConfig : O.Configuration) (governor : Governor.State)
   (start : T.Runtime) (observed : List T.Event) (before born : T.Runtime)
   (parent : WorkerId) (label : T.Event) (suffix : List T.Event) (current : T.Runtime) : Set where
  field
   initialized : T.initialize inputConfig governor ≡ just start
   prefix-run : T.Runs start observed before
   suffix-run : T.Runs born suffix current
   label-class : ForkLabel parent label
   reconstructed : Located.ForkOrigin start observed before born parent label
   captured : S.HandlerStart
   descriptor : captured ≡ S.handlerStart (F.entry reconstructed)
     (S.socketRef (F.request reconstructed)) (F.promise reconstructed) (S.key (F.request reconstructed))
   promise-allocated : F.promise reconstructed ∈ S.promises (shared (H.allocationAfter (F.selection reconstructed)))
   at-birth : Facts (S.child (F.request reconstructed)) captured (shared born)
   current-facts : Facts (S.child (F.request reconstructed)) captured (shared current)

 -- Successful initialization, an observed prefix/fork and an enabled suffix
 -- suffice; every operational PC and resource certificate is derived internally.
 initialize-origin : ∀ inputConfig governor {start observed before born parent label suffix current} →
   T.initialize inputConfig governor ≡ just start → T.Runs start observed before →
   ForkLabel parent label → T.advance label before ≡ just born → T.Runs born suffix current →
   RecoveredOrigin inputConfig governor start observed before born parent label suffix current
 initialize-origin inputConfig governor {start} {observed} {before} {born} {parent} {label} {suffix} {current}
   initialized prefixRun labelClass actual suffixRun = record
   { initialized = initialized; prefix-run = prefixRun; suffix-run = suffixRun; label-class = labelClass
   ; reconstructed = origin; captured = captured; descriptor = refl
   ; promise-allocated = allocated; at-birth = bornFacts
   ; current-facts = retain (S.child (F.request origin)) captured suffixRun bornFacts }
   where
   origin = initialized-fork-origin inputConfig governor initialized prefixRun labelClass actual
   selected = F.selection origin
   captured = S.handlerStart (F.entry origin) (S.socketRef (F.request origin)) (F.promise origin) (S.key (F.request origin))
   allocated = subst (λ promise → promise ∈ S.promises (shared (H.allocationAfter selected)))
     (sym (H.promise-input selected))
     (proj₂ (Old.allocated-frame parent (F.request origin) (F.heldLease origin)
       (core (H.allocationBefore selected)) (H.before-allocation-PC selected) (H.allocation-source selected)))
   bornFacts = at-fork parent (F.request origin) (F.heldLease origin) (F.promise origin) (F.entry origin)
     {beforeSelect = H.selectionBefore selected} {selected = H.selectionAfter selected}
     {beforeFork = before} {born = born} {gap = H.forkGap selected}
     (H.before-selection-PC selected) (H.selection-source selected) (H.selected-PC selected)
     (Located.from-runs (H.fork-gap-run selected)) (H.current-PC selected) (F.fork-source origin)

 -- When the three located labels are canonical, the same occurrence packet
 -- populates the earlier witnessed History without changing any gap or capture.
 canonical-history : ∀ {inputConfig governor start observed before born parent label suffix current}
   (origin : RecoveredOrigin inputConfig governor start observed before born parent label suffix current) →
   H.allocationLabel (F.selection (RecoveredOrigin.reconstructed origin)) ≡ event parent Admission.allocatePromise →
   H.selectionLabel (F.selection (RecoveredOrigin.reconstructed origin)) ≡ event parent Admission.chooseEntry →
   label ≡ event parent Admission.fork →
   Prior.History start current (S.child (F.request (RecoveredOrigin.reconstructed origin)))
 canonical-history {inputConfig} {governor} {before = before} {born} {parent} {suffix = suffix} {current}
   origin allocationCanonical selectionCanonical forkCanonical = record
   { configuration = inputConfig; governor = governor; initialized = RecoveredOrigin.initialized origin
   ; before = H.allocationBefore selected; allocated = H.allocationAfter selected
   ; beforeSelect = H.selectionBefore selected; selected = H.selectionAfter selected
   ; beforeFork = before; born = born; parent = parent; request = F.request recovered
   ; heldLease = F.heldLease recovered; child-matches = refl
   ; prefix = H.prefix selected; allocationGap = H.allocationGap selected; forkGap = H.forkGap selected; suffix = suffix
   ; prefix-run = Located.from-runs (H.prefix-run selected); before-PC = H.before-allocation-PC selected
   ; allocation-event = trans (cong (λ action → T.advance action (H.allocationBefore selected)) (sym allocationCanonical)) (H.allocation-event selected)
   ; allocation-source = H.allocation-source selected
   ; promise = F.promise recovered; promise-is-fresh-input = H.promise-input selected
   ; promise-allocated = RecoveredOrigin.promise-allocated origin; allocated-PC = H.allocated-PC selected
   ; allocation-gap-run = Located.from-runs (H.allocation-gap-run selected)
   ; before-selection-PC = H.before-selection-PC selected
   ; selection-event = trans (cong (λ action → T.advance action (H.selectionBefore selected)) (sym selectionCanonical)) (H.selection-event selected)
   ; selection-source = H.selection-source selected; entry = F.entry recovered; selected-PC = H.selected-PC selected
   ; fork-gap-run = Located.from-runs (H.fork-gap-run selected); before-fork-PC = H.current-PC selected
   ; fork-event = trans (cong (λ action → T.advance action before) (sym forkCanonical)) (F.fork-event recovered)
   ; fork-source = F.fork-source recovered; captured = RecoveredOrigin.captured origin; descriptor = RecoveredOrigin.descriptor origin
   ; at-fork = RecoveredOrigin.at-birth origin; suffix-run = RecoveredOrigin.suffix-run origin
   ; retained = RecoveredOrigin.current-facts origin }
   where
   recovered = RecoveredOrigin.reconstructed origin
   selected = F.selection recovered

 -- Extend the retained resource history without repeating origin discovery.
 -- All located labels, decomposition and at-birth witnesses are copied exactly.
 extend-origin : ∀ {inputConfig governor start observed before born parent label suffix middle after events} →
   T.Runs middle events after →
   RecoveredOrigin inputConfig governor start observed before born parent label suffix middle →
   RecoveredOrigin inputConfig governor start observed before born parent label (suffix ++ events) after
 extend-origin path origin = record
   { initialized = RecoveredOrigin.initialized origin; prefix-run = RecoveredOrigin.prefix-run origin
   ; suffix-run = Prior.append (RecoveredOrigin.suffix-run origin) path
   ; label-class = RecoveredOrigin.label-class origin; reconstructed = RecoveredOrigin.reconstructed origin
   ; captured = RecoveredOrigin.captured origin; descriptor = RecoveredOrigin.descriptor origin
   ; promise-allocated = RecoveredOrigin.promise-allocated origin; at-birth = RecoveredOrigin.at-birth origin
   ; current-facts = retain (S.child (F.request (RecoveredOrigin.reconstructed origin)))
       (RecoveredOrigin.captured origin) path (RecoveredOrigin.current-facts origin) }

 -- The complete execution retains the observed labels verbatim.
 events : ∀ {inputConfig governor start observed before born parent label suffix current} →
   RecoveredOrigin inputConfig governor start observed before born parent label suffix current → List T.Event
 events {observed = observed} {label = label} {suffix = suffix} origin = observed ++ (label ∷ suffix)
 execution : ∀ {inputConfig governor start observed before born parent label suffix current}
   (origin : RecoveredOrigin inputConfig governor start observed before born parent label suffix current) →
   T.Runs start (events origin) current
 execution origin = Prior.append (RecoveredOrigin.prefix-run origin)
   (T.more (F.fork-event (RecoveredOrigin.reconstructed origin)) (RecoveredOrigin.suffix-run origin))
