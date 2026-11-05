{-# OPTIONS --guardedness #-}

-- Witnessed inbound resource origins with enabled gaps. Continuation guards
-- explicitly align the same allocation, positive selection and actual fork;
-- this does not discover those events from arbitrary collected membership.
module ConnectionManagement.Properties.HandlerOriginHistory where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (WorkerId; EntryId; PromiseId; HandleId; ErrorId; ident)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.HandlerResourceFacts using (Facts)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Properties.ServerPeersHandlerResources as Resources
import ConnectionManagement.Properties.HandlerOriginRetention as Retention

module Frontend (b io : ErrorId → Bool) (canInitiate : HandleId → ℕ → Bool) where
 private module T = Combined.Protocols b io canInitiate using (Event; Runs; Runtime; advance; initialize; more; stop)
 private module Old = Resources b io using (allocated-frame; fork-facts)
 private module Source = Resources.Frontend b io canInitiate using (Origin; allocation-lower; fork-lower; selection-lower)
 private module Keep = Retention.Frontend b io canInitiate using (core; entry-retained; event; selected-entry-present; shared)
 open Keep public using (core; event; shared)

 -- Fixed resources use the existing observer lift, without applying any birth
 -- inversion or shutdown module in this occurrence layer.
 retain : ∀ worker captured {before events after} → T.Runs before events after →
   Facts worker captured (shared before) → Facts worker captured (shared after)
 retain worker captured path = Resources.For.Frontend.run-preserves b io worker captured canInitiate path

 -- Trace concatenation keeps every enabled interference step explicit.
 append : ∀ {start prefix middle suffix current} → T.Runs start prefix middle →
   T.Runs middle suffix current → T.Runs start (prefix ++ suffix) current
 append T.stop right = right
 append (T.more actual rest) right = T.more actual (append rest right)

 record History (start current : T.Runtime) (worker : WorkerId) : Set where
  field
   configuration : CM.Configuration
   governor : Governor.State
   initialized : T.initialize configuration governor ≡ just start
   before allocated beforeSelect selected beforeFork born : T.Runtime
   parent : WorkerId
   request : S.Admission
   heldLease : S.Lease
   child-matches : S.child request ≡ worker
   prefix allocationGap forkGap suffix : List T.Event
   prefix-run : T.Runs start prefix before
   before-PC : lookup parent (S.admissions (shared before)) ≡ just (S.admissionWorker request (S.prepare heldLease))
   allocation-event : T.advance (event parent Admission.allocatePromise) before ≡ just allocated
   allocation-source : Machine.advance (Machine.admissionStep parent Admission.allocatePromise) (core before) ≡ just (core allocated)
   promise : PromiseId
   promise-is-fresh-input : promise ≡ ident (S.nextPromise (shared before))
   promise-allocated : promise ∈ S.promises (shared allocated)
   allocated-PC : lookup parent (S.admissions (shared allocated)) ≡ just (S.admissionWorker request (S.selectEntry heldLease promise))
   allocation-gap-run : T.Runs allocated allocationGap beforeSelect
   before-selection-PC : lookup parent (S.admissions (shared beforeSelect)) ≡ just (S.admissionWorker request (S.selectEntry heldLease promise))
   selection-event : T.advance (event parent Admission.chooseEntry) beforeSelect ≡ just selected
   selection-source : Machine.advance (Machine.admissionStep parent Admission.chooseEntry) (core beforeSelect) ≡ just (core selected)
   entry : EntryId
   selected-PC : lookup parent (S.admissions (shared selected)) ≡ just (S.admissionWorker request (S.forkHandler heldLease promise entry))
   fork-gap-run : T.Runs selected forkGap beforeFork
   before-fork-PC : lookup parent (S.admissions (shared beforeFork)) ≡ just (S.admissionWorker request (S.forkHandler heldLease promise entry))
   fork-event : T.advance (event parent Admission.fork) beforeFork ≡ just born
   fork-source : Machine.advance (Machine.admissionStep parent Admission.fork) (core beforeFork) ≡ just (core born)
   captured : S.HandlerStart
   descriptor : captured ≡ S.handlerStart entry (S.socketRef request) promise (S.key request)
   at-fork : Facts worker captured (shared born)
   suffix-run : T.Runs born suffix current
   retained : Facts worker captured (shared current)

 -- Positive post-selection and pre-fork PCs are operational alignment inputs.
 -- No entry/resource or physical-thread lookup certificate is an input.
 initialize-history : ∀ {c g start before allocated beforeSelect selected beforeFork born current prefix allocationGap forkGap suffix}
   parent request heldLease entry → T.initialize c g ≡ just start → T.Runs start prefix before →
   lookup parent (S.admissions (shared before)) ≡ just (S.admissionWorker request (S.prepare heldLease)) →
   T.advance (event parent Admission.allocatePromise) before ≡ just allocated →
   T.Runs allocated allocationGap beforeSelect →
   lookup parent (S.admissions (shared beforeSelect)) ≡ just (S.admissionWorker request (S.selectEntry heldLease (ident (S.nextPromise (shared before))))) →
   T.advance (event parent Admission.chooseEntry) beforeSelect ≡ just selected →
   lookup parent (S.admissions (shared selected)) ≡ just (S.admissionWorker request (S.forkHandler heldLease (ident (S.nextPromise (shared before))) entry)) →
   T.Runs selected forkGap beforeFork →
   lookup parent (S.admissions (shared beforeFork)) ≡ just (S.admissionWorker request (S.forkHandler heldLease (ident (S.nextPromise (shared before))) entry)) →
   T.advance (event parent Admission.fork) beforeFork ≡ just born →
   T.Runs born suffix current → History start current (S.child request)
 initialize-history {c} {g} {start} {before} {allocated} {beforeSelect} {selected} {beforeFork} {born} {current}
   {prefix} {allocationGap} {forkGap} {suffix} parent request heldLease entry init prefixRun beforePC allocation gap1 beforeSelection selection selectedPC gap2 beforeForkPC fork suffixRun = record
   { configuration = c; governor = g; initialized = init
   ; before = before; allocated = allocated; beforeSelect = beforeSelect; selected = selected; beforeFork = beforeFork; born = born
   ; parent = parent; request = request; heldLease = heldLease; child-matches = refl
   ; prefix = prefix; allocationGap = allocationGap; forkGap = forkGap; suffix = suffix
   ; prefix-run = prefixRun; before-PC = beforePC; allocation-event = allocation; allocation-source = allocationSource
   ; promise = ident (S.nextPromise (shared before)); promise-is-fresh-input = refl; promise-allocated = proj₂ allocatedObservation
   ; allocated-PC = proj₁ allocatedObservation; allocation-gap-run = gap1; before-selection-PC = beforeSelection
   ; selection-event = selection; selection-source = Source.selection-lower parent beforeSelect selection
   ; entry = entry; selected-PC = selectedPC; fork-gap-run = gap2; before-fork-PC = beforeForkPC
   ; fork-event = fork; fork-source = forkSource
   ; captured = captured; descriptor = refl; at-fork = bornFacts
   ; suffix-run = suffixRun; retained = retain (S.child request) captured suffixRun bornFacts }
   where
   allocationSource = Source.allocation-lower parent before allocation
   allocatedObservation = Old.allocated-frame parent request heldLease (core before) beforePC allocationSource
   forkSource = Source.fork-lower parent beforeFork fork
   captured = S.handlerStart entry (S.socketRef request) (ident (S.nextPromise (shared before))) (S.key request)
   selectedEntry = Keep.selected-entry-present parent request heldLease (ident (S.nextPromise (shared before))) entry
     beforeSelect {selected = selected} beforeSelection selection selectedPC
   forkEntry = Keep.entry-retained {before = selected} {gap = forkGap} {after = beforeFork} {entry = entry} gap2 selectedEntry
   bornFacts = Old.fork-facts parent request heldLease (ident (S.nextPromise (shared before))) entry
     (core beforeFork) beforeForkPC forkEntry forkSource

 -- Extend the recorded suffix, retaining the same allocated promise, chosen
 -- entry, actual fork and descriptor through every enabled frontend event.
 extend-history : ∀ {start before after worker events} → T.Runs before events after →
   History start before worker → History start after worker
 extend-history {worker = worker} {events = events} path history = record
   { configuration = History.configuration history; governor = History.governor history; initialized = History.initialized history
   ; before = History.before history; allocated = History.allocated history; beforeSelect = History.beforeSelect history
   ; selected = History.selected history; beforeFork = History.beforeFork history; born = History.born history
   ; parent = History.parent history; request = History.request history; heldLease = History.heldLease history; child-matches = History.child-matches history
   ; prefix = History.prefix history; allocationGap = History.allocationGap history; forkGap = History.forkGap history
   ; suffix = History.suffix history ++ events; prefix-run = History.prefix-run history; before-PC = History.before-PC history
   ; allocation-event = History.allocation-event history; allocation-source = History.allocation-source history
   ; promise = History.promise history; promise-is-fresh-input = History.promise-is-fresh-input history; promise-allocated = History.promise-allocated history
   ; allocated-PC = History.allocated-PC history; allocation-gap-run = History.allocation-gap-run history; before-selection-PC = History.before-selection-PC history
   ; selection-event = History.selection-event history; selection-source = History.selection-source history
   ; entry = History.entry history; selected-PC = History.selected-PC history; fork-gap-run = History.fork-gap-run history; before-fork-PC = History.before-fork-PC history
   ; fork-event = History.fork-event history; fork-source = History.fork-source history
   ; captured = History.captured history; descriptor = History.descriptor history; at-fork = History.at-fork history
   ; suffix-run = append (History.suffix-run history) path
   ; retained = retain worker (History.captured history) path (History.retained history) }

 -- The whole history includes both gaps; no interference event is erased.
 events : ∀ {start current worker} → History start current worker → List T.Event
 events history = History.prefix history ++ (event (History.parent history) Admission.allocatePromise ∷
   (History.allocationGap history ++ (event (History.parent history) Admission.chooseEntry ∷
   (History.forkGap history ++ (event (History.parent history) Admission.fork ∷ History.suffix history)))))
 execution : ∀ {start current worker} (history : History start current worker) → T.Runs start (events history) current
 execution history = append (History.prefix-run history) (T.more (History.allocation-event history)
   (append (History.allocation-gap-run history) (T.more (History.selection-event history)
   (append (History.fork-gap-run history) (T.more (History.fork-event history) (History.suffix-run history))))))

 -- A zero-length enabled gap identifies its endpoints without normalization.
 empty-endpoints : ∀ {before after} → T.Runs before [] after → before ≡ after
 empty-endpoints T.stop = refl

 -- Empty gaps recover the existing adjacent Origin statement unchanged.
 -- The actual fork and captured descriptor are copied, rather than rediscovered.
 empty-gaps-origin : ∀ {start current worker} (history : History start current worker) →
   History.allocationGap history ≡ [] → History.forkGap history ≡ [] → Source.Origin start current worker
 empty-gaps-origin history allocationEmpty forkEmpty = record
   { configuration = History.configuration history; governor = History.governor history; initialized = History.initialized history
   ; before = History.before history; allocated = History.allocated history; selected = History.selected history; born = History.born history
   ; parent = History.parent history; request = History.request history; heldLease = History.heldLease history; child-matches = History.child-matches history
   ; prefix = History.prefix history; suffix = History.suffix history; prefix-run = History.prefix-run history; before-PC = History.before-PC history
   ; allocation-event = History.allocation-event history
   ; selection-event = trans (cong (T.advance (event (History.parent history) Admission.chooseEntry)) allocationSame) (History.selection-event history)
   ; fork-event = trans (cong (T.advance (event (History.parent history) Admission.fork)) forkSame) (History.fork-event history)
   ; allocation-source = History.allocation-source history
   ; selection-source = trans (cong (Machine.advance (Machine.admissionStep (History.parent history) Admission.chooseEntry)) (cong core allocationSame)) (History.selection-source history)
   ; fork-source = trans (cong (Machine.advance (Machine.admissionStep (History.parent history) Admission.fork)) (cong core forkSame)) (History.fork-source history)
   ; promise = History.promise history; promise-is-fresh-input = History.promise-is-fresh-input history; promise-allocated = History.promise-allocated history
   ; entry = History.entry history; captured = History.captured history; descriptor = History.descriptor history
   ; at-fork = History.at-fork history; suffix-run = History.suffix-run history; retained = History.retained history }
   where
   allocationSame = empty-endpoints (subst (λ gap → T.Runs (History.allocated history) gap (History.beforeSelect history)) allocationEmpty (History.allocation-gap-run history))
   forkSame = empty-endpoints (subst (λ gap → T.Runs (History.selected history) gap (History.beforeFork history)) forkEmpty (History.fork-gap-run history))

 -- Compatibility observes exact descriptor equality, not merely existence.
 empty-gaps-captured : ∀ {start current worker} (history : History start current worker)
   (allocationEmpty : History.allocationGap history ≡ []) (forkEmpty : History.forkGap history ≡ []) →
   Source.Origin.captured (empty-gaps-origin history allocationEmpty forkEmpty) ≡ History.captured history
 empty-gaps-captured history allocationEmpty forkEmpty = refl
