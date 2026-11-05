{-# OPTIONS --guardedness #-}

-- Event-indexed recovery of inbound allocation and positive selection. Every
-- located operation retains its actual label and an exact original-list split.
module ConnectionManagement.Properties.InboundOriginFrontend where

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; PromiseId; EntryId; ident)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Properties.InboundOriginCore as Core
import ConnectionManagement.Properties.InboundOriginEffect as Effects

-- The lookup inversion also retains the primitive equation from its creator.
data SelectBefore (before after : M.Configuration) (worker : WorkerId) (request : S.Admission) (saved : S.Lease) (promise : PromiseId) : Set where
 carried-select : lookup worker (S.admissions (M.world before)) ≡ just (S.admissionWorker request (S.selectEntry saved promise)) → SelectBefore before after worker request saved promise
 allocated-here : promise ≡ ident (S.nextPromise (M.world before)) →
   lookup worker (S.admissions (M.world before)) ≡ just (S.admissionWorker request (S.prepare saved)) →
   M.advance (M.admissionStep worker Admission.allocatePromise) before ≡ just after → SelectBefore before after worker request saved promise
data ForkBefore (before after : M.Configuration) (worker : WorkerId) (request : S.Admission) (saved : S.Lease) (promise : PromiseId) (entry : EntryId) : Set where
 carried-fork : lookup worker (S.admissions (M.world before)) ≡ just (S.admissionWorker request (S.forkHandler saved promise entry)) → ForkBefore before after worker request saved promise entry
 selected-here : lookup worker (S.admissions (M.world before)) ≡ just (S.admissionWorker request (S.selectEntry saved promise)) →
   M.advance (M.admissionStep worker Admission.chooseEntry) before ≡ just after → ForkBefore before after worker request saved promise entry

private
 prior-other : ∀ {before after : S.State} writer worker row target → worker ≢ writer →
   S.admissions after ≡ put writer row (S.admissions before) →
   lookup worker (S.admissions after) ≡ just target → lookup worker (S.admissions before) ≡ just target
 prior-other {before} writer worker row target different changed found = trans
   (sym (lookup-put-other writer worker row (S.admissions before) different))
   (trans (sym (cong (lookup worker) changed)) found)
 written-row : ∀ {before after : S.State} worker row target →
   S.admissions after ≡ put worker row (S.admissions before) →
   lookup worker (S.admissions after) ≡ just target → row ≡ target
 written-row {before} worker row target changed found = just-injective (trans
   (sym (lookup-put worker row (S.admissions before)))
   (trans (sym (cong (lookup worker) changed)) found))

select-before : ∀ {before after worker request saved promise} → Effects.Effect before after →
 lookup worker (S.admissions (M.world after)) ≡ just (S.admissionWorker request (S.selectEntry saved promise)) → SelectBefore before after worker request saved promise
select-before {worker = worker} (Effects.effect (Core.same unchanged) source) found = carried-select (trans (sym (cong (lookup worker) unchanged)) found)
select-before {before} {after} {worker} {request} {saved} {promise} (Effects.effect (Core.reset writer row outside changed) source) found with worker ≟ writer
... | no different = carried-select (prior-other {before = M.world before} {after = M.world after} writer worker row (S.admissionWorker request (S.selectEntry saved promise)) different changed found)
... | yes refl with written-row {before = M.world before} {after = M.world after} worker row (S.admissionWorker request (S.selectEntry saved promise)) changed found
...   | refl = case outside of λ ()
select-before {before} {after} {worker} {request} {saved} {promise} (Effects.effect (Core.allocated writer req held owned changed) source) found with worker ≟ writer
... | no different = carried-select (prior-other {before = M.world before} {after = M.world after} writer worker (S.admissionWorker req (S.selectEntry held (ident (S.nextPromise (M.world before))))) (S.admissionWorker request (S.selectEntry saved promise)) different changed found)
... | yes refl with written-row {before = M.world before} {after = M.world after} worker (S.admissionWorker req (S.selectEntry held (ident (S.nextPromise (M.world before))))) (S.admissionWorker request (S.selectEntry saved promise)) changed found
...   | refl = allocated-here refl owned source
select-before {before} {after} {worker} {request} {saved} {promise} (Effects.effect (Core.selected writer req held pid entry owned changed) source) found with worker ≟ writer
... | no different = carried-select (prior-other {before = M.world before} {after = M.world after} writer worker (S.admissionWorker req (S.forkHandler held pid entry)) (S.admissionWorker request (S.selectEntry saved promise)) different changed found)
... | yes refl with written-row {before = M.world before} {after = M.world after} worker (S.admissionWorker req (S.forkHandler held pid entry)) (S.admissionWorker request (S.selectEntry saved promise)) changed found
...   | ()

fork-before : ∀ {before after worker request saved promise entry} → Effects.Effect before after →
 lookup worker (S.admissions (M.world after)) ≡ just (S.admissionWorker request (S.forkHandler saved promise entry)) → ForkBefore before after worker request saved promise entry
fork-before {worker = worker} (Effects.effect (Core.same unchanged) source) found = carried-fork (trans (sym (cong (lookup worker) unchanged)) found)
fork-before {before} {after} {worker} {request} {saved} {promise} {entry} (Effects.effect (Core.reset writer row outside changed) source) found with worker ≟ writer
... | no different = carried-fork (prior-other {before = M.world before} {after = M.world after} writer worker row (S.admissionWorker request (S.forkHandler saved promise entry)) different changed found)
... | yes refl with written-row {before = M.world before} {after = M.world after} worker row (S.admissionWorker request (S.forkHandler saved promise entry)) changed found
...   | refl = case outside of λ ()
fork-before {before} {after} {worker} {request} {saved} {promise} {entry} (Effects.effect (Core.allocated writer req held owned changed) source) found with worker ≟ writer
... | no different = carried-fork (prior-other {before = M.world before} {after = M.world after} writer worker (S.admissionWorker req (S.selectEntry held (ident (S.nextPromise (M.world before))))) (S.admissionWorker request (S.forkHandler saved promise entry)) different changed found)
... | yes refl with written-row {before = M.world before} {after = M.world after} worker (S.admissionWorker req (S.selectEntry held (ident (S.nextPromise (M.world before))))) (S.admissionWorker request (S.forkHandler saved promise entry)) changed found
...   | ()
fork-before {before} {after} {worker} {request} {saved} {promise} {entry} (Effects.effect (Core.selected writer req held pid chosen owned changed) source) found with worker ≟ writer
... | no different = carried-fork (prior-other {before = M.world before} {after = M.world after} writer worker (S.admissionWorker req (S.forkHandler held pid chosen)) (S.admissionWorker request (S.forkHandler saved promise entry)) different changed found)
... | yes refl with written-row {before = M.world before} {after = M.world after} worker (S.admissionWorker req (S.forkHandler held pid chosen)) (S.admissionWorker request (S.forkHandler saved promise entry)) changed found
...   | refl = selected-here owned source

-- This small trace datatype has the same enabled-step meaning and exact event
-- indices as the frontend Runs; concrete adapters convert it in both directions.
module Engine (State Event : Set) (advance : Event → State → Data.Maybe.Maybe State)
 (core : State → M.Configuration)
 (observe : ∀ action before {after} → advance action before ≡ just after → Effects.Effect (core before) (core after)) where

 data Runs : State → List Event → State → Set where
  done : ∀ {state} → Runs state [] state
  next : ∀ {before middle after action tail} → advance action before ≡ just middle → Runs middle tail after → Runs before (action ∷ tail) after

 record Allocation (start : State) (events : List Event) (current : State)
   (worker : WorkerId) (request : S.Admission) (saved : S.Lease) (promise : PromiseId) : Set where
  field
   before after : State
   label : Event
   prefix gap : List Event
   decomposition : events ≡ prefix ++ (label ∷ gap)
   prefix-run : Runs start prefix before
   actual : advance label before ≡ just after
   source : M.advance (M.admissionStep worker Admission.allocatePromise) (core before) ≡ just (core after)
   before-PC : lookup worker (S.admissions (M.world (core before))) ≡ just (S.admissionWorker request (S.prepare saved))
   promise-input : promise ≡ ident (S.nextPromise (M.world (core before)))
   after-PC : lookup worker (S.admissions (M.world (core after))) ≡ just (S.admissionWorker request (S.selectEntry saved promise))
   gap-run : Runs after gap current
   current-PC : lookup worker (S.admissions (M.world (core current))) ≡ just (S.admissionWorker request (S.selectEntry saved promise))

 record Selection (start : State) (events : List Event) (current : State)
   (worker : WorkerId) (request : S.Admission) (saved : S.Lease) (promise : PromiseId) (entry : EntryId) : Set where
  field
   before after : State
   label : Event
   prefix gap : List Event
   decomposition : events ≡ prefix ++ (label ∷ gap)
   prefix-run : Runs start prefix before
   actual : advance label before ≡ just after
   source : M.advance (M.admissionStep worker Admission.chooseEntry) (core before) ≡ just (core after)
   before-PC : lookup worker (S.admissions (M.world (core before))) ≡ just (S.admissionWorker request (S.selectEntry saved promise))
   after-PC : lookup worker (S.admissions (M.world (core after))) ≡ just (S.admissionWorker request (S.forkHandler saved promise entry))
   gap-run : Runs after gap current
   current-PC : lookup worker (S.admissions (M.world (core current))) ≡ just (S.admissionWorker request (S.forkHandler saved promise entry))

 -- Prepending extends only the actual prefix; it does not change the creator.
 prepend-allocation : ∀ {start middle current action events worker request saved promise} → advance action start ≡ just middle →
   Allocation middle events current worker request saved promise → Allocation start (action ∷ events) current worker request saved promise
 prepend-allocation {action = action} actual history = record
   { before = Allocation.before history; after = Allocation.after history; label = Allocation.label history
   ; prefix = action ∷ Allocation.prefix history; gap = Allocation.gap history
   ; decomposition = cong (action ∷_) (Allocation.decomposition history)
   ; prefix-run = next actual (Allocation.prefix-run history); actual = Allocation.actual history; source = Allocation.source history
   ; before-PC = Allocation.before-PC history; promise-input = Allocation.promise-input history; after-PC = Allocation.after-PC history
   ; gap-run = Allocation.gap-run history; current-PC = Allocation.current-PC history }
 prepend-selection : ∀ {start middle current action events worker request saved promise entry} → advance action start ≡ just middle →
   Selection middle events current worker request saved promise entry → Selection start (action ∷ events) current worker request saved promise entry
 prepend-selection {action = action} actual history = record
   { before = Selection.before history; after = Selection.after history; label = Selection.label history
   ; prefix = action ∷ Selection.prefix history; gap = Selection.gap history
   ; decomposition = cong (action ∷_) (Selection.decomposition history)
   ; prefix-run = next actual (Selection.prefix-run history); actual = Selection.actual history; source = Selection.source history
   ; before-PC = Selection.before-PC history; after-PC = Selection.after-PC history
   ; gap-run = Selection.gap-run history; current-PC = Selection.current-PC history }

 -- Tail search either finds a real creator or returns the exact old lookup.
 find-allocation : ∀ {start events current worker request saved promise} → Runs start events current →
   lookup worker (S.admissions (M.world (core current))) ≡ just (S.admissionWorker request (S.selectEntry saved promise)) →
   lookup worker (S.admissions (M.world (core start))) ≡ just (S.admissionWorker request (S.selectEntry saved promise)) ⊎
     Allocation start events current worker request saved promise
 find-allocation done found = inj₁ found
 find-allocation (next {before} {middle} {current} {action} {tail} actual rest) found with find-allocation rest found
 ... | inj₂ history = inj₂ (prepend-allocation actual history)
 ... | inj₁ prior with select-before (observe action before actual) prior
 ...   | carried-select earlier = inj₁ earlier
 ...   | allocated-here promise-input prepared source = inj₂ (record
   { before = before; after = middle; label = action; prefix = []; gap = tail; decomposition = refl
   ; prefix-run = done; actual = actual; source = source; before-PC = prepared; promise-input = promise-input
   ; after-PC = prior; gap-run = rest; current-PC = found })

 find-selection : ∀ {start events current worker request saved promise entry} → Runs start events current →
   lookup worker (S.admissions (M.world (core current))) ≡ just (S.admissionWorker request (S.forkHandler saved promise entry)) →
   lookup worker (S.admissions (M.world (core start))) ≡ just (S.admissionWorker request (S.forkHandler saved promise entry)) ⊎
     Selection start events current worker request saved promise entry
 find-selection done found = inj₁ found
 find-selection (next {before} {middle} {current} {action} {tail} actual rest) found with find-selection rest found
 ... | inj₂ history = inj₂ (prepend-selection actual history)
 ... | inj₁ prior with fork-before (observe action before actual) prior
 ...   | carried-fork earlier = inj₁ earlier
 ...   | selected-here selecting source = inj₂ (record
   { before = before; after = middle; label = action; prefix = []; gap = tail; decomposition = refl
   ; prefix-run = done; actual = actual; source = source; before-PC = selecting
   ; after-PC = prior; gap-run = rest; current-PC = found })

 -- This closed packet fixes the request, captured IDs, actual operation labels
 -- and every matching PC; callers do not provide any of those PC equations.
 record SelectedOrigin (start : State) (observed : List Event) (current : State)
   (worker : WorkerId) (request : S.Admission) (heldLease : S.Lease) (promise : PromiseId) (entry : EntryId) : Set where
  field
   allocationBefore allocationAfter selectionBefore selectionAfter : State
   allocationLabel selectionLabel : Event
   prefix allocationGap forkGap : List Event
   decomposition : observed ≡ prefix ++ (allocationLabel ∷ (allocationGap ++ (selectionLabel ∷ forkGap)))
   prefix-run : Runs start prefix allocationBefore
   allocation-event : advance allocationLabel allocationBefore ≡ just allocationAfter
   allocation-source : M.advance (M.admissionStep worker Admission.allocatePromise) (core allocationBefore) ≡ just (core allocationAfter)
   before-allocation-PC : lookup worker (S.admissions (M.world (core allocationBefore))) ≡ just (S.admissionWorker request (S.prepare heldLease))
   promise-input : promise ≡ ident (S.nextPromise (M.world (core allocationBefore)))
   allocated-PC : lookup worker (S.admissions (M.world (core allocationAfter))) ≡ just (S.admissionWorker request (S.selectEntry heldLease promise))
   allocation-gap-run : Runs allocationAfter allocationGap selectionBefore
   before-selection-PC : lookup worker (S.admissions (M.world (core selectionBefore))) ≡ just (S.admissionWorker request (S.selectEntry heldLease promise))
   selection-event : advance selectionLabel selectionBefore ≡ just selectionAfter
   selection-source : M.advance (M.admissionStep worker Admission.chooseEntry) (core selectionBefore) ≡ just (core selectionAfter)
   selected-PC : lookup worker (S.admissions (M.world (core selectionAfter))) ≡ just (S.admissionWorker request (S.forkHandler heldLease promise entry))
   fork-gap-run : Runs selectionAfter forkGap current
   current-PC : lookup worker (S.admissions (M.world (core current))) ≡ just (S.admissionWorker request (S.forkHandler heldLease promise entry))

 combine : ∀ {start observed current worker request saved promise entry}
   (selected : Selection start observed current worker request saved promise entry) →
   Allocation start (Selection.prefix selected) (Selection.before selected) worker request saved promise →
   SelectedOrigin start observed current worker request saved promise entry
 combine selected allocated = record
   { allocationBefore = Allocation.before allocated; allocationAfter = Allocation.after allocated
   ; selectionBefore = Selection.before selected; selectionAfter = Selection.after selected
   ; allocationLabel = Allocation.label allocated; selectionLabel = Selection.label selected
   ; prefix = Allocation.prefix allocated; allocationGap = Allocation.gap allocated; forkGap = Selection.gap selected
   ; decomposition = trans (Selection.decomposition selected)
       (trans (cong (λ prefix → prefix ++ (Selection.label selected ∷ Selection.gap selected)) (Allocation.decomposition allocated))
         (++-assoc (Allocation.prefix allocated) (Allocation.label allocated ∷ Allocation.gap allocated) (Selection.label selected ∷ Selection.gap selected)))
   ; prefix-run = Allocation.prefix-run allocated; allocation-event = Allocation.actual allocated; allocation-source = Allocation.source allocated
   ; before-allocation-PC = Allocation.before-PC allocated; promise-input = Allocation.promise-input allocated; allocated-PC = Allocation.after-PC allocated
   ; allocation-gap-run = Allocation.gap-run allocated; before-selection-PC = Selection.before-PC selected
   ; selection-event = Selection.actual selected; selection-source = Selection.source selected; selected-PC = Selection.after-PC selected
   ; fork-gap-run = Selection.gap-run selected; current-PC = Selection.current-PC selected }

 -- Empty initialized admissions exclude the old-lookup alternatives, without
 -- imposing empty CM maps, outbound runtimes or fresh promise heaps.
 selected-origin : ∀ {start observed current worker request saved promise entry} →
   S.admissions (M.world (core start)) ≡ [] → Runs start observed current →
   lookup worker (S.admissions (M.world (core current))) ≡ just (S.admissionWorker request (S.forkHandler saved promise entry)) →
   SelectedOrigin start observed current worker request saved promise entry
 selected-origin {start} {observed} {current} {worker} empty path found with find-selection path found
 ... | inj₁ earlier = case trans (sym (cong (lookup worker) empty)) earlier of λ ()
 ... | inj₂ selected with find-allocation (Selection.prefix-run selected) (Selection.before-PC selected)
 ...   | inj₁ earlier = case trans (sym (cong (lookup worker) empty)) earlier of λ ()
 ...   | inj₂ allocated = combine selected allocated
