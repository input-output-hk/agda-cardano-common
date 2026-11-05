{-# OPTIONS --guardedness #-}

-- Recover acquisition creators from original labeled runs. Stored-row tracking
-- tolerates shadowed rows without assuming store-key uniqueness.
module ConnectionManagement.Properties.OutboundOriginHistory where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId; EntryId; PromiseId; ConnectionKey; ident)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Properties.OutboundOriginCore as Core

record Allocation (before after : O.Configuration) (caller : WorkerId) (request : A.Request) (entry : EntryId) (promise : PromiseId) : Set where
 field
  beforeFrame afterFrame : A.Frame
  before-found : lookup caller (O.acquiring before) ≡ just beforeFrame
  before-request : A.req beforeFrame ≡ request
  before-PC : A.pc beforeFrame ≡ A.allocatePromise entry
  actual : A.step caller (M.responder (O.core before)) A.newPromise beforeFrame (M.world (O.core before)) ≡ just (afterFrame , M.world (O.core after))
  after-request : A.req afterFrame ≡ request
  after-PC : A.pc afterFrame ≡ A.openSocket entry promise
  promise-input : promise ≡ ident (S.nextPromise (M.world (O.core before)))
record Reservation (before after : O.Configuration) (caller : WorkerId) (request : A.Request) (entry : EntryId) : Set where
 field
  beforeFrame afterFrame : A.Frame
  before-found : lookup caller (O.acquiring before) ≡ just beforeFrame
  before-request : A.req beforeFrame ≡ request
  before-PC : A.pc beforeFrame ≡ A.selecting
  actual : A.step caller (M.responder (O.core before)) (A.select nothing) beforeFrame (M.world (O.core before)) ≡ just (afterFrame , M.world (O.core after))
  after-request : A.req afterFrame ≡ request
  after-PC : A.pc afterFrame ≡ A.count (A.allocatePromise entry)
  entry-input : entry ≡ ident (S.nextEntry (S.cm (M.world (O.core before))))

-- Only an actual active acquisition writer can create the promise mark.
promise-before : ∀ {before after caller request entry promise} → Core.Effect before after →
 Core.Marked Core.promiseMark (O.acquiring after) caller request (entry , promise) →
 Core.Marked Core.promiseMark (O.acquiring before) caller request (entry , promise) ⊎ Allocation before after caller request entry promise
promise-before {caller = caller} {request} {entry} {promise} (Core.continued preserved) observed = inj₁ (Core.Backwards.promise-back preserved caller request entry promise observed)
promise-before {caller = caller} {request} {entry} {promise} (Core.same unchanged) observed = inj₁ (subst (λ rows → Core.Marked Core.promiseMark rows caller request (entry , promise)) unchanged observed)
promise-before {before} {caller = caller} {request} {entry} {promise} (Core.removed actor changed) observed = inj₁
 (Core.Backwards.promise-back (Core.removed-backwards actor (O.acquiring before)) caller request entry promise
   (subst (λ rows → Core.Marked Core.promiseMark rows caller request (entry , promise)) changed observed))
promise-before {before} {caller = caller} {request} {entry} {promise} (Core.begun actor req changed) observed = inj₁
 (Core.Backwards.promise-back (Core.begun-backwards actor req (O.acquiring before)) caller request entry promise
   (subst (λ rows → Core.Marked Core.promiseMark rows caller request (entry , promise)) changed observed))
promise-before {before} {after} {caller} {request} {entry} {promise}
 (Core.advanced actor action oldFrame newFrame owned actual changed) (Core.marked savedFrame member sameRequest found)
 with Core.put-member actor newFrame (O.acquiring before) (subst (λ rows → (caller , savedFrame) ∈ rows) changed member)
... | inj₂ prior = inj₁ (Core.marked savedFrame prior sameRequest found)
... | inj₁ refl with Core.step-classify caller (M.responder (O.core before)) action oldFrame (M.world (O.core before)) actual
...   | Core.preserved requestSame promiseBack entryBack = inj₁ (Core.marked oldFrame (Core.lookup-member caller (O.acquiring before) owned) (trans (sym requestSame) sameRequest) (promiseBack entry promise found))
...   | Core.reserved actionEq requestSame beforePC afterPC = case trans (sym (cong Core.promiseMark afterPC)) found of λ ()
...   | Core.allocated oldEntry actionEq requestSame beforePC afterPC with just-injective (trans (sym (cong Core.promiseMark afterPC)) found)
...     | refl = inj₂ (record
 { beforeFrame = oldFrame; afterFrame = newFrame; before-found = owned
 ; before-request = trans (sym requestSame) sameRequest; before-PC = beforePC
 ; actual = subst (λ act → A.step caller (M.responder (O.core before)) act oldFrame (M.world (O.core before)) ≡ just (newFrame , M.world (O.core after))) actionEq actual
 ; after-request = sameRequest; after-PC = afterPC; promise-input = refl })

-- Entry selection precedes allocation; reused/failed choices cannot create this mark.
entry-before : ∀ {before after caller request entry} → Core.Effect before after →
 Core.Marked Core.entryMark (O.acquiring after) caller request entry →
 Core.Marked Core.entryMark (O.acquiring before) caller request entry ⊎ Reservation before after caller request entry
entry-before {caller = caller} {request} {entry} (Core.continued preserved) observed = inj₁ (Core.Backwards.entry-back preserved caller request entry observed)
entry-before {caller = caller} {request} {entry} (Core.same unchanged) observed = inj₁ (subst (λ rows → Core.Marked Core.entryMark rows caller request entry) unchanged observed)
entry-before {before} {caller = caller} {request} {entry} (Core.removed actor changed) observed = inj₁
 (Core.Backwards.entry-back (Core.removed-backwards actor (O.acquiring before)) caller request entry
   (subst (λ rows → Core.Marked Core.entryMark rows caller request entry) changed observed))
entry-before {before} {caller = caller} {request} {entry} (Core.begun actor req changed) observed = inj₁
 (Core.Backwards.entry-back (Core.begun-backwards actor req (O.acquiring before)) caller request entry
   (subst (λ rows → Core.Marked Core.entryMark rows caller request entry) changed observed))
entry-before {before} {after} {caller} {request} {entry}
 (Core.advanced actor action oldFrame newFrame owned actual changed) (Core.marked savedFrame member sameRequest found)
 with Core.put-member actor newFrame (O.acquiring before) (subst (λ rows → (caller , savedFrame) ∈ rows) changed member)
... | inj₂ prior = inj₁ (Core.marked savedFrame prior sameRequest found)
... | inj₁ refl with Core.step-classify caller (M.responder (O.core before)) action oldFrame (M.world (O.core before)) actual
...   | Core.preserved requestSame promiseBack entryBack = inj₁ (Core.marked oldFrame (Core.lookup-member caller (O.acquiring before) owned) (trans (sym requestSame) sameRequest) (entryBack entry found))
...   | Core.allocated oldEntry actionEq requestSame beforePC afterPC = case trans (sym (cong Core.entryMark afterPC)) found of λ ()
...   | Core.reserved actionEq requestSame beforePC afterPC with just-injective (trans (sym (cong Core.entryMark afterPC)) found)
...     | refl = inj₂ (record
 { beforeFrame = oldFrame; afterFrame = newFrame; before-found = owned
 ; before-request = trans (sym requestSame) sameRequest; before-PC = beforePC
 ; actual = subst (λ act → A.step caller (M.responder (O.core before)) act oldFrame (M.world (O.core before)) ≡ just (newFrame , M.world (O.core after))) actionEq actual
 ; after-request = sameRequest; after-PC = afterPC; entry-input = refl })

-- This engine indexes every occurrence by the original outer event alphabet.
module Engine (State Event : Set) (advance : Event → State → Maybe State)
 (source : State → O.Configuration)
 (observe : ∀ action before {after} → advance action before ≡ just after → Core.Effect (source before) (source after)) where

 data Runs : State → List Event → State → Set where
  done : ∀ {s} → Runs s [] s
  next : ∀ {s middle after action events} → advance action s ≡ just middle → Runs middle events after → Runs s (action ∷ events) after

 private
  module Search {Value : Set} (mark : A.PC → Maybe Value)
   (Witness : O.Configuration → O.Configuration → WorkerId → A.Request → Value → Set)
   (back : ∀ {before after caller request value} → Core.Effect before after →
     Core.Marked mark (O.acquiring after) caller request value →
     Core.Marked mark (O.acquiring before) caller request value ⊎ Witness before after caller request value) where

   record Located (start current : State) (events : List Event) (caller : WorkerId) (request : A.Request) (value : Value) : Set where
    field
     before after : State
     label : Event
     prefix gap : List Event
     decomposition : events ≡ prefix ++ label ∷ gap
     prefix-run : Runs start prefix before
     actual : advance label before ≡ just after
     birth : Witness (source before) (source after) caller request value
     gap-run : Runs after gap current

   prepend : ∀ {start middle current action events caller request value} →
     advance action start ≡ just middle → Located middle current events caller request value →
     Located start current (action ∷ events) caller request value
   prepend {action = action} enabled located = record
    { before = Located.before located; after = Located.after located; label = Located.label located
    ; prefix = action ∷ Located.prefix located; gap = Located.gap located
    ; decomposition = cong (action ∷_) (Located.decomposition located)
    ; prefix-run = next enabled (Located.prefix-run located); actual = Located.actual located
    ; birth = Located.birth located; gap-run = Located.gap-run located }

   find : ∀ {start current events caller request value} → Runs start events current →
     Core.Marked mark (O.acquiring (source current)) caller request value →
     Core.Marked mark (O.acquiring (source start)) caller request value ⊎ Located start current events caller request value
   find done observed = inj₁ observed
   find (next {s = start} {middle = middle} {action = action} {events = events} enabled rest) observed with find rest observed
   ... | inj₂ located = inj₂ (prepend enabled located)
   ... | inj₁ prior with back (observe action start enabled) prior
   ...   | inj₁ earlier = inj₁ earlier
   ...   | inj₂ created = inj₂ (record
    { before = start; after = middle; label = action; prefix = []; gap = events
    ; decomposition = refl; prefix-run = done; actual = enabled; birth = created; gap-run = rest })

   find-created : ∀ {start current events caller request value} → O.acquiring (source start) ≡ [] →
     Runs start events current → Core.Marked mark (O.acquiring (source current)) caller request value →
     Located start current events caller request value
   find-created {caller = caller} empty path observed with find path observed
   ... | inj₂ located = located
   ... | inj₁ (Core.marked savedFrame member sameRequest found) with subst (λ rows → (caller , savedFrame) ∈ rows) empty member
   ...   | ()

  module Promises = Search Core.promiseMark (λ before after caller request value → Allocation before after caller request (proj₁ value) (proj₂ value)) promise-before
  module Entries = Search Core.entryMark Reservation entry-before

 -- The initialized endpoint supplies only a final operational fork row. Both
 -- creator events and every intervening label are recovered from its run.
 record Origin (start current : State) (observed : List Event) (caller : WorkerId)
   (request : A.Request) (entry : EntryId) (promise : PromiseId) (key : ConnectionKey) : Set where
  field
   selectionBefore selectionAfter allocationBefore allocationAfter : State
   selectionLabel allocationLabel : Event
   prefix selectionGap forkGap : List Event
   decomposition : observed ≡ prefix ++ selectionLabel ∷ (selectionGap ++ allocationLabel ∷ forkGap)
   prefix-run : Runs start prefix selectionBefore
   selection-event : advance selectionLabel selectionBefore ≡ just selectionAfter
   reservation : Reservation (source selectionBefore) (source selectionAfter) caller request entry
   selection-gap-run : Runs selectionAfter selectionGap allocationBefore
   allocation-event : advance allocationLabel allocationBefore ≡ just allocationAfter
   allocation : Allocation (source allocationBefore) (source allocationAfter) caller request entry promise
   fork-gap-run : Runs allocationAfter forkGap current
   final-PC : lookup caller (O.acquiring (source current)) ≡ just (A.frame request (A.forkHandler entry promise key))

 origin : ∀ {start current observed caller request entry promise key} → O.acquiring (source start) ≡ [] →
   Runs start observed current →
   lookup caller (O.acquiring (source current)) ≡ just (A.frame request (A.forkHandler entry promise key)) →
   Origin start current observed caller request entry promise key
 origin {start} {current} {observed} {caller} {request} {entry} {promise} {key} empty path final = result
  where
  allocated : Promises.Located start current observed caller request (entry , promise)
  allocated = Promises.find-created empty path (Core.marked (A.frame request (A.forkHandler entry promise key))
    (Core.lookup-member caller (O.acquiring (source current)) final) refl refl)
  old : Allocation (source (Promises.Located.before allocated)) (source (Promises.Located.after allocated)) caller request entry promise
  old = Promises.Located.birth allocated
  selected : Entries.Located start (Promises.Located.before allocated) (Promises.Located.prefix allocated) caller request entry
  selected = Entries.find-created empty (Promises.Located.prefix-run allocated)
    (Core.marked (Allocation.beforeFrame old)
      (Core.lookup-member caller (O.acquiring (source (Promises.Located.before allocated))) (Allocation.before-found old))
      (Allocation.before-request old) (cong Core.entryMark (Allocation.before-PC old)))
  result : Origin start current observed caller request entry promise key
  result = record
   { selectionBefore = Entries.Located.before selected; selectionAfter = Entries.Located.after selected
   ; allocationBefore = Promises.Located.before allocated; allocationAfter = Promises.Located.after allocated
   ; selectionLabel = Entries.Located.label selected; allocationLabel = Promises.Located.label allocated
   ; prefix = Entries.Located.prefix selected; selectionGap = Entries.Located.gap selected; forkGap = Promises.Located.gap allocated
   ; decomposition = trans (Promises.Located.decomposition allocated)
       (trans (cong (λ prefix → prefix ++ Promises.Located.label allocated ∷ Promises.Located.gap allocated) (Entries.Located.decomposition selected))
         (++-assoc (Entries.Located.prefix selected) (Entries.Located.label selected ∷ Entries.Located.gap selected) (Promises.Located.label allocated ∷ Promises.Located.gap allocated)))
   ; prefix-run = Entries.Located.prefix-run selected; selection-event = Entries.Located.actual selected
   ; reservation = Entries.Located.birth selected; selection-gap-run = Entries.Located.gap-run selected
   ; allocation-event = Promises.Located.actual allocated; allocation = old; fork-gap-run = Promises.Located.gap-run allocated
   ; final-PC = final }
