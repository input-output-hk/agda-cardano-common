{-# OPTIONS --guardedness #-}

-- Current/captured maps reference allocated entries; pending admission map
-- insertions additionally carry the allocation certificate for their entry.
module ConnectionManagement.Properties.StateMapReferences where

open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Counters using (CounterReferences)
open import ConnectionManagement.Properties.Entries using (Present; put-preserves-present)
open import ConnectionManagement.Properties.MapReferenceLaws
open import ConnectionManagement.Properties.Stores using (put-values)
open import ConnectionManagement.Properties.Counters using (lookup-all)
import ConnectionManagement.Rules.CM as CM
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Cleanup as Cleanup

-- No current map is present while the TMVar is taken.
CellReferences : EntryHeap → MapCell → Set
CellReferences heap (full m) = CounterReferences heap m
CellReferences heap (taken _) = ⊤

-- Every admission PC explicitly accounts for a restorable captured map.
AdmissionReferences : EntryHeap → AdmissionPC → Set
AdmissionReferences heap acquireMap = ⊤
AdmissionReferences heap (count l) = CounterReferences heap (savedMap l)
AdmissionReferences heap (prepare l) = CounterReferences heap (savedMap l)
AdmissionReferences heap (selectEntry l _) = CounterReferences heap (savedMap l)
AdmissionReferences heap (forkHandler l _ e) = CounterReferences heap (savedMap l) × Present e heap
AdmissionReferences heap (publish l _ e) = CounterReferences heap (savedMap l) × Present e heap
AdmissionReferences heap (reject l _) = CounterReferences heap (savedMap l)
AdmissionReferences heap (closeSocket _) = ⊤
AdmissionReferences heap (finished _) = ⊤
AdmissionReferences heap (countPublished _ _) = ⊤
AdmissionReferences heap (awaitHandshake _ _) = ⊤
AdmissionReferences heap (commitHandshake _ _) = ⊤
AdmissionReferences heap (countHandshake _) = ⊤
AdmissionReferences heap (notifyInbound _) = ⊤
AdmissionReferences heap (returnHandshake _) = ⊤
AdmissionReferences heap (completedHandshake _) = ⊤
AdmissionReferences heap impossibleHandshake = ⊤

-- Close/publish PCs carry both the original lease and a prospective output map.
CleanupReferences : EntryHeap → CleanupPC → Set
CleanupReferences heap cleanupAcquire = ⊤
CleanupReferences heap (cleanupSelect l) = CounterReferences heap (savedMap l)
CleanupReferences heap (cleanupClose l m _) = CounterReferences heap (savedMap l) × CounterReferences heap m
CleanupReferences heap (cleanupPublish l m _) = CounterReferences heap (savedMap l) × CounterReferences heap m
CleanupReferences heap (cleanupRestore l _) = CounterReferences heap (savedMap l)
CleanupReferences heap (cleanupWaiting _) = ⊤
CleanupReferences heap (cleanupFinalize _ _) = ⊤
CleanupReferences heap (cleanupCount _) = ⊤
CleanupReferences heap (cleanupDone _) = ⊤

AdmissionValid : EntryHeap → AdmissionWorker → Set
AdmissionValid heap a = AdmissionReferences heap (pc a)

-- Store traversal includes hidden duplicate-worker bindings.
At : EntryHeap → State → MapCell → Set
At heap s cell = CellReferences heap cell ×
  All (λ b → AdmissionValid heap (proj₂ b)) (admissions s) ×
  All (λ b → CleanupReferences heap (proj₂ b)) (cleanups s)
Valid : State → Set
Valid s = At (entries (cm s)) s (mapCell (cm s))

-- Reconstruct the state certificate after inspecting its current map cell.
restore-current : ∀ s cell → mapCell (cm s) ≡ cell → At (entries (cm s)) s cell → Valid s
restore-current s cell eq = subst (At (entries (cm s)) s) (sym eq)

-- Retention transports every map and the entry awaiting admission publication.
cell-retained : ∀ heap heap′ cell → (∀ e → Present e heap → Present e heap′) →
  CellReferences heap cell → CellReferences heap′ cell
cell-retained heap heap′ (full m) retain = map-retained heap heap′ m retain
cell-retained heap heap′ (taken _) retain valid = tt
admission-retained : ∀ heap heap′ p → (∀ e → Present e heap → Present e heap′) →
  AdmissionReferences heap p → AdmissionReferences heap′ p
admission-retained heap heap′ acquireMap retain valid = tt
admission-retained heap heap′ (count l) retain valid = map-retained heap heap′ (savedMap l) retain valid
admission-retained heap heap′ (prepare l) retain valid = map-retained heap heap′ (savedMap l) retain valid
admission-retained heap heap′ (selectEntry l p) retain valid = map-retained heap heap′ (savedMap l) retain valid
admission-retained heap heap′ (forkHandler l p e) retain valid = map-retained heap heap′ (savedMap l) retain (proj₁ valid) , retain e (proj₂ valid)
admission-retained heap heap′ (publish l p e) retain valid = map-retained heap heap′ (savedMap l) retain (proj₁ valid) , retain e (proj₂ valid)
admission-retained heap heap′ (reject l reason) retain valid = map-retained heap heap′ (savedMap l) retain valid
admission-retained heap heap′ (closeSocket reason) retain valid = tt
admission-retained heap heap′ (finished reason) retain valid = tt
admission-retained heap heap′ (countPublished p e) retain valid = tt
admission-retained heap heap′ (awaitHandshake p e) retain valid = tt
admission-retained heap heap′ (commitHandshake e result) retain valid = tt
admission-retained heap heap′ (countHandshake result) retain valid = tt
admission-retained heap heap′ (notifyInbound info) retain valid = tt
admission-retained heap heap′ (returnHandshake result) retain valid = tt
admission-retained heap heap′ (completedHandshake result) retain valid = tt
admission-retained heap heap′ impossibleHandshake retain valid = tt
cleanup-retained : ∀ heap heap′ p → (∀ e → Present e heap → Present e heap′) →
  CleanupReferences heap p → CleanupReferences heap′ p
cleanup-retained heap heap′ cleanupAcquire retain valid = tt
cleanup-retained heap heap′ (cleanupSelect l) retain valid = map-retained heap heap′ (savedMap l) retain valid
cleanup-retained heap heap′ (cleanupClose l m tail) retain valid = map-retained heap heap′ (savedMap l) retain (proj₁ valid) , map-retained heap heap′ m retain (proj₂ valid)
cleanup-retained heap heap′ (cleanupPublish l m tail) retain valid = map-retained heap heap′ (savedMap l) retain (proj₁ valid) , map-retained heap heap′ m retain (proj₂ valid)
cleanup-retained heap heap′ (cleanupRestore l err) retain valid = map-retained heap heap′ (savedMap l) retain valid
cleanup-retained heap heap′ (cleanupWaiting st) retain valid = tt
cleanup-retained heap heap′ (cleanupFinalize st outcome) retain valid = tt
cleanup-retained heap heap′ (cleanupCount outcome) retain valid = tt
cleanup-retained heap heap′ (cleanupDone outcome) retain valid = tt

-- No store-key uniqueness premise is needed to recover the selected certificate.
admission-valid : ∀ w a s → lookup w (admissions s) ≡ just a → Valid s → AdmissionValid (entries (cm s)) a
admission-valid w a s found v = lookup-all (AdmissionValid (entries (cm s))) w (admissions s) (proj₁ (proj₂ v)) found
cleanup-valid : ∀ w p s → lookup w (cleanups s) ≡ just p → Valid s → CleanupReferences (entries (cm s)) p
cleanup-valid w p s found v = lookup-all (CleanupReferences (entries (cm s))) w (cleanups s) (proj₂ (proj₂ v)) found

-- New continuations must supply all new map and publication-entry certificates.
admission-update : ∀ w a p s → AdmissionReferences (entries (cm s)) p → Valid s → Valid (Server.setPC w a p s)
admission-update w a p s pvalid v = proj₁ v ,
  put-values (AdmissionValid (entries (cm s))) w (record a { pc = p }) (admissions s) pvalid (proj₁ (proj₂ v)) , proj₂ (proj₂ v)
cleanup-update : ∀ w p s → CleanupReferences (entries (cm s)) p → Valid s → Valid (Cleanup.setCleanup w p s)
cleanup-update w p s pvalid v = proj₁ v , proj₁ (proj₂ v) ,
  put-values (CleanupReferences (entries (cm s))) w p (cleanups s) pvalid (proj₂ (proj₂ v))

-- Lift heap retention across all runtime certificates, not just the active worker.
at-retained : ∀ heap heap′ s cell → (∀ e → Present e heap → Present e heap′) →
  At heap s cell → At heap′ s cell
at-retained heap heap′ s cell retain v = cell-retained heap heap′ cell retain (proj₁ v) ,
  map (λ { {x = w , a} → admission-retained heap heap′ (pc a) retain }) (proj₁ (proj₂ v)) ,
  map (λ { {x = w , p} → cleanup-retained heap heap′ p retain }) (proj₂ (proj₂ v))
replace-cm : ∀ s c′ → mapCell c′ ≡ mapCell (cm s) →
  (∀ e → Present e (entries (cm s)) → Present e (entries c′)) → Valid s → Valid (record s { cm = c′ })
replace-cm s c′ same retain v = subst (At (entries c′) s) (sym same)
  (at-retained (entries (cm s)) (entries c′) s (mapCell (cm s)) retain v)
write-preserves : ∀ e st s → Valid s → Valid (record s { cm = record (cm s) { entries = put e st (entries (cm s)) } })
write-preserves e st s = replace-cm s (record (cm s) { entries = put e st (entries (cm s)) }) refl
  (λ q → put-preserves-present e q st (entries (cm s)))

-- Taking transfers the current map's references into the new captured lease.
take-maps : ∀ w s {l c′} → CM.takeMap w (cm s) ≡ just (l , c′) → Valid s →
  Valid (record s { cm = c′ }) × CounterReferences (entries c′) (savedMap l)
take-maps w s eq v with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with just-injective eq
...   | refl = (tt , proj₂ v) , proj₁ v

-- The actual output map is checked against the unchanged entry heap.
put-maps : ∀ l m s {c′} → CM.putMap l m (cm s) ≡ just c′ → CounterReferences (entries (cm s)) m →
  Valid s → Valid (record s { cm = c′ })
put-maps l m s eq refs v with mapCell (cm s)
... | full _ = case eq of λ ()
... | taken w with owner l ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with just-injective eq
...     | refl = refs , proj₂ v
