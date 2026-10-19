{-# OPTIONS --guardedness #-}

-- All current, saved, and prospective maps have unique remote/local keys.
-- This does not require unique worker-store keys or unique entry aliases.
module ConnectionManagement.Properties.StateMapUniqueness where

open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using (All)
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
open import ConnectionManagement.Properties.MapUniqueness
open import ConnectionManagement.Properties.Stores using (put-values)
open import ConnectionManagement.Properties.Counters using (lookup-all)
import ConnectionManagement.Rules.CM as CM
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Cleanup as Cleanup

-- No current map is present while the TMVar is taken.
CellUnique : MapCell → Set
CellUnique (full m) = MapUnique m
CellUnique (taken _) = ⊤

-- Every admission PC explicitly accounts for a restorable captured map.
AdmissionMaps : AdmissionPC → Set
AdmissionMaps acquireMap = ⊤
AdmissionMaps (count l) = MapUnique (savedMap l)
AdmissionMaps (prepare l) = MapUnique (savedMap l)
AdmissionMaps (selectEntry l _) = MapUnique (savedMap l)
AdmissionMaps (forkHandler l _ _) = MapUnique (savedMap l)
AdmissionMaps (publish l _ _) = MapUnique (savedMap l)
AdmissionMaps (reject l _) = MapUnique (savedMap l)
AdmissionMaps (closeSocket _) = ⊤
AdmissionMaps (finished _) = ⊤
AdmissionMaps (countPublished _ _) = ⊤
AdmissionMaps (awaitHandshake _ _) = ⊤
AdmissionMaps (commitHandshake _ _) = ⊤
AdmissionMaps (countHandshake _) = ⊤
AdmissionMaps (notifyInbound _) = ⊤
AdmissionMaps (returnHandshake _) = ⊤
AdmissionMaps (completedHandshake _) = ⊤
AdmissionMaps impossibleHandshake = ⊤

-- Close/publish PCs carry both the original lease and a prospective output map.
CleanupMaps : CleanupPC → Set
CleanupMaps cleanupAcquire = ⊤
CleanupMaps (cleanupSelect l) = MapUnique (savedMap l)
CleanupMaps (cleanupClose l m _) = MapUnique (savedMap l) × MapUnique m
CleanupMaps (cleanupPublish l m _) = MapUnique (savedMap l) × MapUnique m
CleanupMaps (cleanupRestore l _) = MapUnique (savedMap l)
CleanupMaps (cleanupWaiting _) = ⊤
CleanupMaps (cleanupFinalize _ _) = ⊤
CleanupMaps (cleanupCount _) = ⊤
CleanupMaps (cleanupDone _) = ⊤

AdmissionValid : AdmissionWorker → Set
AdmissionValid a = AdmissionMaps (pc a)

-- Traverse every stored continuation, including shadowed worker bindings.
At : State → MapCell → Set
At s cell = CellUnique cell ×
  All (λ b → AdmissionValid (proj₂ b)) (admissions s) ×
  All (λ b → CleanupMaps (proj₂ b)) (cleanups s)
Valid : State → Set
Valid s = At s (mapCell (cm s))

-- Reassemble a state certificate after inspecting its current map cell.
restore-current : ∀ s cell → mapCell (cm s) ≡ cell → At s cell → Valid s
restore-current s cell eq = subst (At s) (sym eq)

-- Lookup retrieves a certificate without requiring unique worker-store keys.
admission-valid : ∀ w a s → lookup w (admissions s) ≡ just a → Valid s → AdmissionValid a
admission-valid w a s found v = lookup-all AdmissionValid w (admissions s) (proj₁ (proj₂ v)) found
cleanup-valid : ∀ w p s → lookup w (cleanups s) ≡ just p → Valid s → CleanupMaps p
cleanup-valid w p s found v = lookup-all CleanupMaps w (cleanups s) (proj₂ (proj₂ v)) found

-- Update only the selected continuation; all other certificates are retained.
admission-update : ∀ w a p s → AdmissionMaps p → Valid s → Valid (Server.setPC w a p s)
admission-update w a p s pvalid v = proj₁ v ,
  put-values AdmissionValid w (record a { pc = p }) (admissions s) pvalid (proj₁ (proj₂ v)) , proj₂ (proj₂ v)
cleanup-update : ∀ w p s → CleanupMaps p → Valid s → Valid (Cleanup.setCleanup w p s)
cleanup-update w p s pvalid v = proj₁ v , proj₁ (proj₂ v) ,
  put-values CleanupMaps w p (cleanups s) pvalid (proj₂ (proj₂ v))

-- CM entry-only modifications preserve the current map and all captured maps.
replace-cm : ∀ s c′ → mapCell c′ ≡ mapCell (cm s) → Valid s → Valid (record s { cm = c′ })
replace-cm s c′ same v = subst CellUnique (sym same) (proj₁ v) , proj₂ v

-- Taking a full map transfers its certificate into the newly captured lease.
take-maps : ∀ w s {l c′} → CM.takeMap w (cm s) ≡ just (l , c′) → Valid s →
  CellUnique (mapCell c′) × MapUnique (savedMap l)
take-maps w s eq v with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with just-injective eq
...   | refl = tt , proj₁ v

-- Publishing requires the actual output map's certificate, not just the lease's.
put-maps : ∀ l m s {c′} → CM.putMap l m (cm s) ≡ just c′ → MapUnique m →
  Valid s → Valid (record s { cm = c′ })
put-maps l m s eq unique v with mapCell (cm s)
... | full _ = case eq of λ ()
... | taken w with owner l ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with just-injective eq
...     | refl = unique , proj₂ v

-- Identity-guarded deletion preserves both nested key-uniqueness levels.
purge-unique : ∀ k e m → MapUnique m → MapUnique (Cleanup.purgeCaptured k e m)
purge-unique k e m unique with lookupConnection k m
... | nothing = unique
... | just current with e ≟ current
...   | no _ = unique
...   | yes _ = delete-connection-unique k m unique
