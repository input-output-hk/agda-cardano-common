{-# OPTIONS --guardedness #-}

-- The physical pool and protocol-job writers used by the layered preservation
-- proof. These adapters expose only reference tables, avoiding source reduction.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxUpdates (b : ErrorId → Bool) where
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; JobId)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (Present; lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other; UniqueKeys; put-unique)
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Properties.MuxProtocolJobs as Jobs
import ConnectionManagement.Properties.MuxHandlerSupervision as MuxFacts
module Mux = MuxFacts Types.TypedResult
import ConnectionManagement.Properties.LiveTrackerPoolContent as PoolContent
module Kernel = PoolContent Types.TypedResult
open import ConnectionManagement.Properties.LiveTrackerAuxContent b using (Owner; owner; JobContent; Completion; PoolContent)
open import ConnectionManagement.Properties.LiveTrackerAuxTransport b
 using (Retains; OwnerKept; completion-kept; by-fields; job-kept; source)
module U = P.U
module Pool = P.Pool

-- No infrastructure role can exist on an unpublished frame. The phase fact
-- is preserved by pool replacement and is sufficient even for partial startup.
Early : U.Frame → Set
Early f with U.progress f
... | U.returnedSuccess = P.Startup.phase (U.startup f) ≡ P.Startup.awaitPublication
... | U.handleAllocated hid mid = P.Startup.phase (U.startup f) ≡ P.Startup.awaitPublication
... | U.promisePublished hid mid = ⊤
EarlyRows : U.State → Set
EarlyRows u = All (λ { (w , f) → Early f }) (U.frames u)
early-at : ∀ {rows : Store WorkerId U.Frame} → All (λ { (w , f) → Early f }) rows → ∀ w f → lookup w rows ≡ just f → Early f
early-at {[]} [] w f ()
early-at {(q , first) ∷ rows} (good ∷ rest) w f found with w ≟ q
... | yes refl = case just-injective found of λ { refl → good }
... | no _ = early-at rest w f found
early-insert : ∀ (w : WorkerId) (f : U.Frame) (rows : Store WorkerId U.Frame) → Early f → All (λ { (w , f) → Early f }) rows → All (λ { (w , f) → Early f }) (put w f rows)
early-insert w f [] good [] = good ∷ []
early-insert w f ((q , first) ∷ rows) good (old ∷ rest) with w ≟ q
... | yes refl = good ∷ rest
... | no _ = old ∷ early-insert w f rows good rest
early-pool : ∀ f p → Early f → Early (record f { startup = record (U.startup f) { pool = p } })
early-pool f p good with U.progress f
... | U.returnedSuccess = good
... | U.handleAllocated hid mid = good
... | U.promisePublished hid mid = tt
early-kept : ∀ f next →
 (∀ hid mid → U.progress f ≡ U.promisePublished hid mid → U.progress next ≡ U.promisePublished hid mid) →
 P.Startup.phase (U.startup next) ≡ P.Startup.phase (U.startup f) → Early f → Early next
early-kept f next published phase good with U.progress f in before | U.progress next in after
... | U.returnedSuccess | U.returnedSuccess = trans phase good
... | U.returnedSuccess | U.handleAllocated hid mid = trans phase good
... | U.returnedSuccess | U.promisePublished hid mid = tt
... | U.handleAllocated hid mid | U.returnedSuccess = trans phase good
... | U.handleAllocated hid mid | U.handleAllocated hid′ mid′ = trans phase good
... | U.handleAllocated hid mid | U.promisePublished hid′ mid′ = tt
... | U.promisePublished hid mid | U.returnedSuccess = case published hid mid refl of λ ()
... | U.promisePublished hid mid | U.handleAllocated hid′ mid′ = case published hid mid refl of λ ()
... | U.promisePublished hid mid | U.promisePublished hid′ mid′ = tt
role-owner : ∀ w f s role j → lookup w (U.frames (P.base s)) ≡ just f → Early f →
 P.infraId role (P.Startup.phase (U.startup f)) ≡ just j → Owner w s
role-owner w f s role j found early bound with U.progress f in progress
... | U.promisePublished hid mid = owner f hid mid found progress
... | U.returnedSuccess rewrite early = case bound of λ ()
... | U.handleAllocated hid mid rewrite early = case bound of λ ()

-- All traversal rows are used for jobs and every pool is covered, including
-- the empty default of an owner with no mux frame.
record Valid (s : P.State) : Set where
 field unique : UniqueKeys (U.frames (P.base s))
       frames : EarlyRows (P.base s)
       jobs : All (λ { (j , job) → JobContent j job s }) (P.jobs s)
       pools : ∀ w → PoolContent w s
at : ∀ {A : Set} {rows : Store JobId A} {C : JobId → A → Set} →
 All (λ { (j , x) → C j x }) rows → ∀ j x → lookup j rows ≡ just x → C j x
at {rows = []} [] j x ()
at {rows = (k , first) ∷ rows} (good ∷ rest) j x found with j ≟ k
... | yes refl = case just-injective found of λ { refl → good }
... | no _ = at rest j x found
insert : ∀ {A : Set} (C : JobId → A → Set) j x rows → C j x →
 All (λ { (k , value) → C k value }) rows → All (λ { (k , value) → C k value }) (put j x rows)
insert C j x [] good [] = good ∷ []
insert C j x ((k , first) ∷ rows) good (old ∷ rest) with j ≟ k
... | yes refl = good ∷ rest
... | no _ = old ∷ insert C j x rows good rest

-- A selected frame replacement retains published identity, existing role
-- bindings, and all historical physical handles in that same pool.
frame-retains : ∀ w f next s → lookup w (U.frames (P.base s)) ≡ just f →
 (∀ hid mid → U.progress f ≡ U.promisePublished hid mid → U.progress next ≡ U.promisePublished hid mid) →
 (∀ role j → P.infraId role (P.Startup.phase (U.startup f)) ≡ just j → P.infraId role (P.Startup.phase (U.startup next)) ≡ just j) →
 (∀ j → Present j (Pool.handles (P.Startup.pool (U.startup f))) → Present j (Pool.handles (P.Startup.pool (U.startup next)))) →
 Retains s (record s { base = U.setFrame w next (P.base s) })
frame-retains w f next s found progress roles physical = record
 { owners = owners; handles = handles
 ; jobs = λ j job found → Types.phase job , found
 ; captured = λ j w mid dir n gen result found → found }
 where
 owners : ∀ q (old : Owner q s) → Σ (Owner q (record s { base = U.setFrame w next (P.base s) })) (OwnerKept old)
 owners q old with q ≟ w
 ... | yes refl = case just-injective (trans (sym found) (Owner.found old)) of λ { refl → owner next (Owner.handle old) (Owner.mux old) (lookup-put w next (U.frames (P.base s)))
     (progress _ _ (Owner.published old)) , record { same-mux = refl; roles = roles } }
 ... | no apart = owner (Owner.frame old) (Owner.handle old) (Owner.mux old)
     (trans (lookup-put-other w q next (U.frames (P.base s)) apart) (Owner.found old))
     (Owner.published old) , record { same-mux = refl; roles = λ role j present → present }
 handles : ∀ q j phase → lookup j (Pool.handles (P.poolAt q s)) ≡ just phase →
   Present j (Pool.handles (P.poolAt q (record s { base = U.setFrame w next (P.base s) })))
 handles q j phase present with q ≟ w
 ... | yes refl rewrite lookup-put w next (U.frames (P.base s)) | found = physical j (phase , present)
 ... | no apart rewrite lookup-put-other w q next (U.frames (P.base s)) apart = phase , present

pool-retains : ∀ w f p s → lookup w (U.frames (P.base s)) ≡ just f →
 (∀ j → Present j (Pool.handles (P.poolAt w s)) → Present j (Pool.handles p)) → Retains s (P.setPool w f p s)
pool-retains w f p s found physical = frame-retains w f _ s found (λ hid mid eq → eq)
 (λ role j eq → eq) physical′
 where
 physical′ : ∀ j → Present j (Pool.handles (P.Startup.pool (U.startup f))) → Present j (Pool.handles p)
 physical′ j old = physical j (subst (λ p → Present j (Pool.handles p)) (sym same) old)
  where
  same : P.poolAt w s ≡ P.Startup.pool (U.startup f)
  same rewrite found = refl

-- Adapter to the generic pool-content theorem; retarget old references before
-- applying the actual primitive, including body-return and queue publication.
pool-content : ∀ w s t a p → Retains s t → Pool.step a (P.poolAt w s) ≡ just p →
 PoolContent w s → Kernel.NewReturn a (λ value → Completion w value t) →
 Kernel.Content (λ value → Completion w value t) p
pool-content w s t a p kept actual good new = Kernel.step-preserves _ a (P.poolAt w s) actual
 (Kernel.map-content (completion-kept kept w)
   (record { queued = PoolContent.queued good; returned = PoolContent.returned good })) new

-- A fresh physical fork cannot replace a captured job. Ordinary phase writers
-- can replace only an uncommitted body; prior captured payloads survive.
fresh-job : ∀ j job s → lookup j (P.jobs s) ≡ nothing →
 Retains s (record s { jobs = put j job (P.jobs s) })
fresh-job j job s absent = by-fields s _ refl (λ w k phase found → phase , found) rows captured
 where
 rows : ∀ k old → lookup k (P.jobs s) ≡ just old →
   Σ Types.BodyPhase (λ phase → lookup k (put j job (P.jobs s)) ≡ just (record old { phase = phase }))
 rows k old found with k ≟ j
 ... | yes refl = case trans (sym absent) found of λ ()
 ... | no apart = Types.phase old , trans (lookup-put-other j k job (P.jobs s) apart) found
 captured : ∀ k w mid dir n gen result → lookup k (P.jobs s) ≡ just (Types.protocolJob w mid dir n gen (Types.resultCaptured result)) →
   lookup k (put j job (P.jobs s)) ≡ just (Types.protocolJob w mid dir n gen (Types.resultCaptured result))
 captured k w mid dir n gen result found with k ≟ j
 ... | yes refl = case trans (sym absent) found of λ ()
 ... | no apart = trans (lookup-put-other j k job (P.jobs s) apart) found
phase-job : ∀ j job phase s → lookup j (P.jobs s) ≡ just job →
 (∀ result → Types.phase job ≢ Types.resultCaptured result) →
 Retains s (record s { jobs = put j (record job { phase = phase }) (P.jobs s) })
phase-job j job phase s found uncommitted = by-fields s _ refl (λ w k ph eq → ph , eq) rows captured
 where
 rows : ∀ k old → lookup k (P.jobs s) ≡ just old →
   Σ Types.BodyPhase (λ phase′ → lookup k (put j (record job { phase = phase }) (P.jobs s)) ≡ just (record old { phase = phase′ }))
 rows k old present with k ≟ j
 ... | yes refl = case just-injective (trans (sym found) present) of λ { refl → phase , lookup-put j _ (P.jobs s) }
 ... | no apart = Types.phase old , trans (lookup-put-other j k _ (P.jobs s) apart) present
 captured : ∀ k w mid dir n gen result → lookup k (P.jobs s) ≡ just (Types.protocolJob w mid dir n gen (Types.resultCaptured result)) →
   lookup k (put j (record job { phase = phase }) (P.jobs s)) ≡ just (Types.protocolJob w mid dir n gen (Types.resultCaptured result))
 captured k w mid dir n gen result present with k ≟ j
 ... | yes refl = ⊥-elim (uncommitted result (cong Types.phase (just-injective (trans (sym found) present))))
 ... | no apart = trans (lookup-put-other j k _ (P.jobs s) apart) present

-- Whole-core rebuilding: unchanged pools retarget payload witnesses through
-- Retains; the selected pool additionally follows its checked kernel writer.
map-pool : ∀ w s t p → Retains s t → PoolContent w s →
 p ≡ P.poolAt w s → Kernel.Content (λ value → Completion w value t) p
map-pool w s t p kept good same = subst (Kernel.Content (λ value → Completion w value t)) (sym same)
 (Kernel.map-content (completion-kept kept w)
  (record { queued = PoolContent.queued good; returned = PoolContent.returned good }))
as-pool : ∀ w s → Kernel.Content (λ value → Completion w value s) (P.poolAt w s) → PoolContent w s
as-pool w s good = record { queued = Kernel.Content.queued good; returned = Kernel.Content.returned good }
same-valid : ∀ s t → Retains s t → U.frames (P.base t) ≡ U.frames (P.base s) → P.jobs t ≡ P.jobs s → (∀ w → P.poolAt w t ≡ P.poolAt w s) → Valid s → Valid t
same-valid s t kept frames rows pools valid = record
 { unique = subst UniqueKeys (sym frames) (Valid.unique valid)
 ; frames = subst (All (λ { (w , f) → Early f })) (sym frames) (Valid.frames valid)
 ; jobs = subst (All (λ { (j , job) → JobContent j job t })) (sym rows)
     (All.map (λ { {j , job} → job-kept kept j job }) (Valid.jobs valid))
 ; pools = λ w → as-pool w t (map-pool w s t _ kept (Valid.pools valid w) (pools w)) }
source-valid : ∀ c s → Valid s → Valid (P.setSource c s)
source-valid c s = same-valid s _ (source c s) refl refl (λ w → refl)

-- A pool operation keeps the job table and inserts no arbitrary result value.
pool-valid : ∀ w f a s {p} → lookup w (U.frames (P.base s)) ≡ just f →
 (actual : Pool.step a (P.poolAt w s) ≡ just p) →
 Kernel.NewReturn a (λ value → Completion w value (P.setPool w f p s)) → Valid s → Valid (P.setPool w f p s)
pool-valid w f a s {p} found actual new valid = record
 { unique = put-unique w _ _ (Valid.unique valid)
 ; frames = early-insert w _ _ (early-pool f p (early-at (Valid.frames valid) w f found)) (Valid.frames valid)
 ; jobs = All.map (λ { {j , job} → job-kept kept j job }) (Valid.jobs valid)
 ; pools = pools }
 where
 t = P.setPool w f p s
 kept = pool-retains w f p s found (Kernel.handles-retained a (P.poolAt w s) actual)
 pools : ∀ q → PoolContent q t
 pools q with q ≟ w
 ... | yes refl = as-pool w t (subst (Kernel.Content (λ value → Completion w value t))
     (sym (Jobs.pool-same w f p s)) (pool-content w s t a p kept actual (Valid.pools valid w) new))
 ... | no apart = as-pool q t (map-pool q s t _ kept (Valid.pools valid q) (Jobs.pool-other w q f p s apart))

-- Insert one explicitly established job and retarget every older job/payload.
job-valid : ∀ j job s → Retains s (record s { jobs = put j job (P.jobs s) }) →
 JobContent j job (record s { jobs = put j job (P.jobs s) }) → Valid s → Valid (record s { jobs = put j job (P.jobs s) })
job-valid j job s kept good valid = record
 { unique = Valid.unique valid
 ; frames = Valid.frames valid
 ; jobs = insert (λ j job → JobContent j job _) j job (P.jobs s) good
     (All.map (λ { {j , job} → job-kept kept j job }) (Valid.jobs valid))
 ; pools = λ w → as-pool w _ (map-pool w s _ _ kept (Valid.pools valid w) refl) }

-- Changing a frame's progress or startup also replaces its pool projection.
frame-valid : ∀ w next s → Early next →
 (kept : Retains s (record s { base = U.setFrame w next (P.base s) })) →
 Kernel.Content (λ value → Completion w value (record s { base = U.setFrame w next (P.base s) })) (P.Startup.pool (U.startup next)) →
 Valid s → Valid (record s { base = U.setFrame w next (P.base s) })
frame-valid w next s early kept selected valid = record
 { unique = put-unique w next _ (Valid.unique valid)
 ; frames = early-insert w next _ early (Valid.frames valid)
 ; jobs = All.map (λ { {j , job} → job-kept kept j job }) (Valid.jobs valid)
 ; pools = pools }
 where
 t = record s { base = U.setFrame w next (P.base s) }
 pools : ∀ q → PoolContent q t
 pools q with q ≟ w
 ... | yes refl = as-pool w t (subst (Kernel.Content (λ value → Completion w value t))
     (sym (cong P.Startup.pool (Mux.put-same w next (P.base s)))) selected)
 ... | no apart = as-pool q t (map-pool q s t _ kept (Valid.pools valid q)
     (cong P.Startup.pool (Mux.put-other w q next (P.base s) apart)))

-- A wholly fresh owner starts with the empty pool; existing owners are
-- necessarily different from its key.
fresh-frame : ∀ w next s → lookup w (U.frames (P.base s)) ≡ nothing →
 U.startup next ≡ P.Startup.initial → Retains s (record s { base = U.setFrame w next (P.base s) })
fresh-frame w next s absent startup = record
 { owners = owners; handles = handles
 ; jobs = λ j job found → Types.phase job , found
 ; captured = λ j w mid dir n gen result found → found }
 where
 owners : ∀ q (old : Owner q s) → Σ (Owner q (record s { base = U.setFrame w next (P.base s) })) (OwnerKept old)
 owners q old with q ≟ w
 ... | yes refl = case trans (sym absent) (Owner.found old) of λ ()
 ... | no apart = owner (Owner.frame old) (Owner.handle old) (Owner.mux old)
     (trans (lookup-put-other w q next (U.frames (P.base s)) apart) (Owner.found old))
     (Owner.published old) , record { same-mux = refl; roles = λ role j present → present }
 handles : ∀ q j phase → lookup j (Pool.handles (P.poolAt q s)) ≡ just phase →
   Present j (Pool.handles (P.poolAt q (record s { base = U.setFrame w next (P.base s) })))
 handles q j phase present with q ≟ w
 ... | yes refl rewrite absent = case present of λ ()
 ... | no apart rewrite lookup-put-other w q next (U.frames (P.base s)) apart = phase , present

-- Published progress makes the supporting early-frame clause vacuous.
early-published : ∀ f hid mid → U.progress f ≡ U.promisePublished hid mid → Early f
early-published f hid mid published with U.progress f
... | U.promisePublished hid′ mid′ = tt
... | U.returnedSuccess = case published of λ ()
... | U.handleAllocated hid′ mid′ = case published of λ ()

-- The role-based owner certificate uses the selected frame itself.
role-owner-frame : ∀ w f s role j found early bound →
 Owner.frame (role-owner w f s role j found early bound) ≡ f
role-owner-frame w (U.frame h origin ps flow (U.promisePublished hid mid) startup setup) s role j found early bound = refl
role-owner-frame w (U.frame h origin ps flow U.returnedSuccess startup setup) s role j found early bound = case subst (λ pc → P.infraId role pc ≡ just j) early bound of λ ()
role-owner-frame w (U.frame h origin ps flow (U.handleAllocated hid mid) startup setup) s role j found early bound = case subst (λ pc → P.infraId role pc ≡ just j) early bound of λ ()
