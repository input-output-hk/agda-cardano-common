{-# OPTIONS --guardedness #-}

-- Immutable negotiated content for current mux frames. Publication remembers
-- the actual shared registration read by the writer; capture agreement resolves
-- it to the frame's original descriptor at the frontend endpoint.
module ConnectionManagement.Properties.LiveTrackerFrameContent where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId)
open import ConnectionManagement.Store using (Store; lookup; put)
import Data.Bool.ListAction
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.MuxProtocolJobs as P
module U = P.U
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Properties.StateRetention as State
import ConnectionManagement.Properties.IGTableRetention as Tables
import ConnectionManagement.Properties.OutboundWorldInvariant as World
import ConnectionManagement.Properties.LiveTrackerChainSteps as Chain
import ConnectionManagement.Properties.OutboundHandlerSupervision as Base

-- A published frame has an actual immutable handler registration and the exact
-- negotiated result written for that registration, with its own handle and flow.
Published : WorkerId → U.Frame → S.State → Set
Published w f s with U.progress f
... | U.returnedSuccess = ⊤
... | U.handleAllocated hid mid = ⊤
... | U.promisePublished hid mid = Σ S.HandlerStart (λ h →
  lookup w (S.handlers s) ≡ just h ×
  lookup (S.handlerPromise h) (S.handshakeResults s) ≡ just (S.negotiated hid (U.flow f)))
Allocated : U.Frame → IG.Runtime → Set
Allocated f ig with U.progress f
... | U.returnedSuccess = ⊤
... | U.handleAllocated hid mid = Chain.Anchor (U.captured f) (U.bundle f) (U.flow f) hid mid ig
... | U.promisePublished hid mid = Chain.Anchor (U.captured f) (U.bundle f) (U.flow f) hid mid ig
record Content (w : WorkerId) (f : U.Frame) (c : O.Configuration) : Set where
 constructor content
 field allocation : Allocated f (Machine.inboundGovernor (O.core c))
       publication : Published w f (Machine.world (O.core c))
open Content public

-- All traversal rows are covered, including the rows scanned by findOwner.
Covers : Store WorkerId U.Frame → O.Configuration → Set
Covers rows c = All (λ { (w , f) → Content w f c }) rows
at : ∀ rows c → Covers rows c → ∀ w f → lookup w rows ≡ just f → Content w f c
at [] c [] w f ()
at ((q , first) ∷ rows) c (good ∷ rest) w f found with w ≟ q
... | yes refl = case just-injective found of λ { refl → good }
... | no _ = at rows c rest w f found
insert : ∀ w f rows c → Content w f c → Covers rows c → Covers (put w f rows) c
insert w f [] c good [] = good ∷ []
insert w f ((q , old) ∷ rows) c good (oldGood ∷ rest) with w ≟ q
... | yes refl = good ∷ rest
... | no _ = oldGood ∷ insert w f rows c good rest

-- A fixed frame is an ordinary observer of the source stores and IG tables.
module Fixed (w : WorkerId) (f : U.Frame) where
 Predicate : S.State → IG.Runtime → Set
 Predicate s ig = Allocated f ig × Published w f s
 stable : ∀ {s s′ ig ig′} → State.Retains s s′ → Tables.Retains ig ig′ → Predicate s ig → Predicate s′ ig′
 stable state tables (a , p) with U.progress f
 ... | U.returnedSuccess = tt , tt
 ... | U.handleAllocated hid mid = Chain.anchor-retained tables a , tt
 ... | U.promisePublished hid mid = Chain.anchor-retained tables a ,
   proj₁ p , State.handlersRetained state w (proj₁ p) (proj₁ (proj₂ p)) ,
   State.resultsRetained state _ _ (proj₂ (proj₂ p))
 open World.Lift Predicate stable public using (advance-preserves; exec-preserves)
 to : ∀ c → Content w f c → Predicate (Machine.world (O.core c)) (Machine.inboundGovernor (O.core c))
 to c good = allocation good , publication good
 from : ∀ c → Predicate (Machine.world (O.core c)) (Machine.inboundGovernor (O.core c)) → Content w f c
 from c (a , p) = content a p
advance : ∀ a c {d} → O.advance a c ≡ just d → ∀ w f → Content w f c → Content w f d
advance a c {d} actual w f good = Fixed.from w f d (Fixed.advance-preserves w f a c actual (Fixed.to w f c good))
execute : ∀ {c as d} → O.Executes c as d → ∀ w f → Content w f c → Content w f d
execute {c} {d = d} path w f good = Fixed.from w f d (Fixed.exec-preserves w f (Fixed.to w f c good) path)
transport : ∀ rows {c as d} → O.Executes c as d → Covers rows c → Covers rows d
transport [] path [] = []
transport ((w , f) ∷ rows) path (good ∷ rest) = execute path w f good ∷ transport rows path rest

-- Mutable startup/pool and setup replacement preserve all negotiated content.
startup-content : ∀ w f startup c → Content w f c → Content w (record f { startup = startup }) c
startup-content w (U.frame h origin ps flow progress old setup) startup c (content a p) with progress
... | U.returnedSuccess = content tt tt
... | U.handleAllocated hid mid = content a tt
... | U.promisePublished hid mid = content a p
setup-content : ∀ w f setup c → Content w f c → Content w (record f { setup = setup }) c
setup-content w (U.frame h origin ps flow progress startup old) setup c (content a p) with progress
... | U.returnedSuccess = content tt tt
... | U.handleAllocated hid mid = content a tt
... | U.promisePublished hid mid = content a p

-- Publication exposes the actual shared registration selected by its source
-- writer. No agreement with a hypothetical unrelated capture is assumed here.
publication-handler : ∀ w result c {d} →
 O.advance (O.inbound (Machine.handlerPublication w result Machine.resultWritten)) c ≡ just d →
 Σ S.HandlerStart (λ h → lookup w (S.handlers (Machine.world (O.core c))) ≡ just h)
publication-handler w result c eq with Machine.advance (Machine.handlerPublication w result Machine.resultWritten) (O.core c) in actual
... | nothing = case eq of λ ()
... | just core with Data.Bool.ListAction.any (λ v → does (v ≟ w)) (Machine.publicationFaults (O.core c))
...   | true = case actual of λ ()
...   | false with lookup w (S.handlers (Machine.world (O.core c))) in found | lookup w (S.cleanups (Machine.world (O.core c)))
...     | nothing | _ = case actual of λ ()
...     | just h | just _ = case actual of λ ()
...     | just h | nothing = h , refl

publication-writer : ∀ w result c {d} →
 O.advance (O.inbound (Machine.handlerPublication w result Machine.resultWritten)) c ≡ just d →
 Σ S.HandlerStart (λ h → lookup w (S.handlers (Machine.world (O.core d))) ≡ just h ×
 lookup (S.handlerPromise h) (S.handshakeResults (Machine.world (O.core d))) ≡ just result)
publication-writer w result c eq with publication-handler w result c eq
... | h , found = h , registered , Chain.outbound-publication-result w h result c found eq
 where
 module Registration = World.Lift
   (λ s ig → lookup w (S.handlers s) ≡ just h)
   (λ state tables → State.handlersRetained state w h)
 registered = Registration.advance-preserves
   (O.inbound (Machine.handlerPublication w result Machine.resultWritten)) c eq found

-- Convert the content record back to the unchanged round-three target.
as-chain : ∀ w f c → Content w f c → Chain.AllocationAt f c
as-chain w (U.frame h origin ps flow U.returnedSuccess startup setup) c good = tt
as-chain w (U.frame h origin ps flow (U.handleAllocated hid mid) startup setup) c good = allocation good
as-chain w (U.frame h origin ps flow (U.promisePublished hid mid) startup setup) c good = allocation good

-- Only the progress and startup fields change at successful publication.
published-content : ∀ w f hid mid next c → U.progress f ≡ U.handleAllocated hid mid →
 Content w f c →
 (Σ S.HandlerStart (λ h → lookup w (S.handlers (Machine.world (O.core c))) ≡ just h ×
 lookup (S.handlerPromise h) (S.handshakeResults (Machine.world (O.core c))) ≡ just (S.negotiated hid (U.flow f)))) →
 Content w (record f { progress = U.promisePublished hid mid; startup = next }) c
published-content w (U.frame h origin ps flow .(U.handleAllocated hid mid) startup setup) hid mid next c refl (content a p) result = content a result

-- Direct frontend bookkeeping may replace unrelated world fields. These are
-- the only three stores read by negotiated content.
same-stores : ∀ w f c d →
 Machine.inboundGovernor (O.core d) ≡ Machine.inboundGovernor (O.core c) →
 S.handlers (Machine.world (O.core d)) ≡ S.handlers (Machine.world (O.core c)) →
 S.handshakeResults (Machine.world (O.core d)) ≡ S.handshakeResults (Machine.world (O.core c)) →
 Content w f c → Content w f d
same-stores w (U.frame h origin ps flow progress startup setup) c d tables handlers results (content a p)
 with progress
... | U.returnedSuccess = content tt tt
... | U.handleAllocated hid mid = content (subst (Chain.Anchor h ps flow hid mid) (sym tables) a) tt
... | U.promisePublished hid mid = content (subst (Chain.Anchor h ps flow hid mid) (sym tables) a)
 (proj₁ p , trans (cong (lookup w) handlers) (proj₁ (proj₂ p)) ,
   trans (cong (lookup (S.handlerPromise (proj₁ p))) results) (proj₂ (proj₂ p)))
reframe : ∀ rows c d →
 Machine.inboundGovernor (O.core d) ≡ Machine.inboundGovernor (O.core c) →
 S.handlers (Machine.world (O.core d)) ≡ S.handlers (Machine.world (O.core c)) →
 S.handshakeResults (Machine.world (O.core d)) ≡ S.handshakeResults (Machine.world (O.core c)) →
 Covers rows c → Covers rows d
reframe [] c d tables handlers results [] = []
reframe ((w , f) ∷ rows) c d tables handlers results (good ∷ rest) =
 same-stores w f c d tables handlers results good ∷ reframe rows c d tables handlers results rest
