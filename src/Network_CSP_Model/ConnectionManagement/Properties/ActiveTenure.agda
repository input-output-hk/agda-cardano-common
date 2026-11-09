{-# OPTIONS --guardedness #-}

-- M4b: the governor's activeSince keys are exactly its activePeers (network
-- 2f1c154 Governor/Types.hs assertPeerSelectionState), preserved by every
-- governor-state transition. Promotion records its time; every demotion path
-- (job success, job failure, monitor) drops it. Peer sharing and local roots
-- are outside the selected ordinary-peer OG profile.
module ConnectionManagement.Properties.ActiveTenure where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Bool.Properties using (∧-zeroʳ; ∧-identityʳ; ∨-comm)
open import Data.Nat using (ℕ; _≤?_)
open import Data.List using (List; []; _∷_; _++_; length; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put; delete)
open import ConnectionManagement.Properties.Stores using (UniqueKeys; put-unique; delete-unique; apart-lookup; lookup-put-other)
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.PeerActions as P

present : ∀ {V : Set} → Maybe V → Bool
present (just _) = true
present nothing = false
same : PeerAddr → PeerAddr → Bool
same q p = does (q ≟ p)

-- Stated over the two fields so other record updates convert definitionally.
record TenureOf (A : List PeerAddr) (T : Store PeerAddr ℕ) : Set where
  constructor tenure
  field exact : ∀ q → G.member q A ≡ present (lookup q T)
        unique : UniqueKeys T
open TenureOf public
Tenure : G.State → Set
Tenure s = TenureOf (G.activePeers s) (G.activeSince s)

-- Membership through the governor's list operations.
member-++ : ∀ q xs ys → G.member q (xs ++ ys) ≡ G.member q xs ∨ G.member q ys
member-++ q [] ys = refl
member-++ q (x ∷ xs) ys with q ≟ x
... | yes _ = refl
... | no _ = member-++ q xs ys
member-filter : ∀ (f : PeerAddr → Bool) q xs → G.member q (filterᵇ f xs) ≡ G.member q xs ∧ f q
member-filter f q [] = refl
member-filter f q (x ∷ xs) with f x in fx
... | true with q ≟ x
...   | yes refl = sym fx
...   | no _ = member-filter f q xs
member-filter f q (x ∷ xs) | false with q ≟ x
... | yes refl = trans (member-filter f q xs) (trans (cong (G.member q xs ∧_) fx) (trans (∧-zeroʳ _) (sym fx)))
... | no _ = member-filter f q xs
member-single : ∀ q p → G.member q (p ∷ []) ≡ same q p
member-single q p with q ≟ p
... | yes _ = refl
... | no _ = refl
remove-member : ∀ p q xs → G.member q (G.remove p xs) ≡ G.member q xs ∧ not (same q p)
remove-member p q xs = trans (member-filter (λ r → not (G.member r (p ∷ []))) q xs)
  (cong (λ b → G.member q xs ∧ not b) (member-single q p))
absorb : ∀ a b → a ∨ (b ∧ not a) ≡ a ∨ b
absorb true b = refl
absorb false b = ∧-identityʳ b
union-member : ∀ q xs p → G.member q (G.union xs (p ∷ [])) ≡ G.member q xs ∨ same q p
union-member q xs p = trans (member-++ q xs _) (trans (cong (G.member q xs ∨_)
  (trans (member-filter (λ r → not (G.member r xs)) q (p ∷ [])) (cong (_∧ not (G.member q xs)) (member-single q p))))
  (absorb (G.member q xs) (same q p)))

-- Presence through store writes; deletion needs unique keys.
lookup-put-same : ∀ q (v : ℕ) (T : Store PeerAddr ℕ) → lookup q (put q v T) ≡ just v
lookup-put-same q v [] with q ≟ q
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)
lookup-put-same q v ((k , w) ∷ T) with q ≟ k
... | yes refl with q ≟ q
...   | yes _ = refl
...   | no neq = ⊥-elim (neq refl)
lookup-put-same q v ((k , w) ∷ T) | no neq with q ≟ k
... | yes eq = ⊥-elim (neq eq)
... | no _ = lookup-put-same q v T
put-present : ∀ q p (v : ℕ) T → present (lookup q (put p v T)) ≡ same q p ∨ present (lookup q T)
put-present q p v T with q ≟ p
... | yes refl = cong present (lookup-put-same q v T)
... | no neq = cong present (lookup-put-other p q v T neq)
delete-same : ∀ p (T : Store PeerAddr ℕ) → UniqueKeys T → lookup p (delete p T) ≡ nothing
delete-same p [] _ = refl
delete-same p ((k , w) ∷ T) (apart ∷ unique) with p ≟ k
... | yes refl = apart-lookup p T apart
... | no neq with p ≟ k
...   | yes eq = ⊥-elim (neq eq)
...   | no _ = delete-same p T unique
delete-other : ∀ q p (T : Store PeerAddr ℕ) → q ≢ p → lookup q (delete p T) ≡ lookup q T
delete-other q p [] neq = refl
delete-other q p ((k , w) ∷ T) neq with p ≟ k
... | yes refl with q ≟ p
...   | yes eq = ⊥-elim (neq eq)
...   | no _ = refl
delete-other q p ((k , w) ∷ T) neq | no _ with q ≟ k
... | yes _ = refl
... | no _ = delete-other q p T neq
delete-present : ∀ q p (T : Store PeerAddr ℕ) → UniqueKeys T →
  present (lookup q (delete p T)) ≡ present (lookup q T) ∧ not (same q p)
delete-present q p T u with q ≟ p
... | yes refl = trans (cong present (delete-same q T u)) (sym (∧-zeroʳ _))
... | no neq = trans (cong present (delete-other q p T neq)) (sym (∧-identityʳ _))

-- Promotion records the peer; demotion drops it.
tenure-add : ∀ p v A T → TenureOf A T → TenureOf (G.union A (p ∷ [])) (put p v T)
exact (tenure-add p v A T t) q = trans (union-member q A p)
  (trans (cong (_∨ same q p) (exact t q)) (trans (∨-comm (present (lookup q T)) (same q p)) (sym (put-present q p v T))))
unique (tenure-add p v A T t) = put-unique p v T (unique t)
tenure-drop : ∀ p A T → TenureOf A T → TenureOf (G.remove p A) (delete p T)
exact (tenure-drop p A T t) q = trans (remove-member p q A)
  (trans (cong (_∧ not (same q p)) (exact t q)) (sym (delete-present q p T (unique t))))
unique (tenure-drop p A T t) = delete-unique p T (unique t)

tenure-empty : TenureOf [] []
tenure-empty = tenure (λ q → refl) []

-- Every governor-state transition.
tenure-mark : ∀ k ps s → Tenure s → Tenure (G.mark k ps s)
tenure-mark G.forget ps s t = t
tenure-mark G.establish ps s t = t
tenure-mark G.activate ps s t = t
tenure-mark G.close ps s t = t
tenure-mark G.deactivate ps s t = t
tenure-choose : ∀ time picked s {d} → G.choose time picked s ≡ just d → Tenure s → Tenure (G.nextState d)
tenure-choose time [] s ()
tenure-choose time picked@(_ ∷ _) s eq t with G.firstReady time s
... | nothing = case eq of λ ()
... | just kind with G.validPick picked (G.eligible time kind s) ∧ does (length picked ≤? G.quota kind s)
...   | false = case eq of λ ()
...   | true = case just-injective eq of λ { refl → tenure-mark kind picked s t }
tenure-advanceTime : ∀ time s → Tenure s → Tenure (G.advanceTime time s)
tenure-advanceTime time s t = t
tenure-complete : ∀ mr cd now c s → Tenure s → Tenure (G.complete mr cd now c s)
tenure-complete mr cd now c s t with G.kind (G.work c) | G.outcome c
... | G.forget | _ = t
... | G.establish | G.establishedOK ref = t
... | G.establish | G.succeeded = t
... | G.establish | G.failed = t
... | G.establish | G.demotionTimedOut = t
... | G.activate | G.succeeded with lookup (G.peer (G.work c)) (G.establishedPeers s)
...   | nothing = t
...   | just _ = tenure-add (G.peer (G.work c)) now (G.activePeers s) (G.activeSince s) t
tenure-complete mr cd now c s t | G.activate | G.establishedOK ref with G.member (G.peer (G.work c)) (G.promotingWarm s)
... | false = t
... | true = t
tenure-complete mr cd now c s t | G.activate | G.failed with G.member (G.peer (G.work c)) (G.promotingWarm s)
... | false = t
... | true = t
tenure-complete mr cd now c s t | G.activate | G.demotionTimedOut with G.member (G.peer (G.work c)) (G.promotingWarm s)
... | false = t
... | true = t
tenure-complete mr cd now c s t | G.close | G.demotionTimedOut = t
tenure-complete mr cd now c s t | G.close | G.establishedOK ref = t
tenure-complete mr cd now c s t | G.close | G.succeeded = t
tenure-complete mr cd now c s t | G.close | G.failed = t
tenure-complete mr cd now c s t | G.deactivate | G.demotionTimedOut = t
tenure-complete mr cd now c s t | G.deactivate | G.succeeded =
  tenure-drop (G.peer (G.work c)) (G.activePeers s) (G.activeSince s) t
tenure-complete mr cd now c s t | G.deactivate | G.establishedOK ref =
  tenure-drop (G.peer (G.work c)) (G.activePeers s) (G.activeSince s) t
tenure-complete mr cd now c s t | G.deactivate | G.failed =
  tenure-drop (G.peer (G.work c)) (G.activePeers s) (G.activeSince s) t
tenure-monitor : ∀ mr now delay changes s → Tenure s → Tenure (G.applyMonitor mr now delay changes s)
tenure-monitor mr now delay [] s t = t
tenure-monitor mr now delay ((p , P.peerHot) ∷ rest) s t = tenure-monitor mr now delay rest s t
tenure-monitor mr now delay ((p , P.peerWarm) ∷ rest) s t with lookup p (G.establishedPeers s)
... | nothing = tenure-monitor mr now delay rest _ (tenure-drop p (G.activePeers s) (G.activeSince s) t)
... | just e = tenure-monitor mr now delay rest _ (tenure-drop p (G.activePeers s) (G.activeSince s) t)
tenure-monitor mr now delay ((p , P.peerCooling) ∷ rest) s t =
  tenure-monitor mr now delay rest _ (tenure-drop p (G.activePeers s) (G.activeSince s) t)
tenure-monitor mr now delay ((p , P.peerCold) ∷ rest) s t =
  tenure-monitor mr now delay rest _ (tenure-drop p (G.activePeers s) (G.activeSince s) t)
tenure-delays : ∀ mr now delays changes s → Tenure s → Tenure (G.applyMonitorDelays mr now delays changes s)
tenure-delays mr now delays [] s t = t
tenure-delays mr now delays ((p , st) ∷ rest) s t with lookup p delays
... | nothing = t
... | just delay = tenure-delays mr now delays rest _ (tenure-monitor mr now delay ((p , st) ∷ []) s t)

-- The coordinator: the private state, the published state and a decision
-- parked in the continuation all keep tenure, across every enabled step.
module Coordinator where
  open import Data.Bool using (true; false)
  open import Data.Nat using (ℕ; suc; _≤?_)
  open import Data.List using (List; []; _∷_; _++_)
  open import Data.Bool.ListAction using (any)
  open import Data.Maybe using (just; nothing)
  open import Data.Product using (_,_; proj₁; proj₂)
  open import Data.Unit using (⊤; tt)
  open import Relation.Nullary using (yes; no; does)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
  open import Class.DecEq using (_≟_)
  open import ConnectionManagement.Domain hiding (job)
  open import ConnectionManagement.IGTypes using (clean; errored)
  open import ConnectionManagement.Store using (lookup)
  import ConnectionManagement.Subsystem as Sub
  open Sub
  import ConnectionManagement.Rules.PeerJobs as J
  import ConnectionManagement.OutboundMachine as CM
  import ConnectionManagement.Machine as Inbound
  import ConnectionManagement.Rules.IGRegistration as IG
  import ConnectionManagement.Rules.MuxRuntime as M
  import ConnectionManagement.Rules.HandlerLifecycle as Life

  selTenure : Selected → Set
  selTenure (policy d) = Tenure (G.nextState d)
  selTenure _ = ⊤
  pcTenure : PC → Set
  pcTenure (cancelTimer x) = selTenure x
  pcTenure (apply x) = selTenure x
  pcTenure _ = ⊤
  TenureC : Configuration → Set
  TenureC c = Tenure (privateState c) × Tenure (publicState c) × pcTenure (pc c)
  selection : ∀ c x → selTenure x → pcTenure (selectionPC c x)
  selection c x r with wakeupAt c
  ... | nothing = r
  ... | just _ = r
  initial-tenure : ∀ cm s → Tenure s → TenureC (initial cm s)
  initial-tenure cm s t = t , t , tt

  tenure-step : ∀ a c {d} → TenureC c → advance a c ≡ just d → TenureC d
  tenure-step (core action) c inv with CM.advance action (J.cm (world c)) in stepped
  ... | nothing = λ ()
  ... | just cm′ = λ { refl → inv }
  tenure-step publishPublicState c inv with pc c
  ... | publishPublic = λ { refl → proj₁ inv , proj₁ inv , tt }
  tenure-step publishPublicState c inv | sampleInputs = λ ()
  tenure-step publishPublicState c inv | prepareWait = λ ()
  tenure-step publishPublicState c inv | selecting = λ ()
  tenure-step publishPublicState c inv | (cancelTimer selected) = λ ()
  tenure-step publishPublicState c inv | (apply selected) = λ ()
  tenure-step publishPublicState c inv | (publishView work) = λ ()
  tenure-step publishPublicState c inv | (traceDecision work) = λ ()
  tenure-step publishPublicState c inv | (launch work) = λ ()
  tenure-step publishPublicState c inv | (register j rest) = λ ()
  tenure-step publishPublicState c inv | (completionAssertionFailed result) = λ ()
  tenure-step (sampleTime t) c inv with pc c | now c ≤? t
  ... | sampleInputs | yes _ = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , tt }
  ... | sampleInputs | no _ = λ ()
  tenure-step (sampleTime t) c inv | publishPublic | _ = λ ()
  tenure-step (sampleTime t) c inv | prepareWait | _ = λ ()
  tenure-step (sampleTime t) c inv | selecting | _ = λ ()
  tenure-step (sampleTime t) c inv | (cancelTimer selected) | _ = λ ()
  tenure-step (sampleTime t) c inv | (apply selected) | _ = λ ()
  tenure-step (sampleTime t) c inv | (publishView work) | _ = λ ()
  tenure-step (sampleTime t) c inv | (traceDecision work) | _ = λ ()
  tenure-step (sampleTime t) c inv | (launch work) | _ = λ ()
  tenure-step (sampleTime t) c inv | (register j rest) | _ = λ ()
  tenure-step (sampleTime t) c inv | (completionAssertionFailed result) | _ = λ ()
  -- Raw target-input writes do not alter the completion FIFO.
  tenure-step (setTargets t) c inv = λ { refl → inv }
  tenure-step (selectMonitor delay) c inv with pc c | G.monitored (J.peers (world c)) (privateState c)
  ... | selecting | changes@(_ ∷ _) with completeDelays changes delay
  ...   | false = λ ()
  ...   | true = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , selection c (monitor changes delay) tt }
  tenure-step (selectMonitor delay) c inv | selecting | [] = λ ()
  tenure-step (selectMonitor delay) c inv | publishPublic | _ = λ ()
  tenure-step (selectMonitor delay) c inv | sampleInputs | _ = λ ()
  tenure-step (selectMonitor delay) c inv | prepareWait | _ = λ ()
  tenure-step (selectMonitor delay) c inv | (cancelTimer selected) | _ = λ ()
  tenure-step (selectMonitor delay) c inv | (apply selected) | _ = λ ()
  tenure-step (selectMonitor delay) c inv | (publishView work) | _ = λ ()
  tenure-step (selectMonitor delay) c inv | (traceDecision work) | _ = λ ()
  tenure-step (selectMonitor delay) c inv | (launch work) | _ = λ ()
  tenure-step (selectMonitor delay) c inv | (register j rest) | _ = λ ()
  tenure-step (selectMonitor delay) c inv | (completionAssertionFailed result) | _ = λ ()
  tenure-step selectCompletion c inv with pc c | noMonitor c | completions c in fifo
  ... | selecting | true | x ∷ xs = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , selection c (completion x) tt }
  ... | selecting | true | [] = λ ()
  ... | selecting | false | _ = λ ()
  tenure-step selectCompletion c inv | publishPublic | _ | _ = λ ()
  tenure-step selectCompletion c inv | sampleInputs | _ | _ = λ ()
  tenure-step selectCompletion c inv | prepareWait | _ | _ = λ ()
  tenure-step selectCompletion c inv | (cancelTimer selected) | _ | _ = λ ()
  tenure-step selectCompletion c inv | (apply selected) | _ | _ = λ ()
  tenure-step selectCompletion c inv | (publishView work) | _ | _ = λ ()
  tenure-step selectCompletion c inv | (traceDecision work) | _ | _ = λ ()
  tenure-step selectCompletion c inv | (launch work) | _ | _ = λ ()
  tenure-step selectCompletion c inv | (register j rest) | _ | _ = λ ()
  tenure-step selectCompletion c inv | (completionAssertionFailed result) | _ | _ = λ ()
  tenure-step selectTargets c inv with pc c | noMonitor c | noCompletions c | noTargets c
  ... | selecting | true | true | false = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , selection c (targets (targetInput c)) tt }
  tenure-step selectTargets c inv | selecting | true | true | true = λ ()
  tenure-step selectTargets c inv | selecting | true | false | true = λ ()
  tenure-step selectTargets c inv | selecting | true | false | false = λ ()
  tenure-step selectTargets c inv | selecting | false | true | true = λ ()
  tenure-step selectTargets c inv | selecting | false | true | false = λ ()
  tenure-step selectTargets c inv | selecting | false | false | true = λ ()
  tenure-step selectTargets c inv | selecting | false | false | false = λ ()
  tenure-step selectTargets c inv | publishPublic | _ | _ | _ = λ ()
  tenure-step selectTargets c inv | sampleInputs | _ | _ | _ = λ ()
  tenure-step selectTargets c inv | prepareWait | _ | _ | _ = λ ()
  tenure-step selectTargets c inv | (cancelTimer selected) | _ | _ | _ = λ ()
  tenure-step selectTargets c inv | (apply selected) | _ | _ | _ = λ ()
  tenure-step selectTargets c inv | (publishView work) | _ | _ | _ = λ ()
  tenure-step selectTargets c inv | (traceDecision work) | _ | _ | _ = λ ()
  tenure-step selectTargets c inv | (launch work) | _ | _ | _ = λ ()
  tenure-step selectTargets c inv | (register j rest) | _ | _ | _ = λ ()
  tenure-step selectTargets c inv | (completionAssertionFailed result) | _ | _ | _ = λ ()
  tenure-step (selectPolicy picked) c inv with pc c | noMonitor c | noCompletions c | noTargets c
  ... | selecting | true | true | true with G.choose (now c) picked (privateState c) in chosen
  ...   | nothing = λ ()
  ...   | just d = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , selection c (policy d) (tenure-choose (now c) picked (privateState c) chosen (proj₁ inv)) }
  tenure-step (selectPolicy picked) c inv | selecting | true | true | false = λ ()
  tenure-step (selectPolicy picked) c inv | selecting | true | false | true = λ ()
  tenure-step (selectPolicy picked) c inv | selecting | true | false | false = λ ()
  tenure-step (selectPolicy picked) c inv | selecting | false | true | true = λ ()
  tenure-step (selectPolicy picked) c inv | selecting | false | true | false = λ ()
  tenure-step (selectPolicy picked) c inv | selecting | false | false | true = λ ()
  tenure-step (selectPolicy picked) c inv | selecting | false | false | false = λ ()
  tenure-step (selectPolicy picked) c inv | publishPublic | _ | _ | _ = λ ()
  tenure-step (selectPolicy picked) c inv | sampleInputs | _ | _ | _ = λ ()
  tenure-step (selectPolicy picked) c inv | prepareWait | _ | _ | _ = λ ()
  tenure-step (selectPolicy picked) c inv | (cancelTimer selected) | _ | _ | _ = λ ()
  tenure-step (selectPolicy picked) c inv | (apply selected) | _ | _ | _ = λ ()
  tenure-step (selectPolicy picked) c inv | (publishView work) | _ | _ | _ = λ ()
  tenure-step (selectPolicy picked) c inv | (traceDecision work) | _ | _ | _ = λ ()
  tenure-step (selectPolicy picked) c inv | (launch work) | _ | _ | _ = λ ()
  tenure-step (selectPolicy picked) c inv | (register j rest) | _ | _ | _ = λ ()
  tenure-step (selectPolicy picked) c inv | (completionAssertionFailed result) | _ | _ | _ = λ ()
  tenure-step registerWakeup c inv with pc c
  ... | prepareWait = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , tt }
  tenure-step registerWakeup c inv | publishPublic = λ ()
  tenure-step registerWakeup c inv | sampleInputs = λ ()
  tenure-step registerWakeup c inv | selecting = λ ()
  tenure-step registerWakeup c inv | (cancelTimer selected) = λ ()
  tenure-step registerWakeup c inv | (apply selected) = λ ()
  tenure-step registerWakeup c inv | (publishView work) = λ ()
  tenure-step registerWakeup c inv | (traceDecision work) = λ ()
  tenure-step registerWakeup c inv | (launch work) = λ ()
  tenure-step registerWakeup c inv | (register j rest) = λ ()
  tenure-step registerWakeup c inv | (completionAssertionFailed result) = λ ()
  tenure-step expireWakeup c inv with pc c in pcEq | wakeupAt c | wakeupReady c
  ... | selecting | just _ | false = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , subst pcTenure (sym pcEq) tt }
  ... | selecting | just _ | true = λ ()
  ... | selecting | nothing | _ = λ ()
  tenure-step expireWakeup c inv | publishPublic | _ | _ = λ ()
  tenure-step expireWakeup c inv | sampleInputs | _ | _ = λ ()
  tenure-step expireWakeup c inv | prepareWait | _ | _ = λ ()
  tenure-step expireWakeup c inv | (cancelTimer selected) | _ | _ = λ ()
  tenure-step expireWakeup c inv | (apply selected) | _ | _ = λ ()
  tenure-step expireWakeup c inv | (publishView work) | _ | _ = λ ()
  tenure-step expireWakeup c inv | (traceDecision work) | _ | _ = λ ()
  tenure-step expireWakeup c inv | (launch work) | _ | _ = λ ()
  tenure-step expireWakeup c inv | (register j rest) | _ | _ = λ ()
  tenure-step expireWakeup c inv | (completionAssertionFailed result) | _ | _ = λ ()
  tenure-step cancelWakeup c inv with pc c
  ... | cancelTimer selected = λ { refl → inv }
  tenure-step cancelWakeup c inv | publishPublic = λ ()
  tenure-step cancelWakeup c inv | sampleInputs = λ ()
  tenure-step cancelWakeup c inv | prepareWait = λ ()
  tenure-step cancelWakeup c inv | selecting = λ ()
  tenure-step cancelWakeup c inv | (apply selected) = λ ()
  tenure-step cancelWakeup c inv | (publishView work) = λ ()
  tenure-step cancelWakeup c inv | (traceDecision work) = λ ()
  tenure-step cancelWakeup c inv | (launch work) = λ ()
  tenure-step cancelWakeup c inv | (register j rest) = λ ()
  tenure-step cancelWakeup c inv | (completionAssertionFailed result) = λ ()
  tenure-step selectWakeup c inv with pc c | noMonitor c | noCompletions c | noTargets c | wakeupReady c | wakeupAt c | G.firstReady (now c) (privateState c)
  ... | selecting | true | true | true | true | just deadline | nothing = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , selection c (wakeup deadline) tt }
  ... | selecting | false | _ | _ | _ | _ | _ = λ ()
  ... | selecting | true | false | _ | _ | _ | _ = λ ()
  ... | selecting | true | true | false | _ | _ | _ = λ ()
  ... | selecting | true | true | true | false | _ | _ = λ ()
  ... | selecting | true | true | true | true | nothing | _ = λ ()
  ... | selecting | true | true | true | true | just deadline | just ready = λ ()
  tenure-step selectWakeup c inv | publishPublic | _ | _ | _ | _ | _ | _ = λ ()
  tenure-step selectWakeup c inv | sampleInputs | _ | _ | _ | _ | _ | _ = λ ()
  tenure-step selectWakeup c inv | prepareWait | _ | _ | _ | _ | _ | _ = λ ()
  tenure-step selectWakeup c inv | (cancelTimer selected) | _ | _ | _ | _ | _ | _ = λ ()
  tenure-step selectWakeup c inv | (apply selected) | _ | _ | _ | _ | _ | _ = λ ()
  tenure-step selectWakeup c inv | (publishView work) | _ | _ | _ | _ | _ | _ = λ ()
  tenure-step selectWakeup c inv | (traceDecision work) | _ | _ | _ | _ | _ | _ = λ ()
  tenure-step selectWakeup c inv | (launch work) | _ | _ | _ | _ | _ | _ = λ ()
  tenure-step selectWakeup c inv | (register j rest) | _ | _ | _ | _ | _ | _ = λ ()
  tenure-step selectWakeup c inv | (completionAssertionFailed result) | _ | _ | _ | _ | _ | _ = λ ()
  tenure-step (applyAt t) c inv with pc c | now c ≤? t
  ... | apply (policy d) | yes _ = λ { refl → proj₂ (proj₂ inv) , proj₁ (proj₂ inv) , tt }
  ... | apply (completion result) | yes _ with G.completionAssertion result (privateState c)
  ...   | false = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , tt }
  ...   | true = λ { refl → tenure-complete (maxRetries c) (clearFailDelay c) t result (privateState c) (proj₁ inv) , proj₁ (proj₂ inv) , tt }
  tenure-step (applyAt t) c inv | apply (monitor changes delay) | yes _ = λ { refl → tenure-delays (maxRetries c) t delay changes (privateState c) (proj₁ inv) , proj₁ (proj₂ inv) , tt }
  tenure-step (applyAt t) c inv | apply (targets t′) | yes _ = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , tt }
  tenure-step (applyAt t) c inv | apply (wakeup deadline) | yes _ with deadline ≤? t
  ...   | yes _ = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , tt }
  ...   | no _ = λ ()
  tenure-step (applyAt t) c inv | apply (policy d) | no _ = λ ()
  tenure-step (applyAt t) c inv | apply (completion result) | no _ = λ ()
  tenure-step (applyAt t) c inv | apply (monitor changes delay) | no _ = λ ()
  tenure-step (applyAt t) c inv | apply (targets t′) | no _ = λ ()
  tenure-step (applyAt t) c inv | apply (wakeup deadline) | no _ = λ ()
  tenure-step (applyAt t) c inv | publishPublic | _ = λ ()
  tenure-step (applyAt t) c inv | sampleInputs | _ = λ ()
  tenure-step (applyAt t) c inv | prepareWait | _ = λ ()
  tenure-step (applyAt t) c inv | selecting | _ = λ ()
  tenure-step (applyAt t) c inv | (cancelTimer selected) | _ = λ ()
  tenure-step (applyAt t) c inv | (publishView work) | _ = λ ()
  tenure-step (applyAt t) c inv | (traceDecision work) | _ = λ ()
  tenure-step (applyAt t) c inv | (launch work) | _ = λ ()
  tenure-step (applyAt t) c inv | (register j rest) | _ = λ ()
  tenure-step (applyAt t) c inv | (completionAssertionFailed result) | _ = λ ()
  tenure-step publishCounters c inv with pc c
  ... | publishView work = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , tt }
  tenure-step publishCounters c inv | publishPublic = λ ()
  tenure-step publishCounters c inv | sampleInputs = λ ()
  tenure-step publishCounters c inv | prepareWait = λ ()
  tenure-step publishCounters c inv | selecting = λ ()
  tenure-step publishCounters c inv | (cancelTimer selected) = λ ()
  tenure-step publishCounters c inv | (apply selected) = λ ()
  tenure-step publishCounters c inv | (traceDecision work) = λ ()
  tenure-step publishCounters c inv | (launch work) = λ ()
  tenure-step publishCounters c inv | (register j rest) = λ ()
  tenure-step publishCounters c inv | (completionAssertionFailed result) = λ ()
  tenure-step traceSelection c inv with pc c
  ... | traceDecision work = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , tt }
  tenure-step traceSelection c inv | publishPublic = λ ()
  tenure-step traceSelection c inv | sampleInputs = λ ()
  tenure-step traceSelection c inv | prepareWait = λ ()
  tenure-step traceSelection c inv | selecting = λ ()
  tenure-step traceSelection c inv | (cancelTimer selected) = λ ()
  tenure-step traceSelection c inv | (apply selected) = λ ()
  tenure-step traceSelection c inv | (publishView work) = λ ()
  tenure-step traceSelection c inv | (launch work) = λ ()
  tenure-step traceSelection c inv | (register j rest) = λ ()
  tenure-step traceSelection c inv | (completionAssertionFailed result) = λ ()
  tenure-step registerJob c inv with pc c
  ... | register j rest = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , tt }
  tenure-step registerJob c inv | publishPublic = λ ()
  tenure-step registerJob c inv | sampleInputs = λ ()
  tenure-step registerJob c inv | prepareWait = λ ()
  tenure-step registerJob c inv | selecting = λ ()
  tenure-step registerJob c inv | (cancelTimer selected) = λ ()
  tenure-step registerJob c inv | (apply selected) = λ ()
  tenure-step registerJob c inv | (publishView work) = λ ()
  tenure-step registerJob c inv | (traceDecision work) = λ ()
  tenure-step registerJob c inv | (launch work) = λ ()
  tenure-step registerJob c inv | (completionAssertionFailed result) = λ ()
  tenure-step (forkJob caller child sock) c inv with pc c | workerFree caller c
  ... | launch [] | _ = λ ()
  ... | launch (work ∷ rest) | true = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , tt }
  ... | launch (work ∷ rest) | false = λ ()
  tenure-step (forkJob caller child sock) c inv | publishPublic | _ = λ ()
  tenure-step (forkJob caller child sock) c inv | sampleInputs | _ = λ ()
  tenure-step (forkJob caller child sock) c inv | prepareWait | _ = λ ()
  tenure-step (forkJob caller child sock) c inv | selecting | _ = λ ()
  tenure-step (forkJob caller child sock) c inv | (cancelTimer selected) | _ = λ ()
  tenure-step (forkJob caller child sock) c inv | (apply selected) | _ = λ ()
  tenure-step (forkJob caller child sock) c inv | (publishView work) | _ = λ ()
  tenure-step (forkJob caller child sock) c inv | (traceDecision work) | _ = λ ()
  tenure-step (forkJob caller child sock) c inv | (register j rest) | _ = λ ()
  tenure-step (forkJob caller child sock) c inv | (completionAssertionFailed result) | _ = λ ()
  tenure-step finishLaunch c inv with pc c
  ... | launch [] = λ { refl → proj₁ inv , proj₁ (proj₂ inv) , tt }
  ... | launch (work ∷ rest) = λ ()
  tenure-step finishLaunch c inv | publishPublic = λ ()
  tenure-step finishLaunch c inv | sampleInputs = λ ()
  tenure-step finishLaunch c inv | prepareWait = λ ()
  tenure-step finishLaunch c inv | selecting = λ ()
  tenure-step finishLaunch c inv | (cancelTimer selected) = λ ()
  tenure-step finishLaunch c inv | (apply selected) = λ ()
  tenure-step finishLaunch c inv | (publishView work) = λ ()
  tenure-step finishLaunch c inv | (traceDecision work) = λ ()
  tenure-step finishLaunch c inv | (register j rest) = λ ()
  tenure-step finishLaunch c inv | (completionAssertionFailed result) = λ ()
  tenure-step (jobStep j action) c inv with lookup j (jobs c)
  ... | nothing = λ ()
  ... | just frame with queued frame | J.step action (execution frame) (world c) in stepped
  ...   | false | just (f′ , w′) = λ { refl → inv }
  ...   | true | _ = λ ()
  ...   | false | nothing = λ ()
  tenure-step (enqueueCompletion j delay) c inv with lookup j (jobs c) in found
  ... | nothing = λ ()
  ... | just frame with queued frame | J.pc (execution frame) in completed
  ...   | false | J.complete result with validCompletionDelay (J.work (execution frame)) result delay
  ...     | false = λ ()
  ...     | true = λ { refl → inv }
  tenure-step (enqueueCompletion j delay) c inv | just frame | true | _ = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | J.begin = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | J.awaitAcquire = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | (J.startBundle t ns) = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | (J.publishBundle t) = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | J.markWarm = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | J.forkMonitor = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | J.finishActivation = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | J.awaitHot = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | J.awaitAll = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | J.callRelease = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | J.awaitRelease = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | J.delayFailure = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | (J.awaitCold result) = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | (J.acquirePolicy fault) = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | (J.nodeDelivery fault) = λ ()
  tenure-step (enqueueCompletion j delay) c inv | just frame | false | (J.nodeRethrow fault) = λ ()
  tenure-step (deregisterJob j) c inv with lookup j (jobs c)
  ... | nothing = λ ()
  ... | just frame with queued frame | deregistered frame | any (λ x → does (x ≟ j)) (pool c)
  ...   | true | true | true = λ ()
  ...   | true | true | false = λ ()
  ...   | true | false | true = λ { refl → inv }
  ...   | true | false | false = λ ()
  ...   | false | true | true = λ ()
  ...   | false | true | false = λ ()
  ...   | false | false | true = λ ()
  ...   | false | false | false = λ ()
  tenure-step (protocolResult ref n result) c inv with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with P.step (P.protocolResult n result) peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...   | nothing = λ ()
  ...   | just (peer′ , ig′) = λ { refl → inv }
  tenure-step (publishInitiatorResult ref i) c inv with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with P.takePending i (P.pendingResults peer) | lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c)))))) in observed
  ...   | just ((n , result) , retained) | just observedMux with Life.muxAllowed (P.muxRef peer) Life.jobAccess (Inbound.handlerLifecycles (CM.core (J.cm (world c))))
  ...     | false = λ ()
  ...     | true = λ { refl → inv }
  tenure-step (publishInitiatorResult ref i) c inv | just peer | nothing | _ = λ ()
  tenure-step (publishInitiatorResult ref i) c inv | just peer | just selected | nothing = λ ()
  tenure-step (observeInitiatorFailure ref) c inv with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c))))))
  ...   | nothing = λ ()
  ...   | just observedMux with M.completions observedMux
  ...     | M.jobResult M.initiatorJob n (errored err) ∷ rest with CM.advance
    (CM.inbound (Inbound.igStep (IG.monitorCompletion (P.muxRef peer)))) (J.cm (world c)) in stepped
  ...       | nothing = λ ()
  ...       | just cm′ = λ { refl → inv }
  tenure-step (observeInitiatorFailure ref) c inv | just peer | just observedMux | [] = λ ()
  tenure-step (observeInitiatorFailure ref) c inv | just peer | just observedMux | M.jobResult M.responderJob n outcome ∷ rest = λ ()
  tenure-step (observeInitiatorFailure ref) c inv | just peer | just observedMux | M.jobResult M.initiatorJob n clean ∷ rest = λ ()
  tenure-step (pollPeer ref caller) c inv with lookup ref (J.peers (world c)) | lookup ref (monitors c)
  ... | just peer | nothing with P.monitorStarted peer | P.status peer
  ...   | true | P.peerCooling with P.step P.monitorCooling peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...     | nothing = λ ()
  ...     | just (peer′ , _) = λ { refl → inv }
  tenure-step (pollPeer ref caller) c inv | just peer | nothing | true | P.peerCold = λ { refl → inv }
  tenure-step (pollPeer ref caller) c inv | just peer | nothing | true | P.peerWarm with firstResult peer
  ... | nothing = λ ()
  ... | just (_ , errored _) = λ { refl → inv }
  ... | just (kind , clean) with workerFree caller c
  ...   | false = λ ()
  ...   | true = λ { refl → inv }
  tenure-step (pollPeer ref caller) c inv | just peer | nothing | true | P.peerHot with firstResult peer
  ... | nothing = λ ()
  ... | just (_ , errored _) = λ { refl → inv }
  ... | just (kind , clean) with workerFree caller c
  ...   | false = λ ()
  ...   | true = λ { refl → inv }
  tenure-step (pollPeer ref caller) c inv | just peer | nothing | false | _ = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f with J.pc f
  ... | J.awaitCold _ with P.step P.monitorCooling peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...   | nothing = λ ()
  ...   | just (peer′ , _) = λ { refl → inv }
  tenure-step (pollPeer ref caller) c inv | just peer | just f | J.begin = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | J.awaitAcquire = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | (J.startBundle t ns) = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | (J.publishBundle t) = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | J.markWarm = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | J.forkMonitor = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | J.finishActivation = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | J.awaitHot = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | J.awaitAll = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | J.callRelease = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | J.awaitRelease = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | J.delayFailure = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | (J.complete result) = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | (J.acquirePolicy fault) = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | (J.nodeDelivery fault) = λ ()
  tenure-step (pollPeer ref caller) c inv | just peer | just f | (J.nodeRethrow fault) = λ ()
  tenure-step (pollPeer ref caller) c inv | nothing | _ = λ ()
  tenure-step (monitorStep ref action) c inv with lookup ref (monitors c)
  ... | nothing = λ ()
  ... | just f with J.step action f (world c) in stepped
  ...   | nothing = λ ()
  ...   | just (f′ , w′) = λ { refl → inv }
  tenure-step (monitorFinished ref) c inv with lookup ref (monitors c)
  ... | nothing = λ ()
  ... | just f with J.pc f
  ...   | J.complete _ = λ { refl → inv }
  ...   | J.begin = λ ()
  ...   | J.awaitAcquire = λ ()
  ...   | (J.startBundle t ns) = λ ()
  ...   | (J.publishBundle t) = λ ()
  ...   | J.markWarm = λ ()
  ...   | J.forkMonitor = λ ()
  ...   | J.finishActivation = λ ()
  ...   | J.awaitHot = λ ()
  ...   | J.awaitAll = λ ()
  ...   | J.callRelease = λ ()
  ...   | J.awaitRelease = λ ()
  ...   | J.delayFailure = λ ()
  ...   | (J.awaitCold result) = λ ()
  ...   | (J.acquirePolicy fault) = λ ()

  tenure-runs : ∀ {c as d} → Executes c as d → TenureC c → TenureC d
  tenure-runs done inv = inv
  tenure-runs (next {c = c} {a = a} eq path) inv = tenure-runs path (tenure-step a c inv eq)
