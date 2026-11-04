{-# OPTIONS --safe #-}

-- Fresh arbitrary-history and burst controls inhabit and distinguish the conditional resource premises.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CollectOne.ResourceTests where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc; +-identityʳ; ≤-refl)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Function using (_$_)
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Bool as C
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Accounting Bool as A
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Bounds Bool as B
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Safety Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Progress Bool as P
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CollectOne.ContractTests as T
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model ⊥ as Empty
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Progress ⊥ as EmptyProgress
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Safety ⊥ as EmptySafety

-- Decide only the explicit miss premise of an already certified transition.
miss? : ∀ {s t} bound (pr : C.Tau s t) → Dec (B.MissBound bound pr)
miss? bound (C.pollMiss {w = w} {sender = sender} _) = Nat._≤?_ (w + C.activeJob sender) bound
miss? bound C.admitted = yes tt
miss? bound C.excessive = yes tt
miss? bound (C.inspectZero _) = yes tt
miss? bound (C.inspectPositive _) = yes tt
miss? bound C.pollHit = yes tt
miss? bound C.registered = yes tt
miss? bound C.setQuit = yes tt
miss? bound (C.claim _) = yes tt
miss? bound (C.cancel _) = yes tt
miss? bound (C.retire _) = yes tt
miss? bound C.flush = yes tt
miss? bound C.drained = yes tt
miss? bound C.abort = yes tt

-- This checks resource premises on a proof object, not raw logs or arbitrary model reachability.
budget? : ∀ {p s actions t} bound (run : C.Run p s actions t) → Dec (B.Budgeted bound run)
budget? bound C.stop = yes tt
budget? bound (C.visible _ run) = budget? bound run
budget? bound (C.internal pr run) with miss? bound pr | budget? bound run
... | yes hit | yes rest = yes (hit , rest)
... | no bad | _ = no λ pair → bad (proj₁ pair)
... | yes _ | no bad = no λ pair → bad (proj₂ pair)

-- A quiescent sequential endpoint owes no reply but retains one completed job.
ready : C.State
ready = C.state C.awaitNext 0 C.idle 1 false

-- Preserve callback selection and the exact reply value in every ordinary round.
roundActions : List C.Action
roundActions = C.recvRequest ∷ C.nextReply (C.normal true) ∷ C.sendReply (C.normal true) ∷ []

-- The first round creates one retained token without an early collection.
first : C.Run C.nodeNext C.initial roundActions ready
first = C.append T.first-registered $ C.internal (C.claim refl) $
  C.visible (C.choose refl refl) $ C.visible (C.send refl) $ C.internal (C.retire refl) C.stop

-- Every subsequent fully retired round consumes the old token and leaves exactly one new token.
cycle : C.Run C.nodeNext ready roundActions ready
cycle = C.visible (C.receiveRequest C.atNext) $ C.internal C.admitted $
  C.internal (C.inspectPositive (s≤s z≤n)) $ C.internal C.pollHit $
  C.internal C.registered $ C.internal (C.claim refl) $ C.visible (C.choose refl refl) $
  C.visible (C.send refl) $ C.internal (C.retire refl) C.stop

-- One plus n rounds are actual fresh executions, not arbitrary state seeds.
historyActions : ℕ → List C.Action
historyActions zero = roundActions
historyActions (suc n) = historyActions n ++ roundActions

-- The same one-token endpoint is reached after arbitrarily long finite visible histories.
history : ∀ n → C.Run C.nodeNext C.initial (historyActions n) ready
history zero = first
history (suc n) = C.append (history n) cycle

-- No miss with unfinished work occurs anywhere in this sequential family.
history-budget : ∀ n → B.Budgeted 0 (history n)
history-budget zero = toWitness {a? = budget? 0 first} tt
history-budget (suc n) = B.budget-append (history n) cycle (history-budget n)
  (toWitness {a? = budget? 0 cycle} tt)

-- All historical growth is collected early: there are exactly n hits after n+1 rounds.
history-early : ∀ n → A.early (history n) ≡ n
history-early zero = refl
history-early (suc n) = trans (A.early-append (history n) cycle)
  (trans (cong (_+ 1) (history-early n)) (trans (+-suc n 0) (cong suc (+-identityʳ n))))

-- The universal budget theorem applies to every member without a history-length assumption.
history-bound : ∀ n → C.registeredJobs ready ≤ 1
history-bound n = B.initial-bound (history n) (history-budget n)

-- Only the last token needs collection after Quit in this particular family.
shutdown : C.Run C.nodeNext ready (C.recvQuit ∷ C.sendDone ∷ []) (C.state C.closed 0 C.idle 0 true)
shutdown = C.visible (C.receiveQuit C.atNext) $ C.internal C.setQuit $
  C.internal C.flush $ C.internal C.drained $ C.visible C.finish C.stop

-- The one-flush example is deliberately scoped to the constructed family, not every schedule.
one-final : A.final shutdown ≡ 1
one-final = refl

-- Polling after a visible Send but before retirement must budget the still-active old job.
sent-still-unfinished : A.unfinished (C.state C.poll 0 C.sent 0 false) ≡ 1 ×
  C.owed (C.state C.awaitNext 0 C.sent 0 false) ≡ 0
sent-still-unfinished = refl , refl

-- Two requests can be accepted while the sender is wholly unscheduled in this local model.
burst : C.Run C.nodeNext C.initial (C.recvRequest ∷ C.recvRequest ∷ [])
  (C.state C.awaitNext 2 C.idle 0 false)
burst = C.append T.first-registered $ C.visible (C.receiveRequest C.atNext) $
  C.internal C.admitted $ C.internal (C.inspectPositive (s≤s z≤n)) $
  C.internal (C.pollMiss (s≤s z≤n)) $ C.internal C.registered C.stop

-- The burst requires B=1 and saturates the resulting B+1 inventory bound.
burst-bound : C.registeredJobs (C.state C.awaitNext 2 C.idle 0 false) ≤ 2
burst-bound = B.initial-bound burst (toWitness {a? = budget? 1 burst} tt)

-- The smaller premise is false on the same reachable run; it cannot be silently discharged.
burst-needs-premise : B.Budgeted 0 burst → ⊥
burst-needs-premise = toWitnessFalse {a? = budget? 0 burst} tt

-- Rejection retains the current unregistered obligation instead of counting it as collected.
rejection-work : A.work (C.state C.failed 0 C.idle 0 false) ≡ 1 × A.collections T.rejected-run ≡ 0
rejection-work = refl , refl

-- The held-selected example has one early collection and two final collections for three requests.
selected-accounting : A.collections T.selected-hit-closes ≡ 3 ×
  A.early T.selected-hit-closes ≡ 1 × A.final T.selected-hit-closes ≡ 2
selected-accounting = A.closed-collections T.selected-hit-closes , refl , refl

-- The generated drain needs no application Notification value even with a claimed blocked next.
blocked-completes : Data.Product.Σ (List C.Action) λ actions →
  C.Run C.nodeNext (C.state C.flushing 1 C.claimed 0 true) actions (C.state C.closed 0 C.idle 0 true)
blocked-completes = P.complete S.flushing

-- The universal post-Quit bound applies to a held selected normal without replacing its payload.
held-selected-bound : ∀ {actions t}
  (run : C.Run C.nodeNext (C.state C.flushing 0 (C.selected (C.normal false)) 0 true) actions t) →
  P.steps run ≤ 5
held-selected-bound run = P.bounded run S.flushing

-- Without a bounded client, fresh histories can queue arbitrarily many unfinished jobs.
queuedActions : ℕ → List C.Action
queuedActions zero = C.recvRequest ∷ []
queuedActions (suc n) = queuedActions n ++ (C.recvRequest ∷ [])

-- No sender is scheduled and every positive-index optional collection legally misses.
queued : ∀ n → C.Run C.nodeNext C.initial (queuedActions n)
  (C.state C.awaitNext (suc n) C.idle 0 false)
queued zero = T.first-registered
queued (suc n) = C.append (queued n) $ C.visible (C.receiveRequest C.atNext) $
  C.internal C.admitted $ C.internal (C.inspectPositive (s≤s z≤n)) $
  C.internal (C.pollMiss (s≤s z≤n)) $ C.internal C.registered C.stop

-- Collection alone cannot give a universal local bound for arbitrary request writers.
unbounded-without-premise : ∀ bound → C.Run C.nodeNext C.initial (queuedActions bound)
  (C.state C.awaitNext (suc bound) C.idle 0 false) ×
  bound < C.registeredJobs (C.state C.awaitNext (suc bound) C.idle 0 false)
unbounded-without-premise bound rewrite +-identityʳ bound = queued bound , ≤-refl

-- A fresh request can be claimed and Quit received even when ordinary notifications are impossible.
empty-prefix : Empty.Run Empty.nodeNext Empty.initial (Empty.recvRequest ∷ Empty.recvQuit ∷ [])
  (Empty.state Empty.signalQuit 0 Empty.claimed 0 false)
empty-prefix = Empty.visible (Empty.receiveRequest Empty.atFirst) $ Empty.internal Empty.admitted $
  Empty.internal (Empty.inspectZero refl) $ Empty.internal Empty.registered $
  Empty.internal (Empty.claim refl) $ Empty.visible (Empty.receiveQuit Empty.atNext) Empty.stop

-- The general completion theorem still constructs cancellation and Done for that reachable state.
empty-completes : Σ[ actions ∈ List Empty.Action ] Empty.Run Empty.nodeNext
  (Empty.state Empty.signalQuit 0 Empty.claimed 0 false) actions (Empty.state Empty.closed 0 Empty.idle 0 true)
empty-completes = EmptyProgress.complete EmptySafety.publishing
