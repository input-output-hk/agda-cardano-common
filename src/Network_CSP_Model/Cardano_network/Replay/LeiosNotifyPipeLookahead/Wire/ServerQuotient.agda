{-# OPTIONS --safe #-}

-- Both exact finite local server wire languages, preserving initial-state prefixes and callback contracts.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerQuotient (Notification : Set) where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ServerConservation Notification as Count
import Cardano_network.LeiosNotifyPipeLookahead.ServerPhase Notification as Phase
import Cardano_network.LeiosNotifyPipeLookahead.ServerProgress Notification as Shutdown
import Cardano_network.LeiosNotifyPipeLookahead.Properties Notification as Existing
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Notification as Q

-- A concrete source witness retains selections and target, not merely a wire-count calculation.
SourceTrace : S.Contract → List Q.Wire → Set
SourceTrace p rows = Σ[ actions ∈ List S.Action ]
  (Σ[ target ∈ S.State ] (S.Run p S.initial actions target × Q.wire actions ≡ rows))

-- This ghost control remembers whether nodeNext has already sent a cancellation.
data Stage : Set where
  ordinary quitting canceling ended : Stage

-- Quotient control and the numerical count are assembled independently.
at : Stage → ℕ → Q.State
at ordinary n = Q.Open n
at quitting n = Q.QuitSeen n
at canceling n = Q.CancelOnly n
at ended n = Q.Closed

-- Every nonterminal quotient count is the exact remaining wire obligation count.
view : Stage → S.State → Q.State
view stage s = at stage (S.owed s)

-- After a true-flag cancellation, no selected normal reply can remain behind the serial sender.
data NoNormal : S.Sender → Set where
  idle : NoNormal S.idle
  claimed : NoNormal S.claimed
  sent : NoNormal S.sent
  canceled : NoNormal (S.selected S.canceled)

-- Source program phases justify the quotient control, including delayed Quit publication.
data Control : Stage → S.State → Set where
  before : ∀ {r w sender c} → Phase.Before r → Control ordinary (S.state r w sender c false)
  quitting : ∀ {s} → Shutdown.Stopping s → Control quitting s
  canceling : ∀ {r w sender c} → Shutdown.Stopping (S.state r w sender c true) → NoNormal sender →
    Control canceling (S.state r w sender c true)
  ended : Control ended (S.state S.closed 0 S.idle 0 true)

-- Only nodeNext needs a proof that selected Canceled came from the true-flag branch.
SelectedSafe : S.Sender → S.Contract → Bool → Set
SelectedSafe (S.selected S.canceled) S.nodeNext flag = flag ≡ true
SelectedSafe _ _ _ = ⊤

-- This independent invariant excludes a forged pre-Quit node cancellation.
Safe : S.Contract → S.State → Set
Safe p s = SelectedSafe (S.sender s) p (S.quitFlag s)

-- Flag publication establishes selected-cancellation safety regardless of the earlier sender phase.
safe-published : ∀ sender p → SelectedSafe sender p false → SelectedSafe sender p true
safe-published S.idle p _ = tt
safe-published S.claimed p _ = tt
safe-published S.sent p _ = tt
safe-published (S.selected (S.normal _)) p _ = tt
safe-published (S.selected S.canceled) S.genericNext _ = tt
safe-published (S.selected S.canceled) S.nodeNext _ = refl

-- Scheduling cannot manufacture a node callback result that violates its actual contract.
safe-tau : ∀ {p s t} → S.Tau s t → Safe p s → Safe p t
safe-tau S.admitted safe = safe
safe-tau S.excessive safe = safe
safe-tau S.registered safe = safe
safe-tau (S.setQuit {s = sender}) safe = safe-published sender _ safe
safe-tau (S.claim _) _ = tt
safe-tau {p = S.genericNext} (S.cancel _) _ = tt
safe-tau {p = S.nodeNext} (S.cancel _) _ = refl
safe-tau (S.retire _) _ = tt
safe-tau S.flush safe = safe
safe-tau S.drained _ = tt
safe-tau S.abort safe = safe

-- Exact visible source data and the callback guard preserve the same safety invariant.
safe-step : ∀ {p s a t} → S.Step p s a t → Safe p s → Safe p t
safe-step (S.receiveRequest _) safe = safe
safe-step (S.receiveQuit _) safe = safe
safe-step (S.choose {m = S.normal _} _ _) _ = tt
safe-step {p = S.genericNext} (S.choose {m = S.canceled} _ _) _ = tt
safe-step {p = S.nodeNext} (S.choose {m = S.canceled} _ ())
safe-step (S.send _) _ = tt
safe-step S.finish _ = tt

-- Every hidden operation preserves the appropriate quotient region.
control-tau : ∀ {stage s t} → S.Tau s t → Control stage s → Control stage t
control-tau pr (quitting stopping) = quitting (Shutdown.tau-stays pr stopping)
control-tau S.admitted (before _) = before Phase.register
control-tau S.excessive (before _) = before Phase.raising
control-tau S.registered (before _) = before Phase.awaitNext
control-tau S.setQuit (before ())
control-tau (S.claim _) (before phase) = before phase
control-tau (S.retire _) (before phase) = before phase
control-tau S.flush (before ())
control-tau S.abort (before _) = before Phase.failed
control-tau S.admitted (canceling () _)
control-tau S.excessive (canceling () _)
control-tau S.registered (canceling () _)
control-tau pr@(S.claim _) (canceling stopping _) = canceling (Shutdown.tau-stays pr stopping) claimed
control-tau pr@(S.cancel _) (canceling stopping _) = canceling (Shutdown.tau-stays pr stopping) canceled
control-tau pr@(S.retire _) (canceling stopping _) = canceling (Shutdown.tau-stays pr stopping) idle
control-tau pr@S.flush (canceling stopping clean) = canceling (Shutdown.tau-stays pr stopping) clean
control-tau S.drained (canceling _ _) = canceling Shutdown.ready idle
control-tau S.abort (canceling () _)
control-tau () ended

-- An erased next action cannot move the reader or reopen a published cancellation region.
control-choose : ∀ {p stage s m t} → S.Step p s (S.nextReply m) t → Control stage s → Control stage t
control-choose (S.choose _ _) (before phase) = before phase
control-choose pr@(S.choose _ _) (quitting stopping) = quitting (Shutdown.step-stays pr stopping)

-- One visible source operation gives exactly one quotient operation with its original data.
visible : ∀ {p stage s a t row} → S.Step p s a t → Q.observe a ≡ just row →
  Control stage s → Safe p s →
  Σ[ next ∈ Stage ] (Control next t × Q.Step p (view stage s) row (view next t))
visible (S.receiveRequest S.atFirst) refl (before _) safe = ordinary , before Phase.admit , Q.receiveRequest
visible (S.receiveRequest S.atNext) refl (before _) safe = ordinary , before Phase.admit , Q.receiveRequest
visible (S.receiveRequest S.atFirst) refl (quitting ()) safe
visible (S.receiveRequest S.atNext) refl (quitting ()) safe
visible (S.receiveQuit S.atFirst) refl (before _) safe = quitting , quitting Shutdown.publishing , Q.receiveQuit
visible (S.receiveQuit S.atNext) refl (before _) safe = quitting , quitting Shutdown.publishing , Q.receiveQuit
visible (S.receiveQuit S.atFirst) refl (quitting ()) safe
visible (S.receiveQuit S.atNext) refl (quitting ()) safe
visible (S.choose _ _) () control safe
visible (S.send {r = r} {w = w} {m = S.normal value} _) refl (before phase) safe
  rewrite Count.finish-job (S.unregistered r) w = ordinary , before phase , Q.normalOpen
visible pr@(S.send {r = r} {w = w} {m = S.normal value} _) refl (quitting stopping) safe
  rewrite Count.finish-job (S.unregistered r) w = quitting , quitting (Shutdown.step-stays pr stopping) , Q.normalQuit
visible (S.send {m = S.normal value} _) refl (canceling _ ()) safe
visible {p = S.genericNext} (S.send {r = r} {w = w} {m = S.canceled} _) refl (before phase) safe
  rewrite Count.finish-job (S.unregistered r) w = ordinary , before phase , Q.canceledOpen
visible {p = S.nodeNext} (S.send {m = S.canceled} _) refl (before phase) ()
visible {p = S.genericNext} pr@(S.send {r = r} {w = w} {m = S.canceled} _) refl (quitting stopping) safe
  rewrite Count.finish-job (S.unregistered r) w = quitting , quitting (Shutdown.step-stays pr stopping) , Q.canceledQuitGeneric
visible {p = S.nodeNext} pr@(S.send {r = r} {w = w} {m = S.canceled} _) refl (quitting stopping) refl
  rewrite Count.finish-job (S.unregistered r) w = canceling , canceling (Shutdown.step-stays pr stopping) sent , Q.canceledQuitNode
visible pr@(S.send {r = r} {w = w} {m = S.canceled} _) refl (canceling stopping _) safe
  rewrite Count.finish-job (S.unregistered r) w = canceling , canceling (Shutdown.step-stays pr stopping) sent , Q.canceledOnly
visible S.finish refl (quitting _) safe = ended , ended , Q.doneQuit
visible S.finish refl (canceling _ _) safe = ended , ended , Q.doneOnly

-- Internal source rules change only the quotient count's representation, not its value.
view-tau : ∀ stage {s t} → S.Tau s t → view stage s ≡ view stage t
view-tau ordinary pr = cong Q.Open (Count.tau-balance pr)
view-tau quitting pr = cong Q.QuitSeen (Count.tau-balance pr)
view-tau canceling pr = cong Q.CancelOnly (Count.tau-balance pr)
view-tau ended pr = refl

-- Every detailed source prefix projects to a quotient prefix; callback actions alone disappear.
project : ∀ {p stage s actions t} → S.Run p s actions t → Control stage s → Safe p s →
  Σ[ last ∈ Stage ] Q.Run p (view stage s) (Q.wire actions) (view last t)
project {stage = stage} S.stop control safe = stage , Q.stop
project {p = p} {stage = stage} {t = t} (S.internal pr rest) control safe
  with project rest (control-tau pr control) (safe-tau pr safe)
... | last , execution = last , subst (λ start → Q.Run p start _ (view last t)) (sym (view-tau stage pr)) execution
project (S.visible pr@(S.choose _ _) rest) control safe = project rest (control-choose pr control) (safe-step pr safe)
project (S.visible pr@(S.receiveRequest _) rest) control safe with visible pr refl control safe
... | next , after , step with project rest after (safe-step pr safe)
...   | last , execution = last , Q.step step execution
project (S.visible pr@(S.receiveQuit _) rest) control safe with visible pr refl control safe
... | next , after , step with project rest after (safe-step pr safe)
...   | last , execution = last , Q.step step execution
project (S.visible pr@(S.send _) rest) control safe with visible pr refl control safe
... | next , after , step with project rest after (safe-step pr safe)
...   | last , execution = last , Q.step step execution
project (S.visible pr@S.finish rest) control safe with visible pr refl control safe
... | next , after , step with project rest after (safe-step pr safe)
...   | last , execution = last , Q.step step execution

-- The fresh-state sound direction has no externally supplied invariant or resource premise.
source→quotient : ∀ {p rows} → SourceTrace p rows → Q.HasTrace p Q.initial rows
source→quotient (actions , target , execution , refl) with project execution (before Phase.first) tt
... | stage , quotient = _ , quotient

-- Canonical schedules keep the reader available and never select an unobserved future value.
data Canonical : Q.State → S.State → Set where
  openState : ∀ {r n c} → S.Reading r → Canonical (Q.Open n) (S.state r n S.idle c false)
  quitState : ∀ {n c} → Canonical (Q.QuitSeen n) (S.state S.signalQuit n S.idle c false)
  onlyState : ∀ {n c} → Canonical (Q.CancelOnly n) (S.state S.flushing n S.idle c true)
  closedState : Canonical Q.Closed (S.state S.closed 0 S.idle 0 true)

-- Either actual reading phase allows independent sender work in a canonical prefix.
reading-active : ∀ {r} → S.Reading r → S.active r ≡ true
reading-active S.atFirst = refl
reading-active S.atNext = refl

-- A supplied callback value is selected and sent exactly, with retirement recorded separately.
selected-run : ∀ {p r n c} (m : S.Reply) → S.active r ≡ true → S.allowed p m ≡ true →
  S.Run p (S.state r (suc n) S.idle c false) (S.nextReply m ∷ S.sendReply m ∷ [])
    (S.state r n S.idle (suc c) false)
selected-run m live allowed = S.internal (S.claim live)
  (S.visible (S.choose live allowed) (S.visible (S.send live) (S.internal (S.retire live) S.stop)))

-- True-flag cancellation needs no ordinary notification inhabitant or next callback.
canceled-run : ∀ {p r n c} → S.active r ≡ true →
  S.Run p (S.state r (suc n) S.idle c true) (S.sendReply S.canceled ∷ [])
    (S.state r n S.idle (suc c) true)
canceled-run live = S.internal (S.claim live)
  (S.internal (S.cancel live) (S.visible (S.send live) (S.internal (S.retire live) S.stop)))

-- Every quotient operation has an actual finite source schedule under the same callback contract.
realize-step : ∀ {p q row q′ s} → Q.Step p q row q′ → Canonical q s →
  Σ[ actions ∈ List S.Action ] (Σ[ t ∈ S.State ]
    (S.Run p s actions t × Q.wire actions ≡ row ∷ [] × Canonical q′ t))
realize-step Q.receiveRequest (openState reading) = _ , _ ,
  S.visible (S.receiveRequest reading) (S.internal S.admitted (S.internal S.registered S.stop)) , refl , openState S.atNext
realize-step Q.receiveQuit (openState reading) = _ , _ , S.visible (S.receiveQuit reading) S.stop , refl , quitState
realize-step (Q.normalOpen {value = value}) (openState reading) = _ , _ ,
  selected-run (S.normal value) (reading-active reading) refl , refl , openState reading
realize-step (Q.normalQuit {value = value}) quitState = _ , _ ,
  selected-run (S.normal value) refl refl , refl , quitState
realize-step Q.canceledOpen (openState reading) = _ , _ ,
  selected-run S.canceled (reading-active reading) refl , refl , openState reading
realize-step Q.canceledQuitGeneric quitState = _ , _ , selected-run S.canceled refl refl , refl , quitState
realize-step Q.canceledQuitNode quitState = _ , _ , S.internal S.setQuit (canceled-run refl) , refl , onlyState
realize-step Q.canceledOnly onlyState = _ , _ , canceled-run refl , refl , onlyState
realize-step Q.doneQuit (quitState {c = c}) = _ , _ ,
  S.internal S.setQuit (Existing.drain-completed c) , refl , closedState
realize-step Q.doneOnly (onlyState {c = c}) = _ , _ , Existing.drain-completed c , refl , closedState

-- Canonical finite realization composes actual source schedules while preserving exact wire rows.
realize : ∀ {p q rows q′ s} → Q.Run p q rows q′ → Canonical q s →
  Σ[ actions ∈ List S.Action ] (Σ[ t ∈ S.State ]
    (S.Run p s actions t × Q.wire actions ≡ rows × Canonical q′ t))
realize Q.stop canonical = [] , _ , S.stop , refl , canonical
realize (Q.step pr rest) canonical with realize-step pr canonical
... | actions , middle , prefix , first , after with realize rest after
...   | more , target , suffix , second , last = actions ++ more , target , S.append prefix suffix ,
  trans (Q.wire-append actions more)
    (trans (cong (λ rows → rows ++ Q.wire more) first) (cong (_ ∷_) second)) , last

-- Accepted fresh wire traces have concrete source witnesses even over an empty notification type.
quotient→source : ∀ {p rows} → Q.HasTrace p Q.initial rows → SourceTrace p rows
quotient→source (_ , execution) with realize execution (openState S.atFirst)
... | actions , target , source , same , last = actions , target , source , same

-- Both inclusions are exposed together without imposing capacity, fairness or notification assumptions.
equivalence : ∀ p rows → (SourceTrace p rows → Q.HasTrace p Q.initial rows) ×
  (Q.HasTrace p Q.initial rows → SourceTrace p rows)
equivalence p rows = source→quotient , quotient→source

-- Total decision at the unchanged detailed source language; no fuel-exhaustion rejection is used.
decide-source : (p : S.Contract) (rows : List Q.Wire) → Dec (SourceTrace p rows)
decide-source p rows with Q.decide p Q.initial rows
... | yes witness = yes (quotient→source witness)
... | no deny = no λ source → deny (source→quotient source)
