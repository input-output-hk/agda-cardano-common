{-# OPTIONS --safe #-}

-- Completed tokens and every future token retirement are counted throughout actual source runs.
module Cardano_network.LeiosNotifyPipeLookahead.CompletionAccounting
  (Notification : Set) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-suc; ≤-trans; n≤1+n; m≤n+m; m≤m+n)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Properties Notification as Control
import Cardano_network.LeiosNotifyPipeLookahead.ServerConservation Notification as Reply

-- A sent wire response still needs retirement before its completion token can be flushed.
unretired : S.Sender → ℕ
unretired S.sent = 1
unretired _ = 0

-- These are all jobs that will need a completion flush, including replies still owed.
work : S.State → ℕ
work s = S.owed s + (unretired (S.sender s) + S.completed s)

-- Exactly this source rule consumes one completion occurrence.
flush-step : ∀ {s t} → S.Tau s t → ℕ
flush-step S.flush = 1
flush-step _ = 0

-- Exactly this source rule publishes a completed sender job.
retire-step : ∀ {s t} → S.Tau s t → ℕ
retire-step (S.retire _) = 1
retire-step _ = 0

-- Count real flush transitions, independently of visible wire events.
flushes : ∀ {p s actions t} → S.Run p s actions t → ℕ
flushes S.stop = 0
flushes (S.internal pr run) = flush-step pr + flushes run
flushes (S.visible pr run) = flushes run

-- Count real source retirements rather than equating them with reply Send records.
retirements : ∀ {p s actions t} → S.Run p s actions t → ℕ
retirements S.stop = 0
retirements (S.internal pr run) = retire-step pr + retirements run
retirements (S.visible pr run) = retirements run

-- The new count agrees with the earlier witness-specific flush counter on every run.
legacy-count : ∀ {p s actions t} (run : S.Run p s actions t) → flushes run ≡ Control.flushCount run
legacy-count S.stop = refl
legacy-count (S.visible pr run) = legacy-count run
legacy-count (S.internal S.admitted run) = legacy-count run
legacy-count (S.internal S.excessive run) = legacy-count run
legacy-count (S.internal S.registered run) = legacy-count run
legacy-count (S.internal S.setQuit run) = legacy-count run
legacy-count (S.internal (S.claim _) run) = legacy-count run
legacy-count (S.internal (S.cancel _) run) = legacy-count run
legacy-count (S.internal (S.retire _) run) = legacy-count run
legacy-count (S.internal S.flush run) = cong suc (legacy-count run)
legacy-count (S.internal S.drained run) = legacy-count run
legacy-count (S.internal S.abort run) = legacy-count run

-- Every visible source rule leaves the completed counter unchanged.
step-completed : ∀ {p s a t} → S.Step p s a t → S.completed s ≡ S.completed t
step-completed (S.receiveRequest _) = refl
step-completed (S.receiveQuit _) = refl
step-completed (S.choose _ _) = refl
step-completed (S.send _) = refl
step-completed S.finish = refl

-- Completed bookkeeping changes by precisely the actual retirements and flushes in any prefix.
token-balance : ∀ {p s actions t} (run : S.Run p s actions t) →
  S.completed s + retirements run ≡ flushes run + S.completed t
token-balance S.stop = +-identityʳ _
token-balance (S.visible pr run) = trans (cong (_+ retirements run) (step-completed pr)) (token-balance run)
token-balance (S.internal S.admitted run) = token-balance run
token-balance (S.internal S.excessive run) = token-balance run
token-balance (S.internal S.registered run) = token-balance run
token-balance (S.internal S.setQuit run) = token-balance run
token-balance (S.internal (S.claim _) run) = token-balance run
token-balance (S.internal (S.cancel _) run) = token-balance run
token-balance (S.internal (S.retire {c = c} _) run) = trans (+-suc c (retirements run)) (token-balance run)
token-balance (S.internal S.flush run) = cong suc (token-balance run)
token-balance (S.internal S.drained run) = token-balance run
token-balance (S.internal S.abort run) = token-balance run

-- Moving a successor through both additions exposes the unit consumed by a flush.
raise-two : ∀ a b c → a + (b + suc c) ≡ suc (a + (b + c))
raise-two a b c = trans (cong (a +_) (+-suc b c)) (+-suc a (b + c))

-- Every hidden rule preserves total future flush work except the flush itself.
tau-work : ∀ {s t} (pr : S.Tau s t) → work s ≡ flush-step pr + work t
tau-work S.admitted = refl
tau-work S.excessive = refl
tau-work S.registered = refl
tau-work S.setQuit = refl
tau-work pr@(S.claim {c = c} _) = cong (_+ c) (Reply.tau-balance pr)
tau-work (S.cancel _) = refl
tau-work (S.retire _) = refl
tau-work (S.flush {w = w} {s = sender} {c = c}) = raise-two (w + S.unsent sender) (unretired sender) c
tau-work S.drained = refl
tau-work S.abort = refl

-- Sending moves the owed unit into the sent-but-unretired location without losing it.
send-work : ∀ r w c → (S.unregistered r + (w + 1)) + c ≡
  (S.unregistered r + (w + 0)) + suc c
send-work r w c = trans (cong (_+ c) (Reply.finish-job (S.unregistered r) w))
  (sym (+-suc (S.unregistered r + (w + 0)) c))

-- A RequestNext alone adds work; reply Sends and other visible records merely preserve it.
step-work : ∀ {p s a t} → S.Step p s a t → work s + Reply.request a ≡ work t
step-work (S.receiveRequest {w = w} {s = sender} {c = c} S.atFirst) =
  trans (+-suc ((w + S.unsent sender) + (unretired sender + c)) 0)
    (cong suc (+-identityʳ ((w + S.unsent sender) + (unretired sender + c))))
step-work (S.receiveRequest {w = w} {s = sender} {c = c} S.atNext) =
  trans (+-suc ((w + S.unsent sender) + (unretired sender + c)) 0)
    (cong suc (+-identityʳ ((w + S.unsent sender) + (unretired sender + c))))
step-work (S.receiveQuit S.atFirst) = +-identityʳ _
step-work (S.receiveQuit S.atNext) = +-identityʳ _
step-work (S.choose _ _) = +-identityʳ _
step-work (S.send {r = r} {w = w} {c = c} _) = trans (+-identityʳ _) (send-work r w c)
step-work S.finish = refl

-- Total initial work plus newly received requests equals actual flushes plus final work.
run-balance : ∀ {p s actions t} (run : S.Run p s actions t) →
  work s + Reply.requests actions ≡ flushes run + work t
run-balance S.stop = +-identityʳ _
run-balance (S.internal {t = t} {u = u} {es = actions} pr run) =
  trans (cong (_+ Reply.requests actions) (tau-work pr))
    (trans (+-assoc (flush-step pr) (work t) (Reply.requests actions))
      (trans (cong (flush-step pr +_) (run-balance run))
        (sym (+-assoc (flush-step pr) (flushes run) (work u)))))
run-balance (S.visible {s = s} {a = a} {es = actions} pr run) =
  trans (sym (+-assoc (work s) (Reply.request a) (Reply.requests actions)))
    (trans (cong (_+ Reply.requests actions) (step-work pr)) (run-balance run))

-- Every successful close flushes all initial jobs and every request received in that continuation.
closed-flushes : ∀ {p s actions} (run : S.Run p s actions (S.state S.closed 0 S.idle 0 true)) →
  flushes run ≡ work s + Reply.requests actions
closed-flushes run = trans (sym (+-identityʳ (flushes run))) (sym (run-balance run))

-- In a fresh successful session, every historical RequestNext requires exactly one flush.
fresh-closed-flushes : ∀ {p actions} (run : S.Run p S.initial actions (S.state S.closed 0 S.idle 0 true)) →
  flushes run ≡ Reply.requests actions
fresh-closed-flushes = closed-flushes

-- A stopped reader accepts no further request units, including through scheduling interleavings.
no-requests : ∀ {p s actions t} (run : S.Run p s actions t) →
  Control.stopping (S.reader s) ≡ true → Reply.requests actions ≡ 0
no-requests S.stop stopping = refl
no-requests (S.internal pr run) stopping = no-requests run (Control.tau-stopping pr stopping)
no-requests (S.visible (S.receiveRequest S.atFirst) run) ()
no-requests (S.visible (S.receiveRequest S.atNext) run) ()
no-requests (S.visible (S.receiveQuit S.atFirst) run) ()
no-requests (S.visible (S.receiveQuit S.atNext) run) ()
no-requests (S.visible pr@(S.choose _ _) run) stopping = no-requests run (Control.step-stopping pr stopping)
no-requests (S.visible pr@(S.send _) run) stopping = no-requests run (Control.step-stopping pr stopping)
no-requests (S.visible S.finish run) stopping = no-requests run refl

-- All successful post-Quit schedules have the same exact flush count, even with active replies.
shutdown-flushes : ∀ {p s actions} (run : S.Run p s actions (S.state S.closed 0 S.idle 0 true)) →
  Control.stopping (S.reader s) ≡ true → flushes run ≡ work s
shutdown-flushes {s = s} run stopping = trans (closed-flushes run)
  (trans (cong (work s +_) (no-requests run stopping)) (+-identityʳ (work s)))

-- A target preceding shutdown excludes every earlier flush because stopping is persistent.
before-no-flushes : ∀ {p s actions t} (run : S.Run p s actions t) →
  (Control.stopping (S.reader t) ≡ true → Data.Empty.⊥) → flushes run ≡ 0
before-no-flushes S.stop before = refl
before-no-flushes (S.visible pr run) before = before-no-flushes run before
before-no-flushes (S.internal S.flush run) before = ⊥-elim (before (Control.run-stopping run refl))
before-no-flushes (S.internal S.admitted run) before = before-no-flushes run before
before-no-flushes (S.internal S.excessive run) before = before-no-flushes run before
before-no-flushes (S.internal S.registered run) before = before-no-flushes run before
before-no-flushes (S.internal S.setQuit run) before = before-no-flushes run before
before-no-flushes (S.internal (S.claim _) run) before = before-no-flushes run before
before-no-flushes (S.internal (S.cancel _) run) before = before-no-flushes run before
before-no-flushes (S.internal (S.retire _) run) before = before-no-flushes run before
before-no-flushes (S.internal S.drained run) before = before-no-flushes run before
before-no-flushes (S.internal S.abort run) before = before-no-flushes run before

-- Every fresh quiescent ordinary prefix has one retained token per historical request.
ready-history : ∀ {p actions n} → S.Run p S.initial actions (Control.ready n) → Reply.requests actions ≡ n
ready-history run = trans (run-balance run)
  (cong (_+ _) (before-no-flushes run (λ ())))

-- Count actual source operations; flush transitions are a subset rather than an elapsed-time model.
steps : ∀ {p s actions t} → S.Run p s actions t → ℕ
steps S.stop = 0
steps (S.internal pr run) = suc (steps run)
steps (S.visible pr run) = suc (steps run)

-- A source hidden operation consumes at most one flush occurrence.
flush-step≤1 : ∀ {s t} (pr : S.Tau s t) → flush-step pr ≤ 1
flush-step≤1 S.flush = s≤s z≤n
flush-step≤1 S.admitted = z≤n
flush-step≤1 S.excessive = z≤n
flush-step≤1 S.registered = z≤n
flush-step≤1 S.setQuit = z≤n
flush-step≤1 (S.claim _) = z≤n
flush-step≤1 (S.cancel _) = z≤n
flush-step≤1 (S.retire _) = z≤n
flush-step≤1 S.drained = z≤n
flush-step≤1 S.abort = z≤n

-- The exact flush count is a lower bound on the number of source operations required.
flushes≤steps : ∀ {p s actions t} (run : S.Run p s actions t) → flushes run ≤ steps run
flushes≤steps S.stop = z≤n
flushes≤steps (S.internal pr run) = Data.Nat.Properties.+-mono-≤ (flush-step≤1 pr) (flushes≤steps run)
flushes≤steps (S.visible pr run) = ≤-trans (flushes≤steps run) (n≤1+n (steps run))

-- In particular, existing completed tokens alone impose a schedule-independent operation lower bound.
completed-lower-bound : ∀ {p s actions} (run : S.Run p s actions (S.state S.closed 0 S.idle 0 true)) →
  Control.stopping (S.reader s) ≡ true → S.completed s ≤ steps run
completed-lower-bound {s = s} run stopping = ≤-trans
  (≤-trans (m≤n+m (S.completed s) (unretired (S.sender s)))
    (m≤n+m (unretired (S.sender s) + S.completed s) (S.owed s)))
  (subst (_≤ steps run) (shutdown-flushes run stopping) (flushes≤steps run))

-- Existing completions also lower-bound any future successful close, even before Quit is received.
completed-closing-lower-bound : ∀ {p s actions} (run : S.Run p s actions (S.state S.closed 0 S.idle 0 true)) →
  S.completed s ≤ steps run
completed-closing-lower-bound {s = s} {actions} run = ≤-trans
  (≤-trans (m≤n+m (S.completed s) (unretired (S.sender s)))
    (m≤n+m (unretired (S.sender s) + S.completed s) (S.owed s)))
  (≤-trans (m≤m+n (work s) (Reply.requests actions))
    (subst (_≤ steps run) (closed-flushes run) (flushes≤steps run)))

-- No local server source operation can move away from the exact successful closed state.
closed-stays : ∀ {p actions t} → S.Run p (S.state S.closed 0 S.idle 0 true) actions t →
  t ≡ S.state S.closed 0 S.idle 0 true
closed-stays S.stop = refl
closed-stays (S.internal () run)
closed-stays (S.visible () run)
