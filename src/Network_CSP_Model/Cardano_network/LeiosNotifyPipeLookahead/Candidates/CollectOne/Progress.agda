{-# OPTIONS --safe #-}

-- Local successful-operation progress and finite shutdown bounds, not runtime fairness or latency.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Progress
  (Notification : Set) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; +-monoʳ-≤; *-monoˡ-≤;
  +-identityʳ)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Safety Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Rank Notification as R
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Accounting Notification as A
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Bounds Notification as B
import Cardano_network.LeiosNotifyPipeLookahead.ServerConservation Notification as Counts

-- A source move names one actual successful internal or visible operation.
data Move (p : Contract) : State → State → Set where
  internal : ∀ {s t} → Tau s t → Move p s t
  visible : ∀ {s a t} → Step p s a t → Move p s t

-- Every nonclosed shutdown state enables a move without requiring another next callback.
progress : ∀ {p s} → S.Stopping s →
  (s ≡ state closed 0 idle 0 true) ⊎ (Σ[ t ∈ State ] Move p s t)
progress S.publishing = inj₂ (_ , internal setQuit)
progress (S.flushing {c = suc c}) = inj₂ (_ , internal flush)
progress (S.flushing {sender = claimed} {c = zero}) = inj₂ (_ , internal (cancel refl))
progress (S.flushing {sender = selected m} {c = zero}) = inj₂ (_ , visible (send refl))
progress (S.flushing {sender = sent} {c = zero}) = inj₂ (_ , internal (retire refl))
progress (S.flushing {w = suc w} {sender = idle} {c = zero}) = inj₂ (_ , internal (claim refl))
progress (S.flushing {w = zero} {sender = idle} {c = zero}) = inj₂ (_ , internal drained)
progress S.ready = inj₂ (_ , visible finish)
progress S.closed = inj₁ refl

-- Count source operations rather than wall-clock steps or scheduler time.
steps : ∀ {p s actions t} → Run p s actions t → ℕ
steps stop = 0
steps (internal _ run) = suc (steps run)
steps (visible _ run) = suc (steps run)

-- Every finite shutdown continuation is bounded, not just a chosen drain schedule.
bounded : ∀ {p s actions t} (run : Run p s actions t) → S.Stopping s → steps run ≤ R.rank s
bounded stop _ = z≤n
bounded (internal pr run) stopping =
  ≤-trans (s≤s (bounded run (S.tau-stays pr stopping))) (R.decreases pr)
bounded (visible pr run) stopping =
  ≤-trans (s≤s (bounded run (S.step-stays pr stopping))) (R.step-decreases pr stopping)

-- Well-founded recursion constructs a successful drain without a notification inhabitant.
complete-from : ∀ {p} (s : State) → Acc _<_ (R.rank s) → S.Stopping s →
  Σ[ actions ∈ List Action ] Run p s actions (state closed 0 idle 0 true)
complete-from s (acc smaller) stopping with progress stopping
... | inj₁ refl = [] , stop
... | inj₂ (t , internal pr) with complete-from t (smaller (R.decreases pr)) (S.tau-stays pr stopping)
...   | actions , rest = actions , internal pr rest
complete-from s (acc smaller) stopping | inj₂ (t , visible {a = a} pr)
  with complete-from t (smaller (R.step-decreases pr stopping)) (S.step-stays pr stopping)
... | actions , rest = a ∷ actions , visible pr rest

-- Actual Quit supplies the region; successful source Send/scheduling remains an abstraction premise.
complete : ∀ {p s} → S.Stopping s →
  Σ[ actions ∈ List Action ] Run p s actions (state closed 0 idle 0 true)
complete {s = s} stopping = complete-from s (<-wellFounded (R.rank s)) stopping

-- At shutdown no current request remains unregistered.
shutdown-work : ∀ {s} → S.Stopping s → A.work s ≡ registeredJobs s
shutdown-work S.publishing = refl
shutdown-work S.flushing = refl
shutdown-work S.ready = refl
shutdown-work S.closed = refl

-- No further RequestNext can contribute to the conservation equation after Quit.
no-requests : ∀ {p s actions t} (run : Run p s actions t) →
  S.Stopping s → Counts.requests actions ≡ 0
no-requests stop _ = refl
no-requests (internal pr run) stopping = no-requests run (S.tau-stays pr stopping)
no-requests (visible (receiveRequest reading) run) stopping = ⊥-elim (S.no-reading stopping reading)
no-requests (visible (receiveQuit reading) run) stopping = ⊥-elim (S.no-reading stopping reading)
no-requests (visible pr@(choose _ _) run) stopping = no-requests run (S.step-stays pr stopping)
no-requests (visible pr@(send _) run) stopping = no-requests run (S.step-stays pr stopping)
no-requests (visible finish run) stopping = no-requests run S.closed

-- A stopped reader has no early-poll operation; its collections are all final flushes.
final-only : ∀ {s t} (pr : Tau s t) → S.Stopping s → A.collected-step pr ≡ A.final-step pr
final-only admitted ()
final-only excessive ()
final-only (inspectZero _) ()
final-only (inspectPositive _) ()
final-only pollHit ()
final-only (pollMiss _) ()
final-only registered ()
final-only setQuit _ = refl
final-only (claim _) _ = refl
final-only (cancel _) _ = refl
final-only (retire _) _ = refl
final-only flush _ = refl
final-only drained _ = refl
final-only abort ()

-- The final-drain counter equals all collections on any post-Quit continuation.
collections-final : ∀ {p s actions t} (run : Run p s actions t) →
  S.Stopping s → A.collections run ≡ A.final run
collections-final stop _ = refl
collections-final (internal pr run) stopping =
  trans (cong (_+ A.collections run) (final-only pr stopping))
    (cong (A.final-step pr +_) (collections-final run (S.tau-stays pr stopping)))
collections-final (visible pr run) stopping = collections-final run (S.step-stays pr stopping)

-- Every successful shutdown schedule flushes exactly its retained registered inventory.
shutdown-flushes : ∀ {p s actions}
  (run : Run p s actions (state closed 0 idle 0 true)) →
  S.Stopping s → A.final run ≡ registeredJobs s
shutdown-flushes {s = s} run stopping =
  trans (sym (collections-final run stopping))
    (trans (sym (+-identityʳ (A.collections run)))
      (trans (sym (A.run-balance run))
        (trans (cong (A.work s +_) (no-requests run stopping))
          (trans (+-identityʳ (A.work s)) (shutdown-work stopping)))))

-- A budgeted fresh prefix supplies a history-independent bound on later successful flush work.
fresh-shutdown-flushes : ∀ {p prefix s actions bound}
  (before : Run p initial prefix s) → B.Budgeted bound before → S.Stopping s →
  (after : Run p s actions (state closed 0 idle 0 true)) → A.final after ≤ suc bound
fresh-shutdown-flushes before budget stopping after rewrite shutdown-flushes after stopping =
  B.initial-bound before budget

-- The same premise bounds every later finite source continuation by 3+5(B+1) operations.
fresh-shutdown-steps : ∀ {p prefix s actions t bound}
  (before : Run p initial prefix s) → B.Budgeted bound before → S.Stopping s →
  (after : Run p s actions t) → steps after ≤ 3 + R.five (suc bound)
fresh-shutdown-steps before budget stopping after =
  ≤-trans (bounded after stopping)
    (≤-trans (R.shutdown-bound stopping)
      (+-monoʳ-≤ 3 (*-monoˡ-≤ 5 (B.initial-bound before budget))))
