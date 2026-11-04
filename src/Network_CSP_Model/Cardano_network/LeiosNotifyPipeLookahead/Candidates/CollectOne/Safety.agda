{-# OPTIONS --safe #-}

-- CollectOne's local shutdown safety is proved for its own independent transition rules.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Safety
  (Notification : Set) where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification

-- Actual Quit reception establishes this exact structural shutdown region.
data Stopping : State → Set where
  publishing : ∀ {w sender c} → Stopping (state signalQuit w sender c false)
  flushing : ∀ {w sender c} → Stopping (state flushing w sender c true)
  ready : Stopping (state doneReady 0 idle 0 true)
  closed : Stopping (state closed 0 idle 0 true)

-- No resource premise is needed to establish the region at an actual Quit.
quit-starts : ∀ {p s t} → Step p s recvQuit t → Stopping t
quit-starts (receiveQuit _) = publishing

-- A selected normal reply may still be sent while the reader is stopping.
step-stays : ∀ {p s a t} → Step p s a t → Stopping s → Stopping t
step-stays (receiveRequest atFirst) ()
step-stays (receiveRequest atNext) ()
step-stays (receiveQuit atFirst) ()
step-stays (receiveQuit atNext) ()
step-stays (choose _ _) publishing = publishing
step-stays (send _) publishing = publishing
step-stays (send _) flushing = flushing
step-stays finish ready = closed

-- The new inspection/polling phases cannot occur after this reader has received Quit.
tau-stays : ∀ {s t} → Tau s t → Stopping s → Stopping t
tau-stays admitted ()
tau-stays excessive ()
tau-stays (inspectZero _) ()
tau-stays (inspectPositive _) ()
tau-stays pollHit ()
tau-stays (pollMiss _) ()
tau-stays registered ()
tau-stays setQuit publishing = flushing
tau-stays (claim _) publishing = publishing
tau-stays (claim _) flushing = flushing
tau-stays (cancel _) flushing = flushing
tau-stays (retire _) publishing = publishing
tau-stays (retire _) flushing = flushing
tau-stays flush flushing = flushing
tau-stays drained flushing = ready
tau-stays abort ()

-- Every finite continuation retains the exact post-Quit region.
run-stays : ∀ {p s actions t} → Run p s actions t → Stopping s → Stopping t
run-stays stop stopping = stopping
run-stays (internal pr run) stopping = run-stays run (tau-stays pr stopping)
run-stays (visible pr run) stopping = run-stays run (step-stays pr stopping)

-- Neither a new request nor a repeated Quit can be read in the shutdown region.
no-reading : ∀ {s} → Stopping s → Reading (reader s) → ⊥
no-reading publishing ()
no-reading flushing ()
no-reading ready ()
no-reading closed ()

-- Source callback selection still occurs before true-flag publication.
selection-before-flag : ∀ {p s m t} → Step p s (nextReply m) t → quitFlag s ≡ false
selection-before-flag (choose _ _) = refl

-- The node callback contract excludes Canceled as an application result.
node-callback-normal : ∀ {s m t} → Step nodeNext s (nextReply m) t →
  Σ[ a ∈ Notification ] m ≡ normal a
node-callback-normal (choose {m = normal a} _ _) = a , refl
node-callback-normal (choose {m = canceled} _ ())

-- A Send retains exactly the selected reply value, including a normal selected before Quit.
selected-payload-retained : ∀ {p s m t} → Step p s (sendReply m) t → sender s ≡ selected m
selected-payload-retained (send _) = refl

-- Done remains possible only after all registered and current work is drained.
done-only-drained : ∀ {p s t} → Step p s sendDone t → s ≡ state doneReady 0 idle 0 true
done-only-drained finish = refl

-- No visible operation can reset the published flag.
step-flag : ∀ {p s a t} → Step p s a t → quitFlag s ≡ true → quitFlag t ≡ true
step-flag (receiveRequest _) ()
step-flag (receiveQuit _) ()
step-flag (choose _ _) ()
step-flag (send _) flag = flag
step-flag finish _ = refl

-- Inspection, optional collection and scheduling also retain the published flag.
tau-flag : ∀ {s t} → Tau s t → quitFlag s ≡ true → quitFlag t ≡ true
tau-flag admitted flag = flag
tau-flag excessive flag = flag
tau-flag (inspectZero _) flag = flag
tau-flag (inspectPositive _) flag = flag
tau-flag pollHit flag = flag
tau-flag (pollMiss _) flag = flag
tau-flag registered flag = flag
tau-flag setQuit ()
tau-flag (claim _) flag = flag
tau-flag (cancel _) _ = refl
tau-flag (retire _) flag = flag
tau-flag flush flag = flag
tau-flag drained _ = refl
tau-flag abort flag = flag

-- The true-flag invariant holds at every later finite source prefix.
run-flag : ∀ {p s actions t} → Run p s actions t → quitFlag s ≡ true → quitFlag t ≡ true
run-flag stop flag = flag
run-flag (internal pr run) flag = run-flag run (tau-flag pr flag)
run-flag (visible pr run) flag = run-flag run (step-flag pr flag)

-- After publication no new application callback selection is available.
no-callback-after-flag : ∀ {p s m t} → Step p s (nextReply m) t → quitFlag s ≡ true → ⊥
no-callback-after-flag (choose _ _) ()

-- Any newly selected reply from claimed control after publication is Canceled.
new-selection-canceled : ∀ {s t m} → Tau s t → quitFlag s ≡ true →
  sender s ≡ claimed → sender t ≡ selected m → m ≡ canceled
new-selection-canceled admitted _ refl ()
new-selection-canceled excessive _ refl ()
new-selection-canceled (inspectZero _) _ refl ()
new-selection-canceled (inspectPositive _) _ refl ()
new-selection-canceled pollHit _ refl ()
new-selection-canceled (pollMiss _) _ refl ()
new-selection-canceled registered _ refl ()
new-selection-canceled setQuit () _ _
new-selection-canceled (claim _) _ () _
new-selection-canceled (cancel _) _ _ refl = refl
new-selection-canceled (retire _) _ () _
new-selection-canceled flush _ refl ()
new-selection-canceled drained _ () _
new-selection-canceled abort _ refl ()
