{-# OPTIONS --guardedness #-}

-- Exact physical FIFO origin of every newly captured DeltaQ ticket.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.MuxDeltaQCapture (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.MuxDeltaQ as Delta
module D = Delta isBearerClosed
module R = D.R
module X = D.X
module W = D.W
module G = D.G
module M = D.M
import ConnectionManagement.Properties.MuxDeltaQ as DeltaFacts
module Facts = DeltaFacts isBearerClosed
import ConnectionManagement.Properties.MuxStartupUnwind as UnwindFacts
module Base = UnwindFacts isBearerClosed
import ConnectionManagement.Properties.MuxResultMonitor as MonitorFacts
module Monitor = MonitorFacts isBearerClosed

-- Peel only the cheap component guards; the result-consumer certificate is
-- reused instead of normalizing the full composed-system transition.
group-dequeue : ∀ w g {g′} → G.step (G.run (M.consume w)) g ≡ just g′ →
  Monitor.Dequeue w (G.base g) (G.base g′)
group-dequeue w g eq with G.delegateAllowed (M.consume w) g
... | false = case eq of λ ()
... | true with M.step (M.consume w) (G.base g) in consumed
...   | nothing = case eq of λ ()
...   | just m = case just-injective eq of λ { refl → Monitor.consume-observation w (G.base g) consumed }
exit-dequeue : ∀ w x {x′} → W.step (W.run (G.run (M.consume w))) x ≡ just x′ →
  Monitor.Dequeue w (G.base (W.base x)) (G.base (W.base x′))
exit-dequeue w x eq with G.step (G.run (M.consume w)) (W.base x) in consumed
... | nothing = case eq of λ ()
... | just g = case just-injective eq of λ { refl → group-dequeue w (W.base x) consumed }
lower-dequeue : ∀ w r {r′} → R.step (D.wrapMonitor (M.consume w)) r ≡ just r′ →
  Monitor.Dequeue w (G.base (W.base (R.base r))) (G.base (W.base (R.base r′)))
lower-dequeue w r eq with Base.inherited-observation (X.run (W.run (G.run (M.consume w)))) r eq
... | x , consumed , refl = exit-dequeue w (R.base r) consumed
note-view : ∀ w r ts item → M.pcAt w (G.base (W.base (R.base r))) ≡ M.selected item →
  D.note (D.wrapMonitor (M.consume w)) r ts ≡ put w (D.ticket item D.captured) ts
note-view w r ts item eq rewrite eq = refl

record CapturedHead (w : WorkerId) (before after : D.State) : Set where
  constructor capturedHead
  field dequeue : Monitor.Dequeue w (D.monitor before) (D.monitor after)
        ticket-after : lookup w (D.tickets after) ≡ just (D.ticket (Monitor.head dequeue) D.captured)
consume-captures-head : ∀ w s {s′} → D.step (D.run (D.wrapMonitor (M.consume w))) s ≡ just s′ → CapturedHead w s s′
consume-captures-head w s eq with Facts.inherited-observation (D.wrapMonitor (M.consume w)) s eq
... | r , consumed , refl with lower-dequeue w (D.base s) consumed
...   | observation rewrite note-view w r (D.tickets s) (Monitor.head observation) (Monitor.captured-after observation) =
  capturedHead observation (lookup-put w (D.ticket (Monitor.head observation) D.captured) (D.tickets s))
