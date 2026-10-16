{-# OPTIONS --safe #-}

-- Boundary, refill, agency and session-isolation tests for Notify credits.
module Cardano_network.Replay.LeiosNotifyPipelineTests where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)
open import Relation.Nullary using (¬_)
open import Cardano_network.Replay.LeiosNotifySession using (RequestNext; Votes; Done; BlockOffer; BlockTxsOffer; BlockAnnouncement)
open import Cardano_network.Replay.LeiosNotifyPipeline
open import Cardano_network.Replay.SessionReport using (reportWithDepth; reportNotifyWithDepth)

-- Fill a depth-two pipe, partially collect, refill, drain, and close.
refill : List E
refill = (Send , RequestNext) ∷ (Send , RequestNext) ∷ (Recv , Votes [])
       ∷ (Send , RequestNext) ∷ (Recv , BlockOffer 7 2 10)
       ∷ (Recv , BlockTxsOffer 8 3) ∷ (Send , Done) ∷ []

-- Acceptance produces an inhabited trace, not just a boolean result.
refill-run : Spec.HasTrace 2 client idle refill
refill-run = toWitness {a? = Spec.check 2 client refill} tt

-- The same trace really needs depth two.
refill-too-deep : ¬ Spec.HasTrace 1 client idle refill
refill-too-deep = toWitnessFalse {a? = Spec.check 1 client refill} tt

-- A third uncollected request exceeds depth two.
overflow : False (Spec.check 2 client ((Send , RequestNext) ∷ (Send , RequestNext) ∷ (Send , RequestNext) ∷ []))
overflow = tt

-- Responder-side requests share the same bound.
server-overflow : False (Spec.check 2 server ((Recv , RequestNext) ∷ (Recv , RequestNext) ∷ (Recv , RequestNext) ∷ []))
server-overflow = tt

-- The responder may supply different notification kinds for its credits.
server-rounds : True (Spec.check 2 server ((Recv , RequestNext) ∷ (Recv , RequestNext) ∷ (Send , BlockAnnouncement nothing) ∷ (Send , Votes []) ∷ (Recv , Done) ∷ []))
server-rounds = tt

-- A notification cannot consume a nonexistent credit.
underflow : False (Spec.check 2 client ((Send , RequestNext) ∷ (Recv , Votes []) ∷ (Recv , Votes []) ∷ []))
underflow = tt

-- Pending credits prohibit Done, even below capacity.
busy-done : False (Spec.check 2 client ((Send , RequestNext) ∷ (Send , Done) ∷ []))
busy-done = tt

-- Closed sessions cannot reopen.
closed-request : False (Spec.check 2 client ((Send , Done) ∷ (Send , RequestNext) ∷ []))
closed-request = tt

-- Zero means no requests, rather than unlimited capacity.
zero-request : False (Spec.check 0 client ((Send , RequestNext) ∷ []))
zero-request = tt

-- Zero still permits closing an empty session.
zero-done : True (Spec.check 0 client ((Send , Done) ∷ []))
zero-done = tt

-- EOF may leave the pipe full.
full-prefix : True (Spec.check 2 client ((Send , RequestNext) ∷ (Send , RequestNext) ∷ []))
full-prefix = tt

-- Notify depth and Fetch depth are independent and local to each session.
mixed-depths : reportWithDepth 1 2 "sessions notify:client fetch:client notify:server\n0 Send RequestNext\n0 Send RequestNext\n1 Send BlockRequest ab 3\n2 Recv RequestNext\n2 Recv RequestNext\n0 Recv Votes -\n1 Recv Block ab 20\n2 Send Votes -\n" ≡ "accepted (8 events, 3 sessions)"
mixed-depths = refl

-- A request on one Notify session cannot license another's reply.
isolation : reportWithDepth 1 2 "sessions notify:client notify:client\n0 Send RequestNext\n1 Recv Votes -\n" ≡ "rejected at index 2 (session 1): Recv Votes -\nmodel session state after 1 events: notify client open, outstanding 0"
isolation = refl

-- Overflow diagnostics expose the actual outstanding count.
diagnostic : reportNotifyWithDepth 2 "role client\nSend RequestNext\nSend RequestNext\nSend RequestNext\n" ≡ "rejected at index 3 (session 0): Send RequestNext\nmodel session state after 2 events: notify client open, outstanding 2"
diagnostic = refl
