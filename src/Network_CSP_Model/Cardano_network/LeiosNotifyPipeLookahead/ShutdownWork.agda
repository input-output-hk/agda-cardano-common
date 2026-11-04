{-# OPTIONS --safe #-}

-- Once both peers are stopping, the same potential bounds all remaining model operations.
module Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork
  (Notification Return : Set) where

open import Data.Bool using (true)
open import Data.List using (length)
open import Data.Nat using (ℕ; suc; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; +-monoʳ-<)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.ClientShutdown Notification Return as Client
import Cardano_network.LeiosNotifyPipeLookahead.Properties Notification as Server
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingArithmetic as A
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingRank Notification Return as Rank
open import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification Return

-- Both role-specific shutdown paths have begun; this is stronger than either endpoint's Quit.
BothStopping : D.State → Set
BothStopping raw = (Client.stopping (C.main (D.clientState raw)) ≡ true) ×
  (Server.stopping (S.reader (D.serverState raw)) ≡ true)

-- Visible progress cannot return either endpoint to request issuance/acceptance.
step-stays : ∀ {p s row t} → D.Step p s row t → BothStopping s → BothStopping t
step-stays (D.clientSent pr) (client , server) = Client.step-stopping pr client , server
step-stays (D.serverSent pr) (client , server) = client , Server.step-stopping pr server
step-stays (D.clientReceived pr) (client , server) = Client.step-stopping pr client , server
step-stays (D.serverReceived pr) (client , server) = client , Server.step-stopping pr server

-- Hidden callbacks, scheduling and transport preserve those same control predicates.
tau-stays : ∀ {p s t} → D.Tau p s t → BothStopping s → BothStopping t
tau-stays (D.clientInternal pr) (client , server) = Client.tau-stopping pr client , server
tau-stays (D.serverInternal pr) (client , server) = client , Server.tau-stopping pr server
tau-stays (D.clientCallback _ pr) (client , server) = Client.step-stopping pr client , server
tau-stays (D.serverCallback pr) (client , server) = client , Server.step-stopping pr server
tau-stays (D.commitClient _) both = both
tau-stays (D.commitServer _) both = both
tau-stays (D.decodeClient _) both = both
tau-stays (D.decodeServer _) both = both

-- Shutdown wire records consume potential; receiving an earlier queued request is excluded here.
visible-decreases : ∀ {p s row t} → D.Step p s row t → BothStopping s → rank t < rank s
visible-decreases (D.clientSent {m = D.request} C.sentRequest) (() , _)
visible-decreases (D.clientSent {s = s} {cs = cs} {sc = sc} {m = D.quit} {ps = ps} {rc = rc}
  (C.sentQuitIdle {r} {js} {rs = rs})) _ = Rank.drop 0
    (A.quit-idle (length js) (length rs) (receiverCost r) (serverCost s)
      (length cs) (length sc) (sendBudget 9 ps) (receiveBudget rc))
visible-decreases (D.clientSent {s = s} {cs = cs} {sc = sc} {m = D.quit} {ps = ps} {rc = rc}
  (C.sentQuitBusy {r} {js} {rs = rs} {n})) _ = Rank.drop 0
    (A.quit-busy n (length js) (length rs) (receiverCost r) (serverCost s)
      (length cs) (length sc) (sendBudget 9 ps) (receiveBudget rc))
visible-decreases (D.serverSent {c = c} {cs = cs} {sc = sc} {pc = pc} {m = D.reply msg} {rc = rc}
  (S.send {r} {w} {c = completed} _)) _ = Rank.drop 0
    (A.send-reply (clientCost c) (readerCost r) w completed (length cs) (length sc)
      (sendBudget 2 pc) (receiveBudget rc))
visible-decreases (D.serverSent {c = c} {cs = cs} {sc = sc} {pc = pc} {m = D.done} {rc = rc} S.finish) _ = Rank.drop 0
  (A.send-done (clientCost c) (length cs) (length sc) (sendBudget 2 pc) (receiveBudget rc))
visible-decreases (D.clientReceived {s = s} {cs = cs} {sc = sc} {pc = pc} {ps = ps} {m = D.reply msg}
  (C.receivedReply {m} {js} {rs = rs} {n} _)) _ = Rank.drop 1
    (A.receive-reply n (length js) (length rs) (mainCost m) (serverCost s)
      (length cs) (length sc) (sendBudget 2 pc) (sendBudget 9 ps))
visible-decreases (D.clientReceived {c = c} {s = s} {cs = cs} {sc = sc} {pc = pc} {ps = ps} {m = D.done} C.receivedDone) _ =
  +-monoʳ-< (clientCost c) (+-monoʳ-< (serverCost s)
    (Rank.drop 6 (A.receive-done (length cs) (length sc) (sendBudget 2 pc) (sendBudget 9 ps))))
visible-decreases (D.serverReceived {m = D.request} (S.receiveRequest S.atFirst)) (_ , ())
visible-decreases (D.serverReceived {m = D.request} (S.receiveRequest S.atNext)) (_ , ())
visible-decreases (D.serverReceived {m = D.quit} (S.receiveQuit S.atFirst)) (_ , ())
visible-decreases (D.serverReceived {m = D.quit} (S.receiveQuit S.atNext)) (_ , ())

-- Count actual internal and visible operations in a supplied finite execution.
steps : ∀ {p s rows t} → D.Run p s rows t → ℕ
steps D.stop = 0
steps (D.internal _ run) = suc (steps run)
steps (D.visible _ run) = suc (steps run)

-- Every finite shutdown continuation consumes at least one unit per actual model operation.
bounded : ∀ {p s rows t} (run : D.Run p s rows t) → BothStopping s → steps run ≤ rank s
bounded D.stop _ = z≤n
bounded (D.internal pr run) both =
  ≤-trans (s≤s (bounded run (tau-stays pr both))) (Rank.decreases pr)
bounded (D.visible pr run) both =
  ≤-trans (s≤s (bounded run (step-stays pr both))) (visible-decreases pr both)

-- The diagnostic view keeps replies owed, completion tokens and receiver work distinct.
record Work : Set where
  constructor work
  field
    owedReplies : ℕ
    completionTokens : ℕ
    unretiredSend : ℕ
    clientInFlight : ℕ
    potential : ℕ

-- A sent reply owes nothing on the wire but still requires retirement and later flushing.
unretired : S.Sender → ℕ
unretired S.sent = 1
unretired _ = 0

-- These computed quantities are observations of the same state, not extra transition assumptions.
remaining : D.State → Work
remaining raw = work (S.owed (D.serverState raw)) (S.completed (D.serverState raw))
  (unretired (S.sender (D.serverState raw))) (C.inFlight (D.clientState raw)) (rank raw)
