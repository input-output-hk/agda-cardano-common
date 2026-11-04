{-# OPTIONS --safe #-}

-- All hidden product steps decrease, including callbacks with unbounded data domains.
module Cardano_network.LeiosNotifyPipeLookahead.SchedulingRank
  (Notification Return : Set) where

open import Data.List using (length)
open import Data.Nat using (ℕ; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (m<m+n; +-monoˡ-<; +-monoʳ-<)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Notification Return as Accounting
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingArithmetic as A
open import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification Return

-- A positive exact amount consumed gives the strict natural-number decrease.
drop : ∀ {after before} (extra : ℕ) → after + suc extra ≡ before → after < before
drop {after} extra equal = subst (after <_) equal (m<m+n after (s≤s z≤n))

-- All seventeen client scheduling operations consume their assigned credits.
client-decreases : ∀ {s t} → C.Tau s t → clientCost t < clientCost s
client-decreases (C.registerResponse {r} {js} {rs = rs} {n})
  rewrite Accounting.snoc-length js C.responseJob = drop 0 (A.client-register n (length js) (length rs) 0 (receiverCost r))
client-decreases (C.setStopIdle {r} {js} {rs = rs}) = drop 8 (A.client-main 0 (length js) (length rs) 3 (receiverCost r) 8)
client-decreases (C.setStopBusy {r} {js} {rs = rs} {n}) = drop 0 (A.client-main (suc n) (length js) (length rs) 11 (receiverCost r) 0)
client-decreases (C.registerMarker {r} {js} {rs = rs} {n})
  rewrite Accounting.snoc-length js C.quitMarker = drop 0 (A.client-register n (length js) (length rs) 7 (receiverCost r))
client-decreases (C.optionalEmpty {r} {js} {n}) = drop 7 (A.client-main (suc n) (length js) 0 4 (receiverCost r) 7)
client-decreases (C.optionalResult {r} {js} {rs = rs} {n}) = drop 1 (A.client-collect n (length js) (length rs) (receiverCost r))
client-decreases (C.blockingResult {r} {js} {rs = rs} {n}) = drop 1 (A.client-collect n (length js) (length rs) (receiverCost r))
client-decreases (C.adjustArrival {r} {js} {rs = rs} {n}) = drop 0 (A.client-main n (length js) (length rs) 13 (receiverCost r) 0)
client-decreases (C.drainResult {r} {js} {rs = rs} {n}) = drop 3 (A.client-drain n (length js) (length rs) 1 (receiverCost r))
client-decreases (C.drained {r} {js} {rs = rs}) = drop 0 (A.client-main 0 (length js) (length rs) 0 (receiverCost r) 0)
client-decreases (C.startResponse {m} {js} {rs = rs} {n} _) = drop 2 (A.client-start-response n (length js) (length rs) (mainCost m))
client-decreases (C.startMarker {m} {js} {rs = rs} {n} _) = drop 0 (A.client-start-marker n (length js) (length rs) (mainCost m))
client-decreases (C.keepReply {m} {js} {rs = rs} {n} _) = drop 0 (A.client-receiver n (length js) (length rs) (mainCost m) 4 0)
client-decreases (C.discardReply {m} {js} {rs = rs} {n} _) = drop 1 (A.client-receiver n (length js) (length rs) (mainCost m) 3 1)
client-decreases (C.countArrival {m} {js} {rs = rs} {n} _) = drop 0 (A.client-receiver n (length js) (length rs) (mainCost m) 2 0)
client-decreases (C.publishResponse {m} {js} {rs = rs} {n} _)
  rewrite Accounting.snoc-length rs C.responseToken = drop 0 (A.client-publish n (length js) (length rs) (mainCost m))
client-decreases (C.publishMarker {m} {js} {rs = rs} {n} _)
  rewrite Accounting.snoc-length rs C.markerToken = drop 0 (A.client-publish n (length js) (length rs) (mainCost m))

-- Hidden decisions and successful handlers consume client control credits too.
client-callback : ∀ {s a t} → D.ClientCallback a → C.Step s a t → clientCost t < clientCost s
client-callback D.continue (C.continueZero {r} {js} {rs = rs}) = drop 8 (A.client-main 0 (length js) (length rs) 4 (receiverCost r) 8)
client-callback D.continue (C.continueBelow {r} {js} {rs = rs} {n} _) = drop 0 (A.client-main (suc n) (length js) (length rs) 12 (receiverCost r) 0)
client-callback D.continue (C.continueFull {r} {js} {rs = rs} {n} _ _) = drop 0 (A.client-main (suc n) (length js) (length rs) 12 (receiverCost r) 0)
client-callback D.terminate (C.stopRequested {r} {js} {rs = rs} {n}) = drop 0 (A.client-main n (length js) (length rs) 12 (receiverCost r) 0)
client-callback D.handled (C.delivered {m} {js} {rs = rs} {n} _) = drop 0 (A.client-receiver n (length js) (length rs) (mainCost m) 3 0)

-- Server registration and completion bookkeeping consume server credits.
server-decreases : ∀ {s t} → S.Tau s t → serverCost t < serverCost s
server-decreases (S.admitted {w} {s} {c}) = drop 0 (A.server-reader 15 w (senderCost s) c 0)
server-decreases (S.excessive {w} {s} {c}) = drop 14 (A.server-reader 1 w (senderCost s) c 14)
server-decreases (S.registered {w} {s} {c}) = drop 0 (A.server-register w (senderCost s) c)
server-decreases (S.setQuit {w} {s} {c}) = drop 0 (A.server-reader 11 w (senderCost s) c 0)
server-decreases (S.claim {r} {w} {c} _) = drop 0 (A.server-claim (readerCost r) w c)
server-decreases (S.cancel {r} {w} {c} _) = drop 0 (A.server-sender (readerCost r) w 12 c 0)
server-decreases (S.retire {r} {w} {c} _) = drop 0 (A.server-retire (readerCost r) w c)
server-decreases (S.flush {w} {s} {c}) = drop 0 (A.server-flush 11 w (senderCost s) c)
server-decreases S.drained = drop 0 (A.server-reader 10 0 0 0 0)
server-decreases (S.abort {w} {s} {c}) = drop 0 (A.server-reader 0 w (senderCost s) c 0)

-- Explicit next-result callbacks decrease even for infinite payload domains.
server-callback : ∀ {p s msg t} → S.Step p s (S.nextReply msg) t → serverCost t < serverCost s
server-callback (S.choose {r} {w} {c} _ _) = drop 0 (A.server-sender (readerCost r) w 12 c 0)

-- Every hidden paired transition consumes potential, not merely a selector index.
decreases : ∀ {p s t} → D.Tau p s t → rank t < rank s
decreases (D.clientInternal {c = c} {s = s} {cs = cs} {sc = sc} {pc = pc} {ps = ps} {rc = rc} {rs = rs} pr) =
  +-monoˡ-< (serverCost s + transportCost (D.pair c s cs sc pc ps rc rs)) (client-decreases pr)
decreases (D.serverInternal {c = c} {s = s} {cs = cs} {sc = sc} {pc = pc} {ps = ps} {rc = rc} {rs = rs} pr) =
  +-monoʳ-< (clientCost c) (+-monoˡ-< (transportCost (D.pair c s cs sc pc ps rc rs)) (server-decreases pr))
decreases (D.clientCallback {c = c} {s = s} {cs = cs} {sc = sc} {pc = pc} {ps = ps} {rc = rc} {rs = rs} callback pr) =
  +-monoˡ-< (serverCost s + transportCost (D.pair c s cs sc pc ps rc rs)) (client-callback callback pr)
decreases (D.serverCallback {c = c} {s = s} {cs = cs} {sc = sc} {pc = pc} {ps = ps} {rc = rc} {rs = rs} pr) =
  +-monoʳ-< (clientCost c) (+-monoˡ-< (transportCost (D.pair c s cs sc pc ps rc rs)) (server-callback pr))
decreases (D.commitClient {c = c} {s = s} {cs = cs} {sc = sc} {ps = ps} {rc = rc} {rs = rs} {m} pr)
  rewrite Accounting.snoc-length cs m = +-monoʳ-< (clientCost c) (+-monoʳ-< (serverCost s)
    (drop 0 (A.commit-client (length cs) (length sc) (sendBudget 9 ps) (receiveBudget rc))))
decreases (D.commitServer {c = c} {s = s} {cs = cs} {sc = sc} {pc = pc} {rc = rc} {rs = rs} {m} pr)
  rewrite Accounting.snoc-length sc m = +-monoʳ-< (clientCost c) (+-monoʳ-< (serverCost s)
    (drop 0 (A.commit-server (length cs) (length sc) (sendBudget 2 pc) (receiveBudget rc))))
decreases (D.decodeClient {c = c} {s = s} {cs = cs} {sc = sc} {pc = pc} {ps = ps} {rs = rs} pr) =
  +-monoʳ-< (clientCost c) (+-monoʳ-< (serverCost s)
    (drop 0 (A.decode-client (length cs) (length sc) (sendBudget 2 pc) (sendBudget 9 ps))))
decreases (D.decodeServer {c = c} {s = s} {cs = cs} {sc = sc} {pc = pc} {ps = ps} {rc = rc} pr) =
  +-monoʳ-< (clientCost c) (+-monoʳ-< (serverCost s)
    (drop 0 (A.decode-server (length cs) (length sc) (sendBudget 2 pc) (sendBudget 9 ps) (receiveBudget rc))))

-- Natural well-foundedness supplies accessibility for every product state.
from-rank : ∀ p s → Acc _<_ (rank s) → Acc (λ t s → D.Tau p s t) s
from-rank p s (acc smaller) = acc λ {t} step → from-rank p t (smaller (decreases step))

-- Finite branching and reachable-state assumptions are unnecessary for hidden termination.
tau-accessible : ∀ p s → Acc (λ t s → D.Tau p s t) s
tau-accessible p s = from-rank p s (<-wellFounded (rank s))
