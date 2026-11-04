{-# OPTIONS --safe #-}

-- Polynomial identities shared by the model-specific scheduling proofs.
module Cardano_network.LeiosNotifyPipeLookahead.SchedulingArithmetic where

open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Client counters, queues and control credits stay separate.
client : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
client n j r m u = 3 * n + (3 * j + (r + (m + u)))

-- Registration and completion bookkeeping have different weights.
server : ℕ → ℕ → ℕ → ℕ → ℕ
server r w s c = r + (14 * w + (s + c))

-- Queue energy and pending-hook budgets are explicit.
transport : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
transport cs sc pc ps rc = cs + (8 * sc + (pc + (ps + rc)))

-- Component costs compose without subtraction.
total : ℕ → ℕ → ℕ → ℕ
total c s t = c + (s + t)

-- Main control consumes its positive difference.
client-main : ∀ n j r m u k → ((3 * n + (3 * j + (r + (m + u)))) + (1 + k)) ≡ (3 * n + (3 * j + (r + ((m + (1 + k)) + u))))
client-main = solve-∀

-- Receiver control consumes its positive difference.
client-receiver : ∀ n j r m u k → ((3 * n + (3 * j + (r + (m + u)))) + (1 + k)) ≡ (3 * n + (3 * j + (r + (m + (u + (1 + k))))))
client-receiver = solve-∀

-- Registration creates one job using main-thread credits.
client-register : ∀ n j r m u → ((3 * n + (3 * (1 + j) + (r + (m + u)))) + 1) ≡ (3 * n + (3 * j + (r + ((m + 4) + u))))
client-register = solve-∀

-- Collection pays for returning to the decision phase.
client-collect : ∀ n j r u → ((3 * n + (3 * j + (r + (14 + u)))) + 2) ≡ (3 * (1 + n) + (3 * j + ((1 + r) + (12 + u))))
client-collect = solve-∀

-- Draining consumes both one result and its counter occurrence.
client-drain : ∀ n j r m u → ((3 * n + (3 * j + (r + (m + u)))) + 4) ≡ (3 * (1 + n) + (3 * j + ((1 + r) + (m + u))))
client-drain = solve-∀

-- Starting a wire receiver consumes one queued job.
client-start-response : ∀ n j r m → ((3 * n + (3 * j + (r + (m + 0)))) + 3) ≡ (3 * n + (3 * (1 + j) + (r + (m + 0))))
client-start-response = solve-∀

-- Starting a marker reserves its publication credits.
client-start-marker : ∀ n j r m → ((3 * n + (3 * j + (r + (m + 2)))) + 1) ≡ (3 * n + (3 * (1 + j) + (r + (m + 0))))
client-start-marker = solve-∀

-- Publication transfers receiver energy into a result token.
client-publish : ∀ n j r m → ((3 * n + (3 * j + ((1 + r) + (m + 0)))) + 1) ≡ (3 * n + (3 * j + (r + (m + 2))))
client-publish = solve-∀

-- Reader control pays for its positive change.
server-reader : ∀ r w s c k → ((r + (14 * w + (s + c))) + (1 + k)) ≡ ((r + (1 + k)) + (14 * w + (s + c)))
server-reader = solve-∀

-- Sender control pays for its positive change.
server-sender : ∀ r w s c k → ((r + (14 * w + (s + c))) + (1 + k)) ≡ (r + (14 * w + ((s + (1 + k)) + c)))
server-sender = solve-∀

-- Registration trades fifteen credits for fourteen job credits.
server-register : ∀ w s c → ((0 + (14 * (1 + w) + (s + c))) + 1) ≡ (15 + (14 * w + (s + c)))
server-register = solve-∀

-- Claiming transfers one job into the active sender.
server-claim : ∀ r w c → ((r + (14 * w + (13 + c))) + 1) ≡ (r + (14 * (1 + w) + (0 + c)))
server-claim = solve-∀

-- Retirement creates a completion token, rather than an owed reply.
server-retire : ∀ r w c → ((r + (14 * w + (0 + (1 + c)))) + 1) ≡ (r + (14 * w + (2 + c)))
server-retire = solve-∀

-- A flush consumes exactly one completion occurrence.
server-flush : ∀ r w s c → ((r + (14 * w + (s + c))) + 1) ≡ (r + (14 * w + (s + (1 + c))))
server-flush = solve-∀

-- Client commit spends its empty Send slot credits.
commit-client : ∀ cs sc ps rc → (((1 + cs) + (8 * sc + (0 + (ps + rc)))) + 1) ≡ (cs + (8 * sc + (2 + (ps + rc))))
commit-client = solve-∀

-- Server commit transfers nine credits into an eight-credit packet.
commit-server : ∀ cs sc pc rc → ((cs + (8 * (1 + sc) + (pc + (0 + rc)))) + 1) ≡ (cs + (8 * sc + (pc + (9 + rc))))
commit-server = solve-∀

-- Client decode transfers queue energy into its Receive hook.
decode-client : ∀ cs sc pc ps → ((cs + (8 * sc + (pc + (ps + 7)))) + 1) ≡ (cs + (8 * (1 + sc) + (pc + (ps + 0))))
decode-client = solve-∀

-- Server decode consumes its command queue head.
decode-server : ∀ cs sc pc ps rc → ((cs + (8 * sc + (pc + (ps + rc)))) + 1) ≡ ((1 + cs) + (8 * sc + (pc + (ps + rc))))
decode-server = solve-∀

-- Done receive clears seven pending-packet credits.
receive-done : ∀ cs sc pc ps → ((cs + (8 * sc + (pc + (ps + 0)))) + 7) ≡ (cs + (8 * sc + (pc + (ps + 7))))
receive-done = solve-∀

-- Idle Quit pays for reopening its Send slot.
quit-idle : ∀ j r u s cs sc ps rc → (((3 * 0 + (3 * j + (r + (0 + u)))) + (s + (cs + (8 * sc + (2 + (ps + rc)))))) + 1) ≡ ((3 * 0 + (3 * j + (r + (3 + u)))) + (s + (cs + (8 * sc + (0 + (ps + rc))))))
quit-idle = solve-∀

-- Busy Quit also pays for incrementing the marker counter.
quit-busy : ∀ n j r u s cs sc ps rc → (((3 * (1 + n) + (3 * j + (r + (1 + u)))) + (s + (cs + (8 * sc + (2 + (ps + rc)))))) + 1) ≡ ((3 * n + (3 * j + (r + (7 + u)))) + (s + (cs + (8 * sc + (0 + (ps + rc))))))
quit-busy = solve-∀

-- Reply receive transfers packet energy into inspect control.
receive-reply : ∀ n j r m s cs sc pc ps → (((3 * n + (3 * j + (r + (m + 5)))) + (s + (cs + (8 * sc + (pc + (ps + 0)))))) + 2) ≡ ((3 * n + (3 * j + (r + (m + 0)))) + (s + (cs + (8 * sc + (pc + (ps + 7))))))
receive-reply = solve-∀

-- Reply Send pays for reopening its nine-credit Send slot.
send-reply : ∀ c r w completed cs sc pc rc → ((c + ((r + (14 * w + (2 + completed))) + (cs + (8 * sc + (pc + (9 + rc)))))) + 1) ≡ (c + ((r + (14 * w + (12 + completed))) + (cs + (8 * sc + (pc + (0 + rc))))))
send-reply = solve-∀

-- Done Send trades reader credits for its empty Send slot.
send-done : ∀ c cs sc pc rc → ((c + ((0 + (14 * 0 + (0 + 0))) + (cs + (8 * sc + (pc + (9 + rc)))))) + 1) ≡ (c + ((10 + (14 * 0 + (0 + 0))) + (cs + (8 * sc + (pc + (0 + rc))))))
send-done = solve-∀

