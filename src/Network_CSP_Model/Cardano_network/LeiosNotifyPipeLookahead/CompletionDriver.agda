{-# OPTIONS --safe #-}

-- Completion work and exact flush counts at the actual paired driver-record boundary.
module Cardano_network.LeiosNotifyPipeLookahead.CompletionDriver
  (Notification Return : Set) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_,_)
open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-mono-≤; ≤-trans; n≤1+n; m≤n+m; m≤m+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.CompletionAccounting Notification as Source
import Cardano_network.LeiosNotifyPipeLookahead.Properties Notification as Control
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification Return as Operations
import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Notification Return as Endpoint

-- Driver work is the actual server source work, including sent-but-unretired replies.
work : D.State → ℕ
work raw = Source.work (D.serverState raw)

-- Only the server RequestNext Receive adds another completion obligation.
request : D.Event → ℕ
request (D.serverRecv D.request) = 1
request _ = 0

-- Count original server request records without reinterpreting commits or client Sends.
requests : List D.Event → ℕ
requests [] = 0
requests (row ∷ rows) = request row + requests rows

-- Exactly the hidden source flush contributes one paired flush occurrence.
flush-step : ∀ {p s t} → D.Tau p s t → ℕ
flush-step (D.serverInternal pr) = Source.flush-step pr
flush-step _ = 0

-- Physical transport and unrelated work contribute no invented completion flushes.
flushes : ∀ {p s rows t} → D.Run p s rows t → ℕ
flushes D.stop = 0
flushes (D.internal pr run) = flush-step pr + flushes run
flushes (D.visible pr run) = flushes run

-- Source work changes only at the source operations certified by CompletionAccounting.
tau-work : ∀ {p s t} (pr : D.Tau p s t) → work s ≡ flush-step pr + work t
tau-work (D.clientInternal _) = refl
tau-work (D.serverInternal pr) = Source.tau-work pr
tau-work (D.clientCallback _ _) = refl
tau-work (D.serverCallback (S.choose _ _)) = refl
tau-work (D.commitClient _) = refl
tau-work (D.commitServer _) = refl
tau-work (D.decodeClient _) = refl
tau-work (D.decodeServer _) = refl

-- Wire observations retain the source distinction between replies, requests and retirement.
step-work : ∀ {p s row t} → D.Step p s row t → work s + request row ≡ work t
step-work (D.clientSent {s = s} _) = +-identityʳ (Source.work s)
step-work (D.clientReceived {s = s} _) = +-identityʳ (Source.work s)
step-work (D.serverSent {m = D.reply _} pr) = Source.step-work pr
step-work (D.serverSent {m = D.done} pr) = Source.step-work pr
step-work (D.serverReceived {m = D.request} pr) = Source.step-work pr
step-work (D.serverReceived {m = D.quit} pr) = Source.step-work pr

-- Actual paired runs preserve initial work plus requests as flushes plus final work.
run-balance : ∀ {p s rows t} (run : D.Run p s rows t) →
  work s + requests rows ≡ flushes run + work t
run-balance D.stop = +-identityʳ _
run-balance (D.internal {t = t} {u = u} {es = rows} pr run) =
  trans (cong (_+ requests rows) (tau-work pr))
    (trans (+-assoc (flush-step pr) (work t) (requests rows))
      (trans (cong (flush-step pr +_) (run-balance run))
        (sym (+-assoc (flush-step pr) (flushes run) (work u)))))
run-balance (D.visible {s = s} {e = row} {es = rows} pr run) =
  trans (sym (+-assoc (work s) (request row) (requests rows)))
    (trans (cong (_+ requests rows) (step-work pr)) (run-balance run))

-- Exact server closure empties all completion work even when client work remains.
closed-flushes : ∀ {p s rows t} (run : D.Run p s rows t) →
  D.serverState t ≡ S.state S.closed 0 S.idle 0 true → flushes run ≡ work s + requests rows
closed-flushes run closed = sym (trans (run-balance run)
  (trans (cong (flushes run +_) (cong Source.work closed)) (+-identityʳ (flushes run))))

-- Every historical request in a fresh server-closing paired run has one actual hidden flush.
fresh-closed-flushes : ∀ {p rows t} (run : D.Run p D.initial rows t) →
  D.serverState t ≡ S.state S.closed 0 S.idle 0 true → flushes run ≡ requests rows
fresh-closed-flushes = closed-flushes

-- Visible records cannot reopen the server's successful shutdown control.
step-stopping : ∀ {p s row t} → D.Step p s row t →
  Control.stopping (S.reader (D.serverState s)) ≡ true → Control.stopping (S.reader (D.serverState t)) ≡ true
step-stopping (D.clientSent _) stopping = stopping
step-stopping (D.clientReceived _) stopping = stopping
step-stopping (D.serverSent pr) stopping = Control.step-stopping pr stopping
step-stopping (D.serverReceived pr) stopping = Control.step-stopping pr stopping

-- Scheduling, callbacks and transport preserve the same server shutdown predicate.
tau-stopping : ∀ {p s t} → D.Tau p s t →
  Control.stopping (S.reader (D.serverState s)) ≡ true → Control.stopping (S.reader (D.serverState t)) ≡ true
tau-stopping (D.clientInternal _) stopping = stopping
tau-stopping (D.serverInternal pr) stopping = Control.tau-stopping pr stopping
tau-stopping (D.clientCallback _ _) stopping = stopping
tau-stopping (D.serverCallback pr) stopping = Control.step-stopping pr stopping
tau-stopping (D.commitClient _) stopping = stopping
tau-stopping (D.commitServer _) stopping = stopping
tau-stopping (D.decodeClient _) stopping = stopping
tau-stopping (D.decodeServer _) stopping = stopping

-- A server already stopping cannot receive another request record.
row-no-request : ∀ {p s row t} → D.Step p s row t →
  Control.stopping (S.reader (D.serverState s)) ≡ true → request row ≡ 0
row-no-request (D.clientSent _) stopping = refl
row-no-request (D.clientReceived _) stopping = refl
row-no-request (D.serverSent _) stopping = refl
row-no-request (D.serverReceived {m = D.quit} _) stopping = refl
row-no-request (D.serverReceived {m = D.request} (S.receiveRequest S.atFirst)) ()
row-no-request (D.serverReceived {m = D.request} (S.receiveRequest S.atNext)) ()

-- All remaining paired request counts are zero once the server has received Quit.
no-requests : ∀ {p s rows t} (run : D.Run p s rows t) →
  Control.stopping (S.reader (D.serverState s)) ≡ true → requests rows ≡ 0
no-requests D.stop stopping = refl
no-requests (D.internal pr run) stopping = no-requests run (tau-stopping pr stopping)
no-requests (D.visible pr run) stopping rewrite row-no-request pr stopping =
  no-requests run (step-stopping pr stopping)

-- Any successful paired shutdown schedule flushes exactly the initial source work.
shutdown-flushes : ∀ {p s rows t} (run : D.Run p s rows t) →
  Control.stopping (S.reader (D.serverState s)) ≡ true →
  D.serverState t ≡ S.state S.closed 0 S.idle 0 true → flushes run ≡ work s
shutdown-flushes {s = s} run stopping closed = trans (closed-flushes run closed)
  (trans (cong (work s +_) (no-requests run stopping)) (+-identityʳ (work s)))

-- Each actual hidden paired operation can contribute at most one source flush.
flush-step≤1 : ∀ {p s t} (pr : D.Tau p s t) → flush-step pr ≤ 1
flush-step≤1 (D.serverInternal pr) = Source.flush-step≤1 pr
flush-step≤1 (D.clientInternal _) = z≤n
flush-step≤1 (D.clientCallback _ _) = z≤n
flush-step≤1 (D.serverCallback _) = z≤n
flush-step≤1 (D.commitClient _) = z≤n
flush-step≤1 (D.commitServer _) = z≤n
flush-step≤1 (D.decodeClient _) = z≤n
flush-step≤1 (D.decodeServer _) = z≤n

-- Flush work lower-bounds actual paired operations, not only local server scheduling.
flushes≤steps : ∀ {p s rows t} (run : D.Run p s rows t) → flushes run ≤ Operations.steps run
flushes≤steps D.stop = z≤n
flushes≤steps (D.internal pr run) = +-mono-≤ (flush-step≤1 pr) (flushes≤steps run)
flushes≤steps (D.visible pr run) = ≤-trans (flushes≤steps run) (n≤1+n (Operations.steps run))

-- Existing completion history alone imposes a lower bound on every successful paired shutdown.
completed-lower-bound : ∀ {p s rows t} (run : D.Run p s rows t) →
  Control.stopping (S.reader (D.serverState s)) ≡ true →
  D.serverState t ≡ S.state S.closed 0 S.idle 0 true →
  S.completed (D.serverState s) ≤ Operations.steps run
completed-lower-bound {s = s} run stopping closed = ≤-trans
  (≤-trans (m≤n+m (S.completed (D.serverState s)) (Source.unretired (S.sender (D.serverState s))))
    (m≤n+m (Source.unretired (S.sender (D.serverState s)) + S.completed (D.serverState s)) (S.owed (D.serverState s))))
  (subst (_≤ Operations.steps run) (shutdown-flushes run stopping closed) (flushes≤steps run))

-- Any later successful server close must discharge the existing history, even with intervening requests.
completed-closing-lower-bound : ∀ {p s rows t} (run : D.Run p s rows t) →
  D.serverState t ≡ S.state S.closed 0 S.idle 0 true →
  S.completed (D.serverState s) ≤ Operations.steps run
completed-closing-lower-bound {s = s} {rows} run closed = ≤-trans
  (≤-trans (m≤n+m (S.completed (D.serverState s)) (Source.unretired (S.sender (D.serverState s))))
    (m≤n+m (Source.unretired (S.sender (D.serverState s)) + S.completed (D.serverState s)) (S.owed (D.serverState s))))
  (≤-trans (m≤m+n (work s) (requests rows))
    (subst (_≤ Operations.steps run) (closed-flushes run closed) (flushes≤steps run)))

-- Arbitrary client/transport work cannot reopen a source server after its Done Send record.
closed-stays : ∀ {p s rows t} → D.Run p s rows t →
  D.serverState s ≡ S.state S.closed 0 S.idle 0 true → D.serverState t ≡ S.state S.closed 0 S.idle 0 true
closed-stays {p} {t = t} run closed with Endpoint.For.server p run
... | actions , source , matching = Source.closed-stays
  (subst (λ start → S.Run p start actions (D.serverState t)) closed source)

-- A retained server Send-Done record certifies the final server shape at every later prefix.
seen-done : ∀ {p s rows t} → D.Run p s rows t → Any (λ row → row ≡ D.serverSend D.done) rows →
  D.serverState t ≡ S.state S.closed 0 S.idle 0 true
seen-done (D.internal pr run) observed = seen-done run observed
seen-done (D.visible (D.serverSent {m = D.done} S.finish) run) (here refl) = closed-stays run refl
seen-done (D.visible pr run) (there observed) = seen-done run observed
