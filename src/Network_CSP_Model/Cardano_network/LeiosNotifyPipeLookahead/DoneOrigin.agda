{-# OPTIONS --safe #-}

-- Every physical Done packet in a fresh product originates in a drained server.
module Cardano_network.LeiosNotifyPipeLookahead.DoneOrigin
  (Notification Return : Set) where

open import Data.List using (_∷_; _∷ʳ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.ServerShutdown Notification as Server

-- A source operation capable of committing Done is exactly the final drained send.
commit-final : ∀ {p s m t} → S.Step p s (D.serverSendAction m) t → m ≡ D.done → Server.Final s
commit-final {m = D.reply _} _ ()
commit-final {m = D.done} S.finish _ = Server.ready-final

-- Appending a packet preserves old origins and supplies the new Done origin explicitly.
queued-commit : ∀ {p s m t queue} → S.Step p s (D.serverSendAction m) t →
  (D.done ∈ queue → Server.Final s) → D.done ∈ (queue ∷ʳ m) → Server.Final s
queued-commit {queue = queue} pr old present with ∈-++⁻ queue present
... | inj₁ earlier = old earlier
... | inj₂ (here refl) = commit-final pr refl
... | inj₂ (there ())

-- The new pending Send slot carries the exact packet of the source operation.
sending-commit : ∀ {p s m t} → S.Step p s (D.serverSendAction m) t →
  just m ≡ just D.done → Server.Final s
sending-commit pr refl = commit-final pr refl

-- Done can be in the FIFO or either responder-packet hook, with the same source origin.
record Origin (raw : D.State) : Set where
  constructor origin
  field
    queued : D.done ∈ D.serverToClient raw → Server.Final (D.serverState raw)
    sending : D.pendingServerSend raw ≡ just D.done → Server.Final (D.serverState raw)
    receiving : D.pendingClientRecv raw ≡ just D.done → Server.Final (D.serverState raw)
open Origin public

-- Trace hooks preserve origins, including server Done's transition to closed control.
step-origin : ∀ {p s row t} → D.Step p s row t → Origin s → Origin t
step-origin (D.clientSent _) (origin q s r) = origin q s r
step-origin (D.clientReceived _) (origin q s r) = origin q s (λ ())
step-origin (D.serverSent pr) (origin q s r) = origin
  (λ present → Server.step-final pr (q present)) (λ ())
  (λ pending → Server.step-final pr (r pending))
step-origin (D.serverReceived pr) (origin q s r) = origin
  (λ present → Server.step-final pr (q present))
  (λ pending → Server.step-final pr (s pending))
  (λ pending → Server.step-final pr (r pending))

-- Commit creates the origin; decode transfers it from the FIFO into the Receive hook.
tau-origin : ∀ {p s t} → D.Tau p s t → Origin s → Origin t
tau-origin (D.clientInternal _) (origin q s r) = origin q s r
tau-origin (D.serverInternal pr) (origin q s r) = origin
  (λ present → Server.tau-final pr (q present))
  (λ pending → Server.tau-final pr (s pending))
  (λ pending → Server.tau-final pr (r pending))
tau-origin (D.clientCallback _ _) (origin q s r) = origin q s r
tau-origin (D.serverCallback pr) (origin q s r) = origin
  (λ present → Server.step-final pr (q present))
  (λ pending → Server.step-final pr (s pending))
  (λ pending → Server.step-final pr (r pending))
tau-origin (D.commitClient _) (origin q s r) = origin q s r
tau-origin (D.commitServer {sc = queue} {m = m} pr) (origin q s r) = origin
  (queued-commit {m = m} {queue = queue} pr q) (sending-commit {m = m} pr) r
tau-origin (D.decodeClient _) (origin q s r) = origin
  (λ present → q (there present)) s (λ { refl → q (here refl) })
tau-origin (D.decodeServer _) (origin q s r) = origin q s r

-- Every finite execution preserves the physical origin invariant.
run-origin : ∀ {p s rows t} → D.Run p s rows t → Origin s → Origin t
run-origin D.stop valid = valid
run-origin (D.internal pr run) valid = run-origin run (tau-origin pr valid)
run-origin (D.visible pr run) valid = run-origin run (step-origin pr valid)

-- Initially there is no physical Done packet in any queue or hook.
initial-origin : ∀ {p rows t} → D.Run p D.initial rows t → Origin t
initial-origin run = run-origin run (origin (λ ()) (λ ()) (λ ()))
