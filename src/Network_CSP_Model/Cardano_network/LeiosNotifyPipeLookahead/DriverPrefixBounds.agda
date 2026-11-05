{-# OPTIONS --safe #-}

-- Input-prefix bounds concern arbitrary finite paired-driver runs, including delayed hooks.
module Cardano_network.LeiosNotifyPipeLookahead.DriverPrefixBounds
  (Notification Return : Set) where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; +-mono-≤; ≤-refl; ≤-reflexive; ≤-trans; m≤n+m)
open import Data.List using (List; []; _∷_; _++_; _∷ʳ_; length)
open import Data.List.Properties using (length-++; length-++-sucʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Notification Return as B

-- Each unfinished sender/receiver trace hook holds exactly zero or one packet.
occupied : ∀ {A : Set} → Maybe A → ℕ
occupied nothing = 0
occupied (just _) = 1

-- A pending hook is a single slot regardless of packet payload or return policy.
slot-bound : ∀ {A : Set} (slot : Maybe A) → occupied slot ≤ 1
slot-bound nothing = z≤n
slot-bound (just _) = s≤s z≤n

-- A hook accounts for hidden physical operations and its corresponding visible rows.
record Hook : Set₁ where
  field
    slot : D.State → ℕ
    hidden : ∀ {p s t} → D.Tau p s t → ℕ
    row : D.Event → ℕ
    tau-law : ∀ {p s t} (step : D.Tau p s t) → slot s + hidden step ≡ slot t
    step-law : ∀ {p s e t} → D.Step p s e t → slot s ≡ row e + slot t

-- One structural induction supplies exact prefix accounting for any of the four hooks.
module Tally (hook : Hook) where
  open Hook hook

  -- Count actual hidden operations in the supplied run witness, not a guessed search limit.
  operations : ∀ {p s rows t} → D.Run p s rows t → ℕ
  operations D.stop = 0
  operations (D.internal step run) = hidden step + operations run
  operations (D.visible step run) = operations run

  -- Count the relevant original file-order rows; all other records contribute zero.
  rows : List D.Event → ℕ
  rows [] = 0
  rows (e ∷ es) = row e + rows es

  -- Exact accounting also works from arbitrary nonfresh states with an occupied hook.
  exact : ∀ {p s es t} (run : D.Run p s es t) →
    slot s + operations run ≡ rows es + slot t
  exact {s = s} D.stop = +-identityʳ (slot s)
  exact {s = s} (D.internal step run) =
    trans (sym (+-assoc (slot s) (hidden step) (operations run)))
      (trans (cong (_+ operations run) (tau-law step)) (exact run))
  exact {s = s} (D.visible {t = mid} {e = e} {es = es} step run) =
    trans (cong (_+ operations run) (step-law step))
      (trans (+-assoc (row e) (slot mid) (operations run))
        (trans (cong (row e +_) (exact run)) (sym (+-assoc (row e) (rows es) _))))

-- Physical commitClient operations are counted independently of delayed clientSend rows.
clientSendHidden : ∀ {p s t} → D.Tau p s t → ℕ
clientSendHidden (D.clientInternal _) = 0
clientSendHidden (D.serverInternal _) = 0
clientSendHidden (D.clientCallback _ _) = 0
clientSendHidden (D.serverCallback _) = 0
clientSendHidden (D.commitClient _) = 1
clientSendHidden (D.commitServer _) = 0
clientSendHidden (D.decodeClient _) = 0
clientSendHidden (D.decodeServer _) = 0

-- Select exactly the clientSend constructor in the visible input prefix.
clientSendRow : D.Event → ℕ
clientSendRow (D.clientSend _) = 1
clientSendRow (D.serverSend _) = 0
clientSendRow (D.clientRecv _) = 0
clientSendRow (D.serverRecv _) = 0

-- Only commitClient fills this hook; other hidden moves preserve it.
clientSendTau : ∀ {p s t} (step : D.Tau p s t) →
  occupied (D.pendingClientSend s) + clientSendHidden step ≡ occupied (D.pendingClientSend t)
clientSendTau (D.clientInternal _) = +-identityʳ _
clientSendTau (D.serverInternal _) = +-identityʳ _
clientSendTau (D.clientCallback _ _) = +-identityʳ _
clientSendTau (D.serverCallback _) = +-identityʳ _
clientSendTau (D.commitClient _) = refl
clientSendTau (D.commitServer _) = +-identityʳ _
clientSendTau (D.decodeClient _) = +-identityʳ _
clientSendTau (D.decodeServer _) = +-identityʳ _

-- Only the corresponding visible hook discharges the occupied slot.
clientSendStep : ∀ {p s e t} → D.Step p s e t →
  occupied (D.pendingClientSend s) ≡ clientSendRow e + occupied (D.pendingClientSend t)
clientSendStep (D.clientSent _) = refl
clientSendStep (D.serverSent _) = refl
clientSendStep (D.clientReceived _) = refl
clientSendStep (D.serverReceived _) = refl

-- Package the exact laws without imposing any payload or callback policy.
clientSendHook : Hook
clientSendHook = record { slot = λ s → occupied (D.pendingClientSend s); hidden = clientSendHidden;
  row = clientSendRow; tau-law = clientSendTau; step-law = clientSendStep }

-- Public operation/row counts and arbitrary-state exact tally for this hook.
module ClientSend = Tally clientSendHook

-- A fresh run has no inherited operation; at EOF at most one operation lacks its row.
clientSend-exact : ∀ {p es t} (run : D.Run p D.initial es t) →
  ClientSend.operations run ≡ ClientSend.rows es + occupied (D.pendingClientSend t)
clientSend-exact run = ClientSend.exact run

-- The additive one is necessary when the final trace hook is still pending.
clientSend-bound : ∀ {p es t} (run : D.Run p D.initial es t) →
  ClientSend.operations run ≤ ClientSend.rows es + 1
clientSend-bound {t = t} run = ≤-trans (≤-reflexive (clientSend-exact run))
  (+-mono-≤ ≤-refl (slot-bound (D.pendingClientSend t)))

-- Physical commitServer operations are counted independently of delayed serverSend rows.
serverSendHidden : ∀ {p s t} → D.Tau p s t → ℕ
serverSendHidden (D.clientInternal _) = 0
serverSendHidden (D.serverInternal _) = 0
serverSendHidden (D.clientCallback _ _) = 0
serverSendHidden (D.serverCallback _) = 0
serverSendHidden (D.commitClient _) = 0
serverSendHidden (D.commitServer _) = 1
serverSendHidden (D.decodeClient _) = 0
serverSendHidden (D.decodeServer _) = 0

-- Select exactly the serverSend constructor in the visible input prefix.
serverSendRow : D.Event → ℕ
serverSendRow (D.clientSend _) = 0
serverSendRow (D.serverSend _) = 1
serverSendRow (D.clientRecv _) = 0
serverSendRow (D.serverRecv _) = 0

-- Only commitServer fills this hook; other hidden moves preserve it.
serverSendTau : ∀ {p s t} (step : D.Tau p s t) →
  occupied (D.pendingServerSend s) + serverSendHidden step ≡ occupied (D.pendingServerSend t)
serverSendTau (D.clientInternal _) = +-identityʳ _
serverSendTau (D.serverInternal _) = +-identityʳ _
serverSendTau (D.clientCallback _ _) = +-identityʳ _
serverSendTau (D.serverCallback _) = +-identityʳ _
serverSendTau (D.commitClient _) = +-identityʳ _
serverSendTau (D.commitServer _) = refl
serverSendTau (D.decodeClient _) = +-identityʳ _
serverSendTau (D.decodeServer _) = +-identityʳ _

-- Only the corresponding visible hook discharges the occupied slot.
serverSendStep : ∀ {p s e t} → D.Step p s e t →
  occupied (D.pendingServerSend s) ≡ serverSendRow e + occupied (D.pendingServerSend t)
serverSendStep (D.clientSent _) = refl
serverSendStep (D.serverSent _) = refl
serverSendStep (D.clientReceived _) = refl
serverSendStep (D.serverReceived _) = refl

-- Package the exact laws without imposing any payload or callback policy.
serverSendHook : Hook
serverSendHook = record { slot = λ s → occupied (D.pendingServerSend s); hidden = serverSendHidden;
  row = serverSendRow; tau-law = serverSendTau; step-law = serverSendStep }

-- Public operation/row counts and arbitrary-state exact tally for this hook.
module ServerSend = Tally serverSendHook

-- A fresh run has no inherited operation; at EOF at most one operation lacks its row.
serverSend-exact : ∀ {p es t} (run : D.Run p D.initial es t) →
  ServerSend.operations run ≡ ServerSend.rows es + occupied (D.pendingServerSend t)
serverSend-exact run = ServerSend.exact run

-- The additive one is necessary when the final trace hook is still pending.
serverSend-bound : ∀ {p es t} (run : D.Run p D.initial es t) →
  ServerSend.operations run ≤ ServerSend.rows es + 1
serverSend-bound {t = t} run = ≤-trans (≤-reflexive (serverSend-exact run))
  (+-mono-≤ ≤-refl (slot-bound (D.pendingServerSend t)))

-- Physical decodeServer operations are counted independently of delayed serverRecv rows.
serverRecvHidden : ∀ {p s t} → D.Tau p s t → ℕ
serverRecvHidden (D.clientInternal _) = 0
serverRecvHidden (D.serverInternal _) = 0
serverRecvHidden (D.clientCallback _ _) = 0
serverRecvHidden (D.serverCallback _) = 0
serverRecvHidden (D.commitClient _) = 0
serverRecvHidden (D.commitServer _) = 0
serverRecvHidden (D.decodeClient _) = 0
serverRecvHidden (D.decodeServer _) = 1

-- Select exactly the serverRecv constructor in the visible input prefix.
serverRecvRow : D.Event → ℕ
serverRecvRow (D.clientSend _) = 0
serverRecvRow (D.serverSend _) = 0
serverRecvRow (D.clientRecv _) = 0
serverRecvRow (D.serverRecv _) = 1

-- Only decodeServer fills this hook; other hidden moves preserve it.
serverRecvTau : ∀ {p s t} (step : D.Tau p s t) →
  occupied (D.pendingServerRecv s) + serverRecvHidden step ≡ occupied (D.pendingServerRecv t)
serverRecvTau (D.clientInternal _) = +-identityʳ _
serverRecvTau (D.serverInternal _) = +-identityʳ _
serverRecvTau (D.clientCallback _ _) = +-identityʳ _
serverRecvTau (D.serverCallback _) = +-identityʳ _
serverRecvTau (D.commitClient _) = +-identityʳ _
serverRecvTau (D.commitServer _) = +-identityʳ _
serverRecvTau (D.decodeClient _) = +-identityʳ _
serverRecvTau (D.decodeServer _) = refl

-- Only the corresponding visible hook discharges the occupied slot.
serverRecvStep : ∀ {p s e t} → D.Step p s e t →
  occupied (D.pendingServerRecv s) ≡ serverRecvRow e + occupied (D.pendingServerRecv t)
serverRecvStep (D.clientSent _) = refl
serverRecvStep (D.serverSent _) = refl
serverRecvStep (D.clientReceived _) = refl
serverRecvStep (D.serverReceived _) = refl

-- Package the exact laws without imposing any payload or callback policy.
serverRecvHook : Hook
serverRecvHook = record { slot = λ s → occupied (D.pendingServerRecv s); hidden = serverRecvHidden;
  row = serverRecvRow; tau-law = serverRecvTau; step-law = serverRecvStep }

-- Public operation/row counts and arbitrary-state exact tally for this hook.
module ServerRecv = Tally serverRecvHook

-- A fresh run has no inherited operation; at EOF at most one operation lacks its row.
serverRecv-exact : ∀ {p es t} (run : D.Run p D.initial es t) →
  ServerRecv.operations run ≡ ServerRecv.rows es + occupied (D.pendingServerRecv t)
serverRecv-exact run = ServerRecv.exact run

-- The additive one is necessary when the final trace hook is still pending.
serverRecv-bound : ∀ {p es t} (run : D.Run p D.initial es t) →
  ServerRecv.operations run ≤ ServerRecv.rows es + 1
serverRecv-bound {t = t} run = ≤-trans (≤-reflexive (serverRecv-exact run))
  (+-mono-≤ ≤-refl (slot-bound (D.pendingServerRecv t)))

-- Physical decodeClient operations are counted independently of delayed clientRecv rows.
clientRecvHidden : ∀ {p s t} → D.Tau p s t → ℕ
clientRecvHidden (D.clientInternal _) = 0
clientRecvHidden (D.serverInternal _) = 0
clientRecvHidden (D.clientCallback _ _) = 0
clientRecvHidden (D.serverCallback _) = 0
clientRecvHidden (D.commitClient _) = 0
clientRecvHidden (D.commitServer _) = 0
clientRecvHidden (D.decodeClient _) = 1
clientRecvHidden (D.decodeServer _) = 0

-- Select exactly the clientRecv constructor in the visible input prefix.
clientRecvRow : D.Event → ℕ
clientRecvRow (D.clientSend _) = 0
clientRecvRow (D.serverSend _) = 0
clientRecvRow (D.clientRecv _) = 1
clientRecvRow (D.serverRecv _) = 0

-- Only decodeClient fills this hook; other hidden moves preserve it.
clientRecvTau : ∀ {p s t} (step : D.Tau p s t) →
  occupied (D.pendingClientRecv s) + clientRecvHidden step ≡ occupied (D.pendingClientRecv t)
clientRecvTau (D.clientInternal _) = +-identityʳ _
clientRecvTau (D.serverInternal _) = +-identityʳ _
clientRecvTau (D.clientCallback _ _) = +-identityʳ _
clientRecvTau (D.serverCallback _) = +-identityʳ _
clientRecvTau (D.commitClient _) = +-identityʳ _
clientRecvTau (D.commitServer _) = +-identityʳ _
clientRecvTau (D.decodeClient _) = refl
clientRecvTau (D.decodeServer _) = +-identityʳ _

-- Only the corresponding visible hook discharges the occupied slot.
clientRecvStep : ∀ {p s e t} → D.Step p s e t →
  occupied (D.pendingClientRecv s) ≡ clientRecvRow e + occupied (D.pendingClientRecv t)
clientRecvStep (D.clientSent _) = refl
clientRecvStep (D.serverSent _) = refl
clientRecvStep (D.clientReceived _) = refl
clientRecvStep (D.serverReceived _) = refl

-- Package the exact laws without imposing any payload or callback policy.
clientRecvHook : Hook
clientRecvHook = record { slot = λ s → occupied (D.pendingClientRecv s); hidden = clientRecvHidden;
  row = clientRecvRow; tau-law = clientRecvTau; step-law = clientRecvStep }

-- Public operation/row counts and arbitrary-state exact tally for this hook.
module ClientRecv = Tally clientRecvHook

-- A fresh run has no inherited operation; at EOF at most one operation lacks its row.
clientRecv-exact : ∀ {p es t} (run : D.Run p D.initial es t) →
  ClientRecv.operations run ≡ ClientRecv.rows es + occupied (D.pendingClientRecv t)
clientRecv-exact run = ClientRecv.exact run

-- The additive one is necessary when the final trace hook is still pending.
clientRecv-bound : ∀ {p es t} (run : D.Run p D.initial es t) →
  ClientRecv.operations run ≤ ClientRecv.rows es + 1
clientRecv-bound {t = t} run = ≤-trans (≤-reflexive (clientRecv-exact run))
  (+-mono-≤ ≤-refl (slot-bound (D.pendingClientRecv t)))
