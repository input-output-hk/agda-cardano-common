{-# OPTIONS --safe #-}

-- Prototype Fetch: bounded client, sequential server and two exact-message FIFOs.
open import Data.Nat using (ℕ)
module Cardano_network.Replay.LeiosFetchPairedSession (k : ℕ) where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Cardano_network.Replay.Common using (client; server)
import Cardano_network.Replay.LeiosFetchSession as F
import Cardano_network.Replay.LeiosFetchPairedLocal as Wire
open Wire k using (normal; next; next-sound; next-normal)
module Local = Wire.Local k
open import Cardano_network.Replay.Paired F.St F.Msg F._≟M_ next public
open import Cardano_network.Replay.PairedDecide F.St F.Msg F._≟M_ next public

-- Both endpoints start fresh, with no outstanding requests or queued messages.
initial : State
initial = fresh F.client₀ F.server₀

-- Client projection expands macro steps into genuine original weak traces.
client-trace : ∀ {s es t} → s ⇒⟨ es ⟩ t →
  Local._⇒⟨_⟩_ (normal (clientState s)) (project client es) (normal (clientState t))
client-trace done = Local.done
client-trace (tau () _)
client-trace (vis (clientSend {c = x} pr) run) = Local.⇒-++ (next-sound {r = client} {s = x} pr)
  (subst (λ u → Local._⇒⟨_⟩_ u _ _) (next-normal {r = client} {s = x} pr) (client-trace run))
client-trace (vis (clientRecv {c = x} pr) run) = Local.⇒-++ (next-sound {r = client} {s = x} pr)
  (subst (λ u → Local._⇒⟨_⟩_ u _ _) (next-normal {r = client} {s = x} pr) (client-trace run))
client-trace (vis (serverSend pr) run) = client-trace run
client-trace (vis (serverRecv pr) run) = client-trace run

-- Server projection restores the silent application-serve transitions.
server-trace : ∀ {s es t} → s ⇒⟨ es ⟩ t →
  Local._⇒⟨_⟩_ (normal (serverState s)) (project server es) (normal (serverState t))
server-trace done = Local.done
server-trace (tau () _)
server-trace (vis (clientSend pr) run) = server-trace run
server-trace (vis (clientRecv pr) run) = server-trace run
server-trace (vis (serverSend {s = x} pr) run) = Local.⇒-++ (next-sound {r = server} {s = x} pr)
  (subst (λ u → Local._⇒⟨_⟩_ u _ _) (next-normal {r = server} {s = x} pr) (server-trace run))
server-trace (vis (serverRecv {s = x} pr) run) = Local.⇒-++ (next-sound {r = server} {s = x} pr)
  (subst (λ u → Local._⇒⟨_⟩_ u _ _) (next-normal {r = server} {s = x} pr) (server-trace run))

-- Paired acceptance entails membership in the existing client replay language.
compatible-client : ∀ {cs ss} → Compatible initial cs ss → Local.HasTrace F.client₀ cs
compatible-client run with merge-run run
... | t , pr = normal (clientState t) , subst
  (λ es → Local._⇒⟨_⟩_ F.client₀ es (normal (clientState t)))
  (client-projection run) (client-trace pr)

-- Paired acceptance entails membership in the existing sequential server language.
compatible-server : ∀ {cs ss} → Compatible initial cs ss → Local.HasTrace F.server₀ ss
compatible-server run with merge-run run
... | t , pr = normal (serverState t) , subst
  (λ es → Local._⇒⟨_⟩_ F.server₀ es (normal (serverState t)))
  (server-projection run) (server-trace pr)
