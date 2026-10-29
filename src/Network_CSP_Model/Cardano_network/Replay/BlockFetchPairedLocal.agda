{-# OPTIONS --safe #-}

-- Adapt the distinct existing BlockFetch state types to the shared paired engine.
open import Data.Nat using (ℕ)
module Cardano_network.Replay.BlockFetchPairedLocal (k : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Properties using (_<?_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.Common using (Role; client; server)
import Cardano_network.Replay.BlockFetchClientSession as C
import Cardano_network.Replay.BlockFetchServerSession as S

-- The tag prevents either endpoint from executing the other role's machine.
data St : Set where
  clientS : C.St → St
  serverS : S.St → St

-- Total projections have irrelevant defaults for the disabled opposite tag.
clientView : St → C.St
clientView (clientS s) = s
clientView (serverS _) = C.initial

-- Fresh server state is used only when projecting an unreachable wrong tag.
serverView : St → S.St
serverView (serverS s) = s
serverView (clientS _) = S.idle

-- Existing enumerators have at most one successor; retain its role tag.
choose : ∀ {A : Set} → (A → St) → List A → Maybe St
choose tag [] = nothing
choose tag (s ∷ _) = just (tag s)

-- A selected successor belongs to the original certified enumeration.
choose-sound : ∀ {A : Set} (tag : A → St) (xs : List A) {t} →
  choose tag xs ≡ just t → Σ[ u ∈ A ] (u ∈ xs × tag u ≡ t)
choose-sound tag [] ()
choose-sound tag (s ∷ _) refl = s , here refl , refl

-- Role-specific updates reuse the existing client/server successor lists.
next : Role → St → C.E → Maybe St
next client (clientS s) e = choose clientS (C.after k s e)
next server (serverS s) e = choose serverS (S.after s e)
next _ _ _ = nothing

-- An enabled client step preserves the client tag needed by joint witnesses.
client-target : ∀ {s e t} → next client s e ≡ just t → Σ[ u ∈ C.St ] t ≡ clientS u
client-target {clientS s} {e} p with choose-sound clientS (C.after k s e) p
... | u , mem , refl = u , refl
client-target {serverS _} ()

-- The server adapter likewise cannot change its endpoint's state tag.
server-target : ∀ {s e t} → next server s e ≡ just t → Σ[ u ∈ S.St ] t ≡ serverS u
server-target {serverS s} {e} p with choose-sound serverS (S.after s e) p
... | u , mem , refl = u , refl
server-target {clientS _} ()

-- Every enabled client update is a transition of the original bounded client.
client-sound : ∀ {s e t} → next client s e ≡ just t →
  C.Step k (clientView s) e (clientView t)
client-sound {clientS s} {e} p with choose-sound clientS (C.after k s e) p
... | u , mem , refl = C.after-sound mem
client-sound {serverS _} ()

-- Every enabled server update is a transition of the original sequential server.
server-sound : ∀ {s e t} → next server s e ≡ just t →
  S.Step (serverView s) e (serverView t)
server-sound {serverS s} {e} p with choose-sound serverS (S.after s e) p
... | u , mem , refl = S.after-sound mem
server-sound {clientS _} ()

-- No legal client transition is lost by selecting the enumerated successor.
client-complete : ∀ {s e t} → C.Step k s e t →
  next client (clientS s) e ≡ just (clientS t)
client-complete (C.issue {n} lt) with n <? k
... | yes _ = refl
... | no bad = ⊥-elim (bad lt)
client-complete C.start = refl
client-complete C.none = refl
client-complete C.body = refl
client-complete C.end = refl
client-complete C.close = refl

-- Every legal sequential-server transition is represented without extra steps.
server-complete : ∀ {s e t} → S.Step s e t →
  next server (serverS s) e ≡ just (serverS t)
server-complete S.receive = refl
server-complete S.start = refl
server-complete S.none = refl
server-complete S.body = refl
server-complete S.end = refl
server-complete S.close = refl
