{-# OPTIONS --safe #-}

-- Candidate enumeration guard only; exact proof-bearing lists and stable search priorities are unchanged.
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List using (List)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ReadyGateOrder
  (Notification : Set) (notificationEq : DecidableEquality Notification)
  (basis : List Notification) where

open import Level using (Level)
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; map; concat)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Notification ⊤ basis as B
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasisExecution Notification notificationEq basis as Menu
import Cardano_network.LeiosNotifyPipeLookahead.DriverSearchOrder Notification notificationEq basis as Old

-- The candidate reuses the original dependent successor type, including its exact certificate.
Move : S.Contract → D.State → Set
Move = Menu.Move

-- A mapped family of definitionally absent alternatives contributes the empty concatenation.
concat-empty : ∀ {a b : Level} {A : Set a} {B : Set b} (select : A → List B) (choices : List A) →
  (∀ choice → select choice ≡ []) → concat (map select choices) ≡ []
concat-empty select [] absent = refl
concat-empty select (choice ∷ choices) absent rewrite absent choice | concat-empty select choices absent = refl

-- This classification intentionally omits the reader-active guard; claimed/false still delegates to lookup.
data Inactive : S.State → Set where
  idle-gate : ∀ {r w c q} → Inactive (S.state r w S.idle c q)
  sent-gate : ∀ {r w c q} → Inactive (S.state r w S.sent c q)
  selected-gate : ∀ {r w c q m} → Inactive (S.state r w (S.selected m) c q)
  flagged-gate : ∀ {r w c} → Inactive (S.state r w S.claimed c true)

-- Each old lookup is absent in a gated state, independently of candidate value and membership proof.
one-inactive : ∀ p {client server cs sc pc ps rc rs} → Inactive server →
  (choice : Σ[ reply ∈ S.Reply ] B.AllowedReply reply) →
  Menu.readyOne p (D.pair client server cs sc pc ps rc rs) choice ≡ []
one-inactive p idle-gate (reply , allowed) = refl
one-inactive p sent-gate (reply , allowed) = refl
one-inactive p selected-gate (reply , allowed) = refl
one-inactive p flagged-gate (reply , allowed) = refl

-- The complete old proof-bearing readiness list is empty, even with duplicate/empty bases or unreachable states.
old-inactive : ∀ p {state} → Inactive (D.serverState state) → Menu.readyMoves p state ≡ []
old-inactive p {state = state@(D.pair clientState server cs sc pc ps rc rs)} inactive =
  concat-empty (Menu.readyOne p state) Menu.replyChoices
    (one-inactive p {client = clientState} {server = server} {cs = cs} {sc = sc}
      {pc = pc} {ps = ps} {rc = rc} {rs = rs} inactive)

-- Only claimed/false can select a new callback result; every other case avoids the old candidate scan.
readyMoves : ∀ p (state : D.State) → List (Move p state)
readyMoves p state@(D.pair _ (S.state _ _ S.claimed _ false) _ _ _ _ _ _) = Menu.readyMoves p state
readyMoves p state = []

-- Enabled cases use the original list verbatim; disabled cases equal its proved empty result.
readyMoves-exact : ∀ p state → readyMoves p state ≡ Menu.readyMoves p state
readyMoves-exact p state@(D.pair _ (S.state _ _ S.claimed _ false) _ _ _ _ _ _) = refl
readyMoves-exact p state@(D.pair _ (S.state _ _ S.claimed _ true) _ _ _ _ _ _) =
  sym (old-inactive p {state = state} flagged-gate)
readyMoves-exact p state@(D.pair _ (S.state _ _ S.idle _ _) _ _ _ _ _ _) =
  sym (old-inactive p {state = state} idle-gate)
readyMoves-exact p state@(D.pair _ (S.state _ _ S.sent _ _) _ _ _ _ _ _) =
  sym (old-inactive p {state = state} sent-gate)
readyMoves-exact p state@(D.pair _ (S.state _ _ (S.selected _) _ _) _ _ _ _ _ _) =
  sym (old-inactive p {state = state} selected-gate)

-- All seven other independent families retain their exact original function and menu position.
menus : ∀ p (state : D.State) → List (List (Move p state))
menus p state = Menu.clientMoves p state ∷ Menu.serverMoves p state ∷ Menu.callbackMoves p state ∷
  readyMoves p state ∷ Menu.clientCommitMoves p state ∷ Menu.serverCommitMoves p state ∷
  Menu.clientDecodeMoves p state ∷ Menu.serverDecodeMoves p state ∷ []

-- Family lists remain exactly equal, not merely extensionally equivalent as successor sets.
menus-exact : ∀ p state → menus p state ≡ Menu.menus p state
menus-exact p state rewrite readyMoves-exact p state = refl

-- The candidate menu concatenation retains duplicates, order and original transition evidence.
moves : ∀ p (state : D.State) → List (Move p state)
moves p state = concat (menus p state)

-- Exact menu equality lifts through concatenation without proof irrelevance.
moves-exact : ∀ p state → moves p state ≡ Menu.moves p state
moves-exact p state = cong concat (menus-exact p state)

-- Raw targets are exposed for instrumentation only after retaining the dependent proof list.
targets : S.Contract → D.State → List D.State
targets p state = map proj₁ (moves p state)

-- Raw target order and multiplicity are unchanged as a direct consequence of proof-list equality.
targets-exact : ∀ p state → targets p state ≡ Menu.targets p state
targets-exact p state = cong (map proj₁) (moves-exact p state)

-- The same old stable sort and score consume the gated proof list, with no new ranking policy.
orderedMoves : (p : S.Contract) (state : D.State) →
  List Rows.ClientRow → List Rows.ServerRow → List (Move p state)
orderedMoves p state client server = Old.sort (Old.score client server) (moves p state)

-- Equal proof-bearing inputs give exactly equal sorted lists, including certificates and score ties.
orderedMoves-exact : ∀ p state client server →
  orderedMoves p state client server ≡ Old.orderedMoves p state client server
orderedMoves-exact p state client server = cong (Old.sort (Old.score client server)) (moves-exact p state)

-- The public order interface matches DriverSearchOrder for an optional later measured integration.
orderedTargets : (p : S.Contract) (state : D.State) →
  List Rows.ClientRow → List Rows.ServerRow → List D.State
orderedTargets p state client server = map proj₁ (orderedMoves p state client server)

-- Every ordered target and duplicate occurrence appears at its exact previous position.
orderedTargets-exact : ∀ p state client server →
  orderedTargets p state client server ≡ Old.orderedTargets p state client server
orderedTargets-exact p state client server = cong (map proj₁) (orderedMoves-exact p state client server)

-- Existing soundness transports along exact target-list equality for every arbitrary state.
target-sound : ∀ {p s client server t} → t ∈ orderedTargets p s client server → B.Tau p s t
target-sound {p} {s} {client} {server} {t} member = Old.target-sound {p = p} {s = s} {client = client} {server = server} {t = t}
  (subst (t ∈_) (orderedTargets-exact p s client server) member)

-- Existing completeness likewise retains every basis step without a reachability or freshness premise.
target-complete : ∀ {p s client server t} → B.Tau p s t → t ∈ orderedTargets p s client server
target-complete {p} {s} {client} {server} {t} step = subst (t ∈_)
  (sym (orderedTargets-exact p s client server))
  (Old.target-complete {p = p} {s = s} {client = client} {server = server} {t = t} step)
