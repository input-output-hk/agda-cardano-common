{-# OPTIONS --safe #-}

-- Search order changes only enumeration priority, retaining every independent basis successor.
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List using (List)
module Cardano_network.LeiosNotifyPipeLookahead.DriverSearchOrder
  (Notification : Set) (notificationEq : DecidableEquality Notification)
  (basis : List Notification) where

open import Level using (Level)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using ([]; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤ᵇ_)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverExecution Notification ⊤ notificationEq as Equality
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Notification ⊤ basis as B
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasisExecution Notification notificationEq basis as Menu
module ReplyEquality = S.Executable notificationEq

-- Insertion places an earlier equally scored move first, preserving the original order of ties.
insert : ∀ {a} {A : Set a} → (A → ℕ) → A → List A → List A
insert score value [] = value ∷ []
insert score value (head ∷ rest) with score value ≤ᵇ score head
... | true = value ∷ head ∷ rest
... | false = head ∷ insert score value rest

-- Insertion sorting is finite and leaves the order of equal-priority source candidates stable.
sort : ∀ {a} {A : Set a} → (A → ℕ) → List A → List A
sort score [] = []
sort score (value ∷ rest) = insert score value (sort score rest)

-- The newly inserted move always remains present, regardless of comparisons.
insert-present : ∀ {a} {A : Set a} (score : A → ℕ) value rest → value ∈ insert score value rest
insert-present score value [] = here refl
insert-present score value (head ∷ rest) with score value ≤ᵇ score head
... | true = here refl
... | false = there (insert-present score value rest)

-- Every previous occurrence survives insertion; no candidate is filtered out.
insert-retains : ∀ {a} {A : Set a} (score : A → ℕ) value {rest item} →
  item ∈ rest → item ∈ insert score value rest
insert-retains score value {[]} ()
insert-retains score value {head ∷ rest} member with score value ≤ᵇ score head
... | true = there member
... | false with member
...   | here equal = here equal
...   | there member = there (insert-retains score value member)

-- Insertion never invents an occurrence apart from its declared new move.
insert-origin : ∀ {a} {A : Set a} (score : A → ℕ) value rest {item} →
  item ∈ insert score value rest → (item ≡ value) ⊎ (item ∈ rest)
insert-origin score value [] (here equal) = inj₁ equal
insert-origin score value [] (there ())
insert-origin score value (head ∷ rest) member with score value ≤ᵇ score head
... | true with member
...   | here equal = inj₁ equal
...   | there member = inj₂ member
insert-origin score value (head ∷ rest) member | false with member
... | here equal = inj₂ (here equal)
... | there member with insert-origin score value rest member
...   | inj₁ equal = inj₁ equal
...   | inj₂ old = inj₂ (there old)

-- Stable sorting retains every original candidate and its complete dependent certificate.
sort-retains : ∀ {a} {A : Set a} (score : A → ℕ) {values item} → item ∈ values → item ∈ sort score values
sort-retains score {[]} ()
sort-retains score {head ∷ rest} (here refl) = insert-present score head (sort score rest)
sort-retains score {head ∷ rest} (there member) = insert-retains score head (sort-retains score member)

-- Every sorted occurrence comes from the original finite candidate list.
sort-origin : ∀ {a} {A : Set a} (score : A → ℕ) values {item} → item ∈ sort score values → item ∈ values
sort-origin score [] ()
sort-origin score (head ∷ rest) member with insert-origin score head (sort score rest) member
... | inj₁ equal = here equal
... | inj₂ old = there (sort-origin score rest old)

-- Future initiator commands guide hidden callback choices without moving any visible record.
clientCommand : List Rows.ClientRow → Maybe D.ClientMessage
clientCommand [] = nothing
clientCommand (Rows.sendCommand command ∷ _) = just command
clientCommand (_ ∷ rest) = clientCommand rest

-- A server reply demand is taken from its next send before consulting the client receive prefix.
serverReply : List Rows.ServerRow → Maybe S.Reply
serverReply [] = nothing
serverReply (Rows.sendResponse (D.reply reply) ∷ _) = just reply
serverReply (Rows.sendResponse D.done ∷ _) = nothing
serverReply (_ ∷ rest) = serverReply rest

-- If the server capture ends first, a client Receive can still name an unrecorded pending Send.
clientReply : List Rows.ClientRow → Maybe S.Reply
clientReply [] = nothing
clientReply (Rows.receiveResponse (D.reply reply) ∷ _) = just reply
clientReply (Rows.receiveResponse D.done ∷ _) = nothing
clientReply (_ ∷ rest) = clientReply rest

-- Exact next packet demand guides readiness while every other basis value remains a candidate.
wantedReply : List Rows.ClientRow → List Rows.ServerRow → Maybe S.Reply
wantedReply client server with serverReply server
... | just reply = just reply
... | nothing = clientReply client

-- Request and Quit have fixed distinct agency; equality is a priority test, never a source guard.
commandMatches : D.ClientMessage → Maybe D.ClientMessage → Bool
commandMatches D.request (just D.request) = true
commandMatches D.quit (just D.quit) = true
commandMatches _ _ = false

-- Exact notification equality favors the demanded payload without collapsing any fields.
replyMatches : S.Reply → Maybe S.Reply → Bool
replyMatches value nothing = false
replyMatches value (just wanted) with ReplyEquality.replyEq value wanted
... | yes _ = true
... | no _ = false

-- The already decoded or committed packet should enable its next corresponding visible hook.
clientCommitWanted : D.ClientMessage → List Rows.ClientRow → List Rows.ServerRow → Bool
clientCommitWanted value (Rows.sendCommand command ∷ _) server = commandMatches value (just command)
clientCommitWanted value client (Rows.receiveCommand command ∷ _) = commandMatches value (just command)
clientCommitWanted _ _ _ = false

-- Matching response packets serve either endpoint's immediate next visible record.
serverCommitWanted : D.ServerMessage → List Rows.ClientRow → List Rows.ServerRow → Bool
serverCommitWanted value client (Rows.sendResponse wanted ∷ _) with Equality.serverMessageEq value wanted
... | yes _ = true
... | no _ = false
serverCommitWanted value (Rows.receiveResponse wanted ∷ _) server with Equality.serverMessageEq value wanted
... | yes _ = true
... | no _ = false
serverCommitWanted _ _ _ = false

-- A physical command decode is useful exactly when the server head awaits that command.
serverDecodeWanted : D.ClientMessage → List Rows.ServerRow → Bool
serverDecodeWanted value (Rows.receiveCommand command ∷ _) = commandMatches value (just command)
serverDecodeWanted _ _ = false

-- A physical response decode is useful exactly when the client head awaits that packet.
clientDecodeWanted : D.ServerMessage → List Rows.ClientRow → Bool
clientDecodeWanted value (Rows.receiveResponse wanted ∷ _) with Equality.serverMessageEq value wanted
... | yes _ = true
... | no _ = false
clientDecodeWanted _ _ = false

-- Collection is useful while any published receiver result is available.
hasResult : C.State → Bool
hasResult state with C.results state
... | [] = false
... | _ ∷ _ = true

-- A selected normal may survive Quit publication, but a new normal cannot be selected afterward.
normalPending : S.Sender → Bool
normalPending (S.selected (S.normal _)) = true
normalPending _ = false

-- Delay irreversible server flag publication while a demanded normal still needs selection.
publicationScore : Maybe S.Reply → S.Sender → ℕ
publicationScore (just (S.normal _)) sender = if normalPending sender then 1 else 8
publicationScore _ _ = 1

-- Callback continuation is favored for an actual next Request or immediately available collection.
continueScore : C.State → List Rows.ClientRow → ℕ
continueScore state client with hasResult state
... | true = 1
... | false = if commandMatches D.request (clientCommand client) then 2 else 8

-- Termination is promoted for a declared next Quit, including intervening response Receive records.
terminateScore : List Rows.ClientRow → ℕ
terminateScore client = if commandMatches D.quit (clientCommand client) then 0 else 8

-- Every score changes search order only; none is an exclusion or a runtime protocol policy.
score : ∀ {p s} → List Rows.ClientRow → List Rows.ServerRow → Menu.Move p s → ℕ
score client server (_ , B.clientCallback D.terminate C.stopRequested) = terminateScore client
score {s = state} client server (_ , B.clientCallback D.continue _) = continueScore (D.clientState state) client
score client server (_ , B.clientCallback D.handled _) = 1
score client server (_ , B.clientInternal _) = 1
score client server (_ , B.serverInternal S.excessive) = 9
score client server (_ , B.serverInternal S.abort) = 9
score {s = state} client server (_ , B.serverInternal S.setQuit) =
  publicationScore (wantedReply client server) (S.sender (D.serverState state))
score client server (_ , B.serverInternal (S.cancel _)) =
  if replyMatches S.canceled (wantedReply client server) then 0 else 7
score client server (_ , B.serverInternal _) = 1
score client server (_ , B.serverCallback {reply = value} _ _) =
  if replyMatches value (wantedReply client server) then 0 else 7
score client server (_ , B.commitClient {message = value} _) =
  if clientCommitWanted value client server then 0 else 6
score client server (_ , B.commitServer {message = value} _) =
  if serverCommitWanted value client server then 0 else 6
score client server (_ , B.decodeClient {message = value} _) =
  if clientDecodeWanted value client then 0 else 6
score client server (_ , B.decodeServer {message = value} _) =
  if serverDecodeWanted value server then 0 else 6

-- The complete proof-bearing finite menu is stably reordered for the current exact input suffixes.
orderedMoves : (p : S.Contract) (s : D.State) → List Rows.ClientRow → List Rows.ServerRow → List (Menu.Move p s)
orderedMoves p s client server = sort (score client server) (Menu.moves p s)

-- Generic ordered replay consumes the same state targets under an input-dependent enumeration.
orderedTargets : (p : S.Contract) (s : D.State) → List Rows.ClientRow → List Rows.ServerRow → List D.State
orderedTargets p s client server = map proj₁ (orderedMoves p s client server)

-- Reordered target membership reconstructs an actual original basis-restricted hidden step.
target-sound : ∀ {p s client server t} → t ∈ orderedTargets p s client server → B.Tau p s t
target-sound {p} {s} {client} {server} member with ∈-map⁻ proj₁ member
... | move , listed , refl = Menu.target-sound (∈-map⁺ proj₁ (sort-origin (score client server) (Menu.moves p s) listed))

-- Every independent hidden step remains present for every possible input suffix and contract.
target-complete : ∀ {p s client server t} → B.Tau p s t → t ∈ orderedTargets p s client server
target-complete {p} {s} {client} {server} pr with ∈-map⁻ proj₁ (Menu.target-complete pr)
... | move , listed , refl = ∈-map⁺ proj₁ (sort-retains (score client server) listed)
