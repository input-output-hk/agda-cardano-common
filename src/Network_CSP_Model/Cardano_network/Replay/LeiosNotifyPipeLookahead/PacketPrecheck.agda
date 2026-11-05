{-# OPTIONS --safe #-}

-- Necessary exact packet-prefix compatibility permits either endpoint's unfinished Send hook.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketPrecheck
  (Notification Return : Set) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ∷-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification Return as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Notification Return as Conservation

-- Both lists must agree wherever both contain a recorded packet; either may end first.
Compatible : ∀ {A : Set} → List A → List A → Set
Compatible [] _ = ⊤
Compatible (_ ∷ _) [] = ⊤
Compatible (x ∷ xs) (y ∷ ys) = x ≡ y × Compatible xs ys

-- Exact decidable equality checks only common packet positions, without truncating either input list.
compatible-decide : ∀ {A : Set} → DecidableEquality A → (xs ys : List A) → Dec (Compatible xs ys)
compatible-decide equal [] ys = yes tt
compatible-decide equal (_ ∷ _) [] = yes tt
compatible-decide equal (x ∷ xs) (y ∷ ys) with equal x y
... | no different = no λ { (same , rest) → different same }
... | yes same with compatible-decide equal xs ys
...   | yes rest = yes (same , rest)
...   | no absent = no λ { (_ , rest) → absent rest }

-- Any equality of extended histories forces agreement throughout their recorded common prefix.
compatible-append : ∀ {A : Set} (xs ys : List A) {after before} →
  xs ++ after ≡ ys ++ before → Compatible xs ys
compatible-append [] ys same = tt
compatible-append (_ ∷ _) [] same = tt
compatible-append (x ∷ xs) (y ∷ ys) same =
  proj₁ (∷-injective same) , compatible-append xs ys (proj₂ (∷-injective same))

-- Commands preserve the client endpoint's exact Send order and every duplicate occurrence.
clientSends : List Rows.ClientRow → List D.ClientMessage
clientSends [] = []
clientSends (Rows.sendCommand value ∷ rows) = value ∷ clientSends rows
clientSends (Rows.receiveResponse _ ∷ rows) = clientSends rows

-- Responses preserve the client endpoint's exact Receive order and complete Notification values.
clientReceives : List Rows.ClientRow → List D.ServerMessage
clientReceives [] = []
clientReceives (Rows.sendCommand _ ∷ rows) = clientReceives rows
clientReceives (Rows.receiveResponse value ∷ rows) = value ∷ clientReceives rows

-- Commands preserve the server endpoint's exact Receive order independently of its response rows.
serverReceives : List Rows.ServerRow → List D.ClientMessage
serverReceives [] = []
serverReceives (Rows.receiveCommand value ∷ rows) = value ∷ serverReceives rows
serverReceives (Rows.sendResponse _ ∷ rows) = serverReceives rows

-- Reply/Done records preserve all server Send occurrences, without deduplicating values or payload lists.
serverSends : List Rows.ServerRow → List D.ServerMessage
serverSends [] = []
serverSends (Rows.receiveCommand _ ∷ rows) = serverSends rows
serverSends (Rows.sendResponse value ∷ rows) = value ∷ serverSends rows

-- Extend all four histories by their corresponding exact endpoint projection.
extend : Conservation.History → List Rows.ClientRow → List Rows.ServerRow → Conservation.History
extend (Conservation.history a b c d) client server = Conservation.history
  (a ++ clientSends client) (b ++ serverReceives server)
  (c ++ serverSends server) (d ++ clientReceives client)

-- Every order-preserving merge has the same four packet histories, even after an arbitrary prior history.
merge-history : ∀ {client server events} → Rows.Merge client server events → (past : Conservation.History) →
  Conservation.observe events past ≡ extend past client server
merge-history Rows.empty (Conservation.history a b c d)
  rewrite ++-identityʳ a | ++-identityʳ b | ++-identityʳ c | ++-identityʳ d = refl
merge-history (Rows.client {row = Rows.sendCommand value} {rows = client} merged) (Conservation.history a b c d)
  rewrite merge-history merged (Conservation.advance (D.clientSend value) (Conservation.history a b c d))
        | ++-assoc a (value ∷ []) (clientSends client) = refl
merge-history (Rows.client {row = Rows.receiveResponse value} {rows = client} merged) (Conservation.history a b c d)
  rewrite merge-history merged (Conservation.advance (D.clientRecv value) (Conservation.history a b c d))
        | ++-assoc d (value ∷ []) (clientReceives client) = refl
merge-history (Rows.server {row = Rows.receiveCommand value} {rows = server} merged) (Conservation.history a b c d)
  rewrite merge-history merged (Conservation.advance (D.serverRecv value) (Conservation.history a b c d))
        | ++-assoc b (value ∷ []) (serverReceives server) = refl
merge-history (Rows.server {row = Rows.sendResponse value} {rows = server} merged) (Conservation.history a b c d)
  rewrite merge-history merged (Conservation.advance (D.serverSend value) (Conservation.history a b c d))
        | ++-assoc c (value ∷ []) (serverSends server) = refl

-- This predicate is necessary only; it makes no claim that matched prefixes have a source schedule.
Pass : List Rows.ClientRow → List Rows.ServerRow → Set
Pass client server = Compatible (clientSends client) (serverReceives server) ×
  Compatible (serverSends server) (clientReceives client)

-- Initiator command equality distinguishes RequestNext from Quit exactly.
command-equal : DecidableEquality D.ClientMessage
command-equal D.request D.request = yes refl
command-equal D.quit D.quit = yes refl
command-equal D.request D.quit = no λ ()
command-equal D.quit D.request = no λ ()

-- Responder equality reuses the model's exact normal/Canceled equality and keeps Done distinct.
response-equal : DecidableEquality Notification → DecidableEquality D.ServerMessage
response-equal equal D.done D.done = yes refl
response-equal equal D.done (D.reply _) = no λ ()
response-equal equal (D.reply _) D.done = no λ ()
response-equal equal (D.reply first) (D.reply second) with S.Executable.replyEq equal first second
... | yes refl = yes refl
... | no different = no λ { refl → different refl }

-- Both independent directional checks use exact packet values and retain finite-prefix EOF semantics.
decide : DecidableEquality Notification → (client : List Rows.ClientRow) (server : List Rows.ServerRow) →
  Dec (Pass client server)
decide equal client server =
  compatible-decide command-equal (clientSends client) (serverReceives server) ×-dec
  compatible-decide (response-equal equal) (serverSends server) (clientReceives client)

-- Actual source conservation transports along merge-history without imposing a global endpoint ordering.
necessary : ∀ {contract client server events target} → Rows.Merge client server events →
  D.Run contract D.initial events target → Pass client server
necessary {client = client} {server} {target = target} merged run =
  compatible-append (clientSends client) (serverReceives server) (Conservation.to-server balanced) ,
  compatible-append (serverSends server) (clientReceives client) (Conservation.to-client balanced)
  where
  -- Pending Sends/Receives and FIFO suffixes remain present in both original conservation equations.
  balanced : Conservation.Balanced (extend Conservation.empty client server) target
  balanced = subst (λ history → Conservation.Balanced history target)
    (merge-history merged Conservation.empty) (Conservation.initial-conservation run)
